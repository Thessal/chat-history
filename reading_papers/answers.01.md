# Answers to Questions

## BK Petersen 2019

**1. While proposed DSO method provide parent and sibling information as sequence to the model, does it preserve adjacency of the expression tree? For example, does the model aware that current depth in the expression tree? What kind of positional encoding is used in the proposed model?**
The method preserves structural adjacency strictly by feeding the previously generated parent and sibling tokens as input states to the RNN at each step. However, it does not explicitly provide the current tree depth. Because it uses a Recurrent Neural Network (RNN) generating the sequence autoregressively, positional and structural dependencies are implicitly learned through the sequence history and the hidden state, without using explicit positional encodings common in Transformers.

**2. Did the paper show the poor performance of the expectation-based method? I assume that is conceptually similar to beam search. Wasn't beam search used for AlphaGeometry? Is the proposed method fundamentally different from the beam search, or is it a modification?**
Yes, the paper empirically demonstrated that standard expectation-based policy gradients plateau prematurely and perform significantly worse. An expectation-based method is an RL training objective that maximizes the average reward of generated samples; it is completely unrelated to beam search, which is a deterministic, inference-time decoding heuristic. The proposed risk-seeking policy gradient modifies the fundamental RL training loss to optimize only the top-epsilon quantile of rewards, whereas beam search simply explores multiple highly-probable branches during decoding.

**3. I guess that high difference between the expected and the best performance of the solution set implies high problem difficulty, because it means small change in genotype space can lead to large change in fitness (correlation analysis in GA perspective). Is there a comparison between easy and difficult problem case? Is there a mention about soultion diversity? Can I see the exptectation based reward works as a global mean-field, and risk-seeking reward works as a local search?**
The paper differentiates easy vs. difficult problems based on the presence of unoptimizable structures (like deeply nested trigonometric functions), but it does not formally map expected/best gap purely to ruggedness. Diversity is explicitly encouraged via an entropy regularization bonus added to the loss function. Yes, one can conceptually view expectation-based reward as a global mean-field approach that pulls the entire distribution toward an average fit, whereas risk-seeking reward pulls the policy directly toward high-performing outliers, functioning similarly to an aggressive, directed local search.

**4. Do this method can be modified to fit the constraints without additional fitting step?**
Yes, the constraints regarding mathematical structure (e.g., preventing inverse operations, limiting length) are processed entirely *in situ* during sequence generation. Probabilities of constraint-violating tokens are set to zero before sampling, preventing the need for any post-hoc discarding or additional structural fitting. (However, numerical constants still require an identical continuous optimization fitting step.)

**5. BFGS may fail to converge, and the solver parameter have to be tuned. How it is handled?**
The paper abstracts continuous optimization away by applying BFGS securely within the reward computation loop for each sampled sequence. To prevent convergence failures or excessive computational overhead, they heavily constrain the number of constants allowed per expression (maximum of three) and initialize all constants uniformly to 1.0.

**6. Explain entropy gradient in Algorithm 1.**
The entropy gradient is a regularization term ($\lambda_H \nabla_\theta H(T|\theta)$) that maximizes the entropy of the RNN's token distribution. This mathematically prevents the model from collapsing prematurely into a single deterministic policy, ensuring continuous exploration across the mathematical search space throughout training.

**7. While the sequence is mathematically identical to the expression tree, does the model learn the tree structure? Or does it just learn the sequence? It is not likely that the model learns the tree structure, because the model is not capable of solving logical puzzle.**
The model strictly learns the probabilities of a linear sequence. However, by explicitly feeding the parent and sibling tokens as auxiliary inputs at every generation step, the algorithm heavily biases the sequence model to condition its next prediction directly on the tree's local structural topology.

**8. There are variants of RL framework. On-line, off-line, etc. Categorize the proposed method.**
This is an on-line, model-free, episodic policy gradient reinforcement learning algorithm. The RNN acts as the policy, the sequence acts as the episode, and the optimization happens continuously using immediately sampled batches.

**9. Explain "Risk-seeking policy gradient" with details, preferably using equations.**
Standard policy gradients optimize the expected return: $J_{std}(\theta) = \mathbb{E}_{\tau \sim p(\tau|\theta)}[R(\tau)]$. Because symbolic regression evaluates success entirely on the single best expression found, the expected return is misaligned with the goal. Risk-seeking policy gradient solves this by maximizing the conditional expectation: $J_{risk}(\theta; \epsilon) = \mathbb{E}_{\tau \sim p(\tau|\theta)}[R(\tau) | R(\tau) \ge R_\epsilon(\theta)]$, where $R_\epsilon(\theta)$ is the empirical $(1-\epsilon)$-quantile of rewards in the batch. Only expressions exceeding this threshold contribute to the gradient update.

**10. Briefly explain EPOpt-$\epsilon$ algorithm.**
EPOpt-$\epsilon$ (Ensemble Policy Optimization) is a robust, risk-averse reinforcement learning algorithm designed to train policies that perform well under worst-case scenarios. It optimizes the objective against the bottom $\epsilon$-quantile of rewards. The risk-seeking policy gradient in this paper is the mathematical inverse of EPOpt-$\epsilon$, optimizing the top $\epsilon$-quantile instead.

---

## PA Kamienny 2022

**1. Symbolic and subsymbolic approaches are usually complementary. It seems the author mixes two methods. What is the logical reason that the author had to choose this approach? What is the advantage?**
The authors explicitly combine symbolic tokens (operators like `sin`, `+`) with subsymbolic floating-point tokens (mantissa, exponent) into a single vocabulary to perform end-to-end regression. The logic is that predicting a bare equation skeleton without exact constants creates a highly non-convex search space that causes continuous solvers to fail. Predicting both together guarantees the continuous solver (BFGS) starts from an incredibly close, informed initialization, bypassing non-convex traps.

**2. It is a usual practice to use constants such as 5, 21, 252 in the research stage, and optimize it later. (usually little bit smaller) However, afaik, that's only for small-scale strategy pool or high-frequency strategy. Why didn't the author simply add nonlinearity at the end of the function, and frame it as constant determination problem?**
Framing it purely as an isolated constant determination problem ignores the fact that predicting an accurate mathematical structure is mutually dependent on having approximately correct constants during the evaluation phase. Providing the constants upfront allows the model to predict highly customized and precise skeletons simultaneously, which acts as a powerful prior for the final continuous refinement.

**3. IMHO, embedder and whitened input may limit the application of the model to time-series modelling. Is whitening a big deal?**
Whitening is extremely critical for this Transformer architecture. Without standardizing the mean and variance, the model utterly fails to generalize across unseen datasets because neural representations are incredibly sensitive to absolute coordinate scales. While this enables generalization across generic physical tabular data, you are correct that it could potentially limit raw time-series modelling if the absolute scale or un-normalized trend components carry unreducible semantic value.

**4. Please give me more explanation about attention head analysis presented in figure 3.**
The authors mapped the self-attention weights generated by the encoder's heads across 1-dimensional inputs sorted chronologically. They discovered that different heads specialized in extracting distinct geometric properties: some mapped local correlation (focusing on the geometric diagonal), some identified critical boundary extremes, some highlighted singularities (like $x=0$ in the function $1/x$), and brilliantly, some heads generated highly rhythmic, repeating grid patterns when analyzing $sin(x)$, effectively mirroring a learned, intrinsic Fourier-like frequency analysis module.
