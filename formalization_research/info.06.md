## Work Objective Field Definitions (after removing time-inconsistent fields, manually)

### Author
* author_id, existence of author_id, existence of author_name
* corresponding_author_ids
* institution_id, institution lineage
* institution country, language country, journal country
* institutions_distinct_count, author count : related to social capital

### Time
* paper publication_date 
* OpenAlex created_date, updated_date : needed to detect time-inconsistency

### Location
* host_organization, locations

### Content
* id
* sum of keyword score
* is "review" in title : indexical utility
* reference to unpublished work : may be an indicator of social capital?

### Method - to get visibility
* biblio, language, length of display_name of paper : causes visibility
* open_access, indexed_in : causes visibility, not time-consistent but looks important
* is publication month right before conference : causes visibility
* first year citation : caused by visibility
* type

### Reason - to disrupt or consolidate
* referenced_works_count : related to disruptiveness

### Result
* citation - counts_by_year - cited_by_count : caused by visibility, indexical utility, methodological utility, and novelty


## Citation network

The raw data is openalex work endpoint response dump.

* Preprocessing : 
    * For each work, extract author id list, publish date and citation count by year
    * Using publish year and citation count by year count, infer citation count of each year
    * Update dictionary dict_author_citation[author_id][year] += citation_count
    * Save dict_author_citation to file

* Graph node building : from the data, crate new node for each work, and assign these fields to each node
    * published year 
    * work type
    * id of the work 
    * institutions_distinct_count
    * max( dict_author_citation[aid][pub_year-1] for aid in author_id_list )
    * open_access, indexed_in, language, length of display_name of paper
    * is "review" in title or is "review" in display_name : if true 1 else false 0
    * first year citation count, 10y citation count (do not use dict_author_citation and use cited_by_count directly)
    * error status : if fields are missing or malformed, store -1. else 0
    * referenced_works_count

* Graph edge building : Edges represent citations. assign these fields to each edge.
    * Author's previous work : if intersection of author_id set of citing work and author_id set of cited work is not empty, assign 1 else 0.
    * Institution's previous work : if intersectino of institution_lineage_id is set of citing work and institution_lineage_id set of cited work is not empty, assign 1 else 0.
    * weight : 1/referenced_works_count

build and save the result using networkx. 
also save edgelist.csv and nodelist.csv using pandas 