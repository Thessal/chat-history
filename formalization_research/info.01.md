# OpenAlex API Endpoints Summary

The OpenAlex API provides access to a variety of scholarly entities through specific REST endpoints. All requests should be made to the base URL: `https://api.openalex.org`.

Below is a summary of the main API endpoints (entities) available, based on the OpenAlex API Reference:

| Entity Name | Base URL Path | Description |
| :--- | :--- | :--- |
| **Works** | `/works` | Scholarly documents such as articles, books, and datasets. |
| **Authors** | `/authors` | Individual researchers with disambiguated identities. |
| **Sources** | `/sources` | Venues where works are published, including journals, repositories, and conferences. |
| **Institutions** | `/institutions` | Universities and other research organizations. |
| **Topics** | `/topics` | Research area classifications (replaces the legacy "Concepts" entity). |
| **Keywords** | `/keywords` | Short phrases extracted from works. |
| **Publishers** | `/publishers` | Organizations that publish scholarly content. |
| **Funders** | `/funders` | Agencies that provide funding for research. |
| **Awards** | `/awards` | Specific research grants and awards. |
| **Domains** | `/domains` | The top-level hierarchy for research topics. |
| **Fields** | `/fields` | The second-level hierarchy for research topics. |
| **Subfields** | `/subfields` | The third-level hierarchy for research topics. |
| **SDGs** | `/sdgs` | Work classifications based on the UN Sustainable Development Goals. |
| **Countries** | `/countries` | Geographic entities representing nations. |
| **Continents** | `/continents` | Geographic entities representing continents. |
| **Languages** | `/languages` | Classifications based on the language of the work. |
| **Work Types** | `/work-types` | An enumeration of the different types of scholarly works available. |

### Key Notes:
* **Topics vs Concepts:** The API has transitioned from using "Concepts" to a newer "Topics" system, which includes a structured hierarchy (Domains → Fields → Subfields → Topics).
* **Utilities:** In addition to entities, the API offers utility endpoints for Autocomplete (`/autocomplete`), Rate Limit Status, and Changefiles (to track data updates).
