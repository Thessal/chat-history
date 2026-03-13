## Work Objective Field Definitions

### Author
* author_id, existence of author_id, existence of author_name
* corresponding_author_ids
* institution_id, institution lineage
* author country, institution country, language country, journal country
* institutions_distinct_count, author count : related to social capital

### Time
* paper publication_date 
* OpenAlex created_date, updated_date

### Location
* primary_location
* host_organization, host_organization_lineage
* locations, locations_count

### Content
* id
* display_name of paper
* display_name of journal
* primary_topic, keywords, concepts
* Is there misalignment in topics
* sum of keyword score
* is "review" in title, Percentage of Books in the Reference : indexical utility
* reference to unpublished work : may be an indicator of social capital?

### Method - to get visibility
* biblio, publication month, open_access, indexed_in, language, length of display_name of paper : causes visibility
* is publication month right before conference : causes visibility
* first year citation : caused by visibility
* count of ISSNs
* type
* referenced_works

### Reason - to disrupt or consolidate
* referenced_works_count : related to disruptiveness

### Result
* citation_normalized_percentile, counts_by_year, fwci, cited_by_percentile_year : caused by visibility, indexical utility, methodological utility, and novelty
* cited_by_count