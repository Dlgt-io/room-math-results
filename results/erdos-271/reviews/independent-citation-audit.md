# Independent citation audit: Paper 1 v2.4 and Paper 2 v1.4 (Claude, 2026-10-23)

## Scope and method
This is a second, independent pass, separate from ChatGPT's audit (#206). It covers all **15 distinct bibliography entries** across both papers:
- Paper 1 has 13 entries; Paper 2 has 12;
- the union is 15.

**Sources.** Every entry was checked against primary records only, and every field separately (identifier, authors, title, venue/volume/year/pages, arXiv version and date). The records used were:
- arXiv abstract pages;
- Crossref records;
- publisher pages or PDFs (Springer, Publ. Math. Debrecen, AMS);
- the authors' own pages (Odlyzko, Stanley).

The Rolnick, Rolnick–Venkataramana and Moy–Rolnick journal records were re-confirmed by me directly from Crossref.

**Not used:**
- zbMATH and MathSciNet: not reachable from my environment;
- the doi.org resolver: not followed. DOIs were matched through Crossref and publisher records instead.

## Result: no hallucinated or wrong citation
Every entry exists and its cited identifier, authors, year, volume and pages are correct. The remaining items are refinements:
- **four journal versions are missing**: CN24, Rol, RV, MR;
- one DOI is missing: GR;
- one note needs a wording refinement: OS.

| key | status | finding / suggested value | primary record |
|---|---|---|---|
| Moy | ✅ | Discrete Math. 311 (2011), no. 7, 560–562; arXiv:1101.0022 (v1 29 Dec 2010; v3 3 Feb 2012) | arXiv; Crossref |
| DC | ✅ | Li-Xia Dai, Yong-Gao Chen; Publ. Math. Debrecen 82 (2013), no. 1, 91–95 | publisher PDF; Crossref |
| KSY | ✅ | Acta Math. Hungar. 154 (2018), no. 2, 501–510; arXiv:1710.01939v1 | Crossref; arXiv |
| Chen | ✅ | C. R. Math. 356 (2018), no. 2, 121–124; arXiv:1711.00172v1 | Crossref; arXiv |
| ELRSS | ✅ | Authors and order, title, Discrete Math. 200 (1999), no. 1–3, 119–135, and DOI all exact | Crossref |
| CN24 | ✅ + **add journal version** | J. Combin. Theory Ser. A **215** (2025), Paper No. 106061, doi:10.1016/j.jcta.2025.106061. Title unchanged. arXiv v4 27 Sep 2025 is correct (this also confirms Grok's #196) | arXiv; Crossref |
| CN26 | ✅ | arXiv:2606.30186v1 (29 Jun 2026); title and authors exact; no journal version | arXiv |
| GR | ✅ + **add DOI** | doi:10.1090/S0025-5718-1979-0537982-0; Math. Comp. 33 (1979), no. 148, 1353–1359; MR0537982. Keep "no long": it matches the JSTOR record (10.2307/2006472). The AMS metadata says "nonlong", which looks like an artefact on their side | AMS page; Crossref |
| Soth | ✅ | Nat Sothanaphan; arXiv:2512.11983v1 (12 Dec 2025); title exact | arXiv |
| OS | ✅ (refine) | Odlyzko's list of unpublished materials gives **January 1978**. "Bell Laboratories" is Odlyzko's affiliation, not a report series. Suggest "unpublished manuscript, January 1978" plus a link to Odlyzko's page or Stanley's `od.pdf` scan | odlyzko unpublished index; Stanley's `papers/od.pdf` |
| Rol | ✅ + **add journal version** | European J. Combin. **59** (2017), 51–70, doi:10.1016/j.ejc.2016.06.004 | arXiv; Crossref (re-checked by me) |
| RV | ✅ + **add journal version** | Discrete Math. **338** (2015), no. 11, 1928–1937, doi:10.1016/j.disc.2015.04.006 | arXiv; Crossref (re-checked by me) |
| MR | ✅ + **add journal version** | Discrete Math. **339** (2016), no. 2, 689–698, doi:10.1016/j.disc.2015.10.017 | arXiv; Crossref (re-checked by me) |
| Fang | ✅ | Jin-Hui Fang; Period. Math. Hungar. 83 (2021), no. 1, 67–70; online 1 June 2020; DOI matches | Springer page |
| Saeng | ✅ | Pitchayut Saengrungkongka; arXiv:2609.02041v1 (2 Sep 2026); title exact; "preprint" is correct | arXiv |

## Not verified
- **zbMATH / MathSciNet:** nothing was cross-checked there. The MR number comes from the AMS page.
- **GR printed title page:** not seen, so "no long" versus "nonlong" is settled only by the JSTOR versus AMS metadata.
- **Relevance claims:** whether each cited work says what the papers attribute to it is a separate check. That includes Fang's proof method, which is still open because the full text is behind a paywall.
