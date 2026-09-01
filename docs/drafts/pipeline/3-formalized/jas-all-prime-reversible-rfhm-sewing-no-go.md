# JAS all-prime reversible RFHM sewing no-go

- **ID:** JAS-RFHM-REV-NG
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/rh-current-frontier-map.md` · JAS
- **Statement:** Reversible source-domain covariance and literal forward RFHM insertion force every nonzero output coefficient to empty native support.

## Goal

Kill JAS's literal-RFHM reversible sewing branch, including unbounded non-diagonal infinite-support relations.

## Gates

- [x] Exact corpus frontier and external parent-theory audit
- [x] Dependency-closed paper proof
- [x] Lean theorem `not_JASAllPrimeReversibleRFHMSewing`; targeted build and axioms pass

## No-go closure

- **Mechanism:** inverse source step followed by forward insertion returns the source; single-valuedness puts output in every insertion range.
- **Positive survivor:** every nonzero output coefficient has native support `∅`.
- **New insight:** inverse target transport is irrelevant; survival requires abandoning literal RFHM insertion or reversible source covariance.
- **Status:** `[LEAN-PROVED]`; no exact literature collision found through 2026-08.
