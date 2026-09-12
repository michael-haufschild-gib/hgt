# Route L: localization with the complete source forcing retained

- **ID:** RH-L-C58
- **Stage:** 1-in-progress
- **Target:** Full-source physical/cyclic reader agreement at the original anchor.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH. C57 tested analytic transfers without deriving the central equality. The current test keeps the actual source forcing in every localized equation before attempting injectivity.

## In progress

1. Deep whole-corpus/method search: `route-l-localized-source-equation-search.json`.
2. The actual local Green equation is `G_m-G_(m+1)=f_m`. Its full jump is the original periodization, not zero. The damping-two source has a nonzero jump coefficient at every original prime mode. An argument using a homogeneous localized equation must first derive cancellation of this forcing.
3. Finite prime-circle coercivity has an exact positive gap, but its extension to the full coupled Kummer/horizontal source has not been proved. The resolved Green composite cancels its two internal defects; this is not componentwise vanishing.
4. Broad newest-first arXiv `localization` found September 10 papers on joint cusp correction and quantum symmetry conversion. Inspect their actual hypotheses and source constructions before proposing a transfer.

No new Lean theorem has been established.
