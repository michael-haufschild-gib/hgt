# Frozen experiment: complete corrected BM Einstein source

Exploration only; not paper-proof or Lean evidence.

Question: after replacing the previous angular correction's scalar orbit block
by its ingoing-regular trace-preserving completion, what are all sixteen actual
quadratic Einstein components? Which higher scalar-jet terms survive, which
constraints vanish, and what explicit forcing remains at the horizon? These
coefficients are unknown; another check of generic nonzero forcing is not the
target. The result determines the ansatz and source data for the physical inverse.

Keep the exact full fundamental scalar/coexact-vector first metric and independent
SS, VV, S+V runs from the previous experiment. Set the second metric coefficient to
`k_tt=0`, `k_tr=B²*aS²*C*S²`, `k_rr=2*k_tr/f`,
`k_tA=f*B²*aS*aV*s*(s+1)/(2r³)*S*(coexact S)_A` and its symmetric entries.
Here `C=s²*((s+1)²-4r²)/(8r⁴)`, `f=r²-1`. All unlisted components vanish.
Retain every ordered derivative, the scalar eigen-equation and differentiated
identities. Evaluate at y=1 and B=1 only after differentiating.

Compute the exact inverse expansion through epsilon² including k, all Christoffel
derivatives, both connection products and all Ricci components. Validate all
background/first equations. Then trace-reverse Ricci+3g to the full cosmological
Einstein source; its zeroth and first coefficients vanish by those checks.
Extract SV by subtraction. Also express the full epsilon² source in ingoing
coordinates and evaluate its rational coefficient at r=1. Regularity is predicted
from the displayed coordinate formulas and is a validation check; the horizon
forcing values and full angular decomposition are unknown.

Run on RunPod only, three worker processes, five-minute hard limit, no parameter
sweep. Save exact expressions, free-jet monomials, consistency checks, timings,
code and checksums. If symbolic work exceeds the limit, retain partial outputs
and reason from them; do not start an hours-long run. Any selected identity must
subsequently be derived from the corpus and proved independently in Lean.
