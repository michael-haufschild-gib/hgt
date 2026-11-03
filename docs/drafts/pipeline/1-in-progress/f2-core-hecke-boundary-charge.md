# F2 — the raw Hecke image of a PM core carries a boundary charge

- **Stage:** 1-in-progress
- **Conjecture:** Every upper-resonant PM core has a nonzero lower-cusp trace after the actual source `T₂`. Thus its raw Hecke image leaves whole-axis Haar `L²`, including at critical-line resonances. Subtracting that one boundary trace restores finite whole-Haar energy.
- **Purpose:** Determine the boundary channel required to attach the closed Cauchy reflection to the actual Mayer–Hecke family.

## Candidate exact trace

Set `w=2s`, `q=2^(−w)`, `Z=ζ(w−1)`. The existing inversion law, the Hecke correction at `1`, and `periodValue(w,1)=2Z` give the candidate formula

`core_s(2)=Z/(w−1) · (w−2−4q)`.

The small-endpoint estimate makes the other three branches vanish as `a→0+`, so

`T₂,s core_s(a) → q core_s(1/2)=core_s(2)`.

The shifted zeta factor is nonzero in `0<Re w<1`. If `w−2=4·2^(−w)` with `Re w>0`, `Im w>0`, the modulus identity forces `Im w<4`. Since `4log2<π`, the right side has negative imaginary part while the left side has positive imaginary part. Hence the candidate trace is nonzero.

## Positive survivor to prove

With `c_s=core_s(2)`, prove

`T₂,s core_s − c_s·1_(0,1) ∈ L²((0,∞),da/a)`.

Near zero, the resonant endpoint estimate bounds the three vanishing branches by `O(a^(1−2 Re s))`; local differentiability near `1/2` controls the shifted branch after its trace is removed. The existing upper cusp estimate controls infinity. This gives an exact one-channel decomposition, rather than discarding the boundary term.

## Gaps

Verify the displayed trace formula and its nonvanishing, then formalize the divergence and renormalized remainder. The whole-Haar window admission theorem is being checked separately. These claims concern unweighted Haar space; they do not exclude the weighted Lewis carrier or prove Weil positivity.
