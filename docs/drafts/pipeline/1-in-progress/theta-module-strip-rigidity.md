# Strip rigidity of ξ in the module θ₃·ℝ[h]

- **ID:** theta-module-strip-rigidity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** 3F/route2-charge-line-hardy-rigidity (real-axis version); route2.md step 3 (the winding must see strip zeros).
- **Statement:** For every P ∈ ℝ[X] with deg P ≥ 1, the transform Ξ_P of θ₃P(h) has only finitely many zeros in |Im z| ≤ ½. Hence ξ is the unique member of θ₃·ℝ[h] (up to scale) with infinitely many zeros in the closed critical strip.

## Goal
Upgrade Hardy rigidity (real zeros) to the strip. Route 2's winding counts strip zeros; this shows the infinite strip population is a zero-charge phenomenon: any nonzero cusp-1 charge expels all but finitely many zeros from every horizontal strip of width < 2.

## Approach
At w = u+iv, |v| ≤ ½: Ξ_j(w) = −(w²+¼)e^{−wβ}∫e^{−ius}e^{vs}T_j(s−iβ)ds. The weight e^{vs} is positive real: the
saddle factorization and Re-positivity survive unchanged (factor ∈ [1−t³, 1+2t²] on the window); the far field gains
e^{|s|/2} against e^{−|s|}. Ξ on the same line: |Ξ(w)| ≤ e^{−uβ}∫e^{|x|/2}|S(x+iβ)|dx. Dominance of the top pole order ⇒ no zeros for Re w ≥ U; evenness + compactness ⇒ finiteness.

## Log
- 2026-09-26 — frozen.
