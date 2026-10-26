# RH ⇔ every escape state has positive gauge mass

- **ID:** acg-gauge-mass-criterion-2026-10-26
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ArithmeticCorrelationGeometry README §9 topic 6; cards acg-escape-spectral, acg-gauge-mass
- **Statement:** RH holds iff for every damping `0 < ε < 1/2` every actual common cofactor limit `L`
  of the damped Möbius receiver has positive gauge mass `inf_d d·K_L(d,d)` (then it equals one).

## Proof
(⇒) RH gives `Θ = 1/2`, so every `ε > 0` is admissible; bounded energy gives mass one.

(⇐) Suppose a zero `ρ`, `1/2 < β = Re ρ < 1`.
1. *Translation.* If `E_ε(T) ≤ C(T+1)^κ`, then `Σ|A_ε(n)| n^{−b−1} < ∞` for `b > (1+κ)/2`
   (Abel summation of `A²/(n(n+1))` against `n^{−γ}`, `κ < γ < 2b−1`, and AM–GM), so
   `Φ(s) = Σ A_ε(n)(n^{−s}−(n+1)^{−s})` is holomorphic on `Re s > (1+κ)/2`. On `(1−ε,1)`,
   `Φ(σ) = ζ(σ)(1/ζ(σ+ε) − 1/ζ(1+ε))`. Hence `H(s) = R(s+ε)(Φ(s)+ζ(s)/ζ(1+ε)) − (s+ε−1)ζ(s)`,
   `R(w)=(w−1)ζ(w)` entire, vanishes on the convex strip `(1+κ)/2 < Re s < 1`; at `s = ρ−ε` with
   `Re ρ > (1+κ)/2+ε`: `ζ(ρ−ε) = 0`.
2. *Some damping has power growth.* Otherwise every `ε ∈ (0, β−1/2)` is subpower, so `ρ−ε` is a
   zero for all such `ε`; these zeros accumulate at `ρ−(β−1/2)/2`, contradicting isolated zeros of
   `R`. So some `ε` and `κ > 0` have `E_ε(T)/(T+1)^κ` unbounded.
3. *Record times.* Choose `R_m ↑` with `E(M)/(M+1)^κ ≤ E(R_m)/(R_m+1)^κ` for `M ≤ R_m`.
4. *Zero mass.* Along horizons `R_m − 1` an actual limit `L` exists (ADR). By the fibre sandwich,
   `d·K_L(d,d) ≤ lim E(⌊(R+1)/d⌋)/E(R) ≤ ((⌊(R+1)/d⌋+1)/(R+1))^κ ≤ (2/d)^κ`, so the mass is `0`.

## Lean
To formalize: `ArithmeticCorrelationGeometry/SubpowerReceiverEnergyTranslatesZeros.lean` (steps 1–2),
`ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean` (steps 3–4, equivalence).
