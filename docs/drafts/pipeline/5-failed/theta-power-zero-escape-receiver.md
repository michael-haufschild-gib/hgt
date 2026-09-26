# Zero-escape receiver in the theta-power family

- **ID:** theta-power-zero-escape-receiver
- **Stage:** 5-failed
- **Type:** FALSIFIED (unrenormalized) / CIRCULAR (renormalized)
- **Source:** 3-formalized/theta-power-transcendental-offline-zeros.md (off-line zeros for transcendental a; openness).
- **Statement:** `H(a) = inf{|Re w| : Λ_a(w) = 0, 0 < |Im w| < 1/2}`; conjectured sandwich
  RH ∧ simple zeros ⟹ `H(a) → ∞` as `a → 0⁺` ⟹ RH.

## Goal
An RH receiver on a family whose members `a > 0` have ℚ-independent frequencies (Kronecker/Fejér machinery in Lean),
so that a lower bound on the height of the Kronecker-created off-line zeros would transfer to ξ.

## Attack and verdict
1. **Unrenormalized (`Λ_a = thetaPowerXiC a`): FALSE as an RH criterion.** `Λ_a = ¼𝓜[F_a(iy)](z)`, `z = ¼ − iw/2`,
   subtracts nothing at the cusp; `F_a(iy) = 2^a e^{−παy}(1 + O(e^{−πy}))`, `α = a/4`. Folding with the S-law,
   `Λ_a(w) = 2^{a−2}[E^{−z}Γ(z) + E^{z−½}Γ(½−z)] + β_a(w)`, `E = πα`, `β_a` bounded on compacts of the strip uniformly
   in small `a`. With `L = log(1/E)` the main term is `e^{L/4}[Γ(¼+ζ)e^{ζL} + Γ(¼−ζ)e^{−ζL}]`, `ζ = z − ¼`; the two
   terms are conjugate on the line and one dominates by `e^{|Im w|L}` off it. Hence for every compact `K` of the strip
   all zeros of `Λ_a` in `K` are real for small `a`: `H(a) → ∞` unconditionally. `Λ_a` does not tend to ξ (it grows like
   `a^{−1/4}`); the RH content of ξ is invisible behind the cusp constant.
2. **Renormalized (`Ξ̃_a = Λ_a − cusp term → ξ`-transform): CIRCULAR.** Locally uniform convergence transfers fixed-box
   zero statements both ways (Hurwitz persistence of off-line zeros; a pair of conjugate zeros converging to a real point
   forces a double zero). The premise "no off-line zeros of `Ξ̃_a` with `|Re w| ≤ M` for `a < a(M)`" is RH ∧ simplicity up
   to height `M`. The `a > 0` structure (independent frequencies) cannot survive the limit; any lower bound `φ(a) → ∞`
   is RH. Heuristically the true scale is set by Lehmer pairs (Rodgers–Tao mechanism): this family is a modular
   analogue of the de Bruijn–Newman flow, with zero slack at `a = 0`.

## No-go closure
- **Exact killing mechanism:** (1) cusp-constant dominance `E^{−Re z}` with conjugate Γ-pair on the line;
  (2) fixed-box transfer under locally uniform convergence.
- **Strongest positive survivor:** *local real-rootedness at the degenerate end.* For every compact `K ⊂ {|Im w| < 1/2}`
  there is `a₀ > 0` such that for `0 < a < a₀` every zero of `Λ_a` in `K` is real (and simple, asymptotically at the
  lattice `arg Γ(¼ + iu/2) + (u/2)log(1/(πa/4)) ∈ π/2 + πℤ`).
- **Paper proof:** decomposition above; `|A(w) + A(−w)| ≥ c e^{L/4}` for `Im w ≥ δ/L` (`A(w) = E^{−z}Γ(z)`, ratio
  `|Γ(z)/Γ(½−z)| ≥ 1 − C Im w`, `e^{vL} ≥ 1 + vL`); for `0 < Im w₀ < δ/L` a zero `w₀` forces the zero `w̄₀`, and along the
  vertical segment `Λ_a′ = −i 2^{a−3}[A(w)(L + ψ(z)) − A(−w)(L + ψ(½−z))] + β_a′ ≈ −i 2^{a−2} L A(w₀)`, so
  `Re(conj(−iA(w₀))·Λ_a′) > 0` and `Λ_a(w₀) ≠ Λ_a(w̄₀)`.
- **New insight:** the family's approach to ξ is not a perturbation: in the transform normalization the cusp constant is
  the leading term, and the only RH-relevant limit is the renormalized one, where the family is a Newman-type flow.
- **Status:** paper proof complete; Lean in progress (RHTower/ThetaPowerSmallParameterRealZeros).

## Log
- 2026-09-26 — receiver stated, unrenormalized form falsified (unconditional escape), renormalized form circular;
  survivor = local real-rootedness at small `a`.
