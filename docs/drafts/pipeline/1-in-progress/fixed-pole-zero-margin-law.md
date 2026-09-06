# The fixed exponential-pole Weil criterion has zero asymptotic margin

- **ID:** `fixed-pole-zero-margin-law`
- **Stage:** 1-in-progress (paper law closed; Lean positive survivor built; bridge to the corpus pole entry pending)
- **Type:** LAW (CANNOT-323 / MUST-226) + THEOREM (Lean, the sharp constant of the diagonal entry)
- **Parent:** `weil-two-pole-compression-prime-error.md` (Route O fixed-pole criterion,
  `riemannHypothesis_iff_primeGammaPoleInequality`), `weil-pole-direct-sign-attack.md`
- **Computation:** `2-fully-proven/computations/fixed-pole-parity-profile/`

## Statement

With `κ = −γ − log 2π`, `X = e^{2a}`, `L(t) = −log(1−e^{−t})`, the corpus's exact entries are

`A(a) = κ·2sinh a − e^a + (1−2a)e^{−a} + B₁(a) − 2e^a E_M(2a) + 2e^{−a}ψ(X)`,
`C(a) = κ·2a + 2a² + (2sinh a)² + B₀(a) − Σ_{2≤n≤X}Λ(n)(1+1/n)(2a − log n)`,

and RH ⟺ `|C(a)| ≤ A(a)` for all `a > 0` (even energy `A + C`, odd energy `A − C`).

**Law.** Unconditionally,
`A(a) = c₀ e^a − 2e^a(E_M(2a) + γ) + 2e^{−a}(ψ(X) − X) + r(a)`, `c₀ = 2 + γ − log 4π = 0.046192…`,
`|r(a)| ≤ (10a + 20)e^{−a}` for `a ≥ 1`. On paper `c₀ = Σ_ρ 1/(ρ(1−ρ)) = 2Σ_ρ 1/ρ` (Hadamard
product of `ξ`), and by the explicit formula `C(a) = Σ_ρ X^ρ/ρ² + O(1)`. Hence, writing
`ρ = ½ + iγ`, `θ_ρ = arg ρ`, under RH

`(A ± C)(a) = e^a Σ_{γ>0} 2(1 ± cos(2aγ − 2θ_ρ))/|ρ|² + O(a²)`,

and off RH the terms `X^ρ/ρ²` with `Re ρ > ½` dominate. The criterion is the triangle inequality
`|Σ_ρ e^{2iaγ}/ρ²| ≤ Σ_ρ|ρ|^{−2}` to leading order: mean and oscillation amplitude of the relative
margin coincide; the margin is a Bohr almost-periodic function of `a` with infimum zero whenever
finitely many ordinates can be phase-aligned (Kronecker under linear independence).

## Derivation of the constant

`B₁(a) = (e^a/2)∫_0^{2a} e^{−t}L(2t)dt + e^{−a}∫_0^{2a}e^t(L(t) − L(2t)/2)dt`. The first integral
has the closed antiderivative `F(t) = G(e^{−t})`, `G(u) = (u−1)log(1−u) + (u+1)log(1+u) − 2u`,
`G'(u) = log(1−u²)`, `G(1) = 2log 2 − 2`, so `∫_0^{2a} = 2 − 2log 2 + G(e^{−2a})`, `|G(u)| ≤ 6u` on
`[0,½]`. The second integral lies in `[0, 2B₀ + 4a] ⊂ [0, 4a + 18]`. Then
`c₀ = κ − 1 + (1 − log 2) + 2γ + 2` from: `κ·2sinh a → κe^a`, `−e^a`, `B₁ → (1 − log 2)e^a`,
`−2e^aE_M → +2γe^a − 2e^a(E_M + γ)` (Mertens' constant for the full von Mangoldt sum is `−γ`),
`2e^{−a}ψ(X) → 2e^a + 2e^{−a}(ψ − X)`.

## Consequences

- The corpus's admitted diagonal bound `|A| ≤ K_A e^a` (`K_A ≈ 30`) overstates the room by three
  orders of magnitude; the true main term is `0.046 e^a`, and the cross fluctuation has the same
  amplitude. The parallel Route O attack (`H(a) ≥ 2a[ψ + M₁] − A − C_sm` at even minima) is a
  one-sided `√X` Chebyshev bound with the *sharp* constant `Σ_ρ|ρ|^{−2}`; sieve, mean-value, or any
  input with a constant loss cannot supply it.
- Numerically (`a ≤ 8`) both parity energies stay positive with relative margins in `[0.029, 0.063]`
  around the mean `0.0462`; `even + odd = 2A` exactly; `C(8) = −16.65` vs `−16.70` from 400 zeros.
- The positivity of `c₀` itself is not derivable from mathlib's bounds `½ < γ < ⅔`
  (`c₀ > 0 ⟺ γ > log 4π − 2 = 0.5310`); a sharper certified lower bound for `γ` would be needed to
  certify the sign of the main term in Lean.

## Lean (`RHTower.PoleBoundaryLogSharpConstant`, built and wired; see Log)

Mathlib-only module; declarations listed in the Log entry below. The bridge to the corpus's
`ccmWeilPoleDiagonal` is pending (heavy import closure).

## Gates

- G1 (paper): constant identification `c₀ = Σ_ρ 1/(ρ(1−ρ))` and `C = Σ_ρ X^ρ/ρ² + O(1)` — classical
  (Hadamard product, explicit formula for `∫_1^X ψ(u)du/u`); not in Lean.
- G2 (Lean): the module builds, axioms clean, wired. Then stage 3.
- G3 (open, RH-strength): any proof of the parity signs must reproduce `c₀` exactly from the source.

## Log

- 2026-09-06 — Lean positive survivor built and wired: `RHTower.PoleBoundaryLogSharpConstant`
  (Mathlib-only, 2771 jobs, axioms `[propext, Classical.choice, Quot.sound]`). Contents:
  `poleBoundaryLog` (`L`), `poleSelfKernelPrimitive` (`G`), `hasDerivAt_…` (`G' = log(1−u²)`),
  `poleSelfKernelAntiderivative` (`F = G∘exp(−·)`), continuity and `F(0) = 2log 2 − 2`,
  `integral_exp_neg_mul_poleBoundaryLog_two_mul` (improper FTC), `abs_poleSelfKernelPrimitive_le`
  (`|G(u)| ≤ 6u`), `poleBoundaryLog_le_log_one_add_sub_log` (`L ≤ log(1+t) − log t`),
  `intervalIntegrable_poleBoundaryLog`, `integral_poleBoundaryLog_le` (`∫_0^T L ≤ T + 1`),
  `poleSelfDifferenceIntegral_bounds` (`0 ≤ J ≤ 8s + 2`), `poleSelfBoundaryPrimitive_eq`,
  `abs_poleSelfBoundaryPrimitive_sub_le` (`|B₁ − (1 − log 2)e^s| ≤ (8s + 5)e^{−s}`),
  `poleDiagonalExplicit_eq_sharp` (exact decomposition with `poleSharpConstant = 2 + γ − log 4π`),
  `abs_poleDiagonalRemainder_le` (`(10s + 20)e^{−s}`), `abs_poleDiagonalExplicit_div_exp_sub_sharp_le`.
  The definitions `poleBoundaryLog`, `poleSelfBoundaryPrimitive`, `reciprocalMangoldtError` are
  syntactically the corpus's `ccmGammaPoleBoundaryLog`, `ccmGammaPoleSelfBoundaryPrimitive`,
  `ccmReciprocalMangoldtError`; the bridge `poleDiagonalExplicit a = ccmWeilPoleDiagonal ⟨a,_⟩` is a
  `rfl`/`rw [ccmWeilPoleDiagonal_eq_error, ccmGammaPoleSelfBoundaryMass_eq_primitive]` in a consumer
  importing `CCMRestrictedWeilFullPoleMatrix`; not compiled here because that closure was being
  rebuilt by concurrent agents (missing oleans).
- Worst-aperture search (`2-fully-proven/computations/fixed-pole-worst-aperture/`): MUST-228.
- Mechanism loop for the source sign (all attempts): Schur decoupling of the pole block from the
  constrained block — CIRCULAR (constrained positivity is RH); aperture-window averaging — BRIDGE
  (MUST-227, removes constant sharpness only); window/sieve-level prime sums — INSIGNIFICANT
  (exponent unchanged); Stieltjes form `E₊ = Gamma − ∫K_a dR` with `R` the `√`-normalised prime
  error — REDISCOVERED (von Koch); two-aperture Gram kernels — BRIDGE (Weil positivity again).
  No mechanism bounding the exponent exists in the corpus or the literature; the loop's output is
  the pair of laws MUST-227/228 and the Lean constant.
- 2026-09-06 (iii) — Structural reading recorded in STATUS (CANNOT-324, MUST-229): self-pairings of
  the pole vectors are PNT-level (`e^{a(2β−1)} = o(e^a)` for `β < 1`), the cross pairing is the whole
  RH content, and the criterion is the archimedean Weil bound with regularised genus
  `c₀ = Σ_ρ 1/(ρ(1−ρ))`: `|N(X) − M(X)| ≤ c₀√X` versus `|#C(F_q) − (q+1)| ≤ 2g√q`. Next Lean target
  (Mathlib-only if the zeta Laurent constant is available): unconditional positivity of the pole
  self-energy `A(a) > 0` for all large `a` from Mertens' constant `−γ` and the prime number theorem
  with error term (corpus `PNTPlus`); this is a PNT-level theorem, recorded as such.
- 2026-09-06 (iv) — Two further Mathlib-only modules, built and wired (3598/3600 jobs, axioms clean):
  `RHTower.MertensVonMangoldtEulerConstant` — the regular part `ζ(s) − 1/(s−1)` updated by `γ` is
  analytic at `1` (removable singularity), `−ζ'(s)/ζ(s) − 1/(s−1) → −γ` (`tendsto_neg_logDeriv_riemannZeta_sub_one_div`),
  measurability and PNT bound of `chebyshevError`, `e^{−cu^{1/10}} ≤ 20!/(c^{20}u²)`,
  integrability of `1/(t log²t)` and of `E(t)/t²` on `(1,∞)`, real summability of `Λ(n)n^{−s}`,
  the Abel/Mellin identity `Σ Λ(n)n^{−s} = s∫_1^∞ ψ t^{−s−1}` (`tsum_vonMangoldt_div_rpow_eq`),
  `∫_1^∞ E(t)t^{−2}dt = −γ − 1` by dominated convergence against the zeta side, and
  **`tendsto_sum_vonMangoldt_div_sub_log : Σ_{n≤x}Λ(n)/n − log x → −γ`** (Mertens' theorem with the
  Euler constant; absent from Mathlib and the corpus).
  `RHTower.PoleSelfEnergyLimit` — `reciprocalMangoldtError → −γ`,
  **`tendsto_poleDiagonalExplicit_div_exp : A(a)e^{−a} → 2 + γ − log 4π`**, `γ > 0.545`
  (`eulerMascheroniSeq 15`), `log(3/2) < 0.4065`, `log 4π < 2.534`, `poleSharpConstant_pos`, and
  `eventually_poleDiagonalExplicit_pos` (the pole self-energy is positive for all large apertures,
  unconditionally). This closes the first clause of CANNOT-324 in Lean: the self-pairing of the
  archimedean pole vector is PNT-level. Traps: `Nat.measurable_floor` needs `(R := ℝ)`;
  `Real.hasDerivAt_rpow_const` wants `x ≠ 0` via `ne_of_gt`; `rw [show -s = 1 + (-s-1) …]` also
  rewrites inside `-s - 1` (use a helper `t * t^(-s-1) = t^(-s)`); `field_simp` may close a goal
  so a trailing `ring` errors; `div_eq_div_iff` argument order matches the goal's denominators.
