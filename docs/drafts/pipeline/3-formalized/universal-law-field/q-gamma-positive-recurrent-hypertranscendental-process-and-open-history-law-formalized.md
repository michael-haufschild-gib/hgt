# q-Gamma positive recurrent hypertranscendental process and open-history law — Lean certification

- **ID:** ULF-QGPRH-1
- **Paper card:**
  `q-gamma-positive-recurrent-hypertranscendental-process-and-open-history-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.QBinomialTheorem`,
  `GaloisForLFunctions.HTGeometry.QGammaAnalytic`,
  `GaloisForLFunctions.HTGeometry.QDigamma`,
  `GaloisForLFunctions.HTGeometry.QGammaBellSubstitution`,
  `GaloisForLFunctions.HTGeometry.ShiftEliminationEngine`,
  `GaloisForLFunctions.HTGeometry.ShiftEigenrelationEngine`,
  `GaloisForLFunctions.HTGeometry.QShiftField`,
  `GaloisForLFunctions.HTGeometry.QShiftInverse`,
  `GaloisForLFunctions.HTGeometry.QIncrement`,
  `GaloisForLFunctions.HTGeometry.QIncrementAnalytic`,
  `GaloisForLFunctions.HTGeometry.QTranscendence`,
  `GaloisForLFunctions.HTGeometry.QDigammaHypertranscendental`,
  `GaloisForLFunctions.HTGeometry.QGammaHypertranscendental`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveQGammaProcess`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## The certified object

Jackson's q-Gamma function for a fixed nome `0 < q < 1` (`RealEulerNome`), in the two forms the
card needs: the atomic weight sequence `w_n = (q;q)_∞ qⁿ/(q;q)_n` with its exponential response,
and the analytic function `qGammaOn q z = (1−q)^{1−z}(q;q)_∞/(qᶻ;q)_∞` on the half-plane
`qHalfPlane = {Re z > 0}`, where `qGammaOn_eq_qGamma` identifies the two.

## Certified declarations

### §1 — the positive atomic law

`qGammaAtom` (equation (2)), `qGammaResponse`, `qGammaWeight_pos`, `qGammaWeight_le_pow`
(`0 < w_n ≤ qⁿ`, the bound that makes every moment converge), and equation (3)
`qGammaResponse_hasSum`.  The analytic input is `qBinomial_hasSum`, the complex q-binomial theorem
`∑ aⁿ/(q;q)ₙ = 1/(a;q)_∞` for `‖a‖ < 1`, proved from Euler's functional equation
`F(aq) = (1−a)F(a)` (`qBinomialTerm_hasSum_mul`), its iteration (`qBinomialSum_mul_prod`), and
Tannery's theorem (`tendsto_qBinomialSum_mul_qpow`).

### §2 — GNS realization and the operator clause

`QGammaSpace = lp (fun _ : ℕ => ℂ) 2`, `qOmega`, `qOrbit`, `qChar` (equation (7)), `inner_qOrbit`,
equation (10) `qChar_eq_inner`, equation (11) `qChar_kernel_eq_normSq` and `qChar_kernel_nonneg`;
the moment layer `qMomentTerm_summable`, `qMoment`, equation (12) `qMomentMatrix`,
`qMomentMatrix_hasSum`, `qMomentMatrix_quadratic`, equation (13) `qMomentMatrix_posDef`.

Diagonal operators on `ℓ²` are absent from mathlib and were built here: `lpDiagFun`,
`memℓp_lpDiagFun`, `lpDiagLM`, `lpDiagLM_norm_le`, `lpDiagCLM`, `lpDiagCLM_opNorm_le`,
`lpSingleCLM`, `isCompactOperator_lpSingleCLM`, `isCompactOperator_rankOne`,
`isCompactOperator_finset_rankOne`, `lpDiagCLM_trunc_eq_sum`, and `isCompactOperator_lpDiagCLM`.
The q-Gamma resolvent is `qResolventEntry`, `qResolventEntry_mul` (it inverts `X − i`
coordinatewise), `tendsto_norm_qResolventEntry`, `qResolvent`, `isCompactOperator_qResolvent`.

### §3 — recurrence and the open marked lift

`norm_sq_lp`, `norm_qOrbit_sub_qOmega_sq`, equation (15) `exists_qOrbit_near_qOmega` (recurrence at
arbitrarily late integer times, from the corpus's compact-group recurrence
`exists_pow_mem_of_compactSpace` in the torus `Fin (N+1) → Circle` plus the tail bound
`∑_{n>N} w_n → 0`), equation (16) `qLift`, `norm_qLift_sq`, `qMoment_two_pos`, and equation (17)
`norm_qLift_tendsto_atTop`.

### §4 — Pastro's q-analogue of Hölder's theorem

**`qGamma_jet_annihilator_eq_zero`** — no nonzero `P ∈ ℂ[z, Y_0, …, Y_{n+1}]` satisfies
`P(z, Γ_q(z), Γ_q'(z), …, Γ_q^{(n)}(z)) = 0` for every `z` with `Re z > 0`.

The proof runs the shift elimination over the two-variable field `ℂ(z,u) = RatFunc (RatFunc ℂ)`
with `u = qᶻ`, on which the shift is `qShift q : f(z,u) ↦ f(z+1, q·u)`.

*The field layer.*  `qConst`, `qShiftPolyMap`, `qShiftCompHom`, `qShift`, `qShift_injective`,
`qShift_algebraMap`, `qShift_coeff`, `qShift_const`; `ratShift_eq_const_mul_self` and
`shift_scaled_cross_const` (a nonzero `r ∈ ℂ(z)` with `r(z+1) = c·r(z)` forces `c = 1`, by leading
coefficients); `monomial_of_qShift_eigen`, `exists_qShift_eigen_const`, and `qShift_fixed_eq_const`
(every `f` with `f(z+1,qu) = f(z,u)` is a constant).  `evalConst`, `evalConst_qShiftPolyMap`,
`not_both_evalConst_zero`, `finite_evalConst_zero`, and `qShift_sub_self_ne` — no `w` satisfies
`σw − w = D` when the only complex pole of `D` is `u = 1`; the proof clears denominators to
`σP·R·B − P·σR·B = A·σR·R` and evaluates at `1`, at `b/q` for the largest-modulus pole, and at the
smallest nonzero-modulus pole, forcing the contradiction `1 ≤ q < 1`.

*The increments.*  `qLog`, `qIncrNum` (the recursion `A_0 = −(log q)u`,
`A_{j+1} = (log q)u(A_j'(1−u) + (j+1)A_j)`), `qIncrNum_eval_one` (`A_j(1) = −(log q)^{j+1} j!`),
`qIncrNumC`, `qPoleFactor`, `qIncr` (`δ_j = A_j(u)/(1−u)^{j+1}`), `qIncrCombNum`,
`qIncr_combination_eq`, `evalConst_qIncrCombNum_one`, and `qIncr_not_coboundary` — the residue
condition of the elimination engine.

*The analytic identification.*  `qIncrFun`, `hasDerivAt_qIncrFun`, `iteratedDeriv_qShiftIncrement`
(`∂ʲ(−(log q)qᶻ/(1−qᶻ)) = A_j(qᶻ)/(1−qᶻ)^{j+1}` — differentiating the closed form under
`du/dz = (log q)u` reproduces exactly the recursion defining `A_{j+1}`), and
`iteratedDeriv_qDigamma_shift_closed`.

*The transcendence of `qᶻ` over `ℂ(z)`.*  `tendsto_pow_mul_qrpow`, `tendsto_normPoly_mul_qrpow`,
and `exists_qcpow_combination_ne_zero`: the lowest surviving power dominates on `[1,∞)` because
`q^{kx}` decays faster than any polynomial grows.

*The elimination.*  `toQField : ℂ[z][u] → ℂ(z,u)` with `toQField_injective`; `qCoeffEval`
(evaluation at `(z, qᶻ)`), `qIntShift` with `toQField_qIntShift` and `qCoeffEval_qIntShift`;
`exists_qClear` (every element of `ℂ(z,u)` is a fraction of elements of `ℂ[z][u]`, through
`IsLocalization.integerNormalization`); the cleared annihilator set `qAnnihilator` with
`qAnnihilator_sub`, `qAnnihilator_smul`, `qAnnihilator_const` (this is where the transcendence
enters) and `qAnnihilator_shift` (through `qClearedShift`, `map_qClearedShift`,
`qPolyJetEval_qClearedShift`); and, feeding the corpus's abstract engine
`no_shift_stable_annihilatorGen`, the theorem **`annihilatesQDigamma_eq_zero`**: *`qᶻ` and the jets
`ψ_q, ψ_q', ψ_q'', …` are algebraically independent over `ℂ(z)`.*

*The Γ_q-power elimination.*  `qMult` (`M = (1−u)/(1−q)`), `qShiftInv` with `qShiftInv_qShift` and
`qShift_qShiftInv` (the shift is an automorphism), `qShift_eq_qMult_pow_mul_eq_zero` (no nonzero
`r` has `σ(r) = Mᵉ·r` for `e ≥ 1`, because `σ` preserves `u`-degrees while `Mᵉ` raises them), the
abstract `no_shift_eigenrelationGen`, and `qGammaPowerRel_eq_zero`.

### §5 — the exact tilt and entropy law

Equation (21) `qTiltWeight`, `qTiltWeight_pos`, `qTiltWeight_hasSum_one` (the tilt is again a
probability law because `Γ_q(2) = 1`), equation (24) `log_qTiltWeight_div`, equation (22)
`qTilt_hasSum`, equation (23) `qTilt_response_eq`, and equation (25): `qWeightExp_summable`,
`qResponseFun`, `qStrip`, `hasDerivAt_qResponseFun` (term-by-term differentiation on
`−1/2 < Re s < 2`), `qKLTiltBase`, `qKLBaseTilt`, `deriv_qResponseFun_one : F_q'(1) = D(w̃‖w)` and
`deriv_qResponseFun_zero : F_q'(0) = −D(w‖w̃)`.

## New infrastructure absent from mathlib

- The complex q-binomial theorem and its Tannery limit.
- Diagonal and rank-one operators on `ℓ²`, and the compactness of a diagonal operator with entries
  tending to zero.
- The two-variable field `ℂ(z,u)` with the q-shift automorphism, its fixed field, its coboundary
  obstruction, and its `u`-degree obstruction.
- The abstract eigenrelation engine over a shifted field (`ShiftEigenrelationEngine`), which also
  re-proves the classical Hölder eigenrelation step as a special case.
- The whole q-Hölder assembly: nothing about `Γ_q` beyond `qGamma_shift` is in mathlib.

## Scope carried into stage 3

- §2's unbounded-operator clause is certified as the explicit compact diagonal resolvent inverting
  `X − i`; mathlib has no unbounded self-adjoint operator theory in which to state more.
- §3's recurrence (15) is certified at integer times.
- §4 is certified on the half-plane `Re z > 0`, which is where `Γ_q` is defined by the card's
  product.

## Verification

`#print axioms` on `qGamma_jet_annihilator_eq_zero`, `qGammaPowerRel_eq_zero`,
`annihilatesQDigamma_eq_zero`, `exists_qcpow_combination_ne_zero`,
`iteratedDeriv_qDigamma_shift_closed`, `qShift_eq_qMult_pow_mul_eq_zero`, and
`no_shift_eigenrelationGen` reports only `propext`, `Classical.choice`, `Quot.sound`.  No project
postulate, interface hypothesis, or computation proof is used.  The dedicated field umbrella
`GaloisForLFunctions.HTGeometry.UniversalLawField` builds green (11,531 jobs).  Repo-wide lint is
otherwise blocked only by unrelated concurrently created unwired `RHTower` modules and the
generated indexes they keep restaling.
