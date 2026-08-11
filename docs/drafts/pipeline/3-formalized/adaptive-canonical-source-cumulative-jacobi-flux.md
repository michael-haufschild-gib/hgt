# Canonical adaptive source and cumulative Jacobi-flux law

- **ID:** adaptive-canonical-source-cumulative-jacobi-flux
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Actual inverse-Hankel `P^sharp` has forced shifted-Xi velocity, produces completed arithmetic source `2h_nE_n` in positive chamber, extends by division-free norm flux to first singular face, and there classifies next PSD extension through first even Padé defect.

## Gates

- [x] 0 → 1: hostile conjecture/failure loop recorded
- [x] 1 → 2: dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3: unconditional Lean proofs; direct checks and targeted builds green; axiom audit PASS
- [ ] 3 → 4: specialist novelty review and standalone exposition

## Exact results `[PROVED HERE]`

Let `s_y(k)=Re m_k(y)`, `H_n(y)=(s_y(i+j))`, `t_n(y)=(s_y(i+n))`, and

`P_n^sharp(y)=X^n-H_n(y)⁻¹t_n(y)`.

1. Shifted-Xi terminal flux and inverse-matrix jet force

   `d(H_n⁻¹)/dy=-H_n⁻¹H_n'H_n⁻¹`,

   `d(-H_n⁻¹t_n)/dy=-(d(H_n⁻¹)/dy·t_n+H_n⁻¹t_n')`.

   Every coefficient derivative is formalized.  Terminal monic velocity is zero.

2. Under only `H_(n+2)(y)≻0`, canonical solve equals finite Gram--Schmidt polynomial.  Therefore
   completed adaptive arithmetic producer selected before formation satisfies

   `S_mix^sharp(w,P_n^sharp)=2h_nE_n>0`

   and completed adaptive packet itself equals `2h_nE_n`.  No orientation map or fixed reporter.

3. In positive chamber actual norm and odd current obey

   `h_n'=(2a_n-(2n+1)α_n)h_n`,

   `B_n'=-2h_nE_n+2h_na_n'`.

   More sharply, under only `det H_n ≠ 0`, including first `H_(n+1)` singular face,

   `N_n'=Φ_n=2a_nN_n-(2n+1)B_n`.

   At flat face `N_n=0`, `B_n=R_n`, hence `N_n'=-(2n+1)R_n`.

4. Quotient derivative of `α_n=B_n/h_n` cancels `a_n'` in

   `C_n=-2a_n+α_n=2Σ_(j<n)α_j+α_n`.

   Exact law:

   `C_n'=-D_n`,

   `D_n=2Σ_(j<n)α_j²+α_n²+4Σ_(j<n)β_j+2(n+1)(β_n+β_(n+1))>0`.

   Hence literal derivative of actual cumulative Jacobi flux is strictly negative throughout each
   finite positive chamber.

5. First singular face has exact source-side classifier.  If `R_n ≠ 0`, then
   `H_(n+2)` is not PSD.  If `R_n = 0`, completed admission-sensitive packet satisfies

   `A_completed^sharp=2(n+1)Δ_(2n+2)`,

   `Φ_n'=2(2n+1)(n+1)Δ_(2n+2)`,

   `H_(n+2) ⪰ 0 ↔ Δ_(2n+2) ≥ 0 ↔ A_completed^sharp ≥ 0`.

## Failed conjectures

- Ordinary odd-current monotonicity: false; `a_n'` survives.
- Monicity kills connection: false; `XP_n` detects degree `n-1` tangent.
- Local primitive `B_n-2h_na_n`: false; leaves `-2a_nh_n'`.
- Sign single `a_n'`: unnecessary and not established.  Cumulative trace is invariant that cancels it.
- First-face inverse-Hankel blow-up: false at degree `n`; admission denominator is `H_n`, still
  positive definite when `H_(n+1)` first becomes singular.  Only quotient `α_n=B_n/N_n` blows.
- Sign completed source from lower finite face: impossible in general; first even successor defect
  is a free new coordinate.  Required sign input must be cofinal/arithmetic, not finite reporting.

## Lean certificate

- `HTGeometry.AdaptiveOrthogonalNormJacobiFlow`
  - `momentInner_monicOrtho_adaptiveOrthoNormCompanion`
  - `momentFunctional_X_shiftedEuler_one_sq_monicOrtho`
- `HTGeometry.MonicMomentAdmissionNormTransport`
  - `momentInner_monicMomentAdmission_lower_eq_zero`
  - `momentFunctional_X_shiftedEuler_one_sq_monicMomentAdmission`
- `RHTower.XiShiftedCanonicalAdmissionConnection`
  - `hasDerivAt_xiShiftedCanonicalAdmissionCoefficient`
  - `hasDerivAt_xiShiftedCanonicalAdmissionCurve`
  - `xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho`
  - `hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_jacobiEnergy`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow`
  - `hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux`
  - `xiShiftedCanonicalAdmissionCumulativeJacobiDissipation_pos`
  - `xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace`
  - `deriv_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_neg`
  - `xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy`
  - `xiShiftedCompletedMomentAggregate_canonicalAdaptiveOddPacket_eq_jacobiEnergy`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_completedAggregate_of_flatTangent`
  - `xiShiftedCanonicalAdmission_firstFace_preemption_or_completedSource`
- `RHTower.XiShiftedCanonicalAdmissionSingularSourceLaw`
  - `xiShiftedCompletedMomentAggregate_canonicalFlatTangent_eq_evenPadeDefect`
  - `xiShiftedMomentHankelMatrix_succ_posSemidef_iff_evenPadeDefect_nonneg_of_flatTangent`
  - `xiShiftedCanonicalAdmission_succ_posSemidef_iff_completedSource_nonneg_of_flatTangent`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_evenPadeDefect_of_flatTangent`

## Remaining boundary

First singular face is now classified exactly and degree-`n` inverse-Hankel blow-up is eliminated.
Nonzero odd remainder preempts next block; tangency lands on first even rank-one filling coordinate.
Remaining exact open core is cofinal: exclude unbounded higher-contact flat plateaux/degree escape,
or prove actual shifted-Xi arithmetic controls first later odd defect uniformly across parity lifts.
No fixed finite admission packet can supply this because even successor coordinate is freely
variable under preservation of all lower face data.  RH is not yet proved.

## Log

- 2026-08-11 — paper proof and unconditional Lean formalization completed without computation.
- 2026-08-11 — targeted builds PASS for both new modules and corrected null-gauge producer. Axiom
  audit reports only `propext`, `Classical.choice`, `Quot.sound`. Global lint remains red solely on
  pre-existing unreachable umbrella modules and pre-existing `sorry` in
  `RHTower/DeningerMeyerOscDomination.lean:88`; no finding-module lint debt.
- 2026-08-11 — division-free norm flux and singular canonical completed-source classifier proved in
  Lean.  First-face extension/blow-up alternative replaced by exact odd-preemption/even-rank-fill
  law.  Open core moved to cofinal parity-lift degree escape.
