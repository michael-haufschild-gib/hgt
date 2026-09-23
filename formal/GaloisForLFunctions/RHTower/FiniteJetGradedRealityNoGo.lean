import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import GaloisForLFunctions.RHTower.GelfondSchneiderProof.AnalyticPart

/-!
# Arbitrarily delayed graded-reality defects

This module formalizes the local analytic core of the finite-jet nonselection theorem.  For every
prescribed depth `N`, an explicit even multiplier is flat at a selected simple zero through order
`N`, while its residue-filled negative logarithmic derivative first breaks reflection symmetry at
the odd order `2N+1`.

The construction is not an arbitrary analytic germ: `flatZeroCompletedFlux` is the actual
residue-filled negative logarithmic derivative of the explicit simple-zero factor

`x * (1 + (x * (2*α+x))^(2N+1))`.

The global order-one aperiodic `cosh` realization is proved on paper in
`finite-jet-graded-reality-nonselection.md`; exact entire-order and aperiodicity formalization remain
outside this local module.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The first forced escape order beyond a prescribed depth. -/
def finiteJetEscapeOrder (N : ℕ) : ℕ := 2 * N + 1

/-- The shift to the selected center of the even multiplier below. -/
def flatLocalFactor (N : ℕ) (α x : ℂ) : ℂ :=
  1 + (x * (2 * α + x)) ^ finiteJetEscapeOrder N

/-- The explicit globally even multiplier, flat at `z=α` to order `2N+1`. -/
def flatEvenMultiplier (N : ℕ) (α z : ℂ) : ℂ :=
  1 + (z ^ (2 : ℕ) - α ^ (2 : ℕ)) ^ finiteJetEscapeOrder N

/-- The analytic unit carrying the first nonzero logarithmic-flux correction. -/
def flatLogFluxUnit (N : ℕ) (α x : ℂ) : ℂ :=
  -(2 * (finiteJetEscapeOrder N : ℂ)) * (α + x) *
      (2 * α + x) ^ (2 * N) / flatLocalFactor N α x

/-- The completed-logarithmic-flux correction introduced by the flat even multiplier. -/
def flatLogFluxCorrection (N : ℕ) (α x : ℂ) : ℂ :=
  x ^ finiteJetEscapeOrder N * flatLogFluxUnit N α x

theorem finiteJetEscapeOrder_pos (N : ℕ) : 0 < finiteJetEscapeOrder N := by
  simp [finiteJetEscapeOrder]

theorem finiteJetEscapeOrder_odd (N : ℕ) : Odd (finiteJetEscapeOrder N) := by
  exact ⟨N, by simp [finiteJetEscapeOrder, two_mul]⟩

theorem lt_finiteJetEscapeOrder (N : ℕ) : N < finiteJetEscapeOrder N := by
  unfold finiteJetEscapeOrder
  omega

@[simp] theorem flatLocalFactor_zero (N : ℕ) (α : ℂ) :
    flatLocalFactor N α 0 = 1 := by
  have hM : finiteJetEscapeOrder N ≠ 0 := (finiteJetEscapeOrder_pos N).ne'
  simp [flatLocalFactor, hM]

theorem flatEvenMultiplier_neg (N : ℕ) (α z : ℂ) :
    flatEvenMultiplier N α (-z) = flatEvenMultiplier N α z := by
  simp [flatEvenMultiplier]

@[simp] theorem flatEvenMultiplier_at_center (N : ℕ) (α : ℂ) :
    flatEvenMultiplier N α α = 1 := by
  have hM : finiteJetEscapeOrder N ≠ 0 := (finiteJetEscapeOrder_pos N).ne'
  simp [flatEvenMultiplier, hM]

theorem flatEvenMultiplier_shift (N : ℕ) (α x : ℂ) :
    flatEvenMultiplier N α (α + x) = flatLocalFactor N α x := by
  unfold flatEvenMultiplier flatLocalFactor
  congr 1
  ring

theorem flatLocalFactor_hasDerivAt (N : ℕ) (α x : ℂ) :
    HasDerivAt (flatLocalFactor N α)
      ((finiteJetEscapeOrder N : ℂ) *
        (x * (2 * α + x)) ^ (2 * N) * (2 * (α + x))) x := by
  have hu : HasDerivAt (fun y : ℂ => y * (2 * α + y)) (2 * (α + x)) x := by
    convert! (hasDerivAt_id x).mul
      ((hasDerivAt_const (x := x) (c := 2 * α)).add (hasDerivAt_id x)) using 1
    all_goals simp
    all_goals ring
  have hp := hu.pow (finiteJetEscapeOrder N)
  have hs := (hasDerivAt_const (x := x) (c := (1 : ℂ))).add hp
  simpa [flatLocalFactor, finiteJetEscapeOrder] using! hs

/-- The correction is exactly `-x` times the logarithmic derivative of the flat factor. -/
theorem flatLogFluxCorrection_eq_neg_mul_logDeriv (N : ℕ) (α x : ℂ) :
    flatLogFluxCorrection N α x =
      -x * deriv (flatLocalFactor N α) x / flatLocalFactor N α x := by
  rw [(flatLocalFactor_hasDerivAt N α x).deriv]
  unfold flatLogFluxCorrection flatLogFluxUnit
  rw [finiteJetEscapeOrder]
  push_cast
  rw [pow_succ', mul_pow]
  ring

theorem flatLogFluxUnit_analyticAt_zero (N : ℕ) (α : ℂ) :
    AnalyticAt ℂ (flatLogFluxUnit N α) 0 := by
  have hP : AnalyticAt ℂ (flatLocalFactor N α) 0 := by
    unfold flatLocalFactor
    fun_prop
  rw [show flatLogFluxUnit N α = fun x : ℂ =>
    -(2 * (finiteJetEscapeOrder N : ℂ)) * (α + x) *
      (2 * α + x) ^ (2 * N) / flatLocalFactor N α x by rfl]
  apply AnalyticAt.div
  · fun_prop
  · exact hP
  · simp

@[simp] theorem flatLogFluxUnit_zero (N : ℕ) (α : ℂ) :
    flatLogFluxUnit N α 0 =
      -(2 * (finiteJetEscapeOrder N : ℂ)) * α * (2 * α) ^ (2 * N) := by
  simp [flatLogFluxUnit]

theorem flatLogFluxUnit_zero_ne {N : ℕ} {α : ℂ} (hα : α ≠ 0) :
    flatLogFluxUnit N α 0 ≠ 0 := by
  rw [flatLogFluxUnit_zero]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply neg_ne_zero.mpr
      apply mul_ne_zero
      · norm_num
      · exact Nat.cast_ne_zero.mpr (finiteJetEscapeOrder_pos N).ne'
    · exact hα
  · exact pow_ne_zero _ (mul_ne_zero (by norm_num) hα)

theorem flatLogFluxCorrection_analyticAt_zero (N : ℕ) (α : ℂ) :
    AnalyticAt ℂ (flatLogFluxCorrection N α) 0 := by
  exact (analyticAt_id.pow _).mul (flatLogFluxUnit_analyticAt_zero N α)

/-- The correction vanishes to exactly the odd order `2N+1`. -/
theorem flatLogFluxCorrection_order {N : ℕ} {α : ℂ} (hα : α ≠ 0) :
    analyticOrderAt (flatLogFluxCorrection N α) 0 = finiteJetEscapeOrder N := by
  change analyticOrderAt
    ((id : ℂ → ℂ) ^ finiteJetEscapeOrder N * flatLogFluxUnit N α) 0 =
      finiteJetEscapeOrder N
  rw [analyticOrderAt_mul (analyticAt_id.pow _)
    (flatLogFluxUnit_analyticAt_zero N α), analyticOrderAt_pow analyticAt_id,
    analyticOrderAt_id]
  have hu : analyticOrderAt (flatLogFluxUnit N α) 0 = 0 :=
    (flatLogFluxUnit_analyticAt_zero N α).analyticOrderAt_eq_zero.mpr
      (flatLogFluxUnit_zero_ne hα)
  rw [hu]
  simp

theorem flatLogFluxCorrection_iteratedDeriv_zero {N n : ℕ} {α : ℂ}
    (hα : α ≠ 0) (hn : n < finiteJetEscapeOrder N) :
    iteratedDeriv n (flatLogFluxCorrection N α) 0 = 0 := by
  have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
    (flatLogFluxCorrection_analyticAt_zero N α) (finiteJetEscapeOrder N)
    (flatLogFluxCorrection_order hα)
  simpa only [iteratedDeriv_eq_iterate] using h.1 n hn

theorem flatLogFluxCorrection_iteratedDeriv_escape_ne_zero {N : ℕ} {α : ℂ}
    (hα : α ≠ 0) :
    iteratedDeriv (finiteJetEscapeOrder N) (flatLogFluxCorrection N α) 0 ≠ 0 := by
  have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
    (flatLogFluxCorrection_analyticAt_zero N α) (finiteJetEscapeOrder N)
    (flatLogFluxCorrection_order hα)
  simpa only [iteratedDeriv_eq_iterate] using h.2

/-- The analytic model of the residue-filled completed logarithmic flux. -/
def finiteJetModelGerm (N : ℕ) (α x : ℂ) : ℂ :=
  -1 + flatLogFluxCorrection N α x

/-- An explicit analytic factor with a simple zero at the local origin. -/
def flatZeroModel (N : ℕ) (α x : ℂ) : ℂ :=
  x * flatLocalFactor N α x

/-- The actual residue-filled negative logarithmic derivative of `flatZeroModel`. -/
def flatZeroCompletedFlux (N : ℕ) (α x : ℂ) : ℂ :=
  if x = 0 then -1
  else -x * deriv (flatZeroModel N α) x / flatZeroModel N α x

theorem flatZeroModel_hasDerivAt (N : ℕ) (α x : ℂ) :
    HasDerivAt (flatZeroModel N α)
      (flatLocalFactor N α x + x *
        ((finiteJetEscapeOrder N : ℂ) *
          (x * (2 * α + x)) ^ (2 * N) * (2 * (α + x)))) x := by
  change HasDerivAt ((fun y : ℂ => y) * flatLocalFactor N α) _ x
  simpa using!
    (hasDerivAt_id x).mul (flatLocalFactor_hasDerivAt N α x)

/-- The explicit residue-filled flux agrees locally with its analytic model. -/
theorem flatZeroCompletedFlux_eventuallyEq_model (N : ℕ) (α : ℂ) :
    flatZeroCompletedFlux N α =ᶠ[𝓝 0] finiteJetModelGerm N α := by
  have hcont : ContinuousAt (flatLocalFactor N α) 0 := by
    unfold flatLocalFactor
    fun_prop
  have hne : ∀ᶠ x : ℂ in 𝓝 0, flatLocalFactor N α x ≠ 0 :=
    hcont.eventually_ne (by simp)
  filter_upwards [hne] with x hxP
  by_cases hx : x = 0
  · subst x
    have hM : finiteJetEscapeOrder N ≠ 0 := (finiteJetEscapeOrder_pos N).ne'
    simp [flatZeroCompletedFlux, finiteJetModelGerm, flatLogFluxCorrection, hM]
  · rw [flatZeroCompletedFlux, if_neg hx, finiteJetModelGerm,
      flatLogFluxCorrection_eq_neg_mul_logDeriv,
      (flatZeroModel_hasDerivAt N α x).deriv,
      (flatLocalFactor_hasDerivAt N α x).deriv]
    unfold flatZeroModel
    field_simp [hx, hxP]
    ring

theorem finiteJetModelGerm_analyticAt_zero (N : ℕ) (α : ℂ) :
    AnalyticAt ℂ (finiteJetModelGerm N α) 0 :=
  analyticAt_const.add (flatLogFluxCorrection_analyticAt_zero N α)

theorem flatZeroCompletedFlux_analyticAt_zero (N : ℕ) (α : ℂ) :
    AnalyticAt ℂ (flatZeroCompletedFlux N α) 0 := by
  exact (finiteJetModelGerm_analyticAt_zero N α).congr
    (flatZeroCompletedFlux_eventuallyEq_model N α).symm

theorem finiteJetModelGerm_iteratedDeriv_eq_reflect_of_le
    {N n : ℕ} {α : ℂ} (hα : α ≠ 0) (hn : n ≤ N) :
    iteratedDeriv n (finiteJetModelGerm N α) 0 =
      iteratedDeriv n (fun x : ℂ => finiteJetModelGerm N α (-x)) 0 := by
  have hnM : n < finiteJetEscapeOrder N := lt_of_le_of_lt hn (lt_finiteJetEscapeOrder N)
  have hcorr := flatLogFluxCorrection_iteratedDeriv_zero hα hnM
  have hg : iteratedDeriv n (finiteJetModelGerm N α) 0 =
      iteratedDeriv n (fun _ : ℂ => (-1 : ℂ)) 0 := by
    change iteratedDeriv n
      ((fun _ : ℂ => (-1 : ℂ)) + flatLogFluxCorrection N α) 0 = _
    have hc : ContDiffAt ℂ n (fun _ : ℂ => (-1 : ℂ)) 0 := contDiffAt_const
    have hr : ContDiffAt ℂ n (flatLogFluxCorrection N α) 0 :=
      (flatLogFluxCorrection_analyticAt_zero N α).contDiffAt
    rw [iteratedDeriv_add hc hr, hcorr, add_zero]
  have hreflect : iteratedDeriv n (fun x : ℂ => finiteJetModelGerm N α (-x)) 0 =
      (-1 : ℂ) ^ n * iteratedDeriv n (finiteJetModelGerm N α) 0 := by
    simpa only [neg_zero, smul_eq_mul] using
      (iteratedDeriv_comp_neg n (finiteJetModelGerm N α) 0)
  rw [hg, hreflect, hg]
  by_cases hn0 : n = 0
  · subst n
    simp
  · simp [iteratedDeriv_const, hn0]

theorem finiteJetModelGerm_iteratedDeriv_ne_reflect_at_escape
    {N : ℕ} {α : ℂ} (hα : α ≠ 0) :
    iteratedDeriv (finiteJetEscapeOrder N) (finiteJetModelGerm N α) 0 ≠
      iteratedDeriv (finiteJetEscapeOrder N)
        (fun x : ℂ => finiteJetModelGerm N α (-x)) 0 := by
  let M := finiteJetEscapeOrder N
  have hcorr := flatLogFluxCorrection_iteratedDeriv_escape_ne_zero (N := N) hα
  have hM0 : M ≠ 0 := (finiteJetEscapeOrder_pos N).ne'
  have hg : iteratedDeriv M (finiteJetModelGerm N α) 0 =
      iteratedDeriv M (flatLogFluxCorrection N α) 0 := by
    change iteratedDeriv M
      ((fun _ : ℂ => (-1 : ℂ)) + flatLogFluxCorrection N α) 0 = _
    have hc : ContDiffAt ℂ M (fun _ : ℂ => (-1 : ℂ)) 0 := contDiffAt_const
    have hr : ContDiffAt ℂ M (flatLogFluxCorrection N α) 0 :=
      (flatLogFluxCorrection_analyticAt_zero N α).contDiffAt
    rw [iteratedDeriv_add hc hr, iteratedDeriv_const, if_neg hM0, zero_add]
  have hreflect : iteratedDeriv M (fun x : ℂ => finiteJetModelGerm N α (-x)) 0 =
      (-1 : ℂ) ^ M * iteratedDeriv M (finiteJetModelGerm N α) 0 := by
    simpa only [neg_zero, smul_eq_mul] using
      (iteratedDeriv_comp_neg M (finiteJetModelGerm N α) 0)
  rw [hreflect, (finiteJetEscapeOrder_odd N).neg_one_pow, neg_one_mul, hg]
  intro h
  have hz : iteratedDeriv M (flatLogFluxCorrection N α) 0 = 0 := by
    have htwo : (2 : ℂ) * iteratedDeriv M (flatLogFluxCorrection N α) 0 = 0 := by
      calc
        (2 : ℂ) * iteratedDeriv M (flatLogFluxCorrection N α) 0 =
            iteratedDeriv M (flatLogFluxCorrection N α) 0 +
              iteratedDeriv M (flatLogFluxCorrection N α) 0 := by ring
        _ = 0 := eq_neg_iff_add_eq_zero.mp h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact hcorr hz

/-- **Arbitrarily delayed defect.**  For every finite depth there is an explicit analytic
residue-filled completed-flux germ whose reflected jet agrees through that depth and fails at the
later odd order `2N+1`. -/
theorem exists_analytic_reflection_germs_same_finite_jet_not_same_later (N : ℕ) :
    ∃ (g : ℂ → ℂ) (M : ℕ),
      AnalyticAt ℂ g 0 ∧ N < M ∧ Odd M ∧
      (∀ n ≤ N, iteratedDeriv n g 0 = iteratedDeriv n (fun x => g (-x)) 0) ∧
      iteratedDeriv M g 0 ≠ iteratedDeriv M (fun x => g (-x)) 0 := by
  refine ⟨flatZeroCompletedFlux N 1, finiteJetEscapeOrder N,
    flatZeroCompletedFlux_analyticAt_zero N 1, lt_finiteJetEscapeOrder N,
    finiteJetEscapeOrder_odd N, ?_, ?_⟩
  · intro n hn
    have heq := (flatZeroCompletedFlux_eventuallyEq_model N 1).iteratedDeriv_eq n
    have href := (flatZeroCompletedFlux_eventuallyEq_model N 1).comp_tendsto
      (by simpa using (continuous_neg.tendsto (0 : ℂ)))
    have hrefd :
        iteratedDeriv n (fun x : ℂ => flatZeroCompletedFlux N 1 (-x)) 0 =
          iteratedDeriv n (fun x : ℂ => finiteJetModelGerm N 1 (-x)) 0 := by
      simpa only [Function.comp_apply] using! href.iteratedDeriv_eq n
    rw [heq, hrefd]
    exact finiteJetModelGerm_iteratedDeriv_eq_reflect_of_le (by norm_num) hn
  · have heq := (flatZeroCompletedFlux_eventuallyEq_model N 1).iteratedDeriv_eq
      (finiteJetEscapeOrder N)
    have href := (flatZeroCompletedFlux_eventuallyEq_model N 1).comp_tendsto
      (by simpa using (continuous_neg.tendsto (0 : ℂ)))
    have hrefd :
        iteratedDeriv (finiteJetEscapeOrder N)
            (fun x : ℂ => flatZeroCompletedFlux N 1 (-x)) 0 =
          iteratedDeriv (finiteJetEscapeOrder N)
            (fun x : ℂ => finiteJetModelGerm N 1 (-x)) 0 := by
      simpa only [Function.comp_apply] using!
        href.iteratedDeriv_eq (finiteJetEscapeOrder N)
    rw [heq, hrefd]
    exact finiteJetModelGerm_iteratedDeriv_ne_reflect_at_escape (by norm_num)

end

end RHTower
