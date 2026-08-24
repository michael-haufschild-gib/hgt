import GaloisForLFunctions.RHTower.ReflectedBiHeatPhaseFinitePartExpansion
import GaloisForLFunctions.RHTower.DeningerMeyerXiSpectralInclusion
import GaloisForLFunctions.RHTower.ArchimedeanGammaModule
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Multiplicity tomography of the reflected bi-heat channels

At an actual Xi divisor point, every completed-channel jet below the exact divisor multiplicity
vanishes.  At the multiplicity itself, Leibniz collapses to the completed-zeta top jet times the
unchanged aperture character.  Each of the two channels is therefore nonzero at that first grade.
The regular product has no contribution through that grade.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Left completed response after subtracting the universal anomaly. -/
def reflectedBiHeatLeftResponse (x : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 * reflectedCompletedLambda z) * ((x : ℂ) ^ ((z - 1) / 2))

/-- Right completed response after subtracting the universal anomaly. -/
def reflectedBiHeatRightResponse (x : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 * reflectedCompletedLambda z) * ((x : ℂ) ^ (-z / 2))

/-- Zeta-bearing part of the reflected small-aperture model. -/
def reflectedBiHeatZetaResponse (x : ℝ) (z : ℂ) : ℂ :=
  reflectedBiHeatLeftResponse x z + reflectedBiHeatRightResponse x z
    + riemannZeta z * riemannZeta (1 - z)

/-- Local affine chain rule for reflection about `1/2`. -/
theorem iteratedDeriv_comp_one_sub_of_analyticAt :
    ∀ (n : ℕ) {f : ℂ → ℂ} {z : ℂ}, AnalyticAt ℂ f (1 - z) →
      iteratedDeriv n (fun w => f (1 - w)) z =
        (-1 : ℂ) ^ n * iteratedDeriv n f (1 - z) := by
  intro n
  induction n with
  | zero =>
      intro f z _
      simp [iteratedDeriv_zero]
  | succ n ih =>
      intro f z hf
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hdiff : ∀ᶠ u in nhds (1 - z), DifferentiableAt ℂ f u := by
        have h := (hf.contDiffAt (n := (1 : ℕ∞))).eventually (by simp)
        filter_upwards [h] with u hu
        exact hu.differentiableAt (by simp)
      have hpre : ∀ᶠ w in nhds z, DifferentiableAt ℂ f (1 - w) :=
        (continuousAt_const.sub continuousAt_id).tendsto hdiff
      have hderiv : deriv (fun w : ℂ => f (1 - w)) =ᶠ[nhds z]
          fun w : ℂ => -deriv f (1 - w) := by
        filter_upwards [hpre] with w hw
        have hinner : HasDerivAt (fun u : ℂ => 1 - u) (-1) w := by
          simpa using (hasDerivAt_id w).const_sub 1
        simpa [Function.comp_def] using (hw.hasDerivAt.comp w hinner).deriv
      rw [hderiv.iteratedDeriv_eq n]
      change iteratedDeriv n (-(fun w : ℂ => deriv f (1 - w))) z = _
      rw [iteratedDeriv_neg, ih hf.deriv]
      ring

/-- Additivity of zero orders, vanishing part. -/
theorem complex_iteratedDeriv_mul_eq_zero_before_add_order
    {m n k : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ k f z) (hg : ContDiffAt ℂ k g z)
    (hfvanish : ∀ j < m, iteratedDeriv j f z = 0)
    (hgvanish : ∀ j < n, iteratedDeriv j g z = 0)
    (hk : k < m + n) :
    iteratedDeriv k (fun w => f w * g w) z = 0 := by
  have hfun : (fun w => f w * g w) = f * g := rfl
  rw [hfun, iteratedDeriv_mul hf hg]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≤ k := by
    simpa [Finset.mem_range] using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  by_cases him : i < m
  · rw [hfvanish i him]
    simp
  · have hkn : k - i < n := by omega
    rw [hgvanish (k - i) hkn]
    simp

/-- Additivity of zero orders, first surviving term. -/
theorem complex_iteratedDeriv_mul_at_add_order
    {m n : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ (m + n) f z) (hg : ContDiffAt ℂ (m + n) g z)
    (hfvanish : ∀ j < m, iteratedDeriv j f z = 0)
    (hgvanish : ∀ j < n, iteratedDeriv j g z = 0) :
    iteratedDeriv (m + n) (fun w => f w * g w) z =
      (Nat.choose (m + n) m : ℂ) * iteratedDeriv m f z * iteratedDeriv n g z := by
  have hfun : (fun w => f w * g w) = f * g := rfl
  rw [hfun, iteratedDeriv_mul hf hg]
  rw [Finset.sum_eq_single m]
  · rw [Nat.add_sub_cancel_left]
  · intro i hi him
    have hi_le : i ≤ m + n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rcases lt_or_gt_of_ne him with hi | hi
    · rw [hfvanish i hi]
      simp
    · have hsub : m + n - i < n := by omega
      rw [hgvanish (m + n - i) hsub]
      simp
  · simp

/-- Lightweight one-sided Leibniz collapse. -/
theorem complex_iteratedDeriv_mul_of_left_vanishing_below
    (m : ℕ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ m f z) (hg : ContDiffAt ℂ m g z)
    (hvanish : ∀ j < m, iteratedDeriv j f z = 0) :
    iteratedDeriv m (fun w => f w * g w) z = iteratedDeriv m f z * g z := by
  have hprod : (fun w => f w * g w) = f * g := rfl
  rw [hprod, iteratedDeriv_mul hf hg]
  rw [Finset.sum_eq_single m]
  · simp [iteratedDeriv_zero]
  · intro i hi him
    have hi' : i < m := by
      rw [Finset.mem_range] at hi
      omega
    rw [hvanish i hi']
    simp
  · simp

theorem contDiffAt_Gammaℝ_of_pos_re {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ContDiffAt ℂ n Complex.Gammaℝ s := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hpow : Differentiable ℂ (fun z : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-z / 2)) := by
    intro z
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z / 2) z).const_cpow
      (Or.inl hpi)
  have hhalf : AnalyticAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
  have hgamma : AnalyticAt ℂ Complex.Gamma (s / 2) := by
    apply GaloisForLFunctions.analyticAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.div_re, Complex.natCast_re, Complex.neg_re] at hre
    norm_num at hre
    linarith [hs, Nat.cast_nonneg (α := ℝ) m]
  have hgammaComp : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    simpa [Function.comp_def] using hgamma.comp (f := fun z : ℂ => z / 2) hhalf
  rw [show Complex.Gammaℝ = fun z : ℂ =>
      ((Real.pi : ℝ) : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) by
        funext z
        rw [Complex.Gammaℝ_def]]
  exact (hpow.contDiff.contDiffAt.mul hgammaComp.contDiffAt)

theorem contDiffAt_riemannZeta_at_xiDivisorSupport
    (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n riemannZeta (rho : ℂ) := by
  have hrho := xi_divisor_support_re_mem_open_unit rho
  have hne : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [hrho.2]
  exact (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hne).contDiffAt

/-- Exact top zeta jet, derived directly from equality of Xi and zeta analytic orders. -/
theorem iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity_from_order
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) ≠ 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [hstrip.2]
  have horder : analyticOrderAt xi (rho : ℂ) =
      analyticOrderAt riemannZeta (rho : ℂ) :=
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have hzetaFinite : analyticOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
    rw [← horder]
    exact xi_orderAt_ne_top (rho : ℂ)
  have hm : ((xiSupportMultiplicity rho : ℕ) : ℕ∞) =
      analyticOrderAt riemannZeta (rho : ℂ) := by
    rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat, horder]
    exact ENat.coe_toNat hzetaFinite
  intro htop
  have hall : ∀ i < xiSupportMultiplicity rho + 1,
      iteratedDeriv i riemannZeta (rho : ℂ) = 0 := by
    intro i hi
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | hieq
    · exact iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho hil
    · simpa [hieq] using htop
  have hle : ((xiSupportMultiplicity rho + 1 : ℕ) : ℕ∞) ≤
      analyticOrderAt riemannZeta (rho : ℂ) :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticOn_riemannZeta (rho : ℂ) hne1)).mpr hall
  rw [← hm] at hle
  exact (by omega : ¬ xiSupportMultiplicity rho + 1 ≤ xiSupportMultiplicity rho)
    (by exact_mod_cast hle)

theorem analyticAt_riemannZeta_one_sub_xiDivisorSupport
    (rho : XiDivisorSupport) :
    AnalyticAt ℂ riemannZeta (1 - (rho : ℂ)) := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith [(xi_divisor_support_re_mem_open_unit rho).1]

theorem contDiffAt_riemannZeta_one_sub_at_xiDivisorSupport
    (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n (fun z : ℂ => riemannZeta (1 - z)) (rho : ℂ) := by
  have hinner : AnalyticAt ℂ (fun z : ℂ => 1 - z) (rho : ℂ) := by fun_prop
  have hcomp := (analyticAt_riemannZeta_one_sub_xiDivisorSupport rho).comp
    (f := fun z : ℂ => 1 - z) hinner
  simpa [Function.comp_def] using hcomp.contDiffAt (n := (n : ℕ∞))

theorem iteratedDeriv_riemannZeta_one_sub_eq_zero_before_supportMultiplicity
    (rho : XiDivisorSupport) {j : ℕ} (hj : j < xiSupportMultiplicity rho) :
    iteratedDeriv j (fun z : ℂ => riemannZeta (1 - z)) (rho : ℂ) = 0 := by
  rw [iteratedDeriv_comp_one_sub_of_analyticAt j
    (analyticAt_riemannZeta_one_sub_xiDivisorSupport rho),
    ← xiZeroReflectEquiv_apply]
  have hj' : j < xiSupportMultiplicity (xiZeroReflectEquiv rho) := by
    rwa [xiSupportMultiplicity_reflect]
  rw [iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
    (xiZeroReflectEquiv rho) hj', mul_zero]

theorem iteratedDeriv_riemannZeta_one_sub_at_supportMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho)
        (fun z : ℂ => riemannZeta (1 - z)) (rho : ℂ) =
      (-1 : ℂ) ^ xiSupportMultiplicity rho *
        iteratedDeriv (xiSupportMultiplicity (xiZeroReflectEquiv rho))
          riemannZeta (xiZeroReflectEquiv rho : ℂ) := by
  rw [iteratedDeriv_comp_one_sub_of_analyticAt (xiSupportMultiplicity rho)
    (analyticAt_riemannZeta_one_sub_xiDivisorSupport rho),
    ← xiZeroReflectEquiv_apply, xiSupportMultiplicity_reflect]

theorem iteratedDeriv_riemannZeta_one_sub_ne_zero_at_supportMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho)
        (fun z : ℂ => riemannZeta (1 - z)) (rho : ℂ) ≠ 0 := by
  rw [iteratedDeriv_riemannZeta_one_sub_at_supportMultiplicity]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity_from_order
      (xiZeroReflectEquiv rho))

/-- The regular--regular product has the paper's exact order `2m`. -/
theorem iteratedDeriv_reflectedBiHeatRegularProduct_eq_zero_before_twiceMultiplicity
    (rho : XiDivisorSupport) {j : ℕ} (hj : j < 2 * xiSupportMultiplicity rho) :
    iteratedDeriv j (fun z : ℂ => riemannZeta z * riemannZeta (1 - z))
        (rho : ℂ) = 0 := by
  rw [show 2 * xiSupportMultiplicity rho =
      xiSupportMultiplicity rho + xiSupportMultiplicity rho by ring] at hj
  exact complex_iteratedDeriv_mul_eq_zero_before_add_order
    (contDiffAt_riemannZeta_at_xiDivisorSupport rho j)
    (contDiffAt_riemannZeta_one_sub_at_xiDivisorSupport rho j)
    (fun k hk => iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho hk)
    (fun k hk =>
      iteratedDeriv_riemannZeta_one_sub_eq_zero_before_supportMultiplicity rho hk)
    hj

theorem iteratedDeriv_reflectedBiHeatRegularProduct_at_twiceMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (2 * xiSupportMultiplicity rho)
        (fun z : ℂ => riemannZeta z * riemannZeta (1 - z)) (rho : ℂ) =
      (Nat.choose (2 * xiSupportMultiplicity rho) (xiSupportMultiplicity rho) : ℂ) *
        iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) *
        iteratedDeriv (xiSupportMultiplicity rho)
          (fun z : ℂ => riemannZeta (1 - z)) (rho : ℂ) := by
  have htwo : 2 * xiSupportMultiplicity rho =
      xiSupportMultiplicity rho + xiSupportMultiplicity rho := by ring
  rw [htwo]
  exact complex_iteratedDeriv_mul_at_add_order
    (contDiffAt_riemannZeta_at_xiDivisorSupport rho _)
    (contDiffAt_riemannZeta_one_sub_at_xiDivisorSupport rho _)
    (fun k hk => iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho hk)
    (fun k hk =>
      iteratedDeriv_riemannZeta_one_sub_eq_zero_before_supportMultiplicity rho hk)

theorem iteratedDeriv_reflectedBiHeatRegularProduct_ne_zero_at_twiceMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (2 * xiSupportMultiplicity rho)
        (fun z : ℂ => riemannZeta z * riemannZeta (1 - z)) (rho : ℂ) ≠ 0 := by
  rw [iteratedDeriv_reflectedBiHeatRegularProduct_at_twiceMultiplicity]
  have hchoose : (Nat.choose (2 * xiSupportMultiplicity rho)
      (xiSupportMultiplicity rho) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega :
      xiSupportMultiplicity rho ≤ 2 * xiSupportMultiplicity rho)).ne'
  exact mul_ne_zero
    (mul_ne_zero hchoose
      (iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity_from_order rho))
    (iteratedDeriv_riemannZeta_one_sub_ne_zero_at_supportMultiplicity rho)

theorem contDiffAt_reflectedCompletedLambda_at_xiDivisorSupport
    (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n reflectedCompletedLambda (rho : ℂ) := by
  have hrho := xi_divisor_support_re_mem_open_unit rho
  rw [show reflectedCompletedLambda = fun z : ℂ =>
      riemannZeta z * Complex.Gammaℝ z by
        funext z
        rw [reflectedCompletedLambda]
        ring]
  exact (contDiffAt_riemannZeta_at_xiDivisorSupport rho n).mul
    (contDiffAt_Gammaℝ_of_pos_re hrho.1 n)

theorem iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity
    (rho : XiDivisorSupport) {j : ℕ} (hj : j < xiSupportMultiplicity rho) :
    iteratedDeriv j reflectedCompletedLambda (rho : ℂ) = 0 := by
  have hrho := xi_divisor_support_re_mem_open_unit rho
  have hfun : reflectedCompletedLambda = fun z : ℂ =>
      riemannZeta z * Complex.Gammaℝ z := by
    funext z
    rw [reflectedCompletedLambda]
    ring
  rw [hfun, complex_iteratedDeriv_mul_of_left_vanishing_below j
    (contDiffAt_riemannZeta_at_xiDivisorSupport rho j)
    (contDiffAt_Gammaℝ_of_pos_re hrho.1 j)]
  · rw [iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho hj,
      zero_mul]
  · intro k hk
    exact iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho
      (lt_trans hk hj)

theorem iteratedDeriv_reflectedCompletedLambda_at_supportMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) reflectedCompletedLambda (rho : ℂ) =
      iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) *
        Complex.Gammaℝ (rho : ℂ) := by
  have hrho := xi_divisor_support_re_mem_open_unit rho
  have hfun : reflectedCompletedLambda = fun z : ℂ =>
      riemannZeta z * Complex.Gammaℝ z := by
    funext z
    rw [reflectedCompletedLambda]
    ring
  rw [hfun]
  exact complex_iteratedDeriv_mul_of_left_vanishing_below (xiSupportMultiplicity rho)
    (contDiffAt_riemannZeta_at_xiDivisorSupport rho _)
    (contDiffAt_Gammaℝ_of_pos_re hrho.1 _)
    (fun j hj => iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho hj)

theorem iteratedDeriv_reflectedCompletedLambda_ne_zero_at_supportMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) reflectedCompletedLambda (rho : ℂ) ≠ 0 := by
  rw [iteratedDeriv_reflectedCompletedLambda_at_supportMultiplicity]
  exact mul_ne_zero
    (iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity_from_order rho)
    (GaloisForLFunctions.Gammaℝ_ne_zero
      (xi_divisor_support_re_mem_open_unit rho).1)

theorem contDiffAt_reflectedBiHeatLeftCharacter
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n (fun z : ℂ => ((x : ℂ) ^ ((z - 1) / 2))) (rho : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hdiff : Differentiable ℂ (fun z : ℂ => ((x : ℂ) ^ ((z - 1) / 2))) := by
    intro z
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (z - 1) / 2) z).const_cpow
      (Or.inl hx0)
  exact hdiff.contDiff.contDiffAt

theorem contDiffAt_reflectedBiHeatRightCharacter
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n (fun z : ℂ => ((x : ℂ) ^ (-z / 2))) (rho : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hdiff : Differentiable ℂ (fun z : ℂ => ((x : ℂ) ^ (-z / 2))) := by
    intro z
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z / 2) z).const_cpow
      (Or.inl hx0)
  exact hdiff.contDiff.contDiffAt

theorem iteratedDeriv_reflectedBiHeatLeftResponse_eq_zero_before_supportMultiplicity
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < xiSupportMultiplicity rho) :
    iteratedDeriv j (reflectedBiHeatLeftResponse x) (rho : ℂ) = 0 := by
  have hfun : reflectedBiHeatLeftResponse x = fun z : ℂ =>
      reflectedCompletedLambda z *
        (1 / 2 * ((x : ℂ) ^ ((z - 1) / 2))) := by
    funext z
    rw [reflectedBiHeatLeftResponse]
    ring
  rw [hfun, complex_iteratedDeriv_mul_of_left_vanishing_below j
    (contDiffAt_reflectedCompletedLambda_at_xiDivisorSupport rho j)
    (contDiffAt_const.mul (contDiffAt_reflectedBiHeatLeftCharacter hx rho j))]
  · rw [iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity rho hj,
      zero_mul]
  · intro k hk
    exact iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity rho
      (lt_trans hk hj)

theorem iteratedDeriv_reflectedBiHeatRightResponse_eq_zero_before_supportMultiplicity
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < xiSupportMultiplicity rho) :
    iteratedDeriv j (reflectedBiHeatRightResponse x) (rho : ℂ) = 0 := by
  have hfun : reflectedBiHeatRightResponse x = fun z : ℂ =>
      reflectedCompletedLambda z *
        (1 / 2 * ((x : ℂ) ^ (-z / 2))) := by
    funext z
    rw [reflectedBiHeatRightResponse]
    ring
  rw [hfun, complex_iteratedDeriv_mul_of_left_vanishing_below j
    (contDiffAt_reflectedCompletedLambda_at_xiDivisorSupport rho j)
    (contDiffAt_const.mul (contDiffAt_reflectedBiHeatRightCharacter hx rho j))]
  · rw [iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity rho hj,
      zero_mul]
  · intro k hk
    exact iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity rho
      (lt_trans hk hj)

theorem iteratedDeriv_reflectedBiHeatLeftResponse_at_supportMultiplicity
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) (reflectedBiHeatLeftResponse x) (rho : ℂ) =
      (1 / 2 * iteratedDeriv (xiSupportMultiplicity rho) reflectedCompletedLambda (rho : ℂ)) *
        ((x : ℂ) ^ (((rho : ℂ) - 1) / 2)) := by
  have hfun : reflectedBiHeatLeftResponse x = fun z : ℂ =>
      reflectedCompletedLambda z *
        (1 / 2 * ((x : ℂ) ^ ((z - 1) / 2))) := by
    funext z
    rw [reflectedBiHeatLeftResponse]
    ring
  rw [hfun, complex_iteratedDeriv_mul_of_left_vanishing_below (xiSupportMultiplicity rho)
    (contDiffAt_reflectedCompletedLambda_at_xiDivisorSupport rho _)
    (contDiffAt_const.mul (contDiffAt_reflectedBiHeatLeftCharacter hx rho _))]
  · ring
  · exact fun j hj =>
      iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity rho hj

theorem iteratedDeriv_reflectedBiHeatRightResponse_at_supportMultiplicity
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) (reflectedBiHeatRightResponse x) (rho : ℂ) =
      (1 / 2 * iteratedDeriv (xiSupportMultiplicity rho) reflectedCompletedLambda (rho : ℂ)) *
        ((x : ℂ) ^ (-(rho : ℂ) / 2)) := by
  have hfun : reflectedBiHeatRightResponse x = fun z : ℂ =>
      reflectedCompletedLambda z *
        (1 / 2 * ((x : ℂ) ^ (-z / 2))) := by
    funext z
    rw [reflectedBiHeatRightResponse]
    ring
  rw [hfun, complex_iteratedDeriv_mul_of_left_vanishing_below (xiSupportMultiplicity rho)
    (contDiffAt_reflectedCompletedLambda_at_xiDivisorSupport rho _)
    (contDiffAt_const.mul (contDiffAt_reflectedBiHeatRightCharacter hx rho _))]
  · ring
  · exact fun j hj =>
      iteratedDeriv_reflectedCompletedLambda_eq_zero_before_supportMultiplicity rho hj

theorem iteratedDeriv_reflectedBiHeatLeftResponse_ne_zero_at_supportMultiplicity
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) (reflectedBiHeatLeftResponse x) (rho : ℂ) ≠ 0 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [iteratedDeriv_reflectedBiHeatLeftResponse_at_supportMultiplicity hx]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num)
      (iteratedDeriv_reflectedCompletedLambda_ne_zero_at_supportMultiplicity rho))
    (by
      intro hzero
      rw [Complex.cpow_eq_zero_iff] at hzero
      exact hx0 hzero.1)

theorem iteratedDeriv_reflectedBiHeatRightResponse_ne_zero_at_supportMultiplicity
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) (reflectedBiHeatRightResponse x) (rho : ℂ) ≠ 0 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [iteratedDeriv_reflectedBiHeatRightResponse_at_supportMultiplicity hx]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num)
      (iteratedDeriv_reflectedCompletedLambda_ne_zero_at_supportMultiplicity rho))
    (by
      intro hzero
      rw [Complex.cpow_eq_zero_iff] at hzero
      exact hx0 hzero.1)

/-- Closed actual-divisor capstone: both completed channels vanish to exactly the Xi multiplicity
and their scale-order difference records horizontal displacement from the self-dual wall. -/
theorem reflectedBiHeatMultiplicityTomography_capstone :
    ∀ (rho : XiDivisorSupport) (x : ℝ), 0 < x →
      (∀ j < xiSupportMultiplicity rho,
        iteratedDeriv j (reflectedBiHeatLeftResponse x) (rho : ℂ) = 0) ∧
      (∀ j < xiSupportMultiplicity rho,
        iteratedDeriv j (reflectedBiHeatRightResponse x) (rho : ℂ) = 0) ∧
      iteratedDeriv (xiSupportMultiplicity rho)
          (reflectedBiHeatLeftResponse x) (rho : ℂ) ≠ 0 ∧
      iteratedDeriv (xiSupportMultiplicity rho)
          (reflectedBiHeatRightResponse x) (rho : ℂ) ≠ 0 ∧
      (∀ j < 2 * xiSupportMultiplicity rho,
        iteratedDeriv j (fun z : ℂ => riemannZeta z * riemannZeta (1 - z))
          (rho : ℂ) = 0) ∧
      iteratedDeriv (2 * xiSupportMultiplicity rho)
          (fun z : ℂ => riemannZeta z * riemannZeta (1 - z))
          (rho : ℂ) ≠ 0 ∧
      reflectedBiHeatLeftScaleOrder (rho : ℂ) -
          reflectedBiHeatRightScaleOrder (rho : ℂ) = (rho : ℂ).re - 1 / 2 := by
  intro rho x hx
  exact ⟨fun j hj =>
      iteratedDeriv_reflectedBiHeatLeftResponse_eq_zero_before_supportMultiplicity hx rho hj,
    fun j hj =>
      iteratedDeriv_reflectedBiHeatRightResponse_eq_zero_before_supportMultiplicity hx rho hj,
    iteratedDeriv_reflectedBiHeatLeftResponse_ne_zero_at_supportMultiplicity hx rho,
    iteratedDeriv_reflectedBiHeatRightResponse_ne_zero_at_supportMultiplicity hx rho,
    fun j hj =>
      iteratedDeriv_reflectedBiHeatRegularProduct_eq_zero_before_twiceMultiplicity rho hj,
    iteratedDeriv_reflectedBiHeatRegularProduct_ne_zero_at_twiceMultiplicity rho,
    reflectedBiHeat_scaleOrder_difference (rho : ℂ)⟩

end

end RHTower
