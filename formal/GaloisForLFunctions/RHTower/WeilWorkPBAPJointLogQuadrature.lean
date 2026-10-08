import GaloisForLFunctions.RHTower.WeilWorkPBAPJointShortPrefix
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Complex logarithmic-grid quadrature, with derivatives on the fixed cutoff. -/

open Complex MeasureTheory Real Set Filter Finset
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem integer_quadrature {g : ℝ → ℂ} {n m : ℕ} (hnm : n ≤ m)
    {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ x ∈ Icc (n:ℝ) m, DifferentiableAt ℝ g x)
    (hb : ∀ x ∈ Icc (n:ℝ) m, ‖deriv g x‖ ≤ D) :
    ‖(∑ j ∈ Finset.Ico n m, g j)-∫ x in (n:ℝ)..m, g x‖ ≤ ((m-n:ℕ):ℝ)*D := by
  have hs (j : ℕ) (hj : j ∈ Finset.Ico n m) : Icc (j:ℝ) (j+1) ⊆ Icc (n:ℝ) m := by
    have hj' := Finset.mem_Ico.mp hj
    intro x hx
    refine ⟨(Nat.cast_le.mpr hj'.1).trans hx.1, hx.2.trans ?_⟩
    exact_mod_cast Nat.succ_le_of_lt hj'.2
  have hi (j : ℕ) (hj : j ∈ Finset.Ico n m) :
      IntervalIntegrable g volume (j:ℝ) (j+1:ℕ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by exact_mod_cast Nat.le_succ j)
    intro x hx
    apply (hd x ?_).continuousAt.continuousWithinAt
    apply hs j hj
    simpa only [Nat.cast_add, Nat.cast_one] using hx
  have hcell (j : ℕ) (hj : j ∈ Finset.Ico n m) :
      ‖g j-∫ x in (j:ℝ)..(j+1:ℕ), g x‖ ≤ D := by
    have hn : ∀ x ∈ uIoc (j:ℝ) (j+1:ℕ), ‖g j-g x‖ ≤ D := by
      intro x hx
      rw [uIoc_of_le (by exact_mod_cast Nat.le_succ j)] at hx
      have hx' : x ∈ Icc (j:ℝ) (j+1) := ⟨hx.1.le, by exact_mod_cast hx.2⟩
      have hj' : (j:ℝ) ∈ Icc (n:ℝ) m := hs j hj ⟨le_rfl, by linarith⟩
      have he := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _)
        (hs j hj hx') hj'
      have hdist : ‖(j:ℝ)-x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx'.1, hx'.2]
      exact he.trans ((mul_le_mul_of_nonneg_left hdist hD).trans_eq (mul_one D))
    have he := intervalIntegral.norm_integral_le_of_norm_le_const hn
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi j hj),
      intervalIntegral.integral_const] at he
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_smul,
      abs_one, mul_one] using he
  have hint := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun j : ℕ => (j:ℝ)) (f := g) hnm
      (fun j hj => hi j (Finset.mem_Ico.mpr hj))
  calc
    _ = ‖∑ j ∈ Finset.Ico n m, (g j-∫ x in (j:ℝ)..(j+1:ℕ), g x)‖ := by
      rw [Finset.sum_sub_distrib, hint]
    _ ≤ ∑ j ∈ Finset.Ico n m, ‖g j-∫ x in (j:ℝ)..(j+1:ℕ), g x‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.Ico n m, D := Finset.sum_le_sum hcell
    _ = _ := by simp

/-- The positive-variable integrand; no negative-log duplicate interval is introduced. -/
def jointLogGridIntegrand (v : ℝ → ℝ) (L t x : ℝ) : ℂ :=
  (v (Real.log x-L):ℂ)/(x:ℂ)*Complex.exp (((t*(Real.log x-L):ℝ):ℂ)*I)

theorem jointLogGridIntegrand_hasDerivAt {v : ℝ → ℝ} {L t x : ℝ} (hx : 0 < x)
    (hv : DifferentiableAt ℝ v (Real.log x-L)) :
    HasDerivAt (jointLogGridIntegrand v L t)
      ((((deriv v (Real.log x-L)-v (Real.log x-L):ℝ):ℂ)+
        (v (Real.log x-L):ℂ)*(t:ℂ)*I)/(x:ℂ)^2*
          Complex.exp (((t*(Real.log x-L):ℝ):ℂ)*I)) x := by
  have hl := (Real.hasDerivAt_log hx.ne').sub_const L
  have ha := (hv.hasDerivAt.comp x hl).ofReal_comp.div
    (hasDerivAt_id x).ofReal_comp (Complex.ofReal_ne_zero.mpr hx.ne')
  have hp := ((hl.const_mul t).ofReal_comp.mul_const I).cexp
  convert ha.mul hp using 1 <;> try rfl
  dsimp only [Function.comp_apply, Pi.div_apply, id_eq]
  push_cast
  field_simp [hx.ne']

/-- The derivative cost is explicit and involves only the auxiliary cutoff. -/
theorem jointLogGridIntegrand_deriv_le {v : ℝ → ℝ} {L t x : ℝ} (hx : 0 < x)
    (hv : DifferentiableAt ℝ v (Real.log x-L)) :
    ‖deriv (jointLogGridIntegrand v L t) x‖ ≤
      (|deriv v (Real.log x-L)|+(1+|t|)*|v (Real.log x-L)|)/x^2 := by
  rw [(jointLogGridIntegrand_hasDerivAt hx hv).deriv, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  apply div_le_div_of_nonneg_right _ (sq_nonneg x)
  calc
    _ ≤ ‖((deriv v (Real.log x-L)-v (Real.log x-L):ℝ):ℂ)‖+
        ‖(v (Real.log x-L):ℂ)*(t:ℂ)*I‖ := norm_add_le _ _
    _ = |deriv v (Real.log x-L)-v (Real.log x-L)|+|v (Real.log x-L)| * |t| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    _ ≤ _ := by linarith [abs_sub (deriv v (Real.log x-L)) (v (Real.log x-L))]

/-- Complex cellwise quadrature on an actual positive integer interval. -/
theorem jointLogGridIntegrand_quadrature (v : ℝ → ℝ) (L t : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hv : Differentiable ℝ v)
    {A0 A1 : ℝ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hv0 : ∀ y, |v y| ≤ A0) (hv1 : ∀ y, |deriv v y| ≤ A1) :
    ‖(∑ j ∈ Finset.Ico n m, jointLogGridIntegrand v L t j)-
      ∫ x in (n:ℝ)..m, jointLogGridIntegrand v L t x‖ ≤
      ((m-n:ℕ):ℝ)*((A1+(1+|t|)*A0)/(n:ℝ)^2) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  apply integer_quadrature hnm (by positivity)
  · intro x hx
    exact (jointLogGridIntegrand_hasDerivAt (hn0.trans_le hx.1) (hv _)).differentiableAt
  · intro x hx
    have hx0 := hn0.trans_le hx.1
    calc
      _ ≤ (|deriv v (Real.log x-L)|+(1+|t|)*|v (Real.log x-L)|)/x^2 :=
        jointLogGridIntegrand_deriv_le hx0 (hv _)
      _ ≤ (A1+(1+|t|)*A0)/x^2 := by gcongr; exact hv1 _; exact hv0 _
      _ ≤ (A1+(1+|t|)*A0)/(n:ℝ)^2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn0)
          (pow_le_pow_left₀ hn0.le hx.1 2)

/-- The logarithmic substitution is paid on the positive interval itself. -/
theorem jointLogGridIntegrand_integral (v : ℝ → ℝ) (hv : Continuous v)
    (L t : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, jointLogGridIntegrand v L t x) =
      ∫ y in (Real.log a-L)..(Real.log b-L),
        (v y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*I) := by
  let G : ℝ → ℂ := fun y => (v y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*I)
  have hxpos (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x : ℝ => Real.log x-L) (x⁻¹) x :=
    fun x hx => (Real.hasDerivAt_log (hxpos x hx).ne').sub_const L
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) :=
    fun x hx => (continuousAt_inv₀ (hxpos x hx).ne').continuousWithinAt
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hi := intervalIntegral.integral_deriv_smul_comp hd hc hG
  calc
    _ = ∫ x in a..b, x⁻¹ • G (Real.log x-L) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [jointLogGridIntegrand, G, Complex.real_smul, Complex.ofReal_inv]
      ring
    _ = _ := hi

/-- The discrete Fourier sum is compared with the actual logarithmic integral. -/
theorem joint_log_fourier_quadrature (v : ℝ → ℝ) (L t : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hv : Differentiable ℝ v)
    {A0 A1 : ℝ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hv0 : ∀ y, |v y| ≤ A0) (hv1 : ∀ y, |deriv v y| ≤ A1) :
    ‖(∑ j ∈ Finset.Ico n m, (v (Real.log j-L):ℂ)/(j:ℂ)*
        Complex.exp (((t*(Real.log j-L):ℝ):ℂ)*I))-
      ∫ y in (Real.log n-L)..(Real.log m-L),
        (v y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*I)‖ ≤
      ((m-n:ℕ):ℝ)*((A1+(1+|t|)*A0)/(n:ℝ)^2) := by
  have h := jointLogGridIntegrand_quadrature v L t hn hnm hv hA0 hA1 hv0 hv1
  rw [jointLogGridIntegrand_integral v hv.continuous L t
    (by exact_mod_cast hn) (Nat.cast_le.mpr hnm)] at h
  exact h

/-- The same cutoff derivative budget pays the actual finite Abel variation. -/
theorem joint_log_cutoff_variation (v : ℝ → ℝ) (L : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hv : Differentiable ℝ v)
    {A0 A1 : ℝ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hv0 : ∀ y, |v y| ≤ A0) (hv1 : ∀ y, |deriv v y| ≤ A1) :
    (∑ j ∈ Finset.Ico n m,
      |v (Real.log j-L)/(j:ℝ)-v (Real.log (j+1:ℕ)-L)/(j+1:ℕ)|)+
      |v (Real.log m-L)/(m:ℝ)| ≤
      ((m-n:ℕ):ℝ)*((A1+A0)/(n:ℝ)^2)+A0/(n:ℝ) := by
  let D : ℝ := (A1+A0)/(n:ℝ)^2
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hm0 : (0:ℝ) < m := hn0.trans_le (Nat.cast_le.mpr hnm)
  have hd (x : ℝ) (hx : x ∈ Icc (n:ℝ) m) :
      DifferentiableAt ℝ (jointLogGridIntegrand v L 0) x :=
    (jointLogGridIntegrand_hasDerivAt (hn0.trans_le hx.1) (hv _)).differentiableAt
  have hb (x : ℝ) (hx : x ∈ Icc (n:ℝ) m) :
      ‖deriv (jointLogGridIntegrand v L 0) x‖ ≤ D := by
    have he := jointLogGridIntegrand_deriv_le (L := L) (t := 0) (hn0.trans_le hx.1) (hv _)
    simp only [abs_zero, add_zero, one_mul] at he
    calc
      _ ≤ (|deriv v (Real.log x-L)|+|v (Real.log x-L)|)/x^2 := he
      _ ≤ (A1+A0)/x^2 := by gcongr; exact hv1 _; exact hv0 _
      _ ≤ D := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn0)
        (pow_le_pow_left₀ hn0.le hx.1 2)
  have heq (x : ℝ) : jointLogGridIntegrand v L 0 x = ((v (Real.log x-L)/x:ℝ):ℂ) := by
    simp only [jointLogGridIntegrand, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      mul_one, Complex.ofReal_div]
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico n m) :
      |v (Real.log j-L)/(j:ℝ)-v (Real.log (j+1:ℕ)-L)/(j+1:ℕ)| ≤ D := by
    have hj' := Finset.mem_Ico.mp hj
    have hja : (j:ℝ) ∈ Icc (n:ℝ) m := ⟨Nat.cast_le.mpr hj'.1,
      Nat.cast_le.mpr hj'.2.le⟩
    have hjb : ((j+1:ℕ):ℝ) ∈ Icc (n:ℝ) m := ⟨Nat.cast_le.mpr (by omega),
      Nat.cast_le.mpr (by omega)⟩
    have he := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _) hja hjb
    rw [norm_sub_rev] at he
    simpa only [heq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_one, mul_one] using he
  have hend : |v (Real.log m-L)/(m:ℝ)| ≤ A0/(n:ℝ) := by
    rw [abs_div, abs_of_pos hm0]
    exact (div_le_div_of_nonneg_right (hv0 _) hm0.le).trans
      (div_le_div_of_nonneg_left hA0 hn0 (Nat.cast_le.mpr hnm))
  have hs := add_le_add (Finset.sum_le_sum hterm) hend
  simpa [D] using hs

/-- Short-phase cancellation with the literal logarithmic cutoff weights. -/
theorem joint_log_short_phase_weighted (v : ℝ → ℝ) (L t : ℝ) (ht : 0 < t)
    (k n m : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (hnm : n < m) (hm : m ≤ 2*n+1)
    (U : ℝ) (hU : 0 ≤ U)
    (hsmall : (4:ℝ)^k*(t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k)
      ≤ Real.exp (-U))
    (hlarge : Real.exp U ≤ ((m-n:ℕ):ℝ)^2*
      (t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k))
    (hv : Differentiable ℝ v) {A0 A1 : ℝ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hv0 : ∀ y, |v y| ≤ A0) (hv1 : ∀ y, |deriv v y| ≤ A1) :
    ‖∑ j ∈ Finset.Ico n m, ((v (Real.log j-L)/(j:ℝ):ℝ):ℂ)*
      (j:ℂ)^(-(I*(t:ℂ)))‖ ≤
      512*((m-n:ℕ):ℝ)*Real.exp (-U/(2:ℝ)^k)*
        (((m-n:ℕ):ℝ)*((A1+A0)/(n:ℝ)^2)+A0/(n:ℝ)) := by
  have h := joint_short_phase_weighted t ht k n m hk hn hnm hm U hU hsmall hlarge
    (fun j => v (Real.log j-L)/(j:ℝ))
  exact h.trans (mul_le_mul_of_nonneg_left
    (joint_log_cutoff_variation v L hn hnm.le hv hA0 hA1 hv0 hv1) (by positivity))

end RHTower.WeilWorkPBAP
