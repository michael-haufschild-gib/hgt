import GaloisForLFunctions.HTGeometry.SchwartzCoordPowerBound
import GaloisForLFunctions.HTGeometry.CompactPrimitive
import GaloisForLFunctions.HTGeometry.WeakDerivativeConstant

/-!
# The exponential twist of a vector-valued tempered distribution

A vector-valued tempered distribution cannot be multiplied by an operator-valued function, but it
can be twisted by the exponential of a bounded operator through the series

`(E_A u)(φ) = ∑_n (-A)^n u(η^n φ) / n!`,

which converges on every test function supported in a bounded interval because the values of `u`
along coordinate powers grow at most geometrically.  The twist is the distributional form of
`η ↦ exp(-η A) u(η)`: if `u` solves the constant-coefficient transport equation `u' = A u` on an
interval, then the twist has vanishing derivative there, so by the du Bois-Reymond lemma its value
on a test function depends only on the integral of the test function.
-/

open Set SchwartzMap MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- A power of a bounded operator contracts by at most the power of its norm. -/
theorem norm_pow_apply_le (S : X →L[ℂ] X) (n : ℕ) (w : X) : ‖(S ^ n) w‖ ≤ ‖S‖ ^ n * ‖w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcomp : ((S ^ (n + 1)) w) = S ((S ^ n) w) := by rw [pow_succ']; rfl
    rw [hcomp]
    calc ‖S ((S ^ n) w)‖ ≤ ‖S‖ * ‖(S ^ n) w‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (‖S‖ ^ n * ‖w‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg S)
      _ = ‖S‖ ^ (n + 1) * ‖w‖ := by ring

/-- The `n`-th term of the exponential twist, shifted by `j` extra operator factors. -/
def expTwistShift (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) (φ : SchwartzMap ℝ ℂ)
    (j n : ℕ) : X :=
  ((n.factorial : ℂ))⁻¹ • (((-A) ^ (n + j)) (u (coordPow n φ)))

/-- The `n`-th term of the exponential twist. -/
def expTwistTerm (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) (φ : SchwartzMap ℝ ℂ) (n : ℕ) : X :=
  expTwistShift A u φ 0 n

/-- **The exponential twist of a vector-valued tempered distribution by a bounded operator.** -/
def expTwist (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) (φ : SchwartzMap ℝ ℂ) : X :=
  ∑' n : ℕ, expTwistTerm A u φ n

omit [CompleteSpace X] in
theorem expTwistTerm_eq (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) (φ : SchwartzMap ℝ ℂ)
    (n : ℕ) : expTwistTerm A u φ n = ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (u (coordPow n φ))) := by
  rw [expTwistTerm, expTwistShift, Nat.add_zero]

/-- The twist series converges on every test function supported in a bounded interval. -/
theorem summable_expTwistShift (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    {φ : SchwartzMap ℝ ℂ} (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) (j : ℕ) :
    Summable (expTwistShift A u φ j) := by
  obtain ⟨C, D, hC, hD, hbd⟩ := exists_bound_coordPow u hsupp
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (C * ‖A‖ ^ j) * ((‖A‖ * D) ^ n / (n.factorial : ℝ)))
    ((Real.summable_pow_div_factorial (‖A‖ * D)).mul_left (C * ‖A‖ ^ j)) fun n => ?_
  have h1 : ‖expTwistShift A u φ j n‖
      = ((n.factorial : ℝ))⁻¹ * ‖((-A) ^ (n + j)) (u (coordPow n φ))‖ := by
    rw [expTwistShift, norm_smul]
    simp
  have h2 : ‖((-A) ^ (n + j)) (u (coordPow n φ))‖ ≤ ‖A‖ ^ (n + j) * (C * D ^ n) := by
    refine le_trans (norm_pow_apply_le (-A) (n + j) _) ?_
    rw [norm_neg]
    exact mul_le_mul_of_nonneg_left (hbd n) (by positivity)
  rw [h1]
  calc ((n.factorial : ℝ))⁻¹ * ‖((-A) ^ (n + j)) (u (coordPow n φ))‖
      ≤ ((n.factorial : ℝ))⁻¹ * (‖A‖ ^ (n + j) * (C * D ^ n)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (C * ‖A‖ ^ j) * ((‖A‖ * D) ^ n / (n.factorial : ℝ)) := by
        rw [mul_pow, div_eq_mul_inv, pow_add]
        ring

theorem summable_expTwistTerm (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    {φ : SchwartzMap ℝ ℂ} (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) :
    Summable (expTwistTerm A u φ) :=
  summable_expTwistShift A u hsupp 0

omit [CompleteSpace X] in
theorem expTwistTerm_sub_smul (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) (c : ℂ)
    (φ χ : SchwartzMap ℝ ℂ) (n : ℕ) :
    expTwistTerm A u (φ - c • χ) n = expTwistTerm A u φ n - c • expTwistTerm A u χ n := by
  simp only [expTwistTerm_eq, map_sub, map_smul, smul_sub]
  congr 1
  rw [smul_comm]

/-- The twist is linear on the test functions supported in the interval. -/
theorem expTwist_sub_smul (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ} (c : ℂ)
    {φ χ : SchwartzMap ℝ ℂ} (hφ : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0)
    (hχ : ∀ x, x ∉ Ioo a b → (χ : ℝ → ℂ) x = 0) :
    expTwist A u (φ - c • χ) = expTwist A u φ - c • expTwist A u χ := by
  have hsφ := summable_expTwistTerm A u hφ
  have hsχ := summable_expTwistTerm A u hχ
  have hsc : Summable (fun n : ℕ => c • expTwistTerm A u χ n) := hsχ.const_smul c
  have hcongr : ∑' n : ℕ, expTwistTerm A u (φ - c • χ) n
      = ∑' n : ℕ, (expTwistTerm A u φ n - c • expTwistTerm A u χ n) :=
    tsum_congr (expTwistTerm_sub_smul A u c φ χ)
  rw [expTwist, hcongr, hsφ.tsum_sub hsc, hsχ.tsum_const_smul c, expTwist, expTwist]

omit [CompleteSpace X] in
/-- Coordinate powers commute with differentiation up to the lower coordinate power. -/
theorem coordPow_derivCLM (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    coordPow n (SchwartzMap.derivCLM ℂ ℂ φ)
      = SchwartzMap.derivCLM ℂ ℂ (coordPow n φ) - (n : ℂ) • coordPow (n - 1) φ := by
  refine SchwartzMap.ext fun x => ?_
  have hdφ : HasDerivAt (φ : ℝ → ℂ) (deriv (φ : ℝ → ℂ) x) x :=
    (φ.smooth'.differentiable (by simp) x).hasDerivAt
  have hprod : HasDerivAt (fun y : ℝ => (φ : ℝ → ℂ) y * ((y : ℂ)) ^ n)
      (deriv (φ : ℝ → ℂ) x * ((x : ℂ)) ^ n
        + (φ : ℝ → ℂ) x * ((n : ℂ) * ((x : ℂ)) ^ (n - 1))) x :=
    hdφ.mul (hasDerivAt_ofReal_pow n x)
  have hfun : ((coordPow n φ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => (φ : ℝ → ℂ) y * ((y : ℂ)) ^ n := by
    funext y; exact coordPow_apply n φ y
  have hR : ((SchwartzMap.derivCLM ℂ ℂ (coordPow n φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = deriv (φ : ℝ → ℂ) x * ((x : ℂ)) ^ n
        + (φ : ℝ → ℂ) x * ((n : ℂ) * ((x : ℂ)) ^ (n - 1)) := by
    show deriv ((coordPow n φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = _
    rw [hfun]
    exact hprod.deriv
  have hL : ((coordPow n (SchwartzMap.derivCLM ℂ ℂ φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = deriv (φ : ℝ → ℂ) x * ((x : ℂ)) ^ n := coordPow_apply n _ x
  have hsub : ((SchwartzMap.derivCLM ℂ ℂ (coordPow n φ) - (n : ℂ) • coordPow (n - 1) φ :
        SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = ((SchwartzMap.derivCLM ℂ ℂ (coordPow n φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
        - (n : ℂ) * ((coordPow (n - 1) φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x := rfl
  rw [hL, hsub, hR, coordPow_apply]
  ring

/-- The twist of a solution of the constant-coefficient transport equation has vanishing
derivative on the interval. -/
theorem expTwist_derivCLM_eq_zero (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    (hode : ∀ ψ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) →
      u (SchwartzMap.derivCLM ℂ ℂ ψ) = -(A (u ψ)))
    {φ : SchwartzMap ℝ ℂ} (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) :
    expTwist A u (SchwartzMap.derivCLM ℂ ℂ φ) = 0 := by
  set g : ℕ → X := expTwistShift A u φ 1 with hg
  set h : ℕ → X := fun n =>
    ((n : ℂ) / (n.factorial : ℂ)) • (((-A) ^ n) (u (coordPow (n - 1) φ))) with hh
  have hgapply : ∀ n : ℕ,
      g n = ((n.factorial : ℂ))⁻¹ • (((-A) ^ (n + 1)) (u (coordPow n φ))) := fun _ => rfl
  have hhapply : ∀ n : ℕ,
      h n = ((n : ℂ) / (n.factorial : ℂ)) • (((-A) ^ n) (u (coordPow (n - 1) φ))) := fun _ => rfl
  have hgsum : Summable g := summable_expTwistShift A u hsupp 1
  -- the shift identity
  have hshift : ∀ m : ℕ, h (m + 1) = g m := by
    intro m
    have hne : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hfacne : ((m.factorial : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hfac : (((m + 1).factorial : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) * ((m.factorial : ℕ) : ℂ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hcoef : (((m + 1 : ℕ) : ℂ) / (((m + 1).factorial : ℕ) : ℂ))
        = ((m.factorial : ℕ) : ℂ)⁻¹ := by
      rw [hfac]
      field_simp
    rw [hhapply (m + 1), hgapply m]
    simp only [Nat.add_sub_cancel]
    rw [hcoef]
  have hhsum : Summable h := by
    refine (summable_nat_add_iff 1).mp ?_
    have : (fun m : ℕ => h (m + 1)) = g := funext hshift
    rw [this]
    exact hgsum
  have hzero : h 0 = 0 := by
    rw [hhapply 0]
    simp
  -- the term identity
  have hterm : ∀ n : ℕ, expTwistTerm A u (SchwartzMap.derivCLM ℂ ℂ φ) n = g n - h n := by
    intro n
    have hu : u (coordPow n (SchwartzMap.derivCLM ℂ ℂ φ))
        = -(A (u (coordPow n φ))) - (n : ℂ) • u (coordPow (n - 1) φ) := by
      rw [coordPow_derivCLM, map_sub, map_smul, hode _ (coordPow_eq_zero_of_notMem hsupp n)]
    have hpow : ((-A) ^ n) (-(A (u (coordPow n φ)))) = ((-A) ^ (n + 1)) (u (coordPow n φ)) := by
      rw [pow_succ]
      rfl
    rw [expTwistTerm_eq, hu, map_sub, map_smul, hpow, smul_sub, hgapply n, hhapply n]
    congr 1
    rw [smul_smul, div_eq_mul_inv, mul_comm]
  calc expTwist A u (SchwartzMap.derivCLM ℂ ℂ φ)
      = ∑' n : ℕ, (g n - h n) := by rw [expTwist]; exact tsum_congr hterm
    _ = (∑' n : ℕ, g n) - ∑' n : ℕ, h n := hgsum.tsum_sub hhsum
    _ = 0 := by
        rw [hhsum.tsum_eq_zero_add, hzero, zero_add]
        have : (fun m : ℕ => h (m + 1)) = g := funext hshift
        rw [show (∑' m : ℕ, h (m + 1)) = ∑' m : ℕ, g m from tsum_congr hshift, sub_self]

/-- A normalised complex test function supported in a bounded open interval. -/
theorem exists_normalised_test {a b : ℝ} (hab : a < b) :
    ∃ χ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (χ : ℝ → ℂ) x = 0) ∧
      (∫ t in a..b, (χ : ℝ → ℂ) t) = 1 := by
  obtain ⟨χ₀, hcd, hcs, hts, hint⟩ := exists_test_integral_one hab
  have hcdC : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((χ₀ x : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp hcd
  have hcsC : HasCompactSupport (fun x : ℝ => ((χ₀ x : ℂ))) :=
    hcs.comp_left (g := fun z : ℝ => ((z : ℂ))) Complex.ofReal_zero
  refine ⟨schwartzOfCompactSupport hcdC hcsC, ?_, ?_⟩
  · intro x hx
    have hxs : x ∉ tsupport χ₀ := fun hc => hx (hts hc)
    show ((χ₀ x : ℂ)) = 0
    rw [image_eq_zero_of_notMem_tsupport hxs, Complex.ofReal_zero]
  · have hzero : ∀ x ∉ Ioc a b, χ₀ x = 0 := by
      intro x hx
      refine image_eq_zero_of_notMem_tsupport fun hc => hx ?_
      exact Ioo_subset_Ioc_self (hts hc)
    have hreal : (∫ t in a..b, χ₀ t) = 1 := by
      rw [intervalIntegral.integral_of_le hab.le,
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      exact hint
    show (∫ t in a..b, ((χ₀ t : ℂ))) = 1
    rw [intervalIntegral.integral_ofReal, hreal, Complex.ofReal_one]

/-- **The twist of a distributional solution of `u' = A u` is constant on the interval.**  Its
value on a test function supported there is the integral of the test function times a fixed
vector. -/
theorem exists_expTwist_const (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    (hab : a < b)
    (hode : ∀ ψ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) →
      u (SchwartzMap.derivCLM ℂ ℂ ψ) = -(A (u ψ))) :
    ∃ c : X, ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      expTwist A u φ = (∫ t in a..b, (φ : ℝ → ℂ) t) • c := by
  obtain ⟨χ, hχsupp, hχint⟩ := exists_normalised_test hab
  refine ⟨expTwist A u χ, ?_⟩
  refine apply_eq_integral_smul_of_deriv_zero_of_linearOn
    (fun φ' χ' c hφ' hχ' => expTwist_sub_smul A u c hφ' hχ')
    (fun ψ hψ => expTwist_derivCLM_eq_zero A u hode hψ) hχsupp hχint

end

end GaloisForLFunctions.HTGeometry
