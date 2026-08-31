import GaloisForLFunctions.HTGeometry.OmittedValueLogarithmicGrowth
import GaloisForLFunctions.HTGeometry.MaxModulusCharacteristicBound
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.AnalyticEquilibriumUniqueness
import GaloisForLFunctions.HTGeometry.ProximityFirstOrderAutonomous

/-!
# The Briot–Bouquet no-go when the coefficient has two distinct roots

A nonconstant entire solution of `F' = c(F)` omits every root of `c`, so `c(F)` — that is, `F'` —
never vanishes.  With two distinct roots omitted the second main theorem applies with both counting
terms zero and the ramification term supplied by Jensen, and the Borel closure gives
`T(r,F) = O(log r)`.

Comparing the maximum modulus at `r` with the characteristic at `2r` converts that into the growth
bound `‖F z‖ ≤ M (1 + ‖z‖)^{36}`, so `F` is a polynomial `p`.  Then `p' = c ∘ p` as polynomials, and
`deg p − 1 = deg c · deg p` has no solution with `deg c ≥ 2` and `deg p ≥ 1`.  Hence `F` is constant.

Together with `AutonomousPowerRigidity` — the single-root case — this covers every `c` of degree at
least two.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real Set

theorem le_exp_posLog {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.exp (Real.posLog x) := by
  rcases le_or_gt x 1 with hle | hgt
  · have h0 : Real.posLog x = 0 := (Real.posLog_eq_zero_iff x).mpr (by rwa [abs_of_nonneg hx])
    rw [h0, Real.exp_zero]
    exact hle
  · have hlog : Real.posLog x = Real.log x :=
      Real.posLog_eq_log (by rw [abs_of_nonneg hx]; exact hgt.le)
    rw [hlog, Real.exp_log (by linarith)]

set_option maxHeartbeats 1000000 in
/-- **Logarithmic characteristic gives polynomial growth.**  Comparing the maximum modulus at radius
`r` with the characteristic at `2r` turns `T(s) ≤ 6 log(s + A) + B` into a degree-`36` bound. -/
theorem exists_polyGrowth_of_characteristic_le_log {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (horder : ∀ u, meromorphicOrderAt F u ≠ ⊤) {A B : ℝ} (hA : 1 ≤ A)
    (hbd : ∀ s : ℝ, 1 ≤ s → characteristic F ⊤ s ≤ 6 * Real.log (s + A) + B) :
    ∃ M : ℝ, ∀ z : ℂ, ‖F z‖ ≤ M * (1 + ‖z‖) ^ 36 := by
  classical
  set C₀ : ℝ := max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| with hC₀
  have hC₀0 : 0 ≤ C₀ := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨Real.exp (6 * B + 3 * C₀) * (2 + A) ^ 36, fun z => ?_⟩
  set r : ℝ := max ‖z‖ 1 with hr
  have hr1 : (1 : ℝ) ≤ r := le_max_right _ _
  have hzr : ‖z‖ ≤ r := le_max_left _ _
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hR : (1 : ℝ) ≤ 2 * r := by linarith
  have hrR : r < 2 * r := by linarith
  have hpj := posLog_norm_le_characteristic hF horder hR hr0 hrR hzr
  have hfac : (2 * r + r) / (2 * r - r) = 3 := by
    field_simp
    ring
  rw [hfac, ← hC₀] at hpj
  have hchar : characteristic F ⊤ (2 * r) ≤ 6 * Real.log (2 * r + A) + B := hbd (2 * r) hR
  have hstep : Real.posLog ‖F z‖ ≤ 36 * Real.log (2 * r + A) + 6 * B + 3 * C₀ := by
    linarith [hpj, hchar]
  -- exponentiate
  have hexp : ‖F z‖ ≤ Real.exp (36 * Real.log (2 * r + A) + 6 * B + 3 * C₀) := by
    refine le_trans (le_exp_posLog (norm_nonneg _)) ?_
    exact Real.exp_le_exp.mpr hstep
  have hpos : (0 : ℝ) < 2 * r + A := by linarith
  have hval : Real.exp (36 * Real.log (2 * r + A) + 6 * B + 3 * C₀)
      = Real.exp (6 * B + 3 * C₀) * (2 * r + A) ^ 36 := by
    have ht : Real.exp (36 * Real.log (2 * r + A)) = (2 * r + A) ^ (36 : ℕ) := by
      rw [show (36 : ℝ) * Real.log (2 * r + A) = ((36 : ℕ) : ℝ) * Real.log (2 * r + A) by norm_num,
        Real.exp_nat_mul, Real.exp_log hpos]
    rw [show (36 : ℝ) * Real.log (2 * r + A) + 6 * B + 3 * C₀
        = (6 * B + 3 * C₀) + 36 * Real.log (2 * r + A) by ring, Real.exp_add, ht]
  rw [hval] at hexp
  refine le_trans hexp ?_
  have hbase : 2 * r + A ≤ (2 + A) * (1 + ‖z‖) := by
    have : r ≤ 1 + ‖z‖ := by
      rcases le_or_gt ‖z‖ 1 with hle | hgt
      · rw [hr]; simp only [max_le_iff]; constructor <;> linarith [norm_nonneg z]
      · rw [hr, max_eq_left hgt.le]; linarith
    nlinarith [this, norm_nonneg z, hA]
  have hpow : (2 * r + A) ^ 36 ≤ ((2 + A) * (1 + ‖z‖)) ^ 36 :=
    pow_le_pow_left₀ (by linarith) hbase 36
  have hEpos : (0 : ℝ) < Real.exp (6 * B + 3 * C₀) := Real.exp_pos _
  calc Real.exp (6 * B + 3 * C₀) * (2 * r + A) ^ 36
      ≤ Real.exp (6 * B + 3 * C₀) * ((2 + A) * (1 + ‖z‖)) ^ 36 :=
        mul_le_mul_of_nonneg_left hpow hEpos.le
    _ = Real.exp (6 * B + 3 * C₀) * (2 + A) ^ 36 * (1 + ‖z‖) ^ 36 := by
        rw [mul_pow, ← mul_assoc]

set_option maxHeartbeats 1000000 in
/-- **No nonconstant entire solution of `F' = c(F)` when `c` has two distinct roots and degree at
least two.**  The solution omits both roots, so its derivative is zero-free; the second main theorem
then forces `T(r,F) = O(log r)`, hence `F` is a polynomial, and the degree count
`deg p − 1 = deg c · deg p` is impossible. -/
theorem not_nonconstant_of_two_roots {c : Polynomial ℂ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (heq : ∀ z, deriv F z = c.eval (F z)) (hc : 2 ≤ c.natDegree)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (hr₁ : c.eval a₁ = 0) (hr₂ : c.eval a₂ = 0)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) : False := by
  classical
  have h₁ : ∀ z, F z ≠ a₁ := fun z hz =>
    hnc ⟨a₁, eq_const_of_root_of_deriv_eq_comp hr₁ hF heq hz⟩
  have h₂ : ∀ z, F z ≠ a₂ := fun z hz =>
    hnc ⟨a₂, eq_const_of_root_of_deriv_eq_comp hr₂ hF heq hz⟩
  have hF' : ∀ z, deriv F z ≠ 0 := by
    intro z hz
    rw [heq z] at hz
    exact hnc ⟨F z, eq_const_of_root_of_deriv_eq_comp hz hF heq rfl⟩
  have horder : ∀ u, meromorphicOrderAt F u ≠ ⊤ :=
    fun u => meromorphicOrderAt_ne_top_of_deriv_ne_zero hF hF' u
  -- the first-main-theorem defect
  have hmF : Meromorphic F := fun z => (hF.analyticAt z).meromorphicAt
  have hmS : ∀ a : ℂ, Meromorphic (F - fun _ => a) :=
    fun a z => ((hF.sub_const a).analyticAt z).meromorphicAt
  set K₁ : ℝ := (Real.posLog ‖a₁‖ + Real.log 2)
    + max |Real.log ‖((F - fun _ : ℂ => a₁) : ℂ → ℂ) 0‖|
        |Real.log ‖meromorphicTrailingCoeffAt ((F - fun _ : ℂ => a₁) : ℂ → ℂ) 0‖| with hK₁
  set K₂ : ℝ := (Real.posLog ‖a₂‖ + Real.log 2)
    + max |Real.log ‖((F - fun _ : ℂ => a₂) : ℂ → ℂ) 0‖|
        |Real.log ‖meromorphicTrailingCoeffAt ((F - fun _ : ℂ => a₂) : ℂ → ℂ) 0‖| with hK₂
  have hfmt : ∀ r : ℝ, r ≠ 0 → ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + max K₁ K₂ := by
    intro r _ j
    fin_cases j
    · have h := characteristic_top_le_characteristic_coe (f := F) (a₀ := a₁) (r := r) hmF (hmS a₁)
      have hle : K₁ ≤ max K₁ K₂ := le_max_left _ _
      show characteristic F ⊤ r ≤ characteristic F ((a₁ : ℂ) : WithTop ℂ) r + max K₁ K₂
      rw [← hK₁] at h
      linarith
    · have h := characteristic_top_le_characteristic_coe (f := F) (a₀ := a₂) (r := r) hmF (hmS a₂)
      have hle : K₂ ≤ max K₁ K₂ := le_max_right _ _
      show characteristic F ⊤ r ≤ characteristic F ((a₂ : ℂ) : WithTop ℂ) r + max K₁ K₂
      rw [← hK₂] at h
      linarith
  obtain ⟨A, B, hA, hbd⟩ :=
    exists_characteristic_le_log_of_omits_two hF hane h₁ h₂ hF' hfmt
  obtain ⟨M, hM⟩ := exists_polyGrowth_of_characteristic_le_log hF horder hA hbd
  obtain ⟨p, hp⟩ := exists_polynomial_of_polynomial_growth hF hM
  -- the polynomial identity and the degree count
  have hderiv : ∀ z : ℂ, (Polynomial.derivative p).eval z = (c.comp p).eval z := by
    intro z
    have hFz : deriv F z = (Polynomial.derivative p).eval z := by
      have hfun : F = fun w => p.eval w := funext hp
      rw [hfun, Polynomial.deriv]
    rw [← hFz, heq z, hp z, Polynomial.eval_comp]
  have hpoly : Polynomial.derivative p = c.comp p := Polynomial.funext hderiv
  have hdeg := natDegree_eq_zero_of_derivative_eq_comp hc hpoly
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  exact hnc ⟨b, funext fun z => by rw [hp z, ← hb, Polynomial.eval_C]⟩

end GaloisForLFunctions.HTGeometry
