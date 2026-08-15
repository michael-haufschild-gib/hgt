import GaloisForLFunctions.HTGeometry.CirclePolynomialSupBound
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyNumerator
import GaloisForLFunctions.RHTower.EntireMontel

/-!
# Uniform complex bounds for the hard-edge Cayley packets

The hard-edge coordinate `(a² - z²)/(a² + z²)` is the Zhukovsky image of the disc variable
`w = (a + iz)/(a - iz)`, which stays within `(a+R)/(a-R)` of the unit circle on every disc of
radius `R`.  A polynomial of degree at most `d` in the hard-edge coordinate is therefore bounded
on that disc by its circle energy times `((a+R)/(a-R))^{d+2}`, and the last factor is at most
`exp(2R(d+2)/(a-R))`.  When the degree grows proportionally to `a`, the whole bound is uniform:
this is the normality hypothesis of the hard-edge limit.
-/

open Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The disc variable of the hard-edge Cayley chart. -/
def hardEdgeDiskVariable (a : ℝ) (z : ℂ) : ℂ := ((a : ℂ) + z * I) / ((a : ℂ) - z * I)

/-- The hard-edge coordinate is the Zhukovsky image of the disc variable. -/
theorem zhukovsky_hardEdgeDiskVariable (a : ℝ) (z : ℂ)
    (h₁ : (a : ℂ) + z * I ≠ 0) (h₂ : (a : ℂ) - z * I ≠ 0) :
    (hardEdgeDiskVariable a z + (hardEdgeDiskVariable a z)⁻¹) / 2
      = ((a : ℂ) ^ 2 - z ^ 2) / ((a : ℂ) ^ 2 + z ^ 2) := by
  have hprod : ((a : ℂ) - z * I) * ((a : ℂ) + z * I) = (a : ℂ) ^ 2 + z ^ 2 := by
    linear_combination (-(z ^ 2)) * Complex.I_sq
  have hne : (a : ℂ) ^ 2 + z ^ 2 ≠ 0 := by
    rw [← hprod]
    exact mul_ne_zero h₂ h₁
  have hnum : ((a : ℂ) + z * I) * ((a : ℂ) + z * I) + ((a : ℂ) - z * I) * ((a : ℂ) - z * I)
      = 2 * ((a : ℂ) ^ 2 - z ^ 2) := by
    linear_combination (2 * z ^ 2) * Complex.I_sq
  rw [hardEdgeDiskVariable, inv_div, div_add_div _ _ h₂ h₁, hprod, hnum]
  field_simp

theorem hardEdgeDiskVariable_ne_zero (a : ℝ) (z : ℂ)
    (h₁ : (a : ℂ) + z * I ≠ 0) (h₂ : (a : ℂ) - z * I ≠ 0) :
    hardEdgeDiskVariable a z ≠ 0 :=
  div_ne_zero h₁ h₂

/-- On a disc of radius `R` the disc variable stays within `(a+R)/(a-R)` of the unit circle. -/
theorem max_norm_hardEdgeDiskVariable_le {a R : ℝ} (hR : 0 ≤ R) (hRa : R < a) {z : ℂ}
    (hz : ‖z‖ ≤ R) :
    max ‖hardEdgeDiskVariable a z‖ ‖hardEdgeDiskVariable a z‖⁻¹ ≤ (a + R) / (a - R) := by
  have hzI : ‖z * I‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hnorma : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hR hRa.le)]
  have hsubpos : 0 < a - R := by linarith
  have hlow₂ : a - R ≤ ‖(a : ℂ) - z * I‖ := by
    have h := norm_sub_norm_le ((a : ℂ)) (z * I)
    rw [hnorma, hzI] at h
    linarith
  have hlow₁ : a - R ≤ ‖(a : ℂ) + z * I‖ := by
    have h := norm_sub_norm_le ((a : ℂ)) (-(z * I))
    rw [hnorma, norm_neg, hzI, sub_neg_eq_add] at h
    linarith
  have hup₁ : ‖(a : ℂ) + z * I‖ ≤ a + R := by
    have h := norm_add_le ((a : ℂ)) (z * I)
    rw [hnorma, hzI] at h
    linarith
  have hup₂ : ‖(a : ℂ) - z * I‖ ≤ a + R := by
    have h := norm_sub_le ((a : ℂ)) (z * I)
    rw [hnorma, hzI] at h
    linarith
  have hpos₁ : 0 < ‖(a : ℂ) + z * I‖ := lt_of_lt_of_le hsubpos hlow₁
  have hpos₂ : 0 < ‖(a : ℂ) - z * I‖ := lt_of_lt_of_le hsubpos hlow₂
  have hw : ‖hardEdgeDiskVariable a z‖ = ‖(a : ℂ) + z * I‖ / ‖(a : ℂ) - z * I‖ := by
    rw [hardEdgeDiskVariable, norm_div]
  have hwinv : ‖hardEdgeDiskVariable a z‖⁻¹ = ‖(a : ℂ) - z * I‖ / ‖(a : ℂ) + z * I‖ := by
    rw [hw, inv_div]
  refine max_le ?_ ?_
  · rw [hw]
    exact div_le_div₀ (by linarith) hup₁ hsubpos hlow₂
  · rw [hwinv]
    exact div_le_div₀ (by linarith) hup₂ hsubpos hlow₁

/-- The ratio power is controlled by an exponential in the degree over the aperture. -/
theorem ratio_pow_le_exp {a R : ℝ} (hR : 0 ≤ R) (hRa : R < a) (n : ℕ) :
    ((a + R) / (a - R)) ^ n ≤ Real.exp (2 * R * n / (a - R)) := by
  have hsubpos : 0 < a - R := by linarith
  have hstep : (a + R) / (a - R) = 1 + 2 * R / (a - R) := by
    field_simp
    ring
  have hexp : (1 : ℝ) + 2 * R / (a - R) ≤ Real.exp (2 * R / (a - R)) := by
    have h := Real.add_one_le_exp (2 * R / (a - R))
    linarith
  have hnonneg : (0 : ℝ) ≤ 1 + 2 * R / (a - R) := by positivity
  calc ((a + R) / (a - R)) ^ n = (1 + 2 * R / (a - R)) ^ n := by rw [hstep]
    _ ≤ (Real.exp (2 * R / (a - R))) ^ n := pow_le_pow_left₀ hnonneg hexp n
    _ = Real.exp (n * (2 * R / (a - R))) := by
        rw [← Real.exp_nat_mul]
    _ = Real.exp (2 * R * n / (a - R)) := by
        congr 1
        field_simp

/-- **Uniform bound for a hard-edge packet on a complex disc.**  A polynomial of degree at most
`d` in the hard-edge coordinate is bounded on the disc of radius `R` by its circle energy times
`exp(2R(d+2)/(a-R))`. -/
theorem norm_eval_hardEdgeCoordinate_le {a R : ℝ} (hR : 0 ≤ R) (hRa : R < a)
    (d : ℕ) (P : Polynomial ℂ) (hd : P.natDegree ≤ d) {z : ℂ} (hz : ‖z‖ ≤ R)
    (h₁ : (a : ℂ) + z * I ≠ 0) (h₂ : (a : ℂ) - z * I ≠ 0) :
    ‖P.eval (((a : ℂ) ^ 2 - z ^ 2) / ((a : ℂ) ^ 2 + z ^ 2))‖
      ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P)
          * Real.exp (2 * R * (d + 2) / (a - R)) := by
  have hwne := hardEdgeDiskVariable_ne_zero a z h₁ h₂
  have hzhu := zhukovsky_hardEdgeDiskVariable a z h₁ h₂
  have hbase := norm_eval_cayley_le' d P hd hwne
  rw [hzhu] at hbase
  refine hbase.trans ?_
  have hcoef : 0 ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  have hmax := max_norm_hardEdgeDiskVariable_le hR hRa hz
  have hmaxpos : 0 ≤ max ‖hardEdgeDiskVariable a z‖ ‖hardEdgeDiskVariable a z‖⁻¹ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  calc (max ‖hardEdgeDiskVariable a z‖ ‖hardEdgeDiskVariable a z‖⁻¹) ^ (d + 2)
      ≤ ((a + R) / (a - R)) ^ (d + 2) := pow_le_pow_left₀ hmaxpos hmax _
    _ ≤ Real.exp (2 * R * (d + 2) / (a - R)) := by
        have := ratio_pow_le_exp hR hRa (d + 2)
        simpa using this

/-- **The normalized hard-edge numerator is bounded on every disc.**  Writing the numerator as the
cleared substitution and passing to a square root of the variable, the packet bound applies. -/
theorem norm_scaledCayleyNumerator_le {a : ℝ} {d : ℕ} {P : Polynomial ℂ} (hd : P.natDegree ≤ d)
    {R : ℝ} (hR : 0 ≤ R) (hsq : Real.sqrt R < a) {u : ℂ} (hu : ‖u‖ ≤ R) :
    ‖((((a : ℝ) : ℂ) ^ 2) ^ d)⁻¹ * (cayleyNumerator a d P).eval u‖
      ≤ (1 + R / a ^ 2) ^ d * (Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P)
          * Real.exp (2 * Real.sqrt R * (d + 2) / (a - Real.sqrt R))) := by
  have hRs : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hapos : 0 < a := lt_of_le_of_lt hRs hsq
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ 2 = u := IsSepClosed.exists_pow_nat_eq u 2
  have hznorm : ‖z‖ ≤ Real.sqrt R := by
    have hn : ‖z‖ ^ 2 = ‖u‖ := by rw [← hz, norm_pow]
    have hle : ‖z‖ ^ 2 ≤ R := by rw [hn]; exact hu
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg z)] at this
  have hnorma : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hapos.le]
  have hzI : ‖z * I‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have h₁ : ((a : ℝ) : ℂ) + z * I ≠ 0 := by
    intro hcon
    have h := norm_sub_norm_le (((a : ℝ) : ℂ)) (-(z * I))
    rw [hnorma, norm_neg, hzI, sub_neg_eq_add, hcon, norm_zero] at h
    linarith
  have h₂ : ((a : ℝ) : ℂ) - z * I ≠ 0 := by
    intro hcon
    have h := norm_sub_norm_le (((a : ℝ) : ℂ)) (z * I)
    rw [hnorma, hzI, hcon, norm_zero] at h
    linarith
  have hane : (((a : ℝ) : ℂ) ^ 2) ≠ 0 := by
    intro hcon
    have := norm_ofReal_sq a
    rw [hcon, norm_zero] at this
    nlinarith
  have hsum : (((a : ℝ) : ℂ) ^ 2 + u) ≠ 0 := by
    intro hcon
    have heq : u = -(((a : ℝ) : ℂ) ^ 2) := by linear_combination hcon
    have hnu : ‖u‖ = a ^ 2 := by rw [heq, norm_neg, norm_ofReal_sq]
    have hRa : R < a ^ 2 := by
      have := Real.sq_sqrt hR
      nlinarith
    linarith
  have heval := eval_cayleyNumerator a d P hd u hsum
  rw [heval, ← hz]
  have hsplit : ((((a : ℝ) : ℂ) ^ 2) ^ d)⁻¹ *
      ((((a : ℝ) : ℂ) ^ 2 + z ^ 2) ^ d *
        P.eval (((((a : ℝ) : ℂ) ^ 2 - z ^ 2) / (((a : ℝ) : ℂ) ^ 2 + z ^ 2))))
      = (1 + z ^ 2 / (((a : ℝ) : ℂ) ^ 2)) ^ d *
        P.eval (((((a : ℝ) : ℂ) ^ 2 - z ^ 2) / (((a : ℝ) : ℂ) ^ 2 + z ^ 2))) := by
    have hbase : (1 + z ^ 2 / (((a : ℝ) : ℂ) ^ 2))
        = ((((a : ℝ) : ℂ) ^ 2)⁻¹) * (((a : ℝ) : ℂ) ^ 2 + z ^ 2) := by
      rw [mul_add, inv_mul_cancel₀ hane, div_eq_inv_mul]
    rw [hbase, mul_pow, inv_pow]
    ring
  rw [hsplit, norm_mul]
  have hfac : ‖(1 + z ^ 2 / (((a : ℝ) : ℂ) ^ 2)) ^ d‖ ≤ (1 + R / a ^ 2) ^ d := by
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ d
    have hbound : ‖z ^ 2 / (((a : ℝ) : ℂ) ^ 2)‖ ≤ R / a ^ 2 := by
      have hz2 : ‖z ^ 2‖ ≤ R := by rw [hz]; exact hu
      have ha2 : (0 : ℝ) < a ^ 2 := by positivity
      rw [norm_div, norm_ofReal_sq]
      gcongr
    calc ‖(1 : ℂ) + z ^ 2 / (((a : ℝ) : ℂ) ^ 2)‖
        ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 / (((a : ℝ) : ℂ) ^ 2)‖ := norm_add_le _ _
      _ ≤ 1 + R / a ^ 2 := by rw [norm_one]; linarith
  have hpacket := norm_eval_hardEdgeCoordinate_le hRs hsq d P hd hznorm h₁ h₂
  have hnn : (0 : ℝ) ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P)
      * Real.exp (2 * Real.sqrt R * (d + 2) / (a - Real.sqrt R)) := by positivity
  exact mul_le_mul hfac hpacket (norm_nonneg _) (pow_nonneg (by positivity) d)

open Filter in
/-- **Uniform normality bound.**  With circle energy and degree controlled by the aperture, the
normalized numerators are eventually bounded on every disc by one constant. -/
theorem eventually_norm_scaledCayleyNumerator_le {a : ℕ → ℝ} {d : ℕ → ℕ} {P : ℕ → Polynomial ℂ}
    {B K : ℝ} (hd : ∀ n, (P n).natDegree ≤ d n) (hK : 0 ≤ K)
    (hdeg : ∀ᶠ n in atTop, (d n : ℝ) ≤ K * a n)
    (hE : ∀ n, (2 * (d n : ℝ) + 2) * cayleyEnergy (P n) ≤ B)
    (hlarge : Tendsto a atTop atTop) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ n in atTop, ∀ u ∈ Metric.ball (0 : ℂ) R,
      ‖((((a n : ℝ) : ℂ) ^ 2) ^ (d n))⁻¹ * (cayleyNumerator (a n) (d n) (P n)).eval u‖
        ≤ Real.exp (K * R) * (Real.sqrt B * Real.exp (2 * Real.sqrt R * (2 * K + 4))) := by
  have hRs : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  filter_upwards [hdeg, hlarge.eventually_ge_atTop (max 1 (2 * Real.sqrt R + 1))]
    with n hdn han u hu
  have ha1 : (1 : ℝ) ≤ a n := le_trans (le_max_left _ _) han
  have haR : 2 * Real.sqrt R + 1 ≤ a n := le_trans (le_max_right _ _) han
  have hsq : Real.sqrt R < a n := by linarith
  have hunorm : ‖u‖ ≤ R := by
    have := Metric.mem_ball.1 hu
    rw [dist_zero_right] at this
    exact this.le
  have hmain := norm_scaledCayleyNumerator_le (hd n) hR hsq hunorm
  refine hmain.trans ?_
  have hapos : (0 : ℝ) < a n := by linarith
  have ha2 : (0 : ℝ) < (a n) ^ 2 := by positivity
  have hfac1 : (1 + R / (a n) ^ 2) ^ (d n) ≤ Real.exp (K * R) := by
    have h1 : (1 : ℝ) + R / (a n) ^ 2 ≤ Real.exp (R / (a n) ^ 2) := by
      have h := Real.add_one_le_exp (R / (a n) ^ 2)
      linarith
    have h2 : (1 + R / (a n) ^ 2) ^ (d n) ≤ (Real.exp (R / (a n) ^ 2)) ^ (d n) :=
      pow_le_pow_left₀ (by positivity) h1 _
    have h3 : (Real.exp (R / (a n) ^ 2)) ^ (d n) = Real.exp ((d n : ℝ) * (R / (a n) ^ 2)) := by
      rw [← Real.exp_nat_mul]
    have h4 : (d n : ℝ) * (R / (a n) ^ 2) ≤ K * R := by
      rw [mul_div_assoc', div_le_iff₀ ha2]
      have e1 : (d n : ℝ) * R ≤ (K * a n) * R := mul_le_mul_of_nonneg_right hdn hR
      have e2 : (0 : ℝ) ≤ K * R * (a n) * (a n - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg hK hR) hapos.le) (by linarith)
      nlinarith [e1, e2]
    calc (1 + R / (a n) ^ 2) ^ (d n) ≤ (Real.exp (R / (a n) ^ 2)) ^ (d n) := h2
      _ = Real.exp ((d n : ℝ) * (R / (a n) ^ 2)) := h3
      _ ≤ Real.exp (K * R) := Real.exp_le_exp.2 h4
  have hfac2 : Real.sqrt (2 * (d n : ℝ) + 2) * Real.sqrt (cayleyEnergy (P n)) ≤ Real.sqrt B := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (hE n)
  have hden : (0 : ℝ) < a n - Real.sqrt R := by linarith
  have hfac3 : Real.exp (2 * Real.sqrt R * ((d n : ℝ) + 2) / (a n - Real.sqrt R))
      ≤ Real.exp (2 * Real.sqrt R * (2 * K + 4)) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ hden]
    have hAs : (a n + 1) / 2 ≤ a n - Real.sqrt R := by linarith
    have hkey : (d n : ℝ) + 2 ≤ (2 * K + 4) * (a n - Real.sqrt R) := by
      have h1 : (2 * K + 4) * ((a n + 1) / 2) ≤ (2 * K + 4) * (a n - Real.sqrt R) :=
        mul_le_mul_of_nonneg_left hAs (by linarith)
      nlinarith [h1, hdn, hK, ha1]
    have h2 : (2 * Real.sqrt R) * ((d n : ℝ) + 2)
        ≤ (2 * Real.sqrt R) * ((2 * K + 4) * (a n - Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left hkey (by linarith)
    nlinarith [h2]
  have hnn1 : (0 : ℝ) ≤ (1 + R / (a n) ^ 2) ^ (d n) := by positivity
  have hnn2 : (0 : ℝ) ≤ Real.sqrt (2 * (d n : ℝ) + 2) * Real.sqrt (cayleyEnergy (P n)) := by
    positivity
  calc (1 + R / (a n) ^ 2) ^ (d n) *
        (Real.sqrt (2 * (d n : ℝ) + 2) * Real.sqrt (cayleyEnergy (P n))
          * Real.exp (2 * Real.sqrt R * ((d n : ℝ) + 2) / (a n - Real.sqrt R)))
      ≤ Real.exp (K * R) * (Real.sqrt B * Real.exp (2 * Real.sqrt R * (2 * K + 4))) := by
        refine mul_le_mul hfac1 ?_ (by positivity) (Real.exp_nonneg _)
        exact mul_le_mul hfac2 hfac3 (Real.exp_nonneg _) (Real.sqrt_nonneg _)

open Filter in
/-- **(HHWB.11)/(HHWB.13) Normality of the normalized hard-edge numerators.**  Under the same
control of circle energy and degree, a subsequence of the normalized numerators converges locally
uniformly on the plane. -/
theorem exists_subseq_tendstoLocallyUniformly_scaledCayleyNumerator
    {a : ℕ → ℝ} {d : ℕ → ℕ} {P : ℕ → Polynomial ℂ} {B K : ℝ}
    (hd : ∀ n, (P n).natDegree ≤ d n) (hK : 0 ≤ K)
    (hdeg : ∀ᶠ n in atTop, (d n : ℝ) ≤ K * a n)
    (hE : ∀ n, (2 * (d n : ℝ) + 2) * cayleyEnergy (P n) ≤ B)
    (hlarge : Tendsto a atTop atTop) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformly
        (fun k u => ((((a (φ k) : ℝ) : ℂ) ^ 2) ^ (d (φ k)))⁻¹ *
          (cayleyNumerator (a (φ k)) (d (φ k)) (P (φ k))).eval u) g atTop := by
  refine exists_subseq_tendstoLocallyUniformly_of_eventually_bounded
    (F := fun n u => ((((a n : ℝ) : ℂ) ^ 2) ^ (d n))⁻¹ *
      (cayleyNumerator (a n) (d n) (P n)).eval u)
    (fun n => (Polynomial.differentiable_aeval _).const_mul _) fun R => ?_
  by_cases hR : 0 ≤ R
  · exact ⟨_, eventually_norm_scaledCayleyNumerator_le hd hK hdeg hE hlarge R hR⟩
  · refine ⟨0, Filter.Eventually.of_forall fun n z hz => ?_⟩
    rw [Metric.ball_eq_empty.2 (by linarith)] at hz
    exact absurd hz (Set.not_mem_empty z)

end RHTower

end
