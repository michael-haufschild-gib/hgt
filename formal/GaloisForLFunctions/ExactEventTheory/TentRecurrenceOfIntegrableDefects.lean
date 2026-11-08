import GaloisForLFunctions.ExactEventTheory.TentPairingsOfIntegrableDefects
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient
import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationDeterminesThePrimes

/-!
# Recurrence and the atomic mass floor

Tent Fourier coefficients are absolutely summable under the inverse-square moment.
The resulting observables have common distant almost periods. A fixed mass threshold
for nested atomic windows therefore persists after removing errors that vanish at infinity.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

/-- The pole and cosine-series part of a physical tent centred at `y`. -/
def tentRecurrentPart {ι : Type*} (lam : ι → ℝ) (β h y : ℝ) : ℝ :=
  h * β + (expSeriesCarrier (fun i => ((h * tentFourierWeight h (lam i) : ℝ) : ℂ))
    (fun i => 2 * Real.pi * lam i) y).re

/-- Half the atomic mass seen by a physical tent; this is the normalization of the Laplace identity. -/
def tentAtomMass {ι : Type*} (lam : ι → ℝ) (h y : ℝ) : ℝ :=
  (1 / 2) * ∑' i, unitTent (y / h) (lam i / h)

theorem unitTent_div_le_inv_sq {h u : ℝ} (hh : 0 < h) (hu : 0 < u) (n : ℝ) :
    unitTent n (u / h) ≤ (h * (n + 1)) ^ 2 * (1 / u ^ 2) := by
  by_cases hz : 1 ≤ |u / h - n|
  · rw [unitTent_eq_zero hz]
    positivity
  have hab : |u / h - n| < 1 := lt_of_not_ge hz
  have hb : u ≤ h * (n + 1) := by
    have hb' : u / h < n + 1 := by linarith only [(abs_lt.mp hab).2]
    simpa only [mul_comm] using ((div_lt_iff₀ hh).mp hb').le
  have hsq := pow_le_pow_left₀ hu.le hb 2
  rw [mul_one_div, le_div_iff₀ (sq_pos_of_pos hu)]
  calc unitTent n (u / h) * u ^ 2 ≤ 1 * u ^ 2 :=
      mul_le_mul_of_nonneg_right (unitTent_le_one _ _) (sq_nonneg _)
    _ ≤ (h * (n + 1)) ^ 2 := by simpa only [one_mul] using hsq

theorem summable_unitTent_div {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h : ℝ} (hh : 0 < h) (n : ℝ) : Summable fun i => unitTent n (lam i / h) := by
  refine Summable.of_norm_bounded (hsum.mul_left ((h * (n + 1)) ^ 2)) fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (unitTent_nonneg _ _)]
  exact unitTent_div_le_inv_sq hh (hlam i) n

/-- Tents contained in the unit gap see no positive atom. -/
theorem tentAtomMass_eq_zero_in_unit_gap {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 1 ≤ lam i) {h y : ℝ} (hh : 0 < h) (hy : y + h ≤ 1) :
    tentAtomMass lam h y = 0 := by
  have hz (i : ι) : unitTent (y / h) (lam i / h) = 0 := by
    apply unitTent_eq_zero
    have hd : 1 ≤ lam i / h - y / h := by
      rw [← sub_div, le_div_iff₀ hh]
      linarith only [hy, hlam i]
    exact hd.trans (le_abs_self _)
  simp only [tentAtomMass, hz, tsum_zero, mul_zero]

/-- A mass below one quarter excludes every atom from the tent of half the width. -/
theorem tentAtomMass_half_eq_zero_of_lt {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h y : ℝ} (hh : 0 < h) (hm : tentAtomMass lam h y < 1 / 4) :
    tentAtomMass lam (h / 2) y = 0 := by
  have hz (i : ι) : unitTent (y / (h / 2)) (lam i / (h / 2)) = 0 := by
    have hi := (summable_unitTent_div hlam hsum hh (y / h)).le_tsum i
      (fun j _ => unitTent_nonneg _ _)
    have hlt : unitTent (y / h) (lam i / h) < 1 / 2 := by
      dsimp only [tentAtomMass] at hm
      linarith only [hi, hm]
    have hd : 1 / 2 < |lam i / h - y / h| := by
      have hb : 1 - |lam i / h - y / h| ≤ unitTent (y / h) (lam i / h) := le_max_right _ _
      linarith only [hb, hlt]
    apply unitTent_eq_zero
    have he : lam i / (h / 2) - y / (h / 2) = 2 * (lam i / h - y / h) := by field_simp; ring
    rw [he, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith only [hd]
  simp only [tentAtomMass, hz, tsum_zero, mul_zero]

theorem norm_tentFourierCoefficient_le {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    ‖((h * tentFourierWeight h u : ℝ) : ℂ)‖ ≤
      (1 / (Real.pi ^ 2 * h)) * (1 / u ^ 2) := by
  have hw : 0 ≤ tentFourierWeight h u := sq_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh.le hw)]
  have hs : tentFourierWeight h u ≤ 1 / (Real.pi * (h * u)) ^ 2 := by
    rw [tentFourierWeight, div_pow]
    exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (sq_nonneg _)
  calc h * tentFourierWeight h u ≤ h * (1 / (Real.pi * (h * u)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs hh.le
    _ = _ := by field_simp

theorem summable_norm_tentFourierCoefficient {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h : ℝ} (hh : 0 < h) :
    Summable fun i => ‖((h * tentFourierWeight h (lam i) : ℝ) : ℂ)‖ := by
  refine Summable.of_norm_bounded (hsum.mul_left (1 / (Real.pi ^ 2 * h))) fun i => ?_
  rw [norm_norm]
  exact norm_tentFourierCoefficient_le hh (hlam i)

theorem tentRecurrentPart_eq {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h : ℝ} (hh : 0 < h) (β y : ℝ) :
    tentRecurrentPart lam β h y = h * β +
      h * ∑' i, Real.cos (2 * Real.pi * lam i * y) * tentFourierWeight h (lam i) := by
  rw [tentRecurrentPart, expSeriesCarrier,
    Complex.re_tsum (summable_expSeries (summable_norm_tentFourierCoefficient hlam hsum hh) _ _)]
  have he (i : ι) :
      (((h * tentFourierWeight h (lam i) : ℝ) : ℂ) * expChar (2 * Real.pi * lam i) y).re =
        h * (Real.cos (2 * Real.pi * lam i * y) * tentFourierWeight h (lam i)) := by
    simp only [Complex.re_ofReal_mul, expChar, Complex.exp_re]
    simp
    ring
  simp only [he, tsum_mul_left]

theorem continuous_tentRecurrentPart {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h : ℝ} (hh : 0 < h) (β : ℝ) : Continuous (tentRecurrentPart lam β h) :=
  continuous_const.add (Complex.continuous_re.comp
    (continuous_expSeriesCarrier (summable_norm_tentFourierCoefficient hlam hsum hh) _))

/-- Absolute Fourier convergence supplies recurrence without an arithmetic alignment premise. -/
theorem isBohrAlmostPeriodic_tentRecurrentPart {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h : ℝ} (hh : 0 < h) (β : ℝ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (tentRecurrentPart lam β h) := by
  have ha := isBohrAlmostPeriodic_expSeriesCarrier
    (summable_norm_tentFourierCoefficient hlam hsum hh) (fun i => 2 * Real.pi * lam i)
  intro ε hε
  obtain ⟨L, hL, hR⟩ := ha ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hτR⟩ := hR a
  refine ⟨τ, hτ, fun y => ?_⟩
  unfold tentRecurrentPart
  rw [add_sub_add_left_eq_sub, Real.norm_eq_abs, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (hτR y)

/-- Two physical tent widths have simultaneous returns beyond every prescribed height. -/
theorem exists_common_tent_returns {ι : Type*} {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (hsum : Summable fun i => 1 / lam i ^ 2)
    {h k ε : ℝ} (hh : 0 < h) (hk : 0 < k) (hε : 0 < ε) (β T : ℝ) :
    ∃ τ : ℝ, T ≤ τ ∧
      (∀ y, ‖tentRecurrentPart lam β h (y + τ) - tentRecurrentPart lam β h y‖ ≤ ε) ∧
      (∀ y, ‖tentRecurrentPart lam β k (y + τ) - tentRecurrentPart lam β k y‖ ≤ ε) := by
  obtain ⟨L, _, hL⟩ := exists_common_almostPeriods
    (continuous_tentRecurrentPart hlam hsum hh β)
    (isBohrAlmostPeriodic_tentRecurrentPart hlam hsum hh β)
    (continuous_tentRecurrentPart hlam hsum hk β)
    (isBohrAlmostPeriodic_tentRecurrentPart hlam hsum hk β) hε
  obtain ⟨τ, hτ, hhτ, hkτ⟩ := hL T
  exact ⟨τ, hτ.1, hhτ, hkτ⟩

/-- A threshold relation between two observables survives removal of decaying errors.
Common distant returns carry any strict threshold violation to where both errors are small. -/
theorem recurrent_threshold_of_decaying_errors
    {P Q E F : ℝ → ℝ} (hPc : Continuous P) (hPa : _root_.HTGeometry.IsBohrAlmostPeriodic P)
    (hQc : Continuous Q) (hQa : _root_.HTGeometry.IsBohrAlmostPeriodic Q)
    (hE : Tendsto E atTop (𝓝 0)) (hF : Tendsto F atTop (𝓝 0))
    {d : ℝ} (hfloor : ∀ᶠ t in atTop, P t + E t < d → Q t + F t = 0)
    {x : ℝ} (hx : P x < d) : Q x = 0 := by
  by_contra hQ
  have hQpos : 0 < |Q x| := abs_pos.mpr hQ
  let ε : ℝ := min ((d - P x) / 4) (|Q x| / 4)
  have hε : 0 < ε := lt_min (by linarith only [hx]) (by positivity)
  have hεP : ε ≤ (d - P x) / 4 := min_le_left _ _
  have hεQ : ε ≤ |Q x| / 4 := min_le_right _ _
  have hEs : ∀ᶠ t in atTop, |E t| < ε := by
    simpa only [Real.norm_eq_abs] using
      (tendsto_zero_iff_norm_tendsto_zero.mp hE).eventually (gt_mem_nhds hε)
  have hFs : ∀ᶠ t in atTop, |F t| < ε := by
    simpa only [Real.norm_eq_abs] using
      (tendsto_zero_iff_norm_tendsto_zero.mp hF).eventually (gt_mem_nhds hε)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hfloor.and (hEs.and hFs))
  obtain ⟨L, _, hL⟩ := exists_common_almostPeriods hPc hPa hQc hQa hε
  obtain ⟨τ, hτ, hPτ, hQτ⟩ := hL (T - x)
  obtain ⟨hf, he, hg⟩ := hT (x + τ) (by linarith only [hτ.1])
  have hp := (abs_le.mp (hPτ x)).2
  have he' := (abs_lt.mp he).2
  have hz : Q (x + τ) + F (x + τ) = 0 := hf (by linarith only [hp, he', hεP, hx])
  have hq : |Q x| ≤ |Q (x + τ) - Q x| + |F (x + τ)| := by
    calc |Q x| = |-(Q (x + τ) - Q x) - F (x + τ)| := by congr 1; linarith only [hz]
      _ ≤ |-(Q (x + τ) - Q x)| + |F (x + τ)| := abs_sub _ _
      _ = _ := by rw [abs_neg]
  have hqt := hQτ x
  rw [Real.norm_eq_abs] at hqt
  linarith only [hq, hqt, hg, hεQ, hQpos]

theorem summable_beurling_inv_sq (B : RHTower.BeurlingSystem)
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ))) :
    Summable fun i : B.Integer => 1 / B.intNorm i ^ 2 := by
  refine hBsum.of_nonneg_of_le (fun i => by positivity) fun i => ?_
  have hu := (B.intNorm_pos i).le
  rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hu]
  exact Real.rpow_le_rpow_of_exponent_le (B.one_le_intNorm i) (by norm_num)

/-- The actual Beurling tent mass splits into its recurrent part and its decaying boundary error. -/
theorem beurling_tent_identity (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hy : h < y) :
    tentAtomMass B.intNorm h y = tentRecurrentPart B.intNorm β h y +
      tentBoundaryError g h (y / h) := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hn : 1 < y / h := (lt_div_iff₀ hh).mpr (by simpa only [one_mul] using hy)
  have hid := tent_boundary_identity_of_theta_defect hsupp hmom hgm hgb hgi hθ hh hh1 hn
  have he (u : ℝ) : 2 * Real.pi * (h * u) * (y / h) = 2 * Real.pi * u * y := by
    field_simp
  simp only [integral_beurlingSystemIntegerMeasure_eq_tsum, he] at hid
  rw [tentRecurrentPart_eq B.intNorm_pos (summable_beurling_inv_sq B hBsum) hh]
  dsimp only [tentAtomMass, tentBoundaryError]
  linarith only [hid]

theorem tendsto_physicalTentBoundaryError {g : ℝ → ℂ} (hg : Integrable g)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun y : ℝ => tentBoundaryError g h (y / h)) atTop (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ => y / h) atTop atTop := by
    refine tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨b * h, fun y hy => ?_⟩
    exact (le_div_iff₀ hh).mpr hy
  exact (tendsto_tentBoundaryError_atTop hg hh).comp ht

/-- A nonlinear spectral restriction forced by the atomic floor, the FE, and recurrence.
No recurrence or smallness assumption on the FE defect is needed. -/
theorem beurling_tentRecurrentPart_half_eq_zero (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hy : tentRecurrentPart B.intNorm β h y < 1 / 4) :
    tentRecurrentPart B.intNorm β (h / 2) y = 0 := by
  have hsum := summable_beurling_inv_sq B hBsum
  have hh2 : 0 < h / 2 := by positivity
  apply recurrent_threshold_of_decaying_errors
    (continuous_tentRecurrentPart B.intNorm_pos hsum hh β)
    (isBohrAlmostPeriodic_tentRecurrentPart B.intNorm_pos hsum hh β)
    (continuous_tentRecurrentPart B.intNorm_pos hsum hh2 β)
    (isBohrAlmostPeriodic_tentRecurrentPart B.intNorm_pos hsum hh2 β)
    (tendsto_physicalTentBoundaryError hgi hh)
    (tendsto_physicalTentBoundaryError hgi hh2) ?_ hy
  refine eventually_atTop.mpr ⟨h + 1, fun x hx => ?_⟩
  rw [← beurling_tent_identity B hBsum hgm hgb hgi hθ hh hh1 (by linarith only [hx]),
    ← beurling_tent_identity B hBsum hgm hgb hgi hθ hh2 (by linarith only [hh1, hh])
      (by linarith only [hx, hh])]
  exact tentAtomMass_half_eq_zero_of_lt B.intNorm_pos hsum hh

end GaloisForLFunctions.ExactEventTheory

#print axioms GaloisForLFunctions.ExactEventTheory.exists_common_tent_returns
#print axioms GaloisForLFunctions.ExactEventTheory.recurrent_threshold_of_decaying_errors
#print axioms GaloisForLFunctions.ExactEventTheory.beurling_tentRecurrentPart_half_eq_zero
