import GaloisForLFunctions.RHTower.BandKaiserL2Trial

/-!
# Complexification of the conditioned Kaiser packet span

The actual prolate carrier is complex.  The real packet estimate extends without loss because
every packet and every even Fourier reading is real-valued.  Thus real and imaginary coefficient
parts are Pythagorean both before and after the compressed Fourier operator.
-/

open MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The Fourier transform of a continuous even real aperture function is real, with its exact
cosine-transform value. -/
theorem fourier_bandTrunc_eq_ofReal_cosine {Phi : ℝ → ℝ}
    (hPhi : Continuous Phi) (heven : Function.Even Phi) (xi : ℝ) :
    FourierTransform.fourier (bandTrunc Phi) xi =
      ((∫ x in (-1 : ℝ)..1,
        Phi x * Real.cos (2 * Real.pi * xi * x) : ℝ) : ℂ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfreq : -(-(2 * Real.pi * xi) / (2 * Real.pi)) = xi := by
    field_simp
  have hband : FourierTransform.fourier (bandTrunc Phi) xi =
      bandFourier (-(2 * Real.pi * xi)) Phi := by
    rw [bandFourier_eq_fourier (-(2 * Real.pi * xi)) Phi, hfreq]
  rw [hband, bandFourier_of_even hPhi heven]
  congr 2
  funext x
  rw [show -(2 * Real.pi * xi) * x = -(2 * Real.pi * xi * x) by ring,
    Real.cos_neg]

theorem fourier_bandTrunc_kaiserGridCombination_im {m : ℕ}
    (c : ℝ) (b : Fin m → ℝ) (xi : ℝ) :
    (FourierTransform.fourier
      (bandTrunc (kaiserGridCombination c b)) xi).im = 0 := by
  rw [fourier_bandTrunc_eq_ofReal_cosine
    (continuous_kaiserGridCombination c b)
    (kaiserCosCombination_even c (kaiserPacketFrequency c) b)]
  exact Complex.ofReal_im _

/-- Two real Kaiser combinations have real `L²` pairing. -/
theorem inner_kaiserGridEven_im_eq_zero {m : ℕ}
    (c : ℝ) (b d : Fin m → ℝ) :
    (inner ℂ (kaiserGridEven c b) (kaiserGridEven c d)).im = 0 := by
  change (inner ℂ (kaiserGridL2 c b) (kaiserGridL2 c d)).im = 0
  rw [MeasureTheory.L2.inner_def]
  change RCLike.im (∫ x : ℝ,
    inner ℂ ((kaiserGridL2 c b : ℝ → ℂ) x)
      ((kaiserGridL2 c d : ℝ → ℂ) x)) = 0
  rw [
    ← integral_im (MeasureTheory.L2.integrable_inner (kaiserGridL2 c b) (kaiserGridL2 c d))]
  apply integral_eq_zero_of_ae
  filter_upwards [kaiserGridL2_coeFn c b, kaiserGridL2_coeFn c d] with x hb hd
  rw [RCLike.inner_apply, hb, hd]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp [bandTrunc, hx]
  · simp [bandTrunc, hx]

/-- Frequency-truncated transforms of two real even Kaiser combinations also have real pairing. -/
theorem inner_fourierCutoff_kaiserGridEven_im_eq_zero {m : ℕ}
    (c r : ℝ) (b d : Fin m → ℝ) :
    (inner ℂ
      (evenIndicatorCutoff r (evenFourierTransform (kaiserGridEven c b)))
      (evenIndicatorCutoff r (evenFourierTransform (kaiserGridEven c d)))).im = 0 := by
  change (inner ℂ
    (indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
      (fourierUnitary (kaiserGridL2 c b)))
    (indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
      (fourierUnitary (kaiserGridL2 c d)))).im = 0
  rw [MeasureTheory.L2.inner_def]
  change RCLike.im (∫ x : ℝ,
    inner ℂ
      (((indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
        (fourierUnitary (kaiserGridL2 c b)) : SoninL2) : ℝ → ℂ) x)
      (((indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
        (fourierUnitary (kaiserGridL2 c d)) : SoninL2) : ℝ → ℂ) x)) = 0
  rw [
    ← integral_im (MeasureTheory.L2.integrable_inner
      (indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
        (fourierUnitary (kaiserGridL2 c b)))
      (indicatorCutoff (centralInterval r) (measurableSet_centralInterval r)
        (fourierUnitary (kaiserGridL2 c d))))]
  apply integral_eq_zero_of_ae
  filter_upwards [indicatorCutoff_ae (centralInterval r)
      (measurableSet_centralInterval r) (fourierUnitary (kaiserGridL2 c b)),
    indicatorCutoff_ae (centralInterval r)
      (measurableSet_centralInterval r) (fourierUnitary (kaiserGridL2 c d)),
    fourierUnitary_kaiserGridL2_coeFn c b,
    fourierUnitary_kaiserGridL2_coeFn c d] with xi hbcut hdcut hb hd
  rw [RCLike.inner_apply, hbcut, hdcut]
  by_cases hxi : xi ∈ centralInterval r
  · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hxi, hb, hd]
    have hbim := fourier_bandTrunc_kaiserGridCombination_im c b xi
    have hdim := fourier_bandTrunc_kaiserGridCombination_im c d xi
    simp_all [Complex.mul_im]
  · rw [Set.indicator_of_notMem hxi, Set.indicator_of_notMem hxi]
    simp

/-- A complex coefficient vector is represented by its real and imaginary Kaiser combinations. -/
def kaiserPhysicalGridComplex {m : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Fin m → ℂ) : evenSubspace :=
  kaiserPhysicalGridEven a ha (fun j => (z j).re) +
    Complex.I • kaiserPhysicalGridEven a ha (fun j => (z j).im)

/-- Pythagoras for the physical complex packet before applying the time-band operator. -/
theorem norm_sq_kaiserPhysicalGridComplex {m : ℕ} {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℂ) :
    ‖kaiserPhysicalGridComplex a ha z‖ ^ (2 : ℕ) =
      ‖kaiserPhysicalGridEven a ha (fun j => (z j).re)‖ ^ (2 : ℕ) +
        ‖kaiserPhysicalGridEven a ha (fun j => (z j).im)‖ ^ (2 : ℕ) := by
  let u := kaiserPhysicalGridEven a ha (fun j => (z j).re)
  let v := kaiserPhysicalGridEven a ha (fun j => (z j).im)
  have huvIm : (inner ℂ u v).im = 0 := by
    change (inner ℂ
      (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)
        (kaiserGridEven (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (z j).re)))
      (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)
        (kaiserGridEven (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (z j).im)))).im = 0
    rw [(evenDilationUnitary a⁻¹ (inv_pos.mpr ha)).inner_map_map]
    exact inner_kaiserGridEven_im_eq_zero _ _ _
  have hcross : RCLike.re (inner ℂ u (Complex.I • v)) = 0 := by
    have heq : inner ℂ u (Complex.I • v) =
        Complex.I * inner ℂ u v := inner_smul_right u v Complex.I
    rw [heq]
    simpa [Complex.mul_re, huvIm]
  change ‖u + Complex.I • v‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ)
  rw [norm_add_sq (𝕜 := ℂ), hcross, norm_smul, Complex.norm_I]
  ring

/-- Pythagoras is preserved after the actual compressed Fourier operator. -/
theorem norm_sq_timeBand_kaiserPhysicalGridComplex {m : ℕ}
    {a : ℝ} (ha : 0 < a) (z : Fin m → ℂ) :
    ‖evenTimeBandFourier a (kaiserPhysicalGridComplex a ha z)‖ ^ (2 : ℕ) =
      ‖evenTimeBandFourier a
          (kaiserPhysicalGridEven a ha (fun j => (z j).re))‖ ^ (2 : ℕ) +
        ‖evenTimeBandFourier a
          (kaiserPhysicalGridEven a ha (fun j => (z j).im))‖ ^ (2 : ℕ) := by
  let u := kaiserPhysicalGridEven a ha (fun j => (z j).re)
  let v := kaiserPhysicalGridEven a ha (fun j => (z j).im)
  have huvIm :
      (inner ℂ (evenTimeBandFourier a u) (evenTimeBandFourier a v)).im = 0 := by
    let c : ℝ := 2 * Real.pi * a ^ (2 : ℕ)
    have hre := evenTimeBandFourier_evenDilation_inv_kaiserGridEven
      ha c (fun j => (z j).re)
    have him := evenTimeBandFourier_evenDilation_inv_kaiserGridEven
      ha c (fun j => (z j).im)
    change (inner ℂ
      (evenTimeBandFourier a
        (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)
          (kaiserGridEven c (fun j => (z j).re))))
      (evenTimeBandFourier a
        (evenDilationUnitary a⁻¹ (inv_pos.mpr ha)
          (kaiserGridEven c (fun j => (z j).im))))).im = 0
    rw [hre, him, (evenDilationUnitary a ha).inner_map_map]
    exact inner_fourierCutoff_kaiserGridEven_im_eq_zero _ _ _ _
  have hcross : RCLike.re
      (inner ℂ (evenTimeBandFourier a u)
        (Complex.I • evenTimeBandFourier a v)) = 0 := by
    have heq : inner ℂ (evenTimeBandFourier a u)
        (Complex.I • evenTimeBandFourier a v) =
      Complex.I * inner ℂ (evenTimeBandFourier a u) (evenTimeBandFourier a v) :=
        by simpa only using
          (inner_smul_right (evenTimeBandFourier a u) (evenTimeBandFourier a v) Complex.I)
    rw [heq]
    simpa [Complex.mul_re, huvIm]
  change ‖evenTimeBandFourier a (u + Complex.I • v)‖ ^ (2 : ℕ) = _
  rw [map_add, map_smul, norm_add_sq (𝕜 := ℂ), hcross, norm_smul, Complex.norm_I]
  ring

/-- The uniform real packet estimate extends to arbitrary complex coefficients with no loss. -/
theorem eventually_exp_mul_timeBand_defect_kaiserPhysicalGridComplex_le {m : ℕ}
    (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ (ha : 0 < a) (z : Fin m → ℂ),
      Real.exp ((2 - ε) * (2 * Real.pi * a ^ (2 : ℕ))) *
          (‖kaiserPhysicalGridComplex a ha z‖ ^ (2 : ℕ) -
            ‖evenTimeBandFourier a (kaiserPhysicalGridComplex a ha z)‖ ^ (2 : ℕ)) ≤
        ‖kaiserPhysicalGridComplex a ha z‖ ^ (2 : ℕ) := by
  have hreal := eventually_exp_mul_timeBand_defect_kaiserPhysicalGridEven_le hm hε
  filter_upwards [hreal] with a haReal
  intro ha z
  have hre := haReal ha (fun j => (z j).re)
  have him := haReal ha (fun j => (z j).im)
  rw [norm_sq_kaiserPhysicalGridComplex ha,
    norm_sq_timeBand_kaiserPhysicalGridComplex ha]
  linarith

/-! ## Complex-linear synthesis and dimension -/

theorem kaiserGridEven_add {m : ℕ} (c : ℝ) (b d : Fin m → ℝ) :
    kaiserGridEven c (b + d) = kaiserGridEven c b + kaiserGridEven c d := by
  apply Subtype.ext
  apply Lp.ext
  change (kaiserGridL2 c (b + d) : ℝ → ℂ) =ᵐ[volume]
    ((kaiserGridL2 c b + kaiserGridL2 c d : SoninL2) : ℝ → ℂ)
  filter_upwards [kaiserGridL2_coeFn c (b + d),
    Lp.coeFn_add (kaiserGridL2 c b) (kaiserGridL2 c d),
    kaiserGridL2_coeFn c b, kaiserGridL2_coeFn c d] with x hbd hadd hb hd
  rw [hbd, hadd, Pi.add_apply, hb, hd]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp only [bandTrunc, Set.indicator_of_mem hx]
    norm_cast
    simp only [kaiserGridCombination, kaiserCosCombination, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [bandTrunc, hx]

theorem kaiserGridEven_smul_real {m : ℕ} (c r : ℝ) (b : Fin m → ℝ) :
    kaiserGridEven c (r • b) = r • kaiserGridEven c b := by
  apply Subtype.ext
  apply Lp.ext
  change (kaiserGridL2 c (r • b) : ℝ → ℂ) =ᵐ[volume]
    (((r : ℂ) • kaiserGridL2 c b : SoninL2) : ℝ → ℂ)
  filter_upwards [kaiserGridL2_coeFn c (r • b),
    Lp.coeFn_smul (r : ℂ) (kaiserGridL2 c b),
    kaiserGridL2_coeFn c b] with x hrb hsmul hb
  rw [hrb, hsmul, Pi.smul_apply, hb]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp only [bandTrunc, Set.indicator_of_mem hx]
    norm_cast
    simp only [kaiserGridCombination, kaiserCosCombination, Pi.smul_apply, smul_eq_mul]
    push_cast
    change (∑ j, (r : ℂ) * (b j : ℂ) *
      (kaiserCosTrial c (kaiserPacketFrequency c j) x : ℂ)) =
        (r : ℂ) * ∑ j, (b j : ℂ) *
          (kaiserCosTrial c (kaiserPacketFrequency c j) x : ℂ)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [bandTrunc, hx]

/-- Real-linear normalized Kaiser synthesis. -/
def kaiserGridEvenRealLinear {m : ℕ} (c : ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] evenSubspace where
  toFun := kaiserGridEven c
  map_add' := kaiserGridEven_add c
  map_smul' := kaiserGridEven_smul_real c

/-- Coordinate unit vector used for packet synthesis. -/
def kaiserGridCoordinate {m : ℕ} (j : Fin m) : Fin m → ℝ :=
  fun k => if k = j then 1 else 0

theorem sum_smul_kaiserGridCoordinate {m : ℕ} (b : Fin m → ℝ) :
    ∑ j, b j • kaiserGridCoordinate j = b := by
  funext k
  simp [kaiserGridCoordinate]

theorem sum_real_smul_kaiserGridEven_coordinate {m : ℕ}
    (c : ℝ) (b : Fin m → ℝ) :
    ∑ j, (b j : ℂ) • kaiserGridEven c (kaiserGridCoordinate j) =
      kaiserGridEven c b := by
  let R := kaiserGridEvenRealLinear (m := m) c
  change ∑ j, (b j : ℂ) • R (kaiserGridCoordinate j) = R b
  have hreal : ∀ j,
      (b j : ℂ) • R (kaiserGridCoordinate j) =
        b j • R (kaiserGridCoordinate j) := by
    intro j
    rfl
  simp_rw [hreal]
  have h := congrArg R (sum_smul_kaiserGridCoordinate b)
  simpa only [map_sum, map_smul] using h

theorem sum_real_smul_kaiserPhysicalGridEven_coordinate {m : ℕ}
    {a : ℝ} (ha : 0 < a) (b : Fin m → ℝ) :
    ∑ j, (b j : ℂ) •
        kaiserPhysicalGridEven a ha (kaiserGridCoordinate j) =
      kaiserPhysicalGridEven a ha b := by
  rw [kaiserPhysicalGridEven]
  simp_rw [kaiserPhysicalGridEven, ← map_smul,
    ← map_sum, sum_real_smul_kaiserGridEven_coordinate]

/-- Complex-linear synthesis of the physical conditioned packet family. -/
def kaiserPhysicalGridSynthesis {m : ℕ} (a : ℝ) (ha : 0 < a) :
    (Fin m → ℂ) →ₗ[ℂ] evenSubspace where
  toFun z := ∑ j, z j • kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)
  map_add' z w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' alpha z := by
    change (∑ j, (alpha * z j) •
      kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) =
        alpha • ∑ j, z j •
          kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul]

theorem kaiserPhysicalGridSynthesis_apply {m : ℕ} {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℂ) :
    kaiserPhysicalGridSynthesis a ha z = kaiserPhysicalGridComplex a ha z := by
  change (∑ j, z j • kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) =
    kaiserPhysicalGridEven a ha (fun j => (z j).re) +
      Complex.I • kaiserPhysicalGridEven a ha (fun j => (z j).im)
  have hz : ∀ j, z j = ((z j).re : ℂ) + ((z j).im : ℂ) * Complex.I := by
    intro j
    exact (Complex.re_add_im (z j)).symm
  calc
    (∑ j, z j • kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) =
        ∑ j, (((z j).re : ℂ) + ((z j).im : ℂ) * Complex.I) •
          kaiserPhysicalGridEven a ha (kaiserGridCoordinate j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg
        (fun alpha : ℂ => alpha •
          kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) (hz j)
    _ = (∑ j, ((z j).re : ℂ) •
          kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) +
        ∑ j, (((z j).im : ℂ) * Complex.I) •
          kaiserPhysicalGridEven a ha (kaiserGridCoordinate j) := by
      simp only [add_smul, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_real_smul_kaiserPhysicalGridEven_coordinate ha]
      congr 1
      calc
        (∑ j, (((z j).im : ℂ) * Complex.I) •
            kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) =
            ∑ j, Complex.I • (((z j).im : ℂ) •
              kaiserPhysicalGridEven a ha (kaiserGridCoordinate j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_comm, mul_smul]
        _ = Complex.I • ∑ j, ((z j).im : ℂ) •
              kaiserPhysicalGridEven a ha (kaiserGridCoordinate j) := by
          rw [Finset.smul_sum]
        _ = _ := by
          rw [sum_real_smul_kaiserPhysicalGridEven_coordinate ha]

/-- The physical packet synthesis is injective once the real energy lower bound is active. -/
theorem kaiserPhysicalGridSynthesis_injective {m : ℕ} (hm : 0 < m)
    {a : ℝ} (ha : 0 < a)
    (hc : 1 ≤ 2 * Real.pi * a ^ (2 : ℕ))
    (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt (2 * Real.pi * a ^ (2 : ℕ)))
    (hsmall : 32 * (m : ℝ) *
      Real.exp (-(Real.sqrt (2 * Real.pi * a ^ (2 : ℕ)) / 2)) ≤ 1) :
    Function.Injective (kaiserPhysicalGridSynthesis (m := m) a ha) := by
  intro z w hzw
  apply sub_eq_zero.mp
  let q : Fin m → ℂ := z - w
  have hqzero : kaiserPhysicalGridComplex a ha q = 0 := by
    rw [← kaiserPhysicalGridSynthesis_apply]
    change kaiserPhysicalGridSynthesis a ha (z - w) = 0
    rw [map_sub, hzw, sub_self]
  have hnorm : ‖kaiserPhysicalGridComplex a ha q‖ ^ (2 : ℕ) = 0 := by simp [hqzero]
  have hreEnergy := exp_sq_mul_coeffEnergy_le_kaiserGridEnergy hm hc hscale hsmall
    (fun j => (q j).re)
  have himEnergy := exp_sq_mul_coeffEnergy_le_kaiserGridEnergy hm hc hscale hsmall
    (fun j => (q j).im)
  have hnormSplit := norm_sq_kaiserPhysicalGridComplex ha q
  rw [norm_sq_kaiserPhysicalGridEven, norm_sq_kaiserPhysicalGridEven] at hnormSplit
  rw [hnorm] at hnormSplit
  have hreCoeff : (∑ j, (q j).re ^ (2 : ℕ)) = 0 := by
    have hexp : 0 < Real.exp (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
    have hreNonneg : 0 ≤ (∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (q j).re) x ^ (2 : ℕ)) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
    have himNonneg : 0 ≤ (∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (q j).im) x ^ (2 : ℕ)) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
    have hre0 : (∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (q j).re) x ^ (2 : ℕ)) = 0 := by
      nlinarith [hnormSplit]
    rw [hre0, mul_zero] at hreEnergy
    have hsum0 : 0 ≤ ∑ j, (q j).re ^ (2 : ℕ) := Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  have himCoeff : (∑ j, (q j).im ^ (2 : ℕ)) = 0 := by
    have hexp : 0 < Real.exp (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
    have hreNonneg : 0 ≤ (∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (q j).re) x ^ (2 : ℕ)) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
    have himNonneg : 0 ≤ (∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (q j).im) x ^ (2 : ℕ)) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
    have him0 : (∫ x in (-1 : ℝ)..1,
        kaiserGridCombination (2 * Real.pi * a ^ (2 : ℕ)) (fun j => (q j).im) x ^ (2 : ℕ)) = 0 := by
      nlinarith [hnormSplit]
    rw [him0, mul_zero] at himEnergy
    have hsum0 : 0 ≤ ∑ j, (q j).im ^ (2 : ℕ) := Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  funext j
  have hre : (q j).re = 0 := by
    have hle : (q j).re ^ (2 : ℕ) ≤ ∑ k, (q k).re ^ (2 : ℕ) :=
      Finset.single_le_sum (fun k _ => sq_nonneg ((q k).re)) (Finset.mem_univ j)
    nlinarith [sq_nonneg ((q j).re), hreCoeff]
  have him : (q j).im = 0 := by
    have hle : (q j).im ^ (2 : ℕ) ≤ ∑ k, (q k).im ^ (2 : ℕ) :=
      Finset.single_le_sum (fun k _ => sq_nonneg ((q k).im)) (Finset.mem_univ j)
    nlinarith [sq_nonneg ((q j).im), himCoeff]
  change q j = 0
  exact Complex.ext hre him

end RHTower

end
