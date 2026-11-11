import GaloisForLFunctions.RHTower.UniformEulerTargetDensityOnZeroFreeDiscs
import GaloisForLFunctions.RHTower.EulerProductDiscUniformCarlsonTail

/-!
# Uniform lower bounds for zeta at typical heights

The logarithm of an Euler-product tail is a prime sum plus an absolutely convergent
remainder. Its Hardy-space second moment controls the prime sum on a disc outside
arbitrarily small Haar measure, uniformly in the cutoff. The fixed Euler head has
a positive lower bound. The prime flow and the disc-uniform Euler approximation
transfer this lower bound to zeta at all but a small proportion of heights.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- Every Euler factor has modulus at least one half in the right half-plane. -/
theorem half_pow_card_le_norm_eulerPhaseProduct (y : ℕ) (ω : Nat.Primes → Circle)
    {z : ℂ} (hz : 0 < z.re) :
    (1 / 2 : ℝ) ^ (primesLE y).card ≤ ‖eulerPhaseProduct y ω z‖ := by
  rw [eulerPhaseProduct, norm_prod, ← prod_const]
  refine prod_le_prod (fun _ _ => by positivity) fun p _ => ?_
  rw [norm_inv]
  have hpos : 0 < ‖1 - (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ :=
    norm_pos_iff.mpr (one_sub_phase_cpow_ne_zero p (ω p) hz)
  have hle : ‖1 - (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ ≤ 2 := by
    calc ‖1 - (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖
        ≤ ‖(1 : ℂ)‖ + ‖(ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_mul, Circle.norm_coe, one_mul]
        linarith [norm_prime_cpow_neg_lt_one_of_pos_re p hz]
  simpa only [one_div] using inv_anti₀ hpos hle

/-- A bounded Hardy prime tail prevents the Euler product from becoming small. -/
theorem eulerPhaseProduct_lower_of_primeTail (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < z₀.re - ρ) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1)
    {y₀ y : ℕ} (hy : y₀ ≤ y) (x : UnitAddTorus Nat.Primes)
    (hsum : ‖torusPrimePhaseSum (primesLE y \ primesLE y₀)
      (primeVectorOf z₀ hρ.le) x‖ ≤ 1)
    (hrem : ∑ n ∈ Finset.Ico (y₀ + 1) (y + 1),
      (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 *
        (n : ℝ) ^ (-(2 * (z₀.re - ρ))) ≤ 1)
    {z : ℂ} (hz : z ∈ closedBall z₀ (ρ * r₁)) :
    (1 / 2 : ℝ) ^ (primesLE y₀).card *
      Real.exp (-(Real.sqrt ((1 - r₁ ^ 2)⁻¹) + 1)) ≤
        ‖eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) z‖ := by
  have hzre : z₀.re - ρ ≤ z.re := by
    have := re_ge_of_mem_closedBall_center hz
    have := mul_le_mul_of_nonneg_left hr₁.le hρ.le
    linarith
  have hzpos := lt_of_lt_of_le hσ hzre
  have hq : ‖(z - z₀) / ρ‖ ≤ r₁ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_le_iff₀ hρ]
    have := mem_closedBall_iff_norm.mp hz
    linarith
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hz' : z₀ + ρ * ((z - z₀) / ρ) = z := by
    rw [mul_div_cancel₀ _ hρne]
    ring
  let B := primesLE y \ primesLE y₀
  let ω := unitTorusHomeomorphCircles Nat.Primes x
  let S : ℂ := ∑ p ∈ B, (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z) +
    ∑ p ∈ B, eulerLogRemainder (ω p : ℂ) z (p : ℕ)
  have hlin : ‖∑ p ∈ B, (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ ≤
      Real.sqrt ((1 - r₁ ^ 2)⁻¹) := by
    have h := norm_sum_torusPhase_cpow_le z₀ hρ.le B x hr₁0 hr₁ hq
    rw [hz'] at h
    exact h.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg ((1 - r₁ ^ 2)⁻¹)))
  have hremB : ‖∑ p ∈ B, eulerLogRemainder (ω p : ℂ) z (p : ℕ)‖ ≤ 1 := by
    refine (norm_sum_eulerLogRemainder_block_le B ω hσ hzre).trans ?_
    exact (sum_primesLE_sdiff_le_sum_Ico
      (F := fun n : ℕ => (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 *
        (n : ℝ) ^ (-(2 * (z₀.re - ρ))))
      (fun n => mul_nonneg (eulerRemainderConstant_nonneg hσ) (by positivity)) y₀ y).trans hrem
  have hS : ‖S‖ ≤ Real.sqrt ((1 - r₁ ^ 2)⁻¹) + 1 :=
    (norm_add_le _ _).trans (add_le_add hlin hremB)
  have hlow : -(Real.sqrt ((1 - r₁ ^ 2)⁻¹) + 1) ≤ S.re := by
    have := (abs_le.mp (Complex.abs_re_le_norm S)).1
    linarith
  rw [eulerPhaseProduct_eq_mul_block hy, eulerBlock_eq_exp B ω hzpos, norm_mul,
    Complex.norm_exp]
  exact mul_le_mul (half_pow_card_le_norm_eulerPhaseProduct y₀ ω hzpos)
    (Real.exp_le_exp.mpr hlow) (by positivity) (norm_nonneg _)

/-- For every cutoff beyond a fixed head, most prime phases give the same positive
lower bound on the whole disc. The exceptional proportion is uniform in the cutoff. -/
theorem exists_uniform_eulerPhaseProduct_floor (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 < z₀.re - ρ) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b > 0, ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ∃ U : Set (Nat.Primes → Circle), IsOpen U ∧
        torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹' U)ᶜ ≤
          ENNReal.ofReal δ ∧
        ∀ ω ∈ U, ∀ z ∈ closedBall z₀ (ρ * r₁), b ≤ ‖eulerPhaseProduct y ω z‖ := by
  have hσ0 : 0 < z₀.re - ρ := by linarith
  let C := max ((1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2) 1
  have hC0 : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCrem : (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 ≤ C := le_max_left _ _
  obtain ⟨y₀, -, htail⟩ := exists_remainder_tail_le hσ hC0 (lt_min zero_lt_one hδ) 0
  refine ⟨(1 / 2 : ℝ) ^ (primesLE y₀).card *
    Real.exp (-(Real.sqrt ((1 - r₁ ^ 2)⁻¹) + 1)), by positivity, y₀, fun y hy => ?_⟩
  let B := primesLE y \ primesLE y₀
  let u := primeVectorOf z₀ hρ.le
  let V : Set (UnitAddTorus Nat.Primes) := {x | ‖torusPrimePhaseSum B u x‖ < 1}
  have hV : IsOpen V := isOpen_lt (continuous_torusPrimePhaseSum B u).norm continuous_const
  let U := (unitTorusHomeomorphCircles Nat.Primes).symm ⁻¹' V
  have hpre : unitTorusHomeomorphCircles Nat.Primes ⁻¹' U = V := by
    ext x
    simp only [U, Set.mem_preimage, Homeomorph.symm_apply_apply]
  refine ⟨U, hV.preimage (unitTorusHomeomorphCircles Nat.Primes).symm.continuous, ?_, ?_⟩
  · rw [hpre]
    have heq : Vᶜ = {x | 1 ≤ ‖torusPrimePhaseSum B u x‖} := by
      ext x
      simp only [V, mem_compl_iff, mem_setOf_eq, not_lt]
    rw [heq]
    refine (measure_torusPrimePhaseSum_ge_le B u zero_lt_one).trans
      (ENNReal.ofReal_le_ofReal ?_)
    simp only [one_pow, div_one]
    calc ∑ p ∈ B, ‖u p‖ ^ 2
        ≤ ∑ p ∈ B, C * ((p : ℕ) : ℝ) ^ (-(2 * (z₀.re - ρ))) :=
          sum_le_sum fun p _ => (norm_primeVectorOf_sq_le z₀ hρ.le p).trans
            (le_mul_of_one_le_left (by positivity) hC1)
      _ ≤ ∑ n ∈ Finset.Ico (y₀ + 1) (y + 1), C * (n : ℝ) ^ (-(2 * (z₀.re - ρ))) :=
          sum_primesLE_sdiff_le_sum_Ico
            (F := fun n : ℕ => C * (n : ℝ) ^ (-(2 * (z₀.re - ρ))))
            (fun n => by positivity) y₀ y
      _ ≤ min 1 δ := htail _
      _ ≤ δ := min_le_right _ _
  · intro ω hω z hz
    let x := (unitTorusHomeomorphCircles Nat.Primes).symm ω
    have hx : ‖torusPrimePhaseSum B u x‖ ≤ 1 := le_of_lt hω
    have hrem : ∑ n ∈ Finset.Ico (y₀ + 1) (y + 1),
        (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 *
          (n : ℝ) ^ (-(2 * (z₀.re - ρ))) ≤ 1 := by
      refine (sum_le_sum fun n _ => mul_le_mul_of_nonneg_right hCrem (by positivity)).trans ?_
      exact (htail _).trans (min_le_left _ _)
    simpa only [x, Homeomorph.apply_symm_apply] using
      eulerPhaseProduct_lower_of_primeTail z₀ hρ hσ0 hr₁0 hr₁ hy x hx hrem hz

/-- An open phase event whose complement has small Haar mass misses only a small
proportion of the prime flow. -/
theorem eventually_volume_primeFlow_compl_le {U : Set (Nat.Primes → Circle)}
    (hU : IsOpen U) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbad : torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹' U)ᶜ ≤
      ENNReal.ofReal (δ / 2)) :
    ∀ᶠ T : ℝ in atTop,
      volume ((circlePhaseFlow primeFrequency ⁻¹' U)ᶜ ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  let V := unitTorusHomeomorphCircles Nat.Primes ⁻¹' U
  have hV : MeasurableSet V := (hU.preimage (unitTorusHomeomorphCircles Nat.Primes).continuous).measurableSet
  have hlower : ENNReal.ofReal (1 - δ / 2) ≤ torusHaar Nat.Primes V := by
    have heq : torusHaar Nat.Primes V = 1 - torusHaar Nat.Primes Vᶜ := by
      rw [← prob_compl_eq_one_sub hV.compl, compl_compl]
    rw [heq, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    exact tsub_le_tsub_left hbad 1
  have hreal : 1 - δ / 2 ≤ (torusHaar Nat.Primes V).toReal := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hlower
    rwa [ENNReal.toReal_ofReal (by linarith)] at h
  have hflow := eventually_ofReal_mul_le_volume_preimage_primeFlow hU
    (show 1 - δ < (torusHaar Nat.Primes V).toReal by linarith)
  let A := circlePhaseFlow primeFrequency ⁻¹' U
  have hA : MeasurableSet A := (hU.preimage (continuous_circlePhaseFlow _)).measurableSet
  filter_upwards [hflow, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  have hsplit : volume (A ∩ Icc 0 T) + volume (Aᶜ ∩ Icc 0 T) = ENNReal.ofReal T := by
    have h := measure_add_measure_compl (μ := volume.restrict (Icc 0 T)) hA
    simpa only [Measure.restrict_apply hA, Measure.restrict_apply hA.compl,
      Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] using h
  have hsum : ENNReal.ofReal ((1 - δ) * T) + volume (Aᶜ ∩ Icc 0 T) ≤
      ENNReal.ofReal ((1 - δ) * T) + ENNReal.ofReal (δ * T) := by
    calc ENNReal.ofReal ((1 - δ) * T) + volume (Aᶜ ∩ Icc 0 T)
        ≤ volume (A ∩ Icc 0 T) + volume (Aᶜ ∩ Icc 0 T) := add_le_add hT le_rfl
      _ = ENNReal.ofReal T := hsplit
      _ = ENNReal.ofReal ((1 - δ) * T) + ENNReal.ofReal (δ * T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  exact (ENNReal.add_le_add_iff_left (by simp)).mp hsum

/-- On every disc strictly right of the critical line, zeta has a fixed positive
lower bound outside an arbitrarily small proportion of vertical translates. -/
theorem exists_zeta_disc_floor_at_typical_heights {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b > 0, ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | ∃ z ∈ closedBall c r, ‖riemannZeta (z + τ * I)‖ < b} ∩ Icc 0 T)
        ≤ ENNReal.ofReal (δ * T) := by
  let η := min (δ / 2) (1 / 2)
  have hη : 0 < η := lt_min (half_pos hδ) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηδ : 2 * η ≤ δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  obtain ⟨b, hb, y₀, hy₀⟩ := exists_uniform_eulerPhaseProduct_floor c
    (show 0 < 2 * r by positivity) h0 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num) (half_pos hη)
  have htail := eventually_eventually_volume_eulerDiscTailBadSet_le hr h0 h1 (half_pos hb) hη
  obtain ⟨y, hy, hytail⟩ := ((eventually_ge_atTop y₀).and htail).exists
  obtain ⟨U, hU, hUbad, hUfloor⟩ := hy₀ y hy
  have hflow := eventually_volume_primeFlow_compl_le hU hη hη1 hUbad
  refine ⟨b / 2, half_pos hb, ?_⟩
  filter_upwards [hflow, hytail, eventually_ge_atTop (0 : ℝ)] with T hTflow hTtail hT0
  have hsub : {τ : ℝ | ∃ z ∈ closedBall c r, ‖riemannZeta (z + τ * I)‖ < b / 2} ∩ Icc 0 T
      ⊆ ((circlePhaseFlow primeFrequency ⁻¹' U)ᶜ ∩ Icc 0 T) ∪
        (eulerDiscTailBadSet y c r (b / 2) ∩ Icc 0 T) := by
    rintro τ ⟨⟨z, hz, hzsmall⟩, hτT⟩
    by_cases hτU : circlePhaseFlow primeFrequency τ ∈ U
    · right
      refine ⟨?_, hτT⟩
      have hz' : z ∈ closedBall c (2 * r * (1 / 2)) := by
        simpa only [show 2 * r * (1 / 2) = r by ring] using hz
      have hfloor := hUfloor _ hτU z hz'
      rw [eulerPhaseProduct_circlePhaseFlow] at hfloor
      refine ⟨z, hz, ?_⟩
      change b / 2 ≤ ‖riemannZeta (z + τ * I) - eulerPhaseProduct y 1 (z + τ * I)‖
      have hnorm := norm_sub_norm_le (eulerPhaseProduct y 1 (z + τ * I))
        (riemannZeta (z + τ * I))
      rw [norm_sub_rev] at hnorm
      linarith
    · exact Or.inl ⟨hτU, hτT⟩
  calc volume _ ≤ volume (((circlePhaseFlow primeFrequency ⁻¹' U)ᶜ ∩ Icc 0 T) ∪
        (eulerDiscTailBadSet y c r (b / 2) ∩ Icc 0 T)) := measure_mono hsub
    _ ≤ volume ((circlePhaseFlow primeFrequency ⁻¹' U)ᶜ ∩ Icc 0 T) +
        volume (eulerDiscTailBadSet y c r (b / 2) ∩ Icc 0 T) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η * T) + ENNReal.ofReal (η * T) := add_le_add hTflow hTtail
    _ ≤ ENNReal.ofReal (δ * T) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_right hηδ hT0]

end RHTower
