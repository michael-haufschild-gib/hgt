import GaloisForLFunctions.HTGeometry.EllipticGammaReciprocalNome
import GaloisForLFunctions.HTGeometry.GeometricFlatSequence

/-!
# The flat estimate on the disk

Combining the two degeneration bounds with the uniform control of the coordinate on the disk of
radius `1/4` about `i`, the multiple elliptic Gamma product differs from its parity-correct
zero-nome boundary by at most a constant times the nome, uniformly on that disk.

The arithmetic is isolated first, over abstract bounds: the coordinate lies in `[X, 1]`, the
boundary factor in `[W, 2]`, and the nome is small against `G`.  The analytic statement then only
has to supply those bounds.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A sequence that is geometrically small beyond a threshold is geometrically small. -/
theorem isGeometricallySmall_of_eventually {E : Type*} [NormedAddCommGroup E] {D : ℕ → E}
    {C r : ℝ} {M₀ : ℕ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ m, M₀ ≤ m → ‖D m‖ ≤ C * r ^ m) : IsGeometricallySmall D := by
  classical
  obtain ⟨r', hr'pos, hr'1, hrr'⟩ : ∃ r' : ℝ, 0 < r' ∧ r' < 1 ∧ r ≤ r' :=
    ⟨max r (1 / 2), lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      max_lt hr1 (by norm_num), le_max_left _ _⟩
  obtain ⟨T, hT0, hTle⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ m : ℕ, m < M₀ → ‖D m‖ / r' ^ m ≤ T := by
    refine ⟨∑ k ∈ Finset.range M₀, ‖D k‖ / r' ^ k,
      Finset.sum_nonneg fun k _ => by positivity, fun m hm => ?_⟩
    exact Finset.single_le_sum (f := fun k => ‖D k‖ / r' ^ k)
      (fun k _ => by positivity) (Finset.mem_range.mpr hm)
  refine ⟨C + T, r', by linarith, hr'pos.le, hr'1, fun m => ?_⟩
  have hpm : (0 : ℝ) < r' ^ m := by positivity
  by_cases hm : M₀ ≤ m
  · have hb := h m hm
    have hpow : r ^ m ≤ r' ^ m := pow_le_pow_left₀ hr0 hrr' m
    have hCr : C * r ^ m ≤ C * r' ^ m := mul_le_mul_of_nonneg_left hpow hC
    nlinarith
  · rw [not_le] at hm
    have hterm := hTle m hm
    rw [div_le_iff₀ hpm] at hterm
    nlinarith

section Arithmetic

variable {H G X W x w t : ℝ}

/-- The forward mass condition. -/
theorem flat_massF (_hH0 : 0 ≤ H) (hHG : H ≤ G) (hXpos : 0 < X) (hxX : X ≤ x)
    (ht0 : 0 ≤ t) (hGtX : G * t ≤ X) : H * (t / x) ≤ 1 := by
  have hxpos : 0 < x := lt_of_lt_of_le hXpos hxX
  rw [mul_div_assoc', div_le_one hxpos]
  have h1 : H * t ≤ G * t := mul_le_mul_of_nonneg_right hHG ht0
  linarith

/-- The inner backward mass, in terms of the abstract bounds. -/
theorem flat_inner_le (hH0 : 0 ≤ H) (hHG : H ≤ G) (hx1 : x ≤ 1) (hx0 : 0 ≤ x) (ht0 : 0 ≤ t) :
    (2 * H) * x * t ≤ 2 * (G * t) := by
  have hG0 : 0 ≤ G := le_trans hH0 hHG
  have hxt : 0 ≤ x * t := mul_nonneg hx0 ht0
  have hGt : 0 ≤ G * t := mul_nonneg hG0 ht0
  calc (2 * H) * x * t = 2 * (H * (x * t)) := by ring
    _ ≤ 2 * (G * (x * t)) := by nlinarith
    _ = 2 * ((G * t) * x) := by ring
    _ ≤ 2 * ((G * t) * 1) := by nlinarith
    _ = 2 * (G * t) := by ring

/-- The backward mass condition. -/
theorem flat_massB (hH0 : 0 ≤ H) (hHG : H ≤ G) (hx1 : x ≤ 1) (hx0 : 0 ≤ x)
    (ht0 : 0 ≤ t) (hGt8 : 8 * G * t ≤ 1) : (2 * H) * x * t ≤ 1 := by
  have h1 := flat_inner_le hH0 hHG hx1 hx0 ht0
  have h2 : 8 * G * t = 8 * (G * t) := by ring
  linarith

/-- The backward error stays below half the boundary factor. -/
theorem flat_bw (hH0 : 0 ≤ H) (hHG : H ≤ G) (hx1 : x ≤ 1) (hx0 : 0 ≤ x)
    (hw0 : 0 ≤ w) (ht0 : 0 ≤ t) (hGt8 : 8 * G * t ≤ 1) :
    w * (2 * ((2 * H) * x * t)) ≤ w / 2 := by
  have h1 := flat_inner_le hH0 hHG hx1 hx0 ht0
  have h2 : 8 * G * t = 8 * (G * t) := by ring
  have hinner : 2 * ((2 * H) * x * t) ≤ 1 / 2 := by linarith
  calc w * (2 * ((2 * H) * x * t)) ≤ w * (1 / 2) := mul_le_mul_of_nonneg_left hinner hw0
    _ = w / 2 := by ring

/-- The forward error, in terms of the abstract bounds. -/
theorem flat_aBound (hH0 : 0 ≤ H) (hHG : H ≤ G) (hXpos : 0 < X) (hxX : X ≤ x) (ht0 : 0 ≤ t) :
    2 * (H * (t / x)) ≤ 2 * G * t / X := by
  have hxpos : 0 < x := lt_of_lt_of_le hXpos hxX
  have hdiv : t / x ≤ t / X := div_le_div_of_nonneg_left ht0 hXpos hxX
  have hd0 : (0 : ℝ) ≤ t / x := by positivity
  have hstep : H * (t / x) ≤ G * (t / X) := by nlinarith
  have hEq : 2 * (G * (t / X)) = 2 * G * t / X := by ring
  linarith

/-- The backward error, in terms of the abstract bounds. -/
theorem flat_bBound (hH0 : 0 ≤ H) (hHG : H ≤ G) (hx1 : x ≤ 1) (hx0 : 0 ≤ x) (hw2 : w ≤ 2)
    (_hw0 : 0 ≤ w) (ht0 : 0 ≤ t) : w * (2 * ((2 * H) * x * t)) ≤ 8 * G * t := by
  have h1 := flat_inner_le hH0 hHG hx1 hx0 ht0
  have hH0' : (0 : ℝ) ≤ (2 * H) * x * t := by positivity
  have hinner : 2 * ((2 * H) * x * t) ≤ 4 * (G * t) := by linarith
  have hinner0 : (0 : ℝ) ≤ 2 * ((2 * H) * x * t) := by linarith
  calc w * (2 * ((2 * H) * x * t)) ≤ 2 * (2 * ((2 * H) * x * t)) := by nlinarith
    _ ≤ 2 * (4 * (G * t)) := by linarith
    _ = 8 * G * t := by ring

/-- **The arithmetic of the flat estimate.** -/
theorem flat_max_bound {a b : ℝ} (hG1 : 1 ≤ G) (hXpos : 0 < X) (hWpos : 0 < W)
    (hWw : W ≤ w) (hw2 : w ≤ 2) (ht0 : 0 ≤ t) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (haB : a ≤ 2 * G * t / X) (hbB : b ≤ 8 * G * t) (ha2 : a ≤ 2) :
    max ((1 + a) * b + w * a) ((w * a + b) * (2 / w ^ (2 : ℕ)))
      ≤ (24 * G + 4 * G / X + (4 * G / X + 8 * G) * (2 / W ^ (2 : ℕ))) * t := by
  have hG0 : (0 : ℝ) < G := by linarith
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le hWpos hWw
  have hXG : 2 * G * t / X = (2 * G / X) * t := by
    field_simp
  have hwa : w * a ≤ 2 * ((2 * G / X) * t) := by
    rw [hXG] at haB
    nlinarith
  have hfirst : (1 + a) * b + w * a ≤ (24 * G + 4 * G / X) * t := by
    have h1 : (1 + a) * b ≤ 3 * (8 * G * t) := by nlinarith
    have h2 : 2 * ((2 * G / X) * t) = (4 * G / X) * t := by ring
    linarith
  have hsecond : (w * a + b) * (2 / w ^ (2 : ℕ)) ≤ ((4 * G / X + 8 * G) * (2 / W ^ (2 : ℕ))) * t := by
    have hnum : w * a + b ≤ (4 * G / X + 8 * G) * t := by
      have h2 : 2 * ((2 * G / X) * t) = (4 * G / X) * t := by ring
      linarith
    have hden : 2 / w ^ (2 : ℕ) ≤ 2 / W ^ (2 : ℕ) := by
      have hsq : W ^ (2 : ℕ) ≤ w ^ (2 : ℕ) := by nlinarith
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    have hnn : (0 : ℝ) ≤ w * a + b := by positivity
    have hd0 : (0 : ℝ) ≤ 2 / W ^ (2 : ℕ) := by positivity
    calc (w * a + b) * (2 / w ^ (2 : ℕ)) ≤ (w * a + b) * (2 / W ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hden hnn
      _ ≤ ((4 * G / X + 8 * G) * t) * (2 / W ^ (2 : ℕ)) := mul_le_mul_of_nonneg_right hnum hd0
      _ = ((4 * G / X + 8 * G) * (2 / W ^ (2 : ℕ))) * t := by ring
  refine max_le ?_ ?_
  · refine le_trans hfirst ?_
    have hnn : (0 : ℝ) ≤ (4 * G / X + 8 * G) * (2 / W ^ (2 : ℕ)) := by positivity
    nlinarith
  · refine le_trans hsecond ?_
    have hnn : (0 : ℝ) ≤ 24 * G + 4 * G / X := by positivity
    nlinarith

end Arithmetic

/-- **The flat estimate.**  On the disk of radius `1/4` about `i` the multiple elliptic Gamma
product differs from its parity-correct zero-nome boundary by at most a constant times the nome. -/
theorem exists_flat_estimate (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ {τ : ι → ℂ} {t : ℝ}, (∀ i, 0 < (τ i).im) → 0 ≤ t → t ≤ ε →
      (∀ i, ‖ellipticNome (τ i)‖ ≤ t) → ∀ z ∈ flatDisk,
        ‖multipleEllipticGammaProduct τ z - zeroNomeBoundary ι z‖ ≤ C * t := by
  classical
  have hH0 : (0 : ℝ) ≤ multiIndexHalfSum ι := multiIndexHalfSum_nonneg
  obtain ⟨G, hG1, hGle⟩ : ∃ G : ℝ, 1 ≤ G ∧ multiIndexHalfSum ι ≤ G :=
    ⟨multiIndexHalfSum ι + 1, by linarith, by linarith⟩
  have hGpos : (0 : ℝ) < G := by linarith
  obtain ⟨X, hXpos, hXbd⟩ : ∃ X : ℝ, 0 < X ∧ ∀ z ∈ flatDisk,
      X ≤ ‖multipleEllipticGammaCoordinate z‖ ∧ ‖multipleEllipticGammaCoordinate z‖ ≤ 1 := by
    refine ⟨Real.exp (-(5 * Real.pi / 2)), Real.exp_pos _, fun z hz => ⟨?_, ?_⟩⟩
    · exact norm_coordinate_ge_of_mem hz
    · exact le_trans (norm_coordinate_le_of_mem hz) exp_neg_three_pi_half_lt_one.le
  obtain ⟨W, hWpos, hWbd⟩ : ∃ W : ℝ, 0 < W ∧ ∀ z ∈ flatDisk,
      W ≤ ‖1 - multipleEllipticGammaCoordinate z‖ := by
    refine ⟨1 - Real.exp (-(3 * Real.pi / 2)), ?_,
      fun z hz => norm_one_sub_coordinate_ge_of_mem hz⟩
    have := exp_neg_three_pi_half_lt_one
    linarith
  refine ⟨24 * G + 4 * G / X + (4 * G / X + 8 * G) * (2 / W ^ (2 : ℕ)),
    min (1 / 2) (min (1 / (8 * G)) (X / G)), by positivity, by positivity, ?_⟩
  intro τ t hτ ht0 htε hq z hz
  obtain ⟨hxlow, hxhigh⟩ := hXbd z hz
  have hwlow : W ≤ ‖1 - multipleEllipticGammaCoordinate z‖ := hWbd z hz
  have hwhigh : ‖1 - multipleEllipticGammaCoordinate z‖ ≤ 2 :=
    norm_one_sub_coordinate_le_of_mem hz
  have hxne : (1 : ℂ) - multipleEllipticGammaCoordinate z ≠ 0 :=
    one_sub_coordinate_ne_zero_of_mem hz
  have hthalf : t ≤ 1 / 2 := le_trans htε (min_le_left _ _)
  have ht8 : t ≤ 1 / (8 * G) := le_trans htε (le_trans (min_le_right _ _) (min_le_left _ _))
  have htX : t ≤ X / G := le_trans htε (le_trans (min_le_right _ _) (min_le_right _ _))
  have hGt8 : 8 * G * t ≤ 1 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * G)] at ht8
    linarith
  have hGtX : G * t ≤ X := by
    rw [le_div_iff₀ hGpos] at htX
    linarith
  have hmassF := flat_massF hH0 hGle hXpos hxlow ht0 hGtX
  have hmassB := flat_massB hH0 hGle hxhigh
    (norm_nonneg (multipleEllipticGammaCoordinate z)) ht0 hGt8
  have hF := norm_forwardProduct_sub_one_le hτ ht0 hthalf hq z hmassF
  have hB := norm_backwardProduct_sub_le hτ ht0 hthalf hq z hmassB
  have hbw := flat_bw hH0 hGle hxhigh (norm_nonneg (multipleEllipticGammaCoordinate z))
    (norm_nonneg (1 - multipleEllipticGammaCoordinate z)) ht0 hGt8
  have ha0 : (0 : ℝ) ≤ 2 * (multiIndexHalfSum ι * (t / ‖multipleEllipticGammaCoordinate z‖)) := by
    positivity
  have hb0 : (0 : ℝ) ≤ ‖1 - multipleEllipticGammaCoordinate z‖
      * (2 * ((2 * multiIndexHalfSum ι) * ‖multipleEllipticGammaCoordinate z‖ * t)) := by
    positivity
  have haB := flat_aBound hH0 hGle hXpos hxlow ht0
  have hbB := flat_bBound hH0 hGle hxhigh (norm_nonneg (multipleEllipticGammaCoordinate z))
    hwhigh (norm_nonneg (1 - multipleEllipticGammaCoordinate z)) ht0
  have ha2 : 2 * (multiIndexHalfSum ι * (t / ‖multipleEllipticGammaCoordinate z‖)) ≤ 2 := by
    have hq2 : 2 * G * t / X ≤ 2 := by
      rw [div_le_iff₀ hXpos]
      linarith
    linarith
  have hmain := norm_product_sub_zeroNomeBoundary_le hxne hF hB ha0 hb0 hbw
  exact le_trans hmain (flat_max_bound hG1 hXpos hWpos hwlow hwhigh ht0 ha0 hb0 haB hbB ha2)

/-- **The flat difference.**  Along the reciprocal family the multiple elliptic Gamma product
differs from its zero-nome boundary by an exponentially small amount, at every point of the disk. -/
theorem flat_difference_isGeometricallySmall {N : ℕ} {omega : ℂ}
    (homega : Transcendental ℚ omega) (himω : 0 < omega.im) (n : Fin N → ℤ) (hN : 0 < N)
    {z : ℂ} (hz : z ∈ flatDisk) :
    IsGeometricallySmall (fun m : ℕ =>
      multipleEllipticGammaProduct (inversePeriod omega n m) z - zeroNomeBoundary (Fin N) z) := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨r, hr0, hr1, hnome⟩ := exists_nome_bound homega himω n
  obtain ⟨C, ε, hC, hε, hest⟩ := exists_flat_estimate (Fin N)
  have hpow : ∀ᶠ m : ℕ in Filter.atTop, r ^ m < ε :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually_lt_const hε
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp hpow
  refine isGeometricallySmall_of_eventually (C := C) (r := r) (M₀ := max M₁ 1) hC hr0 hr1 ?_
  intro m hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hmM₁ : M₁ ≤ m := le_trans (le_max_left _ _) hm
  have hmpos : 0 < m := hm1
  have hτ : ∀ j, 0 < (inversePeriod omega n m j).im :=
    fun j => inversePeriod_im_pos homega himω n hmpos j
  have ht0 : (0 : ℝ) ≤ r ^ m := pow_nonneg hr0 m
  have htε : r ^ m ≤ ε := (hM₁ m hmM₁).le
  exact hest hτ ht0 htε (fun j => hnome m j) z hz

end

end GaloisForLFunctions.HTGeometry
