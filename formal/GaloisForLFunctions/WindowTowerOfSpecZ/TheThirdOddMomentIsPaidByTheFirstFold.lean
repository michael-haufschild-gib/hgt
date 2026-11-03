import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldHasAPolynomialSpectralBracket

/-!
# The first fold pays its third odd moment

The bounded polynomial comparison controls the third Legendre moment by an
inverse chord estimate. Its remaining positive mass leaves only the first
moment charge in the complete Weil form.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open SelectivePositivityAndThresholdLaws SpacingScaleHarmonicAnalysis

private def pairQ (a b w x y : ℝ) : ℝ := a * x ^ 2 + 2 * w * x * y + b * y ^ 2

-- The inverse chord is proved by completing a square in each reflection block.
private theorem pair_inverse_chord {a b w m M : ℝ} (hm : 0 < m)
    (hM : m ≤ M)
    (hlo : ∀ x y, m * (x ^ 2 + y ^ 2) ≤ pairQ a b w x y)
    (hup : ∀ x y, pairQ a b w x y ≤ M * (x ^ 2 + y ^ 2))
    (p q x y t : ℝ) :
    0 ≤ m * M * pairQ a b w x y + 2 * m * M * t * (p * x + q * y) +
      t ^ 2 * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q) := by
  have ha : m ≤ a := by simpa [pairQ] using hlo 1 0
  have hb : m ≤ b := by simpa [pairQ] using hlo 0 1
  have hAa : a ≤ M := by simpa [pairQ] using hup 1 0
  have hBb : b ≤ M := by simpa [pairQ] using hup 0 1
  have hdetL : w ^ 2 ≤ (a - m) * (b - m) := by
    apply HTGeometry.sq_le_mul_of_quadratic_nonneg (sub_nonneg.mpr hb)
    intro z
    have h := hlo 1 z
    simp only [pairQ, one_pow, mul_one] at h
    linarith only [h]
  have hdetU : w ^ 2 ≤ (M - a) * (M - b) := by
    have h : (-w) ^ 2 ≤ (M - a) * (M - b) := by
      apply HTGeometry.sq_le_mul_of_quadratic_nonneg (sub_nonneg.mpr hBb)
      intro z
      have h := hup 1 z
      simp only [pairQ, one_pow, mul_one] at h
      linarith only [h]
    simpa only [neg_sq] using h
  let δ := a * b - w ^ 2
  have hd : 0 < δ := by
    have hm2 := mul_pos hm hm
    have hma := mul_le_mul_of_nonneg_left ha hm.le
    have hmb := mul_le_mul_of_nonneg_left hb hm.le
    dsimp [δ]
    nlinarith only [hdetL, hm2, hma, hmb]
  have hn : 0 ≤ p ^ 2 + q ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hchord : m * M * (b * p ^ 2 - 2 * w * p * q + a * q ^ 2) ≤
      δ * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q) := by
    by_cases hδ : δ ≤ m * M
    · have h2 := mul_nonneg (mul_nonneg (hm.trans_le hM).le
        (sub_nonneg.mpr hdetL)) hn
      have he : δ * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q) -
          m * M * (b * p ^ 2 - 2 * w * p * q + a * q ^ 2) =
          (m * M - δ) * (pairQ a b w p q - m * (p ^ 2 + q ^ 2)) +
          M * ((a - m) * (b - m) - w ^ 2) * (p ^ 2 + q ^ 2) := by
        dsimp [δ, pairQ]; ring
      rw [← sub_nonneg] at ⊢
      rw [he]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr (hlo p q))) h2
    · have h2 := mul_nonneg (mul_nonneg hm.le (sub_nonneg.mpr hdetU)) hn
      have he : δ * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q) -
          m * M * (b * p ^ 2 - 2 * w * p * q + a * q ^ 2) =
          (δ - m * M) * (M * (p ^ 2 + q ^ 2) - pairQ a b w p q) +
          m * ((M - a) * (M - b) - w ^ 2) * (p ^ 2 + q ^ 2) := by
        dsimp [δ, pairQ]; ring
      rw [← sub_nonneg] at ⊢
      rw [he]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr (lt_of_not_ge hδ).le)
        (sub_nonneg.mpr (hup p q))) h2
  have hpos (v z : ℝ) : 0 ≤ pairQ a b w v z :=
    (mul_nonneg hm.le (add_nonneg (sq_nonneg _) (sq_nonneg _))).trans (hlo v z)
  have hs := hpos (δ * x + t * (b * p - w * q)) (δ * y + t * (a * q - w * p))
  have he : pairQ a b w (δ * x + t * (b * p - w * q)) (δ * y + t * (a * q - w * p)) =
      δ * (δ * pairQ a b w x y + 2 * δ * t * (p * x + q * y) +
        t ^ 2 * (b * p ^ 2 - 2 * w * p * q + a * q ^ 2)) := by
    dsimp [δ, pairQ]; ring
  rw [he] at hs
  have hraw := nonneg_of_mul_nonneg_right hs hd
  have hmul := mul_nonneg (mul_nonneg hm.le (hm.trans_le hM).le) hraw
  have hfinal : 0 ≤ δ * (m * M * pairQ a b w x y + 2 * m * M * t * (p * x + q * y) +
      t ^ 2 * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q)) := by
    have he : δ * (m * M * pairQ a b w x y + 2 * m * M * t * (p * x + q * y) +
        t ^ 2 * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q)) =
        m * M * (δ * pairQ a b w x y + 2 * δ * t * (p * x + q * y) +
          t ^ 2 * (b * p ^ 2 - 2 * w * p * q + a * q ^ 2)) +
        t ^ 2 * (δ * ((m + M) * (p ^ 2 + q ^ 2) - pairQ a b w p q) -
          m * M * (b * p ^ 2 - 2 * w * p * q + a * q ^ 2)) := by ring
    rw [he]
    exact add_nonneg hmul (mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hchord))
  exact nonneg_of_mul_nonneg_right hfinal hd

/-- Bounded polynomial comparison with the signed first-prime reflection. -/
def firstFoldPolynomialEnergy (G : ℝ → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * G u ^ 2) +
    (Real.log 2 / Real.sqrt 2) *
      ∫ u in (2 * Real.log 2 - 1)..1, G u * G (2 * Real.log 2 - u)

private def stripLeft : ℝ := 2 * Real.log 2 - 1

private def stripReflect (u : ℝ) : ℝ := 2 * Real.log 2 - u

private theorem stripLeft_bounds : 0 ≤ stripLeft ∧ stripLeft ≤ 1 := by
  unfold stripLeft
  constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]

@[fun_prop] private theorem continuous_potential : Continuous firstFoldPolynomialPotential :=
  continuous_const.add continuous_firstFoldLogPolynomial

@[fun_prop] private theorem continuous_reflect : Continuous stripReflect := continuous_const.sub continuous_id

private def blockIntegral (f g : ℝ → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..stripLeft, f u) + (∫ u in stripLeft..1, g u) / 2

private theorem blockIntegral_add {f g h k : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    blockIntegral (fun u => f u + h u) (fun u => g u + k u) =
      blockIntegral f g + blockIntegral h k := by
  unfold blockIntegral
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _),
    intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  ring

private theorem blockIntegral_const_mul (c : ℝ) (f g : ℝ → ℝ) :
    blockIntegral (fun u => c * f u) (fun u => c * g u) = c * blockIntegral f g := by
  unfold blockIntegral
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

private theorem blockIntegral_sub {f g h k : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    blockIntegral (fun u => f u - h u) (fun u => g u - k u) =
      blockIntegral f g - blockIntegral h k := by
  unfold blockIntegral
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  ring

private theorem blockIntegral_nonneg {f g : ℝ → ℝ}
    (hf : ∀ u ∈ Icc (0 : ℝ) stripLeft, 0 ≤ f u)
    (hg : ∀ u ∈ Icc stripLeft 1, 0 ≤ g u) : 0 ≤ blockIntegral f g := by
  unfold blockIntegral
  exact add_nonneg (intervalIntegral.integral_nonneg stripLeft_bounds.1 (fun u hu => hf u hu))
    (div_nonneg (intervalIntegral.integral_nonneg stripLeft_bounds.2 (fun u hu => hg u hu))
      (by norm_num))

private theorem reflection_integral (f : ℝ → ℝ) :
    (∫ u in stripLeft..1, f (stripReflect u)) = ∫ u in stripLeft..1, f u := by
  have h := intervalIntegral.integral_comp_sub_left f (2 * Real.log 2)
    (a := stripLeft) (b := 1)
  simpa only [stripLeft, stripReflect, sub_sub_cancel] using h

private theorem blockIntegral_diagonal {f : ℝ → ℝ} (hf : Continuous f) :
    blockIntegral f (fun u => f u + f (stripReflect u)) = ∫ u in (0 : ℝ)..1, f u := by
  unfold blockIntegral
  rw [intervalIntegral.integral_add (f := f) (g := fun u => f (stripReflect u))
    (hf.intervalIntegrable _ _)
    ((hf.comp continuous_reflect).intervalIntegrable _ _), reflection_integral]
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable 0 stripLeft)
    (hf.intervalIntegrable stripLeft 1)
  linarith only [h]

private def pairDensity (G : ℝ → ℝ) (u : ℝ) : ℝ :=
  pairQ (firstFoldPolynomialPotential u) (firstFoldPolynomialPotential (stripReflect u))
    (Real.log 2 / Real.sqrt 2) (G u) (G (stripReflect u))

@[fun_prop] private theorem continuous_pairDensity {G : ℝ → ℝ} (hG : Continuous G) :
    Continuous (pairDensity G) := by
  unfold pairDensity pairQ
  exact ((continuous_potential.mul (hG.pow 2)).add
    ((continuous_const.mul hG).mul (hG.comp continuous_reflect))).add
    ((continuous_potential.comp continuous_reflect).mul ((hG.comp continuous_reflect).pow 2))

private theorem blockIntegral_energy {G : ℝ → ℝ} (hG : Continuous G) :
    blockIntegral (fun u => firstFoldPolynomialPotential u * G u ^ 2) (pairDensity G) =
      firstFoldPolynomialEnergy G := by
  have hi (a b : ℝ) : IntervalIntegrable (fun u => firstFoldPolynomialPotential u * G u ^ 2)
      volume a b := (continuous_potential.mul (hG.pow 2)).intervalIntegrable a b
  have hir (a b : ℝ) : IntervalIntegrable
      (fun u => firstFoldPolynomialPotential (stripReflect u) * G (stripReflect u) ^ 2) volume a b :=
    ((continuous_potential.mul (hG.pow 2)).comp continuous_reflect).intervalIntegrable a b
  have hic (a b : ℝ) : IntervalIntegrable
      (fun u => 2 * (Real.log 2 / Real.sqrt 2) * G u * G (stripReflect u)) volume a b :=
    ((continuous_const.mul hG).mul (hG.comp continuous_reflect)).intervalIntegrable a b
  unfold blockIntegral pairDensity pairQ firstFoldPolynomialEnergy
  rw [intervalIntegral.integral_add ((hi _ _).add (hic _ _)) (hir _ _),
    intervalIntegral.integral_add (hi _ _) (hic _ _)]
  have hr := reflection_integral (fun u => firstFoldPolynomialPotential u * G u ^ 2)
  rw [hr]
  have hc : (∫ u in stripLeft..1, 2 * (Real.log 2 / Real.sqrt 2) * G u * G (stripReflect u)) =
      2 * (Real.log 2 / Real.sqrt 2) * ∫ u in stripLeft..1, G u * G (stripReflect u) := by
    rw [show (fun u => 2 * (Real.log 2 / Real.sqrt 2) * G u * G (stripReflect u)) =
      (fun u => (2 * (Real.log 2 / Real.sqrt 2)) * (G u * G (stripReflect u))) by funext u; ring,
      intervalIntegral.integral_const_mul]
  rw [hc]
  have ha := intervalIntegral.integral_add_adjacent_intervals (hi 0 stripLeft) (hi stripLeft 1)
  change _ = (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * G u ^ 2) +
    (Real.log 2 / Real.sqrt 2) * ∫ u in stripLeft..1, G u * G (stripReflect u)
  linarith only [ha]

private theorem polynomial_energy_lower {G : ℝ → ℝ} (hG : Continuous G) :
    (19 / 50 : ℝ) * (∫ u in (0 : ℝ)..1, G u ^ 2) ≤ firstFoldPolynomialEnergy G := by
  have h := blockIntegral_nonneg
    (f := fun u => firstFoldPolynomialPotential u * G u ^ 2 - (19 / 50 : ℝ) * G u ^ 2)
    (g := fun u => pairDensity G u - (19 / 50 : ℝ) * (G u ^ 2 + G (stripReflect u) ^ 2))
    (fun u hu => by
      have hv := firstFoldPolynomialPotential_bounds ⟨hu.1, hu.2.trans stripLeft_bounds.2⟩
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hv.1 (sq_nonneg _)))
    (fun u hu => sub_nonneg.mpr (firstFoldPolynomial_pair_bounds hu _ _).1)
  rw [blockIntegral_sub
    (f := fun u => firstFoldPolynomialPotential u * G u ^ 2) (g := pairDensity G)
    (h := fun u => (19 / 50 : ℝ) * G u ^ 2)
    (k := fun u => (19 / 50 : ℝ) * (G u ^ 2 + G (stripReflect u) ^ 2))
    (continuous_potential.mul (hG.pow 2))
    (continuous_pairDensity hG) (continuous_const.mul (hG.pow 2))
    (continuous_const.mul ((hG.pow 2).add ((hG.comp continuous_reflect).pow 2))),
    blockIntegral_energy hG, blockIntegral_const_mul,
    blockIntegral_diagonal (f := fun u => G u ^ 2) (hG.pow 2)] at h
  linarith only [h]

private theorem scalar_inverse_chord {a : ℝ}
    (ha : (19 / 50 : ℝ) ≤ a) (hA : a ≤ 37 / 20) (p x t : ℝ) :
    0 ≤ (19 / 50 : ℝ) * (37 / 20) * (a * x ^ 2) +
      (2 * (19 / 50 : ℝ) * (37 / 20) * t) * (p * x) +
      t ^ 2 * (((19 / 50 : ℝ) + 37 / 20) * p ^ 2 - a * p ^ 2) := by
  have hlo (v z : ℝ) : (19 / 50 : ℝ) * (v ^ 2 + z ^ 2) ≤ pairQ a a 0 v z := by
    have h := mul_nonneg (sub_nonneg.mpr ha) (add_nonneg (sq_nonneg v) (sq_nonneg z))
    dsimp [pairQ]
    nlinarith only [h]
  have hup (v z : ℝ) : pairQ a a 0 v z ≤ (37 / 20 : ℝ) * (v ^ 2 + z ^ 2) := by
    have h := mul_nonneg (sub_nonneg.mpr hA) (add_nonneg (sq_nonneg v) (sq_nonneg z))
    dsimp [pairQ]
    nlinarith only [h]
  have h := pair_inverse_chord (by norm_num : (0 : ℝ) < 19 / 50)
    (by norm_num : (19 / 50 : ℝ) ≤ 37 / 20) hlo hup p 0 x 0 t
  simpa [pairQ, mul_assoc] using h

private theorem polynomial_energy_young {G P : ℝ → ℝ}
    (hG : Continuous G) (hP : Continuous P) (t : ℝ) :
    0 ≤ (19 / 50 : ℝ) * (37 / 20) * firstFoldPolynomialEnergy G +
      (2 * (19 / 50 : ℝ) * (37 / 20) * t) * (∫ u in (0 : ℝ)..1, P u * G u) +
      t ^ 2 * (((19 / 50 : ℝ) + 37 / 20) * (∫ u in (0 : ℝ)..1, P u ^ 2) -
        firstFoldPolynomialEnergy P) := by
  have h := blockIntegral_nonneg
    (f := fun u => (19 / 50 : ℝ) * (37 / 20) * (firstFoldPolynomialPotential u * G u ^ 2) +
      (2 * (19 / 50 : ℝ) * (37 / 20) * t) * (P u * G u) +
      t ^ 2 * (((19 / 50 : ℝ) + 37 / 20) * P u ^ 2 - firstFoldPolynomialPotential u * P u ^ 2))
    (g := fun u => (19 / 50 : ℝ) * (37 / 20) * pairDensity G u +
      (2 * (19 / 50 : ℝ) * (37 / 20) * t) *
        (P u * G u + P (stripReflect u) * G (stripReflect u)) +
      t ^ 2 * (((19 / 50 : ℝ) + 37 / 20) * (P u ^ 2 + P (stripReflect u) ^ 2) - pairDensity P u))
    (fun u hu => by
      have hA := firstFoldPolynomialPotential_bounds ⟨hu.1, hu.2.trans stripLeft_bounds.2⟩
      exact scalar_inverse_chord hA.1 hA.2 _ _ t)
    (fun u hu => by
      exact pair_inverse_chord (by norm_num : (0 : ℝ) < 19 / 50)
        (by norm_num : (19 / 50 : ℝ) ≤ 37 / 20)
        (fun x y => (firstFoldPolynomial_pair_bounds hu x y).1)
        (fun x y => (firstFoldPolynomial_pair_bounds hu x y).2) _ _ _ _ t)
  simpa (disch := fun_prop) only [blockIntegral_add, blockIntegral_sub, blockIntegral_const_mul,
    blockIntegral_energy hG, blockIntegral_energy hP,
    blockIntegral_diagonal (f := fun u => P u * G u) (hP.mul hG),
    blockIntegral_diagonal (f := fun u => P u ^ 2) (hP.pow 2)] using h

private theorem third_poly (u : ℝ) : legP 3 u = (5 * u ^ 3 - 3 * u) / 2 := by
  norm_num [legP]
  ring

private theorem third_weighted_mass (n : ℕ) :
    (∫ u in (0 : ℝ)..1, u ^ n * legP 3 u ^ 2) =
      (25 / 4 : ℝ) / (n + 7) - (15 / 2 : ℝ) / (n + 5) + (9 / 4 : ℝ) / (n + 3) := by
  have he : (fun u : ℝ => u ^ n * legP 3 u ^ 2) =
      fun u => (25 / 4 : ℝ) * u ^ (n + 6) - (15 / 2 : ℝ) * u ^ (n + 4) +
        (9 / 4 : ℝ) * u ^ (n + 2) := by
    funext u
    rw [third_poly]
    simp only [pow_add]
    ring
  have hc (j : ℕ) (c : ℝ) : Continuous (fun u : ℝ => c * u ^ j) :=
    continuous_const.mul (continuous_id.pow _)
  rw [he, intervalIntegral.integral_add
    (f := fun u : ℝ => (25 / 4 : ℝ) * u ^ (n + 6) - (15 / 2 : ℝ) * u ^ (n + 4))
    (g := fun u : ℝ => (9 / 4 : ℝ) * u ^ (n + 2))
    (((hc (n + 6) (25 / 4)).sub (hc (n + 4) (15 / 2))).intervalIntegrable _ _)
    ((hc (n + 2) (9 / 4)).intervalIntegrable _ _),
    intervalIntegral.integral_sub
      (f := fun u : ℝ => (25 / 4 : ℝ) * u ^ (n + 6))
      (g := fun u : ℝ => (15 / 2 : ℝ) * u ^ (n + 4))
      ((hc (n + 6) (25 / 4)).intervalIntegrable _ _)
      ((hc (n + 4) (15 / 2)).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num [Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem third_mass : (∫ u in (0 : ℝ)..1, legP 3 u ^ 2) = (1 / 7 : ℝ) := by
  have h := third_weighted_mass 0
  norm_num at h
  exact h

private def thirdReflectionAnti (d u : ℝ) : ℝ :=
  (-15 * d ^ 3 + 9 * d) / 4 * u ^ 2 / 2 +
  (45 * d ^ 2 - 9) / 4 * u ^ 3 / 3 +
  (25 * d ^ 3 - 60 * d) / 4 * u ^ 4 / 4 +
  (30 - 75 * d ^ 2) / 4 * u ^ 5 / 5 +
  (75 * d) / 4 * u ^ 6 / 6 - (25 / 4 : ℝ) * u ^ 7 / 7

private theorem thirdReflection_deriv (d u : ℝ) :
    HasDerivAt (thirdReflectionAnti d) (legP 3 u * legP 3 (d - u)) u := by
  have h1 := ((hasDerivAt_pow 2 u).const_mul ((-15 * d ^ 3 + 9 * d) / 4)).div_const 2
  have h2 := ((hasDerivAt_pow 3 u).const_mul ((45 * d ^ 2 - 9) / 4)).div_const 3
  have h3 := ((hasDerivAt_pow 4 u).const_mul ((25 * d ^ 3 - 60 * d) / 4)).div_const 4
  have h4 := ((hasDerivAt_pow 5 u).const_mul ((30 - 75 * d ^ 2) / 4)).div_const 5
  have h5 := ((hasDerivAt_pow 6 u).const_mul ((75 * d) / 4)).div_const 6
  have h6 := ((hasDerivAt_pow 7 u).const_mul (25 / 4)).div_const 7
  exact (((((h1.add h2).add h3).add h4).add h5).sub h6).congr_deriv
    (by rw [third_poly, third_poly]; ring)

private def thirdReflectionPoly (s : ℝ) : ℝ :=
  s - 6 * s ^ 2 + 11 * s ^ 3 - 35 * s ^ 4 / 4 + 27 * s ^ 5 / 8 -
    5 * s ^ 6 / 8 + 5 * s ^ 7 / 112

private theorem third_reflection_identity (d : ℝ) :
    (∫ u in (d - 1)..1, legP 3 u * legP 3 (d - u)) = thirdReflectionPoly (2 - d) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => thirdReflection_deriv d u)
    (((continuous_legP 3).mul ((continuous_legP 3).comp
      (continuous_const.sub continuous_id))).intervalIntegrable _ _)]
  unfold thirdReflectionAnti thirdReflectionPoly
  ring

private theorem third_reflection_lower :
    -(83 / 1000 : ℝ) ≤ ∫ u in stripLeft..1, legP 3 u * legP 3 (stripReflect u) := by
  let s : ℝ := 2 - 2 * Real.log 2
  have hs : (613705638 / 1000000000 : ℝ) ≤ s ∧ s ≤ 613705640 / 1000000000 := by
    dsimp [s]
    constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hs0 : 0 ≤ s := by linarith only [hs.1]
  have hl (n : ℕ) := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 613705638 / 1000000000) hs.1 n
  have hu (n : ℕ) := pow_le_pow_left₀ hs0 hs.2 n
  have hbound : -(83 / 1000 : ℝ) ≤
      (613705638 / 1000000000 : ℝ) - 6 * (613705640 / 1000000000) ^ 2 +
        11 * (613705638 / 1000000000) ^ 3 - 35 * (613705640 / 1000000000) ^ 4 / 4 +
        27 * (613705638 / 1000000000) ^ 5 / 8 - 5 * (613705640 / 1000000000) ^ 6 / 8 +
        5 * (613705638 / 1000000000) ^ 7 / 112 := by norm_num
  change -(83 / 1000 : ℝ) ≤ ∫ u in (2 * Real.log 2 - 1)..1, legP 3 u * legP 3 (2 * Real.log 2 - u)
  rw [third_reflection_identity]
  change -(83 / 1000 : ℝ) ≤ thirdReflectionPoly s
  unfold thirdReflectionPoly
  linarith only [hbound, hs.1, hu 2, hl 3, hu 4, hl 5, hu 6, hl 7]

private theorem third_potential_lower :
    (11 / 140 : ℝ) + 23 / 630 + 13 / 924 + 7 / 858 + 19 / 3432 ≤
      ∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * legP 3 u ^ 2 := by
  have he : (fun u : ℝ => ((11 / 20 : ℝ) + firstFoldLogPolynomial u) * legP 3 u ^ 2) =
      fun u => (11 / 20 : ℝ) * legP 3 u ^ 2 + (1 / 2 : ℝ) * (u ^ 2 * legP 3 u ^ 2) +
        (1 / 4 : ℝ) * (u ^ 4 * legP 3 u ^ 2) + (1 / 6 : ℝ) * (u ^ 6 * legP 3 u ^ 2) +
        (1 / 8 : ℝ) * (u ^ 8 * legP 3 u ^ 2) := by
    funext u
    unfold firstFoldLogPolynomial
    ring
  have hval : (∫ u in (0 : ℝ)..1,
      ((11 / 20 : ℝ) + firstFoldLogPolynomial u) * legP 3 u ^ 2) =
      (11 / 140 : ℝ) + 23 / 630 + 13 / 924 + 7 / 858 + 19 / 3432 := by
    rw [he]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
      [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, third_mass,
        third_weighted_mass]
    norm_num
  rw [← hval]
  apply intervalIntegral.integral_mono_on
    (f := fun u => ((11 / 20 : ℝ) + firstFoldLogPolynomial u) * legP 3 u ^ 2)
    (g := fun u => firstFoldPolynomialPotential u * legP 3 u ^ 2) (by norm_num)
    (((continuous_const.add continuous_firstFoldLogPolynomial).mul
      ((continuous_legP 3).pow 2)).intervalIntegrable _ _)
    ((continuous_potential.mul ((continuous_legP 3).pow 2)).intervalIntegrable _ _)
  intro u _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  unfold firstFoldPolynomialPotential
  linarith only [firstFold_polynomial_mass_bounds.1]

private theorem third_energy_lower : (51 / 500 : ℝ) ≤ firstFoldPolynomialEnergy (legP 3) := by
  have hr := mul_le_mul_of_nonneg_left third_reflection_lower firstFold_prime_weight_bounds.1
  have hw := mul_le_mul_of_nonpos_right firstFold_prime_weight_bounds.2
    (by norm_num : -(83 / 1000 : ℝ) ≤ 0)
  have hc : (51 / 500 : ℝ) ≤
      11 / 140 + 23 / 630 + 13 / 924 + 7 / 858 + 19 / 3432 -
        (4902 / 10000) * (83 / 1000) := by norm_num
  unfold firstFoldPolynomialEnergy
  change (51 / 500 : ℝ) ≤ (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * legP 3 u ^ 2) +
    (Real.log 2 / Real.sqrt 2) * ∫ u in stripLeft..1, legP 3 u * legP 3 (stripReflect u)
  linarith only [third_potential_lower, hr, hw, hc]

private theorem prime_weight_lower : (49 / 100 : ℝ) ≤ Real.log 2 / Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≤ 14143 / 10000 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
  linarith only [hs, Real.log_two_gt_d9]

private theorem first_third_weighted_mass (n : ℕ) :
    (∫ u in (0 : ℝ)..1, u ^ n * (u * legP 3 u)) =
      (5 / 2 : ℝ) / (n + 5) - (3 / 2 : ℝ) / (n + 3) := by
  have he : (fun u : ℝ => u ^ n * (u * legP 3 u)) =
      fun u => (5 / 2 : ℝ) * u ^ (n + 4) - (3 / 2 : ℝ) * u ^ (n + 2) := by
    funext u
    rw [third_poly]
    simp only [pow_add]
    ring
  rw [he, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun u : ℝ => (5 / 2 : ℝ) * u ^ (n + 4))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u : ℝ => (3 / 2 : ℝ) * u ^ (n + 2))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num [Nat.cast_add, Nat.cast_ofNat]

private theorem first_third_mass : (∫ u in (0 : ℝ)..1, u * legP 3 u) = 0 := by
  have h := first_third_weighted_mass 0
  norm_num at h
  exact h

private theorem first_reflection_identity (d : ℝ) :
    (∫ u in (d - 1)..1, u * (d - u)) = (2 - d) - (2 - d) ^ 2 + (2 - d) ^ 3 / 6 := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => d * u ^ 2 / 2 - u ^ 3 / 3) (u * (d - u)) u := by
    exact (((hasDerivAt_pow 2 u).const_mul d).div_const 2 |>.sub
      ((hasDerivAt_pow 3 u).div_const 3)).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => u * (d - u))).intervalIntegrable _ _)]
  ring

private def mixedReflectionAnti (d u : ℝ) : ℝ :=
  (5 * d ^ 3 - 3 * d) * u ^ 2 / 4 + (1 - 5 * d ^ 2) * u ^ 3 / 2 +
    15 * d * u ^ 4 / 8 - u ^ 5 / 2

private def mixedReflectionPoly (s : ℝ) : ℝ :=
  s - 7 * s ^ 2 / 2 + 7 * s ^ 3 / 2 - 5 * s ^ 4 / 4 + s ^ 5 / 8

private theorem mixed_reflection_identity (d : ℝ) :
    (∫ u in (d - 1)..1, u * legP 3 (d - u)) = mixedReflectionPoly (2 - d) := by
  have hd (u : ℝ) : HasDerivAt (mixedReflectionAnti d) (u * legP 3 (d - u)) u := by
    have h1 := ((hasDerivAt_pow 2 u).const_mul (5 * d ^ 3 - 3 * d)).div_const 4
    have h2 := ((hasDerivAt_pow 3 u).const_mul (1 - 5 * d ^ 2)).div_const 2
    have h3 := ((hasDerivAt_pow 4 u).const_mul (15 * d)).div_const 8
    have h4 := (hasDerivAt_pow 5 u).div_const 2
    exact (((h1.add h2).add h3).sub h4).congr_deriv (by rw [third_poly]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_id.mul ((continuous_legP 3).comp
      (continuous_const.sub continuous_id))).intervalIntegrable _ _)]
  unfold mixedReflectionAnti mixedReflectionPoly
  ring

private theorem overlap_length_bounds :
    (613705638 / 1000000000 : ℝ) ≤ 2 - 2 * Real.log 2 ∧
      2 - 2 * Real.log 2 ≤ 613705640 / 1000000000 := by
  constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem first_reflection_lower :
    (27 / 100 : ℝ) ≤ ∫ u in stripLeft..1, u * stripReflect u := by
  let s := 2 - 2 * Real.log 2
  have hs := overlap_length_bounds
  change (613705638 / 1000000000 : ℝ) ≤ s ∧ s ≤ 613705640 / 1000000000 at hs
  have hs0 : 0 ≤ s := by linarith only [hs.1]
  have h2 := pow_le_pow_left₀ hs0 hs.2 2
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 613705638 / 1000000000) hs.1 3
  have hc : (27 / 100 : ℝ) ≤
      (613705638 / 1000000000 : ℝ) - (613705640 / 1000000000) ^ 2 +
        (613705638 / 1000000000) ^ 3 / 6 := by norm_num
  change (27 / 100 : ℝ) ≤ ∫ u in (2 * Real.log 2 - 1)..1, u * (2 * Real.log 2 - u)
  rw [first_reflection_identity]
  change (27 / 100 : ℝ) ≤ s - s ^ 2 + s ^ 3 / 6
  linarith only [hc, hs.1, h2, h3]

private theorem mixed_reflection_bounds :
    -(7 / 100 : ℝ) ≤ (∫ u in stripLeft..1, u * legP 3 (stripReflect u)) ∧
      (∫ u in stripLeft..1, u * legP 3 (stripReflect u)) ≤ -(3 / 50 : ℝ) := by
  let s := 2 - 2 * Real.log 2
  have hs := overlap_length_bounds
  change (613705638 / 1000000000 : ℝ) ≤ s ∧ s ≤ 613705640 / 1000000000 at hs
  have hs0 : 0 ≤ s := by linarith only [hs.1]
  have hl (n : ℕ) := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 613705638 / 1000000000) hs.1 n
  have hu (n : ℕ) := pow_le_pow_left₀ hs0 hs.2 n
  have hcl : -(7 / 100 : ℝ) ≤
      (613705638 / 1000000000 : ℝ) - 7 * (613705640 / 1000000000) ^ 2 / 2 +
        7 * (613705638 / 1000000000) ^ 3 / 2 - 5 * (613705640 / 1000000000) ^ 4 / 4 +
        (613705638 / 1000000000) ^ 5 / 8 := by norm_num
  have hcu : (613705640 / 1000000000 : ℝ) - 7 * (613705638 / 1000000000) ^ 2 / 2 +
      7 * (613705640 / 1000000000) ^ 3 / 2 - 5 * (613705638 / 1000000000) ^ 4 / 4 +
      (613705640 / 1000000000) ^ 5 / 8 ≤ -(3 / 50 : ℝ) := by norm_num
  change -(7 / 100 : ℝ) ≤ (∫ u in (2 * Real.log 2 - 1)..1, u * legP 3 (2 * Real.log 2 - u)) ∧ _
  rw [mixed_reflection_identity]
  change -(7 / 100 : ℝ) ≤ mixedReflectionPoly s ∧ mixedReflectionPoly s ≤ -(3 / 50 : ℝ)
  unfold mixedReflectionPoly
  constructor
  · linarith only [hcl, hs.1, hu 2, hl 3, hu 4, hl 5]
  · linarith only [hcu, hs.2, hl 2, hu 3, hl 4, hu 5]

private theorem first_potential_identity :
    (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * u ^ 2) =
      (137 / 60 - firstFoldMomentMassCost) / 3 + 1 / 10 + 1 / 28 + 1 / 54 + 1 / 88 := by
  have he : (fun u => firstFoldPolynomialPotential u * u ^ 2) = fun u : ℝ =>
      (137 / 60 - firstFoldMomentMassCost) * u ^ 2 + (1 / 2 : ℝ) * u ^ 4 +
        (1 / 4 : ℝ) * u ^ 6 + (1 / 6 : ℝ) * u ^ 8 + (1 / 8 : ℝ) * u ^ 10 := by
    funext u
    unfold firstFoldPolynomialPotential firstFoldLogPolynomial
    ring
  rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem first_energy_lower : (12 / 25 : ℝ) ≤ firstFoldPolynomialEnergy (fun u => u) := by
  have hr := mul_le_mul_of_nonneg_left first_reflection_lower firstFold_prime_weight_bounds.1
  have hw := mul_le_mul_of_nonneg_right prime_weight_lower (by norm_num : (0 : ℝ) ≤ 27 / 100)
  have hc : (12 / 25 : ℝ) ≤ 11 / 60 + 1 / 10 + 1 / 28 + 1 / 54 + 1 / 88 +
      (49 / 100) * (27 / 100) := by norm_num
  unfold firstFoldPolynomialEnergy
  rw [first_potential_identity]
  change (12 / 25 : ℝ) ≤ (137 / 60 - firstFoldMomentMassCost) / 3 +
    1 / 10 + 1 / 28 + 1 / 54 + 1 / 88 +
      (Real.log 2 / Real.sqrt 2) * ∫ u in stripLeft..1, u * stripReflect u
  linarith only [hc, hr, hw, firstFold_polynomial_mass_bounds.1]

private def firstThirdPairing : ℝ :=
  (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * (u * legP 3 u)) +
    (Real.log 2 / Real.sqrt 2) * ∫ u in stripLeft..1, u * legP 3 (stripReflect u)

private theorem mixed_potential_identity :
    (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * (u * legP 3 u)) =
      (1 / 35 + 1 / 63 + 1 / 99 + 1 / 143 : ℝ) := by
  have he : (fun u => firstFoldPolynomialPotential u * (u * legP 3 u)) = fun u =>
      (137 / 60 - firstFoldMomentMassCost) * (u * legP 3 u) +
        (1 / 2 : ℝ) * (u ^ 2 * (u * legP 3 u)) +
        (1 / 4 : ℝ) * (u ^ 4 * (u * legP 3 u)) +
        (1 / 6 : ℝ) * (u ^ 6 * (u * legP 3 u)) +
        (1 / 8 : ℝ) * (u ^ 8 * (u * legP 3 u)) := by
    funext u
    unfold firstFoldPolynomialPotential firstFoldLogPolynomial
    ring
  rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      first_third_mass, first_third_weighted_mass]
  norm_num

private theorem mixed_pairing_bounds : 0 ≤ firstThirdPairing ∧ firstThirdPairing ≤ 1 / 30 := by
  have hl := mul_le_mul_of_nonneg_left mixed_reflection_bounds.1 firstFold_prime_weight_bounds.1
  have hu := mul_le_mul_of_nonneg_left mixed_reflection_bounds.2 firstFold_prime_weight_bounds.1
  have hwl := mul_le_mul_of_nonpos_right firstFold_prime_weight_bounds.2
    (by norm_num : -(7 / 100 : ℝ) ≤ 0)
  have hwu := mul_le_mul_of_nonpos_right prime_weight_lower (by norm_num : -(3 / 50 : ℝ) ≤ 0)
  have hcl : (0 : ℝ) ≤ 1 / 35 + 1 / 63 + 1 / 99 + 1 / 143 -
      (4902 / 10000) * (7 / 100) := by norm_num
  have hcu : (1 / 35 + 1 / 63 + 1 / 99 + 1 / 143 : ℝ) -
      (49 / 100) * (3 / 50) ≤ 1 / 30 := by norm_num
  unfold firstThirdPairing
  rw [mixed_potential_identity]
  constructor <;> linarith only [hl, hu, hwl, hwu, hcl, hcu]

private theorem low_moment_mass (x y : ℝ) :
    (∫ u in (0 : ℝ)..1, (x * u + y * legP 3 u) ^ 2) = x ^ 2 / 3 + y ^ 2 / 7 := by
  have he : (fun u => (x * u + y * legP 3 u) ^ 2) = fun u =>
      x ^ 2 * u ^ 2 + (2 * x * y) * (u * legP 3 u) + y ^ 2 * legP 3 u ^ 2 := by
    funext u; ring
  rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      first_third_mass, third_mass, integral_pow]
  norm_num
  ring

private theorem low_moment_energy (x y : ℝ) :
    firstFoldPolynomialEnergy (fun u => x * u + y * legP 3 u) =
      x ^ 2 * firstFoldPolynomialEnergy (fun u => u) +
        2 * x * y * firstThirdPairing + y ^ 2 * firstFoldPolynomialEnergy (legP 3) := by
  have hr := reflection_integral (fun u => u * legP 3 (stripReflect u))
  have hri : (∫ u in stripLeft..1, stripReflect u * legP 3 u) =
      ∫ u in stripLeft..1, u * legP 3 (stripReflect u) := by
    simpa only [stripReflect, sub_sub_cancel] using hr
  have hp : (fun u => firstFoldPolynomialPotential u * (x * u + y * legP 3 u) ^ 2) =
      fun u => x ^ 2 * (firstFoldPolynomialPotential u * u ^ 2) +
        (2 * x * y) * (firstFoldPolynomialPotential u * (u * legP 3 u)) +
        y ^ 2 * (firstFoldPolynomialPotential u * legP 3 u ^ 2) := by funext u; ring
  have hq : (fun u => (x * u + y * legP 3 u) *
      (x * stripReflect u + y * legP 3 (stripReflect u))) = fun u =>
        x ^ 2 * (u * stripReflect u) + (x * y) * (u * legP 3 (stripReflect u)) +
        (x * y) * (stripReflect u * legP 3 u) +
        y ^ 2 * (legP 3 u * legP 3 (stripReflect u)) := by funext u; ring
  unfold firstFoldPolynomialEnergy firstThirdPairing
  change (∫ u in (0 : ℝ)..1, firstFoldPolynomialPotential u * (x * u + y * legP 3 u) ^ 2) +
    (Real.log 2 / Real.sqrt 2) * (∫ u in stripLeft..1,
      (x * u + y * legP 3 u) * (x * stripReflect u + y * legP 3 (stripReflect u))) = _
  rw [hp, hq]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
  rw [hri]
  dsimp only [stripLeft, stripReflect]
  ring

-- The mixed entry costs exactly the square `(6x+y)²/180` in the adverse sign.
private theorem low_moment_energy_lower (x y : ℝ) :
    (7 / 25 : ℝ) * x ^ 2 + (217 / 2250 : ℝ) * y ^ 2 ≤
      firstFoldPolynomialEnergy (fun u => x * u + y * legP 3 u) := by
  have h1 := mul_le_mul_of_nonneg_left first_energy_lower (sq_nonneg x)
  have h3 := mul_le_mul_of_nonneg_left third_energy_lower (sq_nonneg y)
  rw [low_moment_energy]
  by_cases hxy : 0 ≤ x * y
  · have hc := mul_nonneg hxy mixed_pairing_bounds.1
    nlinarith only [h1, h3, hc, sq_nonneg x, sq_nonneg y]
  · have hc := mul_le_mul_of_nonpos_left mixed_pairing_bounds.2 (le_of_not_ge hxy)
    nlinarith only [h1, h3, hc, sq_nonneg (6 * x + y)]

private theorem low_moment_chord_bound (x y : ℝ) :
    ((19 / 50 : ℝ) + 37 / 20) * (∫ u in (0 : ℝ)..1, (x * u + y * legP 3 u) ^ 2) -
      firstFoldPolynomialEnergy (fun u => x * u + y * legP 3 u) ≤
      (249 / 250 : ℝ) * (19 / 50) * (37 / 20) * ((2 / 3) * x ^ 2 + (20 / 63) * y ^ 2) := by
  rw [low_moment_mass]
  have h1 : ((19 / 50 : ℝ) + 37 / 20) / 3 - 7 / 25 ≤
      (249 / 250) * (19 / 50) * (37 / 20) * (2 / 3) := by norm_num
  have h3 : ((19 / 50 : ℝ) + 37 / 20) / 7 - 217 / 2250 ≤
      (249 / 250) * (19 / 50) * (37 / 20) * (20 / 63) := by norm_num
  have hx := mul_le_mul_of_nonneg_right h1 (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right h3 (sq_nonneg y)
  linarith only [low_moment_energy_lower x y, hx, hy]

/-- The inverse chord jointly pays the full third charge and `3/2` of the first charge. -/
theorem firstFoldPolynomialEnergy_sub_joint_moments {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ u in (0 : ℝ)..1, G u ^ 2) / 1000 ≤ firstFoldPolynomialEnergy G -
      (3 / 2 : ℝ) * (∫ u in (0 : ℝ)..1, u * G u) ^ 2 -
      (63 / 20 : ℝ) * (∫ u in (0 : ℝ)..1, G u * legP 3 u) ^ 2 := by
  let a := ∫ u in (0 : ℝ)..1, u * G u
  let b := ∫ u in (0 : ℝ)..1, legP 3 u * G u
  let P : ℝ → ℝ := fun u => (3 / 2 : ℝ) * a * u + (63 / 20 : ℝ) * b * legP 3 u
  have hP : Continuous P := (continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_legP 3))
  have hi : (∫ u in (0 : ℝ)..1, P u * G u) = (3 / 2 : ℝ) * a ^ 2 + (63 / 20 : ℝ) * b ^ 2 := by
    have he : (fun u => P u * G u) = fun u =>
        ((3 / 2 : ℝ) * a) * (u * G u) + ((63 / 20 : ℝ) * b) * (legP 3 u * G u) := by
      funext u; dsimp [P]; ring
    rw [he, intervalIntegral.integral_add
      ((continuous_const.mul (continuous_id.mul hG)).intervalIntegrable _ _)
      ((continuous_const.mul ((continuous_legP 3).mul hG)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    change (3 / 2 : ℝ) * a * a + (63 / 20 : ℝ) * b * b = _
    ring
  have hc := low_moment_chord_bound ((3 / 2 : ℝ) * a) ((63 / 20 : ℝ) * b)
  have hy := polynomial_energy_young hG hP (-1)
  rw [hi] at hy
  change ((19 / 50 : ℝ) + 37 / 20) * (∫ u in (0 : ℝ)..1, P u ^ 2) -
    firstFoldPolynomialEnergy P ≤ _ at hc
  have hj : (251 / 250 : ℝ) * ((3 / 2) * a ^ 2 + (63 / 20) * b ^ 2) ≤
      firstFoldPolynomialEnergy G := by nlinarith only [hy, hc]
  have hm := polynomial_energy_lower hG
  have hn : 0 ≤ ∫ u in (0 : ℝ)..1, G u ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => sq_nonneg _)
  have hb : (∫ u in (0 : ℝ)..1, G u * legP 3 u) = b := by
    dsimp [b]
    congr 1
    funext u
    exact mul_comm _ _
  rw [hb]
  change (∫ u in (0 : ℝ)..1, G u ^ 2) / 1000 ≤ firstFoldPolynomialEnergy G -
    (3 / 2 : ℝ) * a ^ 2 - (63 / 20 : ℝ) * b ^ 2
  linarith only [hj, hm, hn]

private theorem third_moment_bound {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ u in (0 : ℝ)..1, legP 3 u * G u) ^ 2 ≤ (1558 / 4921 : ℝ) * firstFoldPolynomialEnergy G := by
  have h := HTGeometry.sq_le_mul_of_quadratic_nonneg (by norm_num : (0 : ℝ) ≤ 1558 / 4921)
    (A := firstFoldPolynomialEnergy G) (B := ∫ u in (0 : ℝ)..1, legP 3 u * G u)
    (fun t => by
      have hy := polynomial_energy_young hG (continuous_legP 3) t
      rw [third_mass] at hy
      have hp := mul_le_mul_of_nonneg_left third_energy_lower (sq_nonneg t)
      nlinarith only [hy, hp])
  linarith only [h]

/-- The signed polynomial first fold pays the entire third Legendre charge with a uniform reserve. -/
theorem firstFoldPolynomialEnergy_sub_third_moment {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ u in (0 : ℝ)..1, G u ^ 2) / 1000 ≤ firstFoldPolynomialEnergy G -
      (63 / 20 : ℝ) * (∫ u in (0 : ℝ)..1, G u * legP 3 u) ^ 2 := by
  have hm := third_moment_bound hG
  have hmass := polynomial_energy_lower hG
  have hn : 0 ≤ ∫ u in (0 : ℝ)..1, G u ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => sq_nonneg _)
  simp only [mul_comm (legP 3 _) (G _)] at hm
  linarith only [hm, hmass, hn]

private theorem polynomialEnergy_le_twoMoment_add_charges {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    firstFoldPolynomialEnergy (fun u => F ((1 / 2) * u)) ≤
      firstFoldTwoMomentForm (fun u => F ((1 / 2) * u)) +
      (77 / 20 + 39 / 256 : ℝ) * (∫ u in Ioo (0 : ℝ) 1, u * F ((1 / 2) * u)) ^ 2 +
      (63 / 20 : ℝ) * (∫ u in Ioo (0 : ℝ) 1, F ((1 / 2) * u) * legP 3 u) ^ 2 := by
  let G : ℝ → ℝ := fun u => F ((1 / 2) * u)
  have hG : Continuous G := hF.continuous.comp (continuous_const.mul continuous_id)
  have hmass : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hG.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hExt := (LatticeSectionTheory.unit_odd_logarithmic_lag_and_exterior hF hs ho).1
  change IntegrableOn (fun u => G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2))
    (Ioo (0 : ℝ) 1) at hExt
  have hExact : IntegrableOn (fun u =>
      (137 / 60 - firstFoldMomentMassCost - Real.log (1 - u ^ 2) / 2) * G u ^ 2)
      (Ioo (0 : ℝ) 1) := by
    have he : (fun u => (137 / 60 - firstFoldMomentMassCost - Real.log (1 - u ^ 2) / 2) * G u ^ 2) =
        fun u => (137 / 60 - firstFoldMomentMassCost - Real.log 2) * G u ^ 2 +
          G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by funext u; ring
    rw [he]
    exact (hmass.const_mul (137 / 60 - firstFoldMomentMassCost - Real.log 2)).add hExt
  have hPoly : IntegrableOn (fun u => firstFoldPolynomialPotential u * G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (continuous_potential.mul (hG.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hle := integral_mono_ae hPoly hExact
    ((ae_restrict_mem measurableSet_Ioo).mono (fun u hu => by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (G u))
      unfold firstFoldPolynomialPotential
      linarith only [firstFoldLogPolynomial_le_log hu]))
  change firstFoldPolynomialEnergy G ≤ firstFoldTwoMomentForm G + _ + _
  unfold firstFoldPolynomialEnergy firstFoldTwoMomentForm
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (show 2 * Real.log 2 - 1 ≤ 1 from stripLeft_bounds.2),
    ← integral_Icc_eq_integral_Ioc]
  dsimp only [G] at hle ⊢
  linarith only [hle]

/-- The explicit two-moment lower form pays its third moment, leaving a single debit. -/
theorem firstFoldTwoMomentForm_add_first_moment_ge_mass {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) / 1000 ≤ firstFoldTwoMomentForm (fun u => F ((1 / 2) * u)) +
      (77 / 20 + 39 / 256 : ℝ) * (∫ u in Ioo (0 : ℝ) 1, u * F ((1 / 2) * u)) ^ 2 := by
  have hG : Continuous (fun u : ℝ => F ((1 / 2) * u)) :=
    hF.continuous.comp (continuous_const.mul continuous_id)
  have hp := firstFoldPolynomialEnergy_sub_third_moment hG
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hp
  rw [unit_odd_dilation_half_mass hF.continuous hs ho] at hp
  have hd := polynomialEnergy_le_twoMoment_add_charges hF hs ho
  linarith only [hp, hd]

/-- On the unit odd window, the complete Weil form needs only its first-moment charge. -/
theorem weilQuad_add_first_moment_ge_mass {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) / 1000 ≤ weilQuad F + (5123 / 320 : ℝ) * (∫ x, x * F x) ^ 2 := by
  have hd := firstFoldTwoMomentForm_add_first_moment_ge_mass hF hs ho
  have hq := weilQuad_ge_firstFoldTwoMomentForm hF hs ho
  have hpos := unit_odd_dilation_half_position hF.continuous hs ho
  rw [hpos]
  nlinarith only [hd, hq]

/-- Paying both low moments reduces the first-moment debit without losing the mass floor. -/
theorem firstFoldTwoMomentForm_add_reduced_first_moment_ge_mass {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) / 1000 ≤ firstFoldTwoMomentForm (fun u => F ((1 / 2) * u)) +
      (3203 / 1280 : ℝ) * (∫ u in Ioo (0 : ℝ) 1, u * F ((1 / 2) * u)) ^ 2 := by
  have hG : Continuous (fun u : ℝ => F ((1 / 2) * u)) :=
    hF.continuous.comp (continuous_const.mul continuous_id)
  have hp := firstFoldPolynomialEnergy_sub_joint_moments hG
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hp
  rw [unit_odd_dilation_half_mass hF.continuous hs ho] at hp
  have hd := polynomialEnergy_le_twoMoment_add_charges hF hs ho
  linarith only [hp, hd]

/-- The complete odd unit-window form retains only the reduced first-moment charge. -/
theorem weilQuad_add_reduced_first_moment_ge_mass {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) / 1000 ≤ weilQuad F + (3203 / 320 : ℝ) * (∫ x, x * F x) ^ 2 := by
  have hd := firstFoldTwoMomentForm_add_reduced_first_moment_ge_mass hF hs ho
  have hq := weilQuad_ge_firstFoldTwoMomentForm hF hs ho
  have hpos := unit_odd_dilation_half_position hF.continuous hs ho
  rw [hpos]
  nlinarith only [hd, hq]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldPolynomialEnergy_sub_third_moment
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldTwoMomentForm_add_first_moment_ge_mass
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_add_first_moment_ge_mass
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldPolynomialEnergy_sub_joint_moments
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldTwoMomentForm_add_reduced_first_moment_ge_mass
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_add_reduced_first_moment_ge_mass
