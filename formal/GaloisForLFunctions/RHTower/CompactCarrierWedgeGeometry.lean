import GaloisForLFunctions.RHTower.CompactCarrierSectorUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Wedge geometry for compact right-half-plane carriers

Every compact carrier with real part bounded below by a positive number and
imaginary part bounded in modulus fits a sufficiently narrow sector-root
pullback.  This file proves that geometry quantitatively and supplies the
sector exponent rather than postulating it.
-/

noncomputable section

namespace RHTower

open Complex Metric Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- A sufficiently high principal root of a right-half-plane point makes a
nonnegative real pairing with every point in a fixed right-half-plane
rectangle. -/
theorem sectorRoot_mul_re_nonnegative
    (w a : ℂ) (n : ℕ) (δ M : ℝ)
    (hn : 0 < n) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hangle : Real.pi / (2 * (n : ℝ)) ≤ 1 / 2)
    (hslope : M * (Real.pi / (2 * (n : ℝ))) ≤ δ / 2)
    (hw : 0 < w.re) (hare : δ ≤ a.re) (haim : |a.im| ≤ M) :
    0 ≤ (w ^ ((n : ℂ)⁻¹) * a).re := by
  have hwnz : w ≠ 0 := by intro h; subst w; simp at hw
  let b : ℝ := w.arg / (n : ℝ)
  let A : ℝ := Real.exp ((Complex.log w).re / (n : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have harglo : -(Real.pi / 2) < w.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hw)
  have harghi : w.arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hbabs : |b| ≤ Real.pi / (2 * (n : ℝ)) := by
    rw [abs_le]
    constructor
    · dsimp [b]
      rw [show -(Real.pi / (2 * (n : ℝ))) = (-Real.pi / 2) / (n : ℝ) by
        field_simp]
      apply (div_le_div_iff_of_pos_right hnR).2
      linarith
    · dsimp [b]
      rw [show Real.pi / (2 * (n : ℝ)) = (Real.pi / 2) / (n : ℝ) by
        field_simp]
      exact (div_le_div_iff_of_pos_right hnR).2 harghi.le
  have hbhalf : |b| ≤ 1 / 2 := hbabs.trans hangle
  have hsin : |Real.sin b| ≤ Real.pi / (2 * (n : ℝ)) :=
    Real.abs_sin_le_abs.trans hbabs
  have hcos : 1 / 2 ≤ Real.cos b := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := b)
    have hbsq : b ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      sq_le_sq.mpr (by simpa using hbhalf)
    nlinarith
  have hrootre : (w ^ ((n : ℂ)⁻¹)).re = A * Real.cos b := by
    have hrediv : (Complex.log w / (n : ℂ)).re =
        (Complex.log w).re / (n : ℝ) := by
      rw [Complex.div_re]
      norm_num
      field_simp
    have himdiv : (Complex.log w / (n : ℂ)).im = w.arg / (n : ℝ) := by
      rw [Complex.div_im, Complex.log_im]
      norm_num
      field_simp
    rw [Complex.cpow_def_of_ne_zero hwnz, show Complex.log w * (n : ℂ)⁻¹ =
      Complex.log w / (n : ℂ) by rw [div_eq_mul_inv], Complex.exp_re, hrediv, himdiv]
  have hrootim : (w ^ ((n : ℂ)⁻¹)).im = A * Real.sin b := by
    have hrediv : (Complex.log w / (n : ℂ)).re =
        (Complex.log w).re / (n : ℝ) := by
      rw [Complex.div_re]
      norm_num
      field_simp
    have himdiv : (Complex.log w / (n : ℂ)).im = w.arg / (n : ℝ) := by
      rw [Complex.div_im, Complex.log_im]
      norm_num
      field_simp
    rw [Complex.cpow_def_of_ne_zero hwnz, show Complex.log w * (n : ℂ)⁻¹ =
      Complex.log w / (n : ℂ) by rw [div_eq_mul_inv], Complex.exp_im, hrediv, himdiv]
  have hA : 0 < A := Real.exp_pos _
  rw [mul_re, hrootre, hrootim]
  have hbad : |Real.sin b * a.im| ≤ δ / 2 := by
    rw [abs_mul]
    calc
      |Real.sin b| * |a.im| ≤ (Real.pi / (2 * (n : ℝ))) * M := by gcongr
      _ = M * (Real.pi / (2 * (n : ℝ))) := by ring
      _ ≤ δ / 2 := hslope
  have hgood : δ / 2 ≤ Real.cos b * a.re := by
    nlinarith [mul_le_mul hcos hare (by linarith) (by linarith)]
  have hinside : 0 ≤ Real.cos b * a.re - Real.sin b * a.im := by
    have hle : Real.sin b * a.im ≤ δ / 2 :=
      le_trans (le_abs_self _) hbad
    linarith
  nlinarith

/-- There is always an integer root order narrow enough for a prescribed
right-half-plane rectangle. -/
theorem exists_sectorRoot_order (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∃ n : ℕ, 0 < n ∧
      Real.pi / (2 * (n : ℝ)) ≤ 1 / 2 ∧
      M * (Real.pi / (2 * (n : ℝ))) ≤ δ / 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max Real.pi (Real.pi * M / δ))
  have hnpi : Real.pi < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnM : Real.pi * M / δ < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnposR : (0 : ℝ) < n := Real.pi_pos.trans hnpi
  have hnpos : 0 < n := by exact_mod_cast hnposR
  refine ⟨n, hnpos, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
    nlinarith
  · rw [show M * (Real.pi / (2 * (n : ℝ))) =
        (M * Real.pi) / (2 * (n : ℝ)) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
    have hprod : Real.pi * M < δ * (n : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).mp hnM
    nlinarith

/-- Every compact carrier in a right-half-plane rectangle satisfies the
uniform translated-sector condition for some root order. -/
theorem exists_uniformSectorCarrierPositive
    (s : C(K, ℂ)) (δ M R₀ : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hR₀ : 0 < R₀)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M) :
    ∃ n : ℕ, n ≠ 0 ∧ UniformSectorCarrierPositive s n R₀ := by
  obtain ⟨n, hn, hangle, hslope⟩ := exists_sectorRoot_order δ M hδ hM
  refine ⟨n, hn.ne', ?_⟩
  intro R hR
  refine ⟨R * δ, mul_pos (hR₀.trans_le hR) hδ, fun z hz k => ?_⟩
  have hroot : 0 ≤
      (diskToRight z ^ ((n : ℂ)⁻¹) * s k).re :=
    sectorRoot_mul_re_nonnegative (diskToRight z) (s k) n δ M hn hδ hM
      hangle hslope (diskToRight_re_pos hz) (hre k) (him k)
  unfold sectorRootMap
  rw [add_mul, add_re]
  have hRpart : R * δ ≤ ((R : ℂ) * s k).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (hre k) (hR₀.le.trans hR)
  linarith

/-- Unconditional right-rectangle capstone: cofinite actual Euler-tangent
annihilation forces the compact Fourier--Borel transform to vanish.  The
sector order is constructed from the carrier bounds. -/
theorem compactFourierBorel_eq_zero_of_tangent_annihilation_rightRectangle
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    (δ M R₀ : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (hann : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      L (compactPrimeEulerUnitTangent s (p : ℕ)) = 0) :
    ∀ z : ℂ, compactFourierBorel L s z = 0 := by
  obtain ⟨n, hn, hsector⟩ :=
    exists_uniformSectorCarrierPositive s δ M R₀ hδ hM hR₀ hre him
  exact compactFourierBorel_eq_zero_of_tangent_annihilation
    L s hn hR₀.le hsector hann

end RHTower
