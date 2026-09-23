import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs
import GaloisForLFunctions.RHTower.DirichletLLineLowerBound
import GaloisForLFunctions.RHTower.DirichletZeroAbscissa
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# Polynomial lower bound for the L-function right of the zero abscissa

Borel–Carathéodory on the disc centred at `σ₀ + it`, with radii chosen so that the outer disc stays
inside the zero-free half-plane `Re s > Θ_χ`, converts the polynomial *upper* bound of the
Phragmén–Lindelöf stage into a polynomial *lower* bound.

The centre is fixed at `Re = σ₀` where the modulus is at least `1/2` uniformly, the outer radius
is `σ₀ - (Θ_χ + ε/2)` and the inner radius `σ₀ - (Θ_χ + ε)`, so `R - r = ε/2` and the exponent of
the resulting bound is proportional to `1/ε`.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Polynomial lower bound right of the zero abscissa.** -/
theorem exists_lower_bound_right_of_abscissa {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ σ₀ K A : ℝ, 2 ≤ σ₀ ∧ 0 < K ∧ 0 ≤ A ∧
      ∀ s : ℂ, zeroAbscissa χ + ε ≤ s.re → s.re ≤ σ₀ →
        K * Real.exp (-(A * Real.log (2 + |s.im|))) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  obtain ⟨σ₀, hσ₀2, hline⟩ := exists_line_lower_bound χ
  obtain ⟨C₁, hC₁, hright⟩ := exists_bound_LFunction_of_two_le_re χ
  obtain ⟨C₂, hC₂, hstrip⟩ := bound_LFunction_strip hχ hprim
  have hΘ1' : zeroAbscissa χ ≤ 1 := zeroAbscissa_le_one hχ hprim
  have hΘhalf' : (1 : ℝ) / 2 ≤ zeroAbscissa χ := half_le_zeroAbscissa hχ hprim
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ, zeroAbscissa χ = Θ := ⟨_, rfl⟩
  rw [hΘ] at hΘ1' hΘhalf'
  have hΘ1 : Θ ≤ 1 := hΘ1'
  have hΘhalf : (1 : ℝ) / 2 ≤ Θ := hΘhalf'
  rw [hΘ]
  set r : ℝ := σ₀ - (Θ + ε) with hr
  set R : ℝ := σ₀ - (Θ + ε / 2) with hR
  have hR0 : (0 : ℝ) < R := by rw [hR]; linarith
  have hr0 : (0 : ℝ) ≤ r := by rw [hr]; linarith
  have hrR : r < R := by rw [hr, hR]; linarith
  have hRr : R - r = ε / 2 := by rw [hr, hR]; ring
  set D : ℝ := R + |σ₀ - 4| with hD
  have hD0 : (0 : ℝ) ≤ D := by rw [hD]; positivity
  set E : ℝ := C₁ + C₂ * (D + 1) ^ (3 : ℕ) with hE
  have hE0 : (0 : ℝ) < E := by rw [hE]; positivity
  clear_value E D R r
  refine ⟨σ₀, (1 / 2) * Real.exp (-(4 * r / ε) * (Real.log (2 * E) + 1)), 12 * r / ε,
    hσ₀2, by positivity, by positivity, fun s hs1 hs2 => ?_⟩
  set t : ℝ := s.im with ht
  set c : ℂ := (σ₀ : ℂ) + (t : ℂ) * Complex.I with hc
  have hcre : c.re = σ₀ := by rw [hc]; simp
  have hcim : c.im = t := by rw [hc]; simp
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hbase : (1 : ℝ) ≤ 2 + |t| := by linarith
  have hbase3 : (1 : ℝ) ≤ (2 + |t|) ^ (3 : ℕ) := one_le_pow₀ hbase
  clear_value c t
  -- geometry of the disc
  have hballre : ∀ z ∈ Metric.ball c R, Θ + ε / 2 < z.re := by
    intro z hz
    have hd : ‖z - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre] at hre
    have : |z.re - σ₀| < R := lt_of_le_of_lt hre hd
    have h2 := abs_lt.mp this
    rw [hR] at h2
    linarith [h2.1]
  have hne : ∀ z ∈ Metric.ball c R, DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz
    refine LFunction_ne_zero_of_zeroAbscissa_lt hχ ?_
    have hb := hballre z hz
    rw [hΘ]
    linarith
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball c R) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  -- upper bound on the disc
  have hM : ∀ z ∈ Metric.ball c R, ‖DirichletCharacter.LFunction χ z‖ ≤ E * (2 + |t|) ^ (3 : ℕ) := by
    intro z hz
    have hd : ‖z - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    rcases le_or_gt 2 z.re with hge | hlt
    · calc ‖DirichletCharacter.LFunction χ z‖ ≤ C₁ := hright z hge
        _ ≤ E * (2 + |t|) ^ (3 : ℕ) := by
            have hCE : C₁ ≤ E := by
              rw [hE]
              nlinarith [hC₂.le, pow_nonneg (by linarith : (0 : ℝ) ≤ D + 1) 3]
            nlinarith [hC₁.le, hbase3, hCE]
    · have hlow : (-2 : ℝ) ≤ z.re := by
        have := hballre z hz
        linarith
      have hupp : z.re ≤ 3 := by linarith
      have hz4 : ‖z - 4‖ ≤ D + |t| := by
        have h1 : ‖z - 4‖ ≤ ‖z - c‖ + ‖c - 4‖ := by
          have : z - 4 = (z - c) + (c - 4) := by ring
          rw [this]
          exact norm_add_le _ _
        have h2 : ‖c - 4‖ ≤ |σ₀ - 4| + |t| := by
          refine (Complex.norm_le_abs_re_add_abs_im (c - 4)).trans ?_
          rw [Complex.sub_re, Complex.sub_im, hcre, hcim]
          simp
        rw [hD]
        linarith
      have hz4' : ‖z - 4‖ ≤ (D + 1) * (2 + |t|) := by nlinarith [hD0, ht0]
      calc ‖DirichletCharacter.LFunction χ z‖ ≤ C₂ * ‖z - 4‖ ^ (3 : ℕ) := hstrip z hlow hupp
        _ ≤ C₂ * ((D + 1) * (2 + |t|)) ^ (3 : ℕ) := by
            refine mul_le_mul_of_nonneg_left ?_ hC₂.le
            exact pow_le_pow_left₀ (norm_nonneg _) hz4' 3
        _ = C₂ * (D + 1) ^ (3 : ℕ) * (2 + |t|) ^ (3 : ℕ) := by ring
        _ ≤ E * (2 + |t|) ^ (3 : ℕ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hE]
            nlinarith [hC₁.le, hC₂.le, pow_nonneg (by linarith : (0 : ℝ) ≤ D + 1) 3]
  have hm : (1 : ℝ) / 2 ≤ ‖DirichletCharacter.LFunction χ c‖ := hline c (le_of_eq hcre.symm)
  -- the target point sits in the inner disc
  have hsc : s - c = (((s.re - σ₀ : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [hc, ht]
  have hzc : ‖s - c‖ ≤ r := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    rw [hr]
    linarith
  have hBC := norm_lower_bound_of_ball hr0 hrR hdiff hne hM (by norm_num : (0:ℝ) < 1/2) hm hzc
  -- rewrite the constant
  have hMm : E * (2 + |t|) ^ (3 : ℕ) / (1 / 2) = 2 * E * (2 + |t|) ^ (3 : ℕ) := by ring
  rw [hMm, hRr] at hBC
  have hlogsplit : Real.log (2 * E * (2 + |t|) ^ (3 : ℕ))
      = Real.log (2 * E) + 3 * Real.log (2 + |t|) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlogsplit] at hBC
  refine le_trans (le_of_eq ?_) hBC
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  field_simp
  ring

end RHTower
