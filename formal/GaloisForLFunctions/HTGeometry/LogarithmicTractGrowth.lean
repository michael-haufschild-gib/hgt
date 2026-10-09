import GaloisForLFunctions.HTGeometry.OneFiberDiskGrowth
import GaloisForLFunctions.HTGeometry.IteratedExponentialGrowthHeight

/-!
# Positive lower order from an injective inverse logarithmic chart

The one-fiber disk estimate bounds the chart on a geometric sequence along the positive real ray.
Geometric spacing transfers the resulting exponential values to every sufficiently large disk.
This supplies positive lower order without a Koebe distortion theorem.
-/

open Complex Filter Metric Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- Geometrically spaced exponential values already force positive lower order on all disks. -/
theorem positiveLowerOrder_of_geometric_samples {F : ℂ → ℂ} {z : ℕ → ℂ}
    {A B q : ℝ} (hA : 0 < A) (hB : 1 < B) (hq : 1 < q)
    (hnorm : ∀ n, ‖z n‖ ≤ A * B ^ n)
    (hvalue : ∀ n, Real.exp (q ^ n) ≤ ‖F (z n)‖) : PositiveLowerOrder F := by
  obtain ⟨N, hBN⟩ := pow_unbounded_of_one_lt B hq
  have hNne : N ≠ 0 := by intro h; rw [h, pow_zero] at hBN; linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne
  let δ : ℝ := 1 / (2 * (N : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, eventually_atTop.2 ⟨max A ((A * B) ^ 2), ?_⟩⟩
  intro r hr
  have hAr : A ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := hA.trans_le hAr
  have hABr : (A * B) ^ 2 ≤ r := (le_max_right _ _).trans hr
  have hAB : 0 < A * B := mul_pos hA (by linarith)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near
    ((le_div_iff₀ hA).2 (by simpa using hAr)) hB
  have hz : ‖z n‖ ≤ r := (hnorm n).trans (by
    have h := (le_div_iff₀ hA).1 hnlo
    nlinarith)
  have hbn : B ^ n ≤ (q ^ n) ^ N := by
    calc
      B ^ n ≤ (q ^ N) ^ n := pow_le_pow_left₀ (by linarith) hBN.le n
      _ = (q ^ n) ^ N := by simp only [← pow_mul, Nat.mul_comm]
  have hQ : 0 < (q ^ n) ^ N := pow_pos (pow_pos (by linarith) n) N
  have hrupper : r < A * B * (q ^ n) ^ N := by
    calc
      r < B ^ (n + 1) * A := (div_lt_iff₀ hA).1 hnhi
      _ = A * B * (B ^ n) := by rw [pow_succ]; ring
      _ ≤ A * B * (q ^ n) ^ N := mul_le_mul_of_nonneg_left hbn hAB.le
  have hABQ : A * B < (q ^ n) ^ N := by nlinarith
  have hrpow : r < (q ^ n) ^ (2 * N) := by
    calc
      r < A * B * (q ^ n) ^ N := hrupper
      _ < (q ^ n) ^ N * (q ^ n) ^ N := mul_lt_mul_of_pos_right hABQ hQ
      _ = (q ^ n) ^ (2 * N) := by rw [← pow_add]; congr 1; omega
  have hcancel : ((q ^ n) ^ (2 * N)) ^ δ = q ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (pow_pos (by linarith : 0 < q) n).le]
    have hexp : ((2 * N : ℕ) : ℝ) * δ = 1 := by
      dsimp [δ]
      push_cast
      field_simp [ne_of_gt hNpos]
    rw [hexp, Real.rpow_one]
  refine ⟨z n, hz, ?_⟩
  simp only [iterExp_succ, iterExp_zero]
  apply (Real.exp_le_exp.2 ?_).trans (hvalue n)
  calc
    r ^ δ ≤ ((q ^ n) ^ (2 * N)) ^ δ := Real.rpow_le_rpow hr0.le hrpow.le hδ.le
    _ = q ^ n := hcancel

/-- Uniform geometric growth of a univalent half-plane chart around an omitted value. -/
theorem exists_univalent_halfPlane_geometric_bound :
    ∃ B : ℝ, 1 < B ∧ ∀ (φ : ℂ → ℂ) (a : ℂ),
      DifferentiableOn ℂ φ {z | 0 < z.re} → InjOn φ {z | 0 < z.re} →
      (∀ z : ℂ, 0 < z.re → φ z ≠ a) →
      ∀ n : ℕ, ‖φ (((3 / 2 : ℝ) ^ n : ℝ) : ℂ) - a‖ ≤ B ^ n * ‖φ 1 - a‖ := by
  obtain ⟨B, hB, hlocal⟩ := exists_one_fiber_omitted_value_disk_bound
  refine ⟨B, hB, ?_⟩
  intro φ a hφ hinj homit
  have hstep (x : ℝ) (hx : 0 < x) :
      ‖φ ((3 * x / 2 : ℝ) : ℂ) - a‖ ≤ B * ‖φ (x : ℂ) - a‖ := by
    have hsub : ball (x : ℂ) x ⊆ {z : ℂ | 0 < z.re} := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have h := Complex.re_le_norm ((x : ℂ) - z)
      rw [norm_sub_rev] at h
      simp only [Complex.sub_re, Complex.ofReal_re] at h
      change 0 < z.re
      linarith
    apply hlocal φ (x : ℂ) a x hx (hφ.mono hsub)
      (fun z hz heq => hinj (hsub hz) (by simpa using hx) heq)
      (fun z hz => homit z (hsub hz))
    have heq : ((3 * x / 2 : ℝ) : ℂ) - (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < x / 2)]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : 0 < (3 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
      have heq : (3 / 2 : ℝ) ^ (n + 1) = 3 * (3 / 2 : ℝ) ^ n / 2 := by
        rw [pow_succ]; ring
      rw [heq]
      calc
        ‖φ ((3 * (3 / 2 : ℝ) ^ n / 2 : ℝ) : ℂ) - a‖ ≤
          B * ‖φ (((3 / 2 : ℝ) ^ n : ℝ) : ℂ) - a‖ := hstep _ hx
        _ ≤ B * (B ^ n * ‖φ 1 - a‖) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = B ^ (n + 1) * ‖φ 1 - a‖ := by rw [pow_succ]; ring

/-- An injective inverse logarithmic chart with an omitted point forces positive lower order. -/
theorem positiveLowerOrder_of_univalent_logarithmic_chart {F φ : ℂ → ℂ} {a : ℂ}
    (hφ : DifferentiableOn ℂ φ {z | 0 < z.re}) (hinj : InjOn φ {z | 0 < z.re})
    (homit : ∀ z : ℂ, 0 < z.re → φ z ≠ a)
    (hvalue : ∀ x : ℝ, 0 < x → Real.exp x ≤ ‖F (φ (x : ℂ))‖) :
    PositiveLowerOrder F := by
  obtain ⟨B, hB, hgeo⟩ := exists_univalent_halfPlane_geometric_bound
  let A : ℝ := 1 + ‖a‖ + ‖φ 1 - a‖
  apply positiveLowerOrder_of_geometric_samples (z := fun n => φ (((3 / 2 : ℝ) ^ n : ℝ) : ℂ))
    (A := A) (B := B) (q := 3 / 2) (by dsimp [A]; positivity) hB (by norm_num)
  · intro n
    have h := hgeo φ a hφ hinj homit n
    have hn := one_le_pow₀ hB.le (n := n)
    have htri := norm_add_le (φ (((3 / 2 : ℝ) ^ n : ℝ) : ℂ) - a) a
    rw [sub_add_cancel] at htri
    have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1 + ‖a‖ by positivity)
    dsimp [A]
    nlinarith [hmul]
  · intro n
    exact hvalue _ (pow_pos (by norm_num) n)

end GaloisForLFunctions.HTGeometry
