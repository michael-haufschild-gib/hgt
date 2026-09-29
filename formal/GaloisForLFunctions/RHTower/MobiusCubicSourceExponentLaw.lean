import GaloisForLFunctions.RHTower.MobiusCubicSourceCriticalFloor
import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw

/-!
# The exponent law of the cubic Möbius source

Route L's cubic source `S_N(t) = Σ_{n ≤ N} μ(n) n² e^{-nt}` has, at level `0 ≤ δ < 1`, a norm
`‖S_N‖_δ` bounded uniformly in `N` exactly when every zero of `ζ` has real part below `(1+δ)/2`
(`bddAbove_range_gammaEnergy_mobiusCubicSource_iff`, off the boundary `1 + δ = 2Θ`).

Divergence below the threshold is `tendsto_gammaEnergy_mobiusCubicSource_atTop_of_riemannZeta_eq_zero`.
Boundedness above it: a Mertens bound `|M(n)| ≤ C₁(n+1)^b` gives, through the Abel form
`S_N = M(N) f_N + Σ_{n<N} M(n) (f_n - f_{n+1})` and the derivative of `u ↦ u² e^{-ut}`,
the uniform pointwise bound `|S_N(t)| ≤ K t^{-b-2}` on `(0, 1]`
(`exists_abs_mobiusCubicSource_le_of_mertens`); then `t^{4+δ} S_N(t)² ≪ t^{δ-2b}` is integrable
at `0` when `2b < 1 + δ` (`exists_forall_gammaEnergy_mobiusCubicSource_le_of_mertens`).
-/

open MeasureTheory Set Filter Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-- `y^a e^{-yt} ≤ (a/t)^a e^{-a}` for `a, y ≥ 0`, `t > 0`. -/
theorem rpow_mul_exp_neg_mul_le {a y t : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (ht : 0 < t) :
    y ^ a * Real.exp (-(y * t)) ≤ (a / t) ^ a * Real.exp (-a) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [Real.rpow_zero, one_mul, neg_zero, Real.exp_zero]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  rcases eq_or_lt_of_le hy with rfl | hy'
  · rw [Real.zero_rpow ha'.ne', zero_mul]; positivity
  have hw : 0 < y * t / a := by positivity
  have hlog := Real.log_le_sub_one_of_pos hw
  rw [Real.rpow_def_of_pos hy', Real.rpow_def_of_pos (by positivity), ← Real.exp_add,
    ← Real.exp_add, Real.exp_le_exp]
  have hsplit : Real.log (y * t / a) = Real.log y - Real.log (a / t) := by
    rw [show y * t / a = y / (a / t) by field_simp, Real.log_div hy'.ne' (by positivity)]
  rw [hsplit] at hlog
  have : a * (Real.log y - Real.log (a / t)) ≤ a * (y * t / a - 1) :=
    mul_le_mul_of_nonneg_left hlog ha
  have h2 : a * (y * t / a - 1) = y * t - a := by field_simp
  nlinarith

/-- `1 - e^{-x} ≥ x/2` for `0 ≤ x ≤ 1`. -/
theorem half_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have hpos : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have : (Real.exp x)⁻¹ ≤ (x + 1)⁻¹ := inv_anti₀ (by linarith) h
  have hx1' : (x + 1)⁻¹ * (x + 1) = 1 := inv_mul_cancel₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0:ℝ) ≤ x + 1)]

/-- **A discrete Gamma bound.**  For `c ≥ 0` and `0 < t ≤ 1`,
`Σ_{n < M} (n+1)^c e^{-(n+1)t} ≤ (2c/t)^c e^{-c} · 4/t`. -/
theorem sum_rpow_mul_exp_neg_le {c t : ℝ} (hc : 0 ≤ c) (ht0 : 0 < t) (ht1 : t ≤ 1) (M : ℕ) :
    ∑ n ∈ range M, ((n : ℝ) + 1) ^ c * Real.exp (-(((n : ℝ) + 1) * t)) ≤
      (2 * c / t) ^ c * Real.exp (-c) * (4 / t) := by
  set q : ℝ := Real.exp (-(t / 2)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1q : t / 4 ≤ 1 - q := by
    have := half_le_one_sub_exp_neg (x := t / 2) (by linarith) (by linarith)
    rw [hq]; linarith
  have hA : 0 ≤ (2 * c / t) ^ c * Real.exp (-c) := by positivity
  have hterm : ∀ n ∈ range M, ((n : ℝ) + 1) ^ c * Real.exp (-(((n : ℝ) + 1) * t)) ≤
      (2 * c / t) ^ c * Real.exp (-c) * q ^ n := by
    intro n _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hsup := rpow_mul_exp_neg_mul_le hc hn0 (t := t / 2) (by linarith)
    rw [show c / (t / 2) = 2 * c / t by field_simp] at hsup
    have hsplit : Real.exp (-(((n : ℝ) + 1) * t)) =
        Real.exp (-(((n : ℝ) + 1) * (t / 2))) * Real.exp (-(((n : ℝ) + 1) * (t / 2))) := by
      rw [← Real.exp_add]; ring_nf
    have hqn : Real.exp (-(((n : ℝ) + 1) * (t / 2))) ≤ q ^ n := by
      rw [hq, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul hsup hqn (Real.exp_pos _).le hA
  calc ∑ n ∈ range M, ((n : ℝ) + 1) ^ c * Real.exp (-(((n : ℝ) + 1) * t))
      ≤ ∑ n ∈ range M, (2 * c / t) ^ c * Real.exp (-c) * q ^ n := Finset.sum_le_sum hterm
    _ = (2 * c / t) ^ c * Real.exp (-c) * ∑ n ∈ range M, q ^ n := by rw [Finset.mul_sum]
    _ ≤ (2 * c / t) ^ c * Real.exp (-c) * (1 - q)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hA
        rw [geom_sum_eq hq1.ne]
        rw [div_eq_mul_inv, show (q ^ M - 1) = -(1 - q ^ M) by ring, show (q - 1) = -(1 - q) by ring,
          neg_mul, inv_neg, mul_neg, neg_neg]
        have hqM : 0 ≤ q ^ M := pow_nonneg hq0 M
        have hinv : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (by linarith)
        nlinarith
    _ ≤ (2 * c / t) ^ c * Real.exp (-c) * (4 / t) := by
        apply mul_le_mul_of_nonneg_left _ hA
        rw [show 4 / t = (t / 4)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) h1q

/-- `|u² e^{-ut}|' ≤ e^{-ut}(2u + t u²)` for `u, t ≥ 0`. -/
theorem abs_atomJet_one_le {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    |atomJet 1 u t| ≤ Real.exp (-(u * t)) * (2 * u + t * u ^ 2) := by
  unfold atomJet
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  norm_num
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg ht (sq_nonneg u)]

/-- The unit Abel dipole is bounded by the derivative at the left endpoint. -/
theorem abs_abelDipole_le {n t : ℝ} (hn : 0 ≤ n) (ht : 0 ≤ t) :
    |abelDipole n t| ≤ Real.exp (-(n * t)) * (2 * (n + 1) + t * (n + 1) ^ 2) := by
  rw [abelDipole_eq_neg_integral, abs_neg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := n) (b := n + 1) (f := fun u => atomJet 1 u t)
    (C := Real.exp (-(n * t)) * (2 * (n + 1) + t * (n + 1) ^ 2)) ?_
  · rw [show |n + 1 - n| = 1 by norm_num, mul_one, Real.norm_eq_abs] at h
    exact h
  intro u hu
  rw [uIoc_of_le (by linarith)] at hu
  rw [Real.norm_eq_abs]
  refine (abs_atomJet_one_le (by linarith [hu.1]) ht).trans ?_
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hsq : u ^ 2 ≤ (n + 1) ^ 2 := pow_le_pow_left₀ hu0 hu.2 2
  apply mul_le_mul _ _ (by nlinarith [mul_nonneg ht (sq_nonneg u)]) (Real.exp_pos _).le
  · exact Real.exp_le_exp.mpr (by nlinarith [hu.1])
  · nlinarith [mul_le_mul_of_nonneg_left hsq ht, hu.2]

/-- The Mertens prefix is the complex Mertens sum. -/
theorem abs_abelMertens_eq (n : ℕ) : |abelMertens n| = ‖mobiusMertensPartialSum n‖ := by
  rw [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal, shiftedMertensReal_eq]
  rfl

/-- **Uniform pointwise bound.**  If `|M(n)| ≤ C₁(n+1)^b`, then `|S_N(t)| ≤ K t^{-b-2}` for all
`N` and `0 < t ≤ 1`. -/
theorem exists_abs_mobiusCubicSource_le_of_mertens {b C₁ : ℝ} (hb : 0 ≤ b) (hC₁ : 0 ≤ C₁)
    (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤ C₁ * ((n : ℝ) + 1) ^ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ N : ℕ,
      |mobiusCubicSource N t| ≤ K * t ^ (-b - 2) := by
  set A₁ : ℝ := (2 * (b + 1)) ^ (b + 1) * Real.exp (-(b + 1)) with hA₁
  set A₂ : ℝ := (2 * (b + 2)) ^ (b + 2) * Real.exp (-(b + 2)) with hA₂
  set A₀ : ℝ := (b + 2) ^ (b + 2) * Real.exp (-(b + 2)) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨C₁ * (2 ^ b * A₀ + Real.exp 1 * (8 * A₁ + 4 * A₂)), by positivity,
    fun t ht0 ht1 N => ?_⟩
  have htp : ∀ c : ℝ, t ^ (-c) = (1 / t) ^ c := fun c => by
    rw [Real.rpow_neg ht0.le, one_div, Real.inv_rpow ht0.le]
  have hMa : ∀ n : ℕ, |abelMertens n| ≤ C₁ * ((n : ℝ) + 1) ^ b := fun n => by
    rw [abs_abelMertens_eq]; exact hM n
  -- the dipole sum
  have hdip : ∀ K : ℕ, |∑ n ∈ Finset.Icc 1 K, abelMertens n * abelDipole n t| ≤
      C₁ * Real.exp 1 * (8 * A₁ + 4 * A₂) * t ^ (-b - 2) := by
    intro K
    have hterm : ∀ n ∈ Finset.Icc 1 K, |abelMertens n * abelDipole n t| ≤
        C₁ * Real.exp 1 * (2 * (((n : ℝ) + 1) ^ (b + 1) * Real.exp (-(((n : ℝ) + 1) * t))) +
          t * (((n : ℝ) + 1) ^ (b + 2) * Real.exp (-(((n : ℝ) + 1) * t)))) := by
      intro n _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [abs_mul]
      have hd := abs_abelDipole_le hn0 ht0.le
      have hexp : Real.exp (-((n : ℝ) * t)) = Real.exp 1 * Real.exp (-(((n : ℝ) + 1) * t)) *
          Real.exp (t - 1) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have hexp1 : Real.exp (t - 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hpow1 : ((n : ℝ) + 1) ^ b * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (b + 1) := by
        rw [Real.rpow_add hn1, Real.rpow_one]
      have hpow2 : ((n : ℝ) + 1) ^ b * ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ (b + 2) := by
        rw [Real.rpow_add hn1, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hE : 0 ≤ Real.exp (-(((n : ℝ) + 1) * t)) := (Real.exp_pos _).le
      have hB : 0 ≤ 2 * ((n : ℝ) + 1) + t * ((n : ℝ) + 1) ^ 2 := by positivity
      calc |abelMertens n| * |abelDipole n t|
          ≤ (C₁ * ((n : ℝ) + 1) ^ b) *
              (Real.exp (-((n : ℝ) * t)) * (2 * ((n : ℝ) + 1) + t * ((n : ℝ) + 1) ^ 2)) :=
            mul_le_mul (hMa n) hd (abs_nonneg _) (by positivity)
        _ = C₁ * Real.exp 1 * Real.exp (t - 1) *
              (2 * (((n : ℝ) + 1) ^ b * ((n : ℝ) + 1) * Real.exp (-(((n : ℝ) + 1) * t))) +
                t * (((n : ℝ) + 1) ^ b * ((n : ℝ) + 1) ^ 2 *
                  Real.exp (-(((n : ℝ) + 1) * t)))) := by rw [hexp]; ring
        _ ≤ C₁ * Real.exp 1 * 1 *
              (2 * (((n : ℝ) + 1) ^ b * ((n : ℝ) + 1) * Real.exp (-(((n : ℝ) + 1) * t))) +
                t * (((n : ℝ) + 1) ^ b * ((n : ℝ) + 1) ^ 2 *
                  Real.exp (-(((n : ℝ) + 1) * t)))) := by
            gcongr
        _ = _ := by rw [hpow1, hpow2, mul_one]
    have hsum1 := sum_rpow_mul_exp_neg_le (c := b + 1) (by linarith) ht0 ht1 (K + 1)
    have hsum2 := sum_rpow_mul_exp_neg_le (c := b + 2) (by linarith) ht0 ht1 (K + 1)
    have hsub : ∀ c : ℝ, ∑ n ∈ Finset.Icc 1 K, ((n : ℝ) + 1) ^ c * Real.exp (-(((n : ℝ) + 1) * t)) ≤
        ∑ n ∈ range (K + 1), ((n : ℝ) + 1) ^ c * Real.exp (-(((n : ℝ) + 1) * t)) := fun c =>
      Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
        rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
        (fun n _ _ => by positivity)
    have hS1 := (hsub (b + 1)).trans hsum1
    have hS2 := (hsub (b + 2)).trans hsum2
    have hconst1 : (2 * (b + 1) / t) ^ (b + 1) * Real.exp (-(b + 1)) * (4 / t) =
        4 * A₁ * t ^ (-b - 2) := by
      rw [hA₁, div_eq_mul_one_div (2 * (b + 1)), Real.mul_rpow (by positivity) (by positivity),
        show t ^ (-b - 2) = (1 / t) ^ (b + 1) * (1 / t) by
          rw [show -b - 2 = -((b + 1) + 1) by ring, htp, Real.rpow_add (by positivity),
            Real.rpow_one]]
      ring
    have hconst2 : t * ((2 * (b + 2) / t) ^ (b + 2) * Real.exp (-(b + 2)) * (4 / t)) =
        4 * A₂ * t ^ (-b - 2) := by
      rw [hA₂, div_eq_mul_one_div (2 * (b + 2)), Real.mul_rpow (by positivity) (by positivity),
        show -b - 2 = -(b + 2) by ring, htp]
      have h4 : t * (4 / t) = 4 := by field_simp
      linear_combination ((2 * (b + 2)) ^ (b + 2) * (1 / t) ^ (b + 2) * Real.exp (-(b + 2))) * h4
    calc |∑ n ∈ Finset.Icc 1 K, abelMertens n * abelDipole n t|
        ≤ ∑ n ∈ Finset.Icc 1 K, |abelMertens n * abelDipole n t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 K, C₁ * Real.exp 1 *
            (2 * (((n : ℝ) + 1) ^ (b + 1) * Real.exp (-(((n : ℝ) + 1) * t))) +
              t * (((n : ℝ) + 1) ^ (b + 2) * Real.exp (-(((n : ℝ) + 1) * t)))) :=
          Finset.sum_le_sum hterm
      _ = C₁ * Real.exp 1 * (2 * ∑ n ∈ Finset.Icc 1 K,
            ((n : ℝ) + 1) ^ (b + 1) * Real.exp (-(((n : ℝ) + 1) * t)) +
            t * ∑ n ∈ Finset.Icc 1 K, ((n : ℝ) + 1) ^ (b + 2) * Real.exp (-(((n : ℝ) + 1) * t))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ C₁ * Real.exp 1 * (2 * (4 * A₁ * t ^ (-b - 2)) + 4 * A₂ * t ^ (-b - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have e1 := hconst1 ▸ hS1
          have e2 : t * ∑ n ∈ Finset.Icc 1 K,
              ((n : ℝ) + 1) ^ (b + 2) * Real.exp (-(((n : ℝ) + 1) * t)) ≤ 4 * A₂ * t ^ (-b - 2) :=
            hconst2 ▸ mul_le_mul_of_nonneg_left hS2 ht0.le
          linarith
      _ = C₁ * Real.exp 1 * (8 * A₁ + 4 * A₂) * t ^ (-b - 2) := by ring
  -- the endpoint term
  have hend : ∀ K : ℕ, |abelMertens (K + 1) * atom ((K + 1 : ℕ) : ℝ) t| ≤
      C₁ * 2 ^ b * A₀ * t ^ (-b - 2) := by
    intro K
    set y : ℝ := ((K + 1 : ℕ) : ℝ) with hy
    have hy1 : 1 ≤ y := by rw [hy]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
    have hy0 : 0 < y := by linarith
    rw [abs_mul]
    unfold atom
    rw [abs_of_nonneg (show (0 : ℝ) ≤ y ^ 2 * Real.exp (-(y * t)) by positivity)]
    have hMy : |abelMertens (K + 1)| ≤ C₁ * 2 ^ b * y ^ b := by
      refine (hMa (K + 1)).trans ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC₁
      rw [← Real.mul_rpow (by norm_num) hy0.le]
      apply Real.rpow_le_rpow (by positivity) _ hb
      rw [hy]; push_cast; linarith
    have hsup := rpow_mul_exp_neg_mul_le (a := b + 2) (by linarith) hy0.le ht0
    have hpow : y ^ b * y ^ 2 = y ^ (b + 2) := by
      rw [Real.rpow_add hy0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hconst : ((b + 2) / t) ^ (b + 2) * Real.exp (-(b + 2)) = A₀ * t ^ (-b - 2) := by
      rw [hA₀, div_eq_mul_one_div (b + 2), Real.mul_rpow (by positivity) (by positivity),
        show -b - 2 = -(b + 2) by ring, htp]
      ring
    calc |abelMertens (K + 1)| * (y ^ 2 * Real.exp (-(y * t)))
        ≤ (C₁ * 2 ^ b * y ^ b) * (y ^ 2 * Real.exp (-(y * t))) :=
          mul_le_mul_of_nonneg_right hMy (by positivity)
      _ = C₁ * 2 ^ b * (y ^ (b + 2) * Real.exp (-(y * t))) := by rw [← hpow]; ring
      _ ≤ C₁ * 2 ^ b * (A₀ * t ^ (-b - 2)) := by
          rw [← hconst]; exact mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = C₁ * 2 ^ b * A₀ * t ^ (-b - 2) := by ring
  rcases N with _ | K
  · simp [mobiusCubicSource]; positivity
  · rw [mobiusCubicSource_eq_abel]
    refine (abs_add_le _ _).trans ?_
    have h1 := hend K
    have h2 := hdip K
    nlinarith

/-- The discrete Gamma bound over `1 ≤ n ≤ N`. -/
theorem sum_Icc_rpow_mul_exp_neg_le {c t : ℝ} (hc : 0 ≤ c) (ht0 : 0 < t) (ht1 : t ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ c * Real.exp (-((n : ℝ) * t)) ≤
      (2 * c / t) ^ c * Real.exp (-c) * (4 / t) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, add_tsub_cancel_right]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) (sum_rpow_mul_exp_neg_le hc ht0 ht1 N)
  push_cast
  rw [add_comm (1 : ℝ)]

/-- For `t ≥ 1` the cubic source decays like `e^{-t}`, uniformly in `N`. -/
theorem abs_mobiusCubicSource_le_of_one_le {t : ℝ} (ht : 1 ≤ t) (N : ℕ) :
    |mobiusCubicSource N t| ≤ 64 * Real.exp (-1) * Real.exp (-t) := by
  unfold mobiusCubicSource
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 1 N, |((μ n : ℤ) : ℝ) * atom n t| ≤
      Real.exp (1 - t) * ((n : ℝ) ^ 2 * Real.exp (-(n : ℝ))) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hmu : |((μ n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    unfold atom
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) * t)) by positivity)]
    have hexp : Real.exp (-((n : ℝ) * t)) ≤ Real.exp (1 - t) * Real.exp (-(n : ℝ)) := by
      rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
    calc |((μ n : ℤ) : ℝ)| * ((n : ℝ) ^ 2 * Real.exp (-((n : ℝ) * t)))
        ≤ 1 * ((n : ℝ) ^ 2 * (Real.exp (1 - t) * Real.exp (-(n : ℝ)))) := by
          gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum' : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) ≤ 64 * Real.exp (-2) := by
    have h := sum_Icc_rpow_mul_exp_neg_le (c := 2) (by norm_num) one_pos le_rfl N
    have e1 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (2 : ℝ) * Real.exp (-((n : ℝ) * 1)) =
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) :=
      Finset.sum_congr rfl fun n _ => by rw [Real.rpow_two, mul_one]
    have e2 : (2 * (2 : ℝ) / 1) ^ (2 : ℝ) * Real.exp (-2) * (4 / 1) = 64 * Real.exp (-2) := by
      rw [Real.rpow_two]; ring
    rw [e1, e2] at h
    exact h
  calc Real.exp (1 - t) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ 2 * Real.exp (-(n : ℝ))
      ≤ Real.exp (1 - t) * (64 * Real.exp (-2)) :=
        mul_le_mul_of_nonneg_left hsum' (Real.exp_pos _).le
    _ = 64 * Real.exp ((1 - t) + -2) := by rw [Real.exp_add]; ring
    _ = 64 * Real.exp (-1 + -t) := by congr 2; ring
    _ = 64 * Real.exp (-1) * Real.exp (-t) := by rw [Real.exp_add]; ring

/-- **Boundedness above the threshold.**  If `|M(n)| ≤ C₁(n+1)^b` with `2b < 1 + δ`, then the cubic
Gamma energies `‖S_N‖_δ²` are bounded uniformly in `N`. -/
theorem exists_forall_gammaEnergy_mobiusCubicSource_le_of_mertens {b C₁ δ : ℝ} (hb : 0 ≤ b)
    (hC₁ : 0 ≤ C₁) (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤ C₁ * ((n : ℝ) + 1) ^ b)
    (hbδ : 2 * b < 1 + δ) :
    ∃ B : ℝ, ∀ N : ℕ, gammaEnergy δ (mobiusCubicSource N) ≤ B := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_mobiusCubicSource_le_of_mertens hb hC₁ hM
  set A : ℝ := 64 * Real.exp (-1) with hA
  set g : ℝ → ℝ := fun t => (Ioc (0 : ℝ) 1).indicator (fun t => K ^ 2 * t ^ (δ - 2 * b)) t +
    A ^ 2 * (t ^ (5 + δ - 1) * Real.exp (-(2 * t))) with hg
  have hgi : IntegrableOn g (Ioi 0) := by
    refine Integrable.add ?_ ((integrableOn_rpow_mul_exp (by linarith) two_pos).const_mul _)
    have hloc : IntegrableOn (fun t : ℝ => K ^ 2 * t ^ (δ - 2 * b)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    exact (hloc.integrable_indicator measurableSet_Ioc).integrableOn
  refine ⟨(Real.Gamma (5 + δ))⁻¹ * ∫ t in Ioi (0 : ℝ), g t, fun N => ?_⟩
  unfold gammaEnergy gammaInner
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith)).le)
  refine integral_mono_of_nonneg ?_ hgi ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (mul_self_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hind : 0 ≤ (Ioc (0 : ℝ) 1).indicator (fun t => K ^ 2 * t ^ (δ - 2 * b)) t :=
      Set.indicator_nonneg (fun x hx => mul_nonneg (sq_nonneg K) (Real.rpow_nonneg hx.1.le _)) _
    have hgam : 0 ≤ A ^ 2 * (t ^ (5 + δ - 1) * Real.exp (-(2 * t))) := by positivity
    rcases le_or_gt t 1 with ht1 | ht1
    · have hS := hK t ht0 ht1 N
      have hsq : mobiusCubicSource N t * mobiusCubicSource N t ≤ K ^ 2 * (t ^ (-b - 2)) ^ 2 := by
        rw [← abs_mul_abs_self]
        exact (mul_le_mul hS hS (abs_nonneg _) (by positivity)).trans (le_of_eq (by ring))
      have hpow : t ^ (4 + δ) * (t ^ (-b - 2)) ^ 2 = t ^ (δ - 2 * b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
        congr 1; push_cast; ring
      simp only [hg, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1⟩)]
      calc t ^ (4 + δ) * (mobiusCubicSource N t * mobiusCubicSource N t)
          ≤ t ^ (4 + δ) * (K ^ 2 * (t ^ (-b - 2)) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg ht0.le _)
        _ = K ^ 2 * t ^ (δ - 2 * b) := by rw [← hpow]; ring
        _ ≤ _ := le_add_of_nonneg_right hgam
    · have hS := abs_mobiusCubicSource_le_of_one_le ht1.le N
      have hsq : mobiusCubicSource N t * mobiusCubicSource N t ≤ A ^ 2 * Real.exp (-(2 * t)) := by
        rw [← abs_mul_abs_self]
        have := mul_le_mul hS hS (abs_nonneg _) (by positivity)
        refine this.trans (le_of_eq ?_)
        rw [hA, show -(2 * t) = -t + -t by ring, Real.exp_add]; ring
      simp only [hg, Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => by
        linarith [h.2]), zero_add, show (5 + δ - 1) = 4 + δ by ring]
      calc t ^ (4 + δ) * (mobiusCubicSource N t * mobiusCubicSource N t)
          ≤ t ^ (4 + δ) * (A ^ 2 * Real.exp (-(2 * t))) :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg ht0.le _)
        _ = _ := by ring

/-- Bounded cubic energies below the zero abscissa: if `2Θ < 1 + δ`, the energies `‖S_N‖_δ²` are
bounded uniformly in `N`. -/
theorem exists_forall_gammaEnergy_mobiusCubicSource_le_of_two_mul_zetaZeroAbscissa_lt {δ : ℝ}
    (hδ : 2 * zetaZeroAbscissa < 1 + δ) :
    ∃ B : ℝ, ∀ N : ℕ, gammaEnergy δ (mobiusCubicSource N) ≤ B := by
  set ε : ℝ := (1 + δ - 2 * zetaZeroAbscissa) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C, hC, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε0
  exact exists_forall_gammaEnergy_mobiusCubicSource_le_of_mertens
    (by linarith [half_le_zetaZeroAbscissa]) hC hM (by rw [hε]; linarith)

/-- **Exponent law for Route L's cubic source.**  Let `Θ = sup {Re ρ : ζ(ρ) = 0}`.  For `δ ≥ 0`
off the boundary `1 + δ = 2Θ`, the cubic Gamma energies `‖S_N‖_δ²` of
`S_N(t) = Σ_{n ≤ N} μ(n) n² e^{-nt}` are bounded in `N` exactly when `2Θ < 1 + δ`; below the
threshold they tend to infinity.  At `δ = 0` the energies are always unbounded. -/
theorem bddAbove_range_gammaEnergy_mobiusCubicSource_iff {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hne : 1 + δ ≠ 2 * zetaZeroAbscissa) :
    BddAbove (range fun N : ℕ => gammaEnergy δ (mobiusCubicSource N)) ↔
      2 * zetaZeroAbscissa < 1 + δ := by
  constructor
  · intro hbdd
    by_contra hlt
    have hlt' : 1 + δ < 2 * zetaZeroAbscissa := lt_of_le_of_ne (not_lt.mp hlt) hne
    have hδ1 : δ < 1 := by linarith [zetaZeroAbscissa_le_one]
    obtain ⟨ρ, hζ, hρ⟩ := exists_zetaZero_lt_re (b := (1 + δ) / 2) (by linarith)
    have hT := tendsto_gammaEnergy_mobiusCubicSource_atTop_of_riemannZeta_eq_zero hδ0 hδ1 hζ
      (by linarith)
    exact not_bddAbove_iff.mpr (fun B => by
      obtain ⟨N, hN⟩ := (hT.eventually_gt_atTop B).exists
      exact ⟨_, ⟨N, rfl⟩, hN⟩) hbdd
  · intro hlt
    obtain ⟨B, hB⟩ := exists_forall_gammaEnergy_mobiusCubicSource_le_of_two_mul_zetaZeroAbscissa_lt hlt
    exact ⟨B, by rintro _ ⟨N, rfl⟩; exact hB N⟩

end RHTower.CubicGamma
