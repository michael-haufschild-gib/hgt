import GaloisForLFunctions.RHTower.RegularizedLogZetaAbscissa
import GaloisForLFunctions.RHTower.DirichletSummatorySwap

/-!
# Power growth under arithmetic convolution

Multiplication by a power shifts the growth exponent of partial sums.
Dirichlet convolution preserves every strict power bound when the other
factor is absolutely summable at those exponents. An inverse satisfying
the same absolute bounds makes this preservation an equivalence.
-/

noncomputable section

open Filter Topology Finset

namespace RHTower

private theorem weightedDirichletTerm (g : ℕ → ℝ) (b σ : ℝ) (n : ℕ) :
    ((g n * ((n : ℝ) + 1) ^ b : ℝ) : ℂ) *
        (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)) =
      (g n : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((σ - b : ℝ) : ℂ)) := by
  have hn : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity : (n : ℝ) + 1 ≠ 0)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), mul_assoc,
    ← Complex.cpow_add _ _ hn]
  congr 2
  push_cast
  ring

/-- A real power shifts the strict partial-sum growth class exactly. -/
theorem PartialSumPowerBound.rpow_weight {g : ℕ → ℝ} {θ b : ℝ}
    (hg : PartialSumPowerBound g θ) (hθ : 0 ≤ θ) (hθb : 0 ≤ θ + b) :
    PartialSumPowerBound (fun n => g n * ((n : ℝ) + 1) ^ b) (θ + b) := by
  apply (partialSumPowerBound_iff_convergesRightOf _ hθb).2
  intro σ hσ
  obtain ⟨L, hL⟩ := (partialSumPowerBound_iff_convergesRightOf g hθ).1 hg
    (σ - b) (by linarith only [hσ])
  refine ⟨L, ?_⟩
  simpa only [weightedDirichletTerm] using hL

/-- Removing the same power recovers the original growth class. -/
theorem partialSumPowerBound_rpow_weight_iff {g : ℕ → ℝ} {θ b : ℝ}
    (hθ : 0 ≤ θ) (hθb : 0 ≤ θ + b) :
    PartialSumPowerBound (fun n => g n * ((n : ℝ) + 1) ^ b) (θ + b) ↔
      PartialSumPowerBound g θ := by
  constructor
  · intro h
    have hback := h.rpow_weight (b := -b) hθb (by linarith only [hθ])
    have he : (fun n : ℕ => (g n * ((n : ℝ) + 1) ^ b) * ((n : ℝ) + 1) ^ (-b)) = g := by
      funext n
      rw [mul_assoc, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, mul_one]
    simpa only [he, add_neg_cancel_right] using hback
  · intro h
    exact h.rpow_weight hθ hθb

/-- The hyperbola identity transfers partial-sum cancellation through an
absolutely summable arithmetic factor. -/
theorem partialSumPowerBound_convolution {f g : ArithmeticFunction ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hg : PartialSumPowerBound (fun n => g (n + 1)) θ)
    (hf : ∀ δ : ℝ, 0 < δ →
      Summable (fun n : ℕ => |f n| * (n : ℝ) ^ (-(θ + δ)))) :
    PartialSumPowerBound (fun n => (f * g) (n + 1)) θ := by
  intro δ hδ
  obtain ⟨C, hC, hG⟩ := hg (δ / 2) (half_pos hδ)
  let p := θ + δ / 2
  have hp : 0 ≤ p := by dsimp only [p]; linarith only [hθ, hδ]
  have hs := hf (δ / 2) (half_pos hδ)
  let D : ℝ := ∑' n : ℕ, |f n| * (n : ℝ) ^ (-p)
  have hD : 0 ≤ D := tsum_nonneg fun n =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C * (2 : ℝ) ^ p * D, by positivity, fun N => ?_⟩
  have hG' (M : ℕ) : |∑ m ∈ Icc 1 M, g m| ≤ C * ((M : ℝ) + 1) ^ p := by
    simpa only [sum_range_succ_eq_sourcePartialSum, sourcePartialSum] using hG M
  have hscale {d : ℕ} (hd : d ∈ Icc 1 N) :
      (((N / d : ℕ) : ℝ) + 1) ^ p ≤
        (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p * (d : ℝ) ^ (-p) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdiv : ((N / d : ℕ) : ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
    have hdN : (d : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hd).2
    have hmul : (((N / d : ℕ) : ℝ) + 1) * d ≤ 2 * ((N : ℝ) + 1) := by
      nlinarith only [hdiv, hdN]
    have hpow := Real.rpow_le_rpow (by positivity) hmul hp
    rw [Real.mul_rpow (by positivity) hdR.le,
      Real.mul_rpow (by norm_num) (by positivity)] at hpow
    have hc : (d : ℝ) ^ p * (d : ℝ) ^ (-p) = 1 := by
      rw [← Real.rpow_add hdR, add_neg_cancel, Real.rpow_zero]
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hdR p)).mp
    calc
      _ = ((((N / d : ℕ) : ℝ) + 1) ^ p) * (d : ℝ) ^ p := by ring
      _ ≤ (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p := hpow
      _ = ((2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) * ((d : ℝ) ^ p * (d : ℝ) ^ (-p)) := by
        rw [hc, mul_one]
      _ = _ := by ring
  have hterm (d : ℕ) (hd : d ∈ Icc 1 N) :
      |f d| * |∑ m ∈ Icc 1 (N / d), g m| ≤
        (C * (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) * (|f d| * (d : ℝ) ^ (-p)) := by
    calc
      _ ≤ |f d| * (C * (((N / d : ℕ) : ℝ) + 1) ^ p) :=
        mul_le_mul_of_nonneg_left (hG' (N / d)) (abs_nonneg _)
      _ ≤ |f d| * (C * ((2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p * (d : ℝ) ^ (-p))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hscale hd) hC) (abs_nonneg _)
      _ = _ := by ring
  have hbound : |∑ n ∈ Icc 1 N, (f * g) n| ≤
      (C * (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) * D := by
    rw [sum_Icc_mul_apply]
    calc
      _ ≤ ∑ d ∈ Icc 1 N, |f d * ∑ m ∈ Icc 1 (N / d), g m| := abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Icc 1 N, |f d| * |∑ m ∈ Icc 1 (N / d), g m| := by simp only [abs_mul]
      _ ≤ ∑ d ∈ Icc 1 N,
          (C * (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) * (|f d| * (d : ℝ) ^ (-p)) :=
        sum_le_sum hterm
      _ = (C * (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) *
          ∑ d ∈ Icc 1 N, |f d| * (d : ℝ) ^ (-p) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum _ (fun d _ => mul_nonneg (abs_nonneg _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (by positivity)
  rw [sum_range_succ_eq_sourcePartialSum]
  change |∑ n ∈ Icc 1 N, (f * g) n| ≤ _
  calc
    _ ≤ (C * (2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) * D := hbound
    _ = (C * (2 : ℝ) ^ p * D) * ((N : ℝ) + 1) ^ p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) N])
        (by dsimp only [p]; linarith only [hδ])) (by positivity)

/-- A convolution unit with absolutely summable inverse preserves the
strict power-growth threshold in both directions. -/
theorem partialSumPowerBound_convolution_iff {f g h : ArithmeticFunction ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hfg : f * g = 1)
    (hf : ∀ δ : ℝ, 0 < δ → Summable (fun n : ℕ => |f n| * (n : ℝ) ^ (-(θ + δ))))
    (hg : ∀ δ : ℝ, 0 < δ → Summable (fun n : ℕ => |g n| * (n : ℝ) ^ (-(θ + δ)))) :
    PartialSumPowerBound (fun n => (f * h) (n + 1)) θ ↔
      PartialSumPowerBound (fun n => h (n + 1)) θ := by
  constructor
  · intro hbound
    have hx := partialSumPowerBound_convolution hθ hbound hg
    have he : g * (f * h) = h := by rw [← mul_assoc, mul_comm g f, hfg, one_mul]
    simpa only [he] using hx
  · intro hbound
    exact partialSumPowerBound_convolution hθ hbound hf

end RHTower
