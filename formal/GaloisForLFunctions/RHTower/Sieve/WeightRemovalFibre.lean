import GaloisForLFunctions.RHTower.Sieve.FibreWindowBridge
import GaloisForLFunctions.RHTower.Sieve.FibreKernelUniform
import GaloisForLFunctions.RHTower.Sieve.FibreTrivialBound

/-!
# Removing an arithmetic weight from the fibre mean square

The short-interval argument does not work with the Möbius function itself but with the Möbius
function weighted by the number of its prime factors from a designated set, because only the
weighted polynomial factors.  Undoing the weight costs the variance of the weight around its mean:
writing `W·f = f·g − f·(g − W)` and squaring,

    W² (∑_{b ∈ F} f b)² ≤ 2 (∑_{b ∈ F} f b g b)² + 2 |F| ∑_{b ∈ F} (g b − W)² .

Averaged over the fibres this is quantitative, because a fibre has at most `h + 1` elements and
each index lies in at most `2h + 1` fibres, so the whole cost is the variance of `g` over the single
dyadic block carrying every fibre.

Nothing here is arithmetic: `g` is an arbitrary real weight.  The arithmetic enters only when `g` is
the designated prime count and its variance is supplied by Turán--Kubilius.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-! ## One fibre -/

/-- **Undoing a weight on one index set.**  The cost is the weight's variance, times the size of the
set. -/
theorem sq_sum_le_weighted_add_variance {f g : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (W : ℝ)
    (F : Finset ℕ) :
    W ^ 2 * (∑ b ∈ F, f b) ^ 2
      ≤ 2 * (∑ b ∈ F, f b * g b) ^ 2 + 2 * (F.card : ℝ) * ∑ b ∈ F, (g b - W) ^ 2 := by
  classical
  have hsplit : W * ∑ b ∈ F, f b
      = (∑ b ∈ F, f b * g b) - ∑ b ∈ F, f b * (g b - W) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdev : (∑ b ∈ F, f b * (g b - W)) ^ 2
      ≤ (F.card : ℝ) * ∑ b ∈ F, (g b - W) ^ 2 := by
    refine le_trans sq_sum_le_card_mul_sum_sq ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (Nat.cast_nonneg _)
    have hb := hf b
    have hsq : (f b) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (f b), sq_abs (f b)]
    nlinarith [sq_nonneg (g b - W), hsq]
  have hval : W ^ 2 * (∑ b ∈ F, f b) ^ 2 = (W * ∑ b ∈ F, f b) ^ 2 := by ring
  rw [hval, hsplit]
  nlinarith [hdev, sq_nonneg ((∑ b ∈ F, f b * g b) + ∑ b ∈ F, f b * (g b - W)),
    sq_nonneg ((∑ b ∈ F, f b * g b) - ∑ b ∈ F, f b * (g b - W))]

/-! ## The multiplicity of an index -/

/-- **Each index lies in at most `2h + 1` fibres.** -/
theorem card_outer_of_mem_innerFibre_le {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h) {b : ℕ}
    (hb : b ∈ fibreDyadicIndex x h) :
    (((outerBlock x h).filter (fun a => b ∈ innerFibre x h a)).card : ℝ) ≤ 2 * h + 1 := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [fibreDyadicIndex, Finset.mem_Icc] at hb
  have hb1 : 1 ≤ b := by
    have h1 : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
    omega
  have hblo : Real.sqrt x / 2 ≤ (b : ℝ) := by
    have hceil : Real.sqrt x / 2 ≤ ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have : ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1
    linarith
  have hcongr : (outerBlock x h).filter (fun a => b ∈ innerFibre x h a)
      = (outerBlock x h).filter (fun a => b ∈ innerFibre x h a ∧ b ∈ innerFibre x h a) := by
    refine Finset.filter_congr fun a _ => ?_
    constructor
    · intro hmem
      exact ⟨hmem, hmem⟩
    · intro hmem
      exact hmem.1
  rw [hcongr]
  refine fibre_kernel_le_two_h hx0.le hh0 hb1 hb1 ?_
  rwa [min_self]

/-! ## The averaged cost -/

/-- **Undoing the weight, averaged over the fibres.**  Every fibre pays its own variance; each index
is counted at most `2h + 1` times, and each fibre has at most `h + 1` elements, so the total cost is
the variance of the weight over the single dyadic block carrying all the fibres. -/
theorem sum_sq_fibreSum_le_weighted {f g : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 4 ≤ x) (hh0 : 0 ≤ h) (W : ℝ) :
    W ^ 2 * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ 2 * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b * g b) ^ 2
        + 2 * (h + 1) * (2 * h + 1) * ∑ b ∈ fibreDyadicIndex x h, (g b - W) ^ 2 := by
  classical
  set D : Finset ℕ := fibreDyadicIndex x h with hD
  set c : ℕ → ℝ := fun b => (g b - W) ^ 2 with hc
  have hc0 : ∀ b, 0 ≤ c b := fun b => sq_nonneg _
  -- one fibre
  have hfibre : ∀ a ∈ outerBlock x h,
      W ^ 2 * (∑ b ∈ innerFibre x h a, f b) ^ 2
        ≤ 2 * (∑ b ∈ innerFibre x h a, f b * g b) ^ 2
          + 2 * (h + 1) * ∑ b ∈ innerFibre x h a, c b := by
    intro a ha
    refine (sq_sum_le_weighted_add_variance (g := g) hf W (innerFibre x h a)).trans ?_
    have hsum0 : (0 : ℝ) ≤ ∑ b ∈ innerFibre x h a, c b :=
      Finset.sum_nonneg fun b _ => hc0 b
    have hcard := card_innerFibre_le_block (by linarith : (0:ℝ) ≤ x) hh0 ha
    nlinarith [hsum0, hcard]
  have hstep := Finset.sum_le_sum hfibre
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hstep
  refine hstep.trans ?_
  -- the double count
  have hdouble : (∑ a ∈ outerBlock x h, ∑ b ∈ innerFibre x h a, c b)
      = ∑ b ∈ D, (((outerBlock x h).filter (fun a => b ∈ innerFibre x h a)).card : ℝ) * c b := by
    have hrestrict : ∀ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, c b)
        = ∑ b ∈ D, (if b ∈ innerFibre x h a then c b else 0) := by
      intro a ha
      rw [Finset.sum_ite_mem]
      refine (Finset.sum_congr ?_ fun _ _ => rfl).symm
      exact Finset.inter_eq_right.2 (innerFibre_subset_fibreDyadicIndex hx ha)
    rw [Finset.sum_congr rfl hrestrict, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hdouble]
  have hmult : ∑ b ∈ D, (((outerBlock x h).filter (fun a => b ∈ innerFibre x h a)).card : ℝ) * c b
      ≤ ∑ b ∈ D, (2 * h + 1) * c b := by
    refine Finset.sum_le_sum fun b hb => ?_
    exact mul_le_mul_of_nonneg_right (card_outer_of_mem_innerFibre_le hx hh0 hb) (hc0 b)
  rw [← Finset.mul_sum] at hmult
  have hfac : (0 : ℝ) ≤ 2 * (h + 1) := by linarith
  have := mul_le_mul_of_nonneg_left hmult hfac
  have hval : 2 * (h + 1) * ((2 * h + 1) * ∑ b ∈ D, c b)
      = 2 * (h + 1) * (2 * h + 1) * ∑ b ∈ D, c b := by ring
  rw [hval] at this
  linarith [this]

end

end RHTower.Sieve
