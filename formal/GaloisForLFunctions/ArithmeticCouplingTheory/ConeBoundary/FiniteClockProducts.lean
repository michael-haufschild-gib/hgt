import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite products of positive clock shifts

Bounded two-clock moments control every product of affine clock factors by
the product of their coefficient norms. Joint clock separation supplies a
normalized factor that kills one selected point and preserves another.
The same coefficient norm bounds each factor on a bounded clock set.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- Three coefficients act by the two forward clock shifts and the identity. -/
lemma norm_three_clock_terms_le {x y z c₀ c₁ c₂ : ℂ} {B : ℝ}
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) (hz : ‖z‖ ≤ B) :
    ‖c₀*x+c₁*y+c₂*z‖ ≤ (‖c₀‖+‖c₁‖+‖c₂‖)*B := by
  calc
    _ ≤ ‖c₀*x‖+‖c₁*y‖+‖c₂*z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖c₀‖*‖x‖+‖c₁‖*‖y‖+‖c₂‖*‖z‖ := by rw [norm_mul,norm_mul,norm_mul]
    _ ≤ ‖c₀‖*B+‖c₁‖*B+‖c₂‖*B := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
    _ = _ := by ring

/-- Bounded positive clock moments control every finite product of affine clock factors.
The cost is the product of the coefficient norms; no inverse clock is used. -/
theorem clock_product_moment_bound {ι κ : Type*} (d U V : ι → ℂ)
    (c₀ c₁ c₂ : κ → ℂ) {M : ℝ}
    (hs : ∀ m n : ℕ, Summable (fun i => d i*U i^m*V i^n))
    (hM : ∀ m n : ℕ, ‖∑' i, d i*U i^m*V i^n‖ ≤ M)
    (F : Finset κ) : ∀ m n : ℕ,
      Summable (fun i => d i*(∏ j ∈ F, (c₀ j+c₁ j*U i+c₂ j*V i))*U i^m*V i^n) ∧
      ‖∑' i, d i*(∏ j ∈ F, (c₀ j+c₁ j*U i+c₂ j*V i))*U i^m*V i^n‖ ≤
        M*∏ j ∈ F, (‖c₀ j‖+‖c₁ j‖+‖c₂ j‖) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro m n
    simpa only [prod_empty,mul_one] using And.intro (hs m n) (hM m n)
  | @insert j F hj ih =>
    intro m n
    let f (a b : ℕ) (i : ι) := d i*(∏ k ∈ F, (c₀ k+c₁ k*U i+c₂ k*V i))*U i^a*V i^b
    have he (i : ι) :
        d i*(∏ k ∈ insert j F, (c₀ k+c₁ k*U i+c₂ k*V i))*U i^m*V i^n =
        c₀ j*f m n i+c₁ j*f (m+1) n i+c₂ j*f m (n+1) i := by
      rw [prod_insert hj]
      simp only [f,pow_succ]
      ring
    have hs₀ : Summable (f m n) := (ih m n).1
    have hs₁ : Summable (f (m+1) n) := (ih (m+1) n).1
    have hs₂ : Summable (f m (n+1)) := (ih m (n+1)).1
    have hsum := ((hs₀.mul_left (c₀ j)).add (hs₁.mul_left (c₁ j))).add (hs₂.mul_left (c₂ j))
    refine ⟨hsum.congr (fun i => (he i).symm),?_⟩
    rw [tsum_congr he,((hs₀.mul_left (c₀ j)).add (hs₁.mul_left (c₁ j))).tsum_add
      (hs₂.mul_left (c₂ j)),(hs₀.mul_left (c₀ j)).tsum_add (hs₁.mul_left (c₁ j)),
      tsum_mul_left,tsum_mul_left,tsum_mul_left,prod_insert hj]
    have hh := norm_three_clock_terms_le (c₀ := c₀ j) (c₁ := c₁ j) (c₂ := c₂ j)
      (ih m n).2 (ih (m+1) n).2 (ih m (n+1)).2
    convert hh using 1; ring

/-- A separated clock gives an affine factor equal to zero at one point and one at another. -/
lemma one_clock_affine_separator {u₀ u : ℂ} {δ R : ℝ}
    (hδ : 0 < δ) (hsep : δ/2 ≤ ‖u₀-u‖) (hu : ‖u‖ ≤ R) :
    ∃ c₀ c₁ : ℂ, c₀+c₁*u=0 ∧ c₀+c₁*u₀=1 ∧
      ‖c₀‖+‖c₁‖ ≤ 2*(R+1)/δ := by
  have hd : 0 < ‖u₀-u‖ := (half_pos hδ).trans_le hsep
  have hne : u₀-u ≠ 0 := norm_pos_iff.mp hd
  refine ⟨-u/(u₀-u),1/(u₀-u),by ring,?_,?_⟩
  · field_simp
    ring
  · rw [norm_div,norm_neg,norm_div,norm_one,← add_div]
    calc
      _ ≤ (R+1)/‖u₀-u‖ := div_le_div_of_nonneg_right (add_le_add hu le_rfl) hd.le
      _ ≤ (R+1)/(δ/2) := div_le_div_of_nonneg_left
        (by linarith only [norm_nonneg u,hu]) (half_pos hδ) hsep
      _ = _ := by ring

/-- Joint separation supplies a normalized affine factor using only positive clocks. -/
theorem exists_affine_clock_separator {u₀ v₀ u v : ℂ} {δ R : ℝ}
    (hδ : 0 < δ) (hsep : δ ≤ ‖u₀-u‖+‖v₀-v‖)
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ∃ c₀ c₁ c₂ : ℂ, c₀+c₁*u+c₂*v=0 ∧ c₀+c₁*u₀+c₂*v₀=1 ∧
      ‖c₀‖+‖c₁‖+‖c₂‖ ≤ 2*(R+1)/δ := by
  by_cases h : δ/2 ≤ ‖u₀-u‖
  · obtain ⟨c₀,c₁,hzero,hone,hbound⟩ := one_clock_affine_separator hδ h hu
    refine ⟨c₀,c₁,0,?_,?_,?_⟩
    · simpa only [zero_mul,add_zero] using hzero
    · simpa only [zero_mul,add_zero] using hone
    · simpa only [norm_zero,add_zero] using hbound
  · have hh : δ/2 ≤ ‖v₀-v‖ := by linarith only [hsep,lt_of_not_ge h]
    obtain ⟨c₀,c₂,hzero,hone,hbound⟩ := one_clock_affine_separator hδ hh hv
    refine ⟨c₀,0,c₂,?_,?_,?_⟩
    · simpa only [zero_mul,add_zero] using hzero
    · simpa only [zero_mul,add_zero] using hone
    · simpa only [norm_zero,add_zero] using hbound

/-- The same coefficient bound controls an affine factor throughout a bounded clock set. -/
lemma norm_affine_clocks_le {c₀ c₁ c₂ U V : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hU : ‖U‖ ≤ R) (hV : ‖V‖ ≤ R) :
    ‖c₀+c₁*U+c₂*V‖ ≤ R*(‖c₀‖+‖c₁‖+‖c₂‖) := by
  have hh := norm_three_clock_terms_le (c₀ := c₀) (c₁ := c₁) (c₂ := c₂)
    (show ‖(1:ℂ)‖ ≤ R by simpa only [norm_one] using hR) hU hV
  simpa only [mul_one,mul_comm] using hh

lemma norm_clock_product_le {κ : Type*} (F : Finset κ) (c₀ c₁ c₂ : κ → ℂ)
    {U V : ℂ} {R L : ℝ} (hR : 1 ≤ R)
    (hU : ‖U‖ ≤ R) (hV : ‖V‖ ≤ R)
    (hcoeff : ∀ j ∈ F, ‖c₀ j‖+‖c₁ j‖+‖c₂ j‖ ≤ L) :
    ‖∏ j ∈ F, (c₀ j+c₁ j*U+c₂ j*V)‖ ≤ (R*L)^F.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _j ∈ F, (R*L) := prod_le_prod (fun _ _ => norm_nonneg _) fun j hj =>
      (norm_affine_clocks_le hR hU hV).trans
        (mul_le_mul_of_nonneg_left (hcoeff j hj) (zero_le_one.trans hR))
    _ = _ := by rw [prod_const]

#print axioms clock_product_moment_bound
#print axioms exists_affine_clock_separator
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
