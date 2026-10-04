import GaloisForLFunctions.RHTower.RoutePFinitePrimeCovariance
import Mathlib.Data.Finset.SymmDiff

/-!
# Complete signed-pair expansion of the cofactor covariance

The local two-channel matrix has entries `1`, `-b`, and `b²+w`.
Finite prime induction identifies its complete pair sum with the
cofactor squares, retaining all off-diagonal source correlations.
-/

open Finset
open scoped symmDiff

namespace RHTower.RoutePWindow

variable {ι : Type*} [DecidableEq ι]

noncomputable def pairKernel (P : Finset ι) (b w : ι → ℝ) (S T : Finset ι) : ℝ :=
  ∏ p ∈ P, if p ∈ S then (if p ∈ T then (b p)^2+w p else -b p)
    else (if p ∈ T then -b p else 1)

noncomputable def sourcePair (P : Finset ι) (a b w : ι → ℝ)
    (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
    pairKernel P b w S T*f (t-∑ p ∈ S, a p)*g (t-∑ p ∈ T, a p)

private theorem kernel_left_irrelevant (P S T : Finset ι) (b w : ι → ℝ)
    {p : ι} (hp : p ∉ P) : pairKernel P b w (insert p S) T = pairKernel P b w S T := by
  apply prod_congr rfl
  intro q hq
  have hqp : q ≠ p := fun h => hp (h ▸ hq)
  simp only [mem_insert, hqp, false_or]

private theorem kernel_right_irrelevant (P S T : Finset ι) (b w : ι → ℝ)
    {p : ι} (hp : p ∉ P) : pairKernel P b w S (insert p T) = pairKernel P b w S T := by
  apply prod_congr rfl
  intro q hq
  have hqp : q ≠ p := fun h => hp (h ▸ hq)
  simp only [mem_insert, hqp, false_or]

private theorem kernel_none (P S T : Finset ι) (b w : ι → ℝ)
    {p : ι} (hp : p ∉ P) (hpS : p ∉ S) (hpT : p ∉ T) :
    pairKernel (insert p P) b w S T = pairKernel P b w S T := by
  simp only [pairKernel, prod_insert hp, hpS, hpT, if_false, one_mul]

private theorem kernel_left (P S T : Finset ι) (b w : ι → ℝ)
    {p : ι} (hp : p ∉ P) (hpT : p ∉ T) :
    pairKernel (insert p P) b w (insert p S) T = -b p*pairKernel P b w S T := by
  change (∏ q ∈ insert p P, if q ∈ insert p S then
    (if q ∈ T then (b q)^2+w q else -b q) else (if q ∈ T then -b q else 1)) = _
  rw [prod_insert hp]
  simp only [mem_insert_self, hpT, if_true, if_false]
  rw [show (∏ q ∈ P, if q ∈ insert p S then
    (if q ∈ T then (b q)^2+w q else -b q) else (if q ∈ T then -b q else 1)) =
      pairKernel P b w S T from kernel_left_irrelevant P S T b w hp]

private theorem kernel_right (P S T : Finset ι) (b w : ι → ℝ)
    {p : ι} (hp : p ∉ P) (hpS : p ∉ S) :
    pairKernel (insert p P) b w S (insert p T) = -b p*pairKernel P b w S T := by
  change (∏ q ∈ insert p P, if q ∈ S then
    (if q ∈ insert p T then (b q)^2+w q else -b q)
    else (if q ∈ insert p T then -b q else 1)) = _
  rw [prod_insert hp]
  simp only [mem_insert_self, hpS, if_true, if_false]
  rw [show (∏ q ∈ P, if q ∈ S then
    (if q ∈ insert p T then (b q)^2+w q else -b q)
    else (if q ∈ insert p T then -b q else 1)) =
      pairKernel P b w S T from kernel_right_irrelevant P S T b w hp]

private theorem kernel_both (P S T : Finset ι) (b w : ι → ℝ)
    {p : ι} (hp : p ∉ P) :
    pairKernel (insert p P) b w (insert p S) (insert p T) =
      ((b p)^2+w p)*pairKernel P b w S T := by
  change (∏ q ∈ insert p P, if q ∈ insert p S then
    (if q ∈ insert p T then (b q)^2+w q else -b q)
    else (if q ∈ insert p T then -b q else 1)) = _
  rw [prod_insert hp]
  simp only [mem_insert_self, if_true]
  change ((b p)^2+w p)*pairKernel P b w (insert p S) (insert p T) = _
  rw [kernel_left_irrelevant P S (insert p T) b w hp,
    kernel_right_irrelevant P S T b w hp]

private theorem sourcePair_insert (P : Finset ι) (a b w : ι → ℝ)
    (f g : ℝ → ℝ) {p : ι} (hp : p ∉ P) (t : ℝ) :
    sourcePair (insert p P) a b w f g t = sourcePair P a b w f g t -
      b p*sourcePair P a b w f (fun x => g (x-a p)) t -
      b p*sourcePair P a b w (fun x => f (x-a p)) g t +
      ((b p)^2+w p)*sourcePair P a b w
        (fun x => f (x-a p)) (fun x => g (x-a p)) t := by
  have h00 : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      pairKernel (insert p P) b w S T*f (t-∑ q ∈ S, a q)*g (t-∑ q ∈ T, a q)) =
        sourcePair P a b w f g t := by
    apply sum_congr rfl
    intro S hS
    apply sum_congr rfl
    intro T hT
    rw [kernel_none P S T b w hp
      (fun h => hp ((mem_powerset.mp hS) h)) (fun h => hp ((mem_powerset.mp hT) h))]
  have h01 : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      pairKernel (insert p P) b w S (insert p T)*
        f (t-∑ q ∈ S, a q)*g (t-∑ q ∈ insert p T, a q)) =
        -b p*sourcePair P a b w f (fun x => g (x-a p)) t := by
    unfold sourcePair
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    have hpS : p ∉ S := fun h => hp ((mem_powerset.mp hS) h)
    have hpT : p ∉ T := fun h => hp ((mem_powerset.mp hT) h)
    rw [kernel_right P S T b w hp hpS, sum_insert hpT]
    dsimp only
    rw [show t-(a p+∑ q ∈ T, a q) = t-(∑ q ∈ T, a q)-a p by ring]
    ring
  have h10 : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      pairKernel (insert p P) b w (insert p S) T*
        f (t-∑ q ∈ insert p S, a q)*g (t-∑ q ∈ T, a q)) =
        -b p*sourcePair P a b w (fun x => f (x-a p)) g t := by
    unfold sourcePair
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    have hpS : p ∉ S := fun h => hp ((mem_powerset.mp hS) h)
    have hpT : p ∉ T := fun h => hp ((mem_powerset.mp hT) h)
    rw [kernel_left P S T b w hp hpT, sum_insert hpS]
    dsimp only
    rw [show t-(a p+∑ q ∈ S, a q) = t-(∑ q ∈ S, a q)-a p by ring]
    ring
  have h11 : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      pairKernel (insert p P) b w (insert p S) (insert p T)*
        f (t-∑ q ∈ insert p S, a q)*g (t-∑ q ∈ insert p T, a q)) =
        ((b p)^2+w p)*sourcePair P a b w
          (fun x => f (x-a p)) (fun x => g (x-a p)) t := by
    unfold sourcePair
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    have hpS : p ∉ S := fun h => hp ((mem_powerset.mp hS) h)
    have hpT : p ∉ T := fun h => hp ((mem_powerset.mp hT) h)
    rw [kernel_both P S T b w hp, sum_insert hpS, sum_insert hpT]
    dsimp only
    rw [show t-(a p+∑ q ∈ S, a q) = t-(∑ q ∈ S, a q)-a p by ring,
      show t-(a p+∑ q ∈ T, a q) = t-(∑ q ∈ T, a q)-a p by ring]
    ring
  change (∑ S ∈ (insert p P).powerset, ∑ T ∈ (insert p P).powerset,
    pairKernel (insert p P) b w S T*f (t-∑ q ∈ S, a q)*g (t-∑ q ∈ T, a q)) = _
  simp_rw [sum_powerset_insert hp, sum_add_distrib]
  rw [h00, h01, h10, h11]
  ring

private theorem sourcePair_difference (P : Finset ι) (a b w : ι → ℝ)
    (f : ℝ → ℝ) (c d z t : ℝ) :
    sourcePair P a b w (fun x => f x-c*f (x-d)) (fun x => f x-c*f (x-d)) t +
      z*sourcePair P a b w (fun x => f (x-d)) (fun x => f (x-d)) t =
    sourcePair P a b w f f t - c*sourcePair P a b w f (fun x => f (x-d)) t -
      c*sourcePair P a b w (fun x => f (x-d)) f t +
      (c^2+z)*sourcePair P a b w (fun x => f (x-d)) (fun x => f (x-d)) t := by
  unfold sourcePair
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro T _
  ring

/-- Exact signed-pair identity: every common, unmatched, and delayed
prime channel survives in the cofactor-square expansion. -/
theorem covariance_eq_sourcePair (P : Finset ι) (a b w : ι → ℝ)
    (f : ℝ → ℝ) (t : ℝ) : covariance P a b w f t = sourcePair P a b w f f t := by
  induction P using Finset.induction_on generalizing f with
  | empty => simp [covariance, sourcePair, pairKernel, pow_two]
  | @insert p P hp ih =>
    rw [covariance_insert P a b w f hp, ih, ih,
      sourcePair_difference, sourcePair_insert P a b w f f hp]

/-- With the biased prime gains, the complete matrix is exactly the
symmetric-difference kernel on the original signed source coefficients. -/
theorem pairKernel_bias (P S T : Finset ι) (θ q : ι → ℝ)
    (hS : S ⊆ P) (hT : T ⊆ P) :
    pairKernel P (fun p => θ p*q p) (fun p => (1-(θ p)^2)*(q p)^2) S T =
      (∏ p ∈ S, -q p)*(∏ p ∈ T, -q p)*(∏ p ∈ S ∆ T, θ p) := by
  have hm (R : Finset ι) (hR : R ⊆ P) (v : ι → ℝ) :
      (∏ p ∈ P, if p ∈ R then v p else 1) = ∏ p ∈ R, v p := by
    calc
      _ = ∏ p ∈ R, if p ∈ R then v p else 1 :=
        (prod_subset hR (fun p _ hp => if_neg hp)).symm
      _ = _ := prod_congr rfl (fun p hp => if_pos hp)
  have hST : S ∆ T ⊆ P := by
    intro p hp
    rcases mem_symmDiff.mp hp with h | h
    · exact hS h.1
    · exact hT h.1
  rw [← hm S hS (fun p => -q p), ← hm T hT (fun p => -q p), ← hm (S ∆ T) hST θ,
    ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  by_cases hs : p ∈ S <;> by_cases ht : p ∈ T <;>
    simp only [mem_symmDiff, hs, ht, true_and, false_and, and_false,
      or_false, false_or, not_true_eq_false, not_false_eq_true, if_true, if_false] <;> ring

end RHTower.RoutePWindow
