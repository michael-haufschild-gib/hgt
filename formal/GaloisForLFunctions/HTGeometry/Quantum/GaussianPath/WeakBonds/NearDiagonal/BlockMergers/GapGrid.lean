import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Spectral spacing of a sum of two independently scaled blocks -/
open Finset
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- Right-block dilation in a fixed grid between one half and one. -/
def scale {N : ℕ} (k : Fin N) : ℝ := 1/2+(k.val:ℝ)/(2*(N:ℝ))

theorem scale_mem {N : ℕ} (k : Fin N) : scale k ∈ Set.Icc (1/2:ℝ) 1 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hk : (k.val:ℝ)<N := Nat.cast_lt.mpr k.isLt
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (by positivity))
  · have h : (k.val:ℝ)/(2*N)≤1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hk])
    dsimp only [scale]; linarith only [h]

private theorem mesh_gap {N : ℕ} {s t : Fin N} (h : s≠t) :
    1/(2*(N:ℝ)) ≤ |scale s-scale t| := by
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt s.isLt)
  have inc (i j : Fin N) (hij : i<j) : 1/(2*(N:ℝ)) ≤ scale j-scale i := by
    have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1≤j.val from hij)
    have h := div_le_div_of_nonneg_right (by linarith only [hh] : (1:ℝ) ≤ j.val-i.val)
      (by positivity : (0:ℝ) ≤ 2*N)
    simpa only [scale,add_sub_add_left_eq_sub,sub_div] using h
  rcases lt_or_gt_of_ne h with hs|ht
  · rw [abs_sub_comm]; exact (inc s t hs).trans (le_abs_self _)
  · exact (inc t s ht).trans (le_abs_self _)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- One more grid point than ordered pairs of product levels suffices.
A single pair cannot collide at two scales because its relative
velocity is either zero or at least the right-block spacing. -/
theorem exists_separated_scale (a : I→ℝ) (b : J→ℝ) {g : ℝ} (hg : 0<g)
    (ha : ∀ i j, i≠j → g ≤ |a i-a j|) (hb : ∀ i j, i≠j → g ≤ |b i-b j|) :
    let N := Fintype.card ((I×J)×(I×J))+1
    ∃ k : Fin N, ∀ u v : I×J, u≠v →
      g/(8*(N:ℝ)) ≤ |(a u.1+scale k*b u.2)-(a v.1+scale k*b v.2)| := by
  classical
  intro N
  have hN : (1:ℝ)≤N := by exact_mod_cast (show 1≤N from Nat.succ_pos _)
  have hN₀ : (0:ℝ)<N := zero_lt_one.trans_le hN
  let r := g/(8*(N:ℝ))
  let d (i : Fin N) (u v : I×J) := (a u.1+scale i*b u.2)-(a v.1+scale i*b v.2)
  by_contra! h
  choose u v huv hcollision using h
  let F (i : Fin N) := (u i,v i)
  have hinj : Function.Injective F := by
    intro s t he
    by_contra hne
    have hu : u s=u t := congrArg Prod.fst he
    have hv : v s=v t := congrArg Prod.snd he
    have h₁ : |d s (u s) (v s)|<r := hcollision s
    have h₂ : |d t (u s) (v s)|<r := by rw [hu,hv]; exact hcollision t
    have hj : (u s).2 ≠ (v s).2 := by
      intro hj
      have hi : (u s).1≠(v s).1 := fun hi => huv s (Prod.ext hi hj)
      have hgap := ha _ _ hi
      dsimp only [d] at h₁
      rw [hj,add_sub_add_right_eq_sub] at h₁
      have hr : r≤g := div_le_self hg.le (by linarith only [hN])
      exact hgap.not_gt (h₁.trans_le hr)
    have hdiff : (scale s-scale t)*(b (u s).2-b (v s).2)=d s (u s) (v s)-d t (u s) (v s) := by
      dsimp only [d]; ring
    have ht := abs_sub_le (d s (u s) (v s)) 0 (d t (u s) (v s))
    rw [sub_zero,zero_sub,abs_neg,←hdiff,abs_mul] at ht
    have hl := mul_le_mul (mesh_gap hne) (hb _ _ hj) hg.le (abs_nonneg _)
    have hl' : (1/(2*(N:ℝ)))*g=4*r := by dsimp only [r]; ring
    rw [hl'] at hl
    have hr : 0<r := div_pos hg (by positivity)
    linarith only [hl,ht,h₁,h₂,hr]
  have hc := Fintype.card_le_of_injective F hinj
  rw [Fintype.card_fin] at hc
  exact (Nat.not_succ_le_self _) hc

#print axioms exists_separated_scale
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
