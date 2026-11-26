import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! # Separating product spectra by contracting one child Hamiltonian -/

open Finset
namespace GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap.BalancedCuts
noncomputable section

/-- Equally spaced contractions between one half and one. -/
def scale {M : ℕ} (k : Fin M) : ℝ := 1/2+(k.val:ℝ)/(2*M)

theorem scale_mem {M : ℕ} (k : Fin M) : scale k∈Set.Icc (1/2:ℝ) 1 := by
  have hm : 0<(M:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hk : (k.val:ℝ)≤M := Nat.cast_le.mpr k.isLt.le
  refine ⟨le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (by positivity)),?_⟩
  change 1/2+(k.val:ℝ)/(2*M)≤1
  have h := (div_le_iff₀ (show 0<2*(M:ℝ) by positivity)).mpr
    (show (k.val:ℝ)≤(1/2)*(2*M) by linarith only [hk])
  linarith only [h]

private theorem scale_separation {M : ℕ} {k l : Fin M} (h : k≠l) :
    1/(2*(M:ℝ))≤|scale k-scale l| := by
  have hm : 0<(M:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hdiff : scale k-scale l=((k.val:ℝ)-(l.val:ℝ))/(2*M) := by
    unfold scale; ring
  rw [hdiff,abs_div,abs_of_pos (show 0<2*(M:ℝ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rcases lt_or_gt_of_ne h with hkl|hlk
  · have hval : (k.val:ℝ)+1≤l.val := by exact_mod_cast (show k.val+1≤l.val from hkl)
    rw [abs_of_nonpos (by linarith only [hval])]
    linarith only [hval]
  · have hval : (l.val:ℝ)+1≤k.val := by exact_mod_cast (show l.val+1≤k.val from hlk)
    exact (by linarith only [hval] : 1≤(k.val:ℝ)-l.val).trans (le_abs_self _)

/-- On a grid of M contractions, one nonhorizontal spectral difference
excludes at most one tick at radius g/(8M). -/
private theorem affine_bad_unique {M : ℕ} {A B g : ℝ} (hg : 0<g) (hB : g≤|B|)
    {k l : Fin M} (hk : |A+scale k*B|<g/(8*M)) (hl : |A+scale l*B|<g/(8*M)) : k=l := by
  by_contra h
  have hm : 0<(M:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hlo := mul_le_mul (scale_separation h) hB hg.le (abs_nonneg _)
  have he : (scale k-scale l)*B=(A+scale k*B)-(A+scale l*B) := by ring
  rw [←abs_mul,he] at hlo
  have hhi := (abs_sub _ _).trans_lt (add_lt_add hk hl)
  have hn := hlo.trans_lt hhi
  field_simp at hn
  nlinarith only [hn,hg,mul_pos hg hm]

/-- At most one scale per ordered pair of product eigenvalues can spoil
the spacing. The bound is uniform in both spectra and their widths. -/
theorem few_bad_product_scales {I J : Type*} [Fintype I] [Fintype J]
    (E : I→ℝ) (F : J→ℝ) {g h : ℝ} (hh : 0<h)
    (hE : ∀ i j, i≠j → g≤|E i-E j|) (hF : ∀ i j, i≠j → h≤|F i-F j|) (M : ℕ) :
    open Classical in
    let z (k : Fin M) (p : I×J) := E p.1+scale k*F p.2
    let r := min g (h/(8*M))
    (univ.filter fun k => ∃ p q, p≠q ∧ |z k p-z k q|<r).card≤(Fintype.card (I×J))^2 := by
  classical
  intro z r
  let bad (v : (I×J)×(I×J)) := univ.filter fun k : Fin M =>
    v.1≠v.2 ∧ |z k v.1-z k v.2|<r
  have hone (v : (I×J)×(I×J)) : (bad v).card≤1 := by
    apply card_le_one.mpr
    intro k hk l hl
    obtain ⟨hne,hk⟩ := (mem_filter.mp hk).2
    have hl := (mem_filter.mp hl).2.2
    by_cases hv : v.1.2=v.2.2
    · have hf : v.1.1≠v.2.1 := fun he => hne (Prod.ext he hv)
      have he : z k v.1-z k v.2=E v.1.1-E v.2.1 := by dsimp only [z]; rw [hv]; ring
      rw [he] at hk
      exact ((hk.trans_le (min_le_left ..)).not_ge (hE _ _ hf)).elim
    · have he (s : Fin M) : z s v.1-z s v.2=
          (E v.1.1-E v.2.1)+scale s*(F v.1.2-F v.2.2) := by dsimp only [z]; ring
      rw [he] at hk hl
      exact affine_bad_unique hh (hF _ _ hv) (hk.trans_le (min_le_right ..)) (hl.trans_le (min_le_right ..))
  apply (card_le_card (t:=univ.biUnion bad) ?_).trans
  · apply (card_biUnion_le (s:=univ) (t:=bad)).trans
    apply (sum_le_sum (s:=univ) (fun v _ => hone v)).trans_eq
    simp [Fintype.card_prod,pow_two,mul_assoc]
  · intro k hk
    obtain ⟨p,q,hpq,hsmall⟩ := (mem_filter.mp hk).2
    exact mem_biUnion.mpr ⟨(p,q),mem_univ _,mem_filter.mpr ⟨mem_univ _,hpq,hsmall⟩⟩

#print axioms few_bad_product_scales
end
end GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap.BalancedCuts
