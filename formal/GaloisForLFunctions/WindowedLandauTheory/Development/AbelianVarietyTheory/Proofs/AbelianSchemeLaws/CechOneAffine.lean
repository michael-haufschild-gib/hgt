import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CechOneSplitting
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Tactic.Ring

/-! Clearing denominators on a finite principal refinement splits an additive Čech
one-cocycle on an affine open. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.LineBundleSections

namespace GlobalTheory.CechOne

variable {Z : Scheme.{0}} {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}

/-- Every additive Čech one-cocycle has a primitive upon restriction to an affine open. -/
theorem exists_splitting_on_affine (hV : ⨆ a, V a = ⊤) (hφ : IsCocycle V φ) {O : Z.Opens}
    (hO : IsAffineOpen O) : ∃ ψ, Splits V φ O ψ := by
  classical
  have h1 : ∀ x : O, ∃ (f : Γ(Z, O)) (a : I), Z.basicOpen f ≤ V a ∧ x.1 ∈ Z.basicOpen f := by
    intro x
    have : x.1 ∈ ⨆ a, V a := by rw [hV]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp this
    obtain ⟨f, hf, hx⟩ := hO.exists_basicOpen_le ⟨x.1, ha⟩ x.2
    exact ⟨f, a, hf, hx⟩
  choose f₀ a₀ hfa₀ hx₀ using h1
  obtain ⟨s, hs⟩ := hO.isCompact.elim_finite_subcover (fun x : O => (Z.basicOpen (f₀ x) : Set Z))
    (fun x => (Z.basicOpen (f₀ x)).2) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx₀ _⟩)
  let f : s → Γ(Z, O) := fun k => f₀ k.1
  let a : s → I := fun k => a₀ k.1
  let D : s → Z.Opens := fun k => Z.basicOpen (f k)
  have hDa : ∀ k, D k ≤ V (a k) := fun k => hfa₀ k.1
  have hDO : ∀ k, D k ≤ O := fun k => Z.basicOpen_le _
  have hcov : O ≤ iSup D := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Opens.mem_iSup.mpr ⟨⟨k, hk⟩, hxk⟩
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hO.self_le_iSup_basicOpen_iff]
    refine hcov.trans (iSup_le fun k => ?_)
    exact le_iSup (fun g : Set.range f => Z.basicOpen g.1) ⟨f k, k, rfl⟩
  have hDaff : ∀ k, IsAffineOpen (D k) := fun k => hO.basicOpen _
  have hbo : ∀ (N : Z.Opens) (hN : N ≤ O) l, Z.basicOpen (resG Z hN (f l)) = N ⊓ D l :=
    fun N hN l => Z.basicOpen_res _ _

  have h2 : ∀ k l, ∃ (n : ℕ) (u : Γ(Z, D k)), resG Z (inf_le_left : D k ⊓ D l ≤ D k) u =
      resG Z (inf_le_left.trans (hDO k)) (f l) ^ n * resG Z (inf_le_inf (hDa k) (hDa l)) (φ (a k) (a l)) := by
    intro k l
    have e := hbo (D k) (hDO k) l
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Z (D k) (hDaff k) (resG Z (hDO k) (f l))
      (resG Z (e.le.trans (inf_le_inf (hDa k) (hDa l))) (φ (a k) (a l)))
    refine ⟨n, y, ?_⟩
    have hy' : resG Z (Z.basicOpen_le _) y = resG Z (Z.basicOpen_le _) (resG Z (hDO k) (f l)) ^ n *
      resG Z (e.le.trans (inf_le_inf (hDa k) (hDa l))) (φ (a k) (a l)) := hy
    simpa only [resG_resG, map_mul, map_pow] using congrArg (resG Z e.ge) hy'
  choose n u hu using h2
  obtain ⟨A, hA⟩ := (Set.finite_range fun p : s × s => n p.1 p.2).bddAbove
  have hA' : ∀ k l, n k l ≤ A := fun k l => hA ⟨(k, l), rfl⟩
  let u' : ∀ k l : s, Γ(Z, D k) := fun k l => resG Z (hDO k) (f l) ^ (A - n k l) * u k l
  have hu' : ∀ k l (M : Z.Opens) (hk : M ≤ D k) (hl : M ≤ D l), resG Z hk (u' k l) =
      resG Z (hk.trans (hDO k)) (f l) ^ A * resG Z (le_inf (hk.trans (hDa k)) (hl.trans (hDa l)))
        (φ (a k) (a l)) := by
    intro k l M hk hl
    have := congrArg (resG Z (le_inf hk hl)) (hu k l)
    simp only [u', resG_resG, map_mul, map_pow] at this ⊢
    rw [this, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hA' k l)]
  have h3 : ∀ k m l, ∃ n : ℕ, resG Z ((inf_le_left : D k ⊓ D m ≤ D k).trans (hDO k)) (f l) ^ n *
      (resG Z inf_le_left (u' k l) - resG Z inf_le_right (u' m l) -
        resG Z (inf_le_left.trans (hDO k)) (f l) ^ A *
          resG Z (inf_le_inf (hDa k) (hDa m)) (φ (a k) (a m))) = 0 := by
    intro k m l
    have haff : IsAffineOpen (D k ⊓ D m) := by
      rw [← hbo (D k) (hDO k) m]; exact (hDaff k).basicOpen _
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Z haff _ _ ?_
    have e := hbo (D k ⊓ D m) (inf_le_left.trans (hDO k)) l
    have hk := e.le.trans (inf_le_left.trans inf_le_left)
    have hm := e.le.trans (inf_le_left.trans inf_le_right)
    have hl := e.le.trans inf_le_right
    change resG Z (Z.basicOpen_le _) _ = 0
    have e1 := hu' k l _ hk hl
    have e2 := hu' m l _ hm hl
    have e3 := hφ (a k) (a m) (a l) _ (hk.trans (hDa k)) (hm.trans (hDa m)) (hl.trans (hDa l))
    simp only [resG_resG, map_mul, map_pow, map_sub]
    rw [e1, e2, ← e3]
    ring
  choose n' hn' using h3
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : s × s × s => n' p.1 p.2.1 p.2.2).bddAbove
  have hB' : ∀ k m l, n' k m l ≤ B := fun k m l => hB ⟨(k, m, l), rfl⟩
  have hspan' : Ideal.span (Set.range fun l => f l ^ (B + A)) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hspan (B + A)
    rwa [← Set.range_comp] at this
  obtain ⟨e, he⟩ := (Ideal.mem_span_range_iff_exists_fun).mp
    ((Ideal.eq_top_iff_one _).mp hspan')
  let g : ∀ k, Γ(Z, D k) := fun k => -∑ l, resG Z (hDO k) (e l * f l ^ B) * u' k l
  let ψ : ∀ k b, Γ(Z, D k ⊓ V b) := fun k b =>
    resG Z (le_inf inf_le_right (inf_le_left.trans (hDa k))) (φ b (a k))
  refine splittings_glue D ψ ?_ g ?_ O hcov
  · intro k b d N hk hb hd
    have := hφ b d (a k) N hb hd (hk.trans (hDa k))
    simp only [ψ, resG_resG]
    linear_combination this
  · intro k m b M hk hm hb
    have e1 := hφ b (a k) (a m) M hb (hk.trans (hDa k)) (hm.trans (hDa m))
    have hM := hk.trans (hDO k)
    have e2 : ∀ l, resG Z hM (e l * f l ^ B) * resG Z hk (u' k l) - resG Z hM (e l * f l ^ B) * resG Z hm (u' m l) =
        resG Z hM (e l * f l ^ (B + A)) *
          resG Z (le_inf (hk.trans (hDa k)) (hm.trans (hDa m))) (φ (a k) (a m)) := by
      intro l
      have := congrArg (resG Z (le_inf hk hm)) (hn' k m l)
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (hB' k m l)
      simp only [resG_resG, map_mul, map_pow, map_sub, map_zero] at this ⊢
      rw [hc]
      linear_combination (resG Z hM (e l) * resG Z hM (f l) ^ c) * this
    have e3 := Finset.sum_congr (rfl : (Finset.univ : Finset s) = _) (fun l _ => e2 l)
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum, he, map_one, one_mul] at e3
    simp only [ψ, g, resG_resG, map_neg, map_sum, map_mul] at e3 ⊢
    linear_combination e3 + e1

end GlobalTheory.CechOne
