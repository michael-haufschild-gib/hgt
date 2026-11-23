import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.MixedCechCupBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechFiltrationExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact

/-! When the right columns are acyclic, a left cocycle is a boundary
if its edge is a boundary in the complex of mixed intersections. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι κ M : Type} [Field k] [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
  [AddCommGroup M] [Module k M]

/-- Keep the coefficients on intersections with at least one left index. -/
def leftSupported (G : Finset (ι ⊕ₗ κ) → Submodule k M) :
    Finset (ι ⊕ₗ κ) → Submodule k M :=
  fun s => if (lft s).Nonempty then G s else ⊥

/-- For a finite joined cover, acyclicity of the right columns implies
acyclicity of the total weighted complex. -/
theorem boundary_of_rightColumns_exact
    {A : Finset (ι ⊕ₗ κ) → Submodule k M} {w : ι ⊕ₗ κ → Module.End k M}
    (hcx : (acx A w).IsCx)
    (hE : ∀ I m, (rightColumn A w I).Z m ≤ (rightColumn A w I).B m)
    {n : ℤ} {c : Finset (ι ⊕ₗ κ) → M} (hc : c ∈ (acx A w).Z n) :
    c ∈ (acx A w).B n := by
  let d : ℤ := (Fintype.card κ : ℤ) + 1
  have hQ := qEx_of_rightColumn_exact A w d (fun I m _ => hE I m)
  have hcard (s : Finset (ι ⊕ₗ κ)) : ((s ∩ rightIndices).card : ℤ) < d := by
    rw [← uni_lft_rgt s, card_inter_rightIndices]
    have e : (rgt s).card ≤ Fintype.card κ := Finset.card_le_univ _
    dsimp only [d]
    omega
  exact boundary_of_top_level_boundary hcx hQ (y := 0) hc
    (fun s hs => (hs (hcard s).le).elim) (zero_mem _) (fun _ _ => rfl)
    (fun s hs => ((hcard s).ne hs).elim)

/-- Restricting a primitive on the joined cover to an empty right
index set gives a primitive on the left cover. -/
theorem left_boundary_of_edge_boundary (G : Finset (ι ⊕ₗ κ) → Submodule k M)
    (hcx : (acx (leftSupported G) (1 : (ι ⊕ₗ κ) → Module.End k M)).IsCx)
    (hE : ∀ I m, (rightColumn (leftSupported G) 1 I).Z m ≤ (rightColumn (leftSupported G) 1 I).B m)
    {q : ℕ} {a : Finset ι → M} (ha : a ∈ (cech (fun I => G (uni I (∅ : Finset κ)))).Z q)
    (h : edge1 a ∈ (mixedCech (fun I J => G (uni I J))).B ((q : ℤ) + 2)) :
    a ∈ (cech (fun I => G (uni I (∅ : Finset κ)))).B q := by
  let w : (ι ⊕ₗ κ) → Module.End k M := 1
  let e : ℤ := (-1) ^ (q + 1)
  have hterm (I : Finset ι) :
      a I ∈ (if I.Nonempty ∧ (I.card : ℤ) = q + 1 then G (uni I ∅) else ⊥) :=
    Submodule.mem_pi.mp ha.1 I (Set.mem_univ _)
  have haz (I : Finset ι) (hI : I.card ≠ q + 1) : a I = 0 :=
    (Submodule.mem_bot k).mp (by
      have H : ¬ (I.Nonempty ∧ (I.card : ℤ) = q + 1) := fun h => hI (by exact_mod_cast h.2)
      simpa only [if_neg H] using hterm I)
  have hD : deltaL k (ι ⊕ₗ κ) M (extendLeft a) = e • edge1 a := by
    rw [deltaL_extendLeft a (LinearMap.mem_ker.mp ha.2)]
    funext s
    change (-1 : ℤ) ^ (lft s).card • edge1 a s = e • edge1 a s
    by_cases hs : (lft s).card = q + 1
    · rw [hs]
    · simp [edge1, haz _ hs]
  obtain ⟨v, hv, hdv⟩ := Submodule.mem_map.mp h
  change wd w v = edge1 a at hdv
  let C := acx (leftSupported G) w
  let b := extendLeft (κ := κ) a - e • v
  have hvC : v ∈ C.C ((q : ℤ) + 1) := by
    refine acx_mem_terms_iff.mpr fun s => ?_
    have hmem := acx_mem_terms_iff.mp hv s
    change v s ∈ (if (s.card : ℤ) = (q : ℤ) + 2 - 1 then
      (if (lft s).Nonempty ∧ (rgt s).Nonempty then G (uni (lft s) (rgt s)) else ⊥) else ⊥) at hmem
    rw [show (q : ℤ) + 2 - 1 = q + 1 by omega, uni_lft_rgt] at hmem
    unfold leftSupported
    split_ifs at hmem with hd hboth
    · rw [if_pos hd, if_pos hboth.1]
      exact hmem
    all_goals rw [(Submodule.mem_bot k).mp hmem]; exact zero_mem _
  have haC : extendLeft (κ := κ) a ∈ C.C ((q : ℤ) + 1) := by
    refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    simp only [extendLeft, lft_uni, rgt_uni, leftSupported, card_uni]
    by_cases hJ : J = ∅
    · subst J
      simp only [if_true, Finset.card_empty, add_zero]
      have hs := hterm I
      split_ifs at hs with hI
      · rw [if_pos hI.2, if_pos hI.1]
        exact hs
      · rw [(Submodule.mem_bot k).mp hs]
        exact zero_mem _
    · rw [if_neg hJ]
      exact zero_mem _
  have hb : b ∈ C.Z ((q : ℤ) + 1) := by
    refine ⟨sub_mem haC (zsmul_mem hvC _), ?_⟩
    change wd w (extendLeft a - e • v) = 0
    rw [map_sub, map_zsmul, hdv, show w = 1 from rfl, wd_one, hD, sub_self]
  obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (boundary_of_rightColumns_exact hcx hE hb)
  refine ⟨fun I => u (uni I ∅), Submodule.mem_pi.mpr (fun I _ => ?_), ?_⟩
  · have hs := acx_mem_terms_iff.mp hu (uni I (∅ : Finset κ))
    change u (uni I (∅ : Finset κ)) ∈ (if ((uni I (∅ : Finset κ)).card : ℤ) = (q : ℤ) + 1 - 1 then
      leftSupported G (uni I (∅ : Finset κ)) else ⊥) at hs
    simp only [card_uni, Finset.card_empty, add_zero, add_sub_cancel_right, leftSupported, lft_uni] at hs
    change u (uni I (∅ : Finset κ)) ∈
      (if I.Nonempty ∧ (I.card : ℤ) = (q : ℤ) - 1 + 1 then G (uni I ∅) else ⊥)
    rw [sub_add_cancel]
    split_ifs at hs with hI hI'
    · rw [if_pos ⟨hI', hI⟩]
      exact hs
    all_goals rw [(Submodule.mem_bot k).mp hs]; exact zero_mem _
  · funext I
    change deltaL k ι M (fun J => u (uni J (∅ : Finset κ))) I = a I
    have hd := deltaL_uni u I (∅ : Finset κ)
    have hu0 : deltaL k κ M (fun J => u (uni I J)) ∅ = 0 := by rw [deltaL_apply, Finset.sum_empty]
    rw [hu0, smul_zero, add_zero] at hd
    change wd w u = b at hdu
    have he : deltaL k (ι ⊕ₗ κ) M u = b := by simpa only [w, wd_one] using hdu
    rw [← hd, he]
    have hs := acx_mem_terms_iff.mp hv (uni I (∅ : Finset κ))
    change v (uni I (∅ : Finset κ)) ∈ (if ((uni I (∅ : Finset κ)).card : ℤ) = (q : ℤ) + 2 - 1 then
      (if (lft (uni I (∅ : Finset κ))).Nonempty ∧ (rgt (uni I (∅ : Finset κ))).Nonempty then
        G (uni (lft (uni I (∅ : Finset κ))) (rgt (uni I (∅ : Finset κ)))) else ⊥) else ⊥) at hs
    have hv0 : v (uni I (∅ : Finset κ)) = 0 := by
      simpa only [rgt_uni, Finset.not_nonempty_empty, and_false, if_false, ite_self, Submodule.mem_bot] using hs
    simp only [b, Pi.sub_apply, Pi.smul_apply, hv0, smul_zero, sub_zero, extendLeft, lft_uni, rgt_uni, if_true]

end GlobalTheory.WH
