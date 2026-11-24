import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechMinorCocycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedKoszulComponent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechRestriction

/-! If the weights are linear combinations of a selected subsequence,
the top values on any other subsequence differ by its change-of-basis
determinant modulo that subsequence's weight ideal. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k R E κ : Type} [Field k] [CommRing R] [Algebra k R]
  [AddCommGroup E] [Module k E] [LinearOrder κ] [Fintype κ] {d : ℕ}

omit [Fintype κ] in
theorem orderedMinor_selectedIndices (ρ : κ → Fin d → R) (e : Fin d ↪o κ) :
    orderedMinor ρ (selectedIndices e) = (Matrix.of fun i j => ρ (e i) j).det := by
  have hcard : (selectedIndices e).card = d := by simp [selectedIndices]
  have he : (fun i => e i) = (selectedIndices e).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard
      (fun i => Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩) e.strictMono
  rw [orderedMinor, dif_pos hcard]
  congr 1
  ext i j
  simp only [Matrix.of_apply, ← congrFun he i]

omit [Fintype κ] in
private theorem selectedValue_mem_selectedBoundaryValues {P : Submodule k E}
    {w : κ → Module.End k E} (e : Fin d ↪o κ) {a : Finset κ → E}
    (ha : a ∈ (acx (fun _ => P) w).B (d : ℤ)) :
    a (selectedIndices e) ∈ selectedBoundaryValues P w e := by
  obtain ⟨v, hv, hvD⟩ := ha
  let b (s : Finset (Fin d)) := v (s.map e.toEmbedding)
  have hb : b ∈ (acx (fun _ => P) fun i => w (e i)).C ((d : ℤ) - 1) :=
    acx_mem_terms_iff.mpr fun L => by
      simpa only [Finset.card_map] using acx_mem_terms_iff.mp hv (L.map e.toEmbedding)
  refine ⟨wd (fun i => w (e i)) b, ⟨b, hb, rfl⟩, ?_⟩
  change wd (fun i => w (e i)) b Finset.univ = a (selectedIndices e)
  dsimp only [b]
  rw [wd_orderEmbedding e w v Finset.univ]
  exact congrFun hvD (selectedIndices e)

/-- A minor cocycle provides the change-of-basis law for the top
components modulo the selected boundary values. -/
theorem sub_selectedDeterminant_mem_boundaryValues
    (act : R →ₐ[k] Module.End k E) (P : Submodule k E)
    (hP : ∀ r v, v ∈ P → act r v ∈ P)
    (e f : Fin d ↪o κ) (r : κ → R) (ρ : κ → Fin d → R)
    (hr : ∀ l, r l = ∑ j, ρ l j * r (e j))
    (hρ : (Matrix.of fun i j => ρ (e i) j) = 1)
    (hE : ∀ m < (d : ℤ),
      (acx (fun _ => P) fun i => act (r (e i))).Z m ≤
        (acx (fun _ => P) fun i => act (r (e i))).B m)
    {a : Finset κ → E} (ha : a ∈ (acx (fun _ => P) fun l => act (r l)).Z (d : ℤ)) :
    a (selectedIndices f) - act ((Matrix.of fun i j => ρ (f i) j).det) (a (selectedIndices e)) ∈
      selectedBoundaryValues P (fun l => act (r l)) f := by
  let w (l : κ) := act (r l)
  let v := a (selectedIndices e)
  have hv : v ∈ P := by
    have hcard : ((selectedIndices e).card : ℤ) = d := by simp [selectedIndices]
    simpa only [if_pos hcard] using acx_mem_terms_iff.mp ha.1 (selectedIndices e)
  let b (L : Finset κ) := act (orderedMinor ρ L) v
  have hb : b ∈ (acx (fun _ => P) w).Z (d : ℤ) := by
    refine ⟨acx_mem_terms_iff.mpr (fun L => ?_), ?_⟩
    · by_cases hd : L.card = d
      · have hcast : (L.card : ℤ) = d := congrArg (fun a : ℕ => (a : ℤ)) hd
        rw [if_pos hcast]
        exact hP _ _ hv
      · change b L ∈ _
        dsimp only [b]
        rw [orderedMinor, dif_neg hd, map_zero, LinearMap.zero_apply]
        exact zero_mem _
    · change wd w b = 0
      have hw : w = fun l => act (∑ j, ρ l j * r (e j)) :=
        funext fun l => congrArg act (hr l)
      rw [hw]
      exact wd_orderedMinor_eq_zero act ρ (fun j => r (e j)) v
  have hbe : b (selectedIndices e) = v := by
    dsimp only [b]
    rw [orderedMinor_selectedIndices, hρ, Matrix.det_one, map_one, Module.End.one_apply]
  have hzero : (a - b) (selectedIndices e) ∈ selectedBoundaryValues P w e := by
    rw [Pi.sub_apply, hbe, sub_self]
    exact zero_mem _
  have hB : a - b ∈ (acx (fun _ => P) w).B (d : ℤ) :=
    boundary_of_selected_component e
      (fun i j => (Commute.all (r i) (r j)).map act)
      (fun i _ hu => hP _ _ hu) hE (sub_mem ha hb) hzero
  have hm := selectedValue_mem_selectedBoundaryValues f hB
  simpa only [Pi.sub_apply, b, orderedMinor_selectedIndices] using hm

end GlobalTheory.WH
