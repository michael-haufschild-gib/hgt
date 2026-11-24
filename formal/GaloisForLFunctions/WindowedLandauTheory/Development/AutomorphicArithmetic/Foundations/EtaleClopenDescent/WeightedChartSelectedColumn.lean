import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnScaling
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedKoszulComponent

/-! A selected affine Koszul subsequence controls the lower exactness
and top boundary criterion of the corresponding homogeneous column. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ] [Fintype κ]
  {d r : ℕ} (T : WeightedChartSystem k d S E)
  {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)}
  (n : κ → ℕ × ℕ) (z : κ → S)

/-- Exactness for the normalized selected weights gives homogeneous
column exactness. In top degree it suffices to test the selected value
by a condition invariant under scalar units. -/
theorem columnExact_and_boundary_of_selected (hT : T.Good) (hz : T.Admitted n z)
    (hi : i ∈ I) (hj : j ∈ J) (e : Fin r ↪o κ) (K : E → Prop)
    (hunit : ∀ (u : Sˣ) a, K a → K (T.act u a))
    (hK : let w := fun l => T.act (T.normalizedWeight n z i j l)
      ∀ (m : ℤ), m < (r : ℤ) →
        (acx (fun _ => T.M I J) (fun l => w (e l))).Z m ≤
          (acx (fun _ => T.M I J) (fun l => w (e l))).B m)
    (htop : let w := fun l => T.act (T.normalizedWeight n z i j l)
      ∀ a ∈ T.M I J, K a → a ∈ selectedBoundaryValues (T.M I J) w e) :
    let C := T.columnComplex n z I J
    (∀ (m : ℤ), m < (r : ℤ) → C.Z m ≤ C.B m) ∧
      (∀ a ∈ C.Z (r : ℤ), K (a (selectedIndices e)) → a ∈ C.B (r : ℤ)) := by
  let C := T.columnComplex n z I J
  let M := T.M I J
  let w := fun l => T.act (T.normalizedWeight n z i j l)
  let D := acx (fun _ => M) w
  have hw (l m : κ) : Commute (w l) (w m) := (Commute.all _ _).map T.act
  have hM (l : κ) : M ≤ M.comap (w l) := fun a ha =>
    hT.stab I J ⟨i, hi⟩ ⟨j, hj⟩ _ (T.normalizedWeight_mem hT hz hi hj l) _ ha
  refine ⟨?_, ?_⟩
  · intro m hm
    apply T.columnExact_of_normalized hT n z hi hj m
    change D.Z m ≤ D.B m
    intro c hc
    have hz (L : Finset κ) (hne : (L.card : ℤ) ≠ m) : c L = 0 :=
      (Submodule.mem_bot k).mp (by simpa only [if_neg hne] using acx_mem_terms_iff.mp hc.1 L)
    refine boundary_of_top_level_boundary (acx_isCx _ w hw (fun _ l _ => hM l))
      (qEx_of_subsequence_exact M w e hK) hc ?_
      (zero_mem _ : (0 : Finset κ → E) ∈ D.C (m - 1)) (fun _ _ => rfl) ?_
    · intro L hL
      have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := L) (s₂ := selectedIndices e))
      exact hz L (by omega)
    · intro L hL
      have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := L) (s₂ := selectedIndices e))
      rw [map_zero, Pi.zero_apply, hz L (by omega)]
  · intro a ha hka
    let σ := T.scaleColumn n i j
    let c := σ.symm a
    let L := selectedIndices e
    have hca : σ c = a := σ.apply_symm_apply a
    have hc : c ∈ D.Z (r : ℤ) :=
      (T.scaleColumn_mem_cycles_iff hT n z hi hj r c).mp (hca.symm ▸ ha)
    have hcard : (L.card : ℤ) = r := by simp [L, selectedIndices]
    have hcM : c L ∈ M := by
      simpa only [hcard, if_true] using acx_mem_terms_iff.mp hc.1 L
    have hkc : K (c L) := hunit ((T.normalizationProduct n i j L)⁻¹) (a L) hka
    have hcb : c ∈ D.B (r : ℤ) :=
      boundary_of_selected_component e hw hM hK hc (htop (c L) hcM hkc)
    exact hca ▸ (T.scaleColumn_mem_boundaries_iff hT n z hi hj r c).mpr hcb

end GlobalTheory.WH.WeightedChartSystem
