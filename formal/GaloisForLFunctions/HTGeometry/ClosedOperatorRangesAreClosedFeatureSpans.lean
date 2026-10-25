import GaloisForLFunctions.HTGeometry.OneSidedFeatureGramIsometry

/-!
# Closed operator ranges are closed spans of image features

A continuous linear map sends a total feature family to a family spanning
the closure of its range. Nonzero uniform scaling preserves that span.
-/

noncomputable section
set_option autoImplicit false
open Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- A continuous linear image of a total family spans the closure of the whole range. -/
theorem closed_range_eq_closed_span_features
    {ι H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K) (v : ι → H)
    (hv : Dense ((Submodule.span ℂ (Set.range v) : Submodule ℂ H) : Set H)) :
    (LinearMap.range T.toLinearMap).topologicalClosure =
      (Submodule.span ℂ (Set.range fun i => T (v i))).topologicalClosure := by
  let S := Submodule.span ℂ (Set.range fun i => T (v i))
  have hspan : Submodule.span ℂ (Set.range v) ≤
      S.topologicalClosure.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact S.le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)
  have hclosed : IsClosed (S.topologicalClosure.comap T.toLinearMap : Set H) :=
    S.isClosed_topologicalClosure.preimage T.continuous
  have hall := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hspan hclosed
  rw [Submodule.dense_iff_topologicalClosure_eq_top.mp hv] at hall
  apply le_antisymm
  · apply (LinearMap.range T.toLinearMap).topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact hall (show x ∈ (⊤ : Submodule ℂ H) from trivial)
    · exact S.isClosed_topologicalClosure
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self T.toLinearMap (v i)

/-- Scaling every feature by one nonzero scalar leaves its algebraic span unchanged. -/
theorem span_scaled_features_eq
    {ι H : Type*} [AddCommGroup H] [Module ℂ H]
    (v : ι → H) {c : ℂ} (hc : c ≠ 0) :
    Submodule.span ℂ (Set.range fun i => c • v i) = Submodule.span ℂ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Submodule.span ℂ (Set.range v)).smul_mem c (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := (Submodule.span ℂ (Set.range fun j => c • v j)).smul_mem c⁻¹
      (Submodule.subset_span (show c • v i ∈ Set.range (fun j => c • v j) from ⟨i, rfl⟩))
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
    change v i ∈ Submodule.span ℂ (Set.range fun j => c • v j)
    exact h

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.closed_range_eq_closed_span_features
#print axioms GaloisForLFunctions.HTGeometry.span_scaled_features_eq
end
