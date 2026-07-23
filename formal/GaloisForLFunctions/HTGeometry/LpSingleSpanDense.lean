import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Density of the coordinate span in `ℓ¹`

Every element of `lp E 1` is the convergent sum of its coordinate singles, so
the linear span of the coordinate vectors is dense.  This is the
coefficient-space half of joint-graph density statements: the weighted
critical coefficient space is an `ℓ¹` in the rescaled coordinates, and the
finite-support fields are exactly the coordinate span.
-/

noncomputable section

namespace HTGeometry

open scoped ENNReal

/-- **Coordinate span density in `ℓ¹`**: the span of the unit coordinate
vectors is dense in `lp (fun _ : α => ℝ) 1`. -/
theorem span_lp_single_dense (α : Type*) [DecidableEq α] :
    (Submodule.span ℝ (Set.range fun i : α =>
        lp.single (E := fun _ : α => ℝ) 1 i (1 : ℝ))).topologicalClosure
      = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  set p : Submodule ℝ (lp (fun _ : α => ℝ) 1) :=
    Submodule.span ℝ (Set.range fun i : α =>
      lp.single (E := fun _ : α => ℝ) 1 i (1 : ℝ)) with hp
  have hsum := lp.hasSum_single (E := fun _ : α => ℝ) (p := 1)
    (by norm_num) f
  have hmem : ∀ s : Finset α,
      (∑ i ∈ s, lp.single (E := fun _ : α => ℝ) 1 i ((f : ∀ _ : α, ℝ) i))
        ∈ p := by
    intro s
    apply Submodule.sum_mem
    intro i _
    have hsingle : lp.single (E := fun _ : α => ℝ) 1 i ((f : ∀ _ : α, ℝ) i)
        = ((f : ∀ _ : α, ℝ) i) • lp.single (E := fun _ : α => ℝ) 1 i (1:ℝ) := by
      rw [← lp.single_smul]
      congr 1
      simp
    rw [hsingle]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto hsum
    (Filter.Eventually.of_forall fun s => hmem s)

end HTGeometry
