import GaloisForLFunctions.RHTower.MuentzZetaRelationImpossible

/-!
# Every finite family of dilations is obstructed

`MuentzZetaRelationImpossible` proves a positive Báez-Duarte distance for finite families of *distinct*
dilations in `(0,1)`.  Both restrictions are cosmetic: repeated dilations contribute the same generator, and
`θ = 1` contributes the zero vector (`bdGen_one`), so passing to the distinct values below `1` does not
change the span.

* `bdGenFun_one`, `bdGen_one` — the generator at `θ = 1` vanishes;
* `bdDist_mono_span` — nested spans compare the distances (the span form of `bdDist_mono`);
* **`bdDist_pos_of_finite` — every finite family of dilations in `(0,1]` has positive Báez-Duarte distance**,
  with no injectivity hypothesis and no exclusion of `1`;
* `bdDistFinset_pos` — hence every finite section of an arbitrary family of dilations is obstructed.

The second statement subsumes the corpus's earlier positivity results: `bdDistDiscrete_pos`, proved from the
factorial floor of `DistancePositivity`, is the case `θ = 1/(n+1)` — including the index `θ = 1` that the
structural theorem excludes.
-/

open MeasureTheory Set Complex Metric

noncomputable section

namespace RHTower

/-- At `θ = 1` the generator function vanishes identically: `{u} − 1·{u} = 0`. -/
theorem bdGenFun_one : bdGenFun 1 = (0 : ℝ → ℂ) := by
  funext u
  rw [bdGenFun]
  simp

/-- **The generator at `θ = 1` is the zero vector.** -/
theorem bdGen_one : bdGen (1 : ℝ) = 0 := by
  refine MeasureTheory.Lp.ext ?_
  calc (bdGen (1 : ℝ) : ℝ → ℂ)
      =ᵐ[bdMeasure] bdGenFun 1 := (memLp_bdGenFun 1).coeFn_toLp
    _ =ᵐ[bdMeasure] (0 : ℝ → ℂ) := Filter.EventuallyEq.of_eq bdGenFun_one
    _ =ᵐ[bdMeasure] ((0 : BDCarrier) : ℝ → ℂ) :=
        (MeasureTheory.Lp.coeFn_zero ℂ 2 bdMeasure).symm

/-- Nested spans compare the Báez-Duarte distances. -/
theorem bdDist_mono_span {I J : Type*} (θ : I → ℝ) (η : J → ℝ)
    (h : Submodule.span ℂ (Set.range fun i : I => bdGen (θ i))
        ≤ Submodule.span ℂ (Set.range fun j : J => bdGen (η j))) :
    bdDist η ≤ bdDist θ :=
  Metric.infDist_le_infDist_of_subset h (bdSpanSet_nonempty θ)

/-- **Every finite family of dilations in `(0,1]` is obstructed.**  Repetitions and the value `1` are
harmless: the span is that of the distinct values below `1`, to which the structural theorem applies. -/
theorem bdDist_pos_of_finite {I : Type*} [Fintype I] (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) :
    0 < bdDist θ := by
  classical
  set S : Finset ℝ := (Finset.univ.image θ).erase 1 with hS
  set η : Fin S.card → ℝ := fun k => ((S.equivFin.symm k : {x // x ∈ S}) : ℝ) with hη
  have hηmem : ∀ k, η k ∈ S := fun k => (S.equivFin.symm k).2
  have hηspec : ∀ k, η k ≠ 1 ∧ ∃ i, θ i = η k := by
    intro k
    have hm := hηmem k
    rw [hS, Finset.mem_erase, Finset.mem_image] at hm
    obtain ⟨hne, i, -, hi⟩ := hm
    exact ⟨hne, ⟨i, hi⟩⟩
  have hη0 : ∀ k, 0 < η k := by
    intro k
    obtain ⟨-, i, hi⟩ := hηspec k
    rw [← hi]
    exact (hθ i).1
  have hη1 : ∀ k, η k < 1 := by
    intro k
    obtain ⟨hne, i, hi⟩ := hηspec k
    have hle : η k ≤ 1 := by rw [← hi]; exact (hθ i).2
    exact lt_of_le_of_ne hle hne
  have hηinj : Function.Injective η := by
    intro a b hab
    exact S.equivFin.symm.injective (Subtype.coe_injective hab)
  have hspan : Submodule.span ℂ (Set.range fun i : I => bdGen (θ i))
      ≤ Submodule.span ℂ (Set.range fun k : Fin S.card => bdGen (η k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show bdGen (θ i) ∈ (Submodule.span ℂ (Set.range fun k : Fin S.card => bdGen (η k)) :
      Set BDCarrier)
    by_cases hone : θ i = 1
    · rw [hone, bdGen_one]
      exact Submodule.zero_mem _
    · have hmem : θ i ∈ S := by
        rw [hS, Finset.mem_erase]
        exact ⟨hone, Finset.mem_image_of_mem θ (Finset.mem_univ i)⟩
      refine Submodule.subset_span ⟨S.equivFin ⟨θ i, hmem⟩, ?_⟩
      show bdGen (η (S.equivFin ⟨θ i, hmem⟩)) = bdGen (θ i)
      have hval : η (S.equivFin ⟨θ i, hmem⟩) = θ i := by
        rw [hη]
        simp
      rw [hval]
  exact lt_of_lt_of_le (bdDist_pos_of_injective_of_lt_one η hη0 hη1 hηinj)
    (bdDist_mono_span θ η hspan)

/-- Every finite section of an arbitrary family of dilations in `(0,1]` is obstructed. -/
theorem bdDistFinset_pos {I : Type*} [DecidableEq I] (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (s : Finset I) :
    0 < bdDistFinset θ s :=
  bdDist_pos_of_finite (fun i : {x // x ∈ s} => θ i) fun i => hθ i.1

end RHTower

end
