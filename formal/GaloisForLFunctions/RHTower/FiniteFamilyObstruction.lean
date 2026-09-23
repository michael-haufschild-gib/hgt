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

/-! ## Strictness of the single-generator Cauchy--Schwarz bound -/

/-- **The one-generator lower bound is always strict.**  Equality would put the target exactly on
the generator's line, contradicting the positive distance to every finite Báez--Duarte span. -/
theorem norm_bdGen_lower_strict_of_lt_one {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    θ * |Real.log θ| < ‖bdGen θ‖ := by
  refine lt_of_le_of_ne (norm_bdGen_lower hθ0 hθ1.le) ?_
  intro heq
  obtain ⟨c, hc⟩ := exists_norm_sq_sub_smul_bdGen hθ0 hθ1
  have hsq : (θ * Real.log θ) ^ (2 : ℕ) = ‖bdGen θ‖ ^ (2 : ℕ) := by
    calc
      (θ * Real.log θ) ^ (2 : ℕ) = (θ * |Real.log θ|) ^ (2 : ℕ) := by
        rw [mul_pow, mul_pow, sq_abs]
      _ = ‖bdGen θ‖ ^ (2 : ℕ) := congrArg (fun x : ℝ => x ^ (2 : ℕ)) heq
  have hnpos : (0 : ℝ) < ‖bdGen θ‖ := norm_pos_iff.mpr (bdGen_ne_zero hθ0 hθ1)
  rw [hsq, div_self (by positivity : ‖bdGen θ‖ ^ (2 : ℕ) ≠ 0), sub_self] at hc
  have hzero : bdTarget - c • bdGen θ = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (bdTarget - c • bdGen θ), hc]
  let η : Unit → ℝ := fun _ => θ
  have hdistPos : 0 < bdDist η :=
    bdDist_pos_of_finite η (fun _ => ⟨hθ0, hθ1.le⟩)
  have hmem : c • bdGen θ ∈ bdSpanSet η := by
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨(), rfl⟩)
  have hle := Metric.infDist_le_dist_of_mem (x := bdTarget) hmem
  have hdist : dist bdTarget (c • bdGen θ) = 0 := by
    rw [dist_eq_norm, hzero, norm_zero]
  rw [hdist] at hle
  exact (not_lt_of_ge hle hdistPos).elim

/-- Strict Gram-diagonal form of `norm_bdGen_lower_strict_of_lt_one`. -/
theorem sq_lt_bdGram_self_of_lt_one {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (θ * Real.log θ) ^ (2 : ℕ) < bdGram θ θ := by
  rw [bdGram_self]
  have h := norm_bdGen_lower_strict_of_lt_one hθ0 hθ1
  have hnonneg : 0 ≤ θ * |Real.log θ| := by positivity
  have hnorm : 0 ≤ ‖bdGen θ‖ := norm_nonneg _
  have hsq := (sq_lt_sq₀ hnonneg hnorm).2 h
  simpa [mul_pow, sq_abs] using hsq

end RHTower

end
