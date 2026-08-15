import GaloisForLFunctions.HTGeometry.OrbitBaireCountable

/-!
# A generic source also has full Taylor support

Having a nonzero coefficient at a prescribed degree is an open dense condition on the coefficient
box: the coordinate projection is continuous, and a neighbourhood of any point of a ball of positive
radius contains a nonzero point.  Adding those countably many conditions to the genericity
intersection produces one source family that is simultaneously good for every finite jet-monomial
family and has every Taylor coefficient nonzero — which is what the Stanley--Reisner annihilator
argument needs of the same source.
-/

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A neighbourhood of a point of a complex ball of positive radius contains a nonzero point. -/
theorem exists_ne_zero_mem_of_nhds {r : ℝ} (hr : 0 < r)
    {v₀ : Metric.closedBall (0 : ℂ) r} {V : Set (Metric.closedBall (0 : ℂ) r)}
    (hV : V ∈ nhds v₀) : ∃ v ∈ V, (v : ℂ) ≠ 0 := by
  classical
  by_cases hv₀ : (v₀ : ℂ) ≠ 0
  · exact ⟨v₀, mem_of_mem_nhds hV, hv₀⟩
  · push Not at hv₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨⟨((min ε r / 2 : ℝ) : ℂ), ?_⟩, hball ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have h1 : min ε r ≤ r := min_le_right _ _
      linarith
    · rw [Metric.mem_ball, Subtype.dist_eq, hv₀, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have h1 : min ε r ≤ ε := min_le_left _ _
      linarith
    · intro hzero
      have hval : ((min ε r / 2 : ℝ) : ℂ) = 0 := hzero
      have : (min ε r / 2 : ℝ) = 0 := by exact_mod_cast hval
      have h2 : 0 < min ε r := lt_min hε hr
      linarith

variable {L : ℕ} {ι : Type} [Countable ι] [DecidableEq ι]

/-- Having a nonzero coefficient at a prescribed degree is an open condition. -/
theorem isOpen_boxSeq_ne_zero (j : Fin L) (n : ℕ) :
    IsOpen {C : Fin L → sourceBox | boxSeq (C j) n ≠ 0} := by
  have hcont : Continuous fun C : Fin L → sourceBox => boxSeq (C j) n :=
    (continuous_boxSeq n).comp (continuous_apply j)
  exact hcont.isOpen_preimage _ isOpen_compl_singleton

/-- Having a nonzero coefficient at a prescribed degree is a dense condition. -/
theorem dense_boxSeq_ne_zero (j : Fin L) (n : ℕ) :
    Dense {C : Fin L → sourceBox | boxSeq (C j) n ≠ 0} := by
  classical
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨C₀, hC₀⟩ := hUne
  have hcont : Continuous fun v : Metric.closedBall (0 : ℂ) (((n.factorial : ℝ))⁻¹) =>
      (Function.update C₀ j (Function.update (C₀ j) n v) : Fin L → sourceBox) := by
    refine continuous_pi fun k => ?_
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self]
      refine continuous_pi fun m => ?_
      by_cases hm : m = n
      · subst hm
        simpa using continuous_id'
      · simpa [Function.update_of_ne hm] using continuous_const
    · simpa [Function.update_of_ne hk] using continuous_const
  have hmem : (Function.update C₀ j (Function.update (C₀ j) n (C₀ j n)) : Fin L → sourceBox)
      = C₀ := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self]
      funext m
      by_cases hm : m = n
      · subst hm; simp
      · simp [Function.update_of_ne hm]
    · simp [Function.update_of_ne hk]
  have hpre : (fun v => (Function.update C₀ j (Function.update (C₀ j) n v) :
      Fin L → sourceBox)) ⁻¹' U ∈ nhds (C₀ j n) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [hmem]
    exact hUopen.mem_nhds hC₀
  obtain ⟨v, hvU, hvne⟩ := exists_ne_zero_mem_of_nhds
    (r := ((n.factorial : ℝ))⁻¹) (by positivity) hpre
  refine ⟨Function.update C₀ j (Function.update (C₀ j) n v), hvU, ?_⟩
  show boxSeq ((Function.update C₀ j (Function.update (C₀ j) n v)) j) n ≠ 0
  rw [Function.update_self, boxSeq, Function.update_self]
  exact hvne

/-- **One source family that is generic and has full Taylor support.** -/
theorem exists_source_orbGood_all_fullSupport [Nonempty ι]
    (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0) (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i')) :
    ∃ C : Fin L → sourceBox, (∀ (j : Fin L) (n : ℕ), boxSeq (C j) n ≠ 0) ∧
      JointlyHypertranscendental (orbFun lam src sh C) := by
  classical
  have hdistA : ∀ A : Finset ι, ∀ i i' : ↥A,
      src (i : ι) = src (i' : ι) → i ≠ i' →
        Complex.exp (sh (i : ι)) ≠ Complex.exp (sh (i' : ι)) := by
    intro A i i' hsrc hne
    exact hdist (i : ι) (i' : ι) hsrc fun h => hne (Subtype.ext h)
  set G : orbTaskCountable ι ⊕ (Fin L × ℕ) → Set (Fin L → sourceBox) := fun τ =>
    match τ with
    | Sum.inl σ =>
        if Function.Injective σ.2.2 then
          orbGood lam (fun i : ↥σ.1 => src (i : ι)) (fun i : ↥σ.1 => sh (i : ι)) σ.2.2
        else Set.univ
    | Sum.inr p => {C : Fin L → sourceBox | boxSeq (C p.1) p.2 ≠ 0}
    with hG
  have hGopen : ∀ τ, IsOpen (G τ) := by
    intro τ
    rw [hG]
    cases τ with
    | inl σ =>
        by_cases h : Function.Injective σ.2.2
        · simpa only [if_pos h] using isOpen_orbGood lam _ _ σ.2.2
        · simpa only [if_neg h] using isOpen_univ
    | inr p => exact isOpen_boxSeq_ne_zero p.1 p.2
  have hGdense : ∀ τ, Dense (G τ) := by
    intro τ
    rw [hG]
    cases τ with
    | inl σ =>
        by_cases h : Function.Injective σ.2.2
        · simpa only [if_pos h] using dense_orbGood lam hlam _ _ (hdistA σ.1) σ.2.2 h
        · simpa only [if_neg h] using dense_univ
    | inr p => exact dense_boxSeq_ne_zero p.1 p.2
  obtain ⟨C, hC⟩ := (dense_iInter_of_isOpen hGopen hGdense).nonempty
  refine ⟨C, ?_, ?_⟩
  · intro j n
    have hmem := Set.mem_iInter.mp hC (Sum.inr (j, n))
    rw [hG] at hmem
    exact hmem
  · refine jointlyHypertranscendental_of_finite_restrictions _ fun S hS => ?_
    have hres : (fun i : ↥S => orbFun lam src sh C (i : ι))
        = orbFun lam (fun i : ↥S => src (i : ι)) (fun i : ↥S => sh (i : ι)) C := rfl
    rw [hres]
    refine jointlyHypertranscendental_of_orbGood_all _ _ _ C ?_
    intro n K M hM
    have hmem := Set.mem_iInter.mp hC (Sum.inl (⟨S, (n, K), M⟩ : orbTaskCountable ι))
    rw [hG] at hmem
    simpa only [if_pos hM] using hmem

end

end GaloisForLFunctions.HTGeometry
