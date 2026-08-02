import GaloisForLFunctions.HTGeometry.UniformShapeDominance

/-!
# The dominant residue of a finite sum, uniformly on a vertical tube

A finite sum of quantities, each with a residue against its own boundary shape, has the residue of its
dominant member against that member's shape: every other term picks up a strictly subordinate shape
ratio, which vanishes uniformly.

With the tube-limit calculus this is the same three lines as on a fixed line — the sum of tube limits,
the product of tube limits, and the dominance ratio — and it is the assembly step of the tube form of
eq. (19)/(3).
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Tube limits sum over a finite set. -/
theorem TubeLimit.finsetSum {M : ℝ} {ι : Type*} [DecidableEq ι] {f : ι → ℝ → ℝ → ℂ} {c : ι → ℂ}
    (s : Finset ι) (h : ∀ α ∈ s, TubeLimit M (f α) (c α)) :
    TubeLimit M (fun σ t => ∑ α ∈ s, f α σ t) (∑ α ∈ s, c α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨0, fun σ t hσ hσM ht => ?_⟩
      simp only [Finset.sum_empty, sub_zero, norm_zero]
      exact le_of_lt hε
  | insert α s hα ih =>
      rw [Finset.sum_insert hα]
      have hstep := (h α (Finset.mem_insert_self α s)).add
        (ih fun γ hγ => h γ (Finset.mem_insert_of_mem hγ))
      refine hstep.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
      rw [Finset.sum_insert hα]

/-- Tube limits sum over a finite index type. -/
theorem TubeLimit.sum {M : ℝ} {N : ℕ} {f : Fin N → ℝ → ℝ → ℂ} {c : Fin N → ℂ}
    (h : ∀ α, TubeLimit M (f α) (c α)) :
    TubeLimit M (fun σ t => ∑ α : Fin N, f α σ t) (∑ α : Fin N, c α) :=
  TubeLimit.finsetSum Finset.univ fun α _ => h α

/-- The boundary shape is nonzero beyond a fixed height. -/
theorem gammaShapeZ_ne_zero_of_le {σ t : ℝ} (hσ : 0 < σ) (ht : 3 ≤ t) (k a b : ℤ) :
    gammaShapeZ σ k a b t ≠ 0 := by
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h0] at him
    simp only [Complex.zero_im] at him
    linarith
  have hL : vertLog t ≠ 0 := by
    intro h0
    have hre : (vertLog t).re = Real.log t := by
      rw [vertLog]
      simp
    rw [h0] at hre
    simp only [Complex.zero_re] at hre
    have hlog1 : (1 : ℝ) ≤ Real.log t := by
      have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  rw [gammaShapeZ]
  exact mul_ne_zero (zpow_ne_zero _ hΓ) (mul_ne_zero (zpow_ne_zero _ hs) (zpow_ne_zero _ hL))

/-- **The residue of a finite sum against the dominant shape, uniformly on a tube.** -/
theorem tubeLimit_sum_div_dominant {M : ℝ} (hM : 0 < M) {N : ℕ} (F : Fin N → ℝ → ℝ → ℂ)
    (k a b : Fin N → ℤ) (c : Fin N → ℂ) (β : Fin N)
    (hlim : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShapeZ σ (k α) (a α) (b α) t) (c α))
    (hdom : ∀ α, α ≠ β →
      (k β < k α ∨ (k α = k β ∧ a α < a β) ∨ (k α = k β ∧ a α = a β ∧ b α < b β))) :
    TubeLimit M (fun σ t => (∑ α : Fin N, F α σ t)
      / gammaShapeZ σ (k β) (a β) (b β) t) (c β) := by
  classical
  -- each term against the dominant shape
  have hterm : ∀ α : Fin N, TubeLimit M
      (fun σ t => F α σ t / gammaShapeZ σ (k β) (a β) (b β) t)
      (if α = β then c β else 0) := by
    intro α
    by_cases hαβ : α = β
    · subst hαβ
      rw [if_pos rfl]
      exact hlim α
    · rw [if_neg hαβ]
      have hmul := (hlim α).mul (tubeLimit_gammaShapeZ_ratio_zero hM (hdom α hαβ))
      rw [mul_zero] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hSα : gammaShapeZ σ (k α) (a α) (b α) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      have hSβ : gammaShapeZ σ (k β) (a β) (b β) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      field_simp
  -- sum them
  have hsum := TubeLimit.sum hterm
  rw [Finset.sum_ite_eq' Finset.univ β (fun _ => c β), if_pos (Finset.mem_univ β)] at hsum
  refine hsum.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  rw [Finset.sum_div]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The dominant class residue of a finite sum, uniformly on a tube.**  Members sharing the
dominant datum keep their residues; every other member vanishes. -/
theorem tubeLimit_sum_div_dominant_class {M : ℝ} (hM : 0 < M) {N : ℕ} (F : Fin N → ℝ → ℝ → ℂ)
    (k a b : Fin N → ℤ) (c : Fin N → ℂ) (β : Fin N)
    (hlim : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShapeZ σ (k α) (a α) (b α) t) (c α))
    (hdom : ∀ α, (k α = k β ∧ a α = a β ∧ b α = b β)
      ∨ (k β < k α ∨ (k α = k β ∧ a α < a β) ∨ (k α = k β ∧ a α = a β ∧ b α < b β))) :
    TubeLimit M (fun σ t => (∑ α : Fin N, F α σ t) / gammaShapeZ σ (k β) (a β) (b β) t)
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => k α = k β ∧ a α = a β ∧ b α = b β), c α) := by
  classical
  have hterm : ∀ α : Fin N, TubeLimit M
      (fun σ t => F α σ t / gammaShapeZ σ (k β) (a β) (b β) t)
      (if (k α = k β ∧ a α = a β ∧ b α = b β) then c α else 0) := by
    intro α
    by_cases htie : k α = k β ∧ a α = a β ∧ b α = b β
    · rw [if_pos htie]
      obtain ⟨h1, h2, h3⟩ := htie
      have hshape : ∀ σ t : ℝ, gammaShapeZ σ (k α) (a α) (b α) t
          = gammaShapeZ σ (k β) (a β) (b β) t := by
        intro σ t
        rw [h1, h2, h3]
      refine (hlim α).congr (T₀ := 0) fun σ t hσ hσM ht => ?_
      rw [hshape σ t]
    · rw [if_neg htie]
      have hsub : k β < k α ∨ (k α = k β ∧ a α < a β)
          ∨ (k α = k β ∧ a α = a β ∧ b α < b β) := (hdom α).resolve_left htie
      have hmul := (hlim α).mul (tubeLimit_gammaShapeZ_ratio_zero hM hsub)
      rw [mul_zero] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hSα : gammaShapeZ σ (k α) (a α) (b α) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      have hSβ : gammaShapeZ σ (k β) (a β) (b β) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      field_simp
  have hsum := TubeLimit.sum hterm
  rw [← Finset.sum_filter] at hsum
  refine hsum.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  rw [Finset.sum_div]

/-- **The residue of a finite family of data, uniformly on a tube.**  A nonempty family always has a
dominant datum, and the sum has the residue of that class. -/
theorem exists_tubeLimit_dominant_class {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℝ → ℂ) (k a b : Fin N → ℤ) (c : Fin N → ℂ)
    (hlim : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShapeZ σ (k α) (a α) (b α) t) (c α)) :
    ∃ β : Fin N, TubeLimit M
      (fun σ t => (∑ α : Fin N, F α σ t) / gammaShapeZ σ (k β) (a β) (b β) t)
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => k α = k β ∧ a α = a β ∧ b α = b β), c α) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shapeZ_index hN k a b
  exact ⟨β, tubeLimit_sum_div_dominant_class hM F k a b c β hlim hβ⟩

end

end GaloisForLFunctions.HTGeometry
