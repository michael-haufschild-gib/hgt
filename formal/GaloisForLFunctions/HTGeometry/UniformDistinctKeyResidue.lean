import GaloisForLFunctions.HTGeometry.UniformJetPolyGroup

/-!
# A family whose data cannot tie

When the members of a family are separated by their `Γ`-exponent and their `log`-degree — as the
`ψ`-degree groups of a jet polynomial are, and as the `Γ`-powers of a presentation are — no two of
them can share a datum.  The dominant class is then a single member, and the residue of the sum is
that member's residue, which is nonzero.

This is what keeps the residue of a whole presentation nonzero: cancellation is possible only inside a
group, and each group is handled by the dichotomy as a whole.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The residue of a family separated by Gamma exponent and log degree.**  The dominant class is a
singleton, so the residue of the sum is a single nonzero constant. -/
theorem exists_tubeLimit_distinctKey_residue {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (F : ι → ℝ → ℝ → ℂ) (k : ι → ℤ) (p : ι → ℕ) (e : ι → ℤ)
    (c : ι → ℂ) (_hc : ∀ γ, c γ ≠ 0)
    (hsep : ∀ α β : ι, k α = k β → e α = e β → α = β)
    (hlim : ∀ γ, TubeLimit M
      (fun σ t => F γ σ t / gammaShapeZ σ (k γ) (-(p γ : ℤ)) (e γ) t) (c γ)) :
    ∃ β : ι, TubeLimit M
      (fun σ t => (∑ γ : ι, F γ σ t) / gammaShapeZ σ (k β) (-(p β : ℤ)) (e β) t) (c β) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shapeZ_index_fintype k (fun γ => -(p γ : ℤ)) e
  refine ⟨β, ?_⟩
  have hclass := tubeLimit_sum_div_dominant_class_fintype hM F k (fun γ => -(p γ : ℤ)) e c β
    hlim hβ
  -- the dominant class is the single index `β`
  have hfilter : (Finset.univ.filter
      (fun γ : ι => k γ = k β ∧ (-(p γ : ℤ)) = (-(p β : ℤ)) ∧ e γ = e β)) = {β} := by
    refine Finset.ext fun γ => ?_
    constructor
    · intro hγ
      obtain ⟨h1, -, h3⟩ := Finset.mem_filter.mp hγ |>.2
      exact Finset.mem_singleton.mpr (hsep γ β h1 h3)
    · intro hγ
      rw [Finset.mem_singleton] at hγ
      subst hγ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ γ, rfl, rfl, rfl⟩
  rw [hfilter, Finset.sum_singleton] at hclass
  exact hclass

/-- **The residue of a family of `ψ`-degree groups.**  Distinct log degrees separate the groups, so
the residue of their sum is the dominant group's residue. -/
theorem exists_tubeLimit_logSeparated_residue {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (F : ι → ℝ → ℝ → ℂ) (p : ι → ℕ) (e : ι → ℕ) (c : ι → ℂ)
    (hc : ∀ γ, c γ ≠ 0) (hinj : Function.Injective e)
    (hlim : ∀ γ, TubeLimit M
      (fun σ t => F γ σ t / gammaShapeZ σ 0 (-(p γ : ℤ)) ((e γ : ℤ)) t) (c γ)) :
    ∃ β : ι, TubeLimit M
      (fun σ t => (∑ γ : ι, F γ σ t) / gammaShapeZ σ 0 (-(p β : ℤ)) ((e β : ℤ)) t) (c β) := by
  refine exists_tubeLimit_distinctKey_residue hM F (fun _ => (0 : ℤ)) p (fun γ => (e γ : ℤ)) c hc
    (fun α β _ hE => hinj (by exact_mod_cast hE)) hlim

end

end GaloisForLFunctions.HTGeometry
