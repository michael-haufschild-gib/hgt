import GaloisForLFunctions.RHTower.DeningerNuclearProduct

/-!
# A finite-rank map is nuclear

A continuous linear map with finite-dimensional range corestricts to a map into that range, and a
basis of the range writes it as a finite sum of rank-one maps: the coordinate functionals composed
with the corestriction, against the basis vectors.  So a finite-rank map is nuclear.

This complements the case of a finite-dimensional source, where the basis is taken in the source
instead.

* `deningerIsNuclear_of_finiteRank` : a map with finite-dimensional range is nuclear.
* `deningerIsNuclearSpace_of_finiteRank` : a space with finite-rank comparison maps is nuclear.
-/

namespace RHTower

section FiniteRank

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A map with finite-dimensional range is nuclear.**  A basis of the range turns the
corestriction into a finite sum of rank-one maps. -/
theorem deningerIsNuclear_of_finiteRank (T : X →L[𝕜] Y)
    [FiniteDimensional 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y))] : DeningerIsNuclear T := by
  classical
  set V : Submodule 𝕜 Y := LinearMap.range (T : X →ₗ[𝕜] Y) with hV
  set T' : X →L[𝕜] V := T.codRestrict V (fun x => LinearMap.mem_range_self _ x) with hT'
  set n := Module.finrank 𝕜 V with hn
  set b := Module.finBasis 𝕜 V with hb
  refine ⟨Fin n, fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp T',
    fun i => ((b i : V) : Y), ?_, ?_⟩
  · exact (hasSum_fintype fun i =>
      ‖(LinearMap.toContinuousLinearMap (b.coord i)).comp T'‖ * ‖((b i : V) : Y)‖).summable
  · intro x
    have hx : ∑ i, b.coord i (T' x) • b i = T' x := by
      simp [Module.Basis.coord_apply]
    have hsum : HasSum (fun i => ((LinearMap.toContinuousLinearMap (b.coord i)).comp T') x
        • ((b i : V) : Y))
        (∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp T') x • ((b i : V) : Y)) :=
      hasSum_fintype _
    have hval : ∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp T') x
        • ((b i : V) : Y) = T x := by
      have hstep : ∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp T') x
          • ((b i : V) : Y)
          = ((∑ i, b.coord i (T' x) • b i : V) : Y) := by
        rw [Submodule.coe_sum]
        exact Finset.sum_congr rfl fun i _ => rfl
      rw [hstep, hx]
      rfl
    rwa [hval] at hsum

end FiniteRank

section NuclearSpaceCriterion

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- **A space whose comparison maps have finite rank is nuclear.**  This is the usable criterion:
one need not exhibit a nuclear representation, only a dominating seminorm whose comparison map has
finite-dimensional range. -/
theorem deningerIsNuclearSpace_of_finiteRank {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (h : ∀ i : ι, ∃ (j : ι) (C : ℝ) (hc : ∀ x, P i x ≤ C * P j x),
      FiniteDimensional 𝕜
        (LinearMap.range ((deningerSeminormComparison hc :
          DeningerSeminormSpace (P j) →L[𝕜] DeningerSeminormSpace (P i)) :
          DeningerSeminormSpace (P j) →ₗ[𝕜] DeningerSeminormSpace (P i)))) :
    DeningerIsNuclearSpace P := by
  intro i
  obtain ⟨j, C, hc, hfin⟩ := h i
  refine ⟨j, C, hc, ?_⟩
  haveI := hfin
  exact deningerIsNuclear_of_finiteRank _

end NuclearSpaceCriterion

end RHTower

