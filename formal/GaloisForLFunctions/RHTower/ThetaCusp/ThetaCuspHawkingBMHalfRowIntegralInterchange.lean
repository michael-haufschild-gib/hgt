import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-! Actual half-row norm-integral summability and the justified strip interchange. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
noncomputable section

/-- Strip admission supplies summability of the actual half-row integral norms. -/
theorem modularStrip_halfRow_norm_integrals_summable (F : UpperHalfPlane → ℂ)
    (hper : ∀ (n : ℤ) (z : UpperHalfPlane), F (T^n • z) = F z)
    (hi : IntegrableOn F modularStrip volume) :
    Summable (fun v : gammaSetHalf => ∫ z : UpperHalfPlane in fd, ‖F (gammaSetMatrix v.1 • z)‖) := by
  have hn := summable_fdUnfoldTerm
    (φ := fun z => ((‖F z‖:ℝ):ℂ)) (fun n z => by rw [hper]) hi.norm.ofReal
  have he : fdUnfoldTerm (fun z => ((‖F z‖:ℝ):ℂ)) =
      fun v => ((∫ z : UpperHalfPlane in fd, ‖F (gammaSetMatrix v • z)‖ : ℝ):ℂ) := by
    funext v
    rw [fdUnfoldTerm]
    exact integral_ofReal
  rw [he] at hn
  exact (Complex.summable_ofReal.mp hn).subtype (fun v => v ∈ gammaSetHalf)

/-- The complete admitted half-row sum unfolds with multiplicity one in the original measure. -/
theorem modularStrip_integral_halfRow_sum (F : UpperHalfPlane → ℂ)
    (hper : ∀ (n : ℤ) (z : UpperHalfPlane), F (T^n • z) = F z)
    (hi : IntegrableOn F modularStrip volume) :
    (∫ z : UpperHalfPlane in fd, ∑' v : gammaSetHalf, F (gammaSetMatrix v.1 • z)) =
      ∫ z : UpperHalfPlane in modularStrip, F z := by
  have he := integral_tsum_of_summable_integral_norm
    (fun v : gammaSetHalf => (integrableOn_smul_set_iff (gammaSetMatrix v.1) F fd).mp
      (integrableOn_smul_fd_of_periodic hper hi _))
    (modularStrip_halfRow_norm_integrals_summable F hper hi)
  rw [← he]
  change (∑' v : gammaSetHalf, fdUnfoldTerm F v.1) = _
  rw [(hasSum_fdUnfoldTerm_half hper hi).tsum_eq]
  exact isFundamentalDomain_iUnion_halfRep_smul_fd.setIntegral_eq isFundamentalDomain_modularStrip
    (translationSubgroup_invariant_of_periodic hper)

end
end RHTower.D4BMModularCore
