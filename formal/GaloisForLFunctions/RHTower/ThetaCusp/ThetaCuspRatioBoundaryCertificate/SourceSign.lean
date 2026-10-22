import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.GlobalSign

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

theorem boundaryV77_ofReal (h s : ℝ) :
    ((9-boundaryR77 h s*h^2 : ℝ):ℂ)=nonlinearBoundaryV (h:ℂ) (s:ℂ) := by
  unfold nonlinearBoundaryV
  rw [←boundaryR77_ofReal]
  push_cast <;> rfl

theorem boundaryRegularCore77_reduced_source_re {h s : ℝ}
    (hh : h≠0) (hv : 9-boundaryR77 h s*h^2≠0) :
    (((6:ℝ)^24*24^9)⁻¹*h^16)*
        (eval (basePoint (nonlinearBoundaryV (h:ℂ) (s:ℂ)) (h:ℂ)⁻¹
          (nonlinearBoundaryZ (h:ℂ) (s:ℂ))) reducedSlope).re=
      boundaryRegularCore77 h s := by
  have hhC : (h:ℂ)≠0 := by exact_mod_cast hh
  have hvC : nonlinearBoundaryV (h:ℂ) (s:ℂ)≠0 := by
    rw [←boundaryV77_ofReal]
    exact_mod_cast hv
  have he := boundaryRegularCore76_source hhC (s:ℂ) 0 hvC
  rw [reducedNonlinearBoundaryCore_source hhC,←boundaryRegularCore77_ofReal,
    ←mul_assoc] at he
  have hc : (((((6:ℝ)^24*24^9)⁻¹*h^16 : ℝ):ℂ))=
      ((6:ℂ)^24*24^9)⁻¹*(h:ℂ)^16 := by
    push_cast <;> rfl
  rw [←hc] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_ofReal_mul,Complex.ofReal_re] using hr

theorem boundaryReducedSlope77_pos {h s : ℝ}
    (hh0 : 0<h) (hh1 : h≤4/5) (hs0 : 0≤s) (hs1 : s≤(6/5)*(361/25))
    (hv : 0<9-boundaryR77 h s*h^2) :
    0<(eval (basePoint (nonlinearBoundaryV (h:ℂ) (s:ℂ)) (h:ℂ)⁻¹
      (nonlinearBoundaryZ (h:ℂ) (s:ℂ))) reducedSlope).re := by
  have hg := boundaryRegularCore77_global_pos hh0.le
    (by simpa only [boundaryH77] using hh1) hs0
    (by simpa only [boundaryS77] using hs1)
  have he := boundaryRegularCore77_reduced_source_re hh0.ne' hv.ne'
  have ha : 0<((6:ℝ)^24*24^9)⁻¹*h^16 := by positivity
  by_contra hn
  have hm := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
  rw [he] at hm
  linarith only [hg,hm]

theorem boundarySlope77_pos {h s : ℝ}
    (hh0 : 0<h) (hh1 : h≤4/5) (hs0 : 0≤s) (hs1 : s≤(6/5)*(361/25))
    (hv : 0<9-boundaryR77 h s*h^2) :
    0<(eval (basePoint (nonlinearBoundaryV (h:ℂ) (s:ℂ)) (h:ℂ)⁻¹
      (nonlinearBoundaryZ (h:ℂ) (s:ℂ))) ThetaRatioSquare.slope).re := by
  have hp := boundaryReducedSlope77_pos hh0 hh1 hs0 hs1 hv
  rw [slope_seam_factor]
  simp only [map_mul,eval_X,basePoint]
  rw [←boundaryV77_ofReal,Complex.re_ofReal_mul]
  rw [←boundaryV77_ofReal] at hp
  exact mul_pos hv hp

theorem nonlinearBoundary_physical_source_slope_pos {h r t : ℝ}
    (hh0 : 0<h) (hh1 : h≤4/5) (hr0 : 0<r) (hr1 : r≤361/25)
    (hv : 0<9-r*h^2) (ht : 0<t) (hht : h*t<1)
    (he : t-h^2*t^2=r*ThetaCriticalBarrier.b h) :
    0<(eval (sourcePoint (h:ℂ) (r:ℂ) (t:ℂ)) ThetaRatioSquare.slope).re := by
  obtain ⟨s,hs0,hs1,hts,hrs⟩ :=
    nonlinearBoundary_parameter_coverage hh0 hh1 hr0 hr1 hv ht hht he
  have hrR : boundaryR77 h s=r := by
    simpa only [boundaryR77,ThetaCriticalBarrier.b] using hrs.symm
  have hrC : nonlinearBoundaryR (h:ℂ) (s:ℂ)=(r:ℂ) := by
    rw [←boundaryR77_ofReal,hrR]
  have htC : nonlinearBoundaryT (h:ℂ) (s:ℂ)=(t:ℂ) := by
    have htR : (1/12-7*h/72)*s=t := by
      simpa only [ThetaCriticalBarrier.b] using hts.symm
    unfold nonlinearBoundaryT nonlinearBoundarySeed
    have hc := congrArg (fun x : ℝ => (x : ℂ)) htR
    push_cast at hc
    exact hc
  have hp := boundarySlope77_pos hh0 hh1 hs0.le hs1.le
    (by rw [hrR]; exact hv)
  rw [←nonlinearBoundary_sourcePoint,hrC,htC] at hp
  exact hp

end
end HTGeometry.ThetaRatioInfinity
