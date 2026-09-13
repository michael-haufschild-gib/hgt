import GaloisForLFunctions.HTGeometry.Arxiv2608CausalitySumRules
import GaloisForLFunctions.HTGeometry.FokasLenellsRawScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsRegularizedData
import GaloisForLFunctions.HTGeometry.FokasLenellsContourScattering
import GaloisForLFunctions.HTGeometry.HLSScattering

/-!
# Applications of arXiv:2608.10427 across the scattering corpus

The paper's domain-delay algebra is instantiated here for every independent concrete
finite scattering matrix currently exposed by the HTGeometry corpus.  Each theorem is
closed and unconditional.  In particular, all five Fokas--Lenells constructions have
determinant one before correction, so their corrected determinants are exactly the
product of channel phases and retain unit modulus.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FokasLenells

theorem scatteringMatrix_domainDelay_powerBalance
    (q : SchwartzMap ℝ ℂ) (κ omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau (scatteringMatrix q κ))ᴴ *
        causalityDomainDelayedScattering omega tau (scatteringMatrix q κ) =
      (scatteringMatrix q κ)ᴴ * scatteringMatrix q κ :=
  causalityDomainDelayedScattering_powerBalance _ _ _

theorem scatteringMatrix_domainDelay_det
    (q : SchwartzMap ℝ ℂ) (κ omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau (scatteringMatrix q κ)).det =
      ∏ i, causalityDomainDelayPhase omega (tau i) := by
  rw [det_causalityDomainDelayedScattering, scatteringMatrix_det, mul_one]

theorem scatteringMatrix_domainDelay_det_norm
    (q : SchwartzMap ℝ ℂ) (κ omega : ℝ) (tau : Fin 2 → ℝ) :
    ‖(causalityDomainDelayedScattering omega tau (scatteringMatrix q κ)).det‖ = 1 := by
  rw [norm_det_causalityDomainDelayedScattering, scatteringMatrix_det, norm_one]

theorem scatteringMatrix_commonDelay_coherentReturn_norm
    (q : SchwartzMap ℝ ℂ) (κ omega tau : ℝ) (v : Fin 2 → ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau) (scatteringMatrix q κ))‖ =
      ‖causalityCoherentReturn v (scatteringMatrix q κ)‖ :=
  norm_causalityCoherentReturn_domainDelayed_const _ _ _ _

theorem rawScatteringMatrix_domainDelay_powerBalance
    (q : SchwartzMap ℝ ℂ) (k omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau (rawScatteringMatrix q k))ᴴ *
        causalityDomainDelayedScattering omega tau (rawScatteringMatrix q k) =
      (rawScatteringMatrix q k)ᴴ * rawScatteringMatrix q k :=
  causalityDomainDelayedScattering_powerBalance _ _ _

theorem rawScatteringMatrix_domainDelay_det
    (q : SchwartzMap ℝ ℂ) (k omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau (rawScatteringMatrix q k)).det =
      ∏ i, causalityDomainDelayPhase omega (tau i) := by
  rw [det_causalityDomainDelayedScattering, rawScatteringMatrix_det, mul_one]

theorem rawScatteringMatrix_domainDelay_det_norm
    (q : SchwartzMap ℝ ℂ) (k omega : ℝ) (tau : Fin 2 → ℝ) :
    ‖(causalityDomainDelayedScattering omega tau (rawScatteringMatrix q k)).det‖ = 1 := by
  rw [norm_det_causalityDomainDelayedScattering, rawScatteringMatrix_det, norm_one]

theorem rawScatteringMatrix_commonDelay_coherentReturn_norm
    (q : SchwartzMap ℝ ℂ) (k omega tau : ℝ) (v : Fin 2 → ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau) (rawScatteringMatrix q k))‖ =
      ‖causalityCoherentReturn v (rawScatteringMatrix q k)‖ :=
  norm_causalityCoherentReturn_domainDelayed_const _ _ _ _

theorem regularScatteringMatrix_domainDelay_powerBalance
    (q : SchwartzMap ℝ ℂ) (z omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau (regularScatteringMatrix q z))ᴴ *
        causalityDomainDelayedScattering omega tau (regularScatteringMatrix q z) =
      (regularScatteringMatrix q z)ᴴ * regularScatteringMatrix q z :=
  causalityDomainDelayedScattering_powerBalance _ _ _

theorem regularScatteringMatrix_domainDelay_det
    (q : SchwartzMap ℝ ℂ) (z omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau (regularScatteringMatrix q z)).det =
      ∏ i, causalityDomainDelayPhase omega (tau i) := by
  rw [det_causalityDomainDelayedScattering, regularScatteringMatrix_det, mul_one]

theorem regularScatteringMatrix_domainDelay_det_norm
    (q : SchwartzMap ℝ ℂ) (z omega : ℝ) (tau : Fin 2 → ℝ) :
    ‖(causalityDomainDelayedScattering omega tau (regularScatteringMatrix q z)).det‖ = 1 := by
  rw [norm_det_causalityDomainDelayedScattering, regularScatteringMatrix_det, norm_one]

theorem regularScatteringMatrix_commonDelay_coherentReturn_norm
    (q : SchwartzMap ℝ ℂ) (z omega tau : ℝ) (v : Fin 2 → ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau) (regularScatteringMatrix q z))‖ =
      ‖causalityCoherentReturn v (regularScatteringMatrix q z)‖ :=
  norm_causalityCoherentReturn_domainDelayed_const _ _ _ _

theorem contourScatteringMatrix_domainDelay_powerBalance
    (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ omega : ℝ)
    (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau
        (contourScatteringMatrix q vertical negative κ))ᴴ *
        causalityDomainDelayedScattering omega tau
          (contourScatteringMatrix q vertical negative κ) =
      (contourScatteringMatrix q vertical negative κ)ᴴ *
        contourScatteringMatrix q vertical negative κ :=
  causalityDomainDelayedScattering_powerBalance _ _ _

theorem contourScatteringMatrix_domainDelay_det
    (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ omega : ℝ)
    (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau
        (contourScatteringMatrix q vertical negative κ)).det =
      ∏ i, causalityDomainDelayPhase omega (tau i) := by
  rw [det_causalityDomainDelayedScattering, contourScatteringMatrix_det, mul_one]

theorem contourScatteringMatrix_domainDelay_det_norm
    (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ omega : ℝ)
    (tau : Fin 2 → ℝ) :
    ‖(causalityDomainDelayedScattering omega tau
        (contourScatteringMatrix q vertical negative κ)).det‖ = 1 := by
  rw [norm_det_causalityDomainDelayedScattering, contourScatteringMatrix_det, norm_one]

theorem contourScatteringMatrix_commonDelay_coherentReturn_norm
    (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ omega tau : ℝ)
    (v : Fin 2 → ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau)
          (contourScatteringMatrix q vertical negative κ))‖ =
      ‖causalityCoherentReturn v (contourScatteringMatrix q vertical negative κ)‖ :=
  norm_causalityCoherentReturn_domainDelayed_const _ _ _ _

theorem uniformizedScatteringMatrix_domainDelay_powerBalance
    (f g h : SchwartzMap ℝ ℂ) (z omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau
        (uniformizedScatteringMatrix f g h z))ᴴ *
        causalityDomainDelayedScattering omega tau
          (uniformizedScatteringMatrix f g h z) =
      (uniformizedScatteringMatrix f g h z)ᴴ * uniformizedScatteringMatrix f g h z :=
  causalityDomainDelayedScattering_powerBalance _ _ _

theorem uniformizedScatteringMatrix_domainDelay_det
    (f g h : SchwartzMap ℝ ℂ) (z omega : ℝ) (tau : Fin 2 → ℝ) :
    (causalityDomainDelayedScattering omega tau
        (uniformizedScatteringMatrix f g h z)).det =
      ∏ i, causalityDomainDelayPhase omega (tau i) := by
  rw [det_causalityDomainDelayedScattering, uniformizedScatteringMatrix_det, mul_one]

theorem uniformizedScatteringMatrix_domainDelay_det_norm
    (f g h : SchwartzMap ℝ ℂ) (z omega : ℝ) (tau : Fin 2 → ℝ) :
    ‖(causalityDomainDelayedScattering omega tau
        (uniformizedScatteringMatrix f g h z)).det‖ = 1 := by
  rw [norm_det_causalityDomainDelayedScattering, uniformizedScatteringMatrix_det, norm_one]

theorem uniformizedScatteringMatrix_commonDelay_coherentReturn_norm
    (f g h : SchwartzMap ℝ ℂ) (z omega tau : ℝ) (v : Fin 2 → ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau)
          (uniformizedScatteringMatrix f g h z))‖ =
      ‖causalityCoherentReturn v (uniformizedScatteringMatrix f g h z)‖ :=
  norm_causalityCoherentReturn_domainDelayed_const _ _ _ _

end FokasLenells

theorem hlsFiniteScatteringMatrix_domainDelay_powerBalance
    (omega : ℝ) (tau : HLSTwoQubit → ℝ) :
    (causalityDomainDelayedScattering omega tau hlsFiniteScatteringMatrix)ᴴ *
        causalityDomainDelayedScattering omega tau hlsFiniteScatteringMatrix =
      hlsFiniteScatteringMatrixᴴ * hlsFiniteScatteringMatrix :=
  causalityDomainDelayedScattering_powerBalance _ _ _

theorem hlsFiniteScatteringMatrix_domainDelay_det_norm
    (omega : ℝ) (tau : HLSTwoQubit → ℝ) :
    ‖(causalityDomainDelayedScattering omega tau hlsFiniteScatteringMatrix).det‖ =
      ‖hlsFiniteScatteringMatrix.det‖ :=
  norm_det_causalityDomainDelayedScattering _ _ _

theorem hlsFiniteScatteringMatrix_commonDelay_coherentReturn_norm
    (omega tau : ℝ) (v : HLSTwoQubit → ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau)
          hlsFiniteScatteringMatrix)‖ =
      ‖causalityCoherentReturn v hlsFiniteScatteringMatrix‖ :=
  norm_causalityCoherentReturn_domainDelayed_const _ _ _ _

end


end GaloisForLFunctions.HTGeometry
