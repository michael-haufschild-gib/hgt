import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyQuadraticRealClosureMixing

/-!
# Source-faithful branch covariance no-go for the HB Peierls route

For a nonzero Einstein seed, the canonical global left-coordinate `++` source at the reflected Xi
copy equals the canonical `--` source at the original copy exactly on the critical line. This
upgrades the square-root-branch obstruction to a representation-independent law.

Indeed, let any complex field space, any bilinear quadratic residual, and any two branch families
realize those literal source packets. If functional-equation reflection swaps the branches, their
quadratic residuals are equal, so source faithfulness forces the Xi fibre onto the wall. No
symmetry, cyclicity, Peierls pairing, propagator, or chosen square root is needed.

Off wall, the same fibre has a four-element FE--Schwarz real closure. Thus the strongest positive
survivor is precise: a physical continuation must leave the two-branch individual-incidence model
and use at least the four-sector real-closure packet with an orbit-level landing.

`[NEW] [REPRESENTATION-INDEPENDENT NO-GO] [FOUR-SECTOR NECESSITY] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

theorem hbXiPeierlsPlusSource_reflect_eq_minusSource_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsPlusSource amplitude (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsMinusSource amplitude q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hfst := congrArg (fun x : HBXiPeierlsCarrier => x.1) h
    have heval := congrArg
      (fun f : HBXiPeierlsPacket => f (xiZeroCopyReflectEquiv q)) hfst
    simp [hbXiPeierlsPlusSource, hbXiPeierlsMinusSource] at heval
    have hrefline :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha
        (xiZeroCopyReflectEquiv q)).mp heval
    rw [xiZeroCopyReflect_re_eq_one_sub] at hrefline
    linarith
  · intro hline
    have hrefline : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 := by
      rw [xiZeroCopyReflect_re_eq_one_sub]
      linarith
    have hq :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha q).mpr hline
    have href :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha
        (xiZeroCopyReflectEquiv q)).mpr hrefline
    unfold hbXiPeierlsPlusSource hbXiPeierlsMinusSource
    rw [hq, href]
    simp

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem hbXiPeierls_sourceFaithful_branchCovariance_forces_criticalLine
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] HBXiPeierlsCarrier)
    (p m : XiZeroCopy → X) (q : XiZeroCopy)
    (hplus :
      d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B
          (p (xiZeroCopyReflectEquiv q)) =
        hbXiPeierlsPlusSource amplitude (xiZeroCopyReflectEquiv q))
    (hminus :
      d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B (m q) =
        hbXiPeierlsMinusSource amplitude q)
    (hswap : p (xiZeroCopyReflectEquiv q) = m q) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (hbXiPeierlsPlusSource_reflect_eq_minusSource_iff ha q).mp
  calc
    hbXiPeierlsPlusSource amplitude (xiZeroCopyReflectEquiv q) =
        d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B
          (p (xiZeroCopyReflectEquiv q)) := hplus.symm
    _ = d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B (m q) := by rw [hswap]
    _ = hbXiPeierlsMinusSource amplitude q := hminus

theorem hbXiPeierls_tilted_no_sourceFaithful_branchCovariance
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] HBXiPeierlsCarrier)
    (p m : XiZeroCopy → X) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬(d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B
          (p (xiZeroCopyReflectEquiv q)) =
        hbXiPeierlsPlusSource amplitude (xiZeroCopyReflectEquiv q) ∧
      d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B (m q) =
        hbXiPeierlsMinusSource amplitude q ∧
      p (xiZeroCopyReflectEquiv q) = m q) := by
  intro h
  exact htilt (hbXiPeierls_sourceFaithful_branchCovariance_forces_criticalLine
    ha B p m q h.1 h.2.1 h.2.2)

theorem hbXiPeierls_sourceFaithful_global_branchCovariance_forces_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] HBXiPeierlsCarrier)
    (p m : XiZeroCopy → X)
    (hplus : ∀ q,
      d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B (p q) =
        hbXiPeierlsPlusSource amplitude q)
    (hminus : ∀ q,
      d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B (m q) =
        hbXiPeierlsMinusSource amplitude q)
    (hswap : ∀ q, p (xiZeroCopyReflectEquiv q) = m q) :
    RiemannHypothesis := by
  apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
    0).mp
  intro q
  apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff 0 q).mpr
  exact hbXiPeierls_sourceFaithful_branchCovariance_forces_criticalLine
    ha B p m q (hplus (xiZeroCopyReflectEquiv q)) (hminus q) (hswap q)

theorem hbXiPeierls_tilted_sourceFaithful_noGo_and_realClosure_ge_four
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] HBXiPeierlsCarrier)
    (p m : XiZeroCopy → X) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (support : Finset ℂ)
    (hq : d4ThetaTeukolskyQuadraticReturnWeight q ∈ support)
    (htheta : ∀ z ∈ support, 1 - z ∈ support)
    (hreal : ∀ z ∈ support, (starRingEnd ℂ) z ∈ support) :
    (¬(d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B
            (p (xiZeroCopyReflectEquiv q)) =
          hbXiPeierlsPlusSource amplitude (xiZeroCopyReflectEquiv q) ∧
        d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B (m q) =
          hbXiPeierlsMinusSource amplitude q ∧
        p (xiZeroCopyReflectEquiv q) = m q)) ∧
      4 ≤ support.card := by
  exact ⟨hbXiPeierls_tilted_no_sourceFaithful_branchCovariance ha B p m q htilt,
    d4ThetaTeukolsky_tilted_closedPacket_card_ge_four
      q htilt support hq htheta hreal⟩

end

end RHTower
