import GaloisForLFunctions.HTGeometry.PaperGenealogyFredholmRecovery
import GaloisForLFunctions.HTGeometry.QGammaGNSChart

/-! # The exact phase ambiguity of native genealogy Gram determinants

The complete determinant sequence classifies scalar operator-certificate streams
up to a normalized depthwise phase gauge. The gauge acts unitarily on the original
history space and conjugates the actual full genealogy operators.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap
open scoped ComplexConjugate

def certificateGaugeSequence (a b : OpCertStream 1) : ℕ → ℂ
  | 0 => 1
  | n + 1 => certificateGaugeSequence a b n * scalarCertificateCoefficient a n /
      scalarCertificateCoefficient b n

@[simp] theorem certificateGaugeSequence_zero (a b : OpCertStream 1) :
    certificateGaugeSequence a b 0 = 1 := rfl

theorem certificateGaugeSequence_succ (a b : OpCertStream 1) (n : ℕ) :
    certificateGaugeSequence a b (n + 1) =
      certificateGaugeSequence a b n * scalarCertificateCoefficient a n /
        scalarCertificateCoefficient b n := rfl

private theorem gauge_norm (a b : OpCertStream 1)
    (h : ∀ n, ‖scalarCertificateCoefficient a n‖ = ‖scalarCertificateCoefficient b n‖) :
    ∀ n, ‖certificateGaugeSequence a b n‖ = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [certificateGaugeSequence_succ, norm_div, norm_mul, ih, h n, one_mul]
      exact div_self (norm_ne_zero_iff.mpr (scalarCertificateCoefficient_ne_zero b n))

private theorem mul_conj_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

private theorem gauge_coefficient (a b : OpCertStream 1)
    (h : ∀ n, ‖scalarCertificateCoefficient a n‖ = ‖scalarCertificateCoefficient b n‖)
    (n : ℕ) :
    scalarCertificateCoefficient b n = certificateGaugeSequence a b n *
      scalarCertificateCoefficient a n * conj (certificateGaugeSequence a b (n + 1)) := by
  have hs : certificateGaugeSequence a b (n + 1) * scalarCertificateCoefficient b n =
      certificateGaugeSequence a b n * scalarCertificateCoefficient a n := by
    rw [certificateGaugeSequence_succ]
    field_simp [scalarCertificateCoefficient_ne_zero b n]
  have hu := mul_conj_of_norm_one (gauge_norm a b h (n + 1))
  calc
    scalarCertificateCoefficient b n = scalarCertificateCoefficient b n *
        (certificateGaugeSequence a b (n + 1) * conj (certificateGaugeSequence a b (n + 1))) := by
          rw [hu, mul_one]
    _ = (certificateGaugeSequence a b (n + 1) * scalarCertificateCoefficient b n) *
        conj (certificateGaugeSequence a b (n + 1)) := by ring
    _ = _ := by rw [hs]

def scalarCertificatePhaseUnitary (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1) :
    FibSeq 1 ≃ₗᵢ[ℂ] FibSeq 1 :=
  scalarCertificateCoordinates.trans ((lpPhaseEquiv u hu).trans scalarCertificateCoordinates.symm)

theorem scalarCertificateCoordinates_phaseUnitary (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1)
    (f : FibSeq 1) (n : ℕ) :
    scalarCertificateCoordinates (scalarCertificatePhaseUnitary u hu f) n =
      u n * scalarCertificateCoordinates f n := by
  change scalarCertificateCoordinates
    (scalarCertificateCoordinates.symm (lpPhaseEquiv u hu (scalarCertificateCoordinates f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, lpPhaseEquiv_apply]

private theorem genealogy_phase_conjugation (a b : OpCertStream 1)
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1)
    (hc : ∀ n, scalarCertificateCoefficient b n =
      u n * scalarCertificateCoefficient a n * conj (u (n + 1))) :
    b.genealogy = RHTower.unitaryPush (scalarCertificatePhaseUnitary u hu) a.genealogy := by
  let U := scalarCertificatePhaseUnitary u hu
  have hi : b.genealogy ∘L (U : FibSeq 1 →L[ℂ] FibSeq 1) =
      (U : FibSeq 1 →L[ℂ] FibSeq 1) ∘L a.genealogy := by
    apply ContinuousLinearMap.ext
    intro f
    apply scalarCertificateCoordinates.injective
    apply lp.ext
    funext n
    change scalarCertificateCoordinates (b.genealogy (U f)) n =
      scalarCertificateCoordinates (U (a.genealogy f)) n
    simp only [U, scalarCertificateCoordinates_genealogy, scalarCertificateCoordinates_phaseUnitary]
    have hunit : conj (u (n + 1)) * u (n + 1) = 1 := by
      rw [mul_comm]
      exact mul_conj_of_norm_one (hu (n + 1))
    rw [hc n]
    calc
      _ = u n * scalarCertificateCoordinates f n -
          u n * scalarCertificateCoefficient a n *
            (conj (u (n + 1)) * u (n + 1)) * scalarCertificateCoordinates f (n + 1) := by ring
      _ = _ := by rw [hunit]; ring
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun T : FibSeq 1 →L[ℂ] FibSeq 1 => T (U.symm f)) hi
  change b.genealogy (U (U.symm f)) = U (a.genealogy (U.symm f)) at h
  rw [U.apply_symm_apply] at h
  exact h

theorem paperGenealogyGramDet_eq_iff_phaseGauge (a b : OpCertStream 1) :
    (∀ N, paperGenealogyGramDet a N = paperGenealogyGramDet b N) ↔
      ∃ (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1), u 0 = 1 ∧
        (∀ n, scalarCertificateCoefficient b n =
          u n * scalarCertificateCoefficient a n * conj (u (n + 1))) ∧
        b.genealogy = RHTower.unitaryPush (scalarCertificatePhaseUnitary u hu) a.genealogy := by
  rw [paperGenealogyGramDet_eq_iff]
  constructor
  · intro h
    refine ⟨certificateGaugeSequence a b, gauge_norm a b h,
      certificateGaugeSequence_zero a b, gauge_coefficient a b h, ?_⟩
    exact genealogy_phase_conjugation a b _ _ (gauge_coefficient a b h)
  · rintro ⟨u, hu, _, hc, _⟩ n
    have h := congrArg norm (hc n)
    simpa only [norm_mul, Complex.norm_conj, hu n, hu (n + 1), one_mul, mul_one] using h.symm

end
end GaloisForLFunctions.HTGeometry
