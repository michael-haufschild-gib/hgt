import GaloisForLFunctions.RHTower.ThetaMovingShellBoundaryLayer
import GaloisForLFunctions.RHTower.ThetaCuspShellIncompleteGammaCoordinate
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard

/-!
# Literal theta-shell Fourier jets at the squared shell scale

Connect the boundary-layer integral to the actual positive-half-line theta
shell. Every normalization and coordinate exchange is exact.
-/

open Real Complex MeasureTheory Set Filter Topology Polynomial

namespace RHTower
noncomputable section

def thetaShellFrequencyJet (n k : ℕ) (b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, (thetaCuspSourceTerm x (n+1) : ℂ) *
    (Complex.I * (x : ℂ))^k * Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))

private theorem integral_Ioi_translate (f : ℝ → ℂ) (a : ℝ) :
    (∫ u : ℝ in Ioi 0, f (u+a)) = ∫ v : ℝ in Ioi a, f v := by
  have h := (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding f (Ioi a)
  have hpre : (fun u : ℝ => u+a) ⁻¹' Ioi a = Ioi 0 := by
    ext u
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hu <;> linarith
  rw [hpre] at h
  exact h

private theorem shellScale_eq (n : ℕ) :
    thetaMovingShellScale n = ((n+1 : ℕ) : ℝ)^2 := by
  simp [thetaMovingShellScale]

theorem thetaMovingShellGammaPhase_eq_coordinate (n : ℕ) (u : ℝ) :
    thetaMovingShellGammaPhase n u = thetaMovingShellScale n *
      thetaCuspShellGammaCoordinate (n+1) (thetaMovingShellScale n + u) := by
  have ha := thetaMovingShellScale_pos n
  unfold thetaCuspShellGammaCoordinate thetaMovingShellGammaPhase
  rw [← shellScale_eq]
  have hr : (thetaMovingShellScale n + u) / thetaMovingShellScale n =
      1 + u / thetaMovingShellScale n := by field_simp
  rw [hr]
  ring

theorem thetaMovingShellGammaAmplitude_eq_normalized (n : ℕ) (u : ℝ) :
    thetaMovingShellGammaAmplitude n u =
      Real.exp (Real.pi * thetaMovingShellScale n) / thetaMovingShellScale n *
        thetaCuspShellGammaAmplitude (n+1) (thetaMovingShellScale n + u) := by
  have ha := thetaMovingShellScale_pos n
  unfold thetaMovingShellGammaAmplitude thetaCuspShellGammaAmplitude
  rw [← shellScale_eq]
  have hr : (thetaMovingShellScale n + u) / thetaMovingShellScale n =
      1 + u / thetaMovingShellScale n := by field_simp
  rw [hr]
  have he : Real.exp (Real.pi * thetaMovingShellScale n) *
      Real.exp (-Real.pi * (thetaMovingShellScale n + u)) = Real.exp (-Real.pi*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  field_simp

theorem integrableOn_thetaShellFrequencyJetIntegrand (n k : ℕ) (b : ℝ) :
    IntegrableOn (fun x : ℝ => (thetaCuspSourceTerm x (n+1) : ℂ) *
      (Complex.I * (x : ℂ))^k * Complex.exp (Complex.I * (b : ℂ) * (x : ℂ)))
        (Ioi 0) := by
  have hreal : IntegrableOn (fun x : ℝ => x^k * thetaCuspSourceTerm x (n+1)) (Ioi 0) := by
    rw [show (fun x : ℝ => x^k * thetaCuspSourceTerm x (n+1)) =
      (fun x : ℝ => x^k * thetaCuspPolynomialAtom thetaCuspSeedPolynomial (n+1) x) by
        funext x
        rw [congrFun (thetaCuspSourceTerm_eq_polynomialAtom (n+1)) x]]
    exact integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos k
      thetaCuspSeedPolynomial (Nat.succ_pos n)
  apply Integrable.mono hreal.norm
  · exact (by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (fun x : ℝ => (thetaCuspSourceTerm x (n+1) : ℂ) *
        (Complex.I * (x : ℂ))^k *
          Complex.exp (Complex.I * (b : ℂ) * (x : ℂ)))).aestronglyMeasurable.restrict
  · filter_upwards with x
    simp [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      mul_comm]

/-- Exact normalization of every literal positive-index shell Fourier jet. -/
theorem thetaMovingShellGammaJet_eq_normalized_shell (n k : ℕ) (lambda : ℝ) :
    thetaMovingShellGammaJet n k lambda =
      ((Real.exp (Real.pi * thetaMovingShellScale n) / thetaMovingShellScale n *
        (thetaMovingShellScale n)^k : ℝ) : ℂ) *
          thetaShellFrequencyJet n k (lambda * thetaMovingShellScale n) := by
  let a := thetaMovingShellScale n
  let b := lambda*a
  let P : ℝ → ℂ := fun x => (Complex.I * (x : ℂ))^k *
    Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hInt : IntegrableOn (fun x : ℝ => (thetaCuspSourceTerm x (n+1) : ℂ) * P x)
      (Ioi 0) := by
    simpa only [P, mul_assoc] using integrableOn_thetaShellFrequencyJetIntegrand n k b
  have hcoord := thetaCuspShellHalfLineTransform_eq_gammaIntegral P hP
    (Nat.succ_pos n) hInt
  have hshell : thetaShellFrequencyJet n k b =
      ∫ v : ℝ in Ioi a, thetaCuspShellGammaIntegrand P (n+1) v := by
    simpa only [thetaCuspShellHalfLineTransform, thetaShellFrequencyJet, P,
      ← shellScale_eq, a, mul_assoc] using hcoord
  let c : ℂ := ((Real.exp (Real.pi*a) / a * a^k : ℝ) : ℂ)
  change thetaMovingShellGammaJet n k lambda = c * thetaShellFrequencyJet n k b
  calc
    thetaMovingShellGammaJet n k lambda =
        ∫ u : ℝ in Ioi 0, c * thetaCuspShellGammaIntegrand P (n+1) (u+a) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have ha := thetaMovingShellScale_pos n
      have hu0 : 0 < u := hu
      have hav : 0 < u+a := by dsimp [a]; linarith
      rw [thetaCuspShellGammaIntegrand_eq_explicit P (Nat.succ_pos n) hav]
      dsimp [P, c, b]
      rw [add_comm u a]
      unfold thetaMovingShellGammaJetIntegrand
      rw [thetaMovingShellGammaAmplitude_eq_normalized,
        thetaMovingShellGammaPhase_eq_coordinate]
      dsimp [a]
      push_cast
      simp only [mul_pow, mul_assoc]
      ring
    _ = c * ∫ u : ℝ in Ioi 0, thetaCuspShellGammaIntegrand P (n+1) (u+a) :=
      integral_const_mul c _
    _ = c * ∫ v : ℝ in Ioi a, thetaCuspShellGammaIntegrand P (n+1) v := by
      rw [integral_Ioi_translate]
    _ = c * thetaShellFrequencyJet n k b := by rw [hshell]

theorem tendsto_normalized_thetaShellFrequencyJet (k : ℕ) (lambda : ℝ) :
    Tendsto (fun n =>
      ((Real.exp (Real.pi * thetaMovingShellScale n) / thetaMovingShellScale n *
        (thetaMovingShellScale n)^k : ℝ) : ℂ) *
          thetaShellFrequencyJet n k (lambda * thetaMovingShellScale n)) atTop
      (𝓝 (((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
        ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1)))) := by
  simpa only [thetaMovingShellGammaJet_eq_normalized_shell] using
    tendsto_thetaMovingShellGammaJet k lambda

/-- A bound uniform in the real frequency as well as shell index. -/
theorem norm_normalized_thetaShellFrequencyJet_le (n k : ℕ) (b : ℝ) :
    ‖((Real.exp (Real.pi * thetaMovingShellScale n) / thetaMovingShellScale n *
      (thetaMovingShellScale n)^k : ℝ) : ℂ) * thetaShellFrequencyJet n k b‖ ≤
        thetaMovingShellJetBound k := by
  have h := norm_thetaMovingShellGammaJet_le n k (b / thetaMovingShellScale n)
  rw [thetaMovingShellGammaJet_eq_normalized_shell] at h
  rwa [div_mul_cancel₀ _ (thetaMovingShellScale_pos n).ne'] at h

end
end RHTower
