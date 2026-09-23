import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularForcing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularSpectralContinuation
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.ZetaInverseHorizontal
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness

/-!
Modular inversion at every actual Xi occurrence, continued from the convergent primitive-pair Poincare series through the entire Xi-normalized field. The full residual matches the vertical modular sides and the open overlap containing the circular seam.
-/

open Complex Real Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMGlobalAngularResponse
open D4BMAngularSeries D4BMQuadraticMixedSource
noncomputable section

/-- A fixed polynomial clearing both Weyl completion denominators. -/
def clearFactor (u : ℂ) : ℂ := u*(2*u-1)*(2*u+1)

/-- The entire continuation of the polynomial-scaled full scalar cusp field.
Its Weyl coefficients use the entire Xi completion, including removable values. -/
def clearedScalar (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  (2*u+1)*riemannXi (2*u)*(z 1 : ℂ)^(1/2-u) +
  (2*u-1)*riemannXi (1+2*u)*(z 1 : ℂ)^(1/2+u) + clearFactor u*tail u z

private theorem tail_spectral_differentiable (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    Differentiable ℂ (fun u => tail u z) := by
  have hd := ((scalarValue_spectral_differentiable false z hz).add
    (scalarValue_spectral_differentiable true z hz)).const_mul (2:ℂ)
  convert! hd using 1
  funext u
  simp only [tail,d4BMCompletedEisensteinCuspTailPart,d4BMCompletedEisensteinFullSignedZeroWord,
    signedTail_eq_value _ _ _ _ _ z hz,Nat.cast_zero,zero_add,Pi.add_apply]

/-- The entire normalized field retains every nonconstant Fourier mode. -/
theorem clearedScalar_differentiable (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    Differentiable ℂ (fun u => clearedScalar u z) := by
  have hn : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hm : Differentiable ℂ (fun u : ℂ => (z 1 : ℂ)^(1/2-u)) :=
    (show Differentiable ℂ (fun u : ℂ => 1/2-u) by fun_prop).const_cpow (.inl hn)
  have hp : Differentiable ℂ (fun u : ℂ => (z 1 : ℂ)^(1/2+u)) :=
    (show Differentiable ℂ (fun u : ℂ => 1/2+u) by fun_prop).const_cpow (.inl hn)
  have hxm := differentiable_riemannXi.comp (differentiable_id.const_mul (2:ℂ))
  have hxp := differentiable_riemannXi.comp ((differentiable_id.const_mul (2:ℂ)).const_add 1)
  have hm1 : Differentiable ℂ (fun u : ℂ => 2*u+1) := by fun_prop
  have hp1 : Differentiable ℂ (fun u : ℂ => 2*u-1) := by fun_prop
  have hP : Differentiable ℂ clearFactor := by unfold clearFactor; fun_prop
  exact (((hm1.mul hxm).mul hm).add ((hp1.mul hxp).mul hp)).add
    (hP.mul (tail_spectral_differentiable z hz))

private theorem lambda_eq_completed {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda s = completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; exact hs (by rw [h]; rfl)
  rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero hs0]
  field_simp [gammaR_ne_zero_of_im_ne hs]

private theorem nonreal_ne_zero_one {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 ∧ s ≠ 1 := by
  constructor <;> intro h <;> apply hs <;> rw [h] <;> rfl

/-- At every nonreal parameter the entire continuation equals the original literal field
multiplied by the fixed clearing polynomial. -/
theorem clearedScalar_eq (u : ℂ) (hu : u.im ≠ 0) (z : Fin 2 → ℝ) :
    clearedScalar u z = clearFactor u*scalar u z := by
  have h2 : (2*u).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hu
  have h12 : (1+2*u).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hu
  obtain ⟨h20,h21⟩ := nonreal_ne_zero_one h2
  obtain ⟨h120,h121⟩ := nonreal_ne_zero_one h12
  have he2 := riemannXi_eq_mul_completedRiemannZeta h20 h21
  have he12 := riemannXi_eq_mul_completedRiemannZeta h120 h121
  rw [← lambda_eq_completed h2] at he2
  rw [← lambda_eq_completed h12] at he12
  rw [clearedScalar,he2,he12]
  simp only [scalar,d4BMCompletedEisensteinCuspLeg,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    d4BMCompletedEisensteinCuspConstantCoefficient,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,ite_false,ite_true,Int.cast_neg,Int.cast_one,mul_one,
    neg_one_mul,one_mul,← sub_eq_add_neg]
  dsimp [clearFactor,tail]
  ring

private theorem scalar_invert_chamber (u : ℂ) (hu : 1 < u.re)
    (z : D4BMUpperHalfPlaneCoordinate) :
    scalar u ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      scalar u ![z.x,z.y] := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨u+1/2,by simp; linarith⟩
  have hcent : P.s-1/2 = u := by dsimp [P]; ring
  have he (w : D4BMUpperHalfPlaneCoordinate) := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg w P w.x
  have he' (w : D4BMUpperHalfPlaneCoordinate) :
      d4BMCompletedEisensteinPoincareSeries w P = scalar u ![w.x,w.y] := by
    have h := he w
    rw [hcent] at h
    exact h
  rw [← he',← he']
  exact d4BM_completedEisensteinPoincareSeries_invert z P

/-- Modular inversion of the entire normalized full field, obtained by analytic continuation
from the actual convergent primitive-pair Poincare series. -/
theorem clearedScalar_invert (u : ℂ) (z : D4BMUpperHalfPlaneCoordinate) :
    clearedScalar u ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      clearedScalar u ![z.x,z.y] := by
  have hL := (clearedScalar_differentiable
    ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y]
    (d4BMEisensteinInvertCoordinate z).y_pos).differentiableOn.analyticOnNhd isOpen_univ
  have hR := (clearedScalar_differentiable ![z.x,z.y] z.y_pos).differentiableOn.analyticOnNhd isOpen_univ
  have he : (fun v => clearedScalar v
      ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y]) =ᶠ[𝓝 (2+Complex.I)]
      (fun v => clearedScalar v ![z.x,z.y]) := by
    have hr : ∀ᶠ v : ℂ in 𝓝 (2+Complex.I), 1 < v.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hi : ∀ᶠ v : ℂ in 𝓝 (2+Complex.I), 0 < v.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by norm_num)
    filter_upwards [hr,hi] with v hv hvi
    rw [clearedScalar_eq v hvi.ne',clearedScalar_eq v hvi.ne',scalar_invert_chamber v hv z]
  exact congrFun (hL.eq_of_eventuallyEq hR he) u

private theorem clearFactor_ne_zero {u : ℂ} (hu : u.im ≠ 0) : clearFactor u ≠ 0 := by
  have h0 : u ≠ 0 := (nonreal_ne_zero_one hu).1
  have hm : 2*u-1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hu (by linarith)
  have hp : 2*u+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hu (by linarith)
  exact mul_ne_zero (mul_ne_zero h0 hm) hp

/-- Every actual Xi scalar field obeys the modular inversion law without a chamber
or critical-line assumption. -/
theorem xi_scalar_invert (q : XiZeroCopy) (z : D4BMUpperHalfPlaneCoordinate) :
    scalar (center q) ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      scalar (center q) ![z.x,z.y] := by
  have hi : (center q).im ≠ 0 := by simpa [center] using xi_divisor_support_im_ne_zero q.1
  have he := clearedScalar_invert (center q) z
  rw [clearedScalar_eq _ hi,clearedScalar_eq _ hi] at he
  exact (mul_left_cancel₀ (clearFactor_ne_zero hi)) he


/-- Below the cutoff, the original unmodified forcing remains exactly, since the
cutoff response and all its local differential contributions vanish. -/
theorem forcing_low (q : XiZeroCopy) (minusBranch : Bool) (z : Fin 2 → ℝ)
    (hz : z 1 < 2) :
    forcing q minusBranch z = (parameter q minusBranch/2)*scalar (center q) z^(2 : ℕ) := by
  have he : cutoffResponse q minusBranch =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hz] with w hw
    exact cutoffResponse_zero q minusBranch w hw.le
  rw [forcing,hyperbolicLaplacian_congr he,he.eq_of_nhds]
  have hd (i : Fin 2) : coordDeriv i (fun _ : Fin 2 → ℝ => (0:ℂ)) = fun _ => 0 := by
    funext w
    simp [coordDeriv]
  simp [hyperbolicLaplacian,hd]

/-- The full residual matches under inversion on the open overlap containing the
compact modular seam; the local cutoff terms vanish on both charts. -/
theorem forcing_invert_overlap (q : XiZeroCopy) (minusBranch : Bool)
    (z : D4BMUpperHalfPlaneCoordinate) (hz : z.y < 2)
    (hzi : (d4BMEisensteinInvertCoordinate z).y < 2) :
    forcing q minusBranch ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      forcing q minusBranch ![z.x,z.y] := by
  rw [forcing_low q minusBranch _ hzi,forcing_low q minusBranch _ hz,xi_scalar_invert]

private theorem periodic_coordDeriv {f : (Fin 2 → ℝ) → ℂ} {p : Fin 2 → ℝ}
    (hf : Function.Periodic f p) (i : Fin 2) : Function.Periodic (coordDeriv i f) p := by
  intro z
  have he : (fun w => f (w+p)) = f := funext hf
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := z) p
  rw [he] at hd
  exact congrArg (fun L => L (Pi.single i 1)) hd.symm

private theorem periodic_laplacian {f : (Fin 2 → ℝ) → ℂ} {p : Fin 2 → ℝ}
    (hf : Function.Periodic f p) (hp : p 1 = 0) : Function.Periodic (hyperbolicLaplacian f) p := by
  intro z
  simp only [hyperbolicLaplacian,Pi.add_apply,hp,add_zero,
    periodic_coordDeriv (periodic_coordDeriv hf 0) 0 z,
    periodic_coordDeriv (periodic_coordDeriv hf 1) 1 z]

/-- The entire differential residual matches across the vertical modular sides. -/
theorem forcing_periodic (q : XiZeroCopy) (minusBranch : Bool) :
    Function.Periodic (forcing q minusBranch) ![1,0] := by
  have hs : Function.Periodic (scalar (center q)) ![1,0] := by
    intro z
    simpa [scalar,Pi.add_apply] using
      d4BM_completedEisensteinCuspLeg_scalar_periodic (center q) (z 1) (z 0)
  have hc : Function.Periodic (cutoffResponse q minusBranch) ![1,0] := by
    intro z
    simp [cutoffResponse,cutoff,cuspResponse,cuspPowerResponse,powerResponse,Pi.add_apply]
  have hl := periodic_laplacian hc (by rfl)
  intro z
  unfold forcing
  rw [hs z,hc z,hl z]

end
end RHTower.D4BMGlobalAngularResponse
