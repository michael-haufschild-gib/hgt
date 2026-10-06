import GaloisForLFunctions.RHTower.ChiCubicReciprocalFourier
import GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets

/-!
# Exact normalized physical reciprocal kernel

The raw reciprocal Fourier identity is rescaled in all three physical
coordinates. The `N^3` Jacobian and original reciprocal factor cancel
against the normalization `(log N)^3/N` and the three exact normalized
slice identities. Every physical window and phase remains, with curvature
`1/N`. This is the actual moving kernel to which derivative budgets and
curved-frequency energy must be applied; no stationary substitution occurs.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem rescale {N : ℝ} (hN : 0<N) (f : ℝ→ℂ) :
    (∫x : ℝ, f x)=(N : ℂ)*∫x : ℝ, f (N*x) := by
  rw [Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hN),Complex.real_smul,
    Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hN.ne'),one_mul]

private theorem rescale_three {N : ℝ} (hN : 0<N) (f : ℝ→ℝ→ℝ→ℂ) :
    (∫r : ℝ,∫q : ℝ,∫p : ℝ, f r q p)=
      (N : ℂ)^3*∫r : ℝ,∫q : ℝ,∫p : ℝ, f (N*r) (N*q) (N*p) := by
  have hq (r : ℝ) : (∫q : ℝ,∫p : ℝ, f r q p)=
      (N : ℂ)^2*∫q : ℝ,∫p : ℝ, f r (N*q) (N*p) := by
    rw [rescale hN (fun q => ∫p : ℝ, f r q p)]
    have hp : (∫q : ℝ,∫p : ℝ, f r (N*q) p)=
        ∫q : ℝ, (N : ℂ)*∫p : ℝ, f r (N*q) (N*p) := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact rescale hN _
    rw [hp,integral_const_mul]
    ring
  rw [rescale hN (fun r => ∫q : ℝ,∫p : ℝ, f r q p)]
  simp_rw [hq,integral_const_mul]
  ring

/-- Exact normalized Fourier kernel of the original selected physical cone profile. -/
theorem bagCubicControlledCone_normalized_fourier (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (a b : ℝ) :
    (((Real.log N.1)^3/N.1 : ℝ) : ℂ)*
      (𝓕 (bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H)))
        (WithLp.toLp 2 ![a,b]) =
      let F := bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1)
      (2*Real.pi : ℂ)*∫r : ℝ,∫q : ℝ,∫p : ℝ,
        F p*F q*(starRingEnd ℂ) (F r)/(r : ℂ)^2*
          (bagPhysicalHeightWindow (p*q/r) : ℂ)*
          bourgainOscillation (-2*Real.pi*((p*b+q*a+a*b/N.1)/r)) := by
  have hN : 0<N.1 := lt_trans zero_lt_one N.2
  have hNC : (N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  rw [bagCubicControlledCone_fourier_eq_reciprocal]
  dsimp only
  rw [rescale_three hN,←mul_assoc]
  simp_rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  apply integral_congr_ae
  filter_upwards [] with q
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hr : r=0
  · simp [hr]
  · have hw : N.1*p*(N.1*q)/(N.1*r*N.1)=p*q/r := by field_simp
    have hp : (N.1*p*b+N.1*q*a+a*b)/(N.1*r)=(p*b+q*a+a*b/N.1)/r := by
      field_simp
    rw [hw,hp,←bagCubicNormalizedSlice_eq_actual N H p,
      ←bagCubicNormalizedSlice_eq_actual N H q,←bagCubicNormalizedSlice_eq_actual N H r]
    simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_mul]
    field_simp

end RHTower.BAGTrace
