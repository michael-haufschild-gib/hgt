import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleBoundaryBounds

/-!
# Uniform square-root scale for the actual Weil pole diagonal

The exact diagonal cancellation, uniform boundary mass, elementary Mertens,
and Chebyshev bounds give an aperture-independent multiple of `exp(a)`.
Consequently positive literal pole compression would give that same scale
for the integrated Chebyshev deficit. The source sign remains an antecedent.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- One explicit aperture-independent bound for the normalized actual pole diagonal. -/
def ccmWeilPoleUniformDiagonalBound : ℝ :=
  |-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+
    (2*Real.log 2+Real.pi+1)+4+2*(Real.log 4+5)+2*(Real.log 4+4)

theorem ccmWeilPoleUniformDiagonalBound_pos : 0<ccmWeilPoleUniformDiagonalBound := by
  unfold ccmWeilPoleUniformDiagonalBound
  positivity

/-- The full pole self energy has the exact square-root scale at every positive
aperture, unconditionally and with every prime-power term retained. -/
theorem abs_ccmWeilPoleDiagonal_le (a : SuzukiPositiveAperture) :
    |ccmWeilPoleDiagonal a| ≤ ccmWeilPoleUniformDiagonalBound*Real.exp a.1 := by
  have ha := a.property
  have he := Real.exp_pos a.1
  have hm := Real.exp_pos (-a.1)
  have he1 : 1≤Real.exp a.1 := Real.one_le_exp ha.le
  have hm1 : Real.exp (-a.1)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hinv : Real.exp a.1*Real.exp (-a.1)=1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hae : a.1≤Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have ham : a.1*Real.exp (-a.1)≤1 := by
    have hh := mul_le_mul_of_nonneg_right hae hm.le
    rwa [hinv] at hh
  have hterm : |(1-2*a.1)*Real.exp (-a.1)|≤3*Real.exp a.1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hN0 : 0≤2*Real.sinh a.1 := by
    rw [Real.sinh_eq]
    linarith
  have hN : 2*Real.sinh a.1≤Real.exp a.1 := by
    rw [Real.sinh_eq]
    linarith
  have hk : |(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1)| ≤
      |-Real.eulerMascheroniConstant-Real.log (2*Real.pi)| *Real.exp a.1 := by
    rw [abs_mul,abs_of_nonneg hN0]
    exact mul_le_mul_of_nonneg_left hN (abs_nonneg _)
  have hEM := abs_ccmReciprocalMangoldtError_le (show 0≤2*a.1 by linarith)
  have hM : |2*Real.exp a.1*ccmReciprocalMangoldtError (2*a.1)|≤
      2*Real.exp a.1*(Real.log 4+5) := by
    rw [abs_mul,abs_of_pos (by positivity : 0<2*Real.exp a.1)]
    exact mul_le_mul_of_nonneg_left hEM (by positivity)
  have hP0 : 0≤2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)) := by
    exact mul_nonneg (by positivity) (Chebyshev.psi_nonneg _)
  have hP : 2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)) ≤
      2*(Real.log 4+4)*Real.exp a.1 := by
    have hp := Chebyshev.psi_le_const_mul_self (Real.exp_pos (2*a.1)).le
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.exp (-a.1) by positivity)
    have heq : Real.exp (-a.1)*Real.exp (2*a.1)=Real.exp a.1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ 2*Real.exp (-a.1)*((Real.log 4+4)*Real.exp (2*a.1)) := hh
      _ = _ := by rw [show 2*Real.exp (-a.1)*((Real.log 4+4)*Real.exp (2*a.1)) =
        2*(Real.log 4+4)*(Real.exp (-a.1)*Real.exp (2*a.1)) by ring,heq]
  have hB0 := (ccmGammaPoleBoundaryMass_nonneg a).2
  have hB := ccmGammaPoleSelfBoundaryMass_le a
  obtain ⟨hkL,hkR⟩ := abs_le.mp hk
  obtain ⟨hML,hMR⟩ := abs_le.mp hM
  obtain ⟨htL,htR⟩ := abs_le.mp hterm
  rw [ccmWeilPoleDiagonal_eq_error,ccmWeilPoleUniformDiagonalBound]
  apply abs_le.mpr
  constructor <;> nlinarith [Real.log_nonneg (show (1:ℝ)≤4 by norm_num),
    Real.log_nonneg (show (1:ℝ)≤2 by norm_num),Real.pi_pos]

/-- Explicit square-root-scale allowance for the integrated Chebyshev deficit
when the actual pole compression is nonnegative. -/
def ccmWeilPoleUniformDeficitBound : ℝ :=
  ccmWeilPoleUniformDiagonalBound+(2*Real.log 2+Real.pi+1)+
    2*(|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+Real.log 4+5)+1

theorem ccmWeilPoleUniformDeficitBound_pos : 0<ccmWeilPoleUniformDeficitBound := by
  unfold ccmWeilPoleUniformDeficitBound
  have := ccmWeilPoleUniformDiagonalBound_pos
  positivity

/-- Positivity of the literal two-pole matrix gives a uniform square-root-scale
bound for the admitted integrated prime-counting error. -/
theorem abs_ccmPoleIntegratedChebyshevDeficit_le_of_compression_nonneg
    (a : SuzukiPositiveAperture) (h : |ccmWeilPoleCross a|≤ccmWeilPoleDiagonal a) :
    |ccmPoleIntegratedChebyshevDeficit a| ≤ ccmWeilPoleUniformDeficitBound*Real.exp a.1 := by
  have hd := ccmPoleIntegratedChebyshevDeficit_bound_of_compression_nonneg a h
  have hA := le_trans (le_abs_self (ccmWeilPoleDiagonal a)) (abs_ccmWeilPoleDiagonal_le a)
  have hB := ccmGammaPoleCrossBoundaryMass_le a
  have ha := a.property
  have he : 1≤Real.exp a.1 := Real.one_le_exp ha.le
  have hae : a.1≤Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hC : 0≤2*Real.log 2+Real.pi+1 := by positivity
  have hK : 0≤|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+Real.log 4+5 := by positivity
  have hBC := mul_le_mul_of_nonneg_left he hC
  have hKC := mul_le_mul_of_nonneg_left hae hK
  unfold ccmWeilPoleUniformDeficitBound
  nlinarith

end RHTower
