import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering

/-!
# Resonant and nonresonant pairs in the cubic hierarchy

On Shi's five-dimensional family (arXiv:2611.22194, equation (1.3)),
both Hirota pair evaluations share an even polynomial in the momenta.
Its zero set is exactly the locus on which a two-wave measurement loses
the interaction coefficient. Elsewhere the coefficient is the squared
contrast of the two logarithmic rates.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
open HilbertMetric.CauchyDephasing

/-- Coefficients of the weight 4, 6, 8, 10 and 12 dispersions. -/
structure Weights where
  w4 : ℝ
  w6 : ℝ
  w8 : ℝ
  w10 : ℝ
  w12 : ℝ

def graph (u v : ℝ) : ℝ := u^3-v

def dispersion (w : Weights) (u v : ℝ) : ℝ :=
  graph u v * (w.w4*u + w.w6*(u^3+2*v) + w.w8*u^2*(u^3-4*v) +
    w.w10*u*(u^3-4*v)*(u^3+2*v) + w.w12*(u^3-4*v)*(u^6+28*u^3*v+16*v^2))

/-- The quartic member is the longitudinal part of the existing KP jet symbol. -/
theorem quartic_is_KP (u v ρ : ℝ) :
    dispersion ⟨1,0,0,0,0⟩ u v = mondalHirotaSymbol 1 ρ v u 0 := by
  simp only [dispersion,graph,mondalHirotaSymbol]
  ring

/-- The common cofactor in the two Hirota evaluations. -/
def resonance (w : Weights) (s t : ℝ) : ℝ :=
  let h := s^2+t^2
  let d := (s^2-t^2)^2
  w.w4+3*w.w6*h-3*w.w8*d-9*w.w10*h*d-27*w.w12*d*(5*h^2-4*s^2*t^2)

theorem sum_symbol (w : Weights) (s t : ℝ) :
    dispersion w (s+t) (s^3+t^3) = 3*s*t*(s+t)^2*resonance w s t := by
  unfold dispersion graph resonance
  ring

theorem difference_symbol (w : Weights) (s t : ℝ) :
    dispersion w (s-t) (s^3-t^3) = -(3*s*t*(s-t)^2*resonance w s t) := by
  rw [show s-t = s+(-t) by ring, show s^3-t^3 = s^3+(-t)^3 by ring, sum_symbol]
  unfold resonance
  ring

/-- The exact inverse problem for a single positive-momentum pair, including
pairs for which both symbol evaluations vanish. -/
theorem phase_locus (w : Weights) (a b A : ℝ) :
    let s := Real.exp a
    let t := Real.exp b
    A * dispersion w (s+t) (s^3+t^3) + dispersion w (s-t) (s^3-t^3) = 0 ↔
      resonance w s t = 0 ∨ A = contrast a b ^ 2 := by
  dsimp only
  rw [sum_symbol,difference_symbol]
  let s := Real.exp a
  let t := Real.exp b
  change A*(3*s*t*(s+t)^2*resonance w s t) + -(3*s*t*(s-t)^2*resonance w s t) = 0 ↔ _
  rw [show A*(3*s*t*(s+t)^2*resonance w s t) + -(3*s*t*(s-t)^2*resonance w s t) =
    (3*s*t)*resonance w s t*(A*(s+t)^2-(s-t)^2) by ring]
  have hst : 3*s*t ≠ 0 := by dsimp [s,t]; positivity
  have hsum : (s+t)^2 ≠ 0 := by dsimp [s,t]; positivity
  simp only [mul_eq_zero,hst,false_or,sub_eq_zero]
  unfold contrast
  rw [div_pow,eq_div_iff hsum]

/-- Repeated cubic factors change each nondegenerate pair phase by the
corresponding integer power. The identity also covers resonant pairs. -/
theorem repeated_pair_cancellation (w : Weights) (n : ℕ) (a b : ℝ) :
    let s := Real.exp a
    let t := Real.exp b
    (contrast a b ^ 2)^(n+1) * (graph (s+t) (s^3+t^3))^(2*n) * dispersion w (s+t) (s^3+t^3) +
      (graph (s-t) (s^3-t^3))^(2*n) * dispersion w (s-t) (s^3-t^3) = 0 := by
  dsimp only
  let s := Real.exp a
  let t := Real.exp b
  have hp : graph (s+t) (s^3+t^3) = 3*s*t*(s+t) := by unfold graph; ring
  have hm : graph (s-t) (s^3-t^3) = -(3*s*t*(s-t)) := by unfold graph; ring
  have hz : s+t ≠ 0 := (add_pos (Real.exp_pos a) (Real.exp_pos b)).ne'
  have scale : contrast a b ^ 2 * graph (s+t) (s^3+t^3)^2 = graph (s-t) (s^3-t^3)^2 := by
    change ((s-t)/(s+t))^2 * _ = _
    rw [hp,hm]
    field_simp
    ring
  have hbase := (phase_locus w a b (contrast a b^2)).mpr (Or.inr rfl)
  change _ * graph (s+t) (s^3+t^3)^(2*n) * _ + graph (s-t) (s^3-t^3)^(2*n) * _ = 0
  rw [pow_succ, pow_mul, pow_mul, ← scale, mul_pow]
  linear_combination (norm := ring) (contrast a b ^ 2)^n * (graph (s+t) (s^3+t^3)^2)^n * hbase

#print axioms quartic_is_KP
#print axioms sum_symbol
#print axioms difference_symbol
#print axioms phase_locus
#print axioms repeated_pair_cancellation
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
