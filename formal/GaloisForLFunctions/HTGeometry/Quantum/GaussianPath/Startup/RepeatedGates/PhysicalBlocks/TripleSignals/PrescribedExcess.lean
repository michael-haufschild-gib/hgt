import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.BoxPrice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.UniformMarks

/-! # An explicit physical gate density at each nonzero time -/
open MeasureTheory Filter Set Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal
noncomputable section

/-- A packet occupies four rows. Its calibrated Gaussian box gives a
positive excess for the physical gate density at each prescribed date. -/
def prescribedExcess (t : ℝ) : ℝ :=
  packetProbabilityFloor (π/(2*sqrt 2*t)) (1/(1008*(1+t))) / 40

theorem prescribed_excess_pos {t : ℝ} (ht : 0<t) : 0<prescribedExcess t :=
  div_pos (packet_probability_pos (by positivity)) (by norm_num)

/-- Almost surely every sufficiently long prefix exceeds the explicit
one-sweep excess, at projective error one quarter. -/
theorem gaussian_prescribed_excess {t : ℝ} (ht : 0<t) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      HasProjectiveCircuitApproximation (n+2) (1/4) s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1+prescribedExcess t)*(n+1:ℕ)<(s:ℝ) := by
  let r := 1/(1008*(1+t))
  let q := π/(2*sqrt 2*t)
  let p := packetProbabilityFloor q r
  have hr : 0<r := by dsimp only [r]; positivity
  have hp : 0<p := packet_probability_pos hr
  let lo := fun i => boxField q i-r
  let hi := fun i => boxField q i+r
  have hf := (good_boxes_half_mass q hr).2
  have hm : p≤gaussianBoxMass lo hi := calibrated_box_mass q hr.le
  have hη : (1/4:ℝ)<sqrt 2 := (by norm_num : (1/4:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))
  filter_upwards [hf,gaussian_uniform_marked_floor (T:=t) ht (show 0<p/40 by positivity)
    (by norm_num : (0:ℝ)≤1/4) hη] with ω hω hfloor
  obtain ⟨K,hK⟩ := eventually_atTop.mp hω
  filter_upwards [hfloor,eventually_ge_atTop (4*K+20)] with n hn hlen
  intro s hs
  obtain ⟨z,hz,C,hC,he⟩ := hs
  have hcal : (q*sqrt 2)*t=π/2 := by
    dsimp only [q]
    field_simp [ht.ne',(sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne']
  have hsml : |t| * (63*(2*r))≤1/8 := by
    rw [abs_of_pos ht]
    dsimp only [r]
    field_simp [show 0<1+t by positivity]
    linarith only [ht]
  have hc := count_good_boxes (show |q-q|≤r by simpa only [sub_self,abs_zero] using hr.le)
    hcal hsml C z hz he
  let m := (n+1)/4
  have hfreq := hK m (by dsimp only [m]; omega)
  change gaussianBoxMass lo hi/2*m≤((goodBoxes q r ω m).card:ℝ) at hfreq
  have hsize : ((n+1:ℕ):ℝ)≤5*(m:ℝ) := by exact_mod_cast (by dsimp only [m]; omega : n+1≤5*m)
  have hmarks : (p/10)*(n+1:ℕ) ≤ ((marked (circuitWord C)).card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg m (R:=ℝ))
    have hh' := mul_le_mul_of_nonneg_left hsize hp.le
    have hh'' : ((goodBoxes q r ω m).card:ℝ) ≤ ((marked (circuitWord C)).card:ℝ) := Nat.cast_le.mpr hc
    linarith only [hh,hh',hh'',hfreq]
  have hg := hn t ⟨le_rfl,le_rfl⟩ C z hz he
  change (1+p/40)*(n+1:ℕ)<(s:ℝ)
  linarith only [hg,hmarks,show (C.gateCount:ℝ)≤s from Nat.cast_le.mpr hC]

#print axioms gaussian_prescribed_excess
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
