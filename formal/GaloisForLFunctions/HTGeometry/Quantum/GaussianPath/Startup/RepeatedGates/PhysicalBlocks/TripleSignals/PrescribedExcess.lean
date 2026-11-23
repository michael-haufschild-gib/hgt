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
    have hh := mul_le_mul_of_nonneg_right hm (show 0≤(m:ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hsize hp.le
    have hh'' : ((goodBoxes q r ω m).card:ℝ) ≤ ((marked (circuitWord C)).card:ℝ) := Nat.cast_le.mpr hc
    linarith only [hh,hh',hh'',hfreq]
  have hg := hn t ⟨le_rfl,le_rfl⟩ C z hz he
  change (1+p/40)*(n+1:ℕ)<(s:ℝ)
  have hcount : (C.gateCount:ℝ) ≤ s := Nat.cast_le.mpr hC
  linarith only [hg,hmarks,hcount]

/-- The excess is at least a Gaussian tail in reciprocal time before
one time unit, and an inverse 48th power afterwards. -/
theorem prescribed_excess_scales :
    ∃ c>0, ∃ A>0, (∀ t : ℝ, 0<t → t≤1 → c*exp (-A/t^2)≤prescribedExcess t) ∧
      ∀ t : ℝ, 1≤t → c*exp (-A)/t^48≤prescribedExcess t := by
  let z := π/(2*sqrt 2)
  let K := 1/(1008*sqrt (2*π))
  let A := 24*(z+1)^2
  have hz : 0<z := by dsimp [z]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨K^48/40,by positivity,A,hA,?_⟩
  have hformula {t : ℝ} (ht : 0<t) :
      prescribedExcess t = (2*K/(1+t))^48 *
        exp (-24*(z/t+1/(1008*(1+t)))^2)/40 := by
    rw [prescribedExcess,packet_probability_formula,
      abs_of_pos (by positivity : 0<π/(2*sqrt 2*t))]
    have hcoeff : 2*(1/(1008*(1+t)))/sqrt (2*π)=2*K/(1+t) := by
      simp only [K,div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hcoeff,show π/(2*sqrt 2*t)=z/t from (div_div ..).symm]
  constructor
  · intro t ht ht'
    rw [hformula ht]
    have hb : K ≤ 2*K/(1+t) := (le_div_iff₀ (by positivity)).mpr
      (by linarith only [mul_le_mul_of_nonneg_left ht' hK.le])
    have hr : 1/(1008*(1+t))≤1/t := one_div_le_one_div_of_le ht (by linarith only [ht])
    have hsq := pow_le_pow_left₀ (by positivity : 0≤z/t+1/(1008*(1+t)))
      (show z/t+1/(1008*(1+t))≤(z+1)/t by rw [add_div]; exact add_le_add le_rfl hr) 2
    rw [div_pow] at hsq
    have he : -A/t^2≤ -24*(z/t+1/(1008*(1+t)))^2 := by
      calc -A/t^2 = -24*((z+1)^2/t^2) := by dsimp only [A]; ring
           _ ≤ _ := mul_le_mul_of_nonpos_left hsq (by norm_num)
    have hh := mul_le_mul (pow_le_pow_left₀ hK.le hb 48) (exp_le_exp.mpr he) (exp_pos _).le (by positivity)
    linarith only [hh]
  · intro t ht
    have ht' := zero_lt_one.trans_le ht
    rw [hformula ht']
    have hb : K/t ≤ 2*K/(1+t) := by
      apply (div_le_div_iff₀ ht' (by positivity)).mpr
      linarith only [mul_le_mul_of_nonneg_left ht hK.le]
    have hz' : z/t≤z := div_le_self hz.le ht
    have hr : 1/(1008*(1+t))≤1 := (div_le_one (by positivity)).mpr (by linarith only [ht])
    have hsq := pow_le_pow_left₀ (by positivity : 0≤z/t+1/(1008*(1+t))) (add_le_add hz' hr) 2
    have he : -A≤ -24*(z/t+1/(1008*(1+t)))^2 := by dsimp only [A]; linarith only [hsq]
    have hh := mul_le_mul (pow_le_pow_left₀ (div_nonneg hK.le ht'.le) hb 48)
      (exp_le_exp.mpr he) (exp_pos _).le (by positivity)
    rw [div_pow] at hh
    calc K^48/40*exp (-A)/t^48 = K^48/t^48*exp (-A)/40 := by ring
         _ ≤ _ := div_le_div_of_nonneg_right hh (by norm_num)

#print axioms gaussian_prescribed_excess
#print axioms prescribed_excess_scales
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
