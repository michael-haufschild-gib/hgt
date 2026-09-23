import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOpticalTail
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Exact radial characteristic contacts of the complementary reduced BM sources. -/
namespace RHTower.D4BMZeroDelayCurrent
open MeasureTheory Set
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def kappa (s : ℂ) : ℂ := s*(s-1)/4
def eta (s : ℂ) : ℂ := (2*s+1)*(2*s+2)
def partner (s : ℂ) : ℂ := -s-3
def delta (s : ℂ) : ℂ := 2*s+3

def profile (s : ℂ) (u : ℝ) : ℂ := Complex.exp (2*s*(Real.log (1+u):ℂ))
def sourceWeight (s : ℂ) (u : ℝ) : ℂ := (u:ℂ)*profile s u
def onsetCoefficient (s : ℂ) (u : ℝ) : ℂ :=
  2*kappa s*(u:ℂ)*(3+delta s*(u:ℂ))/(1+(u:ℂ))
def onsetWeight (s : ℂ) (u : ℝ) : ℂ := sourceWeight s u*onsetCoefficient s u
def onsetPrimitive (s : ℂ) (u : ℝ) : ℂ := 2*kappa s*(u:ℂ)^(3 : ℕ)*profile s u
def sourceMoment (s : ℂ) (u : ℝ) : ℂ := ∫ x in (0:ℝ)..u, sourceWeight s x
def onsetMoment (s : ℂ) (u : ℝ) : ℂ := ∫ x in (0:ℝ)..u, onsetWeight s x
def firstOnsetMoment (s : ℂ) (u : ℝ) : ℂ := ∫ x in (0:ℝ)..u, (x:ℂ)*onsetWeight s x

/-- The positive-base radial profile is the literal original source amplitude
at zero transform frequency, with its independent amplitude restored. -/
theorem physical_radial_amplitude (s a : ℂ) (x : ℝ) :
    D4BMJointSource.sourceAmplitude s 0 a 1 x = a^(2 : ℕ)*profile s (D4BMJointSource.radialUnit x) := by
  have hp := D4BMJointSource.radialUnit_add_one_pos x
  have hn : ((1+D4BMJointSource.radialUnit x:ℝ):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  simp only [D4BMJointSource.sourceAmplitude,D4BMLaplaceRadial.power,
    zero_mul,Complex.exp_zero,one_mul,mul_one]
  rw [Complex.cpow_def_of_ne_zero hn,← Complex.ofReal_log hp.le]
  dsimp only [profile]
  rw [mul_comm (Real.log (1+D4BMJointSource.radialUnit x):ℂ) (2*s),mul_comm]

/-- The coefficient integrated below is the existing full wave-image remainder,
with its original source amplitude, fixed onset and onset derivative. -/
theorem physical_reduced_source (s a : ℂ) (tau x : ℝ) :
    D4BMJointSource.timeReducedCoefficient s a tau x =
      let u : ℂ := D4BMJointSource.radialUnit x
      D4BMJointSource.sourceAmplitude s 0 a 1 x*Complex.exp (2*s*((tau+x:ℝ):ℂ))*
        (-u*(1-u^(2 : ℕ))*(eta s*(Real.smoothTransition (tau+x):ℂ)-
          onsetCoefficient s (D4BMJointSource.radialUnit x)*
            ((deriv Real.smoothTransition (tau+x):ℝ):ℂ))) := by
  rw [D4BMReducedOpticalTail.timeReducedCoefficient_closed]
  have hn : 1+(D4BMJointSource.radialUnit x:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (D4BMJointSource.radialUnit_add_one_pos x))
  dsimp [eta,onsetCoefficient,kappa,delta]
  field_simp [hn]
  ring

private theorem profile_derivative (s : ℂ) {u : ℝ} (hu : -1 < u) :
    HasDerivAt (profile s) (profile s u*(2*s/(1+(u:ℂ)))) u := by
  have hn : 1+u ≠ 0 := by linarith
  have h := ((Real.hasDerivAt_log hn).comp u ((hasDerivAt_id u).const_add 1)).ofReal_comp
  apply (h.const_mul (2*s)).cexp.congr_deriv
  dsimp only [Function.comp_def, profile]
  push_cast
  ring

private theorem profile_continuous (s : ℂ) : ContinuousOn (profile s) (Ioi (-1:ℝ)) :=
  fun _ hu => (profile_derivative s hu).continuousAt.continuousWithinAt

private theorem sourceWeight_continuous (s : ℂ) : ContinuousOn (sourceWeight s) (Ioi (-1:ℝ)) :=
  Complex.continuous_ofReal.continuousOn.mul (profile_continuous s)

private theorem onsetWeight_continuous (s : ℂ) : ContinuousOn (onsetWeight s) (Ioi (-1:ℝ)) := by
  apply (sourceWeight_continuous s).mul
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro u hu
    change -1 < u at hu
    exact_mod_cast (show (1:ℝ)+u ≠ 0 by linarith [hu])

private theorem interval_subset {u : ℝ} (hu : 0 ≤ u) : uIcc (0:ℝ) u ⊆ Ioi (-1:ℝ) := by
  rw [uIcc_of_le hu]
  intro x hx
  exact lt_of_lt_of_le (by norm_num) hx.1

private theorem integral_derivative (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi (-1:ℝ)))
    {u : ℝ} (hu : 0 ≤ u) : HasDerivAt (fun y => ∫ x in (0:ℝ)..y, f x) (f u) u := by
  have hm : u ∈ Ioi (-1:ℝ) := by change -1 < u; linarith
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.mono (interval_subset hu)).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf u hm)
    (hf.continuousAt (isOpen_Ioi.mem_nhds hm))

private theorem sourceMoment_derivative (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (sourceMoment s) (sourceWeight s u) u :=
  integral_derivative _ (sourceWeight_continuous s) hu

private theorem onsetMoment_derivative (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (onsetMoment s) (onsetWeight s u) u :=
  integral_derivative _ (onsetWeight_continuous s) hu

private theorem firstOnsetMoment_derivative (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (firstOnsetMoment s) ((u:ℂ)*onsetWeight s u) u :=
  integral_derivative _ (Complex.continuous_ofReal.continuousOn.mul (onsetWeight_continuous s)) hu

private theorem sourceMoment_continuous (s : ℂ) {a : ℝ} :
    ContinuousOn (sourceMoment s) (Icc (0:ℝ) a) :=
  fun _ hu => (sourceMoment_derivative s hu.1).continuousAt.continuousWithinAt

private theorem onsetMoment_continuous (s : ℂ) {a : ℝ} :
    ContinuousOn (onsetMoment s) (Icc (0:ℝ) a) :=
  fun _ hu => (onsetMoment_derivative s hu.1).continuousAt.continuousWithinAt

private theorem firstOnsetMoment_continuous (s : ℂ) {a : ℝ} :
    ContinuousOn (firstOnsetMoment s) (Icc (0:ℝ) a) :=
  fun _ hu => (firstOnsetMoment_derivative s hu.1).continuousAt.continuousWithinAt

private theorem sourceWeight_continuous_interval (s : ℂ) {a : ℝ} :
    ContinuousOn (sourceWeight s) (Icc (0:ℝ) a) :=
  (sourceWeight_continuous s).mono (fun _ hx => lt_of_lt_of_le (by norm_num) hx.1)

private theorem onsetWeight_continuous_interval (s : ℂ) {a : ℝ} :
    ContinuousOn (onsetWeight s) (Icc (0:ℝ) a) :=
  (onsetWeight_continuous s).mono (fun _ hx => lt_of_lt_of_le (by norm_num) hx.1)

private theorem onsetPrimitive_derivative (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (onsetPrimitive s) (onsetWeight s u) u := by
  have hd := profile_derivative s (show -1<u by linarith)
  have hn : 1+(u:ℂ) ≠ 0 := by exact_mod_cast (show (1:ℝ)+u ≠ 0 by linarith)
  apply ((((hasDerivAt_id u).ofReal_comp.pow 3).const_mul (2*kappa s)).mul hd).congr_deriv
  dsimp [onsetWeight,sourceWeight,onsetCoefficient,delta]
  field_simp [hn]
  ring

/-- The original onset coefficient integrates to the cubic radial lift, at every physical radius. -/
theorem onsetMoment_eq (s : ℂ) (u : Set.Ici (0:ℝ)) :
    onsetMoment s u = onsetPrimitive s u := by
  have hi : IntervalIntegrable (onsetWeight s) volume 0 u :=
    ((onsetWeight_continuous s).mono (interval_subset u.property)).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => onsetPrimitive_derivative s (by
      rw [uIcc_of_le u.property] at hx
      exact hx.1)) hi
  simpa [onsetMoment,onsetPrimitive] using h

private theorem sourceMoment_zero (s : ℂ) : sourceMoment s 0 = 0 := by simp [sourceMoment]
private theorem onsetMoment_zero (s : ℂ) : onsetMoment s 0 = 0 := by simp [onsetMoment]
private theorem firstOnsetMoment_zero (s : ℂ) : firstOnsetMoment s 0 = 0 := by simp [firstOnsetMoment]

def contactQDensity (s t : ℂ) (u w : ℝ) : ℂ :=
  eta s*sourceWeight s u*onsetWeight t w-eta t*onsetWeight s u*sourceWeight t w+
    (s-t)*onsetWeight s u*onsetWeight t w-
  (eta t*sourceWeight t u*onsetWeight s w-eta s*onsetWeight t u*sourceWeight s w+
    (t-s)*onsetWeight t u*onsetWeight s w)

def contactDeltaDensity (s t : ℂ) (u w : ℝ) : ℂ :=
  ((u:ℂ)-(w:ℂ))/2*(onsetWeight s u*onsetWeight t w-onsetWeight t u*onsetWeight s w)

def terminalDensity (s t : ℂ) (u w : ℝ) : ℂ :=
  onsetWeight s u*onsetWeight t w-onsetWeight t u*onsetWeight s w

private theorem primitive_FTC (f g : ℝ → ℂ) {u : ℝ} (hu : 0 ≤ u)
    (hd : ∀ x ∈ Icc (0:ℝ) u, HasDerivAt f (g x) x)
    (hc : ContinuousOn g (Icc (0:ℝ) u)) : (∫ x in (0:ℝ)..u, g x) = f u-f 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · simpa only [uIcc_of_le hu] using hd
  · apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hu] using hc

private theorem inner_contactQ (s t : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ w in (0:ℝ)..u, contactQDensity s t u w) =
      eta s*sourceWeight s u*onsetMoment t u-eta t*onsetWeight s u*sourceMoment t u+
        (s-t)*onsetWeight s u*onsetMoment t u-
      (eta t*sourceWeight t u*onsetMoment s u-eta s*onsetWeight t u*sourceMoment s u+
        (t-s)*onsetWeight t u*onsetMoment s u) := by
  let P (w : ℝ) :=
    eta s*sourceWeight s u*onsetMoment t w-eta t*onsetWeight s u*sourceMoment t w+
      (s-t)*onsetWeight s u*onsetMoment t w-
    (eta t*sourceWeight t u*onsetMoment s w-eta s*onsetWeight t u*sourceMoment s w+
      (t-s)*onsetWeight t u*onsetMoment s w)
  have hd (w : ℝ) (hw : w ∈ Icc (0:ℝ) u) : HasDerivAt P (contactQDensity s t u w) w := by
    exact ((((onsetMoment_derivative t hw.1).const_mul _).sub
      ((sourceMoment_derivative t hw.1).const_mul _)).add
      ((onsetMoment_derivative t hw.1).const_mul _)).sub
      ((((onsetMoment_derivative s hw.1).const_mul _).sub
      ((sourceMoment_derivative s hw.1).const_mul _)).add
      ((onsetMoment_derivative s hw.1).const_mul _))
  have hc : ContinuousOn (contactQDensity s t u) (Icc (0:ℝ) u) := by
    exact ((((onsetWeight_continuous_interval t).const_mul _).sub
      ((sourceWeight_continuous_interval t).const_mul _)).add
      ((onsetWeight_continuous_interval t).const_mul _)).sub
      ((((onsetWeight_continuous_interval s).const_mul _).sub
      ((sourceWeight_continuous_interval s).const_mul _)).add
      ((onsetWeight_continuous_interval s).const_mul _))
  have he := primitive_FTC P (contactQDensity s t u) hu hd hc
  simpa [P,sourceMoment_zero,onsetMoment_zero] using he

/-- The complete antisymmetrized zeroth-jet contact is a product of original radial endpoint moments. -/
theorem contactQ_integral (s t : ℂ) :
    (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, contactQDensity s t u w) =
      eta s*sourceMoment s 1*onsetMoment t 1-
        eta t*onsetMoment s 1*sourceMoment t 1+
        (s-t)*onsetMoment s 1*onsetMoment t 1 := by
  let P (u : ℝ) := eta s*sourceMoment s u*onsetMoment t u-
      eta t*onsetMoment s u*sourceMoment t u+
      (s-t)*onsetMoment s u*onsetMoment t u
  let F (u : ℝ) := eta s*sourceWeight s u*onsetMoment t u-
      eta t*onsetWeight s u*sourceMoment t u+(s-t)*onsetWeight s u*onsetMoment t u-
    (eta t*sourceWeight t u*onsetMoment s u-eta s*onsetWeight t u*sourceMoment s u+
      (t-s)*onsetWeight t u*onsetMoment s u)
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : HasDerivAt P (F u) u := by
    apply (((((sourceMoment_derivative s hu.1).const_mul _).mul
      (onsetMoment_derivative t hu.1)).sub
      (((onsetMoment_derivative s hu.1).const_mul _).mul (sourceMoment_derivative t hu.1))).add
      (((onsetMoment_derivative s hu.1).const_mul _).mul (onsetMoment_derivative t hu.1))).congr_deriv
    dsimp [F]
    ring
  have hc : ContinuousOn F (Icc (0:ℝ) 1) := by
    exact (((((sourceWeight_continuous_interval s).const_mul _).mul
      (onsetMoment_continuous t)).sub
      (((onsetWeight_continuous_interval s).const_mul _).mul (sourceMoment_continuous t))).add
      (((onsetWeight_continuous_interval s).const_mul _).mul (onsetMoment_continuous t))).sub
      (((((sourceWeight_continuous_interval t).const_mul _).mul
      (onsetMoment_continuous s)).sub
      (((onsetWeight_continuous_interval t).const_mul _).mul (sourceMoment_continuous s))).add
      (((onsetWeight_continuous_interval t).const_mul _).mul (onsetMoment_continuous s)))
  have he := primitive_FTC P F (by norm_num : (0:ℝ) ≤ 1) hd hc
  have hi : (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, contactQDensity s t u w) =
      ∫ u in (0:ℝ)..1, F u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact inner_contactQ s t hu.1
  rw [hi,he]
  simp [P,sourceMoment_zero,onsetMoment_zero]

private theorem inner_contactDelta (s t : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ w in (0:ℝ)..u, contactDeltaDensity s t u w) =
      (onsetWeight s u*((u:ℂ)*onsetMoment t u-firstOnsetMoment t u)-
        onsetWeight t u*((u:ℂ)*onsetMoment s u-firstOnsetMoment s u))/2 := by
  let P (w : ℝ) :=
    (onsetWeight s u*((u:ℂ)*onsetMoment t w-firstOnsetMoment t w)-
      onsetWeight t u*((u:ℂ)*onsetMoment s w-firstOnsetMoment s w))/2
  have hd (w : ℝ) (hw : w ∈ Icc (0:ℝ) u) :
      HasDerivAt P (contactDeltaDensity s t u w) w := by
    apply (((((onsetMoment_derivative t hw.1).const_mul (u:ℂ)).sub
      (firstOnsetMoment_derivative t hw.1)).const_mul (onsetWeight s u)).sub
      ((((onsetMoment_derivative s hw.1).const_mul (u:ℂ)).sub
      (firstOnsetMoment_derivative s hw.1)).const_mul (onsetWeight t u))).div_const 2 |>.congr_deriv
    dsimp [contactDeltaDensity]
    ring
  have hc : ContinuousOn (contactDeltaDensity s t u) (Icc (0:ℝ) u) := by
    exact ((continuous_const.sub Complex.continuous_ofReal).div_const 2).continuousOn.mul
      (((onsetWeight_continuous_interval t).const_mul _).sub
        ((onsetWeight_continuous_interval s).const_mul _))
  have he := primitive_FTC P (contactDeltaDensity s t u) hu hd hc
  simpa [P,onsetMoment_zero,firstOnsetMoment_zero] using he

/-- The characteristic first-jet contact is the antisymmetric product of the
first and zeroth original onset moments. -/
theorem contactDelta_integral (s t : ℂ) :
    (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, contactDeltaDensity s t u w) =
      (firstOnsetMoment s 1*onsetMoment t 1-onsetMoment s 1*firstOnsetMoment t 1)/2 := by
  let P (u : ℝ) :=
    (firstOnsetMoment s u*onsetMoment t u-onsetMoment s u*firstOnsetMoment t u)/2
  let F (u : ℝ) :=
    (onsetWeight s u*((u:ℂ)*onsetMoment t u-firstOnsetMoment t u)-
      onsetWeight t u*((u:ℂ)*onsetMoment s u-firstOnsetMoment s u))/2
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : HasDerivAt P (F u) u := by
    apply ((((firstOnsetMoment_derivative s hu.1).mul (onsetMoment_derivative t hu.1)).sub
      ((onsetMoment_derivative s hu.1).mul (firstOnsetMoment_derivative t hu.1))).div_const 2).congr_deriv
    dsimp [F]
    ring
  have hc : ContinuousOn F (Icc (0:ℝ) 1) := by
    exact (((onsetWeight_continuous_interval s).mul
      ((Complex.continuous_ofReal.continuousOn.mul (onsetMoment_continuous t)).sub
        (firstOnsetMoment_continuous t))).sub
      ((onsetWeight_continuous_interval t).mul
      ((Complex.continuous_ofReal.continuousOn.mul (onsetMoment_continuous s)).sub
        (firstOnsetMoment_continuous s)))).div_const 2
  have he := primitive_FTC P F (by norm_num : (0:ℝ) ≤ 1) hd hc
  have hi : (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, contactDeltaDensity s t u w) =
      ∫ u in (0:ℝ)..1, F u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact inner_contactDelta s t hu.1
  rw [hi,he]
  simp [P,onsetMoment_zero,firstOnsetMoment_zero]

private theorem inner_terminal (s t : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ w in (0:ℝ)..u, terminalDensity s t u w) =
      onsetWeight s u*onsetMoment t u-onsetWeight t u*onsetMoment s u := by
  let P (w : ℝ) := onsetWeight s u*onsetMoment t w-onsetWeight t u*onsetMoment s w
  have hd (w : ℝ) (hw : w ∈ Icc (0:ℝ) u) : HasDerivAt P (terminalDensity s t u w) w :=
    ((onsetMoment_derivative t hw.1).const_mul _).sub
      ((onsetMoment_derivative s hw.1).const_mul _)
  have hc : ContinuousOn (terminalDensity s t u) (Icc (0:ℝ) u) :=
    ((onsetWeight_continuous_interval t).const_mul _).sub
      ((onsetWeight_continuous_interval s).const_mul _)
  have he := primitive_FTC P (terminalDensity s t u) hu hd hc
  simpa [P,onsetMoment_zero] using he

private theorem profile_product (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    profile s u*profile (partner s) u = 1/(1+(u:ℂ))^(6 : ℕ) := by
  have hp : 0 < 1+u := by linarith
  have he : Complex.exp (Real.log (1+u):ℂ) = 1+(u:ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp]
    push_cast
    rfl
  rw [profile,profile,← Complex.exp_add]
  have hh : 2*s*(Real.log (1+u):ℂ)+2*partner s*(Real.log (1+u):ℂ) =
      -(6*(Real.log (1+u):ℂ)) := by dsimp [partner]; ring
  rw [hh,Complex.exp_neg]
  have hn : Complex.exp (6*(Real.log (1+u):ℂ)) = (1+(u:ℂ))^(6 : ℕ) := by
    simpa only [Nat.cast_ofNat] using (Complex.exp_nat_mul (Real.log (1+u):ℂ) 6).trans (congrArg (fun z : ℂ => z^(6 : ℕ)) he)
  rw [hn,one_div]

/-- The terminal contact has exactly the radial weight of the retained null-slice lift flux. -/
theorem terminal_radial_density (s : ℂ) (u : Ici (0:ℝ)) :
    onsetWeight s u*onsetMoment (partner s) u-onsetWeight (partner s) u*onsetMoment s u =
      8*delta s*kappa s*kappa (partner s)*(u:ℂ)^(6 : ℕ)/(1+(u:ℂ))^(7 : ℕ) := by
  rw [onsetMoment_eq s u,onsetMoment_eq (partner s) u]
  have hu : 0 ≤ (u:ℝ) := u.property
  have hn : 1+(u:ℂ) ≠ 0 := by exact_mod_cast (show (1:ℝ)+(u:ℝ) ≠ 0 by linarith)
  calc
    _ = 8*delta s*kappa s*kappa (partner s)*(u:ℂ)^(6 : ℕ)/(1+(u:ℂ))*
        (profile s u*profile (partner s) u) := by
      dsimp [onsetWeight,sourceWeight,onsetCoefficient,onsetPrimitive,delta,partner]
      ring
    _ = _ := by
      rw [profile_product s u.property]
      field_simp [hn]

/-- Exact whole-triangle terminal coefficient for the complementary physical branches. -/
theorem terminal_integral (s : ℂ) :
    (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, terminalDensity s (partner s) u w) =
      8*delta s*kappa s*kappa (partner s)*
        (∫ u in (0:ℝ)..1, (u:ℂ)^(6 : ℕ)/(1+(u:ℂ))^(7 : ℕ)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
  dsimp only
  rw [inner_terminal s (partner s) hu.1]
  have h := terminal_radial_density s ⟨u,hu.1⟩
  dsimp only at h
  rw [h]
  ring

/-- The onset endpoint product fixes the lift–lift horizon coefficient, including
its exact normalization, without a condition on the complex frequency. -/
theorem horizon_contact_coefficient (s : ℂ) :
    delta s*onsetMoment s 1*onsetMoment (partner s) 1/2 =
      delta s*((s+1)*(s+2)-2)*((s+1)*(s+2)-6)/512 := by
  have hs := onsetMoment_eq s ⟨1,by norm_num⟩
  have ht := onsetMoment_eq (partner s) ⟨1,by norm_num⟩
  dsimp only at hs ht
  rw [hs,ht]
  have hp := profile_product s (u := 1) (by norm_num)
  calc
    _ = 2*delta s*kappa s*kappa (partner s)*(profile s 1*profile (partner s) 1) := by
      dsimp [onsetPrimitive]
      norm_num
      ring
    _ = _ := by
      rw [hp]
      norm_num
      dsimp [kappa,partner]
      ring

private def nullSlicePrimitive (u : ℝ) : ℂ :=
  (Real.log (1+u):ℂ)+6*(1+(u:ℂ))⁻¹-(15/2:ℂ)*((1+(u:ℂ))⁻¹)^(2 : ℕ)+
    (20/3:ℂ)*((1+(u:ℂ))⁻¹)^(3 : ℕ)-(15/4:ℂ)*((1+(u:ℂ))⁻¹)^(4 : ℕ)+
    (6/5:ℂ)*((1+(u:ℂ))⁻¹)^(5 : ℕ)-(1/6:ℂ)*((1+(u:ℂ))⁻¹)^(6 : ℕ)

private theorem nullSlicePrimitive_derivative {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt nullSlicePrimitive ((u:ℂ)^(6 : ℕ)/(1+(u:ℂ))^(7 : ℕ)) u := by
  have hr : (1:ℝ)+u ≠ 0 := by linarith
  have hn : 1+(u:ℂ) ≠ 0 := by exact_mod_cast hr
  have hl := ((Real.hasDerivAt_log hr).comp u ((hasDerivAt_id u).const_add 1)).ofReal_comp
  have hi := ((hasDerivAt_id u).ofReal_comp.const_add 1).inv hn
  apply ((((((hl.add (hi.const_mul 6)).sub ((hi.pow 2).const_mul (15/2))).add
    ((hi.pow 3).const_mul (20/3))).sub ((hi.pow 4).const_mul (15/4))).add
    ((hi.pow 5).const_mul (6/5))).sub ((hi.pow 6).const_mul (1/6))).congr_deriv
  simp only [Pi.inv_apply,id_eq]
  push_cast
  field_simp [hn]
  ring

/-- Exact integrated null-slice radial coefficient; the integral is finite and
its logarithmic endpoint is retained. -/
theorem nullSlice_integral :
    (∫ u in (0:ℝ)..1, (u:ℂ)^(6 : ℕ)/(1+(u:ℂ))^(7 : ℕ)) = (Real.log 2:ℂ)-1327/1920 := by
  have hc : ContinuousOn (fun u : ℝ => (u:ℂ)^(6 : ℕ)/(1+(u:ℂ))^(7 : ℕ)) (Icc (0:ℝ) 1) := by
    apply (Complex.continuous_ofReal.pow 6).continuousOn.div
      ((continuous_const.add Complex.continuous_ofReal).pow 7).continuousOn
    intro u hu
    apply pow_ne_zero
    have hn : (1:ℝ)+u ≠ 0 := by linarith [hu.1]
    change 1+(u:ℂ) ≠ 0
    exact_mod_cast hn
  have he := primitive_FTC nullSlicePrimitive _ (by norm_num : (0:ℝ) ≤ 1)
    (fun u hu => nullSlicePrimitive_derivative hu.1) hc
  rw [he]
  norm_num [nullSlicePrimitive]
  ring

/-- Closed terminal contact, after the actual complementary source integrations. -/
theorem terminal_integral_closed (s : ℂ) :
    (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, terminalDensity s (partner s) u w) =
      8*delta s*kappa s*kappa (partner s)*((Real.log 2:ℂ)-1327/1920) := by
  rw [terminal_integral,nullSlice_integral]

private def weightedSourcePrimitive (s : ℂ) (u : ℝ) : ℂ :=
  (1+(u:ℂ))*profile s u*((2*s+1)*(u:ℂ)-1)+1

private theorem weightedSourcePrimitive_derivative (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (weightedSourcePrimitive s) (eta s*sourceWeight s u) u := by
  have hn : 1+(u:ℂ) ≠ 0 := by exact_mod_cast (show (1:ℝ)+u ≠ 0 by linarith)
  have hx := (hasDerivAt_id u).ofReal_comp
  apply ((((hx.const_add 1).mul (profile_derivative s (by linarith))).mul
    ((hx.const_mul (2*s+1)).sub_const 1)).add_const 1).congr_deriv
  dsimp [eta,sourceWeight]
  field_simp [hn]
  ring

/-- The original source moment has a division-free endpoint formula, including
all exceptional frequencies at which the polynomial prefactor vanishes. -/
theorem sourceMoment_eta_endpoint (s : ℂ) :
    eta s*sourceMoment s 1 = 1+4*s*profile s 1 := by
  have hc : ContinuousOn (fun u => eta s*sourceWeight s u) (Icc (0:ℝ) 1) :=
    (sourceWeight_continuous_interval s).const_mul _
  have he := primitive_FTC (weightedSourcePrimitive s) _ (by norm_num : (0:ℝ) ≤ 1)
    (fun u hu => weightedSourcePrimitive_derivative s hu.1) hc
  rw [intervalIntegral.integral_const_mul] at he
  change eta s*sourceMoment s 1 = _ at he
  rw [he]
  have hz : profile s 0 = 1 := by simp [profile]
  norm_num [weightedSourcePrimitive,hz]
  ring

/-- Complete zeroth-jet characteristic contact, with both original radial
integrations evaluated and no division by a frequency polynomial. -/
theorem contactQ_integral_closed (s : ℂ) :
    (∫ u in (0:ℝ)..1, ∫ w in (0:ℝ)..u, contactQDensity s (partner s) u w) =
      2*kappa (partner s)*profile (partner s) 1-2*kappa s*profile s 1+
        delta s*((s+1)*(s+2)-2)*((s+1)*(s+2)+2)/256 := by
  rw [contactQ_integral,sourceMoment_eta_endpoint]
  have hs := onsetMoment_eq s ⟨1,by norm_num⟩
  have ht := onsetMoment_eq (partner s) ⟨1,by norm_num⟩
  dsimp only at hs ht
  have he : eta (partner s)*onsetMoment s 1*sourceMoment (partner s) 1 =
      onsetMoment s 1*(1+4*partner s*profile (partner s) 1) := by
    calc
      _ = onsetMoment s 1*(eta (partner s)*sourceMoment (partner s) 1) := by ring
      _ = _ := by rw [sourceMoment_eta_endpoint]
  rw [he,hs,ht]
  have hp := profile_product s (u := 1) (by norm_num)
  calc
    _ = 2*kappa (partner s)*profile (partner s) 1-2*kappa s*profile s 1+
        (8*s*kappa (partner s)-8*partner s*kappa s+
          4*(s-partner s)*kappa s*kappa (partner s))*
          (profile s 1*profile (partner s) 1) := by
      dsimp [onsetPrimitive]
      norm_num
      ring
    _ = _ := by
      rw [hp]
      norm_num
      dsimp [kappa,partner,delta]
      ring

end
end RHTower.D4BMZeroDelayCurrent
