import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Boundary
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ObservationDepth

/-!
# Finite fixed-precision clock readings at each occupation

The number of doublings is the integer part of α log₂(ab). Angular
halving sandwiches the protocol between two positive calibrations of
the power-law chord gate. Hence both have the same heat domain.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks

open SampledClocks
open scoped Classical NNReal

structure Schedule where
  time : ℝ
  exponent : ℝ≥0
  angle : {θ : ℝ // 0 < θ ∧ θ ≤ 2*Real.pi/3}

namespace Schedule

variable (D : Schedule)

def depth (p : Pair) := ⌊(D.exponent:ℝ)*(energy p.1+energy p.2)/Real.log 2⌋₊

private def growth (p : Pair) := Real.exp ((D.exponent:ℝ)*(energy p.1+energy p.2))

private theorem growth_inv (p : Pair) : weight D.exponent p = (D.growth p)⁻¹ := by
  rw [weight,neg_mul,Real.exp_neg,growth]

private theorem horizon (p : Pair) :
    (2:ℝ)^(D.depth p) ≤ D.growth p ∧ D.growth p < 2*(2:ℝ)^(D.depth p) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := (D.exponent:ℝ)*(energy p.1+energy p.2)
  have hA : 0 ≤ A := mul_nonneg D.exponent.property (add_nonneg (energy_nonneg _) (energy_nonneg _))
  have h₁ : (D.depth p:ℝ)*Real.log 2 ≤ A := (le_div_iff₀ hl).mp (Nat.floor_le (div_nonneg hA hl.le))
  have h₂ : A < ((D.depth p:ℝ)+1)*Real.log 2 := (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one _)
  have hp : Real.exp ((D.depth p:ℝ)*Real.log 2) = (2:ℝ)^(D.depth p) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  refine ⟨hp ▸ Real.exp_le_exp.mpr h₁,?_⟩
  have hh := Real.exp_lt_exp.mpr h₂
  rw [add_mul,one_mul,Real.exp_add,hp,Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm] at hh
  exact hh

/-- The longest time multiplier is within a factor two of the chosen power of the energy label. -/
theorem horizon_bounds (p : Pair) :
    (2:ℝ)^(D.depth p) ≤ (((p.1*p.2:ℕ+):ℕ):ℝ)^(D.exponent:ℝ) ∧
      (((p.1*p.2:ℕ+):ℕ):ℝ)^(D.exponent:ℝ) < 2*(2:ℝ)^(D.depth p) := by
  have he : D.growth p = weight (-(D.exponent:ℝ)) p := by simp [growth,weight]
  have hw := weight_power (-(D.exponent:ℝ)) p
  rw [neg_neg] at hw
  simpa only [he,hw] using D.horizon p

/-- Angular aperture left after all doublings on this occupation. -/
def effectiveAngle (p : Pair) := D.angle.val/(2:ℝ)^(D.depth p)

/-- Effective chord tolerance at the initial sampling time. -/
def radius (p : Pair) := 2*|Real.sin (D.effectiveAngle p/2)|

private def lower : Clock := ⟨D.time,⟨2/Real.pi*D.angle.val,mul_pos (by positivity) D.angle.property.1⟩,D.exponent⟩

private def upper : Clock := ⟨D.time,⟨2*D.angle.val,mul_pos (by norm_num) D.angle.property.1⟩,D.exponent⟩

private theorem calibrations (p : Pair) :
    D.lower.scale.val*weight D.exponent p ≤ D.radius p ∧ D.radius p ≤ D.upper.scale.val*weight D.exponent p := by
  let P := (2:ℝ)^(D.depth p)
  let u := D.effectiveAngle p
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hu : 0 ≤ u := div_nonneg D.angle.property.1.le hP0.le
  have huπ : u ≤ Real.pi := (div_le_self D.angle.property.1.le hP).trans
    (D.angle.property.2.trans (by linarith only [Real.pi_pos]))
  have h₁ : D.angle.val*weight D.exponent p ≤ u := by
    rw [D.growth_inv,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left D.angle.property.1.le hP0 (D.horizon p).1
  have h₂ : u ≤ 2*D.angle.val*weight D.exponent p := by
    rw [D.growth_inv,← div_eq_mul_inv]
    apply (div_le_div_iff₀ hP0 (Real.exp_pos _)).mpr
    have h := mul_le_mul_of_nonneg_left (D.horizon p).2.le D.angle.property.1.le
    calc
      _ ≤ D.angle.val*(2*P) := h
      _ = _ := by ring
  have hj := (Real.mul_le_sin (by linarith only [hu] : 0 ≤ u/2)
    (by linarith only [huπ] : u/2 ≤ Real.pi/2)).trans (le_abs_self _)
  have hs := Real.abs_sin_le_abs (x := u/2)
  rw [abs_of_nonneg (by linarith only [hu] : 0 ≤ u/2)] at hs
  constructor
  · change (2/Real.pi*D.angle.val)*weight D.exponent p ≤ 2*|Real.sin (u/2)|
    rw [mul_assoc]
    apply (mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 2/Real.pi)).trans
    linarith only [hj]
  · change 2*|Real.sin (u/2)| ≤ 2*D.angle.val*weight D.exponent p
    exact le_trans (by linarith only [hs] : 2*|Real.sin (u/2)| ≤ u) h₂

def accepts (x : Bool → ℕ+) : Prop := (binary D.time).Prefix (Real.sqrt (aperture D.angle.val))
  (D.depth (x false,x true)+1) x

private theorem aperture_eq (u : ℝ) : aperture u = (2*|Real.sin (u/2)|)^2 := by
  have h := HTGeometry.normSq_exp_mul_I_sub_one u
  rw [_root_.RHTower.Sieve.norm_exp_I_sub_one] at h
  exact h.symm

theorem accepts_iff (x : Bool → ℕ+) : D.accepts x ↔
    dist (clockPhase D.time (x false)) (clockPhase D.time (x true)) < D.radius (x false,x true) := by
  let θ : Set.Icc 0 (2*Real.pi/3) := ⟨D.angle.val,D.angle.property.1.le,D.angle.property.2⟩
  rw [accepts,(binary D.time).prefix_angular_resolution θ]
  have he : chordSq ((binary D.time).phase () x) =
      (dist (clockPhase D.time (x false)) (clockPhase D.time (x true)))^2 := by
    rw [chordSq,Network.phase_distance]
    rfl
  have hr : 0 ≤ D.radius (x false,x true) := mul_nonneg (by norm_num) (abs_nonneg _)
  constructor
  · intro h
    have hh := h ()
    rw [he,aperture_eq] at hh
    exact (sq_lt_sq₀ dist_nonneg hr).mp hh
  · intro h e
    cases e
    rw [he,aperture_eq]
    exact (sq_lt_sq₀ dist_nonneg hr).mpr h

private theorem sector_restrict {P Q : (Bool → ℕ+) → Prop} (inc : ∀ x, P x → Q x) (s : ℂ)
    (h : HasSectorHeat Q s) : HasSectorHeat P s := by
  let f (x : {x // P x}) : {x // Q x} := ⟨x.val,inc x.val x.property⟩
  have hi : Function.Injective f := fun _ _ he => Subtype.ext (congrArg (fun y : {x // Q x} => y.val) he)
  exact (sectorHeat_iff _ _).mpr (((sectorHeat_iff _ _).mp h).comp_injective (i := f) hi)

/-- Exact heat domain for fixed hardware tolerance and occupation-dependent observation counts. -/
theorem trace_iff (s : ℂ) : HasSectorHeat D.accepts s ↔
    (if D.time = 0 then 1 else max (1/2:ℝ) (1-(D.exponent:ℝ))) < s.re := by
  constructor
  · intro h
    apply (D.lower.trace_iff s).mp
    apply sector_restrict _ s h
    intro x hx
    exact (D.accepts_iff x).mpr (hx.trans_le (D.calibrations (x false,x true)).1)
  · intro h
    apply sector_restrict (Q := D.upper.gate) _ s ((D.upper.trace_iff s).mpr h)
    intro x hx
    exact ((D.accepts_iff x).mp hx).trans_le (D.calibrations (x false,x true)).2

/-- Exactly these finite observation schedules detect conservation of probability under splitting. -/
theorem detects_split_iff :
    (∀ s : ℂ, (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ¬HasSectorHeat D.accepts s ∧ ∀ δ : ℝ, 0 < δ → HasSectorHeat D.accepts (s+(δ:ℂ))) ↔
        D.time ≠ 0 ∧ 1/2 ≤ (D.exponent:ℝ) := by
  have same (s : ℂ) : HasSectorHeat D.accepts s ↔ HasSectorHeat D.upper.gate s :=
    (D.trace_iff s).trans (D.upper.trace_iff s).symm
  simp only [same]
  exact D.upper.detects_split_iff

#print axioms detects_split_iff
#print axioms horizon_bounds
#print axioms accepts_iff
#print axioms trace_iff

end Schedule
end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks
