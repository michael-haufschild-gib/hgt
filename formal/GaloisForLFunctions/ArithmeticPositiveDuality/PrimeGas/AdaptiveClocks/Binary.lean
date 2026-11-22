import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.Precision
import GaloisForLFunctions.RHTower.Sieve.ChordalSeparation

/-!
# Energy-dependent resolution of the two-copy gas

The allowed chord distance is a fixed positive calibration times an inverse
power of the product of the occupation labels. The same exponential weight,
at the real part of the inverse temperature, is the absolute heat weight.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks

open CopyExchange SampledClocks
open scoped Classical NNReal

abbrev Pair := ℕ+ × ℕ+

def weight (σ : ℝ) (p : Pair) : ℝ := Real.exp (-σ * (energy p.1 + energy p.2))

theorem energy_nonneg (n : ℕ+) : 0 ≤ energy n := Real.log_nonneg (by exact_mod_cast n.pos)

theorem exp_energy (n : ℕ+) : Real.exp (energy n) = (n : ℕ) := Real.exp_log (Nat.cast_pos.mpr n.pos)

theorem energy_mono {m n : ℕ+} (h : m ≤ n) : energy m ≤ energy n :=
  Real.log_le_log (Nat.cast_pos.mpr m.pos) (by exact_mod_cast h)

theorem weight_power (σ : ℝ) (p : Pair) :
    weight σ p = (((p.1 * p.2 : ℕ+) : ℕ) : ℝ) ^ (-σ) := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (p.1*p.2).pos)]
  change Real.exp _ = Real.exp (energy (p.1*p.2) * -σ)
  rw [energy_mul,mul_comm]

theorem single_summable_iff (ρ : ℝ) :
    (Summable fun n : ℕ+ => Real.exp (-ρ * energy n)) ↔ 1 < ρ := by
  simpa only [norm_heat,Complex.ofReal_re] using heat_abs_summable (ρ : ℂ)

/-- Sampling time, chord calibration and exponent of energy-dependent precision. -/
structure Clock where
  time : ℝ
  scale : {r : ℝ // 0 < r}
  exponent : ℝ≥0

namespace Clock

variable (M : Clock)

def Passes (p : Pair) : Prop :=
  dist (clockPhase M.time p.1) (clockPhase M.time p.2) < M.scale.val * weight M.exponent p

abbrev Word := {p : Pair // M.Passes p}

def gate (x : Bool → ℕ+) : Prop := M.Passes (x false,x true)

theorem gate_iff (x : Bool → ℕ+) : M.gate x ↔
    dist ((binary M.time).phase () x) 1 < M.scale.val *
      (((x false * x true : ℕ+) : ℕ) : ℝ)^(-(M.exponent : ℝ)) := by
  rw [Network.phase_distance,← weight_power (M.exponent : ℝ) (x false,x true)]
  rfl

theorem passes_swap (p : Pair) : M.Passes p.swap ↔ M.Passes p := by
  change (dist _ _ < _ * Real.exp (-(M.exponent : ℝ) * (energy p.2 + energy p.1))) ↔ _
  rw [add_comm (energy p.2),dist_comm]
  rfl

theorem passes_diag (n : ℕ+) : M.Passes (n,n) := by
  unfold Passes
  rw [dist_self]
  exact mul_pos M.scale.property (Real.exp_pos _)

abbrev HeatSum (σ : ℝ) := Summable fun x : M.Word => weight σ x.val

private def words : {x // M.gate x} ≃ M.Word where
  toFun x := ⟨(x.val false,x.val true),x.property⟩
  invFun p := ⟨fun b => cond b p.val.2 p.val.1,p.property⟩
  left_inv x := Subtype.ext (funext fun b => by cases b <;> rfl)
  right_inv _ := rfl

/-- Absolute heat summability on label pairs is exactly trace-class realizability on the sector. -/
theorem heat_iff (s : ℂ) : HasSectorHeat M.gate s ↔ M.HeatSum s.re := by
  rw [sectorHeat_iff,HeatSum,← M.words.summable_iff (f := fun x : M.Word => weight s.re x.val)]
  have hw (x : {x // M.gate x}) : ‖wordHeat s x.val‖ = weight s.re (M.words x).val := by
    rw [Network.wordHeat_norm,Fintype.sum_bool]
    change Real.exp (-s.re * (energy (x.val true) + energy (x.val false))) = _
    rw [add_comm]
    rfl
  exact summable_congr hw

end Clock

/-- Chord distance records the absolute half-angle sine of the relative logarithmic clock. -/
theorem chord (t : ℝ) (a b : ℕ+) :
    dist (clockPhase t a) (clockPhase t b) = 2 * |Real.sin (t*(energy a-energy b)/2)| := by
  let x (k : Bool) : ℕ+ := cond k b a
  have h := (binary t).phase_distance () x
  change dist (Circle.exp (t*(energy a-energy b))) 1 = dist (clockPhase t a) (clockPhase t b) at h
  rw [← h]
  change dist (Complex.exp (((t*(energy a-energy b) : ℝ) : ℂ)*Complex.I)) (1:ℂ) = _
  rw [dist_eq_norm,_root_.RHTower.Sieve.norm_exp_I_sub_one]

theorem chord_le (t : ℝ) (a b : ℕ+) :
    dist (clockPhase t a) (clockPhase t b) ≤ |t| *|energy a-energy b| := by
  rw [chord]
  have h := Real.abs_sin_le_abs (x := t*(energy a-energy b)/2)
  rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith only [h]

#print axioms weight_power
#print axioms Clock.gate_iff
#print axioms Clock.heat_iff
#print axioms chord

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks
