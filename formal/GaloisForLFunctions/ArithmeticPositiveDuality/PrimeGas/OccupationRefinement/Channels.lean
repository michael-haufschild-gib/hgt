import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Probabilities
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting.Isometry

/-! # Coherent routing with three output capacities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement

open CoassociativeSplitting

/-- The complex continuation of the classical routing probability. -/
def amplitude (s : ℂ) (u v : ℝ) : Kernel := fun a b =>
  Complex.exp (s*(Real.log (probability u v a.val b.val):ℂ))

theorem exchange (s : ℂ) (u v : ℝ) (a b : ℕ+) : amplitude s u v a b=amplitude s v u b a := by
  simp only [amplitude,probability,add_comm v u,mul_comm b.val a.val,mul_comm (weight v b.val) (weight u a.val)]

private theorem prob_assoc {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (a b c : ℕ+) :
    probability (u+v) w (a*b).val c.val * probability u v a.val b.val =
    probability u (v+w) a.val (b*c).val * probability v w b.val c.val := by
  have hab := (weight_pos (u+v) (add_pos hu hv) (a*b)).ne'
  have hbc := (weight_pos (v+w) (add_pos hv hw) (b*c)).ne'
  simp only [PNat.mul_coe] at hab hbc ⊢
  simp only [probability,add_assoc,mul_assoc a.val b.val c.val]
  field_simp [hab,hbc]

/-- The intermediate probability cancels under either bracketing, including its phase. -/
theorem associative (s : ℂ) {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (a b c : ℕ+) :
    amplitude s (u+v) w (a*b) c * amplitude s u v a b =
    amplitude s u (v+w) a (b*c) * amplitude s v w b c := by
  simp only [amplitude,←Complex.exp_add,←mul_add,←Complex.ofReal_add]
  rw [←Real.log_mul (probability_pos (add_pos hu hv) hw (a*b) c).ne' (probability_pos hu hv a b).ne',
    ←Real.log_mul (probability_pos hu (add_pos hv hw) a (b*c)).ne' (probability_pos hv hw b c).ne',
    prob_assoc hu hv hw]

theorem wave_associative (s : ℂ) {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (f : Gas) (a b c : ℕ+) :
    amplitude s u v a b * wave (amplitude s (u+v) w) f (a*b,c) =
    amplitude s v w b c * wave (amplitude s u (v+w)) f (a,b*c) := by
  unfold wave
  rw [mul_assoc a b c]
  linear_combination f (a*(b*c)) * associative s hu hv hw a b c

theorem norm_sq (s : ℂ) {u v : ℝ} (hu : 0<u) (hv : 0<v) (a b : ℕ+) :
    ‖amplitude s u v a b‖^2=(probability u v a.val b.val)^(2*s.re) := by
  rw [amplitude,Complex.norm_exp,sq,←Real.exp_add,Real.rpow_def_of_pos (probability_pos hu hv a b)]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  congr 1
  ring

#print axioms exchange
#print axioms associative
#print axioms wave_associative
#print axioms norm_sq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement
