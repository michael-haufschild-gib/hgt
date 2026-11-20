import GaloisForLFunctions.HTGeometry.HelsonEulerMultipliable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The holomorphic Euler correction to the density series

On Re w ≥ a > 0 each retained prime contributes at most 3 p⁻¹⁻ᵃ
to the absolute factor error. The same majorant works for every modulus.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Filter Set GaloisForLFunctions.HTGeometry
open scoped Topology
noncomputable section

/-- The deviation of a single Euler factor from one in (2.11). -/
def densityIncrement (N : ℕ) (p : Nat.Primes) (w : ℂ) : ℂ :=
  if 2 < (p : ℕ) ∧ ¬(p : ℕ) ∣ N then ((p : ℕ) : ℂ) ^ (-w) / ((p : ℂ) - 2) else 0

def densityEuler (N : ℕ) (w : ℂ) : ℂ := ∏' p : Nat.Primes, (1 + densityIncrement N p w)

theorem densityIncrement_differentiable (N : ℕ) (p : Nat.Primes) :
    Differentiable ℂ (densityIncrement N p) := by
  unfold densityIncrement
  split_ifs
  · have hp : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
    fun_prop (disch := exact Or.inl hp)
  · exact differentiable_const _

theorem norm_densityIncrement_le (N : ℕ) (p : Nat.Primes) {a : ℝ} {w : ℂ} (hw : a ≤ w.re) :
    ‖densityIncrement N p w‖ ≤ 3 * ((p : ℕ) : ℝ) ^ (-(1 + a)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_lt.le
  unfold densityIncrement
  split_ifs with he
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast he.1
    have hp2 : 0 < (p : ℝ) - 2 := by linarith only [hp3]
    have hn : ‖((p : ℕ) : ℂ) - 2‖ = (p : ℝ) - 2 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp2]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re, hn,
      show -(1 + a) = -a - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
    calc
      ((p : ℕ) : ℝ) ^ (-w.re) / ((p : ℝ) - 2) ≤ ((p : ℕ) : ℝ) ^ (-a) / ((p : ℝ) - 2) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hw)) hp2.le
      _ ≤ 3 * (((p : ℕ) : ℝ) ^ (-a) / (p : ℝ)) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hp2 hp0]
        have hm := mul_nonneg (Real.rpow_nonneg hp0.le (-a)) (sub_nonneg.mpr hp3)
        linarith only [hm]
  · rw [norm_zero]
    positivity

/-- Local uniform convergence with a majorant independent of N. -/
theorem hasProdLocallyUniformlyOn_densityEuler (N : ℕ) {a : ℝ} (ha : 0 < a) :
    HasProdLocallyUniformlyOn (fun p w => 1 + densityIncrement N p w)
      (densityEuler N) {w : ℂ | a < w.re} :=
  Summable.hasProdLocallyUniformlyOn_one_add (isOpen_lt continuous_const Complex.continuous_re)
    ((summable_prime_rpow_neg (show 1 < 1 + a by linarith)).mul_left 3)
    (.of_forall fun p w hw => norm_densityIncrement_le N p (le_of_lt hw))
    (fun p => (densityIncrement_differentiable N p).continuous.continuousOn)

theorem densityEuler_differentiableAt (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (densityEuler N) w := by
  let a := w.re / 2
  have ha : 0 < a := half_pos hw
  have hopen : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.differentiableAt (s := {z : ℂ | a < z.re}) _
    (hopen.mem_nhds (half_lt_self hw))
  apply (hasProdLocallyUniformlyOn_densityEuler N ha).differentiableOn _ hopen
  filter_upwards with P
  simpa only [Finset.prod_fn] using DifferentiableOn.finsetProd
    (f := fun p w => 1 + densityIncrement N p w)
    (s := {z : ℂ | a < z.re}) (u := P) fun p _ =>
      (differentiable_const (1 : ℂ)).differentiableOn.add (densityIncrement_differentiable N p).differentiableOn

#print axioms densityEuler_differentiableAt
end
end GaloisForLFunctions.Goldbach.LiLiu
