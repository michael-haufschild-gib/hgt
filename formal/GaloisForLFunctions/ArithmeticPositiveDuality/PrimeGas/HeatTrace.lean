import GaloisForLFunctions.HTGeometry.PrimeCompletionHypertranscendenceCollapse
import GaloisForLFunctions.HTGeometry.LpDiagonalOperator
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The logarithmic prime gas

Finite prime occupations index the energy basis of ℓ²(ℕ+). The heat operator in
the trace half-plane factors into two Hilbert–Schmidt half-time propagators.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

abbrev Gas := lp (fun _ : ℕ+ => ℂ) 2

/-- Integer label of a bosonic prime occupation. -/
abbrev label := primeOccupationEquivPNat

theorem label_add (u v : Nat.Primes →₀ ℕ) : label (u + v) = label u * label v := by
  apply PNat.coe_injective
  exact Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

theorem label_one_quantum (p : Nat.Primes) :
    (label (Finsupp.single p 1) : ℕ) = p := by
  change (Finsupp.single p 1).prod (fun q k => (q : ℕ) ^ k) = _
  exact (Finsupp.prod_single_index (h := fun q : Nat.Primes => fun k : ℕ => (q : ℕ) ^ k)
    (pow_zero (p : ℕ))).trans (pow_one _)

def energy (n : ℕ+) : ℝ := Real.log (n : ℕ)

theorem energy_mul (a b : ℕ+) : energy (a * b) = energy a + energy b := by
  simp only [energy, PNat.mul_coe, Nat.cast_mul]
  exact Real.log_mul (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)

/-- Spectral multiplier of the Hamiltonian at complex inverse temperature s. -/
def heat (s : ℂ) (n : ℕ+) : ℂ := Complex.exp (-s * (energy n : ℂ))

theorem heat_add (s w : ℂ) (n : ℕ+) : heat (s + w) n = heat s n * heat w n := by
  simp only [heat, neg_add, add_mul, Complex.exp_add]

theorem heat_mul (s : ℂ) (a b : ℕ+) : heat s (a * b) = heat s a * heat s b := by
  simp only [heat, energy_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_heat (s : ℂ) (n : ℕ+) : ‖heat s n‖ = Real.exp (-s.re * energy n) := by
  simp [heat, Complex.norm_exp, Complex.mul_re]

theorem heat_eq_cpow (s : ℂ) (n : ℕ+) : heat s n = ((n : ℕ) : ℂ) ^ (-s) := by
  have hp : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast n.ne_zero),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hp.le]
  simp only [heat, energy, mul_comm]

/-- The full heat-amplitude vector belongs to ℓ² exactly to the right of the critical line. -/
theorem summable_heat_sq_iff (s : ℂ) :
    (Summable fun n : ℕ+ => ‖heat s n‖ ^ 2) ↔ 1 / 2 < s.re := by
  have he (n : ℕ+) : ‖heat s n‖ ^ 2 = ((n : ℕ) : ℝ) ^ (-2 * s.re) := by
    rw [norm_heat, sq, ← Real.exp_add, Real.rpow_def_of_pos (by exact_mod_cast n.pos)]
    congr 1
    unfold energy
    ring
  simp_rw [he]
  rw [← Equiv.pnatEquivNat.symm.summable_iff]
  change (Summable fun n : ℕ => ((↑(n + 1) : ℝ) ^ (-2 * s.re))) ↔ _
  rw [summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) 1,
    Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- The product of the two half-time propagators is trace class. -/
def gibbsOperator (s : {s : ℂ // 1 < s.re}) : Gas →L[ℂ] Gas :=
  let half := heat (s.val / 2)
  let hs := (summable_heat_sq_iff (s.val / 2)).2 (by
    rw [Complex.div_ofNat_re]; linarith [s.property])
  HilbertSchmidt.diagOp half hs ∘L HilbertSchmidt.diagOp half hs

theorem gibbsOperator_apply (s : {z : ℂ // 1 < z.re}) (f : Gas) (n : ℕ+) :
    gibbsOperator s f n = heat s.val n * f n := by
  simp only [gibbsOperator, ContinuousLinearMap.comp_apply, HilbertSchmidt.diagOp_apply,
    ← mul_assoc, ← heat_add, add_halves]

/-- The operator partition function of all prime occupations is the Riemann zeta function. -/
theorem partition_eq_zeta (s : {z : ℂ // 1 < z.re}) :
    ContinuousLinearMap.opTrace (gibbsOperator s) = riemannZeta s.val := by
  rw [gibbsOperator, HilbertSchmidt.opTrace_diagOp_comp, zeta_eq_tsum_one_div_nat_add_one_cpow s.2,
    ← Equiv.pnatEquivNat.symm.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [← heat_add, add_halves, heat_eq_cpow, Complex.cpow_neg, one_div]
  change (((↑(n + 1) : ℂ) ^ s.val)⁻¹) = _
  rw [Nat.cast_add, Nat.cast_one]

#print axioms label
#print axioms label_add
#print axioms label_one_quantum
#print axioms energy_mul
#print axioms summable_heat_sq_iff
#print axioms gibbsOperator_apply
#print axioms partition_eq_zeta

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
