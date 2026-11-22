import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleBoundary
import GaloisForLFunctions.HTGeometry.OccupationEulerProduct
import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA

/-!
# All root-of-unity gradings of the prime gas

Giving the jth copy phase ωʲ at every elementary prime makes the product of
the local Euler factors equal the factor at r times the temperature. The
graded trace and the cyclic-permutation trace coincide on the full Hilbert space.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open ContinuousLinearMap
open scoped Classical

/-- A constant prime phase, multiplied by the shell heat. -/
def twistedWeight (z s : ℂ) : ℕ+ →* ℂ where
  toFun n := z ^ ArithmeticFunction.cardFactors (n : ℕ) * heat s n
  map_one' := by simp [heat,energy]
  map_mul' a b := by
    rw [PNat.mul_coe,ArithmeticFunction.cardFactors_mul a.ne_zero b.ne_zero,pow_add,heat_mul]
    ring

private theorem twisted_prime (p : Nat.Primes) (z s : ℂ) :
    twistedWeight z s (p : ℕ+) = z*heat s (p : ℕ+) := by
  change z ^ ArithmeticFunction.cardFactors (p : ℕ) * _ = _
  rw [ArithmeticFunction.cardFactors_apply_prime p.property,pow_one]

private theorem twist_monomial (z s : ℂ) (u : Nat.Primes →₀ ℕ) :
    twistedWeight z s (label u) = _root_.HTGeometry.nomeMonomial (fun p : Nat.Primes => z*heat s (p : ℕ+)) u := by
  induction u using Finsupp.induction with
  | zero =>
    change twistedWeight z s 1 = _
    simp [map_one,_root_.HTGeometry.nomeMonomial]
  | single_add p k u _ _ ih =>
    have hp : label (Finsupp.single p k) = (p : ℕ+)^k := by
      apply PNat.coe_injective
      exact Finsupp.prod_single_index (h := fun q : Nat.Primes => fun m : ℕ => (q : ℕ)^m) (pow_zero _)
    rw [label_add,map_mul,hp,map_pow,twisted_prime,ih]
    unfold _root_.HTGeometry.nomeMonomial
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun q : Nat.Primes => fun n : ℕ => (z*heat s (q : ℕ+))^n) (pow_zero _)]

private theorem prime_heat_lt (s : {w : ℂ // 1 < w.re}) (p : Nat.Primes) : ‖heat s.val (p : ℕ+)‖ < 1 := by
  rw [norm_heat,Real.exp_lt_one_iff]
  have hp : 0 < energy (p : ℕ+) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  exact mul_neg_of_neg_of_pos (by linarith only [s.property]) hp

private theorem prime_heat_sum (s : {w : ℂ // 1 < w.re}) :
    Summable (fun p : Nat.Primes => ‖heat s.val (p : ℕ+)‖) := by
  have hi : Function.Injective (fun p : Nat.Primes => (p : ℕ+)) :=
    fun _ _ h => Subtype.ext (congrArg PNat.val h)
  exact ((heat_abs_summable _).mpr s.property).comp_injective hi

private theorem twist_norm (z : ℂ) (hz : ‖z‖ = 1) (s : ℂ) (n : ℕ+) :
    ‖twistedWeight z s n‖ = ‖heat s n‖ := by
  simp only [twistedWeight,MonoidHom.coe_mk,OneHom.coe_mk,norm_mul,norm_pow,hz,one_pow,one_mul]

/-- Euler factorization of a constant rotation at every prime. -/
theorem twisted_euler (z : ℂ) (hz : ‖z‖ = 1) (s : {w : ℂ // 1 < w.re}) :
    HasProd (fun p : Nat.Primes => (1-z*heat s.val (p : ℕ+))⁻¹) (∑' n, twistedWeight z s.val n) := by
  have hn (p : Nat.Primes) : ‖z*heat s.val (p : ℕ+)‖ = ‖heat s.val (p : ℕ+)‖ := by rw [norm_mul,hz,one_mul]
  have h := _root_.HTGeometry.hasProd_inv_one_sub_nome (fun p : Nat.Primes => z*heat s.val (p : ℕ+))
    (fun p => (hn p).trans_lt (prime_heat_lt s p)) ((prime_heat_sum s).congr fun p => (hn p).symm)
  rw [← label.tsum_eq (fun n => twistedWeight z s.val n)]
  simpa only [twist_monomial] using h

def cycleRoot (r : ℕ+) : ℂ := Complex.exp (((2*Real.pi/(r : ℝ) : ℝ) : ℂ)*Complex.I)

theorem cycleRoot_primitive (r : ℕ+) : IsPrimitiveRoot (cycleRoot r) (r : ℕ) := by
  have h : cycleRoot r = Complex.exp (2*(Real.pi : ℂ)*Complex.I/(r : ℂ)) := by
    unfold cycleRoot
    congr 1
    push_cast
    ring
  rw [h]
  exact Complex.isPrimitiveRoot_exp _ r.ne_zero

theorem cycleRoot_norm (r : ℕ+) : ‖cycleRoot r‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- Local interference removes every geometric factor except the r-fold energy. -/
theorem graded_local_product (r : ℕ+) (X : ℂ) :
    (∏ j : Fin (r : ℕ), (1-cycleRoot r ^ (j : ℕ)*X)⁻¹) = (1-X^(r : ℕ))⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun j => 1-cycleRoot r ^ j*X)]
  exact (_root_.HTGeometry.one_sub_pow_eq_prod_primitiveRoot r.pos (cycleRoot_primitive r) X).symm

/-- Product of all r phase-inserted one-copy partitions. -/
theorem cyclic_twist_product (r : ℕ+) (s : {w : ℂ // 1 < w.re}) :
    ∏ j : Fin (r : ℕ), (∑' n, twistedWeight (cycleRoot r ^ (j : ℕ)) s.val n) = riemannZeta ((r : ℂ)*s.val) := by
  have h (j : Fin (r : ℕ)) := twisted_euler (cycleRoot r ^ (j : ℕ))
    (by rw [norm_pow,cycleRoot_norm,one_pow]) s
  have hp := hasProd_prod (s := Finset.univ) (fun j _ => h j)
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ (r : ℕ) from r.pos)
  let t : {w : ℂ // 1 < w.re} := ⟨(r : ℂ)*s.val,by
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    exact s.property.trans_le (le_mul_of_one_le_left (by linarith only [s.property]) hr)⟩
  have ht := twisted_euler 1 (norm_one : ‖(1 : ℂ)‖ = 1) t
  have hsum : (∑' n, twistedWeight 1 t.val n) = riemannZeta t.val := by
    simpa only [twistedWeight,MonoidHom.coe_mk,OneHom.coe_mk,one_pow,one_mul] using (heat_hasSum t).tsum_eq
  rw [hsum] at ht
  have hlocal (p : Nat.Primes) : (∏ j : Fin (r : ℕ), (1-cycleRoot r^(j : ℕ)*heat s.val (p : ℕ+))⁻¹) =
      (1-1*heat t.val (p : ℕ+))⁻¹ := by
    rw [graded_local_product,one_mul]
    change _ = (1-heat (((r : ℕ) : ℂ)*s.val) (p : ℕ+))⁻¹
    rw [heat_nat_mul]
  exact hp.unique (by simpa only [hlocal] using ht)

private def grade (r : ℕ+) (x : Fin (r : ℕ) → ℕ+) : ℂ :=
  ∏ j : Fin (r : ℕ), (cycleRoot r ^ (j : ℕ)) ^ ArithmeticFunction.cardFactors (x j : ℕ)

private theorem grade_norm (r : ℕ+) (x : Fin (r : ℕ) → ℕ+) : ‖grade r x‖ = 1 := by
  simp only [grade,norm_prod,norm_pow,cycleRoot_norm,one_pow,Finset.prod_const_one]

/-- Actual trace-class heat operator with all root-of-unity insertions on the copies. -/
def gradedHeat (r : ℕ+) (s : {w : ℂ // 1 < w.re}) :
    LabelSpace (Fin (r : ℕ) → ℕ+) →L[ℂ] LabelSpace (Fin (r : ℕ) → ℕ+) :=
  HilbertSchmidt.diagOp (fun x => grade r x * wordHeat (s.val/2) x)
    (by simpa only [norm_mul,grade_norm,one_mul] using wordHeat_half_summable (I := Fin (r : ℕ)) s) ∘L
  HilbertSchmidt.diagOp (wordHeat (s.val/2)) (wordHeat_half_summable s)

theorem gradedHeat_traceClass (r : ℕ+) (s : {w : ℂ // 1 < w.re}) : (gradedHeat r s).IsTraceClass :=
  (HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

private theorem graded_weight (r : ℕ+) (s : ℂ) (x : Fin (r : ℕ) → ℕ+) :
    grade r x * wordHeat (s/2) x * wordHeat (s/2) x =
      ∏ j : Fin (r : ℕ), twistedWeight (cycleRoot r ^ (j : ℕ)) s (x j) := by
  rw [mul_assoc,← wordHeat_add,add_halves,grade,wordHeat,← Finset.prod_mul_distrib]
  rfl

private theorem graded_sum (r : ℕ+) (s : {w : ℂ // 1 < w.re}) :
    (∑' x : Fin (r : ℕ) → ℕ+, ∏ j : Fin (r : ℕ), twistedWeight (cycleRoot r ^ (j : ℕ)) s.val (x j)) =
      riemannZeta ((r : ℂ)*s.val) := by
  let w (j : Fin (r : ℕ)) (n : ℕ+) := twistedWeight (cycleRoot r ^ (j : ℕ)) s.val n
  have hw (j : Fin (r : ℕ)) : Summable fun n => ‖w j n‖ :=
    ((heat_abs_summable _).mpr s.property).congr fun n => (twist_norm _ (by rw [norm_pow,cycleRoot_norm,one_pow]) _ n).symm
  have h := FamilyContinuationTheory.hasSum_pi_prod w (fun j => ∑' n, w j n)
    (fun j => (hw j).of_norm.hasSum) hw
  exact h.1.tsum_eq.trans (cyclic_twist_product r s)

theorem gradedHeat_trace (r : ℕ+) (s : {w : ℂ // 1 < w.re}) :
    opTrace (gradedHeat r s) = riemannZeta ((r : ℂ)*s.val) := by
  rw [gradedHeat,HilbertSchmidt.opTrace_diagOp_comp]
  exact (tsum_congr (graded_weight r s.val)).trans (graded_sum r s)

/-- Physical cyclic exchange and prime-phase grading have the same full Gibbs trace. -/
theorem graded_trace_eq_rotation (n : ℕ) (s : {w : ℂ // 1 < w.re}) :
    opTrace (gradedHeat ⟨n+1,Nat.succ_pos n⟩ s) = opTrace (permutedHeat (finRotate (n+1)) s) := by
  rw [gradedHeat_trace,permutedHeat_trace,rotation_partition]
  rfl

#print axioms twisted_euler
#print axioms cycleRoot_primitive
#print axioms graded_local_product
#print axioms cyclic_twist_product
#print axioms gradedHeat_traceClass
#print axioms gradedHeat_trace
#print axioms graded_trace_eq_rotation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
