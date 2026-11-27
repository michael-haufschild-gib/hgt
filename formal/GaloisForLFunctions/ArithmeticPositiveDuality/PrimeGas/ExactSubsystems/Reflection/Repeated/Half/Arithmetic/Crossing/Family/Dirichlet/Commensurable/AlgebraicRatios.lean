import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Stabilization
import GaloisForLFunctions.RHTower.GelfondSchneider

/-! # Isolation among all algebraic order ratios -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Real MvPolynomial

/-- Specializing the prime coordinates preserves every integral polynomial
relation of an individual shell. -/
private theorem algebraic_transfer {s v : ℝ} (h : kernel s ≤ kernel v) (n : ℕ+)
    (alg : IsAlgebraic ℚ (shellPower s n)) : IsAlgebraic ℚ (shellPower v n) := by
  obtain ⟨P,ne,root⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg
  have eval (x : ℝ) : value x (Polynomial.aeval (atom n) P) = Polynomial.aeval (shellPower x n) P := by
    rw [← Polynomial.aeval_algHom_apply,value_atom,← shellPower_exp]
  apply (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp
  refine ⟨P,ne,?_⟩
  rw [← eval]
  apply h
  exact (eval s).trans root

/-- Gelfond–Schneider excludes both signs of an algebraic irrational
multiplier at every dilation. Rational multipliers are separated by the
incomparability of the prime evaluation kernels. -/
theorem algebraic_multiplier_iff (n : ℕ+) (hn : 1<n.val) {t r : ℝ} (ht : 0<t) (hr : 0<r)
    (shell : IsAlgebraic ℚ (shellPower t n)) (alg : IsAlgebraic ℚ r) :
    r*t ∈ accumulated t ↔ r=1 := by
  constructor
  · rintro ⟨_,m,hm,force⟩
    have src := mul_pos ht (Nat.cast_pos.mpr hm : (0 : ℝ) < m)
    rw [mul_assoc] at force
    by_cases irr : Irrational r
    · let x := t*(m : ℝ)
      have base : 1<shellPower x n := one_lt_rpow (Nat.one_lt_cast.mpr hn) src
      have pow : shellPower x n=(shellPower t n)^m :=
        rpow_mul_natCast (Nat.cast_nonneg n.val) t m
      have sourceAlg : IsAlgebraic ℚ (shellPower x n) := by rw [pow]; exact shell.pow m
      have exclude (b : ℝ) (ab : IsAlgebraic ℚ b) (ib : Irrational b)
          (inc : kernel x ≤ kernel (b*x)) : False := by
        have transferred := algebraic_transfer inc n sourceAlg
        have id : shellPower (b*x) n=(shellPower x n)^b := by
          change (n.val : ℝ)^(b*x)=((n.val : ℝ)^x)^b
          rw [← rpow_mul (Nat.cast_nonneg n.val),mul_comm]
        rw [id] at transferred
        exact GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds _ _
          (zero_lt_one.trans base) base.ne' ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr sourceAlg)
          ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr ab) ib transferred
      rcases (forces_iff src (mul_pos hr src)).mp force with plus | minus
      · exact (exclude r alg irr plus).elim
      · rw [← neg_mul] at minus
        exact (exclude (-r) alg.neg irr.neg minus).elim
    · obtain ⟨q,rfl⟩ := exists_rat_of_not_irrational irr
      have res := (resonant_nat_iff ht hm).mpr (algebraic_shell_resonant n hn ht shell)
      have h := ((rational_forces_iff src q (Rat.cast_pos.mp hr)).mp force).resolve_right (not_not.mpr res)
      simp only [h,Rat.cast_one]
  · rintro rfl
    rw [one_mul]
    exact ⟨ht,1,zero_lt_one,fun _ _ h => h⟩

/-- At every positive rational dilation one finite asymmetric shell spectrum
accepts the base and rejects every other positive algebraic multiple. -/
theorem algebraic_isolation (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (shell : IsAlgebraic ℚ (shellPower t n)) (q : ℚ) (hq : 0<q) :
    ∃ S, Attainable S ∧ (q : ℝ)*t ∈ S ∧
      ∀ r : ℝ, 0<r → IsAlgebraic ℚ r → (r*((q : ℝ)*t) ∈ S ↔ r=1) := by
  have pos := mul_pos (Rat.cast_pos.mpr hq : (0 : ℝ) < q) ht
  have res := (resonant_rational_iff ht q hq).mpr (algebraic_shell_resonant n hn ht shell)
  refine ⟨consequences ((q : ℝ)*t),least_spectrum pos res,⟨pos,fun _ _ h => h⟩,fun r hr alg => ?_⟩
  constructor
  · intro hit
    apply (algebraic_multiplier_iff n hn ht hr shell alg).mp
    apply (accumulated_iff_rational ht (mul_pos hr ht)).mpr
    refine ⟨q,hq,?_⟩
    simpa only [mul_left_comm (q : ℝ) r] using hit.2
  · rintro rfl
    rw [one_mul]
    exact ⟨pos,fun _ _ h => h⟩

#print axioms algebraic_multiplier_iff
#print axioms algebraic_isolation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
