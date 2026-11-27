import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Coefficients
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Calibration

/-! # One probe at algebraic damping for sparse prime-power spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse

open Finset Real Polynomial
open _root_.HTGeometry (finiteGibbsStateWeight)

variable {I : Type*} [Fintype I]

/-- At a positive rational blind temperature the prime's power divides a power
of the outermost nonzero multiplicity imbalance. -/
theorem rational_divisibility [Nonempty I] (p : Nat.Primes) (k : I → ℕ) {q : ℚ} (hq : 0 < q)
    (hit : agrees (levels k) ((q : ℝ)*log (p.val : ℝ))) :
    (p.val : ℤ)^q.num.toNat ∣ (imbalancePolynomial k).leadingCoeff^(q.den*Fintype.card I) := by
  let n := Fintype.card I
  let c := (imbalancePolynomial k).leadingCoeff
  let x := exp (-(((q : ℝ)*log (p.val : ℝ))/n))
  have np : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have pp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr p.property.pos
  have num : (q.num.toNat : ℝ)=(q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hq).le
  have frac : (q.den : ℝ)*(q : ℝ)=(q.num.toNat : ℝ) := by
    rw [num]
    exact_mod_cast q.den_mul_eq_num
  have ep : exp ((q.num.toNat : ℝ)*log (p.val : ℝ))=(p.val : ℝ)^q.num.toNat := by
    rw [exp_nat_mul,exp_log pp]
  have power : x^(q.den*n)=((p.val : ℝ)^q.num.toNat)⁻¹ := by
    rw [← ep,← exp_neg]
    unfold x
    rw [← exp_nat_mul]
    congr 1
    rw [Nat.cast_mul,← frac]
    field_simp
  have integ : IsIntegral ℤ ((c : ℝ)*x) := (scaled_integral k hit).2
  have powInt := integ.pow (q.den*n)
  rw [mul_pow,power,← div_eq_mul_inv] at powInt
  obtain ⟨m,hm⟩ := powInt.exists_int_iff_exists_rat.mp
    ⟨(c : ℚ)^(q.den*n)/(p.val : ℚ)^q.num.toNat,by push_cast; rfl⟩
  have cleared := (div_eq_iff (pow_ne_zero _ pp.ne')).mp hm
  refine ⟨m,?_⟩
  change c^(q.den*n)=(p.val : ℤ)^q.num.toNat*m
  rw [mul_comm ((p.val : ℤ)^q.num.toNat) m]
  exact_mod_cast cleared

private theorem positive_obstruction (p : Nat.Primes) (k : I → ℕ)
    (cap : ∀ m, multiplicity k m < p.val) {d : ℝ} (hd : 0 < d)
    (asym : ¬Reflects (levels k)) (hit : agrees (levels k) (d*log (p.val : ℝ))) :
    Transcendental ℚ d := by
  classical
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  · letI := hn
    intro alg
    have pp : (1 : ℝ) < p.val := Nat.one_lt_cast.mpr p.property.one_lt
    by_cases irr : Irrational d
    · have coord := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp (algebraic_coordinate k asym hit)
      have n0 : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have power : exp (d*log (p.val : ℝ)/Fintype.card I)^Fintype.card I=(p.val : ℝ)^d := by
        rw [← exp_nat_mul,rpow_def_of_pos (zero_lt_one.trans pp)]
        congr 1
        field_simp
      exact GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds _ _ (zero_lt_one.trans pp) pp.ne'
        ((isIntegral_natCast (B := ℝ) p.val).isAlgebraic) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg)
        irr (power ▸ coord.pow _)
    · obtain ⟨q,rfl⟩ := Classical.not_not.mp irr
      have qp : 0 < q := Rat.cast_pos.mp hd
      have nz := leadingCoeff_ne_zero.mpr (imbalancePolynomial_ne_zero asym)
      have small := coefficient_bound k (M := p.val-1) (fun m => by have := cap m; omega)
        (imbalancePolynomial k).natDegree
      rw [coeff_natDegree] at small
      have div := rational_divisibility p k qp hit
      have num := Rat.num_pos.mpr qp
      have one : (p.val : ℤ) ∣ (p.val : ℤ)^q.num.toNat := dvd_pow_self _ (by omega)
      have d := (Nat.prime_iff_prime_int.mp p.property).dvd_of_dvd_pow (one.trans div)
      have nat := Int.natCast_dvd.mp d
      have lower := Nat.le_of_dvd (Int.natAbs_pos.mpr nz) nat
      have := p.property.pos
      omega

omit [Fintype I] in
theorem mode_grid (p : Nat.Primes) (k : I → ℕ) :
    primeModes p k=fun i => log (p.val : ℝ)*levels k i+0 := by
  funext i
  change log (((p.val^k i : ℕ) : ℝ))=log (p.val : ℝ)*(k i : ℝ)+0
  rw [Nat.cast_pow,log_pow,add_zero,mul_comm]

/-- A blind asymmetric list of distinct powers of a prime gives an algebraic
unit after exponentiation of its temperature. -/
theorem prime_unit (p : Nat.Primes) (k : I → ℕ) (inj : Function.Injective k) {d : ℝ}
    (asym : ¬Reflects (primeModes p k)) (hit : agrees (primeModes p k) d) :
    let x := (p.val : ℝ)^(d/Fintype.card I)
    IsIntegral ℤ x ∧ IsIntegral ℤ x⁻¹ := by
  have hp : (1 : ℝ) < p.val := Nat.one_lt_cast.mpr p.property.one_lt
  rw [mode_grid,affine_reflects _ _ _ (log_pos hp).ne'] at asym
  rw [mode_grid,agrees_affine] at hit
  have h := unit_coordinates k inj asym hit
  dsimp only
  rw [rpow_def_of_pos (zero_lt_one.trans hp)]
  rw [show log (p.val : ℝ)*(d/Fintype.card I)=d*log (p.val : ℝ)/Fintype.card I by ring]
  exact h

/-- At algebraic damping, one comparison detects every asymmetry if each
occupation appears fewer times than the elementary prime. -/
theorem algebraic_reading (p : Nat.Primes) (k : I → ℕ) (cap : ∀ m, multiplicity k m < p.val)
    (d : ℝ) (alg : IsAlgebraic ℚ d) :
    agrees (primeModes p k) d ↔ d=0 ∨ Reflects (primeModes p k) := by
  have hp : (1 : ℝ) < p.val := Nat.one_lt_cast.mpr p.property.one_lt
  constructor
  · intro hit
    by_contra! both
    rw [mode_grid,affine_reflects _ _ _ (log_pos hp).ne'] at both
    rw [mode_grid,agrees_affine] at hit
    rcases lt_or_gt_of_ne both.1 with neg | pos
    · have negHit : agrees (levels k) ((-d)*log (p.val : ℝ)) := by
        simpa only [neg_mul,agrees,neg_neg] using hit.symm
      exact positive_obstruction p k cap (neg_pos.mpr neg) both.2 negHit alg.neg
    · exact positive_obstruction p k cap pos both.2 hit alg
  · rintro (rfl | symm)
    · simp only [agrees,neg_zero]
    · exact reflection_agrees symm _

/-- The order-one statistic of a single Gibbs distribution decides split
isometry at all algebraic dampings on a sparse asymmetric prime sector. -/
theorem algebraic_law (p : Nat.Primes) (k : I → ℕ) (cap : ∀ m, multiplicity k m < p.val)
    (s : ℂ) (alg : IsAlgebraic ℚ (2*s.re-1)) :
    lawOrder (finiteGibbsStateWeight (2*s.re-1) (primeModes p k)) 1 ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨ Reflects (primeModes p k) := by
  have mid : 2*s.re-1=0 ↔ s.re=1/2 := by constructor <;> intro h <;> linarith only [h]
  rw [gibbs_order,one_mul,algebraic_reading p k cap _ alg,mid,split_isometric_iff]

#print axioms rational_divisibility
#print axioms prime_unit
#print axioms algebraic_reading
#print axioms algebraic_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse
