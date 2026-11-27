import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Temperature

/-! # The vacuum multiplicity as the leading coefficient of the thermal polynomial -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Finset Real Polynomial

variable {I : Type*} [Fintype I]

/-- If all positive displacements are shorter than the vacuum displacement,
the leading coefficient is precisely minus the number of vacuum states. -/
theorem leading_vacuum (k : I → ℕ) (occupied : 0<Sparse.multiplicity k 0)
    (outer : ∀ i, Fintype.card I*k i<2*∑ l, k l) :
    (imbalancePolynomial k).leadingCoeff= -(Sparse.multiplicity k 0 : ℤ) := by
  classical
  let n := Fintype.card I
  let s := ∑ i, k i
  let d := n*s+2*s
  let A (i : I) := n*(s+k i)
  let B (i : I) := n*(s-k i)+2*s
  have pos : 0<n := by
    rcases isEmpty_or_nonempty I with he | hn
    · haveI := he
      simp [Sparse.multiplicity] at occupied
    · exact Fintype.card_pos
  have left (i : I) : A i<d := by
    change n*(s+k i)<n*s+2*s
    rw [Nat.mul_add]
    exact Nat.add_lt_add_left (outer i) _
  have right (i : I) : B i≤d := Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.sub_le s _)) _
  have top (i : I) : d=B i ↔ k i=0 := by
    change n*s+2*s=n*(s-k i)+2*s ↔ _
    rw [Nat.add_right_cancel_iff,Nat.mul_right_inj pos.ne']
    have le : k i ≤ s := single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  have coeff (e : ℕ) : (imbalancePolynomial k).coeff e =
      ((univ.filter (fun i => e=A i)).card : ℤ)-((univ.filter (fun i => e=B i)).card : ℤ) := by
    simp only [imbalancePolynomial,finsetSum_coeff,coeff_sub,coeff_X_pow,sum_sub_distrib,sum_boole,
      A,B,n,s]
  have first {e : ℕ} (ge : d≤e) : univ.filter (fun i => e=A i)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i has
    exact (left i).not_ge ((mem_filter.mp has).2 ▸ ge)
  have high : (imbalancePolynomial k).natDegree≤d := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun e gt => ?_
    have empty : univ.filter (fun i => e=B i)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i has
      exact gt.not_ge ((mem_filter.mp has).2 ▸ right i)
    rw [coeff,first gt.le,empty,sub_self]
  have cd : (imbalancePolynomial k).coeff d= -(Sparse.multiplicity k 0 : ℤ) := by
    rw [coeff,first le_rfl,card_empty,Nat.cast_zero,zero_sub]
    simp only [top,Sparse.multiplicity]
  have degree := natDegree_eq_of_le_of_coeff_ne_zero high (by rw [cd]; exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr occupied.ne'))
  rw [← coeff_natDegree,degree,cd]

/-- At a rational damping, all prime divisibility is already visible in the
vacuum multiplicity; the other levels may be arbitrarily degenerate. -/
theorem vacuum_divisibility [Nonempty I] (p : Nat.Primes) (k : I → ℕ)
    (occupied : 0<Sparse.multiplicity k 0) (outer : ∀ i, Fintype.card I*k i<2*∑ l, k l)
    {q : ℚ} (hq : 0<q) (hit : agrees (primeModes p k) (q : ℝ)) :
    (p.val : ℤ)^q.num.toNat ∣ (Sparse.multiplicity k 0 : ℤ)^(q.den*Fintype.card I) := by
  rw [Sparse.mode_grid,agrees_affine] at hit
  have div := Sparse.rational_divisibility p k hq hit
  rw [leading_vacuum k occupied outer] at div
  exact div.trans (pow_dvd_pow_of_dvd (by simp) _)

/-- A prime not dividing the vacuum multiplicity rules out all algebraic
positive ties when the vacuum is the farthest centered level. -/
theorem vacuum_transcendental [Nonempty I] (p : Nat.Primes) (k : I → ℕ)
    (occupied : 0<Sparse.multiplicity k 0) (outer : ∀ i, Fintype.card I*k i<2*∑ l, k l)
    (cop : ¬p.val ∣ Sparse.multiplicity k 0) {t : ℝ} (ht : 0<t) (hit : agrees (primeModes p k) t) :
    Transcendental ℚ t := by
  intro alg
  by_cases irr : Irrational t
  · have lead := leading_vacuum k occupied outer
    have nz : imbalancePolynomial k≠0 := by
      intro hz
      rw [hz,leadingCoeff_zero] at lead
      exact (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr occupied.ne')).symm lead
    rw [Sparse.mode_grid,agrees_affine] at hit
    have base : IsAlgebraic ℤ (exp (t*log p.val/Fintype.card I)) :=
      ⟨imbalancePolynomial k,nz,(imbalancePolynomial_root k _).mpr hit⟩
    have pp : 1<(p.val : ℝ) := Nat.one_lt_cast.mpr p.property.one_lt
    have poweq : exp (t*log p.val/Fintype.card I)^Fintype.card I=(p.val : ℝ)^t := by
      rw [← exp_nat_mul,rpow_def_of_pos (zero_lt_one.trans pp)]
      congr 1
      field_simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
    have tr := GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds _ _ (zero_lt_one.trans pp)
      pp.ne' ((isIntegral_natCast (B := ℝ) p.val).isAlgebraic) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg) irr
    exact tr (poweq ▸ (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp (base.pow _))
  · obtain ⟨q,rfl⟩ := Classical.not_not.mp irr
    have qp := Rat.cast_pos.mp ht
    have div := vacuum_divisibility p k occupied outer qp hit
    have num := Rat.num_pos.mpr qp
    have small : (p.val : ℤ) ∣ (p.val : ℤ)^q.num.toNat := dvd_pow_self _ (by omega)
    exact cop (Int.natCast_dvd.mp ((Nat.prime_iff_prime_int.mp p.property).dvd_of_dvd_pow (small.trans div)))

#print axioms leading_vacuum
#print axioms vacuum_divisibility
#print axioms vacuum_transcendental

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
