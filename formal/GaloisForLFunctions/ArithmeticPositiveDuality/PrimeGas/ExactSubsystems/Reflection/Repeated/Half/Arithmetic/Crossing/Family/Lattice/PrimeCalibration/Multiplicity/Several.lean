import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Rational

/-! # Successive multiplicity costs of distinct prime radical roots -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Polynomial Finset

/-- Apply the coefficient cost of each elementary prime to the lower
bound already forced by the remaining primes. -/
def required : List Nat.Primes → ℕ → ℕ
  | [], a => a
  | p::ps, a => (p.val-1)*required ps a+1

/-- Removing one monic binomial preserves the other radical roots.
Each removal bounds every coefficient of the quotient. -/
theorem successive_height (ps : List Nat.Primes) (distinct : ps.Nodup) {K : ℕ} (hK : 0<K)
    (P : ℤ[X]) (nz : P≠0) (roots : ∀ p∈ps, ∃ x : ℝ, x^K=(p.val : ℝ) ∧ aeval x P=0)
    {a H : ℕ} (seed : a≤P.leadingCoeff.natAbs) (cap : ∀ j, (P.coeff j).natAbs≤H) :
    required ps a≤H := by
  classical
  induction ps generalizing P H with
  | nil =>
    exact seed.trans (by simpa only [coeff_natDegree] using cap P.natDegree)
  | cons p ps ih =>
    obtain ⟨away,nd⟩ := List.nodup_cons.mp distinct
    obtain ⟨x,power,root⟩ := roots p (List.mem_cons_self ..)
    obtain ⟨Q,eq⟩ := radical_factor p hK power P root
    have lead : P.leadingCoeff=Q.leadingCoeff := by
      rw [eq,leadingCoeff_mul,(monic_X_pow_sub_C (p.val : ℤ) hK.ne').leadingCoeff,one_mul]
    have Qnz : Q≠0 := by intro z; exact nz (by rw [eq,z,mul_zero])
    have remaining (q : Nat.Primes) (hq : q∈ps) : ∃ y : ℝ, y^K=(q.val : ℝ) ∧ aeval y Q=0 := by
      obtain ⟨y,yK,yr⟩ := roots q (List.mem_cons_of_mem _ hq)
      have different : (q.val : ℝ)≠p.val := by
        intro same
        exact away ((Subtype.ext (Nat.cast_injective same) : q=p) ▸ hq)
      rw [eq,map_mul,map_sub,map_pow,aeval_X,aeval_C,yK] at yr
      exact ⟨y,yK,(mul_eq_zero.mp yr).resolve_left (sub_ne_zero.mpr different)⟩
    let m := (H-1)/(p.val-1)
    have predPos : 0<p.val-1 := by have := p.property.one_lt; omega
    have digits (j : ℕ) : (Q.coeff j).natAbs ≤ m := by
      by_cases zero : Q.coeff j=0
      · simp only [zero,Int.natAbs_zero,Nat.zero_le]
      · have strict := stride_digit Q p.property.one_lt hK (eq ▸ cap) zero
        apply (Nat.le_div_iff_mul_le predPos).mpr
        rw [mul_comm]
        omega
    have cost : required ps a ≤ m := ih nd Q Qnz remaining (lead ▸ seed) digits
    have Hpos : 0<H := (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr nz)).trans_le
      (by simpa only [coeff_natDegree] using cap P.natDegree)
    have bound : (p.val-1)*m≤H-1 := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
    exact Nat.succ_le_of_lt ((Nat.mul_le_mul_left _ cost).trans_lt (by omega : (p.val-1)*m<H))

variable {I : Type*} [Fintype I]

/-- For a nonempty list of distinct accepted primes, start with their
product. Each step h ↦ (p-1)h+1 gives a certified lower bound on peak
multiplicity, in any ordering of the tests. -/
theorem ordered_prime_cost (k : I → ℕ) (ps : List Nat.Primes) (distinct : ps.Nodup)
    (non : ps ≠ []) {d : ℝ} (hd : 0<d) (alg : IsAlgebraic ℚ d) (asym : ¬Reflects (levels k))
    (pass : ∀ p∈ps, accepts k p d) {H : ℕ} (cap : ∀ m, Sparse.multiplicity k m≤H) :
    required ps (∏ p ∈ ps.toFinset, p.val)≤H := by
  classical
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  letI := hn
  obtain ⟨p,hp⟩ : ∃ p, p∈ps := by cases ps with
    | nil => exact (non rfl).elim
    | cons p ps => exact ⟨p,List.mem_cons_self ..⟩
  have rat : ¬Irrational d := fun h => asym ((algebraic_irrational_detected p k hd alg h).mp (pass p hp))
  obtain ⟨r,rfl⟩ := Classical.not_not.mp rat
  have pos := Rat.cast_pos.mp hd
  have Apos : 0<r.num.toNat := by have := Rat.num_pos.mpr pos; omega
  let P := expand ℤ r.num.toNat (imbalancePolynomial k)
  have lead : P.leadingCoeff=(imbalancePolynomial k).leadingCoeff := leadingCoeff_expand Apos
  have lnon := leadingCoeff_ne_zero.mpr (imbalancePolynomial_ne_zero asym)
  have nz : P≠0 := leadingCoeff_ne_zero.mp (by rwa [lead])
  have prodDiv := prime_product_dvd k ps.toFinset pos (fun q hq => pass q (List.mem_toFinset.mp hq))
  apply successive_height ps distinct (Nat.mul_pos r.den_pos (Fintype.card_pos (α := I))) P nz
    (fun q hq => rational_radical k q pos (pass q hq))
  · rw [lead]
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr lnon) prodDiv
  · intro j
    rw [show P.coeff j=_ from coeff_expand Apos (imbalancePolynomial k) j]
    split
    · exact Sparse.coefficient_bound k cap _
    · exact Nat.zero_le _

/-- Simultaneously fooling the binary and ternary prime probes at one
positive algebraic damping requires at least fifteen copies of a level. -/
theorem two_three_cost (k : I → ℕ) {d : ℝ} (hd : 0<d) (alg : IsAlgebraic ℚ d)
    (asym : ¬Reflects (levels k)) (two : accepts k ⟨2,Nat.prime_two⟩ d)
    (three : accepts k ⟨3,Nat.prime_three⟩ d) {H : ℕ}
    (cap : ∀ m, Sparse.multiplicity k m≤H) : 15≤H := by
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  let q : Nat.Primes := ⟨3,Nat.prime_three⟩
  have diff : q≠p := by intro eq; have impossible := congrArg Subtype.val eq; change 3=2 at impossible; omega
  have bound := ordered_prime_cost k [q,p] (by simp [diff]) (by simp) hd alg asym
    (fun r hr => by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl <;> assumption) cap
  have product : (∏ r ∈ [q,p].toFinset, r.val)=q.val*p.val := by simp [diff]
  rw [product] at bound
  exact bound

#print axioms two_three_cost
#print axioms successive_height
#print axioms ordered_prime_cost

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
