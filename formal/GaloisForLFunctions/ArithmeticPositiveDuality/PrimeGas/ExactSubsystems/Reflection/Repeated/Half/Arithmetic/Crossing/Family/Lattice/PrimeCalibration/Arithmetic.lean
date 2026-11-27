import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Sharp
import GaloisForLFunctions.GaloisTheoryOfZeros.TheMaximalArithmeticQuotientOfTheZeroMotive

/-! # Which damping parameters can be invisible on several elementary primes? -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration

open Real Finset

/-- A false tie makes the exponential prime coordinate algebraic. -/
theorem accepted_power {I : Type*} [Fintype I] {k : I → ℕ} {p : Nat.Primes} {d : ℝ} (hd : 0<d)
    (asym : ¬Reflects (levels k)) (pass : accepts k p d) : IsAlgebraic ℚ ((p.val : ℝ)^d) := by
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  letI := hn
  rw [accepts_iff,abs_of_pos hd] at pass
  have root := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp (algebraic_coordinate k asym pass)
  have eq : exp (d*log p.val/Fintype.card I)^Fintype.card I=(p.val : ℝ)^d := by
    rw [← exp_nat_mul,rpow_def_of_pos (Nat.cast_pos.mpr p.property.pos)]
    congr 1
    field_simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  exact eq ▸ root.pow _

/-- Simultaneous false ties are equivalent to simultaneous algebraicity, even
when only two prime bases are examined. -/
theorem packet_exists_iff (S : Finset Nat.Primes) {d : ℝ} (hd : 0<d) :
    (∃ (n : ℕ) (k : Fin n → ℕ), ¬Reflects (levels k) ∧ ∀ p ∈ S, accepts k p d) ↔
      ∀ p ∈ S, IsAlgebraic ℚ ((p.val : ℝ)^d) := by
  classical
  constructor
  · rintro ⟨n,k,asym,pass⟩ p hp
    exact accepted_power hd asym (pass p hp)
  · intro alg
    let v (p : Nat.Primes) := (p.val : ℝ)^d
    have eq (p : Nat.Primes) : v p=exp (d*log p.val) := by
      change (p.val : ℝ)^d=exp (d*log p.val)
      rw [rpow_def_of_pos (Nat.cast_pos.mpr p.property.pos),mul_comm]
    have above (p : Nat.Primes) : 1<v p := by
      rw [eq,one_lt_exp_iff]; exact mul_pos hd (log_pos_prime p)
    obtain ⟨n,k,asym,hits⟩ := prescribed (S.image v) (by
      rintro x hx
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
      exact ⟨above p,alg p hp⟩)
    refine ⟨n,k,asym,fun p hp => ?_⟩
    have hit := hits (v p) (mem_image_of_mem v hp)
    rw [eq,log_exp] at hit
    rwa [accepts_iff,abs_of_pos hd]

/-- The two-prime exception is exactly the prime-base four exponentials question. -/
theorem two_prime_exception (p q : Nat.Primes) {d : ℝ} (hd : 0<d) :
    (∃ (n : ℕ) (k : Fin n → ℕ), ¬Reflects (levels k) ∧ accepts k p d ∧ accepts k q d) ↔
      IsAlgebraic ℚ ((p.val : ℝ)^d) ∧ IsAlgebraic ℚ ((q.val : ℝ)^d) := by
  simpa only [mem_insert,mem_singleton,forall_eq_or_imp,forall_eq] using packet_exists_iff {p,q} hd

private theorem complex_alg (p : Nat.Primes) {d : ℝ} (alg : IsAlgebraic ℚ ((p.val : ℝ)^d)) :
    IsAlgebraic ℚ (Complex.exp ((d : ℂ)*(log p.val : ℂ))) := by
  rw [← Complex.ofReal_mul,← Complex.ofReal_exp]
  have eq : exp (d*log p.val)=(p.val : ℝ)^d := by rw [rpow_def_of_pos (Nat.cast_pos.mpr p.property.pos),mul_comm]
  rw [eq]
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp
    (GaloisForLFunctions.RHTower.isAlgebraic_ofReal ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg))

/-- No restriction on the number of levels is needed for three-prime
calibration at irrational damping. At each positive rational, false ties on
all three primes are attained. -/
theorem three_prime_exception (p q r : Nat.Primes) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    {d : ℝ} (hd : 0<d) :
    (∃ (n : ℕ) (k : Fin n → ℕ), ¬Reflects (levels k) ∧ accepts k p d ∧ accepts k q d ∧ accepts k r d) ↔
      ∃ w : ℚ, d=(w : ℝ) := by
  constructor
  · rintro ⟨n,k,asym,hp,hq,hr⟩
    obtain ⟨w,eq⟩ := GaloisForLFunctions.GaloisTheoryOfZeros.rational_of_three_prime_exponentials
      p.property q.property r.property (fun h => pq (Subtype.ext h)) (fun h => pr (Subtype.ext h))
      (fun h => qr (Subtype.ext h)) (complex_alg p (accepted_power hd asym hp))
      (complex_alg q (accepted_power hd asym hq)) (complex_alg r (accepted_power hd asym hr))
    exact ⟨w,by simpa only [Complex.ofReal_re,Complex.ratCast_re] using congrArg Complex.re eq⟩
  · rintro ⟨w,rfl⟩
    obtain ⟨n,k,_,asym,law⟩ := prescribed_prime_set {p,q,r} (Rat.cast_pos.mp hd)
    exact ⟨n,k,asym,(law p).mpr (by simp),(law q).mpr (by simp),(law r).mpr (by simp)⟩

/-- An algebraic irrational damping admits no false tie on any elementary prime. -/
theorem algebraic_irrational_detected {I : Type*} [Fintype I] (p : Nat.Primes) (k : I → ℕ)
    {d : ℝ} (hd : 0<d) (alg : IsAlgebraic ℚ d) (irr : Irrational d) :
    accepts k p d ↔ Reflects (levels k) := by
  constructor
  · intro hit
    by_contra asym
    have gt : 1<(p.val : ℝ) := Nat.one_lt_cast.mpr p.property.one_lt
    have trans := GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds _ _ (zero_lt_one.trans gt)
      gt.ne' (isIntegral_natCast (B := ℝ) p.val).isAlgebraic ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg) irr
    exact trans (accepted_power hd asym hit)
  · intro refl
    exact (accepts_iff k p d).mpr (reflection_agrees refl _)

#print axioms packet_exists_iff
#print axioms two_prime_exception
#print axioms three_prime_exception
#print axioms algebraic_irrational_detected

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration
