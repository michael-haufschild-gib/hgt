import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Rational
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Packet

/-! # Sharp multiplicity for a single-prime Gibbs test of isometry -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset Real

variable {I : Type*} [Fintype I]

/-- Below the sharp multiplicity, an algebraic-damping equality has only
the two causes of zero damping and reflection symmetry. -/
theorem algebraic_test (k : I → ℕ) (p : Nat.Primes)
    (cap : ∀ m, Sparse.multiplicity k m < threshold p) (d : ℝ) (alg : IsAlgebraic ℚ d) :
    accepts k p d ↔ d=0 ∨ Reflects (levels k) := by
  constructor
  · intro pass
    by_contra! neither
    have hit : accepts k p |d| := (accepts_iff k p _).mpr (by
      simpa only [abs_abs] using (accepts_iff k p d).mp pass)
    have aa : IsAlgebraic ℚ |d| := by
      rcases le_total 0 d with h | h
      · rwa [abs_of_nonneg h]
      · simpa only [abs_of_nonpos h] using alg.neg
    have bound := joint_algebraic_bound k {p} p (mem_singleton_self _)
      (abs_pos.mpr neither.1) aa neither.2 (by simpa only [mem_singleton,forall_eq] using hit)
      (H := p.val*(p.val-1)) (fun m => Nat.le_of_lt_succ (cap m))
    rw [prod_singleton,mul_comm] at bound
    exact (lt_irrefl _ bound)
  · rintro (rfl | symm)
    · simp only [accepts_iff,abs_zero,zero_mul,agrees,neg_zero]
    · exact (accepts_iff k p _).mpr (reflection_agrees symm _)

/-- For algebraic damping the normalized Gibbs comparison detects divisor
splitting isometry on every asymmetric packet below the sharp peak. -/
theorem algebraic_isometry (k : I → ℕ) (p : Nat.Primes)
    (cap : ∀ m, Sparse.multiplicity k m < threshold p) (s : ℂ)
    (alg : IsAlgebraic ℚ (2*s.re-1)) :
    accepts k p (2*s.re-1) ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨ Reflects (levels k) := by
  rw [algebraic_test k p cap _ alg,split_isometric_iff]
  have equiv : 2*s.re-1=0 ↔ s.re=1/2 := by constructor <;> intro h <;> linarith only [h]
  rw [equiv]

/-- Every preparation attaining the threshold for a false algebraic
reading on p necessarily rejects all other primes at that same damping. -/
theorem unique_at_threshold (k : I → ℕ) (p : Nat.Primes) {d : ℝ} (hd : 0<d)
    (alg : IsAlgebraic ℚ d) (asym : ¬Reflects (levels k))
    (cap : ∀ m, Sparse.multiplicity k m≤threshold p) (hit : accepts k p d) (q : Nat.Primes) :
    accepts k q d ↔ q=p := by
  classical
  refine ⟨fun pass => ?_,fun eq => eq ▸ hit⟩
  by_contra different
  have bound := joint_algebraic_bound k {p,q} p (mem_insert_self ..) hd alg asym
    (fun r hr => by rcases mem_insert.mp hr with rfl | h; exact hit; exact (mem_singleton.mp h).symm ▸ pass) cap
  have diff : p≠q := fun eq => different eq.symm
  rw [prod_insert (by simpa only [mem_singleton] using diff),prod_singleton] at bound
  let a := (p.val-1)*p.val
  have apos : 0<a := Nat.mul_pos (by have := p.property.one_lt; omega) p.property.pos
  have strict : a<a*q.val := by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left q.property.one_lt apos
  rw [←Nat.mul_assoc,threshold,Nat.mul_comm p.val (p.val-1)] at bound
  change a*q.val<a+1 at bound
  omega

/-- A common integer dilation of occupations preserves multiplicity caps.
Empty fibers are allowed. -/
private theorem dilation_cap (k : I → ℕ) (B : ℕ+) {M : ℕ}
    (cap : ∀ m, Sparse.multiplicity k m≤M) (m : ℕ) :
    Sparse.multiplicity (fun i => (B : ℕ)*k i) m≤M := by
  classical
  by_cases ex : ∃ j, (B : ℕ)*k j=m
  · obtain ⟨j,hj⟩ := ex
    apply le_trans _ (cap (k j))
    apply card_le_card
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,Nat.eq_of_mul_eq_mul_left B.pos ((mem_filter.mp hi).2.trans hj.symm)⟩
  · change (univ.filter (fun i => (B : ℕ)*k i=m)).card≤M
    rw [filter_eq_empty_iff.mpr (fun i _ eq => ex ⟨i,eq⟩),card_empty]
    exact Nat.zero_le _

/-- At damping 1/B the explicit integer dilation accepts exactly p,
retaining its peak multiplicity and its asymmetry. -/
theorem reciprocal_witness (p : Nat.Primes) (B : ℕ+) :
    let k := fun i => (B : ℕ)*packet p i
    ¬Reflects (levels k) ∧ (∀ m, Sparse.multiplicity k m≤threshold p) ∧
      ∀ q : Nat.Primes, accepts k q ((B : ℝ)⁻¹) ↔ q=p := by
  dsimp only
  let a := packet p
  let k (i : States p) := (B : ℕ)*a i
  have bp : 0<(B : ℝ) := Nat.cast_pos.mpr B.pos
  have scaled : levels k=fun i => (B : ℝ)*levels a i+0 := by
    funext i; simp only [levels,k,Nat.cast_mul,add_zero]
  have asym : ¬Reflects (levels k) := by
    rw [scaled,affine_reflects _ _ _ bp.ne']
    exact packet_asymmetric p
  refine ⟨asym,dilation_cap a B (packet_cap p),fun q => ?_⟩
  change accepts k q _ ↔ _
  rw [accepts_iff,abs_of_pos (inv_pos.mpr bp),scaled,agrees_affine,mul_right_comm,inv_mul_cancel₀ bp.ne',
    one_mul,←packet_test p q,accepts_iff,abs_one,one_mul]

/-- Among asymmetric finite preparations accepting p at damping 1/B,
the least peak multiplicity is p(p-1)+1. It can exclude every other prime. -/
theorem reciprocal_threshold (p : Nat.Primes) (B : ℕ+) (H : ℕ) :
    (∃ (J : Type) (F : Fintype J) (k : J → ℕ), letI := F
      ¬Reflects (levels k) ∧ (∀ m, Sparse.multiplicity k m≤H) ∧
        ∀ q : Nat.Primes, accepts k q ((B : ℝ)⁻¹) ↔ q=p) ↔ threshold p≤H := by
  constructor
  · rintro ⟨J,F,k,asym,cap,hit⟩
    letI := F
    have bp : 0<(B : ℝ) := Nat.cast_pos.mpr B.pos
    have alg : IsAlgebraic ℚ ((B : ℝ)⁻¹) :=
      IsAlgebraic.inv_iff.mpr ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp
        (isIntegral_natCast (B := ℝ) (B : ℕ)).isAlgebraic)
    have pass := (hit p).mpr rfl
    have bound := joint_algebraic_bound k {p} p (mem_singleton_self _) (inv_pos.mpr bp) alg asym
      (by simpa only [mem_singleton,forall_eq] using pass) cap
    simpa only [prod_singleton,mul_comm (p.val-1),threshold] using Nat.succ_le_of_lt bound
  · intro enough
    obtain ⟨asym,cap,hit⟩ := reciprocal_witness p B
    exact ⟨States p,inferInstance,_,asym,fun m => (cap m).trans enough,hit⟩

#print axioms algebraic_test
#print axioms unique_at_threshold
#print axioms algebraic_isometry
#print axioms reciprocal_witness
#print axioms reciprocal_threshold

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
