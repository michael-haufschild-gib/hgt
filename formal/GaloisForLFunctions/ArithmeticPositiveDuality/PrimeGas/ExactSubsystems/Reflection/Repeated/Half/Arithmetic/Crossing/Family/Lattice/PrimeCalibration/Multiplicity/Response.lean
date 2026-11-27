import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Packet

/-! # All return dampings of the multiplicity-minimizing preparation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Real

/-- On probe q the unique positive return is the ratio of the calibration
energy log p to the probe energy log q. Zero is always a return. -/
theorem packet_response (p q : Nat.Primes) (d : ℝ) :
    accepts (packet p) q d ↔ d=0 ∨ |d|=log p.val/log q.val := by
  rw [accepts_iff]
  by_cases flat : d=0
  · simp only [flat,abs_zero,zero_mul,agrees,neg_zero,iff_self,true_or]
  · rw [positive_return p (mul_pos (abs_pos.mpr flat) (log_pos_prime q)),or_iff_right flat,
      eq_div_iff (log_pos_prime q).ne']

/-- Every different probe sees exactly one positive return, and that return
is transcendental. The calibration prime itself returns at unit damping. -/
theorem return_arithmetic (p q : Nat.Primes) :
    let t := log p.val/log q.val
    0<t ∧ (t=1 ↔ p=q) ∧ (p≠q → Transcendental ℚ t) ∧
      ∀ d : ℝ, 0<d → (accepts (packet p) q d ↔ d=t) := by
  have pos (r : Nat.Primes) : 0<(r.val : ℝ) := Nat.cast_pos.mpr r.property.pos
  refine ⟨div_pos (log_pos_prime p) (log_pos_prime q),?_,?_,?_⟩
  · rw [div_eq_one_iff_eq (log_pos_prime q).ne']
    exact ⟨fun eq => Subtype.ext (Nat.cast_injective (log_injOn_pos (pos p) (pos q) eq)),
      congrArg (fun r : Nat.Primes => log r.val)⟩
  · intro diff
    exact GaloisForLFunctions.RHTower.log_ratio_transcendental q.property p.property
      (fun eq => diff (Subtype.ext eq.symm))
  · intro d hd
    rw [packet_response,or_iff_right hd.ne',abs_of_pos hd]

/-- Two distinct probe primes discriminate the isometry line at all real
dampings, even with the threshold multiplicity that defeats one probe. -/
theorem pair_isometry (p q r : Nat.Primes) (distinct : q≠r) (s : ℂ) :
    (accepts (packet p) q (2*s.re-1) ∧ accepts (packet p) r (2*s.re-1)) ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) := by
  let d := 2*s.re-1
  have line : d=0 ↔ s.re=1/2 := by dsimp only [d]; constructor <;> intro h <;> linarith only [h]
  rw [split_isometric_iff,←line]
  change (accepts (packet p) q d ∧ accepts (packet p) r d) ↔ d=0
  rw [packet_response,packet_response]
  by_cases flat : d=0
  · simp only [flat,true_or,and_self]
  · simp only [flat,false_or,iff_false]
    rintro ⟨hq,hr⟩
    have qeq := (eq_div_iff (log_pos_prime q).ne').mp hq
    have req := (eq_div_iff (log_pos_prime r).ne').mp hr
    have logs := mul_left_cancel₀ (abs_ne_zero.mpr flat) (qeq.trans req.symm)
    have pos (v : Nat.Primes) : 0<(v.val : ℝ) := Nat.cast_pos.mpr v.property.pos
    exact distinct (Subtype.ext (Nat.cast_injective (log_injOn_pos (pos q) (pos r) logs)))

/-- Two distinct positive moment orders of one normalized Gibbs law
separate the critical line on a single prime. Both comparisons are read
from the same probability vector. -/
theorem one_law_isometry (p q : Nat.Primes) {u v : ℝ} (hu : 0<u) (hv : 0<v)
    (distinct : u≠v) (s : ℂ) :
    let E := primeModes q (packet p)
    let P := _root_.HTGeometry.finiteGibbsStateWeight (2*s.re-1) E
    lawOrder P u ∧ lawOrder P v ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  dsimp only
  let d := 2*s.re-1
  have line : d=0 ↔ s.re=1/2 := by dsimp only [d]; constructor <;> intro h <;> linarith only [h]
  have probe (w : ℝ) : lawOrder (_root_.HTGeometry.finiteGibbsStateWeight d (primeModes q (packet p))) w ↔
      accepts (packet p) q (w*d) := by rw [accepts,gibbs_order,gibbs_order,one_mul]
  rw [split_isometric_iff,←line,probe,probe,packet_response,packet_response]
  by_cases flat : d=0
  · simp only [flat,mul_zero,true_or,and_self]
  · rw [or_iff_right (mul_ne_zero hu.ne' flat),or_iff_right (mul_ne_zero hv.ne' flat)]
    constructor
    · rintro ⟨a,b⟩
      have eq := a.trans b.symm
      rw [abs_mul,abs_mul,abs_of_pos hu,abs_of_pos hv] at eq
      exact (distinct (mul_right_cancel₀ (abs_ne_zero.mpr flat) eq)).elim
    · exact fun h => (flat h).elim

#print axioms one_law_isometry
#print axioms packet_response
#print axioms return_arithmetic
#print axioms pair_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
