import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Packet
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Jet

/-! # A stationary reflection test on one normalized Gibbs law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset

/-- Every finite expectation on the extremal packet reduces to its twelve
occupation values with the two indicated multiplicities. -/
theorem packet_sum {R : Type*} [Semiring R] (p : Nat.Primes) (f : ℕ → R) :
    (∑ i, f (packet p i))=(p.val : R)*(f 0+(f 3+(f 16+(f 19+(f 20+f 23)))))+
      (threshold p : R)*(f 5+(f 6+(f 9+(f 10+(f 25+f 26))))) := by
  simp only [packet,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_sum,univ_eq_attach,sum_attach]
  change (p.val : R)*(∑ j ∈ ({0,3,16,19,20,23} : Finset ℕ), f j)+
    (threshold p : R)*(∑ j ∈ ({5,6,9,10,25,26} : Finset ℕ), f j)=_
  simp

private theorem packet_grid (p : Nat.Primes) : Nonempty (States p) ∧
    2*(∑ i, packet p i)=Fintype.card (States p)*27 ∧ ∀ i, packet p i≤27 := by
  have size := packet_sum p (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] at size
  change Fintype.card (States p)=p.val*6+threshold p*6 at size
  have mass := packet_sum p id
  change (∑ i, packet p i)=p.val*81+threshold p*81 at mass
  have hp := p.property.pos
  refine ⟨Fintype.card_pos_iff.mp (by omega),by omega,fun i => ?_⟩
  let high (j : ℕ) : ℕ := if 27<j then 1 else 0
  have zero : (∑ j, high (packet p j))=0 := by rw [packet_sum]; simp [high]
  have le := single_le_sum (f := fun j => high (packet p j)) (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [zero] at le
  by_contra! large
  simp only [high,if_pos large] at le
  omega

private theorem packet_difference (p : Nat.Primes) (x : ℝ) :
    (∑ i, x^(packet p i))-(∑ i, x^(27-packet p i))=profile (p.val : ℝ) x := by
  rw [packet_sum p (fun j => x^j),packet_sum p (fun j => x^(27-j))]
  simp only [threshold,Nat.cast_add,Nat.cast_mul,Nat.cast_sub p.property.one_lt.le,Nat.cast_one,profile]
  norm_num1
  ring

/-- A single probability vector detects split isometry by a stationary
zero of its reflection comparison at moment order one. -/
theorem stationary_isometry (p q : Nat.Primes) (s : ℂ) :
    let P := _root_.HTGeometry.finiteGibbsStateWeight (2*s.re-1) (primeModes q (packet p))
    (lawOrder P 1 ∧ HasDerivAt (lawDefect P) 0 1) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  let d := 2*s.re-1
  let a := d*Real.log q.val
  let P := _root_.HTGeometry.finiteGibbsStateWeight d (primeModes q (packet p))
  change (lawOrder P 1 ∧ HasDerivAt (lawDefect P) 0 1) ↔ _
  have test : lawOrder P 1 ↔ lawDefect P 1=0 := agrees_odd _ _
  rw [test,split_isometric_iff]
  have line : a=0 ↔ s.re=1/2 := by
    rw [show a=d*Real.log q.val from rfl,mul_eq_zero,or_iff_left (log_pos_prime q).ne']
    dsimp only [d]; constructor <;> intro h <;> linarith only [h]
  rw [←line]
  obtain ⟨hn,align,bounded⟩ := packet_grid p
  letI := hn
  have formula (v : ℝ) : Real.exp (v*a*27/2)*lawDefect P v=
      profile (p.val : ℝ) (Real.exp (v*a)) := by
    rw [gibbs_defect]
    exact (weighted_defect (packet p) align bounded (v*a)).trans
      (packet_difference p (Real.exp (v*a)))
  constructor
  · rintro ⟨root,flat⟩
    by_contra ha
    have hz : profile (p.val : ℝ) (Real.exp a)=0 := by simpa only [one_mul,root,mul_zero] using (formula 1).symm
    have dg : DifferentiableAt ℝ (fun v : ℝ => Real.exp (v*a*27/2)) 1 := by fun_prop
    have slope := dg.hasDerivAt.mul flat
    change HasDerivAt (fun v => Real.exp (v*a*27/2)*lawDefect P v) _ 1 at slope
    rw [show (fun v => Real.exp (v*a*27/2)*lawDefect P v)=_ from funext formula] at slope
    simp only [root,mul_zero,add_zero] at slope
    exact simple_profile ha (Nat.one_lt_cast.mpr p.property.one_lt) hz slope
  · intro ha
    have zero : lawDefect P=fun _ => 0 := by
      funext v
      rw [gibbs_defect]
      change oddTrace _ (v*a)=0
      simp only [ha,mul_zero,oddTrace,oddTerm,zero_mul,neg_zero,sub_self,sum_const_zero]
    rw [zero]
    exact ⟨rfl,hasDerivAt_const 1 0⟩

/-- Both the equality and the tangent can be read as finite sums of
centered negative log probabilities, without changing the preparation. -/
theorem stationary_statistic (p q : Nat.Primes) (s : ℂ) :
    let P := _root_.HTGeometry.finiteGibbsStateWeight (2*s.re-1) (primeModes q (packet p))
    let u := centered (Observation.information P)
    (lawOrder P 1 ∧ (∑ i, u i*(Real.exp (u i)+Real.exp (-u i)))=0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  let P := _root_.HTGeometry.finiteGibbsStateWeight (2*s.re-1) (primeModes q (packet p))
  have derivative := defect_derivative P
  dsimp only at derivative ⊢
  refine Iff.trans ?_ (stationary_isometry p q s)
  exact and_congr_right fun _ => ⟨fun eq => eq ▸ derivative,fun h => derivative.unique h⟩

#print axioms packet_sum
#print axioms stationary_isometry
#print axioms stationary_statistic

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
