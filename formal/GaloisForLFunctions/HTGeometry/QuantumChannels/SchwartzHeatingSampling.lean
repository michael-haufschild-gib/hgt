import GaloisForLFunctions.HTGeometry.QuantumChannels.SchwartzHeatingIdentifiability
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TwoChannelHeatingThreshold

/-!
# Exact channel and sample bounds for Schwartz heating

The positive cone of real momentum polynomials is exactly the image of
position-square heating for two polynomial jumps. Integration of the two
slopes preserves the claimed degree bound. A single jump realizes precisely
the polynomial squares. Sampling the momentum symbol recovers the full
Schwartz operator with the sharp sequential thresholds.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.PolynomialJump.Schwartz
open ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
open ExclusionOfTheCriticalState.ProbeWalk.JumpGrid

def heatOperator (P : ℝ[X]) := momentum (P.map Complex.ofRealHom)

theorem heatOperator_injective : Function.Injective heatOperator :=
  momentum_injective.comp (Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective)

private def pairJumps {d : ℕ} (U : Pair d) : Fin 2 → ℝ[X] := ![primitive U.1.val,primitive U.2.val]

private theorem pair_operator {d : ℕ} (U : Pair d) :
    bankHeating (pairJumps U)=heatOperator (pairSymbol U) := by
  rw [bank_symbol]
  simp only [realSymbol,pairJumps,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    derivative_primitive,pairSymbol,heatOperator]

private theorem symbol_degree {k : ℕ} (F : Fin k → ℝ[X]) (d : ℕ) (h : ∀ i, (F i).natDegree≤d+1) :
    (realSymbol F).natDegree≤2*d := by
  have aux (s : Finset (Fin k)) : (∑ i ∈ s, (F i).derivative^2).natDegree≤2*d := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [sum_insert hi]
      apply (natDegree_add_le _ _).trans (max_le _ ih)
      rw [natDegree_pow,natDegree_derivative]
      exact Nat.mul_le_mul_left _ (by have le := h i; omega)
  exact aux univ

/-- Which polynomial multipliers on Schwartz space can occur as heating from
two real jumps of degree at most d+1? -/
theorem two_jump_operator_cone (d : ℕ) (H : ℝ[X]) :
    (∃ F : Fin 2 → ℝ[X], (∀ i, (F i).natDegree≤d+1) ∧ bankHeating F=heatOperator H) ↔
      H.natDegree≤2*d ∧ ∀ x : ℝ, 0≤H.eval x := by
  constructor
  · rintro ⟨F,deg,he⟩
    rw [bank_symbol] at he
    have hs : realSymbol F=H := heatOperator_injective he
    rw [← hs]
    exact ⟨symbol_degree F d deg,fun x => by
      simp only [realSymbol,eval_finsetSum,eval_pow]
      exact sum_nonneg fun i _ => sq_nonneg _⟩
  · intro h
    obtain ⟨U,he⟩ := (two_channel_cone d H).mpr h
    refine ⟨pairJumps U,fun i => ?_,by rw [pair_operator,he]⟩
    fin_cases i
    · exact (primitive_degree _).trans (Nat.add_le_add_right U.1.property 1)
    · exact (primitive_degree _).trans (Nat.add_le_add_right U.2.property 1)

/-- Every finite jump bank admits an equivalent pair at the same degree
bound, with equality as continuous operators on Schwartz space. -/
theorem two_jump_compression {k : ℕ} (d : ℕ) (F : Fin k → Channel (d+1)) :
    ∃ G : Fin 2 → ℝ[X], (∀ i, (G i).natDegree≤d+1) ∧ bankHeating G=bankHeating (fun i => (F i).val) := by
  let J := fun i => (F i).val
  rw [show (fun i => (F i).val)=J from rfl,bank_symbol]
  apply (two_jump_operator_cone d (realSymbol J)).mpr
  exact ⟨symbol_degree J d (fun i => (F i).property),fun x => by
    simp only [realSymbol,eval_finsetSum,eval_pow]
    exact sum_nonneg fun _ _ => sq_nonneg _⟩

/-- One channel realizes precisely the real polynomial squares. -/
theorem one_jump_operator_cone (H : ℝ[X]) :
    (∃ f : ℝ[X], bankHeating (fun _ : Fin 1 => f)=heatOperator H) ↔ ∃ P : ℝ[X], H=P^2 := by
  have eq (f : ℝ[X]) : bankHeating (fun _ : Fin 1 => f)=heatOperator (f.derivative^2) := by
    rw [bank_symbol]
    simp only [realSymbol,Fin.sum_univ_one,heatOperator]
  constructor
  · rintro ⟨f,h⟩
    rw [eq] at h
    exact ⟨_,(heatOperator_injective h).symm⟩
  · rintro ⟨P,rfl⟩
    exact ⟨primitive P,by rw [eq,derivative_primitive]⟩

/-- Distinct operators from two jumps can match any 2d adaptive readings
of their momentum multipliers. One more fixed reading suffices. -/
theorem two_jump_operator_threshold (d n : ℕ) :
    (∃ T : Policy, ∀ U V : Pair d,
      readings T (pairSymbol U).eval n=readings T (pairSymbol V).eval n →
        bankHeating (pairJumps U)=bankHeating (pairJumps V)) ↔ 2*d<n := by
  simpa only [pair_operator,heatOperator_injective.eq_iff] using two_channel_sequential_threshold d n

/-- The single-channel threshold transfers to the operator through the
injective functional calculus and the polynomial primitive. -/
theorem single_jump_operator_threshold (d n : ℕ) (hd : 0<d) :
    (∃ T : Policy, ∀ P Q : Channel d, history T P.val n=history T Q.val n →
      bankHeating (fun _ : Fin 1 => primitive P.val)=bankHeating (fun _ : Fin 1 => primitive Q.val)) ↔
        d+2≤n := by
  have eq (P Q : Channel d) : bankHeating (fun _ : Fin 1 => primitive P.val)=
      bankHeating (fun _ : Fin 1 => primitive Q.val) ↔ power P.val=power Q.val := by
    rw [bank_heating_iff,funext_iff]
    simp only [Fin.sum_univ_one,derivative_primitive,power]
  simpa only [eq] using sequential_threshold d hd n

#print axioms two_jump_operator_cone
#print axioms two_jump_compression
#print axioms one_jump_operator_cone
#print axioms two_jump_operator_threshold
#print axioms single_jump_operator_threshold
end GaloisForLFunctions.PolynomialJump.Schwartz
