import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CyclicTrace
import GaloisForLFunctions.FamilyContinuationTheory.TheSeriesOfAMultiplicativeFunctionIsItsEulerProduct

/-!
# The fixed labels of a copy permutation

A fixed tuple is one positive integer per cycle. Its heat weights factor into
independent logarithmic gases, with inverse temperature multiplied by the
cycle length. Varying one integer proves necessity of every convergence bound.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open scoped Classical

variable {I : Type*}

/-- Cycles, including singleton fixed positions, are the quotient by successive permutation steps. -/
def Cycle (π : Equiv.Perm I) := Quot (fun i j => π i = j)

def cycleOf (π : Equiv.Perm I) (i : I) : Cycle π := Quot.mk _ i

theorem cycleOf_step (π : Equiv.Perm I) (i : I) : cycleOf π (π i) = cycleOf π i := by
  symm
  exact Quot.sound (rfl : π i = π i)

theorem cycleOf_surjective (π : Equiv.Perm I) : Function.Surjective (cycleOf π) :=
  fun c => Quot.inductionOn c fun i => ⟨i,rfl⟩

noncomputable instance cycleFintype [Fintype I] (π : Equiv.Perm I) : Fintype (Cycle π) :=
  @Fintype.ofFinite _ (Finite.of_surjective _ (cycleOf_surjective π))

def cycleLength [Fintype I] (π : Equiv.Perm I) (c : Cycle π) := Fintype.card {i : I // cycleOf π i = c}

theorem cycleLength_pos [Fintype I] (π : Equiv.Perm I) (c : Cycle π) : 0 < cycleLength π c := by
  obtain ⟨i,hi⟩ := cycleOf_surjective π c
  exact Fintype.card_pos_iff.mpr ⟨⟨i,hi⟩⟩

abbrev FixedWord (π : Equiv.Perm I) := {x : I → ℕ+ // x ∘ π = x}

/-- Choose the common integer label on each cycle. -/
def fixedWords (π : Equiv.Perm I) : (Cycle π → ℕ+) ≃ FixedWord π where
  toFun u := ⟨fun i => u (cycleOf π i),funext fun i => congrArg u (cycleOf_step π i)⟩
  invFun x := Quot.lift x.val (by
    intro i j hij
    exact (congrFun x.property i).symm.trans (congrArg x.val hij))
  left_inv u := funext fun c => Quot.inductionOn c fun _ => rfl
  right_inv x := Subtype.ext rfl

def wordHeat [Fintype I] (s : ℂ) (x : I → ℕ+) : ℂ := ∏ i, heat s (x i)

/-- Multiplying the copy labels gives the total energy label of the tuple. -/
theorem wordHeat_total [Fintype I] (s : ℂ) (x : I → ℕ+) :
    wordHeat s x = heat s (∏ i, x i) := by
  let h : ℕ+ →* ℂ := ⟨⟨heat s,by simp [heat,energy]⟩,heat_mul s⟩
  exact (map_prod h x Finset.univ).symm

theorem wordHeat_add [Fintype I] (s t : ℂ) (x : I → ℕ+) :
    wordHeat (s+t) x = wordHeat s x * wordHeat t x := by
  simp only [wordHeat,heat_add,Finset.prod_mul_distrib]

theorem heat_nat_mul (k : ℕ) (s : ℂ) (n : ℕ+) : heat ((k : ℂ)*s) n = heat s n ^ k := by
  induction k with
  | zero => simp [heat]
  | succ k ih => rw [Nat.cast_succ,add_mul,one_mul,heat_add,ih,pow_succ]

theorem fixedWord_weight [Fintype I] (π : Equiv.Perm I) (s : ℂ) (u : Cycle π → ℕ+) :
    wordHeat s (fixedWords π u).val = ∏ c, heat ((cycleLength π c : ℂ)*s) (u c) := by
  change (∏ i, heat s (u (cycleOf π i))) = _
  rw [← Fintype.prod_fiberwise' (cycleOf π) (fun c => heat s (u c))]
  simp only [Finset.prod_const,Finset.card_univ,cycleLength,heat_nat_mul]

theorem heat_abs_summable (s : ℂ) : (Summable fun n => ‖heat s n‖) ↔ 1 < s.re := by
  have he (n : ℕ+) : ‖heat s n‖ = ‖heat (s/2) n‖^2 := by
    rw [sq, ← norm_mul, ← heat_add,add_halves]
  simp_rw [he]
  rw [summable_heat_sq_iff,Complex.div_ofNat_re]
  constructor <;> intro h <;> linarith only [h]

theorem heat_hasSum (s : {w : ℂ // 1 < w.re}) : HasSum (heat s.val) (riemannZeta s.val) := by
  have hs := ((heat_abs_summable s.val).mpr s.property).of_norm
  have h : (∑' n, heat s.val n) = riemannZeta s.val := by
    rw [← partition_eq_zeta s,gibbsOperator,HilbertSchmidt.opTrace_diagOp_comp]
    exact tsum_congr fun n => by rw [← heat_add,add_halves]
  exact h ▸ hs.hasSum

/-- Each cycle has its own trace-class inequality. -/
def InCycleDomain [Fintype I] (π : Equiv.Perm I) (s : ℂ) : Prop :=
  ∀ c : Cycle π, 1 < (cycleLength π c : ℝ) * s.re

private theorem cycle_re [Fintype I] (π : Equiv.Perm I) (c : Cycle π) (s : ℂ) :
    ((cycleLength π c : ℂ)*s).re = (cycleLength π c : ℝ) * s.re := by simp [Complex.mul_re]

theorem cycleDomain_of_trace [Fintype I] (π : Equiv.Perm I) (s : {w : ℂ // 1 < w.re}) :
    InCycleDomain π s.val := by
  intro c
  have hc : (1 : ℝ) ≤ cycleLength π c := by exact_mod_cast (show 1 ≤ cycleLength π c from cycleLength_pos π c)
  exact lt_of_lt_of_le s.property (le_mul_of_one_le_left (by linarith only [s.property]) hc)

def cyclePartition [Fintype I] (π : Equiv.Perm I) (s : ℂ) : ℂ :=
  ∏ c, riemannZeta ((cycleLength π c : ℂ)*s)

private theorem factored_sum [Fintype I] (π : Equiv.Perm I) (s : ℂ) (h : InCycleDomain π s) :
    HasSum (fun u => wordHeat s (fixedWords π u).val) (cyclePartition π s) ∧
    Summable (fun u => ‖wordHeat s (fixedWords π u).val‖) := by
  have hc (c : Cycle π) : 1 < ((cycleLength π c : ℂ)*s).re := by rw [cycle_re]; exact h c
  simpa only [fixedWord_weight, cyclePartition] using
    FamilyContinuationTheory.hasSum_pi_prod (fun c n => heat ((cycleLength π c : ℂ)*s) n)
      (fun c => riemannZeta ((cycleLength π c : ℂ)*s))
      (fun c => heat_hasSum ⟨_,hc c⟩) (fun c => (heat_abs_summable _).mpr (hc c))

theorem fixed_sum [Fintype I] (π : Equiv.Perm I) (s : ℂ) (h : InCycleDomain π s) :
    (∑' x : FixedWord π, wordHeat s x.val) = cyclePartition π s := by
  rw [← (fixedWords π).tsum_eq (fun x => wordHeat s x.val)]
  exact (factored_sum π s h).1.tsum_eq

/-- Independent copies with different complex temperatures must each be trace summable. -/
theorem independent_heat_summable_iff (t : I → ℂ) [Fintype I] :
    (Summable fun u : I → ℕ+ => ‖∏ i, heat (t i) (u i)‖) ↔ ∀ i, 1 < (t i).re := by
  constructor
  · intro hs i
    let line (n : ℕ+) : I → ℕ+ := Function.update (fun _ => 1) i n
    have hi : Function.Injective line := by
      intro a b hab
      simpa [line] using congrFun hab i
    have he (n : ℕ+) : (∏ j, heat (t j) (line n j)) = heat (t i) n := by
      rw [Finset.prod_eq_single i]
      · simp [line]
      · intro j _ hj
        simp [line,Function.update_of_ne hj,heat,energy]
      · simp
    exact (heat_abs_summable _).mp ((hs.comp_injective hi).congr fun n => congrArg norm (he n))
  · intro h
    exact (FamilyContinuationTheory.hasSum_pi_prod (fun i n => heat (t i) n) (fun i => riemannZeta (t i))
      (fun i => heat_hasSum ⟨_,h i⟩) (fun i => (heat_abs_summable _).mpr (h i))).2

/-- Holding all other cycles in the vacuum isolates the ordinary series on any chosen cycle. -/
theorem fixed_summable_iff [Fintype I] (π : Equiv.Perm I) (s : ℂ) :
    (Summable fun x : FixedWord π => ‖wordHeat s x.val‖) ↔ InCycleDomain π s := by
  rw [← (fixedWords π).summable_iff]
  change (Summable fun u => ‖wordHeat s (fixedWords π u).val‖) ↔ _
  simpa only [fixedWord_weight,cycle_re,InCycleDomain] using
    independent_heat_summable_iff (fun c => (cycleLength π c : ℂ)*s)

#print axioms wordHeat_total
#print axioms fixedWords
#print axioms fixedWord_weight
#print axioms fixed_sum
#print axioms fixed_summable_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
