import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ObservationDepth

/-!
# The two-copy heat on all words and on equal labels

The full word partition is the square of the prime-gas partition.
Identifying both labels doubles the inverse temperature. Complementary
word tests split the trace wherever the full heat is trace class.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks CopyExchange
open scoped Classical

abbrev Word := Bool → ℕ+

def full (_ : Word) : Prop := True
def equal (x : Word) : Prop := x false = x true

/-- The actual binary word test at sampling time t and angular aperture θ. -/
def measured (t θ : ℝ) := (binary t).Repeated (Real.sqrt (aperture θ))

def partition (P : Word → Prop) (s : ℂ) := ∑' x : {x // P x}, wordHeat s x.val

theorem operator_trace (P : Word → Prop) (s : {z : ℂ // AbsoluteHeat P z}) :
    ContinuousLinearMap.opTrace (sectorHeat P s) = partition P s.val := sectorHeat_trace P s

private def fullWords : Word ≃ {x // full x} :=
  ⟨fun x => ⟨x,trivial⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩

private def equalWords : ℕ+ ≃ {x // equal x} where
  toFun n := ⟨fun _ => n,rfl⟩
  invFun x := x.val false
  left_inv _ := rfl
  right_inv x := Subtype.ext (funext fun b => by cases b; exact rfl; exact x.property)

private theorem equal_weight (s : ℂ) (n : ℕ+) : wordHeat s (equalWords n).val = heat (2*s) n := by
  change (∏ _ : Bool, heat s n) = _
  rw [Fintype.prod_bool,← heat_add,two_mul]

theorem full_summable (s : ℂ) : (Summable fun x : Word => ‖wordHeat s x‖) ↔ 1 < s.re := by
  change (Summable fun x : Word => ‖∏ i, heat s (x i)‖) ↔ _
  exact (independent_heat_summable_iff (fun _ : Bool => s)).trans ⟨fun h => h false,fun h _ => h⟩

theorem full_heat (s : ℂ) : HasSectorHeat full s ↔ 1 < s.re := by
  rw [sectorHeat_iff,AbsoluteHeat,← fullWords.summable_iff]
  exact full_summable s

theorem equal_heat (s : ℂ) : HasSectorHeat equal s ↔ 1/2 < s.re := by
  rw [sectorHeat_iff,AbsoluteHeat,← equalWords.summable_iff]
  change (Summable fun n => ‖wordHeat s (equalWords n).val‖) ↔ _
  simp only [equal_weight,heat_abs_summable,two_mul,Complex.add_re]
  constructor <;> intro h <;> linarith only [h]

theorem full_partition (s : {z : ℂ // 1 < z.re}) : partition full s.val = riemannZeta s.val ^ 2 := by
  rw [partition,← fullWords.tsum_eq]
  have h := (FamilyContinuationTheory.hasSum_pi_prod (fun (_ : Bool) n => heat s.val n)
    (fun _ => riemannZeta s.val) (fun _ => heat_hasSum s) (fun _ => (heat_abs_summable s.val).mpr s.property)).1.tsum_eq
  exact h.trans (by rw [Fintype.prod_bool,sq])

theorem equal_partition (s : {z : ℂ // 1/2 < z.re}) : partition equal s.val = riemannZeta (2*s.val) := by
  have hs : 1 < (2*s.val).re := by simpa [Complex.mul_re] using (show 1 < 2*s.val.re by linarith only [s.property])
  rw [partition,← equalWords.tsum_eq]
  change (∑' n, wordHeat s.val (equalWords n).val) = _
  simp only [equal_weight]
  exact (heat_hasSum ⟨_,hs⟩).tsum_eq

/-- Absolute convergence on complementary sectors gives absolute convergence on the full gas. -/
theorem join_heat (P : Word → Prop) (s : ℂ) (hp : HasSectorHeat P s)
    (hq : HasSectorHeat (fun x => ¬P x) s) : HasSectorHeat full s := by
  apply (full_heat s).mpr
  apply (full_summable s).mp
  exact (summable_subtype_and_compl (s := {x | P x})).mp
    ⟨(sectorHeat_iff _ _).mp hp,(sectorHeat_iff _ _).mp hq⟩

/-- Additivity of the two operator partitions above the full-gas boundary. -/
theorem partition_complement (P : Word → Prop) (s : {z : ℂ // 1 < z.re}) :
    partition P s.val + partition (fun x => ¬P x) s.val = riemannZeta s.val ^ 2 := by
  have hs := ((full_summable s.val).mpr s.property).of_norm
  rw [← full_partition s,partition,partition,partition,← fullWords.tsum_eq]
  exact hs.tsum_subtype_add_tsum_subtype_compl {x | P x}

#print axioms full_heat
#print axioms equal_heat
#print axioms full_partition
#print axioms equal_partition
#print axioms partition_complement

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
