import GaloisForLFunctions.HTGeometry.Quantum.IntegerEdgeCostsForJointChargeObservation
import GaloisForLFunctions.CollectiveDiophantineGeometry.VerticalFrequenciesOfAnIntegerLattice
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Which phases can be distinguished with arbitrarily many copies?

For integer charges, every surviving phase frequency belongs to an explicit
subgroup of the integers. Its positive generator, when nonzero, gives the
exact residual ambiguity. Equivalently the invisible phases are precisely
those whose action on the occupied entries is a change of charge reference.
-/

noncomputable section
open Finset Matrix
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

open CollectiveDiophantineGeometry.Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The generator of the vertical lattice. Normalize the first row before
taking the gcd of its two-by-two minors. -/
def frequencyStep {E : Type*} [Fintype E] (q b : E → ℤ) : ℤ :=
  if q=0 then content b else content (minorColumn (fun i => q i / content q) b)

private theorem step_iff {E : Type*} [Fintype E] [DecidableEq E] (q b : E → ℤ) (d : ℤ) :
    d∈vertical q b ↔ frequencyStep q b∣d := by
  classical
  by_cases hz : q=0
  · simpa only [frequencyStep,hz,if_true] using vertical_iff q b d
  have hw : q=content q • (fun i => q i / content q) := by
    funext i
    exact (Int.mul_ediv_cancel' (gcd_dvd (mem_univ i) : content q ∣ q i)).symm
  rw [frequencyStep,if_neg hz,normalized_minors_generate q b hz _ hw,dot_range]

/-- All-copy support is exactly one arithmetic lattice, including the
singleton support when every balanced displacement vanishes. -/
theorem some_copy_iff_divisible (q b : ι → ℤ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (d : ℤ) :
    (∃ n, d∈frequencies q b A n) ↔ frequencyStep (edgeGap q (A:=A)) (edgeGap b) ∣ d := by
  rw [some_copy_iff q b hA]
  exact step_iff _ _ d

/-- The stabilizer across every tensor power is given by a single circle
character, even for disconnected support and missing diagonal entries. -/
theorem all_copies_iff_step (q b : ι → ℤ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (z w : Circle) :
    (∀ n, observe q (twist b z A) n=observe q (twist b w A) n) ↔
      z^(frequencyStep (edgeGap q (A:=A)) (edgeGap b))=w^(frequencyStep (edgeGap q (A:=A)) (edgeGap b)) := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := (some_copy_iff_divisible q b hA _).2 dvd_rfl
    exact (indistinguishable_iff q b A n z w).1 (h n) _ hn
  · intro h n
    apply (indistinguishable_iff q b A n z w).2
    intro d hd
    obtain ⟨k,rfl⟩ := (some_copy_iff_divisible q b hA d).1 ⟨n,hd⟩
    rw [_root_.zpow_mul,_root_.zpow_mul,h]

theorem circle_root (g : ℤ) (hg : g≠0) (x : Circle) : ∃ t : Circle, t^g=x := by
  obtain ⟨a,rfl⟩ := Circle.exp_surjective x
  refine ⟨Circle.exp (a/g),?_⟩
  rw [← Circle.exp_intCast_mul]
  congr 1
  field_simp [show (g : ℝ)≠0 by exact_mod_cast hg]

theorem product_character {E : Type*} (s : Finset E) (x : Circle) (c b : E → ℤ) :
    x^(∑ e ∈ s, c e*b e)=∏ e ∈ s, (x^(b e))^(c e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert e s he ih =>
    rw [sum_insert he,prod_insert he,_root_.zpow_add,ih,mul_comm (c e) (b e),_root_.zpow_mul]

/-- A circle phase annihilates every balanced integer combination exactly
when it agrees on every column with one common charge character. -/
theorem gauge_extension {E : Type*} [Fintype E] [DecidableEq E] (q b : E → ℤ) (x : Circle) :
    (∀ d ∈ vertical q b, x^d=1) ↔ ∃ t : Circle, ∀ i, x^(b i)=t^(q i) := by
  constructor
  · intro h
    by_cases hz : q=0
    · refine ⟨1,fun i => ?_⟩
      rw [_root_.one_zpow]
      exact h _ ⟨Pi.single i 1,by rw [hz,dotProduct_zero],by rw [single_dotProduct,one_mul]⟩
    obtain ⟨v,u,hv,hu⟩ := primitive_direction q hz
    have hg : content q≠0 := fun he => hz (by simpa only [he,zero_smul] using hv)
    obtain ⟨t,ht⟩ := circle_root _ hg (x^(u ⬝ᵥ b))
    refine ⟨t,fun i => ?_⟩
    have hd : b i-v i*(u ⬝ᵥ b)∈vertical q b := by
      refine ⟨Pi.single i 1 - v i • u,?_,?_⟩
      · rw [sub_dotProduct,single_dotProduct,one_mul,smul_dotProduct]
        conv_lhs => rw [hv,dotProduct_smul,hu]
        change content q*v i-v i*(content q*1)=0
        ring
      · simp only [sub_dotProduct,single_dotProduct,one_mul,smul_dotProduct,smul_eq_mul]
    have he := h _ hd
    rw [_root_.zpow_sub,← div_eq_mul_inv,div_eq_one] at he
    rw [he,mul_comm (v i),_root_.zpow_mul,← ht,← _root_.zpow_mul,congrFun hv i,Pi.smul_apply,smul_eq_mul]
  · rintro ⟨t,ht⟩ d ⟨c,hc,rfl⟩
    change x^(∑ e, c e*b e)=1
    rw [product_character]
    simp only [ht]
    rw [← product_character]
    change t^(c ⬝ᵥ q)=1
    rw [hc,_root_.zpow_zero]

/-- No number of copies separates two twists precisely when their ratio
on each occupied edge is induced by one global change of charge phase. -/
theorem all_copies_iff_gauge (q b : ι → ℤ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (z w : Circle) :
    (∀ n, observe q (twist b z A) n=observe q (twist b w A) n) ↔
      ∃ t : Circle, ∀ e : Edge A, (z/w)^(edgeGap b e)=t^(edgeGap q e) := by
  rw [← gauge_extension]
  constructor
  · intro h d hd
    obtain ⟨n,hn⟩ := (some_copy_iff q b hA d).2 hd
    rw [div_zpow,div_eq_one]
    exact (indistinguishable_iff q b A n z w).1 (h n) d hn
  · intro h n
    apply (indistinguishable_iff q b A n z w).2
    intro d hd
    have he := h d ((some_copy_iff q b hA d).1 ⟨n,hd⟩)
    simpa only [div_zpow,div_eq_one] using he

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.some_copy_iff_divisible
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.all_copies_iff_step
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.gauge_extension
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.all_copies_iff_gauge

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.product_character

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.circle_root
