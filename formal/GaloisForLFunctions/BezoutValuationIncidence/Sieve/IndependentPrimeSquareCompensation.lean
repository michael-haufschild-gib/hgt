import GaloisForLFunctions.BezoutValuationIncidence.Sieve.MomentsOfTheCompensatedEgyptianFractionSieve
import GaloisForLFunctions.RHTower.PrimeSquareMobiusSectorFracture

/-!
# Compensation on a product of prime squares

The Chinese remainder theorem identifies a primitive triple modulo the
product with one primitive lift at each prime. The compensated weight
has mean one on this exact sample. Its moments and support probabilities
multiply, even when the local units and rays vary with the prime.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Nat.Primes)
local instance primeFact (i : ι) : Fact (p i).val.Prime := ⟨(p i).property⟩
local instance squareNeZero (i : ι) : NeZero ((p i).val^2) := ⟨pow_ne_zero _ (p i).property.ne_zero⟩

abbrev Combined := ZMod (∏ i, (p i).val^2)
private abbrev Triple (R : Type*) := (R × R) × R

private def tripleCRT (h : Function.Injective p) :
    Triple (Combined p) ≃ ∀ i, Triple (RingAt (p i).val 1) := by
  let e := RHTower.eulerClockCRT (fun i => (p i).val) (fun i j hij =>
    ((Nat.coprime_primes (p i).property (p j).property).2
      (fun he => hij (h (Subtype.ext he)))).pow 2 2)
  exact
    { toFun := fun t i => ((e t.1.1 i,e t.1.2 i),e t.2 i)
      invFun := fun f => ((e.symm (fun i => (f i).1.1),e.symm (fun i => (f i).1.2)),
        e.symm (fun i => (f i).2))
      left_inv := fun t => by simp
      right_inv := fun f => by funext i; simp }

private def primitiveAt (q : Nat.Primes) (t : Triple (RingAt q.val 1)) : Prop :=
  (reduce q.val 1 t.1.1,reduce q.val 1 t.1.2) ≠ (0,0)

/-- Primitive triples represented by three residues modulo the single product. -/
def CombinedPrimitive (h : Function.Injective p) :=
  {t : Triple (Combined p) // ∀ i, primitiveAt (p i) (tripleCRT p h t i)}

/-- CRT followed by the low-digit decomposition at each prime. -/
def primitiveCRT (h : Function.Injective p) : CombinedPrimitive p h ≃ ∀ i, High (p i).val :=
  ((tripleCRT p h).subtypeEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun i => (rawEquiv (p i).val 1).symm))

noncomputable instance (h : Function.Injective p) : Fintype (CombinedPrimitive p h) :=
  Fintype.ofEquiv _ (primitiveCRT p h).symm

private theorem mean_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    mean (fun x => f (e x))=mean f := by rw [mean,mean,e.sum_comp,Fintype.card_congr e]

private theorem mean_product {X : ι → Type*} [∀ i, Fintype (X i)] (f : ∀ i, X i → ℝ) :
    mean (fun x : ∀ i, X i => ∏ i, f i (x i)) = ∏ i, mean (f i) := by
  simp only [mean,prod_div_distrib,Fintype.card_pi,Nat.cast_prod]
  rw [prod_univ_sum (fun i => (univ : Finset (X i))) f,Fintype.piFinset_univ]

variable (h : Function.Injective p) (K : ∀ i, (RingAt (p i).val 1)ˣ)
  (r : ∀ i, (ZMod (p i).val)ˣ)

def globalWeight (x : CombinedPrimitive p h) :=
  ∏ i, weight (p i).val (K i) (r i) (primitiveCRT p h x i)

theorem product_moment (k : ℕ) :
    mean (fun x => (globalWeight p h K r x)^(k+1)) =
      ∏ i, (1+(((p i).val : ℝ)^(k+1)-(p i).val)*rayMass (p i).val) := by
  let f (i : ι) (x : High (p i).val) := (weight (p i).val (K i) (r i) x)^(k+1)
  calc
    _ = mean (fun x : ∀ i, High (p i).val => ∏ i, f i (x i)) := by
      rw [← mean_equiv (primitiveCRT p h)]
      simp only [globalWeight,Finset.prod_pow,f]
    _ = ∏ i, mean (f i) := mean_product f
    _ = _ := prod_congr rfl fun i _ => moment (p i).val (K i) (r i) k

theorem global_mean_one : mean (globalWeight p h K r)=1 := by
  simpa using product_moment p h K r 0

/-- Uniform probability that the compensated sieve weight is nonzero. -/
theorem product_support :
    mean (mark (fun x => globalWeight p h K r x≠0)) =
      ∏ i, (1-(((p i).val : ℝ)-1)*rayMass (p i).val) := by
  let f (i : ι) := mark (fun x => weight (p i).val (K i) (r i) x≠0)
  have indicator (x : CombinedPrimitive p h) :
      mark (fun y => globalWeight p h K r y ≠ 0) x = ∏ i, f i (primitiveCRT p h x i) := by
    by_cases ha : ∀ i, weight (p i).val (K i) (r i) (primitiveCRT p h x i)≠0
    · simp [mark,globalWeight,prod_ne_zero_iff,ha,f]
    · push Not at ha
      obtain ⟨i,hi⟩ := ha
      have hg : globalWeight p h K r x=0 := prod_eq_zero (mem_univ i) hi
      rw [prod_eq_zero (mem_univ i) (show f i (primitiveCRT p h x i)=0 by simp [f,mark,hi])]
      simp [mark,hg]
  rw [show mark (fun y => globalWeight p h K r y≠0) =
      (fun x => ∏ i, f i (primitiveCRT p h x i)) from funext indicator,
    mean_equiv (primitiveCRT p h) (fun x => ∏ i, f i (x i)),mean_product]
  exact prod_congr rfl fun i _ => support_mass (p i).val (K i) (r i)

private theorem second_factor (q : Nat.Primes) :
    1+((q.val : ℝ)^2-q.val)*rayMass q.val =
      1+((q.val : ℝ)-1)^2/(q.val*(q.val+1)) := by
  have hq : 0<(q.val : ℝ) := Nat.cast_pos.mpr q.property.pos
  unfold rayMass
  field_simp

/-- A uniform exponential lower bound for the second moment. -/
theorem product_second_floor :
    (7/6 : ℝ)^Fintype.card ι ≤ mean (fun x => (globalWeight p h K r x)^2) := by
  rw [product_moment p h K r 1,← card_univ,← prod_const]
  refine prod_le_prod (fun _ _ => by norm_num) fun i _ => ?_
  rw [second_factor]
  have hp₂ : (2 : ℝ)≤(p i).val := by exact_mod_cast (p i).property.two_le
  have hp' : 0<((p i).val : ℝ) := by linarith only [hp₂]
  have den : 0 < ((p i).val : ℝ)*((p i).val+1) := by positivity
  rw [← sub_le_iff_le_add',le_div_iff₀ den]
  nlinarith only [mul_nonneg (show 0≤((p i).val : ℝ)-2 by linarith only [hp₂])
    (show 0≤5*((p i).val : ℝ)-3 by linarith only [hp₂])]

/-- The third moment per prime, divided by p, is the cyclotomic factor Φ₆(1/p). -/
theorem third_factor (q : Nat.Primes) :
    (1+((q.val : ℝ)^3-q.val)*rayMass q.val)/q.val =
      1-(q.val : ℝ)⁻¹+((q.val : ℝ)⁻¹)^2 := by
  have hq : 0<(q.val : ℝ) := Nat.cast_pos.mpr q.property.pos
  unfold rayMass
  field_simp
  ring

end GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments

#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.product_moment
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.global_mean_one
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.product_support
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.product_second_floor
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.third_factor
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.primitiveCRT
