import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianConjugacyFibers
import GaloisForLFunctions.RepresentationLifting.Actions.RegularBimoduleKernels

/-!
# Modular orbital operators on the Hermitian translation group

An abscissa fiber acts by summing along fibers and translating the result
on the square constant field. Nonzero abscissae are single conjugacy
classes. Two such operators compose to Q times the operator at the sum.
In characteristic p all products vanish although each operator has rank Q².
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis.Codes RepresentationLifting
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "k" => SquareConstantField p s
local notation "G" => HermitianAffinePoint p s k
local notation "π" => (fun P : G => Prod.fst (Subtype.val P))
local instance baseFintype : Fintype k := Fintype.ofFinite _
local instance pointFintype : Fintype G := Fintype.ofFinite _
variable (K : Type*) [Field K]
local notation "W" => G → K
local notation "E" => Module.End K W

/-- Sum a word over every abscissa fiber. -/
def hermitianFiberSum : W →ₗ[K] (k → K) where
  toFun f x := ∑ y : {y : G // π y = x}, f y.val
  map_add' f g := by funext x; exact Finset.sum_add_distrib
  map_smul' c f := by funext x; exact (Finset.mul_sum ..).symm

local notation "S" => hermitianFiberSum p s K

/-- Every list of fiber sums is attained, even in the defining characteristic. -/
theorem hermitianFiberSum_surjective : Function.Surjective S := by
  intro h
  let c := hermitianAffinePointWithFirst p s
  refine ⟨fun y => if y = c (π y) then h (π y) else 0, ?_⟩
  funext x
  let r : {y : G // π y = x} := ⟨c x,rfl⟩
  change (∑ y : {y : G // π y = x}, if y.val = c (π y.val) then h (π y.val) else 0) = h x
  rw [Finset.sum_eq_single r]
  · rw [r.property, if_pos rfl]
  · intro y _ hy
    rw [y.property, if_neg (fun he => hy (Subtype.ext he))]
  · exact fun hn => (hn (Finset.mem_univ _)).elim

/-- Pulling back a base word and summing it along a fiber multiplies it by Q. -/
theorem hermitianFiberSum_pullback (h : k → K) : S (h ∘ π) = ((Q:ℕ) : K) • h := by
  funext x
  change (∑ y : {y : G // π y = x}, h (π y.val)) = ((Q:ℕ):K)*h x
  have hcard : Nat.card {y : G // π y=x} = Q := hermitianFirstCoordinate_fiber_card p s x
  calc
    _ = ∑ _y : {y : G // π y=x}, h x := Finset.sum_congr rfl fun y _ => congrArg h y.property
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,hcard]

/-- The counting orbital operator of an abscissa displacement. -/
def hermitianOrbitalOperator (a : k) : E where
  toFun f P := S f (π P + a)
  map_add' f g := by funext P; exact congrFun (map_add S f g) _
  map_smul' c f := by funext P; exact congrFun (map_smul S c f) _

local notation "O" => hermitianOrbitalOperator p s K

/-- Entries of the orbital matrix are the indicators of the required abscissa displacements. -/
theorem hermitianOrbitalOperator_entry (a : k) (P U : G) :
    O a (fun X => if X = U then 1 else 0) P = if π U = π P+a then 1 else 0 := by
  change (∑ y : {y : G // π y = π P+a}, if y.val = U then (1:K) else 0) = _
  by_cases h : π U = π P+a
  · let r : {y : G // π y = π P+a} := ⟨U,h⟩
    rw [if_pos h,Finset.sum_eq_single r]
    · exact if_pos rfl
    · exact fun y _ hy => if_neg (fun he => hy (Subtype.ext he))
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    apply if_neg
    exact fun he => h ((congrArg π he).symm.trans y.property)

/-- At nonzero abscissa, this matrix is literally the convolution kernel of one conjugacy class. -/
theorem hermitianOrbitalOperator_conjugacy_kernel (A P U : G) (ha : π A ≠ 0) :
    O (π A) (fun X => if X=U then 1 else 0) P =
      if IsConj A (P⁻¹*U) then 1 else 0 := by
  rw [hermitianOrbitalOperator_entry]
  have he : IsConj A (P⁻¹*U) ↔ π U = π P + π A := by
    rw [hermitianTranslation_isConj_iff]
    change (π A = -π P + π U ∧ (π A = 0 → _)) ↔ _
    constructor
    · rintro ⟨h,_⟩
      linear_combination -h
    · exact fun h => ⟨by linear_combination -h,fun h0 => (ha h0).elim⟩
  by_cases h : IsConj A (P⁻¹*U)
  · rw [if_pos h,if_pos (he.1 h)]
  · rw [if_neg h,if_neg (fun h' => h (he.2 h'))]

/-- Each counting operator has exactly the pullback code as its image. -/
theorem hermitianOrbitalOperator_range (a : k) :
    (O a).range = fiberCode (K := K) π := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨fun x => S g (x+a),rfl⟩
  · rintro ⟨h,rfl⟩
    obtain ⟨g,hg⟩ := hermitianFiberSum_surjective p s K (fun x => h (x-a))
    refine ⟨g,?_⟩
    funext P
    change S g (π P + a) = h (π P)
    rw [hg]
    exact congrArg h (add_sub_cancel_right (π P) a)

/-- The common kernel consists precisely of words whose sum on every fiber is zero. -/
theorem hermitianOrbitalOperator_ker (a : k) : (O a).ker = (S).ker := by
  ext f
  change O a f = 0 ↔ S f = 0
  constructor
  · intro h
    funext x
    let P := hermitianAffinePointWithFirst p s (x-a)
    have he := congrFun h P
    change S f ((x-a)+a) = 0 at he
    rwa [sub_add_cancel] at he
  · intro h
    funext P
    change S f (π P+a) = 0
    rw [h]; rfl

/-- Rank of an individual orbital is Q² in every characteristic. -/
theorem hermitianOrbitalOperator_rank (a : k) :
    Module.finrank K (O a).range = Q^2 := by
  rw [hermitianOrbitalOperator_range]
  calc
    _ = Fintype.card k := fiberCode_finrank (K := K) π (hermitianFirstCoordinate_surjective p s)
    _ = _ := by rw [← Nat.card_eq_fintype_card,squareConstantField_card,Nat.mul_comm 2 (s+1),pow_mul]

/-- Convolution of abscissa orbitals has one intersection number, the fiber size Q. -/
theorem hermitianOrbitalOperator_mul (a b : k) : O a * O b = ((Q:ℕ):K) • O (a+b) := by
  apply LinearMap.ext
  intro f
  funext P
  have h := hermitianFiberSum_pullback p s K (fun x => S f (x+b))
  have he := congrFun h (π P+a)
  change S (fun U => S f (π U+b)) (π P+a) = ((Q:ℕ):K)*S f (π P+(a+b))
  simpa only [Function.comp_def,Pi.smul_apply,smul_eq_mul,add_assoc] using he

/-- These operators are linearly independent even when the counting product is zero. -/
theorem hermitianOrbitalOperator_linearIndependent : LinearIndependent K O := by
  rw [linearIndependent_iff]
  intro l hl
  ext x
  let h : k → K := fun t => if t=x then 1 else 0
  obtain ⟨f,hf⟩ := hermitianFiberSum_surjective p s K h
  let P := hermitianAffinePointWithFirst p s 0
  have he := congrArg (fun T : E => T f P) hl
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.zero_apply, Pi.zero_apply] at he
  change (∑ i ∈ l.support, l i * S f (0+i)) = 0 at he
  simpa [hf,h,Finset.sum_ite_eq',Finsupp.mem_support_iff] using he

/-- The span of the counting operators has dimension Q² over every coefficient field. -/
theorem hermitianOrbitalSpan_dimension : Module.finrank K (Submodule.span K (Set.range O)) = Q^2 := by
  rw [finrank_span_eq_card (hermitianOrbitalOperator_linearIndependent p s K),
    ← Nat.card_eq_fintype_card, squareConstantField_card, Nat.mul_comm 2 (s+1), pow_mul]

/-- In other characteristics, the zero-displacement mean projects onto the abscissa code. -/
theorem hermitianOrbital_mean_idempotent (hq : ((Q:ℕ):K) ≠ 0) :
    let M := (((Q:ℕ):K)⁻¹) • O 0
    M*M = M := by
  dsimp only
  rw [smul_mul_assoc, mul_smul_comm, hermitianOrbitalOperator_mul, add_zero, smul_smul (((Q:ℕ):K)⁻¹) ((Q:ℕ):K),
    inv_mul_cancel₀ hq, one_smul]

/-- The normalized abscissa orbitals multiply by the additive group law on displacements. -/
theorem hermitianOrbital_normalized_product (hq : ((Q:ℕ):K) ≠ 0) (a b : k) :
    ((((Q:ℕ):K)⁻¹) • O a) * ((((Q:ℕ):K)⁻¹) • O b) = (((Q:ℕ):K)⁻¹) • O (a+b) := by
  rw [smul_mul_assoc, mul_smul_comm, hermitianOrbitalOperator_mul, smul_smul (((Q:ℕ):K)⁻¹) ((Q:ℕ):K),
    inv_mul_cancel₀ hq, one_smul]

/-- Characteristic p gives a square-zero space of counting orbitals of dimension Q². -/
theorem hermitianOrbitalSpan_squareZero [CharP K p] :
    ∀ A ∈ Submodule.span K (Set.range O), ∀ B ∈ Submodule.span K (Set.range O), A*B = 0 := by
  have hc : ((Q:ℕ):K) = 0 := by rw [Nat.cast_pow, CharP.cast_eq_zero K p, zero_pow (Nat.succ_ne_zero s)]
  intro A hA B hB
  induction hA using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨a,rfl⟩ := hX
    induction hB using Submodule.span_induction with
    | mem Y hY => obtain ⟨b,rfl⟩ := hY; rw [hermitianOrbitalOperator_mul, hc, zero_smul]
    | zero => exact mul_zero _
    | add X Y _ _ hx hy => rw [mul_add (O a) X Y,hx,hy,add_zero]
    | smul c X _ hx => rw [mul_smul_comm,hx,smul_zero]
  | zero => exact zero_mul _
  | add X Y _ _ hx hy => rw [add_mul X Y B,hx,hy,add_zero]
  | smul c X _ hx => rw [smul_mul_assoc,hx,smul_zero]

/-- The full regular bimodule commutant has one parameter per class per ordered copy-pair. -/
theorem hermitianRegularBimodule_dimension (ι : Type*) [Fintype ι] :
    Module.finrank K (regularBimoduleKernels ι G K) =
      Fintype.card ι ^ 2 * (Q + (Q^2 - 1)) := by
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [regularBimoduleKernels_finrank, ← Nat.card_eq_fintype_card (α := ConjClasses G),
    hermitian_translation_class_number]

#print axioms hermitianFiberSum_pullback
#print axioms hermitianOrbitalOperator_entry
#print axioms hermitianOrbitalOperator_conjugacy_kernel
#print axioms hermitianOrbital_mean_idempotent
#print axioms hermitianOrbital_normalized_product
#print axioms hermitianFiberSum_surjective
#print axioms hermitianOrbitalOperator_range
#print axioms hermitianOrbitalOperator_ker
#print axioms hermitianOrbitalOperator_rank
#print axioms hermitianOrbitalOperator_mul
#print axioms hermitianOrbitalOperator_linearIndependent
#print axioms hermitianOrbitalSpan_dimension
#print axioms hermitianOrbitalSpan_squareZero
#print axioms hermitianRegularBimodule_dimension

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
