import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittCanonicalMultiplication

/-!
# Canonicity of integral big-Witt multiplication

Lenstra's characterization of the big-Witt product requires more than existence of ring laws:
every multiplication which is natural in the coefficient ring, distributive for ordinary
power-series multiplication, and multiplicative on Teichmüller factors must be the canonical
product.  Naturality supplies the missing continuity.  Indeed, a coefficient of the product of
two universal Euler vectors is an integer polynomial and therefore involves only finitely many
Euler variables.  After killing the remaining variables, the inputs are finite polynomials.
They split after an injective passage to an algebraic closure, where distributivity and the
Teichmüller law determine their product.

The final descent evaluates the universal integer polynomial in an arbitrary commutative ring.
No reducedness, torsion-freeness, field, or target ghost-injectivity hypothesis occurs.
-/

namespace RHTower

noncomputable section

open scoped BigOperators Classical

open PowerSeries

universe u

/-- A candidate big-Witt multiplication in one universe.  Its laws are precisely the three
properties in Lenstra's uniqueness theorem: functoriality, distributivity for the literal
additive group, and the Teichmüller-factor formula. -/
@[ext] structure DeningerBigWittMultiplicationLaw where
  mul : ∀ (A : Type u) [CommRing A],
    DeningerBigWittAdditive A → DeningerBigWittAdditive A → DeningerBigWittAdditive A
  natural : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (x y),
    deningerBigWittMap f (mul A x y) =
      mul B (deningerBigWittMap f x) (deningerBigWittMap f y)
  left_distrib : ∀ (A : Type u) [CommRing A] (x y z),
    mul A x (y * z) = mul A x y * mul A x z
  right_distrib : ∀ (A : Type u) [CommRing A] (x y z),
    mul A (x * y) z = mul A x z * mul A y z
  teich : ∀ (A : Type u) [CommRing A] (a b : A),
    mul A (deningerBigWittTeichCarrier a) (deningerBigWittTeichCarrier b) =
      deningerBigWittTeichCarrier (a * b)

/-- The integral gcd--lcm Euler product is a multiplication law in Lenstra's sense. -/
noncomputable def deningerCanonicalBigWittMultiplicationLaw :
    DeningerBigWittMultiplicationLaw.{u} where
  mul := fun _ _ => deningerBigWittMul
  natural := fun f x y => deningerBigWittMul_natural f x y
  left_distrib := fun _ _ x y z => deningerBigWittMul_add x y z
  right_distrib := fun _ _ x y z => deningerBigWittAdd_mul x y z
  teich := fun _ _ a b => deningerBigWittMul_teich a b

/-- Universe-lifted variable indices for two universal Euler vectors. -/
def DeningerBigWittUniquenessIndex := ULift.{u} (Fin 2 × ℕ)

/-- Free integer ring containing the Euler coordinates of two universal big-Witt vectors. -/
abbrev DeningerBigWittUniquenessRing :=
  MvPolynomial (DeningerBigWittUniquenessIndex.{u}) ℤ

def deningerBigWittUniquenessUniversalCoord (i : Fin 2) (n : ℕ) :
    DeningerBigWittUniquenessRing.{u} :=
  MvPolynomial.X (ULift.up (i, n))

def deningerBigWittUniquenessUniversalVector (i : Fin 2) :
    DeningerBigWittAdditive DeningerBigWittUniquenessRing.{u} :=
  deningerBigWittEulerEquiv DeningerBigWittUniquenessRing.{u}
    (deningerBigWittUniquenessUniversalCoord i)

/-- Simultaneous evaluation of the two universal Euler-coordinate families. -/
def deningerBigWittUniquenessUniversalEval {A : Type u} [CommRing A]
    (x : Fin 2 → DeningerBigWittAdditive A) :
    DeningerBigWittUniquenessRing.{u} →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) fun i =>
    (deningerBigWittEulerEquiv A).symm (x i.down.1) i.down.2

@[simp] theorem deningerBigWittUniquenessUniversalEval_vector
    {A : Type u} [CommRing A]
    (x : Fin 2 → DeningerBigWittAdditive A) (i : Fin 2) :
    deningerBigWittMap (deningerBigWittUniquenessUniversalEval x)
        (deningerBigWittUniquenessUniversalVector i) = x i := by
  rw [deningerBigWittUniquenessUniversalVector, deningerBigWittEulerEquiv_natural]
  calc
    deningerBigWittEulerEquiv A
        (deningerBigWittUniquenessUniversalEval x ∘
          deningerBigWittUniquenessUniversalCoord i) =
      deningerBigWittEulerEquiv A
        ((deningerBigWittEulerEquiv A).symm (x i)) := by
          congr 1
          funext n
          simp [deningerBigWittUniquenessUniversalEval,
            deningerBigWittUniquenessUniversalCoord]
    _ = x i := (deningerBigWittEulerEquiv A).apply_symm_apply (x i)

/-- Universal integer polynomial producing coefficient `k` for a candidate multiplication law. -/
def deningerBigWittMultiplicationPolynomial
    (law : DeningerBigWittMultiplicationLaw.{u}) (k : ℕ) :
    DeningerBigWittUniquenessRing.{u} :=
  PowerSeries.coeff k (deningerBigWittSeries
    (law.mul DeningerBigWittUniquenessRing.{u}
      (deningerBigWittUniquenessUniversalVector 0)
      (deningerBigWittUniquenessUniversalVector 1)))

/-- Automatic polynomiality/continuity: each output coefficient of every natural candidate law is
the evaluation of one finite integer polynomial in the two Euler-coordinate families. -/
theorem DeningerBigWittMultiplicationLaw.coeff_eq_eval_universalPolynomial
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] (x y : DeningerBigWittAdditive A) (k : ℕ) :
    PowerSeries.coeff k (deningerBigWittSeries (law.mul A x y)) =
      deningerBigWittUniquenessUniversalEval (![x, y])
        (deningerBigWittMultiplicationPolynomial law k) := by
  let z : Fin 2 → DeningerBigWittAdditive A := ![x, y]
  let ev := deningerBigWittUniquenessUniversalEval z
  have h := law.natural ev
    (deningerBigWittUniquenessUniversalVector 0)
    (deningerBigWittUniquenessUniversalVector 1)
  have hc := congrArg
    (fun w : DeningerBigWittAdditive A =>
      PowerSeries.coeff k (deningerBigWittSeries w)) h
  have hx : deningerBigWittMap ev
      (deningerBigWittUniquenessUniversalVector 0) = x := by
    simp [ev, z]
  have hy : deningerBigWittMap ev
      (deningerBigWittUniquenessUniversalVector 1) = y := by
    simp [ev, z]
  simpa only [deningerBigWittSeries_map, PowerSeries.coeff_map, hx, hy,
    deningerBigWittMultiplicationPolynomial, ev, z] using hc.symm

private noncomputable def deningerBigWittUniquenessTruncEval (N : ℕ) :
    DeningerBigWittUniquenessRing.{u} →+* DeningerBigWittUniquenessRing.{u} :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => if i.down.2 < N then MvPolynomial.X i else 0)

private theorem deningerBigWittUniquenessTruncEval_eq_self
    {p : DeningerBigWittUniquenessRing.{u}} {N : ℕ}
    (hN : ∀ i ∈ p.vars, i.down.2 < N) :
    deningerBigWittUniquenessTruncEval N p = p := by
  change MvPolynomial.eval₂ MvPolynomial.C
      (fun i => if i.down.2 < N then MvPolynomial.X i else 0) p = p
  calc
    _ = MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X p :=
      MvPolynomial.eval₂_congr (p := p) (f := MvPolynomial.C)
        (fun i => if i.down.2 < N then MvPolynomial.X i else 0)
        MvPolynomial.X (fun {i} {d} hid hcoeff => by
          rw [if_pos (hN i ((MvPolynomial.mem_vars_iff_mem_support i).mpr
            ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, hid⟩))])
    _ = p := MvPolynomial.eval₂_eta p

private def deningerBigWittUniquenessBound
    (p q : DeningerBigWittUniquenessRing.{u}) : ℕ :=
  (p.vars ∪ q.vars).sup (fun i => i.down.2) + 1

private theorem deningerBigWittUniqueness_lt_bound_left
    (p q : DeningerBigWittUniquenessRing.{u}) (i) (hi : i ∈ p.vars) :
    i.down.2 < deningerBigWittUniquenessBound p q := by
  apply Nat.lt_succ_of_le
  exact Finset.le_sup
    (f := fun i : DeningerBigWittUniquenessIndex.{u} => i.down.2) (by simp [hi])

private theorem deningerBigWittUniqueness_lt_bound_right
    (p q : DeningerBigWittUniquenessRing.{u}) (i) (hi : i ∈ q.vars) :
    i.down.2 < deningerBigWittUniquenessBound p q := by
  apply Nat.lt_succ_of_le
  exact Finset.le_sup
    (f := fun i : DeningerBigWittUniquenessIndex.{u} => i.down.2) (by simp [hi])

private theorem deningerBigWittUniquenessTruncEval_universalVector
    (N : ℕ) (i : Fin 2) :
    deningerBigWittMap (deningerBigWittUniquenessTruncEval N)
        (deningerBigWittUniquenessUniversalVector i) =
      deningerBigWittEulerEquiv DeningerBigWittUniquenessRing.{u}
        (fun n => if n < N then deningerBigWittUniquenessUniversalCoord i n else 0) := by
  rw [deningerBigWittUniquenessUniversalVector, deningerBigWittEulerEquiv_natural]
  congr 1
  funext n
  simp [deningerBigWittUniquenessUniversalCoord,
    deningerBigWittUniquenessTruncEval]

private def deningerBigWittPolynomialCarrier {A : Type*} [CommRing A]
    (P : Polynomial A) (hP : P.coeff 0 = 1) : DeningerBigWittAdditive A :=
  deningerBigWittOfSeries P.toPowerSeries (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simpa [Polynomial.toPowerSeries] using hP)

private theorem deningerBigWittAtomPolynomialCarrier_eq_prod_teich
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    deningerBigWittPolynomialCarrier (deningerRationalWittAtomPolynomial s)
        (deningerRationalWittAtomPolynomial_coeff_zero s) =
      (s.map fun a : Kˣ => deningerBigWittTeichCarrier (a : K)).prod := by
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittAtomPolynomial s).toPowerSeries =
    deningerBigWittSeries
      ((s.map fun a : Kˣ => deningerBigWittTeichCarrier (a : K)).prod)
  induction s using Multiset.induction_on with
  | empty =>
      apply PowerSeries.ext
      intro n
      simp only [deningerRationalWittAtomPolynomial, Multiset.map_zero,
        Multiset.prod_zero, deningerBigWittSeries, Polynomial.coeff_coe]
      rw [Polynomial.coeff_one]
      change (if n = 0 then 1 else 0) = PowerSeries.coeff n (1 : PowerSeries K)
      rw [PowerSeries.coeff_one]
  | @cons a s ih =>
      rw [show deningerRationalWittAtomPolynomial (a ::ₘ s) =
          deningerRationalWittTeichmullerPolynomial (a : K) *
            deningerRationalWittAtomPolynomial s by
        simp [deningerRationalWittAtomPolynomial]]
      rw [show (deningerRationalWittTeichmullerPolynomial (a : K) *
          deningerRationalWittAtomPolynomial s : Polynomial K).toPowerSeries =
        (deningerRationalWittTeichmullerPolynomial (a : K)).toPowerSeries *
          (deningerRationalWittAtomPolynomial s).toPowerSeries by
            exact map_mul Polynomial.coeToPowerSeries.ringHom _ _]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      change _ = deningerBigWittSeries (deningerBigWittTeichCarrier (a : K)) *
        deningerBigWittSeries
          ((s.map fun b : Kˣ => deningerBigWittTeichCarrier (b : K)).prod)
      rw [← ih, deningerBigWittSeries_teichCarrier]
      simp [deningerRationalWittTeichmullerPolynomial, deningerBigWittFactor]

private theorem deningerBigWittPolynomialCarrier_eq_prod_teich
    {K : Type*} [Field K] [IsAlgClosed K]
    (P : Polynomial K) (hP : P.coeff 0 = 1) :
    deningerBigWittPolynomialCarrier P hP =
      ((deningerNormalizedPolynomialRootUnits P hP).map fun a : Kˣ =>
        deningerBigWittTeichCarrier (a : K)).prod := by
  let s := deningerNormalizedPolynomialRootUnits P hP
  have hPs : P = deningerRationalWittAtomPolynomial s := by
    simpa only [s, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits P hP
  apply Subtype.ext
  apply Units.ext
  change P.toPowerSeries = deningerBigWittSeries
    ((s.map fun a : Kˣ => deningerBigWittTeichCarrier (a : K)).prod)
  rw [hPs]
  exact congrArg deningerBigWittSeries
    (deningerBigWittAtomPolynomialCarrier_eq_prod_teich s)

private def deningerBigWittEulerPartialPolynomial {A : Type*} [CommRing A]
    (x : ℕ → A) (N : ℕ) : Polynomial A :=
  ∏ i ∈ Finset.range N, (1 - Polynomial.C (x i) * Polynomial.X ^ (i + 1))

@[simp] private theorem deningerBigWittEulerPartialPolynomial_coeff_zero
    {A : Type*} [CommRing A] (x : ℕ → A) (N : ℕ) :
    (deningerBigWittEulerPartialPolynomial x N).coeff 0 = 1 := by
  change Polynomial.constantCoeff (deningerBigWittEulerPartialPolynomial x N) = 1
  simp [deningerBigWittEulerPartialPolynomial]

private theorem deningerBigWittEulerPartialPolynomial_toPowerSeries
    {A : Type*} [CommRing A] (x : ℕ → A) (N : ℕ) :
    (deningerBigWittEulerPartialPolynomial x N).toPowerSeries =
      deningerBigWittEulerPartial x N := by
  change Polynomial.coeToPowerSeries.ringHom
    (deningerBigWittEulerPartialPolynomial x N) = _
  simp [deningerBigWittEulerPartialPolynomial, deningerBigWittEulerPartial,
    deningerBigWittFactor]

private theorem deningerBigWittEulerSeries_truncate
    {A : Type*} [CommRing A] (x : ℕ → A) (N : ℕ) :
    deningerBigWittEulerSeries (fun n => if n < N then x n else 0) =
      deningerBigWittEulerPartial x N := by
  apply PowerSeries.ext
  intro k
  rw [deningerBigWittEulerSeries_coeff]
  by_cases hk : k ≤ N
  · have hpartial : deningerBigWittEulerPartial
        (fun n => if n < N then x n else 0) k =
        deningerBigWittEulerPartial x k := by
      unfold deningerBigWittEulerPartial
      apply Finset.prod_congr rfl
      intro i hi
      rw [show (fun n => if n < N then x n else 0) i = x i by
        simp [(Finset.mem_range.mp hi).trans_le hk]]
    rw [hpartial]
    exact (deningerBigWittEulerPartial_coeff_stable x
      (k := k) (N := k) (M := N) le_rfl hk).symm
  · have hNk : N ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    have hpartial : deningerBigWittEulerPartial
        (fun n => if n < N then x n else 0) k =
        deningerBigWittEulerPartial x N := by
      unfold deningerBigWittEulerPartial
      calc
        (∏ i ∈ Finset.range k,
            deningerBigWittFactor ((fun n => if n < N then x n else 0) i) (i + 1)) =
            ∏ i ∈ Finset.range N,
              deningerBigWittFactor ((fun n => if n < N then x n else 0) i) (i + 1) := by
                apply (Finset.prod_subset (Finset.range_mono hNk) ?_).symm
                intro i hik hiN
                rw [show (fun n => if n < N then x n else 0) i = 0 by
                  simp [by simpa using hiN]]
                simp
        _ = ∏ i ∈ Finset.range N, deningerBigWittFactor (x i) (i + 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [show (fun n => if n < N then x n else 0) i = x i by
            simp [Finset.mem_range.mp hi]]
    rw [hpartial]

private theorem deningerBigWittEulerEquiv_truncate_eq_polynomialCarrier
    {A : Type*} [CommRing A] (x : ℕ → A) (N : ℕ) :
    deningerBigWittEulerEquiv A (fun n => if n < N then x n else 0) =
      deningerBigWittPolynomialCarrier (deningerBigWittEulerPartialPolynomial x N)
        (deningerBigWittEulerPartialPolynomial_coeff_zero x N) := by
  apply Subtype.ext
  apply Units.ext
  change deningerBigWittEulerSeries (fun n => if n < N then x n else 0) =
    (deningerBigWittEulerPartialPolynomial x N).toPowerSeries
  rw [deningerBigWittEulerSeries_truncate,
    deningerBigWittEulerPartialPolynomial_toPowerSeries]

theorem DeningerBigWittMultiplicationLaw.mul_additiveZero_left
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] (y : DeningerBigWittAdditive A) :
    law.mul A 1 y = 1 := by
  have h := law.right_distrib A (1 : DeningerBigWittAdditive A) 1 y
  have h' : law.mul A 1 y = law.mul A 1 y * law.mul A 1 y := by
    simpa using h
  apply mul_left_cancel (a := law.mul A 1 y)
  simpa using h'.symm

theorem DeningerBigWittMultiplicationLaw.mul_additiveZero_right
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] (x : DeningerBigWittAdditive A) :
    law.mul A x 1 = 1 := by
  have h := law.left_distrib A x (1 : DeningerBigWittAdditive A) 1
  have h' : law.mul A x 1 = law.mul A x 1 * law.mul A x 1 := by
    simpa using h
  apply mul_left_cancel (a := law.mul A x 1)
  simpa using h'.symm

private def deningerBigWittPairTeich {A : Type*} [CommRing A]
    (s t : Multiset Aˣ) : Multiset (DeningerBigWittAdditive A) :=
  s.bind fun a => t.map fun b =>
    deningerBigWittTeichCarrier ((a * b : Aˣ) : A)

private theorem DeningerBigWittMultiplicationLaw.mul_teich_prod
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] (a : Aˣ) (t : Multiset Aˣ) :
    law.mul A (deningerBigWittTeichCarrier (a : A))
        ((t.map fun b : Aˣ => deningerBigWittTeichCarrier (b : A)).prod) =
      (t.map fun b : Aˣ =>
        deningerBigWittTeichCarrier ((a * b : Aˣ) : A)).prod := by
  induction t using Multiset.induction_on with
  | empty => simp [law.mul_additiveZero_right]
  | @cons b t ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [law.left_distrib, law.teich, ih]
      rfl

private theorem DeningerBigWittMultiplicationLaw.mul_prod_teich
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] (s t : Multiset Aˣ) :
    law.mul A
        ((s.map fun a : Aˣ => deningerBigWittTeichCarrier (a : A)).prod)
        ((t.map fun b : Aˣ => deningerBigWittTeichCarrier (b : A)).prod) =
      (deningerBigWittPairTeich s t).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [law.mul_additiveZero_left, deningerBigWittPairTeich]
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [law.right_distrib, law.mul_teich_prod, ih]
      simp [deningerBigWittPairTeich]

private theorem deningerBigWittMap_injective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (deningerBigWittMap f) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply PowerSeries.map_injective f hf
  change PowerSeries.map f (deningerBigWittSeries x) =
    PowerSeries.map f (deningerBigWittSeries y)
  simpa only [deningerBigWittSeries_map] using congrArg deningerBigWittSeries hxy

private def deningerBigWittAlgebraicClosureMap
    (A : Type*) [CommRing A] [IsDomain A] :
    A →+* AlgebraicClosure (FractionRing A) :=
  (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).comp
    (algebraMap A (FractionRing A))

private theorem deningerBigWittAlgebraicClosureMap_injective
    (A : Type*) [CommRing A] [IsDomain A] :
    Function.Injective (deningerBigWittAlgebraicClosureMap A) := by
  exact (RingHom.injective (algebraMap (FractionRing A)
      (AlgebraicClosure (FractionRing A)))).comp
    (IsFractionRing.injective A (FractionRing A))

/-- Finite Euler products are already forced by the three defining properties.  The proof passes
injectively to an algebraic closure, splits both polynomials, and uses distributivity. -/
theorem DeningerBigWittMultiplicationLaw.mul_eq_canonical_of_finiteEuler
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] [IsDomain A]
    (x y : ℕ → A) (N : ℕ) :
    law.mul A
        (deningerBigWittEulerEquiv A (fun n => if n < N then x n else 0))
        (deningerBigWittEulerEquiv A (fun n => if n < N then y n else 0)) =
      deningerBigWittMul
        (deningerBigWittEulerEquiv A (fun n => if n < N then x n else 0))
        (deningerBigWittEulerEquiv A (fun n => if n < N then y n else 0)) := by
  let L := AlgebraicClosure (FractionRing A)
  let ι : A →+* L := deningerBigWittAlgebraicClosureMap A
  apply deningerBigWittMap_injective ι
    (deningerBigWittAlgebraicClosureMap_injective A)
  rw [law.natural, deningerBigWittMul_natural]
  have hxmap : deningerBigWittMap ι
      (deningerBigWittEulerEquiv A (fun n => if n < N then x n else 0)) =
      deningerBigWittEulerEquiv L (fun n => if n < N then ι (x n) else 0) := by
    rw [deningerBigWittEulerEquiv_natural]
    congr 1
    funext n
    by_cases hn : n < N <;> simp [hn]
  have hymap : deningerBigWittMap ι
      (deningerBigWittEulerEquiv A (fun n => if n < N then y n else 0)) =
      deningerBigWittEulerEquiv L (fun n => if n < N then ι (y n) else 0) := by
    rw [deningerBigWittEulerEquiv_natural]
    congr 1
    funext n
    by_cases hn : n < N <;> simp [hn]
  rw [hxmap, hymap]
  rw [deningerBigWittEulerEquiv_truncate_eq_polynomialCarrier,
    deningerBigWittEulerEquiv_truncate_eq_polynomialCarrier]
  rw [deningerBigWittPolynomialCarrier_eq_prod_teich,
    deningerBigWittPolynomialCarrier_eq_prod_teich]
  rw [law.mul_prod_teich]
  exact (deningerCanonicalBigWittMultiplicationLaw.mul_prod_teich L _ _).symm

/-- On the free integer ring of two universal Euler vectors, every candidate multiplication is
the canonical integral gcd--lcm product.  Finite support of each coefficient supplies the required
truncation without a separately assumed topology. -/
theorem DeningerBigWittMultiplicationLaw.mul_universal_eq_canonical
    (law : DeningerBigWittMultiplicationLaw.{u}) :
    law.mul DeningerBigWittUniquenessRing.{u}
        (deningerBigWittUniquenessUniversalVector 0)
        (deningerBigWittUniquenessUniversalVector 1) =
      deningerBigWittMul
        (deningerBigWittUniquenessUniversalVector 0)
        (deningerBigWittUniquenessUniversalVector 1) := by
  apply Subtype.ext
  apply Units.ext
  apply PowerSeries.ext
  intro k
  let p : DeningerBigWittUniquenessRing.{u} := PowerSeries.coeff k
    (deningerBigWittSeries
      (law.mul DeningerBigWittUniquenessRing.{u}
        (deningerBigWittUniquenessUniversalVector 0)
        (deningerBigWittUniquenessUniversalVector 1)))
  let q : DeningerBigWittUniquenessRing.{u} := PowerSeries.coeff k
    (deningerBigWittSeries
      (deningerBigWittMul
        (deningerBigWittUniquenessUniversalVector 0)
        (deningerBigWittUniquenessUniversalVector 1)))
  let N := deningerBigWittUniquenessBound p q
  have hpfix : deningerBigWittUniquenessTruncEval N p = p :=
    deningerBigWittUniquenessTruncEval_eq_self
      (fun i hi => deningerBigWittUniqueness_lt_bound_left p q i hi)
  have hqfix : deningerBigWittUniquenessTruncEval N q = q :=
    deningerBigWittUniquenessTruncEval_eq_self
      (fun i hi => deningerBigWittUniqueness_lt_bound_right p q i hi)
  have hlawNat := law.natural (deningerBigWittUniquenessTruncEval N)
    (deningerBigWittUniquenessUniversalVector 0)
    (deningerBigWittUniquenessUniversalVector 1)
  have hlawCoeff := congrArg
    (fun w : DeningerBigWittAdditive DeningerBigWittUniquenessRing.{u} =>
      PowerSeries.coeff k (deningerBigWittSeries w)) hlawNat
  have hlawCoeff' : p = PowerSeries.coeff k (deningerBigWittSeries
      (law.mul DeningerBigWittUniquenessRing.{u}
        (deningerBigWittEulerEquiv DeningerBigWittUniquenessRing.{u}
          (fun n => if n < N then deningerBigWittUniquenessUniversalCoord 0 n else 0))
        (deningerBigWittEulerEquiv DeningerBigWittUniquenessRing.{u}
          (fun n => if n < N then deningerBigWittUniquenessUniversalCoord 1 n else 0)))) := by
    rw [deningerBigWittUniquenessTruncEval_universalVector,
      deningerBigWittUniquenessTruncEval_universalVector] at hlawCoeff
    simpa only [deningerBigWittSeries_map, PowerSeries.coeff_map, p, hpfix] using
      hlawCoeff
  have hcanonicalNat := deningerBigWittMul_natural
    (deningerBigWittUniquenessTruncEval N)
    (deningerBigWittUniquenessUniversalVector 0)
    (deningerBigWittUniquenessUniversalVector 1)
  have hcanonicalCoeff := congrArg
    (fun w : DeningerBigWittAdditive DeningerBigWittUniquenessRing.{u} =>
      PowerSeries.coeff k (deningerBigWittSeries w)) hcanonicalNat
  have hcanonicalCoeff' : q = PowerSeries.coeff k (deningerBigWittSeries
      (deningerBigWittMul
        (deningerBigWittEulerEquiv DeningerBigWittUniquenessRing.{u}
          (fun n => if n < N then deningerBigWittUniquenessUniversalCoord 0 n else 0))
        (deningerBigWittEulerEquiv DeningerBigWittUniquenessRing.{u}
          (fun n => if n < N then deningerBigWittUniquenessUniversalCoord 1 n else 0)))) := by
    rw [deningerBigWittUniquenessTruncEval_universalVector,
      deningerBigWittUniquenessTruncEval_universalVector] at hcanonicalCoeff
    simpa only [deningerBigWittSeries_map, PowerSeries.coeff_map, q, hqfix] using
      hcanonicalCoeff
  have hfinite := law.mul_eq_canonical_of_finiteEuler
    DeningerBigWittUniquenessRing.{u}
    (deningerBigWittUniquenessUniversalCoord 0)
    (deningerBigWittUniquenessUniversalCoord 1) N
  have hfiniteCoeff := congrArg
    (fun w : DeningerBigWittAdditive DeningerBigWittUniquenessRing.{u} =>
      PowerSeries.coeff k (deningerBigWittSeries w)) hfinite
  change p = q
  exact hlawCoeff'.trans (hfiniteCoeff.trans hcanonicalCoeff'.symm)

/-- Lenstra uniqueness over every commutative ring, including rings with nilpotents.  No
continuity hypothesis is needed: it follows coefficientwise from naturality. -/
theorem DeningerBigWittMultiplicationLaw.mul_eq_canonical
    (law : DeningerBigWittMultiplicationLaw.{u})
    (A : Type u) [CommRing A] (x y : DeningerBigWittAdditive A) :
    law.mul A x y = deningerBigWittMul x y := by
  let z : Fin 2 → DeningerBigWittAdditive A := ![x, y]
  let ev := deningerBigWittUniquenessUniversalEval z
  have h := congrArg (deningerBigWittMap ev) law.mul_universal_eq_canonical
  rw [law.natural, deningerBigWittMul_natural] at h
  have hx : deningerBigWittMap ev
      (deningerBigWittUniquenessUniversalVector 0) = x := by
    simp [ev, z]
  have hy : deningerBigWittMap ev
      (deningerBigWittUniquenessUniversalVector 1) = y := by
    simp [ev, z]
  simpa only [hx, hy] using h

/-- The functorial distributive Teichmüller multiplication law is unique. -/
theorem deningerBigWittMultiplicationLaw_unique
    (law₁ law₂ : DeningerBigWittMultiplicationLaw.{u}) : law₁ = law₂ := by
  apply DeningerBigWittMultiplicationLaw.ext
  funext A inst x y
  exact (law₁.mul_eq_canonical A x y).trans
    (law₂.mul_eq_canonical A x y).symm

/-- Structural form of the global canonicity theorem. -/
noncomputable instance deningerBigWittMultiplicationLaw_subsingleton :
    Subsingleton DeningerBigWittMultiplicationLaw.{u} :=
  ⟨deningerBigWittMultiplicationLaw_unique⟩

end

end RHTower
