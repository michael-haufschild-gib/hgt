import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusDescent
import GaloisForLFunctions.RHTower.HyperellipticRiemannHypothesis

/-!
# Actual hyperelliptic Frobenius fixed counts

The image of a finite field embedding is exactly the fixed set of the
corresponding Frobenius power. Coordinatewise descent restricts this
equivalence to the curve equation and retains infinity. Quadratic-character
counting then identifies the actual fixed count with the reciprocal-root
power sum. A factorial ambient extension contains every field required by
the cycle lengths of a tuple of the given size.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Polynomial FiniteField
variable {F K E : Type*} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E]

/-- Actual affine solutions of the hyperelliptic equation. -/
abbrev HyperellipticAffinePoints (f : F[X]) (K : Type*) [Field K] [Algebra F K] :=
  {z : K × K // z.2 ^ 2 = aeval z.1 f}

/-- Affine solutions with one distinguished point, the infinity point in odd degree. -/
abbrev HyperellipticPoints (f : F[X]) (K : Type*) [Field K] [Algebra F K] :=
  Option (HyperellipticAffinePoints f K)

/-- Coordinatewise extension of scalars on actual affine points. -/
def hyperellipticAffineMap (f : F[X]) (e : K →ₐ[F] E)
    (z : HyperellipticAffinePoints f K) : HyperellipticAffinePoints f E :=
  ⟨(e z.val.1, e z.val.2), by
    rw [aeval_algHom_apply, ← map_pow, z.property]⟩

/-- Coordinatewise extension of scalars retains infinity. -/
def hyperellipticPointMap (f : F[X]) (e : K →ₐ[F] E) :
    HyperellipticPoints f K → HyperellipticPoints f E :=
  Option.map (hyperellipticAffineMap f e)

theorem hyperellipticPointMap_injective (f : F[X]) (e : K →ₐ[F] E) :
    Function.Injective (hyperellipticPointMap f e) := by
  have hi : Function.Injective (hyperellipticAffineMap f e) := by
    intro a b h
    apply Subtype.ext
    exact Prod.ext (e.injective (congrArg (fun z => z.val.1) h))
      (e.injective (congrArg (fun z => z.val.2) h))
  intro a b h
  cases a <;> cases b <;> simp_all [hyperellipticPointMap, hi.eq_iff]

/-- A field automorphism acts invertibly on the affine equation and infinity. -/
def hyperellipticPointEquiv (f : F[X]) (e : K ≃ₐ[F] E) :
    HyperellipticPoints f K ≃ HyperellipticPoints f E where
  toFun := hyperellipticPointMap f e.toAlgHom
  invFun := hyperellipticPointMap f e.symm.toAlgHom
  left_inv z := by
    cases z with
    | none => rfl
    | some z =>
      apply congrArg Option.some
      apply Subtype.ext
      exact Prod.ext (e.symm_apply_apply _) (e.symm_apply_apply _)
  right_inv z := by
    cases z with
    | none => rfl
    | some z =>
      apply congrArg Option.some
      apply Subtype.ext
      exact Prod.ext (e.apply_symm_apply _) (e.apply_symm_apply _)

variable (F E) [Fintype F] [Finite E]

/-- Arithmetic Frobenius on the actual point set. -/
def hyperellipticFrobenius (f : F[X]) : Equiv.Perm (HyperellipticPoints f E) :=
  hyperellipticPointEquiv f (frobeniusAlgEquivOfAlgebraic F E)

/-- Iteration of point Frobenius is coordinatewise iteration of field Frobenius. -/
theorem hyperellipticFrobenius_pow (f : F[X]) (n : ℕ) (z : HyperellipticPoints f E) :
    (hyperellipticFrobenius F E f ^ n) z =
      hyperellipticPointMap f (frobeniusAlgEquivOfAlgebraic F E ^ n).toAlgHom z := by
  induction n with
  | zero => cases z <;> rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ']
    cases z <;> rfl

variable (K) [Fintype K]

/-- Fixed point coordinates descend simultaneously along the actual field embedding. -/
theorem hyperellipticFrobenius_fixed_iff (f : F[X]) (e : K →ₐ[F] E)
    (z : HyperellipticPoints f E) :
    (hyperellipticFrobenius F E f ^ Module.finrank F K) z = z ↔
      ∃ w : HyperellipticPoints f K, hyperellipticPointMap f e w = z := by
  rw [hyperellipticFrobenius_pow]
  cases z with
  | none =>
    exact ⟨fun _ => ⟨none, rfl⟩, fun _ => rfl⟩
  | some z =>
    constructor
    · intro hz
      have hv := congrArg Subtype.val (Option.some.inj hz)
      have hx := congrArg Prod.fst hv
      have hy := congrArg Prod.snd hv
      obtain ⟨x, hx⟩ := (finiteField_frobenius_pow_fixed_iff F K E e z.val.1).mp hx
      obtain ⟨y, hy⟩ := (finiteField_frobenius_pow_fixed_iff F K E e z.val.2).mp hy
      have hxy : y ^ 2 = aeval x f := by
        apply e.injective
        change e (y ^ 2) = e (aeval x f)
        rw [map_pow, ← aeval_algHom_apply, hx, hy, z.property]
      refine ⟨some ⟨(x, y), hxy⟩, congrArg Option.some (Subtype.ext ?_)⟩
      exact Prod.ext hx hy
    · rintro ⟨w, hw⟩
      rw [← hw]
      cases w with
      | none => rfl
      | some w =>
        apply congrArg Option.some
        apply Subtype.ext
        exact Prod.ext
          ((finiteField_frobenius_pow_fixed_iff F K E e (e w.val.1)).mpr ⟨_, rfl⟩)
          ((finiteField_frobenius_pow_fixed_iff F K E e (e w.val.2)).mpr ⟨_, rfl⟩)

/-- Points over the embedded field are precisely the actual Frobenius fixed points. -/
def hyperellipticFrobeniusFixedEquiv (f : F[X]) (e : K →ₐ[F] E) :
    HyperellipticPoints f K ≃
      {z : HyperellipticPoints f E //
        (hyperellipticFrobenius F E f ^ Module.finrank F K) z = z} :=
  Equiv.ofBijective (fun w => ⟨hyperellipticPointMap f e w,
      (hyperellipticFrobenius_fixed_iff F K E f e _).mpr ⟨w, rfl⟩⟩)
    ⟨fun a b h => hyperellipticPointMap_injective f e (congrArg Subtype.val h), fun z => by
      obtain ⟨w, hw⟩ := (hyperellipticFrobenius_fixed_iff F K E f e z.val).mp z.property
      exact ⟨w, Subtype.ext hw⟩⟩

#print axioms hyperellipticPointMap_injective
#print axioms hyperellipticPointEquiv
#print axioms hyperellipticFrobenius_pow
#print axioms hyperellipticFrobenius_fixed_iff
#print axioms hyperellipticFrobeniusFixedEquiv
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Polynomial Finset FiniteField
open GaloisForLFunctions.RHTower.Hyperelliptic
variable {F : Type*} [Field F] [Fintype F]
variable (K : Type*) [Field K] [Fintype K] [Algebra F K]


omit [Fintype F] in
/-- The affine solution count with infinity is the quadratic-character count plus one. -/
theorem hyperelliptic_card_points (hF : ringChar F ≠ 2) (f : F[X]) :
    (Nat.card (HyperellipticPoints f K) : ℂ) =
      Fintype.card K + 1 + extHyp (E := K) f := by
  classical
  have hK : ringChar K ≠ 2 := by rwa [← Algebra.ringChar_eq F K]
  have hc := card_points_eq hK (f.map (algebraMap F K))
  simp only [eval_map, ← aeval_def] at hc
  have hc' := congrArg (fun z : ℤ => (z : ℂ)) hc
  push_cast at hc'
  have ha : Nat.card (HyperellipticAffinePoints f K) =
      (univ.filter fun z : K × K => z.2 ^ 2 = aeval z.1 f).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hp : Nat.card (HyperellipticPoints f K) =
      Nat.card (HyperellipticAffinePoints f K) + 1 := by
    simp only [HyperellipticPoints, Nat.card_eq_fintype_card, Fintype.card_option]
  rw [hp, ha, Nat.cast_add, Nat.cast_one, hc']
  unfold extHyp
  ring

/-- Extension counts equal the actual L-polynomial root power sums, including infinity. -/
theorem hyperelliptic_card_points_roots (hF : ringChar F ≠ 2) {f : F[X]}
    (hodd : Odd f.natDegree) :
    (Nat.card (HyperellipticPoints f K) : ℂ) =
      (Fintype.card F : ℂ) ^ Module.finrank F K + 1 -
        ((lRoots f).map (· ^ Module.finrank F K)).sum := by
  rw [hyperelliptic_card_points K hF, extHyp_eq_neg_sum_pow hF hodd K,
    Module.card_eq_pow_finrank (K := F), Nat.cast_pow, sub_eq_add_neg]

variable (E : Type*) [Field E] [Fintype E] [Algebra F E]

/-- Every admissible Frobenius iterate counts points over its actual smaller field. -/
theorem hyperelliptic_frobenius_fixed_count (hF : ringChar F ≠ 2) {f : F[X]}
    (hodd : Odd f.natDegree) (d : ℕ) [NeZero d] (hd : d ∣ Module.finrank F E) :
    (Nat.card {z : HyperellipticPoints f E //
      (hyperellipticFrobenius F E f ^ d) z = z} : ℂ) =
        (Fintype.card F : ℂ) ^ d + 1 - ((lRoots f).map (· ^ d)).sum := by
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  let K := Extension F (ringChar F) d
  letI : Fintype K := Fintype.ofFinite K
  have hk : Module.finrank F K = d := finrank_extension F (ringChar F) d
  obtain ⟨e⟩ := nonempty_algHom_of_finrank_dvd (F := F) (K := K) (L := E) (hk.symm ▸ hd)
  have hc := Nat.card_congr (hyperellipticFrobeniusFixedEquiv F K E f e)
  rw [hk] at hc
  rw [← hc, hyperelliptic_card_points_roots K hF hodd, hk]

/-- The factorial ambient field contains every field required by a tuple's cycle lengths. -/
theorem hyperelliptic_factorial_fixed_count (hF : ringChar F ≠ 2) {f : F[X]}
    (hodd : Odd f.natDegree) (n d : ℕ) [NeZero d] (hd : d ≤ n) :
    letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
    letI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
    let E := Extension F (ringChar F) n.factorial
    (Nat.card {z : HyperellipticPoints f E //
      (hyperellipticFrobenius F E f ^ d) z = z} : ℂ) =
        (Fintype.card F : ℂ) ^ d + 1 - ((lRoots f).map (· ^ d)).sum := by
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  let E := Extension F (ringChar F) n.factorial
  letI : Fintype E := Fintype.ofFinite E
  exact hyperelliptic_frobenius_fixed_count E hF hodd d
    ((finrank_extension F (ringChar F) n.factorial).symm ▸
      Nat.dvd_factorial (NeZero.pos d) hd)

#print axioms hyperelliptic_card_points
#print axioms hyperelliptic_card_points_roots
#print axioms hyperelliptic_frobenius_fixed_count
#print axioms hyperelliptic_factorial_fixed_count
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
