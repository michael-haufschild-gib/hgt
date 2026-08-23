import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

/-!
# Exact sequence of finite torsion local invariants

Multiplication by every positive integer `n` is surjective on `ℚ/ℤ`, with kernel exactly
`ℚ/ℤ[n]`.  Thus each finite invariant group identified with that torsion layer supplies a canonical
short exact sequence `0 → H_n → ℚ/ℤ --n→ ℚ/ℤ → 0`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Multiplication by `n` on `ℚ/ℤ`. -/
def ratModIntNsmulAddHom (n : ℕ) : RatModInt →+ RatModInt :=
  nsmulAddMonoidHom n

@[simp] theorem ratModIntNsmulAddHom_apply (n : ℕ) (x : RatModInt) :
    ratModIntNsmulAddHom n x = n • x := rfl

/-- Kernel of multiplication by `n` is exactly the `n`-torsion local-invariant layer. -/
theorem ratModIntNsmulAddHom_ker (n : ℕ) :
    (ratModIntNsmulAddHom n).ker = ratModIntNTorsion n := by
  ext x
  rfl

/-- Inclusion of `n`-torsion followed by multiplication by `n` is exact. -/
theorem ratModIntNTorsion_nsmul_exact (n : ℕ) :
    Function.Exact (ratModIntNTorsion n).subtype (ratModIntNsmulAddHom n) := by
  intro x
  constructor
  · intro hx
    change n • x = 0 at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- Multiplication by every positive integer is onto on `ℚ/ℤ`. -/
theorem ratModIntNsmulAddHom_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (ratModIntNsmulAddHom n) := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨QuotientAddGroup.mk (q / (n : ℚ)), ?_⟩
  change n • (QuotientAddGroup.mk (q / (n : ℚ)) : RatModInt) =
    QuotientAddGroup.mk q
  rw [← QuotientAddGroup.mk_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  exact mul_div_cancel₀ q hnq

/-- Canonical finite-torsion short exact sequence
`0 → ℚ/ℤ[n] → ℚ/ℤ --n→ ℚ/ℤ → 0`. -/
theorem ratModIntNTorsion_shortExact (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (ratModIntNTorsion n).subtype ∧
      Function.Exact (ratModIntNTorsion n).subtype (ratModIntNsmulAddHom n) ∧
      Function.Surjective (ratModIntNsmulAddHom n) :=
  ⟨AddSubgroup.subtype_injective _, ratModIntNTorsion_nsmul_exact n,
    ratModIntNsmulAddHom_surjective n hn⟩

/-- Dividing `ℚ/ℤ` by its finite `n`-torsion layer recovers `ℚ/ℤ`. -/
noncomputable def ratModIntQuotientNTorsionEquiv (n : ℕ) (hn : n ≠ 0) :
    RatModInt ⧸ ratModIntNTorsion n ≃+ RatModInt :=
  (QuotientAddGroup.quotientAddEquivOfEq (ratModIntNsmulAddHom_ker n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (ratModIntNsmulAddHom n) (ratModIntNsmulAddHom_surjective n hn))

/-- The quotient equivalence is induced by multiplication by `n`. -/
@[simp] theorem ratModIntQuotientNTorsionEquiv_mk
    (n : ℕ) (hn : n ≠ 0) (x : RatModInt) :
    ratModIntQuotientNTorsionEquiv n hn (QuotientAddGroup.mk x) = n • x := by
  rfl

/-- Embed any finite invariant group identified with `ℚ/ℤ[n]` into the full local-invariant
target. -/
def finiteTorsionInvariantToRatModInt
    {G : Type*} [AddGroup G] {n : ℕ}
    (e : G ≃+ ratModIntNTorsion n) : G →+ RatModInt :=
  (ratModIntNTorsion n).subtype.comp e.toAddMonoidHom

/-- Every finite torsion invariant supplies the left term of the canonical `ℚ/ℤ` exact sequence. -/
theorem finiteTorsionInvariantToRatModInt_exact
    {G : Type*} [AddGroup G] {n : ℕ}
    (e : G ≃+ ratModIntNTorsion n) :
    Function.Exact (finiteTorsionInvariantToRatModInt e) (ratModIntNsmulAddHom n) := by
  intro x
  constructor
  · intro hx
    change n • x = 0 at hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    simp [finiteTorsionInvariantToRatModInt]
  · rintro ⟨y, rfl⟩
    exact (e y).property

/-- Full finite-invariant short exact sequence with middle and right term `ℚ/ℤ`. -/
theorem finiteTorsionInvariantToRatModInt_shortExact
    {G : Type*} [AddGroup G] {n : ℕ} (hn : n ≠ 0)
    (e : G ≃+ ratModIntNTorsion n) :
    Function.Injective (finiteTorsionInvariantToRatModInt e) ∧
      Function.Exact (finiteTorsionInvariantToRatModInt e) (ratModIntNsmulAddHom n) ∧
      Function.Surjective (ratModIntNsmulAddHom n) := by
  refine ⟨?_, finiteTorsionInvariantToRatModInt_exact e,
    ratModIntNsmulAddHom_surjective n hn⟩
  intro x y hxy
  apply e.injective
  exact Subtype.ext hxy

end


end GaloisForLFunctions.HTGeometry.ABHN
