import GaloisForLFunctions.GaloisTheoryOfZeros.TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit

/-!
# The fibre fields over the prime traces are finite Galois and generate the spectral field

`E` is the field of the prime values `p^ρ` of the zeros, `B` the prime trace field,
`G = Gal(E/B)`. For a height `t` let `Z_t` be the finite set of zeros with `|Im ρ| = |t|` and
`E_t = B(p^ρ : p prime, ρ ∈ Z_t)`, the compositum of the residue fields of the zeros in `Z_t`.

* **Finite layers** (`primeFibreField_finiteDimensional`, `primeFibreField_isGalois`). `E_t/B` is
  finite and Galois.
* **Group** (`mem_fixingSubgroup_primeFibreField_iff`, `finrank_primeFibreField`). `Gal(E/E_t)` is
  the pointwise stabilizer of `Z_t`, so `[E_t : B]` is the order of the group of permutations of
  `Z_t` induced by `G`.
* **Parity** (`even_finrank_primeFibreField`). `[E_t : B]` is even at every occupied height.
* **Compositum** (`iSup_primeFibreField`). `E` is the compositum of the `E_t`.

So `E/B` is the union of the finite Galois layers `E_t`, one for each height, each acted on
through the permutations of the zeros of that height.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-! ## The zeros of one height -/

/-- The zeros with `|Im ρ| = |t|`. -/
abbrev PrimeFibreZero (t : ℝ) := {ρ : XiDivisorSupport // |(ρ : ℂ).im| = |t|}

theorem xiSpectralPoint_re_eq_im (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  change (((q.1 : ℂ) - 1 / 2) * (-I)).re = _
  simp [Complex.mul_re]

/-- The copies of ordinate `±t` cover the zeros of height `t`, which are therefore finite. -/
instance primeFibreZero_finite (t : ℝ) : Finite (PrimeFibreZero t) := by
  refine Finite.of_surjective (fun i : PrimeTraceCopies t => (⟨(primeTraceCopy t i).1, ?_⟩ :
    PrimeFibreZero t)) ?_
  · rcases primeTraceCopy_height t i with h | h <;>
      rw [← xiSpectralPoint_re_eq_im, h]
    exact abs_neg t
  · rintro ⟨ρ, hρ⟩
    rcases abs_eq_abs.1 hρ with h | h
    · refine ⟨.inl ⟨primeTraceSupportCopy ρ, (mem_ordinateFibreCopies t _).2 ?_⟩, rfl⟩
      rw [xiSpectralPoint_re_eq_im]
      exact h
    · refine ⟨.inr ⟨primeTraceSupportCopy ρ, (mem_ordinateFibreCopies (-t) _).2 ?_⟩, rfl⟩
      rw [xiSpectralPoint_re_eq_im]
      exact h

/-- The arithmetic group keeps the zeros of each height. -/
def primeFibreZeroMap (σ : G) {t : ℝ} (ρ : PrimeFibreZero t) : PrimeFibreZero t :=
  ⟨primeTraceZeroMap σ ρ.1, (primeTraceZeroMap_height σ ρ.1).trans ρ.2⟩

/-! ## The fibre field -/

/-- The fibre field `E_t`: the compositum of the residue fields of the zeros of height `t`. -/
def primeFibreField (t : ℝ) : IntermediateField B E :=
  ⨆ ρ : PrimeFibreZero t, primeResidueField ρ.1

instance primeFibreField_finiteDimensional (t : ℝ) : FiniteDimensional B (primeFibreField t) :=
  IntermediateField.finiteDimensional_iSup_of_finite

theorem primeResidueField_le_primeFibreField {t : ℝ} (ρ : PrimeFibreZero t) :
    primeResidueField ρ.1 ≤ primeFibreField t :=
  le_iSup (fun ρ : PrimeFibreZero t => primeResidueField ρ.1) ρ

/-- `Gal(E/E_t)` is the pointwise stabilizer of the zeros of height `t`. -/
theorem mem_fixingSubgroup_primeFibreField_iff (t : ℝ) (σ : G) :
    σ ∈ (primeFibreField t).fixingSubgroup ↔
      ∀ ρ : PrimeFibreZero t, primeTraceZeroMap σ ρ.1 = ρ.1 := by
  constructor
  · intro h ρ
    exact (primeResidueField_fixing σ ρ.1).1
      (IntermediateField.fixingSubgroup_antitone (primeResidueField_le_primeFibreField ρ) h)
  · intro h
    have hle : primeFibreField t ≤ IntermediateField.fixedField (Subgroup.zpowers σ) :=
      iSup_le fun ρ => (IntermediateField.le_iff_le _ _).2
        ((Subgroup.zpowers_le).2 ((primeResidueField_fixing σ ρ.1).2 (h ρ)))
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)

/-- The pointwise stabilizer of a height is normal: the group keeps every height. -/
theorem primeFibreField_fixingSubgroup_normal (t : ℝ) :
    (primeFibreField t).fixingSubgroup.Normal := by
  refine ⟨fun σ hσ τ => (mem_fixingSubgroup_primeFibreField_iff t _).2 fun ρ => ?_⟩
  have h := (mem_fixingSubgroup_primeFibreField_iff t σ).1 hσ (primeFibreZeroMap τ⁻¹ ρ)
  change primeTraceZeroMap σ (primeTraceZeroMap τ⁻¹ ρ.1) = primeTraceZeroMap τ⁻¹ ρ.1 at h
  rw [primeTraceZeroMap_mul, primeTraceZeroMap_mul, h, ← primeTraceZeroMap_mul, mul_inv_cancel,
    primeTraceZeroMap_one]

/-- **Finite layers.** `E_t/B` is Galois. -/
instance primeFibreField_isGalois (t : ℝ) : IsGalois B (primeFibreField t) :=
  (InfiniteGalois.normal_iff_isGalois _).1 (primeFibreField_fixingSubgroup_normal t)

/-- **Group.** `[E_t : B]` is the index of the pointwise stabilizer of the zeros of height `t`. -/
theorem finrank_primeFibreField (t : ℝ) :
    Module.finrank B (primeFibreField t) = (primeFibreField t).fixingSubgroup.index :=
  IntermediateField.finrank_eq_fixingSubgroup_index _

/-- **Parity.** At an occupied height the degree of a residue field divides `[E_t : B]`, which
is therefore even. -/
theorem even_finrank_primeFibreField {t : ℝ} (ρ : PrimeFibreZero t) :
    Even (Module.finrank B (primeFibreField t)) :=
  even_iff_two_dvd.2 ((even_iff_two_dvd.1 (even_finrank_primeResidueField ρ.1)).trans
    (IntermediateField.finrank_dvd_of_le_right (primeResidueField_le_primeFibreField ρ)))

/-- **Compositum.** `E` is generated by the fibre fields. -/
theorem iSup_primeFibreField : (⨆ t : ℝ, primeFibreField t) = ⊤ := by
  refine top_unique ?_
  rw [← primeTraceExtension_two_prime_families ⟨2, Nat.prime_two⟩ ⟨3, Nat.prime_three⟩
    (by decide)]
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (⟨ρ, rfl⟩ | ⟨ρ, rfl⟩) <;>
    exact le_iSup (fun t : ℝ => primeFibreField t) (ρ : ℂ).im
      (primeResidueField_le_primeFibreField (⟨ρ, rfl⟩ : PrimeFibreZero (ρ : ℂ).im)
        (primeResidueValue_mem _ ρ))

end GaloisForLFunctions.GaloisTheoryOfZeros
