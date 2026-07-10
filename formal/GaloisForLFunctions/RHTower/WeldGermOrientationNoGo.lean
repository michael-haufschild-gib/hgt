import GaloisForLFunctions.RHTower.WeldPolarizationDirection

/-!
# The weld class cannot canonically orient a scalar germ line

`WeldPolarizationDirection` proves that a weld class canonically determines an alternating area
form on the real two-generator plane, but not a complex structure.  After scalar FE/Schwarz germ
gluing was proved gauge-trivial, the last scalar arithmetic escape was to ask this area form for a
canonical nonzero covector and use it to orient the germ line.

That escape is impossible.  The area form is preserved by both unipotent symplectic shears.  A
linear functional invariant under the upper shear vanishes on `(1,0)`; invariance under the lower
shear vanishes on `(0,1)`.  Hence every natural scalar reader is zero.  The proof is uniform in the
conversion rate and is then transported through `weldClassLineToArea` to the actual weld-class
line.  Even a reader family allowed to depend on the full weld class vanishes pointwise.

The underlying invariant-covector fact is standard symplectic algebra.  The branch-specific no-go
is its consequence: neither one prime class nor the entire class-to-area family can reduce the
complex germ-basis gauge to a scalar orientation.  Any surviving arithmetic reduction must retain
extra marked structure not present in the scalar weld class—prime labels together with a lattice,
filtration, or pairing—and must derive that structure from the completed datum rather than insert a
location character or a flow parameter.
-/

open Complex Matrix GaloisForLFunctions

noncomputable section
namespace GaloisForLFunctions.RHTower

/-- The lower unipotent shear of the real weld-generator plane. -/
def weldLowerShear : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.1, z.1 + z.2)
  invFun z := (z.1, z.2 - z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by
    ext
    · rfl
    · dsimp
      ring
  map_smul' a x := by
    ext
    · rfl
    · dsimp
      ring

/-- The lower shear preserves every weld area form. -/
theorem weldLowerShear_preserves_area (θ : ℝ) :
    PreservesBilin (weldAreaForm θ) weldLowerShear.toLinearMap := by
  intro x y
  change θ * (x.1 * (y.1 + y.2) - (x.1 + x.2) * y.1) =
    θ * (x.1 * y.2 - x.2 * y.1)
  ring

/-- **No natural scalar reader of a weld area.**  A linear functional invariant under every
area-preserving change of weld generators is zero.  Only the two unipotent shears are needed. -/
theorem weldNaturalScalarReader_eq_zero (θ : ℝ)
    (reader : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (natural : ∀ P : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ),
      PreservesBilin (weldAreaForm θ) P.toLinearMap →
        reader.comp P.toLinearMap = reader) :
    reader = 0 := by
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  have hUpper := natural weldUpperShear (weldUpperShear_preserves_area θ)
  have hUpperAtE₂ := congrArg (fun L : (ℝ × ℝ) →ₗ[ℝ] ℝ => L e₂) hUpper
  have he₁ : reader e₁ = 0 := by
    have hsum : reader (e₁ + e₂) = reader e₂ := by
      simpa [LinearMap.comp_apply, e₁, e₂, weldUpperShear] using hUpperAtE₂
    rw [map_add] at hsum
    linarith
  have hLower := natural weldLowerShear (weldLowerShear_preserves_area θ)
  have hLowerAtE₁ := congrArg (fun L : (ℝ × ℝ) →ₗ[ℝ] ℝ => L e₁) hLower
  have he₂ : reader e₂ = 0 := by
    have hsum : reader (e₁ + e₂) = reader e₁ := by
      simpa [LinearMap.comp_apply, e₁, e₂, weldLowerShear] using hLowerAtE₁
    rw [map_add] at hsum
    linarith
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hdecomp : (x, y) = x • e₁ + y • e₂ := by
    ext <;> simp [e₁, e₂]
  rw [LinearMap.zero_apply, hdecomp, map_add, map_smul, map_smul, he₁, he₂]
  simp

/-- Class-coordinate-free form of the scalar-reader no-go. -/
theorem weldClassLineNaturalScalarReader_eq_zero (c : WeldClassLine)
    (reader : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (natural : ∀ P : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ),
      PreservesBilin (weldClassLineToArea c) P.toLinearMap →
        reader.comp P.toLinearMap = reader) :
    reader = 0 := by
  let θ : ℝ := weldClassLineEquiv.symm c
  have hc : c = weldClassHom.rangeRestrict θ := by
    change c = weldClassLineEquiv (weldClassLineEquiv.symm c)
    exact (weldClassLineEquiv.apply_symm_apply c).symm
  have harea : weldClassLineToArea c = weldAreaForm θ := by
    rw [hc, weldClassLineToArea_apply]
  apply weldNaturalScalarReader_eq_zero θ reader
  intro P hP
  apply natural P
  rwa [harea]

/-- A proposed scalar reader allowed to depend on the entire weld class, natural under every
automorphism of the corresponding area form. -/
structure WeldClassLineNaturalScalarReaderFamily where
  reader : WeldClassLine → ((ℝ × ℝ) →ₗ[ℝ] ℝ)
  natural : ∀ (c : WeldClassLine) (P : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ)),
    PreservesBilin (weldClassLineToArea c) P.toLinearMap →
      (reader c).comp P.toLinearMap = reader c

/-- **Full class-line exhaustion.**  Every natural family of scalar readers is identically zero.
Thus allowing the reader to depend on the prime conversion rate does not break the shear symmetry. -/
theorem WeldClassLineNaturalScalarReaderFamily.reader_eq_zero
    (R : WeldClassLineNaturalScalarReaderFamily) :
    R.reader = 0 := by
  funext c
  exact weldClassLineNaturalScalarReader_eq_zero c (R.reader c) (R.natural c)

/-- No natural scalar-reader family is nonzero. -/
theorem no_nonzero_weldClassLineNaturalScalarReaderFamily :
    ¬ ∃ R : WeldClassLineNaturalScalarReaderFamily, R.reader ≠ 0 := by
  rintro ⟨R, hR⟩
  exact hR R.reader_eq_zero

end GaloisForLFunctions.RHTower

