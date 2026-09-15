import GaloisForLFunctions.RHTower.MaassModelHilbertCompletion
import GaloisForLFunctions.RHTower.RealSphericalComplementaryGeneratorEnergy

/-!
# Factorial bounds for source-attached Maass model generators

The finite complementary model already completes isometrically into the quotient `L²` Maass
model.  This file transfers the closed raising and lowering energy estimates to that actual
pre-Hilbert norm.  For the diagonal noncompact generator `E + F`, finite `K`-support expands by
one per iterate and its norm grows at most factorially.  The resulting bound is the analytic-vector
input required to turn the existing all-time derivative identities into a closed-range orbit
argument.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Raising on the source-attached complementary pre-Hilbert model. -/
def complementaryRaising (lam : SelbergExceptionalEigenvalue) :
    ComplementaryKFinite lam →ₗ[ℂ] ComplementaryKFinite lam where
  toFun v := sphericalPrincipalE ((2 * lam.complementaryExponent : ℝ) : ℂ) v
  map_add' x y := (sphericalPrincipalE _).map_add x y
  map_smul' c x := (sphericalPrincipalE _).map_smul c x

/-- Lowering on the source-attached complementary pre-Hilbert model. -/
def complementaryLowering (lam : SelbergExceptionalEigenvalue) :
    ComplementaryKFinite lam →ₗ[ℂ] ComplementaryKFinite lam where
  toFun v := sphericalPrincipalF ((2 * lam.complementaryExponent : ℝ) : ℂ) v
  map_add' x y := (sphericalPrincipalF _).map_add x y
  map_smul' c x := (sphericalPrincipalF _).map_smul c x

/-- The source-attached raising map agrees with the algebraic spherical raising map. -/
theorem complementaryRaising_toModel (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) :
    ComplementaryKFinite.toModel lam (complementaryRaising lam v) =
      sphericalPrincipalE ((2 * lam.complementaryExponent : ℝ) : ℂ)
        (ComplementaryKFinite.toModel lam v) := rfl

/-- The source-attached lowering map agrees with the algebraic spherical lowering map. -/
theorem complementaryLowering_toModel (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) :
    ComplementaryKFinite.toModel lam (complementaryLowering lam v) =
      sphericalPrincipalF ((2 * lam.complementaryExponent : ℝ) : ℂ)
        (ComplementaryKFinite.toModel lam v) := rfl

/-- The source-attached pre-Hilbert norm is exactly the complementary Hermitian energy. -/
theorem complementaryKFinite_re_inner (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) :
    ‖v‖ ^ 2 =
      (sphericalComplementaryHermitianForm (2 * lam.complementaryExponent)
        (ComplementaryKFinite.toModel lam v) (ComplementaryKFinite.toModel lam v)).re := by
  have h := @norm_sq_eq_re_inner ℂ (ComplementaryKFinite lam) _ _ _ v
  rw [complementaryKFinite_inner] at h
  exact h

/-- The complementary parameter attached to an exceptional Maass eigenvalue lies in `(-1, 1)`. -/
theorem complementaryParameter_abs (lam : SelbergExceptionalEigenvalue) :
    |2 * lam.complementaryExponent| < 1 := by
  exact abs_lt.mpr ⟨by linarith [lam.complementaryExponent_mem_Ioo.1],
    by linarith [lam.complementaryExponent_mem_Ioo.2]⟩

/-- On `K`-support of radius `r`, raising has norm at most `(r + 1/2)`. -/
theorem complementaryRaising_norm_le_of_support (lam : SelbergExceptionalEigenvalue)
    (r : ℝ) (hr : 0 ≤ r) (v : ComplementaryKFinite lam)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) :
    ‖complementaryRaising lam v‖ ≤ (r + 1 / 2) * ‖v‖ := by
  let s : ℝ := 2 * lam.complementaryExponent
  have hs : |s| < 1 := complementaryParameter_abs lam
  have henergy := sphericalPrincipalE_complementary_energy_re_le_of_support s r hs hr
    (ComplementaryKFinite.toModel lam v) hsupp
  have hleft : ‖complementaryRaising lam v‖ ^ 2 =
      (sphericalComplementaryHermitianForm s
        (sphericalPrincipalE (s : ℂ) (ComplementaryKFinite.toModel lam v))
        (sphericalPrincipalE (s : ℂ) (ComplementaryKFinite.toModel lam v))).re := by
    rw [complementaryKFinite_re_inner, complementaryRaising_toModel]
  have hright : ‖v‖ ^ 2 =
      (sphericalComplementaryHermitianForm s
        (ComplementaryKFinite.toModel lam v) (ComplementaryKFinite.toModel lam v)).re :=
    complementaryKFinite_re_inner lam v
  rw [← hleft, ← hright] at henergy
  have hfactor : (2 * r + 1) ^ 2 / 4 = (r + 1 / 2) ^ 2 := by ring
  rw [hfactor] at henergy
  have hA : 0 ≤ r + 1 / 2 := by linarith
  have hB : 0 ≤ (r + 1 / 2) * ‖v‖ := mul_nonneg hA (norm_nonneg _)
  nlinarith [norm_nonneg (complementaryRaising lam v)]

/-- On `K`-support of radius `r`, lowering has norm at most `(r + 1/2)`. -/
theorem complementaryLowering_norm_le_of_support (lam : SelbergExceptionalEigenvalue)
    (r : ℝ) (hr : 0 ≤ r) (v : ComplementaryKFinite lam)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) :
    ‖complementaryLowering lam v‖ ≤ (r + 1 / 2) * ‖v‖ := by
  let s : ℝ := 2 * lam.complementaryExponent
  have hs : |s| < 1 := complementaryParameter_abs lam
  have henergy := sphericalPrincipalF_complementary_energy_re_le_of_support s r hs hr
    (ComplementaryKFinite.toModel lam v) hsupp
  have hleft : ‖complementaryLowering lam v‖ ^ 2 =
      (sphericalComplementaryHermitianForm s
        (sphericalPrincipalF (s : ℂ) (ComplementaryKFinite.toModel lam v))
        (sphericalPrincipalF (s : ℂ) (ComplementaryKFinite.toModel lam v))).re := by
    rw [complementaryKFinite_re_inner, complementaryLowering_toModel]
  have hright : ‖v‖ ^ 2 =
      (sphericalComplementaryHermitianForm s
        (ComplementaryKFinite.toModel lam v) (ComplementaryKFinite.toModel lam v)).re :=
    complementaryKFinite_re_inner lam v
  rw [← hleft, ← hright] at henergy
  have hfactor : (2 * r + 1) ^ 2 / 4 = (r + 1 / 2) ^ 2 := by ring
  rw [hfactor] at henergy
  have hA : 0 ≤ r + 1 / 2 := by linarith
  have hB : 0 ≤ (r + 1 / 2) * ‖v‖ := mul_nonneg hA (norm_nonneg _)
  nlinarith [norm_nonneg (complementaryLowering lam v)]

/-- The source-attached diagonal noncompact generator. -/
def complementaryDiagonalGenerator (lam : SelbergExceptionalEigenvalue) :
    ComplementaryKFinite lam →ₗ[ℂ] ComplementaryKFinite lam :=
  complementaryRaising lam + complementaryLowering lam

/-- The diagonal generator is the model operator `E + F` in spherical coordinates. -/
theorem complementaryDiagonal_toModel (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) :
    ComplementaryKFinite.toModel lam (complementaryDiagonalGenerator lam v) =
      (sphericalPrincipalE ((2 * lam.complementaryExponent : ℝ) : ℂ) +
        sphericalPrincipalF ((2 * lam.complementaryExponent : ℝ) : ℂ))
        (ComplementaryKFinite.toModel lam v) := rfl

/-- The diagonal generator expands finite `K`-support radius by at most one. -/
theorem complementaryDiagonal_support_radius (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) (r : ℝ)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) :
    ∀ m ∈ (ComplementaryKFinite.toModel lam
      (complementaryDiagonalGenerator lam v)).support, |(m : ℝ)| ≤ r + 1 := by
  intro m hm
  rw [complementaryDiagonal_toModel] at hm
  have hnonzero :
      ((sphericalPrincipalE ((2 * lam.complementaryExponent : ℝ) : ℂ) +
        sphericalPrincipalF ((2 * lam.complementaryExponent : ℝ) : ℂ))
        (ComplementaryKFinite.toModel lam v)) m ≠ 0 := Finsupp.mem_support_iff.mp hm
  simp only [LinearMap.add_apply, Finsupp.add_apply] at hnonzero
  by_cases hE : sphericalPrincipalE ((2 * lam.complementaryExponent : ℝ) : ℂ)
      (ComplementaryKFinite.toModel lam v) m = 0
  · have hF : sphericalPrincipalF ((2 * lam.complementaryExponent : ℝ) : ℂ)
        (ComplementaryKFinite.toModel lam v) m ≠ 0 := by
      intro hz
      exact hnonzero (by rw [hE, hz, add_zero])
    exact sphericalPrincipalF_support_radius _ _ r hsupp m (Finsupp.mem_support_iff.mpr hF)
  · exact sphericalPrincipalE_support_radius _ _ r hsupp m (Finsupp.mem_support_iff.mpr hE)

/-- On `K`-support of radius `r`, the diagonal generator has norm at most `2r + 1`. -/
theorem complementaryDiagonal_norm_le_of_support (lam : SelbergExceptionalEigenvalue)
    (r : ℝ) (hr : 0 ≤ r) (v : ComplementaryKFinite lam)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) :
    ‖complementaryDiagonalGenerator lam v‖ ≤ (2 * r + 1) * ‖v‖ := by
  rw [complementaryDiagonalGenerator, LinearMap.add_apply]
  calc
    ‖complementaryRaising lam v + complementaryLowering lam v‖ ≤
        ‖complementaryRaising lam v‖ + ‖complementaryLowering lam v‖ := norm_add_le _ _
    _ ≤ (r + 1 / 2) * ‖v‖ + (r + 1 / 2) * ‖v‖ :=
      add_le_add (complementaryRaising_norm_le_of_support lam r hr v hsupp)
        (complementaryLowering_norm_le_of_support lam r hr v hsupp)
    _ = (2 * r + 1) * ‖v‖ := by ring

/-- The `n`-fold diagonal-generator iterate on the finite source-attached model. -/
def complementaryDiagonalIterate (lam : SelbergExceptionalEigenvalue) : ℕ →
    ComplementaryKFinite lam →ₗ[ℂ] ComplementaryKFinite lam
  | 0 => LinearMap.id
  | n + 1 => (complementaryDiagonalGenerator lam).comp (complementaryDiagonalIterate lam n)

/-- Product of successive support-radius bounds for diagonal-generator iterates. -/
def complementaryDiagonalIterationWeight (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (2 * (r + n) + 1) * complementaryDiagonalIterationWeight r n

/-- The `n`-fold diagonal generator has `K`-support radius at most `r + n`. -/
theorem complementaryDiagonalIterate_support_radius (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) (r : ℝ)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) :
    ∀ n : ℕ, ∀ m ∈ (ComplementaryKFinite.toModel lam
      (complementaryDiagonalIterate lam n v)).support, |(m : ℝ)| ≤ r + n := by
  intro n
  induction n with
  | zero =>
      simpa [complementaryDiagonalIterate] using hsupp
  | succ n ih =>
      simpa [complementaryDiagonalIterate, LinearMap.comp_apply, add_assoc] using
        complementaryDiagonal_support_radius lam (complementaryDiagonalIterate lam n v)
          (r + n) (ih)

/-- The diagonal iteration weight is nonnegative for a nonnegative initial radius. -/
theorem complementaryDiagonalIterationWeight_nonneg (r : ℝ) (hr : 0 ≤ r) :
    ∀ n, 0 ≤ complementaryDiagonalIterationWeight r n := by
  intro n
  induction n with
  | zero => simp [complementaryDiagonalIterationWeight]
  | succ n ih =>
      rw [complementaryDiagonalIterationWeight]
      exact mul_nonneg (by positivity) ih

/-- Exact product norm bound for a finite diagonal-generator iterate. -/
theorem complementaryDiagonalIterate_norm_le_weight (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) :
    ∀ n : ℕ, ‖complementaryDiagonalIterate lam n v‖ ≤
      complementaryDiagonalIterationWeight r n * ‖v‖ := by
  intro n
  induction n with
  | zero => simp [complementaryDiagonalIterate, complementaryDiagonalIterationWeight]
  | succ n ih =>
      have hrn : 0 ≤ r + n := by positivity
      have hsuppn := complementaryDiagonalIterate_support_radius lam v r hsupp n
      have hstep := complementaryDiagonal_norm_le_of_support lam (r + n) hrn
        (complementaryDiagonalIterate lam n v) hsuppn
      have hfactor : 0 ≤ 2 * (r + n) + 1 := by positivity
      calc
        ‖complementaryDiagonalIterate lam (n + 1) v‖ =
            ‖complementaryDiagonalGenerator lam (complementaryDiagonalIterate lam n v)‖ := by
              rfl
        _ ≤ (2 * (r + n) + 1) * ‖complementaryDiagonalIterate lam n v‖ := hstep
        _ ≤ (2 * (r + n) + 1) *
            (complementaryDiagonalIterationWeight r n * ‖v‖) :=
              mul_le_mul_of_nonneg_left ih hfactor
        _ = complementaryDiagonalIterationWeight r (n + 1) * ‖v‖ := by
              rw [complementaryDiagonalIterationWeight]
              ring

/-- The product of diagonal-generator radius factors has a factorial majorant. -/
theorem complementaryDiagonalIterationWeight_le_factorial (r : ℝ) (hr : 0 ≤ r) :
    ∀ n : ℕ, complementaryDiagonalIterationWeight r n ≤
      (2 * r + 2) ^ n * n.factorial := by
  intro n
  induction n with
  | zero => simp [complementaryDiagonalIterationWeight]
  | succ n ih =>
      have hC : 0 ≤ 2 * r + 2 := by linarith
      have hfactor : 0 ≤ 2 * (r + n) + 1 := by positivity
      have hbound : 2 * (r + n) + 1 ≤ (2 * r + 2) * (n + 1) := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [mul_nonneg hr hn]
      have htail : 0 ≤ (2 * r + 2) ^ n * n.factorial := by positivity
      calc
        complementaryDiagonalIterationWeight r (n + 1) =
            (2 * (r + n) + 1) * complementaryDiagonalIterationWeight r n := rfl
        _ ≤ (2 * (r + n) + 1) * ((2 * r + 2) ^ n * n.factorial) :=
            mul_le_mul_of_nonneg_left ih hfactor
        _ ≤ ((2 * r + 2) * (n + 1)) * ((2 * r + 2) ^ n * n.factorial) :=
            mul_le_mul_of_nonneg_right hbound htail
        _ = (2 * r + 2) ^ (n + 1) * (n + 1).factorial := by
            rw [Nat.factorial_succ, pow_succ]
            push_cast
            ring

/-- Factorial analytic-vector majorant for the diagonal Maass generator. -/
theorem complementaryDiagonalIterate_norm_le_factorial (lam : SelbergExceptionalEigenvalue)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r) (n : ℕ) :
    ‖complementaryDiagonalIterate lam n v‖ ≤
      (2 * r + 2) ^ n * n.factorial * ‖v‖ := by
  calc
    ‖complementaryDiagonalIterate lam n v‖ ≤
        complementaryDiagonalIterationWeight r n * ‖v‖ :=
          complementaryDiagonalIterate_norm_le_weight lam v r hr hsupp n
    _ ≤ ((2 * r + 2) ^ n * n.factorial) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (complementaryDiagonalIterationWeight_le_factorial r hr n) (norm_nonneg _)
    _ = (2 * r + 2) ^ n * n.factorial * ‖v‖ := by ring

end

end GaloisForLFunctions.RHTower
