import GaloisForLFunctions.HTGeometry.AbeExponentialDampingMultiplier
import GaloisForLFunctions.HTGeometry.AbePhi2TranslationGrowth

/-!
# A concrete entire `Φ₂` damping profile

The exact period-coordinate character used by Abe is an entire source on `ℂᵈ`. Its literal
exponential damping multiplier is the multiplier already formalized for arbitrary entire profiles.
Together with real period-coordinate shifts, this proves that multiplication by every fixed-time
damping multiplier preserves the full (entire plus translation-growth) `Φ₂` condition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Abe's coordinate character as a concrete entire source on a selected coordinate of `ℂᵈ`. -/
def abeRealCoordinateProfile (d : ℕ) (k : Fin d) : MultivariateEntire d :=
  multivariateEntireCexp
    ((2 * (Real.pi : ℂ) * Complex.I) •
      mvPolynomialMultivariateEntire (MvPolynomial.X k))

/-- Evaluation of the entire coordinate profile is Abe's scalar character `exp (2π i z)`. -/
theorem abeRealCoordinateProfile_apply {d : ℕ} (k : Fin d) (x : Fin d → ℂ) :
    (abeRealCoordinateProfile d k).1 x = abeRealCoordinateCharacter (x k) := by
  rw [abeRealCoordinateProfile, multivariateEntireCexp_apply]
  change Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
    MvPolynomial.eval x (MvPolynomial.X k)) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x k)
  rw [MvPolynomial.eval_X]

/-- A directional derivative of Abe's coordinate character is its coordinate scalar times the
same character. -/
theorem partialDerivEntire_abeRealCoordinateProfile {d : ℕ} (k : Fin d)
    (v : Fin d → ℂ) :
    partialDerivEntire v (abeRealCoordinateProfile d k) =
      ((2 * (Real.pi : ℂ) * Complex.I * v k) • abeRealCoordinateProfile d k) := by
  ext x
  change fderiv ℂ ((abeRealCoordinateProfile d k).1) x v =
    (2 * (Real.pi : ℂ) * Complex.I * v k) * (abeRealCoordinateProfile d k).1 x
  have hprofile : (abeRealCoordinateProfile d k).1 =
      fun y : Fin d → ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * y k) := by
    funext y
    exact abeRealCoordinateProfile_apply k y
  rw [hprofile]
  have hlin0 := (hasFDerivAt_apply (𝕜 := ℂ) k x).const_smul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hlin : HasFDerivAt (fun y : Fin d → ℂ =>
      (2 * (Real.pi : ℂ) * Complex.I) * y k)
      ((2 * (Real.pi : ℂ) * Complex.I) •
        (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ)) x := by
    convert hlin0 using 1 <;> rfl
  have h := (Complex.hasDerivAt_exp
    ((2 * (Real.pi : ℂ) * Complex.I) * x k)).comp_hasFDerivAt x hlin
  have hderiv := congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L v) h.fderiv
  calc
    fderiv ℂ (fun y : Fin d → ℂ =>
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * y k)) x v =
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x k) *
          ((2 * (Real.pi : ℂ) * Complex.I) * v k) := by
      simpa [Function.comp_def, smul_apply, smul_eq_mul] using hderiv
    _ = (2 * (Real.pi : ℂ) * Complex.I * v k) *
          Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x k) := by ring

/-- Translating Abe's coordinate character only multiplies it by the corresponding constant
character value. -/
theorem multivariateEntireTranslate_abeRealCoordinateProfile {d : ℕ} (k : Fin d)
    (γ : Fin d → ℂ) :
    multivariateEntireTranslate (abeRealCoordinateProfile d k) γ =
      abeRealCoordinateCharacter (γ k) • abeRealCoordinateProfile d k := by
  ext x
  rw [multivariateEntireTranslate_apply, abeRealCoordinateProfile_apply]
  change abeRealCoordinateCharacter ((x + γ) k) =
    abeRealCoordinateCharacter (γ k) * (abeRealCoordinateProfile d k).1 x
  rw [abeRealCoordinateProfile_apply]
  simp only [show (x + γ) k = γ k + x k by simp [add_comm], abeRealCoordinateCharacter]
  rw [show (2 * (Real.pi : ℂ) * Complex.I) * (γ k + x k) =
    (2 * (Real.pi : ℂ) * Complex.I) * γ k +
      (2 * (Real.pi : ℂ) * Complex.I) * x k by ring, Complex.exp_add]

/-- Periodizing a source times Abe's coordinate character is exactly multiplication of its
Poincare summand by the translated character. -/
theorem poincareTermEntire_mul_abeRealCoordinateProfile {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d) (k : Fin d) (γ : Γ) :
    poincareTermEntire ψ (seed * abeRealCoordinateProfile d k) γ =
      abeRealCoordinateCharacter (γ.1 k) •
        (abeRealCoordinateProfile d k * poincareTermEntire ψ seed γ) := by
  ext x
  change ((ψ.factor γ).1 x)⁻¹ * (seed * abeRealCoordinateProfile d k).1 (x + γ.1) =
    abeRealCoordinateCharacter (γ.1 k) *
      ((abeRealCoordinateProfile d k).1 x *
        (((ψ.factor γ).1 x)⁻¹ * seed.1 (x + γ.1)))
  rw [multivariateEntire_mul_apply, abeRealCoordinateProfile_apply]
  rw [abeRealCoordinateProfile_apply k x]
  rw [show (x + γ.1) k = γ.1 k + x k by simp [add_comm]]
  unfold abeRealCoordinateCharacter
  rw [show (2 * (Real.pi : ℂ) * Complex.I) * (γ.1 k + x k) =
    (2 * (Real.pi : ℂ) * Complex.I) * γ.1 k +
      (2 * (Real.pi : ℂ) * Complex.I) * x k by ring, Complex.exp_add]
  ring

/-- The preceding translated-character identity holds for every finite coordinate-character
power. -/
theorem poincareTermEntire_mul_abeRealCoordinateProfile_pow {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d) (k : Fin d) (γ : Γ) (n : ℕ) :
    poincareTermEntire ψ (seed * abeRealCoordinateProfile d k ^ n) γ =
      abeRealCoordinateCharacter (γ.1 k) ^ n •
        (abeRealCoordinateProfile d k ^ n * poincareTermEntire ψ seed γ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      rw [poincareTermEntire_mul_abeRealCoordinateProfile]
      rw [ih, pow_succ]
      ext x
      simp [smul_eq_mul, multivariateEntire_mul_apply]
      ring

/-- The general entire multiplier is exactly the literal real-coordinate damping multiplier for
the concrete coordinate profile. -/
theorem abeExponentialDampingMultiplier_abeRealCoordinateProfile_apply {d : ℕ}
    (k : Fin d) (t : ℂ) (x : Fin d → ℂ) :
    (abeExponentialDampingMultiplier t (abeRealCoordinateProfile d k)).1 x =
      abeRealCoordinateDamping t (x k) 1 := by
  rw [abeExponentialDampingMultiplier_apply, abeRealCoordinateProfile_apply]
  rfl

/-- Abe's full `Φ₂` predicate: an entire source satisfying his Section-7 translation-growth
clause. -/
def IsAbePhi2 {d : ℕ} (Γ : AddSubgroup (Fin d → ℂ))
    (f : MultivariateEntire d) : Prop :=
  AbePhi2TranslationGrowth Γ f.1

/-- The concrete entire Abe multiplier is lattice-uniformly bounded whenever its selected
period-coordinate shifts are real. -/
theorem abeExponentialDampingMultiplier_abeRealCoordinateProfile_latticeUniformlyBounded
    {d : ℕ} (k : Fin d) (t : ℂ) (Γ : AddSubgroup (Fin d → ℂ))
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) :
    AbeLatticeUniformlyBounded Γ
      (fun x => (abeExponentialDampingMultiplier t (abeRealCoordinateProfile d k)).1 x) := by
  convert abeRealCoordinateDampingOn_latticeUniformlyBounded k t 1 Γ hreal using 1
  ext x
  exact abeExponentialDampingMultiplier_abeRealCoordinateProfile_apply k t x

/-- In Abe's real period coordinate, multiplying any `Φ₂` source by a fixed-time literal damping
multiplier remains a `Φ₂` source. -/
theorem IsAbePhi2.mul_abeExponentialDampingMultiplier_abeRealCoordinateProfile
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)} (f : MultivariateEntire d)
    (hf : IsAbePhi2 Γ f) (k : Fin d) (t : ℂ)
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) :
    IsAbePhi2 Γ (f * abeExponentialDampingMultiplier t (abeRealCoordinateProfile d k)) := by
  unfold IsAbePhi2 at hf ⊢
  change AbePhi2TranslationGrowth Γ (fun x =>
    f.1 x * (abeExponentialDampingMultiplier t (abeRealCoordinateProfile d k)).1 x)
  exact hf.mul_of_latticeUniformlyBounded
    (abeExponentialDampingMultiplier_abeRealCoordinateProfile_latticeUniformlyBounded
      k t Γ hreal)

/-- The coordinate character itself is uniformly bounded on every compact set of translates
when its lattice shifts are real. -/
theorem abeRealCoordinateProfile_latticeUniformlyBounded {d : ℕ}
    (k : Fin d) (Γ : AddSubgroup (Fin d → ℂ))
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) :
    AbeLatticeUniformlyBounded Γ (fun x => (abeRealCoordinateProfile d k).1 x) := by
  intro K hK
  have hcontinuous : Continuous (fun x : Fin d → ℂ =>
      abeRealCoordinateCharacter (x k)) := by
    unfold abeRealCoordinateCharacter
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Fin d → ℂ => ‖abeRealCoordinateCharacter (x k)‖)
    hcontinuous.norm.continuousOn
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro x hx γ
  obtain ⟨r, hr⟩ := hreal γ
  change ‖(abeRealCoordinateProfile d k).1 (x + γ.1)‖ ≤ |C|
  rw [abeRealCoordinateProfile_apply, show (x + γ.1) k = x k + (r : ℂ) by simp [hr],
    norm_abeRealCoordinateCharacter_translate]
  exact (show ‖abeRealCoordinateCharacter (x k)‖ ≤ C by simpa using hC x hx).trans
    (le_abs_self C)

/-- Multiplication by a finite power of Abe's real-coordinate character preserves the full
`Φ₂` source class. -/
theorem IsAbePhi2.mul_abeRealCoordinateProfile_pow {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (f : MultivariateEntire d)
    (hf : IsAbePhi2 Γ f) (k : Fin d)
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) (n : ℕ) :
    IsAbePhi2 Γ (f * abeRealCoordinateProfile d k ^ n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      unfold IsAbePhi2 at ih
      have hbounded := abeRealCoordinateProfile_latticeUniformlyBounded k Γ hreal
      have hnext : AbePhi2TranslationGrowth Γ (fun x =>
          (f * abeRealCoordinateProfile d k ^ n).1 x *
            (abeRealCoordinateProfile d k).1 x) :=
        ih.mul_of_latticeUniformlyBounded hbounded
      unfold IsAbePhi2
      rw [pow_succ]
      convert hnext using 1
      ext x
      simp only [multivariateEntire_mul_apply]
      ring

end

end GaloisForLFunctions.HTGeometry
