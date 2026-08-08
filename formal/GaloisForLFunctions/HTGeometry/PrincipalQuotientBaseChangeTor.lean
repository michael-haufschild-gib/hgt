import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Base-change Tor for a principal quotient

Let `A` be a commutative domain and `0 ≠ f : A`.  The sequence

```text
0 → A --f→ A → A/(f) → 0
```

is a free resolution.  After base change to an `A`-algebra `B`, its differential is
multiplication by the image of `f`.  This file packages the homology of that actual free
resolution, including degree zero, rather than using a merely analogous two-term complex.

When `f` vanishes in `B`, the base-changed complex is `0 → B --0→ B → 0`; hence its derived
tensor groups are `B` in degrees zero and one and zero in every higher degree.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]

/-- Multiplication by the defining element in the length-one principal free resolution. -/
def principalResolutionDifferential (f : A) : A →ₗ[A] A :=
  LinearMap.mulLeft A f

/-- The augmentation of the principal free resolution. -/
def principalResolutionAugmentation (f : A) :
    A →ₗ[A] A ⧸ Ideal.span ({f} : Set A) :=
  (Ideal.Quotient.mkₐ A (Ideal.span ({f} : Set A))).toLinearMap

/-- Multiplication by a nonzero element of a domain is injective. -/
theorem principalResolutionDifferential_injective (f : A) (hf : f ≠ 0) :
    Function.Injective (principalResolutionDifferential f) := by
  intro x y hxy
  apply mul_left_cancel₀ hf
  simpa only [principalResolutionDifferential, LinearMap.mulLeft_apply] using hxy

omit [IsDomain A] in
/-- Exactness at the middle free module of the principal resolution. -/
theorem range_principalResolutionDifferential_eq_ker_augmentation (f : A) :
    LinearMap.range (principalResolutionDifferential f) =
      LinearMap.ker (principalResolutionAugmentation f) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨b, by
      simp only [principalResolutionDifferential, LinearMap.mulLeft_apply]⟩
  · intro ha
    rw [LinearMap.mem_ker] at ha
    have hmem : a ∈ Ideal.span ({f} : Set A) :=
      Ideal.Quotient.eq_zero_iff_mem.mp ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
    refine ⟨b, ?_⟩
    simpa only [principalResolutionDifferential, LinearMap.mulLeft_apply] using hb.symm

omit [IsDomain A] in
/-- The augmentation onto the principal quotient is surjective. -/
theorem principalResolutionAugmentation_surjective (f : A) :
    Function.Surjective (principalResolutionAugmentation f) :=
  Ideal.Quotient.mk_surjective

/-- **The principal quotient has a length-one free resolution.**  This records injectivity,
middle exactness, and surjectivity of the actual resolution maps. -/
theorem principalQuotient_freeResolution_exact (f : A) (hf : f ≠ 0) :
    Function.Injective (principalResolutionDifferential f) ∧
      LinearMap.range (principalResolutionDifferential f) =
        LinearMap.ker (principalResolutionAugmentation f) ∧
      Function.Surjective (principalResolutionAugmentation f) :=
  ⟨principalResolutionDifferential_injective f hf,
    range_principalResolutionDifferential_eq_ker_augmentation f,
    principalResolutionAugmentation_surjective f⟩

/-- Differential of the principal free resolution after base change to `B`. -/
def principalBaseChangeDifferential (f : A) : B →ₗ[B] B :=
  LinearMap.mulLeft B (algebraMap A B f)

/-- Degree-zero homology (cokernel) of the base-changed principal free resolution. -/
abbrev principalBaseChangeTorZero (f : A) : Type _ :=
  B ⧸ Ideal.span ({algebraMap A B f} : Set B)

/-- Degree-one homology (kernel) of the base-changed principal free resolution. -/
abbrev principalBaseChangeTorOne (f : A) : Type _ :=
  LinearMap.ker (principalBaseChangeDifferential (B := B) f)

/-- All-degree homology of the base-changed length-one free resolution.  Degrees above one are the
zero module because the resolution itself has no terms there. -/
abbrev principalBaseChangeTor (f : A) : ℕ → Type _
  | 0 => principalBaseChangeTorZero (B := B) f
  | 1 => principalBaseChangeTorOne (B := B) f
  | _ + 2 => PUnit

omit [IsDomain A] in
/-- If the relation vanishes after base change, the base-changed differential is zero. -/
theorem principalBaseChangeDifferential_eq_zero (f : A) (hf : algebraMap A B f = 0) :
    principalBaseChangeDifferential (B := B) f = 0 := by
  apply LinearMap.ext
  intro b
  simp [principalBaseChangeDifferential, hf]

/-- If the relation vanishes after base change, degree-zero Tor is canonically the face algebra. -/
noncomputable def principalBaseChangeTorZeroEquiv (f : A) (hf : algebraMap A B f = 0) :
    principalBaseChangeTorZero (B := B) f ≃ₗ[B] B :=
  ((Ideal.quotientEquivAlgOfEq B
      (Ideal.span_singleton_eq_bot.mpr hf)).trans
    (AlgEquiv.quotientBot B B)).toLinearEquiv

/-- If the relation vanishes after base change, degree-one Tor is canonically the face algebra. -/
noncomputable def principalBaseChangeTorOneEquiv (f : A) (hf : algebraMap A B f = 0) :
    principalBaseChangeTorOne (B := B) f ≃ₗ[B] B :=
  LinearEquiv.ofTop _ <| by
    rw [LinearMap.ker_eq_top]
    exact principalBaseChangeDifferential_eq_zero f hf

/-- The degree-zero all-degree package is the face algebra when the relation vanishes. -/
noncomputable def principalBaseChangeTor_zero_equiv (f : A) (hf : algebraMap A B f = 0) :
    principalBaseChangeTor (B := B) f 0 ≃ₗ[B] B :=
  principalBaseChangeTorZeroEquiv f hf

/-- The degree-one all-degree package is the face algebra when the relation vanishes. -/
noncomputable def principalBaseChangeTor_one_equiv (f : A) (hf : algebraMap A B f = 0) :
    principalBaseChangeTor (B := B) f 1 ≃ₗ[B] B :=
  principalBaseChangeTorOneEquiv f hf

omit [IsDomain A] in
/-- All higher groups of the base-changed length-one free resolution are zero. -/
theorem principalBaseChangeTor_subsingleton_of_two_le (f : A) (i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (principalBaseChangeTor (B := B) f i) := by
  cases i with
  | zero => simp at hi
  | succ i =>
      cases i with
      | zero => simp at hi
      | succ k =>
          change Subsingleton PUnit
          infer_instance

end

end GaloisForLFunctions.HTGeometry
