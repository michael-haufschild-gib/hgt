import GaloisForLFunctions.HTGeometry.ContinuousMapLocallyConvex

/-!
# Holomorphic functions on a plane open set, in the compact-open topology

The functions on a plane set that extend holomorphically form a real subspace of the continuous
functions on the subtype, carried with the compact-open topology.  Multiplication by `i` is a real
endomorphism of that subspace, and restriction to a subset is a real map into the continuous
functions there.

This is the domain-general form of the quadrant construction, used when the domain is an arbitrary
convex region rather than the critical quadrant.

* `HTGeometry.holoOn`, `HTGeometry.holoOnImul`, `HTGeometry.holoOnRestrict`.
-/

noncomputable section

open Complex

namespace HTGeometry

/-- The real subspace of continuous functions on a plane set that extend holomorphically. -/
def holoOn (D : Set ℂ) : Submodule ℝ C(D, ℂ) where
  carrier := {f | ∃ F : ℂ → ℂ, DifferentiableOn ℂ F D ∧ ∀ z : D, f z = F (z : ℂ)}
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨fun w => F w + G w, hF.add hG, fun z => by simp [hf z, hg z]⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, fun _ => rfl⟩
  smul_mem' := by
    rintro r f ⟨F, hF, hf⟩
    exact ⟨fun w => (r : ℂ) * F w, (differentiableOn_const (r : ℂ)).mul hF,
      fun z => by simp [hf z, Complex.real_smul]⟩

theorem mem_holoOn_iff {D : Set ℂ} {f : C(D, ℂ)} :
    f ∈ holoOn D ↔ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F D ∧ ∀ z : D, f z = F (z : ℂ) := Iff.rfl

instance (D : Set ℂ) : ContinuousAdd (holoOn D) :=
  (inferInstance : IsTopologicalAddGroup (holoOn D)).toContinuousAdd

instance (D : Set ℂ) : ContinuousNeg (holoOn D) :=
  (inferInstance : IsTopologicalAddGroup (holoOn D)).toContinuousNeg

theorem imul_mem_holoOn {D : Set ℂ} {f : C(D, ℂ)} (hf : f ∈ holoOn D) :
    Complex.I • f ∈ holoOn D := by
  obtain ⟨F, hF, hfF⟩ := hf
  exact ⟨fun w => Complex.I * F w, (differentiableOn_const Complex.I).mul hF,
    fun z => by simp [hfF z]⟩

/-- Multiplication by `i` on the holomorphic subspace, as a real endomorphism. -/
def holoOnImul (D : Set ℂ) : holoOn D →ₗ[ℝ] holoOn D where
  toFun := fun g => ⟨Complex.I • (g : C(D, ℂ)), imul_mem_holoOn g.2⟩
  map_add' := fun g h => by
    apply Subtype.ext
    show Complex.I • ((g : C(D, ℂ)) + (h : C(D, ℂ)))
      = Complex.I • (g : C(D, ℂ)) + Complex.I • (h : C(D, ℂ))
    ext z
    simp [mul_add]
  map_smul' := fun r g => by
    apply Subtype.ext
    show Complex.I • (r • (g : C(D, ℂ))) = r • (Complex.I • (g : C(D, ℂ)))
    ext z
    simp [Complex.real_smul]
    ring

@[simp] theorem holoOnImul_coe {D : Set ℂ} (g : holoOn D) :
    ((holoOnImul D g : holoOn D) : C(D, ℂ)) = Complex.I • (g : C(D, ℂ)) := rfl

/-- Restriction of a holomorphic element to a subset of the domain. -/
def holoOnRestrict {D K : Set ℂ} (hK : K ⊆ D) : holoOn D →ₗ[ℝ] C(K, ℂ) where
  toFun := fun g => (g : C(D, ℂ)).comp
    ⟨fun z => ⟨(z : ℂ), hK z.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem holoOnRestrict_apply {D K : Set ℂ} (hK : K ⊆ D) (g : holoOn D) (z : K) :
    holoOnRestrict hK g z = (g : C(D, ℂ)) ⟨(z : ℂ), hK z.2⟩ := rfl

theorem holoOnRestrict_imul {D K : Set ℂ} (hK : K ⊆ D) (g : holoOn D) :
    holoOnRestrict hK (holoOnImul D g) = Complex.I • holoOnRestrict hK g := rfl

end HTGeometry
