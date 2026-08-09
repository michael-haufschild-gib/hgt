import GaloisForLFunctions.HTGeometry.PrincipalConormal

/-!
# Koszul homology of two unit presentations of one regular factor

For a regular element `z` and units `a,b`, this file computes the actual homology quotients of
the three-term Koszul complex on `(z*a,z*b)`.  Degree zero and degree one are both `R/(z)`, degree
two vanishes, and the degree-one generator is the syzygy `(b,-a)`.  Composing degree one with the
principal cotangent equivalence identifies it with `(z)/(z)^2`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R]

/-- Degree-one differential of the Koszul complex on `(z*a,z*b)`. -/
def commonFactorKoszulD1 (z : R) (a b : Rˣ) : R × R →ₗ[R] R where
  toFun p := p.1 * (z * (a : R)) + p.2 * (z * (b : R))
  map_add' x y := by simp; ring
  map_smul' r x := by simp [smul_eq_mul]; ring

/-- Degree-two differential of the Koszul complex on `(z*a,z*b)`. -/
def commonFactorKoszulD2 (z : R) (a b : Rˣ) : R →ₗ[R] R × R where
  toFun t := (-t * (z * (b : R)), t * (z * (a : R)))
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp [smul_eq_mul] <;> ring

@[simp] theorem commonFactorKoszulD1_apply (z : R) (a b : Rˣ) (p : R × R) :
    commonFactorKoszulD1 z a b p = p.1 * (z * (a : R)) + p.2 * (z * (b : R)) := rfl

@[simp] theorem commonFactorKoszulD2_apply (z : R) (a b : Rˣ) (t : R) :
    commonFactorKoszulD2 z a b t = (-t * (z * (b : R)), t * (z * (a : R))) := rfl

/-- The two Koszul differentials compose to zero. -/
theorem commonFactorKoszulD1_comp_D2 (z : R) (a b : Rˣ) :
    commonFactorKoszulD1 z a b ∘ₗ commonFactorKoszulD2 z a b = 0 := by
  apply LinearMap.ext
  intro t
  simp
  ring

/-- Degree-zero homology, defined as the actual cokernel of `d₁`. -/
abbrev commonFactorKoszulH0 (z : R) (a b : Rˣ) : Type _ :=
  R ⧸ LinearMap.range (commonFactorKoszulD1 z a b)

/-- Degree-one cycles of the actual Koszul complex. -/
abbrev commonFactorKoszulCycles (z : R) (a b : Rˣ) : Submodule R (R × R) :=
  LinearMap.ker (commonFactorKoszulD1 z a b)

/-- Degree-one boundaries, as a submodule of degree-one cycles. -/
def commonFactorKoszulBoundaries (z : R) (a b : Rˣ) :
    Submodule R (commonFactorKoszulCycles z a b) :=
  (LinearMap.range (commonFactorKoszulD2 z a b)).comap
    (commonFactorKoszulCycles z a b).subtype

/-- Degree-one homology, defined as cycles modulo boundaries. -/
abbrev commonFactorKoszulH1 (z : R) (a b : Rˣ) : Type _ :=
  commonFactorKoszulCycles z a b ⧸ commonFactorKoszulBoundaries z a b

/-- Degree-two homology, the kernel of `d₂`. -/
abbrev commonFactorKoszulH2 (z : R) (a b : Rˣ) : Submodule R R :=
  LinearMap.ker (commonFactorKoszulD2 z a b)

/-- The image ideal of `(z*a,z*b)` is exactly the principal ideal `(z)`. -/
theorem range_commonFactorKoszulD1 (z : R) (a b : Rˣ) :
    LinearMap.range (commonFactorKoszulD1 z a b) =
      (Ideal.span ({z} : Set R) : Submodule R R) := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨p.1 * (a : R) + p.2 * (b : R), ?_⟩
    simp
    ring
  · intro hr
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    refine ⟨(c * (↑(a⁻¹) : R), 0), ?_⟩
    simp only [commonFactorKoszulD1_apply, zero_mul, add_zero]
    calc
      c * (↑(a⁻¹) : R) * (z * (a : R)) = c * z * ((↑(a⁻¹) : R) * (a : R)) := by ring
      _ = z * c := by simp [mul_comm]

/-- Degree-zero Koszul homology is the Cartier divisor ring `R/(z)`. -/
def commonFactorKoszulH0Equiv (z : R) (a b : Rˣ) :
    commonFactorKoszulH0 z a b ≃ₗ[R] R ⧸ (Ideal.span ({z} : Set R) : Submodule R R) :=
  Submodule.quotEquivOfEq _ _ (range_commonFactorKoszulD1 z a b)

/-- The shell-presentation syzygy `t ↦ t(b,-a)`. -/
def commonFactorSyzygyMap (a b : Rˣ) : R →ₗ[R] R × R where
  toFun t := (t * (b : R), -(t * (a : R)))
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp [smul_eq_mul] <;> ring

/-- Every multiple of `(b,-a)` is a degree-one cycle. -/
def commonFactorSyzygyToCycles (z : R) (a b : Rˣ) :
    R →ₗ[R] commonFactorKoszulCycles z a b :=
  (commonFactorSyzygyMap a b).codRestrict _ fun t => by
    rw [LinearMap.mem_ker]
    simp [commonFactorSyzygyMap]
    ring

theorem commonFactorSyzygyToCycles_injective (z : R) (a b : Rˣ) :
    Function.Injective (commonFactorSyzygyToCycles z a b) := by
  intro x y h
  have hfst := congrArg (fun p : commonFactorKoszulCycles z a b => p.1.1) h
  apply_fun (fun r : R => r * (↑(b⁻¹) : R)) at hfst
  simpa [commonFactorSyzygyToCycles, commonFactorSyzygyMap, mul_assoc] using hfst

/-- Regularity hypothesis in the exact form used by the homology computation. -/
def IsKoszulRegular (z : R) : Prop := ∀ r : R, z * r = 0 → r = 0

/-- Every degree-one cycle is a unique multiple of `(b,-a)`. -/
theorem commonFactorSyzygyToCycles_surjective {z : R} (a b : Rˣ)
    (hz : IsKoszulRegular z) :
    Function.Surjective (commonFactorSyzygyToCycles z a b) := by
  intro p
  have hp := p.2
  rw [LinearMap.mem_ker] at hp
  rw [commonFactorKoszulD1_apply] at hp
  have hlin : p.1.1 * (a : R) + p.1.2 * (b : R) = 0 := by
    apply hz
    calc
      z * (p.1.1 * (a : R) + p.1.2 * (b : R)) =
          p.1.1 * (z * (a : R)) + p.1.2 * (z * (b : R)) := by ring
      _ = 0 := hp
  refine ⟨p.1.1 * (↑(b⁻¹) : R), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · simp [commonFactorSyzygyToCycles, commonFactorSyzygyMap, mul_assoc]
  · have hmul := congrArg (fun r : R => r * (↑(b⁻¹) : R)) hlin
    simp [add_mul, mul_assoc] at hmul
    change -(p.1.1 * (↑(b⁻¹) : R) * (a : R)) = p.1.2
    linear_combination -hmul

/-- The syzygy line is exactly the degree-one cycle module. -/
def commonFactorSyzygyEquiv {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    R ≃ₗ[R] commonFactorKoszulCycles z a b :=
  LinearEquiv.ofBijective (commonFactorSyzygyToCycles z a b)
    ⟨commonFactorSyzygyToCycles_injective z a b,
      commonFactorSyzygyToCycles_surjective a b hz⟩

/-- Under the syzygy trivialization, boundaries are exactly `z` times the syzygy line. -/
theorem map_span_commonFactorSyzygyEquiv_eq_boundaries {z : R} (a b : Rˣ)
    (hz : IsKoszulRegular z) :
    Submodule.map (commonFactorSyzygyEquiv a b hz).toLinearMap
        (Ideal.span ({z} : Set R) : Submodule R R) =
      commonFactorKoszulBoundaries z a b := by
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    change r ∈ Ideal.span ({z} : Set R) at hr
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    change (commonFactorSyzygyEquiv a b hz (z * c)).1 ∈
      LinearMap.range (commonFactorKoszulD2 z a b)
    refine ⟨-c, ?_⟩
    apply Prod.ext <;>
      simp [commonFactorSyzygyEquiv, commonFactorSyzygyToCycles,
        commonFactorSyzygyMap] <;> ring
  · intro hp
    change p.1 ∈ LinearMap.range (commonFactorKoszulD2 z a b) at hp
    obtain ⟨t, ht⟩ := hp
    refine ⟨-t * z, ?_, ?_⟩
    · change -t * z ∈ Ideal.span ({z} : Set R)
      rw [Ideal.mem_span_singleton]
      exact ⟨-t, by ring⟩
    · apply Subtype.ext
      rw [← ht]
      apply Prod.ext <;>
        simp [commonFactorSyzygyEquiv, commonFactorSyzygyToCycles,
          commonFactorSyzygyMap] <;> ring

/-- Degree-one Koszul homology is `R/(z)`, with `t mod z` represented by `t(b,-a)`. -/
def commonFactorKoszulH1Equiv {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    commonFactorKoszulH1 z a b ≃ₗ[R]
      R ⧸ (Ideal.span ({z} : Set R) : Submodule R R) :=
  (Submodule.Quotient.equiv
    (Ideal.span ({z} : Set R) : Submodule R R)
    (commonFactorKoszulBoundaries z a b)
    (commonFactorSyzygyEquiv a b hz)
    (map_span_commonFactorSyzygyEquiv_eq_boundaries a b hz)).symm

/-- Degree two vanishes for a regular common factor. -/
theorem commonFactorKoszulH2_eq_bot {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    commonFactorKoszulH2 z a b = ⊥ := by
  ext t
  constructor
  · intro ht
    rw [LinearMap.mem_ker] at ht
    have hfst := congrArg Prod.fst ht
    have hzero : z * t = 0 := by
      apply_fun (fun r : R => r * (↑(b⁻¹) : R)) at hfst
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfst
    exact (hz t hzero : t = 0)
  · rintro rfl
    simp

/-- The excess degree-one class is the principal Cartier conormal `(z)/(z)^2`. -/
def commonFactorKoszulH1CotangentEquiv {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    commonFactorKoszulH1 z a b ≃ₗ[R] (Ideal.span ({z} : Set R)).Cotangent :=
  (commonFactorKoszulH1Equiv a b hz).trans
    (principalCotangentEquiv fun x y h => by
      apply sub_eq_zero.mp
      apply hz
      simpa [mul_sub] using sub_eq_zero.mpr h)

end

end GaloisForLFunctions.HTGeometry
