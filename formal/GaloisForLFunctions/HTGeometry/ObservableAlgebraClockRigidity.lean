import GaloisForLFunctions.HTGeometry.RelationalHistoryExternalTimeAmbiguityClassification

/-!
# Universal observable-algebra clock rigidity

For an arbitrary unital algebra acted on by an arbitrary group, a linear
refactorization covariant with every labelled left multiplier and every clock
shift is exactly one clock-origin automorphism followed by right
multiplication by one action-invariant element.  If the refactorization is
unital, the invariant is the identity and only the clock-origin automorphism
remains.

The theorem has no finiteness, cardinality, commutativity, topology, spectral
type, or factor-type restriction.  A regular function-algebra corollary
removes point-reading projectors entirely and applies to groups of arbitrary
cardinality without a decidable equality.
-/

namespace HTGeometry

noncomputable section

universe u v w x

variable {𝕜 : Type u} {A : Type v} {G : Type w}
  [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Group G]

/-- One action automorphism followed by right multiplication by a residual
algebra element. -/
def twistedRightMultiplier
    (σ : G → A ≃ₐ[𝕜] A) (g : G) (c : A) :
    A →ₗ[𝕜] A where
  toFun a := σ g a * c
  map_add' a b := by
    rw [map_add, add_mul]
  map_smul' q a := by
    simp [Algebra.smul_mul_assoc]

/-- **Universal observable-algebra stabilizer, forward form.**  Multiplier
covariance fixes a refactorization up to right multiplication, and shift
covariance forces that residual element to be invariant under the full group
action. -/
theorem covariantIntertwiner_eq_twistedRightMultiplier
    (σ : G → A ≃ₐ[𝕜] A)
    (g : G) (T : A →ₗ[𝕜] A)
    (hmodule :
      ∀ a b : A, T (a * b) = σ g a * T b)
    (hshift :
      ∀ h : G, ∀ b : A,
        T (σ h b) = σ (g * h * g⁻¹) (T b)) :
    ∃ c : A,
      (∀ h : G, σ h c = c) ∧
      T = twistedRightMultiplier σ g c := by
  let c : A := T 1
  have hfixed : ∀ k : G, σ k c = c := by
    intro k
    have hcov := hshift (g⁻¹ * k * g) 1
    have hindex :
        g * (g⁻¹ * k * g) * g⁻¹ = k := by
      group
    rw [map_one, hindex] at hcov
    exact hcov.symm
  refine ⟨c, hfixed, LinearMap.ext fun a => ?_⟩
  have hfactor := hmodule a 1
  simpa [c, twistedRightMultiplier] using hfactor

omit [Group G] in
/-- Every twisted right multiplier has the required labelled-multiplier
covariance. -/
theorem twistedRightMultiplier_module_covariant
    (σ : G → A ≃ₐ[𝕜] A)
    (g : G) (c : A) (a b : A) :
    twistedRightMultiplier σ g c (a * b) =
      σ g a * twistedRightMultiplier σ g c b := by
  simp [twistedRightMultiplier, mul_assoc]

/-- An action-invariant residual element gives exact shift covariance. -/
theorem twistedRightMultiplier_shift_covariant
    (σ : G → A ≃ₐ[𝕜] A)
    (hcomp :
      ∀ p q : G, ∀ a : A,
        σ (p * q) a = σ p (σ q a))
    (g : G) (c : A)
    (hfixed : ∀ h : G, σ h c = c)
    (h : G) (b : A) :
    twistedRightMultiplier σ g c (σ h b) =
      σ (g * h * g⁻¹) (twistedRightMultiplier σ g c b) := by
  simp only [twistedRightMultiplier, LinearMap.coe_mk,
    AddHom.coe_mk, map_mul]
  rw [← hcomp, hfixed, ← hcomp]
  congr 2
  group

/-- **Exact universal observable-algebra stabilizer.**  The full stabilizer
is precisely one action automorphism times one element of the action-fixed
algebra. -/
theorem covariantIntertwiner_iff_exists_fixed_twistedRightMultiplier
    (σ : G → A ≃ₐ[𝕜] A)
    (hcomp :
      ∀ p q : G, ∀ a : A,
        σ (p * q) a = σ p (σ q a))
    (g : G) (T : A →ₗ[𝕜] A) :
    ((∀ a b : A, T (a * b) = σ g a * T b) ∧
      (∀ h : G, ∀ b : A,
        T (σ h b) = σ (g * h * g⁻¹) (T b))) ↔
    ∃ c : A,
      (∀ h : G, σ h c = c) ∧
      T = twistedRightMultiplier σ g c := by
  constructor
  · rintro ⟨hmodule, hshift⟩
    exact covariantIntertwiner_eq_twistedRightMultiplier
      σ g T hmodule hshift
  · rintro ⟨c, hfixed, rfl⟩
    exact
      ⟨twistedRightMultiplier_module_covariant σ g c,
        twistedRightMultiplier_shift_covariant
          σ hcomp g c hfixed⟩

omit [Group G] in
/-- **Unital rigidity.**  If a labelled-multiplier-covariant
refactorization preserves the identity, it is exactly the selected
clock-origin automorphism. -/
theorem unital_covariantIntertwiner_eq_action
    (σ : G → A ≃ₐ[𝕜] A)
    (g : G) (T : A →ₗ[𝕜] A)
    (hmodule :
      ∀ a b : A, T (a * b) = σ g a * T b)
    (hone : T 1 = 1) :
    ∀ a : A, T a = σ g a := by
  intro a
  have hfactor := hmodule a 1
  simpa [hone] using hfactor

section TomographicReports

variable {reporter : Type x}

/-- A family of scalar reports is tomographically complete when equality of
all reports forces equality in the labelled observable algebra. -/
def AlgebraReportsSeparatePoints
    (report : reporter → (A →ₗ[𝕜] 𝕜)) : Prop :=
  ∀ a b : A, (∀ r : reporter, report r a = report r b) → a = b

omit [Group G] in
/-- Tomographically complete equality of all scalar multiplier reports
forces the full algebra-valued multiplier covariance identity. -/
theorem module_covariance_of_all_reports
    (report : reporter → (A →ₗ[𝕜] 𝕜))
    (hseparates : AlgebraReportsSeparatePoints report)
    (σ : G → A ≃ₐ[𝕜] A)
    (g : G) (T : A →ₗ[𝕜] A)
    (hreports :
      ∀ r : reporter, ∀ a b : A,
        report r (T (a * b)) =
          report r (σ g a * T b)) :
    ∀ a b : A, T (a * b) = σ g a * T b := by
  intro a b
  apply hseparates
  intro r
  exact hreports r a b

/-- Tomographically complete equality of all scalar shift reports forces
the full algebra-valued clock covariance identity. -/
theorem shift_covariance_of_all_reports
    (report : reporter → (A →ₗ[𝕜] 𝕜))
    (hseparates : AlgebraReportsSeparatePoints report)
    (σ : G → A ≃ₐ[𝕜] A)
    (g : G) (T : A →ₗ[𝕜] A)
    (hreports :
      ∀ r : reporter, ∀ h : G, ∀ b : A,
        report r (T (σ h b)) =
          report r (σ (g * h * g⁻¹) (T b))) :
    ∀ h : G, ∀ b : A,
      T (σ h b) = σ (g * h * g⁻¹) (T b) := by
  intro h b
  apply hseparates
  intro r
  exact hreports r h b

/-- **Tomographic stabilizer law.**  Equality of every scalar report in a
tomographically complete family has exactly the same stabilizer as the full
observable-algebra covariance law: one origin automorphism times one
action-fixed residual element. -/
theorem allReports_covariantIntertwiner_iff
    (report : reporter → (A →ₗ[𝕜] 𝕜))
    (hseparates : AlgebraReportsSeparatePoints report)
    (σ : G → A ≃ₐ[𝕜] A)
    (hcomp :
      ∀ p q : G, ∀ a : A,
        σ (p * q) a = σ p (σ q a))
    (g : G) (T : A →ₗ[𝕜] A) :
    ((∀ r : reporter, ∀ a b : A,
        report r (T (a * b)) =
          report r (σ g a * T b)) ∧
      (∀ r : reporter, ∀ h : G, ∀ b : A,
        report r (T (σ h b)) =
          report r (σ (g * h * g⁻¹) (T b)))) ↔
    ∃ c : A,
      (∀ h : G, σ h c = c) ∧
      T = twistedRightMultiplier σ g c := by
  constructor
  · rintro ⟨hmoduleReports, hshiftReports⟩
    apply
      (covariantIntertwiner_iff_exists_fixed_twistedRightMultiplier
        σ hcomp g T).mp
    exact
      ⟨module_covariance_of_all_reports
          report hseparates σ g T hmoduleReports,
        shift_covariance_of_all_reports
          report hseparates σ g T hshiftReports⟩
  · rintro ⟨c, hfixed, hT⟩
    have hfull :=
      (covariantIntertwiner_iff_exists_fixed_twistedRightMultiplier
        σ hcomp g T).mpr ⟨c, hfixed, hT⟩
    constructor
    · intro r a b
      exact congrArg (report r) (hfull.1 a b)
    · intro r h b
      exact congrArg (report r) (hfull.2 h b)

end TomographicReports

section RegularFunctionClock

/-- Left translation as an algebra automorphism of the full scalar function
algebra on an arbitrary group.  No point projectors or decidable equality are
used. -/
def functionClockTranslationAlgEquiv
    (g : G) : (G → 𝕜) ≃ₐ[𝕜] (G → 𝕜) where
  toFun f row := f (g⁻¹ * row)
  invFun f row := f (g * row)
  left_inv f := by
    ext row
    simp
  right_inv f := by
    ext row
    simp
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Regular translations compose according to the clock group law. -/
theorem functionClockTranslationAlgEquiv_comp
    (g h : G) (f : G → 𝕜) :
    functionClockTranslationAlgEquiv (𝕜 := 𝕜) (g * h) f =
      functionClockTranslationAlgEquiv g
        (functionClockTranslationAlgEquiv h f) := by
  ext row
  simp [functionClockTranslationAlgEquiv, mul_assoc]

/-- The only functions invariant under every regular left translation are
the constant functions. -/
theorem functionClock_invariant_eq_constant
    (c : G → 𝕜)
    (hfixed :
      ∀ h : G,
        functionClockTranslationAlgEquiv h c = c) :
    c = fun _ => c 1 := by
  funext row
  have hentry := congr_fun (hfixed row) row
  simpa [functionClockTranslationAlgEquiv] using hentry.symm

/-- Multiplier and shift covariance on the full function algebra force one
regular clock translation times one scalar, for every group of arbitrary
cardinality. -/
theorem functionClock_covariantIntertwiner_eq_scalar_translation
    (g : G) (T : (G → 𝕜) →ₗ[𝕜] (G → 𝕜))
    (hmodule :
      ∀ a b : G → 𝕜,
        T (a * b) =
          functionClockTranslationAlgEquiv g a * T b)
    (hshift :
      ∀ h : G, ∀ b : G → 𝕜,
        T (functionClockTranslationAlgEquiv h b) =
          functionClockTranslationAlgEquiv
            (g * h * g⁻¹) (T b)) :
    ∃ c : 𝕜,
      T = c •
        (functionClockTranslationAlgEquiv g).toLinearMap := by
  obtain ⟨w, hfixed, hT⟩ :=
    covariantIntertwiner_eq_twistedRightMultiplier
      (fun h => functionClockTranslationAlgEquiv h)
      g T hmodule hshift
  have hw := functionClock_invariant_eq_constant w hfixed
  refine ⟨w 1, LinearMap.ext fun f => ?_⟩
  have hentry := LinearMap.congr_fun hT f
  ext row
  have hwrow := congr_fun hw row
  simpa [twistedRightMultiplier, hwrow, mul_comm] using
    congr_fun hentry row

/-- **Exact point-projector-free clock law.**  On the full function algebra
over every group, labelled-multiplier and shift covariance holds exactly for
scalar regular translations. -/
theorem functionClock_covariantIntertwiner_iff
    (g : G) (T : (G → 𝕜) →ₗ[𝕜] (G → 𝕜)) :
    ((∀ a b : G → 𝕜,
        T (a * b) =
          functionClockTranslationAlgEquiv g a * T b) ∧
      (∀ h : G, ∀ b : G → 𝕜,
        T (functionClockTranslationAlgEquiv h b) =
          functionClockTranslationAlgEquiv
            (g * h * g⁻¹) (T b))) ↔
    ∃ c : 𝕜,
      T = c •
        (functionClockTranslationAlgEquiv g).toLinearMap := by
  constructor
  · rintro ⟨hmodule, hshift⟩
    exact functionClock_covariantIntertwiner_eq_scalar_translation
      g T hmodule hshift
  · rintro ⟨c, rfl⟩
    constructor
    · intro a b
      ext row
      change
        c * (a (g⁻¹ * row) * b (g⁻¹ * row)) =
          a (g⁻¹ * row) * (c * b (g⁻¹ * row))
      ring
    · intro h b
      ext row
      change
        c * b (h⁻¹ * (g⁻¹ * row)) =
          c * b (g⁻¹ * ((g * h * g⁻¹)⁻¹ * row))
      congr 2
      group

end RegularFunctionClock

end

end HTGeometry
