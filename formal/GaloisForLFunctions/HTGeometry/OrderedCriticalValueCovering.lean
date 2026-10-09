import GaloisForLFunctions.HTGeometry.OrderedCriticalValueSurjectivity
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homotopy.Lifting
import GaloisForLFunctions.HTGeometry.EntireNonzeroPathConnected

/-!
# Connected finite covering by regular polynomial parameters

The actual ordered critical-value map is a surjective proper finite covering over
distinct critical values. Its parameter space is path connected, every value path
lifts uniquely, and monodromy is transitive on every fiber. This concerns parameter
continuation; prescribed monodromy of the polynomial maps remains a separate task.
-/

open Set Filter Topology unitInterval
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

abbrev Configuration (n : ℕ) := ↥(FiniteComplexConfiguration.space (n + 1))
abbrev RegularParameter (n : ℕ) :=
  {v : Parameter n // Function.Injective (valuesWithConstant v)}

def regularMap (n : ℕ) : RegularParameter n → Configuration n :=
  (FiniteComplexConfiguration.space (n + 1)).restrictPreimage valuesWithConstant

theorem continuous_regularMap (n : ℕ) : Continuous (regularMap n) :=
  (continuous_valuesWithConstant n).restrictPreimage

theorem isProperMap_regularMap (n : ℕ) : IsProperMap (regularMap n) :=
  (isProperMap_valuesWithConstant n).restrictPreimage _

theorem isLocalHomeomorph_regularMap (n : ℕ) : IsLocalHomeomorph (regularMap n) := by
  have hpre : IsOpen {v : Parameter n | Function.Injective (valuesWithConstant v)} :=
    (FiniteComplexConfiguration.isOpen_space (n + 1)).preimage (continuous_valuesWithConstant n)
  have hcomp : IsLocalHomeomorph
      (valuesWithConstant (n := n) ∘ (Subtype.val : RegularParameter n → Parameter n)) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact (isLocalHomeomorphOn_valuesWithConstant_distinct n).comp
      hpre.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (fun v _ => v.property)
  exact IsLocalHomeomorph.of_comp (g := (Subtype.val : Configuration n → (Fin (n + 1) → ℂ)))
    hcomp (FiniteComplexConfiguration.isOpen_space (n + 1)).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (continuous_regularMap n)

theorem isCoveringMap_regularMap (n : ℕ) : IsCoveringMap (regularMap n) :=
  isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (isLocalHomeomorph_regularMap n) (isProperMap_regularMap n)

theorem surjective_regularMap (n : ℕ) : Function.Surjective (regularMap n) :=
  (surjective_valuesWithConstant n).restrictPreimage _

theorem finite_regularMap_fiber (n : ℕ) (b : Configuration n) :
    Finite ((regularMap n) ⁻¹' {b}) :=
  fibre_finite (isLocalHomeomorph_regularMap n) (isProperMap_regularMap n) b

/-- Every collision-free critical-value path has exactly one parameter lift from its chosen
initial polynomial. -/
theorem existsUnique_regularMap_path_lift (n : ℕ) (γ : C(I, Configuration n))
    (v : RegularParameter n) (hγ : γ 0 = regularMap n v) :
    ∃! Γ : C(I, RegularParameter n), regularMap n ∘ Γ = γ ∧ Γ 0 = v := by
  let cov := isCoveringMap_regularMap n
  refine ⟨cov.liftPath γ v hγ, ⟨cov.liftPath_lifts γ v hγ, cov.liftPath_zero γ v hγ⟩, ?_⟩
  intro Γ hΓ
  exact (cov.eq_liftPath_iff' hγ).mpr hΓ

/-- The discriminant of the actual ordered values, pulled back to polynomial parameters. -/
def valueDiscriminant {n : ℕ} (v : Parameter n) : ℂ :=
  MvPolynomial.eval (valuesWithConstant v) (FiniteComplexConfiguration.discriminant (n + 1))

theorem valueDiscriminant_ne_zero_iff {n : ℕ} (v : Parameter n) :
    valueDiscriminant v ≠ 0 ↔ Function.Injective (valuesWithConstant v) :=
  FiniteComplexConfiguration.eval_discriminant_ne_zero_iff (n + 1) _

theorem contDiff_valueDiscriminant (n : ℕ) :
    ContDiff ℂ ⊤ (valueDiscriminant (n := n)) := by
  classical
  unfold valueDiscriminant FiniteComplexConfiguration.discriminant
  simp only [map_prod, map_sub, MvPolynomial.eval_X]
  apply contDiff_prod
  intro i _
  apply contDiff_prod
  intro j _
  exact ((contDiff_pi.mp (contDiff_valuesWithConstant n)) i).sub
    ((contDiff_pi.mp (contDiff_valuesWithConstant n)) j)

/-- The actual regular parameter locus is path connected, not merely its value space. -/
theorem isPathConnected_regularParameter (n : ℕ) :
    IsPathConnected {v : Parameter n | Function.Injective (valuesWithConstant v)} := by
  obtain ⟨v, hv⟩ := exists_injective_valuesWithConstant n
  have h := isPathConnected_entire_nonzeroLocus
    ((contDiff_valueDiscriminant n).differentiable (by simp))
    ((valueDiscriminant_ne_zero_iff v).mpr hv)
  simpa only [valueDiscriminant_ne_zero_iff] using h

theorem pathConnectedSpace_regularParameter (n : ℕ) : PathConnectedSpace (RegularParameter n) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_regularParameter n)

/-- Any two parameters in one regular fiber are joined by a lifted loop of critical values. -/
theorem exists_loop_transport_regularMap (n : ℕ) (b : Configuration n)
    (v w : regularMap n ⁻¹' {b}) :
    ∃ Γ : Path v.val w.val, ∃ γ : Path b b, regularMap n ∘ Γ = γ := by
  letI := pathConnectedSpace_regularParameter n
  let Γ := PathConnectedSpace.somePath v.val w.val
  let γ : Path b b :=
    { toFun := fun t => regularMap n (Γ t)
      continuous_toFun := (continuous_regularMap n).comp Γ.continuous
      source' := by rw [Γ.source]; exact v.property
      target' := by rw [Γ.target]; exact w.property }
  exact ⟨Γ, γ, rfl⟩

/-- Monodromy of the actual regular critical-value covering is transitive on every fiber. -/
theorem monodromy_regularMap_transitive (n : ℕ) (b : Configuration n)
    (v w : regularMap n ⁻¹' {b}) :
    ∃ γ : Path.Homotopic.Quotient b b, (isCoveringMap_regularMap n).monodromy γ v = w := by
  obtain ⟨Γ, γ, hΓ⟩ := exists_loop_transport_regularMap n b v w
  refine ⟨Path.Homotopic.Quotient.mk γ, ?_⟩
  apply Subtype.ext
  let cov := isCoveringMap_regularMap n
  change cov.liftPath γ v.val (γ.source.trans v.property.symm) 1 = w.val
  have hΓeq : (Γ : C(I, RegularParameter n)) =
      cov.liftPath γ v.val (γ.source.trans v.property.symm) :=
    (cov.eq_liftPath_iff' _).mpr ⟨hΓ, Γ.source⟩
  rw [← hΓeq]
  exact Γ.target

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
