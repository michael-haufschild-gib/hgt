import GaloisForLFunctions.HTGeometry.ConstitutiveCoefficientLiftTransgression
import GaloisForLFunctions.HTGeometry.UnseparatedCofiberTower
import GaloisForLFunctions.HTGeometry.GammaGaugeClockVarianceSeparation

/-!
# Carrier bifurcation and coherence engine

Cokernel controls existence, kernel controls next coherence, and closure of range controls
exact versus Hausdorff-visible higher-law birth.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

/-- Residual of the pentagon equation for a ternary carrier. -/
def HigherPentagonResidual {M : Type u} {A : Type v}
    [Add M] [AddGroup A] (h : M → M → M → A) (w x y z : M) : A :=
  h w x y + h w (x + y) z + h x y z -
    h (w + x) y z - h w x (y + z)

/-- A ternary carrier whose image is the associator of a binary compensator. -/
def IsHigherCarrierLift {M : Type u} {K : Type v} {A : Type w}
    [Add M] [AddGroup K] [AddGroup A]
    (T : K →+ A) (κ : M → M → A) (h : M → M → M → K) : Prop :=
  ∀ x y z, T (h x y z) = PromotionAssociator κ x y z

/-- Applying an additive observer commutes with forming the pentagon residual. -/
theorem higherPentagonResidual_observed
    {M : Type u} {K : Type v} {A : Type w}
    [Add M] [AddCommGroup K] [AddCommGroup A]
    (T : K →+ A) (h : M → M → M → K) (w x y z : M) :
    T (HigherPentagonResidual h w x y z) =
      HigherPentagonResidual (fun a b c ↦ T (h a b c)) w x y z := by
  simp [HigherPentagonResidual]

/-- Every lifted pentagon residual lands in the kernel of the carrier map. -/
theorem higherCarrierLift_residual_mem_kernel
    {M : Type u} {K : Type v} {A : Type w}
    [AddSemigroup M] [AddCommGroup K] [AddCommGroup A]
    (T : K →+ A) (κ : M → M → A) (h : M → M → M → K)
    (hlift : IsHigherCarrierLift T κ h) (w x y z : M) :
    HigherPentagonResidual h w x y z ∈ AddMonoidHom.ker T := by
  apply AddMonoidHom.mem_ker.mpr
  rw [higherPentagonResidual_observed]
  simp only [HigherPentagonResidual]
  rw [hlift, hlift, hlift, hlift, hlift]
  have hp := promotionAssociator_pentagon κ w x y z
  rw [hp]
  abel

/-- An injective carrier map reflects exact pentagon coherence. -/
theorem higherCarrierLift_pentagon_of_injective
    {M : Type u} {K : Type v} {A : Type w}
    [AddSemigroup M] [AddCommGroup K] [AddCommGroup A]
    (T : K →+ A) (hT : Function.Injective T)
    (κ : M → M → A) (h : M → M → M → K)
    (hlift : IsHigherCarrierLift T κ h) (w x y z : M) :
    HigherPentagonResidual h w x y z = 0 := by
  apply hT
  rw [map_zero]
  exact AddMonoidHom.mem_ker.mp
    (higherCarrierLift_residual_mem_kernel T κ h hlift w x y z)

section Topological

variable {𝕜 : Type u} {E : Type v} {F : Type w}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Algebraic carrier obstruction: the associator modulo the exact carrier range. -/
def higherBirthObstruction {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (x y z : M) :
    unseparatedCofiber T :=
  (LinearMap.range T).mkQ (PromotionAssociator κ x y z)

/-- Hausdorff carrier obstruction: the associator modulo the closed carrier range. -/
def separatedHigherBirthObstruction {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (x y z : M) :
    separatedCofiber T :=
  (LinearMap.range T).topologicalClosure.mkQ (PromotionAssociator κ x y z)

/-- Algebraic obstruction vanishes exactly when the associator has a carrier preimage. -/
theorem higherBirthObstruction_eq_zero_iff_exists
    {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (x y z : M) :
    higherBirthObstruction T κ x y z = 0 ↔
      ∃ e, T e = PromotionAssociator κ x y z := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Separated obstruction vanishes exactly when the associator is approximable by carriers. -/
theorem separatedHigherBirthObstruction_eq_zero_iff_approximable
    {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (x y z : M) :
    separatedHigherBirthObstruction T κ x y z = 0 ↔
      PromotionAssociator κ x y z ∈
        (LinearMap.range T).topologicalClosure := by
  exact Submodule.Quotient.mk_eq_zero _

/-- Hausdorff separation sends the algebraic carrier class to the separated carrier class. -/
theorem higherBirthObstruction_maps_to_separated
    {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (x y z : M) :
    unseparatedCofiberToSeparated T (higherBirthObstruction T κ x y z) =
      separatedHigherBirthObstruction T κ x y z :=
  rfl

/-- The algebraic carrier obstruction retains the universal pentagon law. -/
theorem higherBirthObstruction_pentagon
    {M : Type*} [AddSemigroup M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (w x y z : M) :
    higherBirthObstruction T κ w x y +
          higherBirthObstruction T κ w (x + y) z +
          higherBirthObstruction T κ x y z =
      higherBirthObstruction T κ (w + x) y z +
        higherBirthObstruction T κ w x (y + z) := by
  have hp := congrArg (LinearMap.range T).mkQ
    (promotionAssociator_pentagon κ w x y z)
  simpa [higherBirthObstruction, map_add] using hp

/-- The Hausdorff-separated carrier obstruction retains the universal pentagon law. -/
theorem separatedHigherBirthObstruction_pentagon
    {M : Type*} [AddSemigroup M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (w x y z : M) :
    separatedHigherBirthObstruction T κ w x y +
          separatedHigherBirthObstruction T κ w (x + y) z +
          separatedHigherBirthObstruction T κ x y z =
      separatedHigherBirthObstruction T κ (w + x) y z +
        separatedHigherBirthObstruction T κ w x (y + z) := by
  have hp := congrArg (LinearMap.range T).topologicalClosure.mkQ
    (promotionAssociator_pentagon κ w x y z)
  simpa [separatedHigherBirthObstruction, map_add] using hp

/-- Every associator is exactly carried, only approximably carried, or separated from carriers. -/
theorem higherBirthCarrier_phase_trichotomy
    {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (κ : M → M → F) (x y z : M) :
    PromotionAssociator κ x y z ∈ LinearMap.range T ∨
      (PromotionAssociator κ x y z ∈
          (LinearMap.range T).topologicalClosure ∧
        PromotionAssociator κ x y z ∉ LinearMap.range T) ∨
      PromotionAssociator κ x y z ∉
        (LinearMap.range T).topologicalClosure := by
  by_cases he : PromotionAssociator κ x y z ∈ LinearMap.range T
  · exact Or.inl he
  by_cases ha : PromotionAssociator κ x y z ∈
      (LinearMap.range T).topologicalClosure
  · exact Or.inr (Or.inl ⟨ha, he⟩)
  · exact Or.inr (Or.inr ha)

/-- Closed carrier range eliminates the approximable-but-nonexact phase. -/
theorem no_mirage_of_closed_range
    {M : Type*} [Add M]
    (T : E →ₗ[𝕜] F) (hclosed : IsClosed (LinearMap.range T : Set F))
    (κ : M → M → F) (x y z : M) :
    ¬ (PromotionAssociator κ x y z ∈
        (LinearMap.range T).topologicalClosure ∧
      PromotionAssociator κ x y z ∉ LinearMap.range T) := by
  rw [hclosed.submodule_topologicalClosure_eq]
  exact fun h ↦ h.2 h.1

end Topological

/-- Integer scaling of one Hilbert vector as an additive coefficient map. -/
def integerVectorAddHom
    (a : lp (fun _ : ℕ => ℂ) 2) : ℤ →+ lp (fun _ : ℕ => ℂ) 2 where
  toFun n := (n : ℂ) • a
  map_zero' := by simp
  map_add' x y := by
    push_cast
    exact add_smul (x : ℂ) (y : ℂ) a

/-- Cubic integer compensator transported to a chosen Hilbert direction. -/
def cubicVectorCompensator
    (a : lp (fun _ : ℕ => ℂ) 2) (x y : ℤ) : lp (fun _ : ℕ => ℂ) 2 :=
  observedCompensator (integerVectorAddHom a) cubicPromotionCarry x y

/-- At the unit triple, the vector-valued cubic associator is twice its marked direction. -/
theorem cubicVectorCompensator_associator_one
    (a : lp (fun _ : ℕ => ℂ) 2) :
    PromotionAssociator (cubicVectorCompensator a) 1 1 1 =
      (2 : ℂ) • a := by
  rw [show cubicVectorCompensator a =
      observedCompensator (integerVectorAddHom a) cubicPromotionCarry from rfl,
    promotionAssociator_observed,
    cubicPromotionCarry_associator_formula]
  simp [integerVectorAddHom]

/-- A compact injective dense reporter has a nonzero algebraic carrier class erased by separation. -/
theorem exists_dense_mirage_higher_birth :
    ∃ κ : ℤ → ℤ → lp (fun _ : ℕ => ℂ) 2,
      higherBirthObstruction
          (gammaRadialReporter (1 : ℝ)).toLinearMap κ 1 1 1 ≠ 0 ∧
      separatedHigherBirthObstruction
          (gammaRadialReporter (1 : ℝ)).toLinearMap κ 1 1 1 = 0 := by
  have hcell :=
    gammaRadialReporter_compact_injective_dense_nonsurjective
      (rho := (1 : ℝ)) one_ne_zero
  have hnsurj := hcell.2.2.2
  rw [Function.Surjective] at hnsurj
  push Not at hnsurj
  obtain ⟨a, ha⟩ := hnsurj
  have htwo : (2 : ℂ) ≠ 0 := two_ne_zero
  have hnot :
      (2 : ℂ) • a ∉ LinearMap.range
        (gammaRadialReporter (1 : ℝ)).toLinearMap := by
    rintro ⟨v, hv⟩
    apply ha ((2 : ℂ)⁻¹ • v)
    calc
      gammaRadialReporter (1 : ℝ) ((2 : ℂ)⁻¹ • v) =
          (2 : ℂ)⁻¹ • gammaRadialReporter (1 : ℝ) v := by
            exact map_smul _ _ _
      _ = (2 : ℂ)⁻¹ • ((2 : ℂ) • a) := by
        rw [show gammaRadialReporter (1 : ℝ) v = (2 : ℂ) • a from hv]
      _ = a := by simp [smul_smul, htwo]
  refine ⟨cubicVectorCompensator a, ?_, ?_⟩
  · rw [ne_eq, higherBirthObstruction_eq_zero_iff_exists,
      cubicVectorCompensator_associator_one]
    push Not
    intro v hv
    exact hnot ⟨v, hv⟩
  · rw [separatedHigherBirthObstruction_eq_zero_iff_approximable,
      cubicVectorCompensator_associator_one]
    have hdense : Dense
        (LinearMap.range
          (gammaRadialReporter (1 : ℝ)).toLinearMap :
            Set (lp (fun _ : ℕ => ℂ) 2)) := by
      have hdenseSet := hcell.2.2.1
      change Dense (Set.range (gammaRadialReporter (1 : ℝ))) at hdenseSet
      have hrange :
          Set.range (gammaRadialReporter (1 : ℝ)) =
            (LinearMap.range
              (gammaRadialReporter (1 : ℝ)).toLinearMap :
                Set (lp (fun _ : ℕ => ℂ) 2)) := by
        ext u
        constructor <;> rintro ⟨v, rfl⟩ <;> exact ⟨v, rfl⟩
      rw [hrange] at hdenseSet
      exact hdenseSet
    have hclosure :
        (LinearMap.range
          (gammaRadialReporter (1 : ℝ)).toLinearMap).topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rw [hclosure]
    trivial

/-- An exact mod-two carrier with a potentially nonzero integral pentagon residual. -/
def kernelAmbiguousHigherCarrier (x y z : ℤ) : ℤ :=
  2 * x * x * y * z

/-- The ambiguous integral carrier vanishes after reduction modulo two. -/
theorem kernelAmbiguousHigherCarrier_maps_to_zero (x y z : ℤ) :
    modTwoObserver (kernelAmbiguousHigherCarrier x y z) = 0 := by
  change ((2 * x * x * y * z : ℤ) : ZMod 2) = 0
  push_cast
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
  simp

/-- The ambiguous carrier is an exact lift of the zero associator. -/
theorem kernelAmbiguousHigherCarrier_is_lift :
    IsHigherCarrierLift modTwoObserver (fun _ _ : ℤ ↦ 0)
      kernelAmbiguousHigherCarrier := by
  intro x y z
  rw [kernelAmbiguousHigherCarrier_maps_to_zero]
  simp [PromotionAssociator]

/-- Exact formula for the kernel-valued next-coherence residual. -/
theorem kernelAmbiguousHigherCarrier_residual_formula (w x y z : ℤ) :
    HigherPentagonResidual kernelAmbiguousHigherCarrier w x y z =
      -4 * w * x * y * z := by
  simp only [HigherPentagonResidual, kernelAmbiguousHigherCarrier]
  ring

/-- The exact carrier fails pentagon coherence at the unit quadruple. -/
theorem kernelAmbiguousHigherCarrier_residual_nonzero :
    HigherPentagonResidual kernelAmbiguousHigherCarrier 1 1 1 1 ≠ 0 := by
  rw [kernelAmbiguousHigherCarrier_residual_formula]
  simp only [mul_one]
  exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (by exact Nat.succ_ne_zero 3))

/-- Unconditional capstone: dense mirage birth and kernel ambiguity both occur. -/
theorem carrierBifurcationMechanism_closed :
    (∃ κ : ℤ → ℤ → lp (fun _ : ℕ => ℂ) 2,
      higherBirthObstruction
          (gammaRadialReporter (1 : ℝ)).toLinearMap κ 1 1 1 ≠ 0 ∧
      separatedHigherBirthObstruction
          (gammaRadialReporter (1 : ℝ)).toLinearMap κ 1 1 1 = 0) ∧
    IsHigherCarrierLift modTwoObserver (fun _ _ : ℤ ↦ 0)
      kernelAmbiguousHigherCarrier ∧
    HigherPentagonResidual kernelAmbiguousHigherCarrier 1 1 1 1 ≠ 0 :=
  ⟨exists_dense_mirage_higher_birth,
    kernelAmbiguousHigherCarrier_is_lift,
    kernelAmbiguousHigherCarrier_residual_nonzero⟩

end

end GaloisForLFunctions.HTGeometry
