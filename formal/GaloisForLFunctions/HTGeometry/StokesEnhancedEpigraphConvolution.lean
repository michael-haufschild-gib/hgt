import Mathlib

/-!
# Exponential epigraph support calculus

Support-level algebra for exponential objects in enhanced irregular Riemann--Hilbert theory.
This file does not claim a construction of enhanced sheaves or their derived convolution.
-/

namespace GaloisForLFunctions.IrregularStokes.EnhancedEpigraph

variable {X : Type*}

/-- Closed exponential epigraph attached to a real phase. -/
def exponentialEpigraph (φ : X → ℝ) : Set (X × ℝ) :=
  {p | 0 ≤ p.2 + φ p.1}

/-- Exponential epigraph restricted to a base domain. -/
def exponentialEpigraphOn (U : Set X) (φ : X → ℝ) : Set (X × ℝ) :=
  {p | p.1 ∈ U ∧ 0 ≤ p.2 + φ p.1}

/-- Fiberwise additive convolution of supports in the enhanced real variable. -/
def fiberwiseAdditiveConvolution (A B : Set (X × ℝ)) : Set (X × ℝ) :=
  {p | ∃ u v : ℝ, (p.1, u) ∈ A ∧ (p.1, v) ∈ B ∧ u + v = p.2}

@[simp]
theorem mem_exponentialEpigraph {φ : X → ℝ} {p : X × ℝ} :
    p ∈ exponentialEpigraph φ ↔ 0 ≤ p.2 + φ p.1 :=
  Iff.rfl

@[simp]
theorem mem_exponentialEpigraphOn {U : Set X} {φ : X → ℝ} {p : X × ℝ} :
    p ∈ exponentialEpigraphOn U φ ↔ p.1 ∈ U ∧ 0 ≤ p.2 + φ p.1 :=
  Iff.rfl

@[simp]
theorem mem_fiberwiseAdditiveConvolution {A B : Set (X × ℝ)} {p : X × ℝ} :
    p ∈ fiberwiseAdditiveConvolution A B ↔
      ∃ u v : ℝ, (p.1, u) ∈ A ∧ (p.1, v) ∈ B ∧ u + v = p.2 :=
  Iff.rfl

/-- Support of the zero section in the enhanced real variable. -/
def zeroSectionSupport : Set (X × ℝ) :=
  {p | p.2 = 0}

/-- Fiberwise additive convolution is commutative. -/
theorem fiberwiseAdditiveConvolution_comm (A B : Set (X × ℝ)) :
    fiberwiseAdditiveConvolution A B = fiberwiseAdditiveConvolution B A := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨v, u, hv, hu, by simpa [add_comm] using huv⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨v, u, hv, hu, by simpa [add_comm] using huv⟩

/-- Fiberwise additive convolution is associative. -/
theorem fiberwiseAdditiveConvolution_assoc (A B C : Set (X × ℝ)) :
    fiberwiseAdditiveConvolution (fiberwiseAdditiveConvolution A B) C =
      fiberwiseAdditiveConvolution A (fiberwiseAdditiveConvolution B C) := by
  ext p
  constructor
  · rintro ⟨uv, w, ⟨u, v, hu, hv, huv⟩, hw, huvw⟩
    refine ⟨u, v + w, hu, ⟨v, w, hv, hw, rfl⟩, ?_⟩
    calc
      u + (v + w) = (u + v) + w := (add_assoc u v w).symm
      _ = uv + w := by rw [huv]
      _ = p.2 := huvw
  · rintro ⟨u, vw, hu, ⟨v, w, hv, hw, hvw⟩, huvw⟩
    refine ⟨u + v, w, ⟨u, v, hu, hv, rfl⟩, hw, ?_⟩
    calc
      (u + v) + w = u + (v + w) := add_assoc u v w
      _ = u + vw := by rw [hvw]
      _ = p.2 := huvw

/-- Zero-section support is a left unit for fiberwise additive convolution. -/
theorem fiberwiseAdditiveConvolution_zeroSection_left (A : Set (X × ℝ)) :
    fiberwiseAdditiveConvolution (zeroSectionSupport : Set (X × ℝ)) A = A := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    change u = 0 at hu
    have hvp : v = p.2 := by simpa [hu] using huv
    simpa [hvp] using hv
  · intro hp
    exact ⟨0, p.2, rfl, hp, zero_add p.2⟩

/-- Zero-section support is a right unit for fiberwise additive convolution. -/
theorem fiberwiseAdditiveConvolution_zeroSection_right (A : Set (X × ℝ)) :
    fiberwiseAdditiveConvolution A (zeroSectionSupport : Set (X × ℝ)) = A := by
  rw [fiberwiseAdditiveConvolution_comm]
  exact fiberwiseAdditiveConvolution_zeroSection_left A

/-- Fiberwise convolution intersects base domains and adds phases exactly. -/
theorem fiberwiseAdditiveConvolution_exponentialEpigraphOn
    (U V : Set X) (φ ψ : X → ℝ) :
    fiberwiseAdditiveConvolution (exponentialEpigraphOn U φ) (exponentialEpigraphOn V ψ) =
      exponentialEpigraphOn (U ∩ V) (fun x => φ x + ψ x) := by
  ext p
  constructor
  · rintro ⟨u, v, ⟨huU, hu⟩, ⟨hvV, hv⟩, huv⟩
    refine ⟨⟨huU, hvV⟩, ?_⟩
    rw [← huv]
    linarith
  · rintro ⟨⟨hpU, hpV⟩, h⟩
    refine ⟨-φ p.1, p.2 + φ p.1, ⟨hpU, ?_⟩, ⟨hpV, ?_⟩, ?_⟩
    · simp
    · simpa [add_assoc] using h
    · ring

/-- Fiberwise additive convolution of exponential epigraphs adds their phases exactly. -/
theorem fiberwiseAdditiveConvolution_exponentialEpigraph (φ ψ : X → ℝ) :
    fiberwiseAdditiveConvolution (exponentialEpigraph φ) (exponentialEpigraph ψ) =
      exponentialEpigraph (fun x => φ x + ψ x) := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    change 0 ≤ p.2 + (φ p.1 + ψ p.1)
    change 0 ≤ u + φ p.1 at hu
    change 0 ≤ v + ψ p.1 at hv
    rw [← huv]
    linarith
  · intro h
    change 0 ≤ p.2 + (φ p.1 + ψ p.1) at h
    refine ⟨-φ p.1, p.2 + φ p.1, ?_, ?_, ?_⟩
    · change 0 ≤ -φ p.1 + φ p.1
      simp
    · change 0 ≤ (p.2 + φ p.1) + ψ p.1
      simpa [add_assoc] using h
    · ring

/-- The zero-phase exponential epigraph is idempotent under fiberwise convolution. -/
theorem fiberwiseAdditiveConvolution_zeroPhase_idempotent :
    fiberwiseAdditiveConvolution
        (exponentialEpigraph (fun _ : X => 0))
        (exponentialEpigraph (fun _ : X => 0)) =
      exponentialEpigraph (fun _ : X => 0) := by
  simpa using fiberwiseAdditiveConvolution_exponentialEpigraph
    (fun _ : X => 0) (fun _ : X => 0)

/-- Inclusion of exponential epigraph supports is exactly pointwise phase order. -/
theorem exponentialEpigraph_subset_iff (φ ψ : X → ℝ) :
    exponentialEpigraph φ ⊆ exponentialEpigraph ψ ↔ φ ≤ ψ := by
  constructor
  · intro h x
    have hx : (x, -φ x) ∈ exponentialEpigraph φ := by
      simp [exponentialEpigraph]
    have := h hx
    change 0 ≤ -φ x + ψ x at this
    linarith
  · intro h p hp
    change 0 ≤ p.2 + φ p.1 at hp
    change 0 ≤ p.2 + ψ p.1
    linarith [h p.1]

/-- Exponential epigraph support retains the complete real phase. -/
theorem exponentialEpigraph_injective :
    Function.Injective (exponentialEpigraph : (X → ℝ) → Set (X × ℝ)) := by
  intro φ ψ h
  apply le_antisymm
  · exact (exponentialEpigraph_subset_iff φ ψ).mp (h.le)
  · exact (exponentialEpigraph_subset_iff ψ φ).mp (h.ge)

/-- Phases embed order-reflectingly into exponential epigraph supports. -/
def exponentialEpigraphOrderEmbedding : (X → ℝ) ↪o Set (X × ℝ) where
  toFun := exponentialEpigraph
  inj' := exponentialEpigraph_injective
  map_rel_iff' := by
    intro φ ψ
    exact exponentialEpigraph_subset_iff φ ψ

section Topology

variable [TopologicalSpace X]

/-- A continuous phase has closed exponential epigraph support. -/
theorem isClosed_exponentialEpigraph {φ : X → ℝ} (hφ : Continuous φ) :
    IsClosed (exponentialEpigraph φ) := by
  have hF : Continuous (fun p : X × ℝ => p.2 + φ p.1) :=
    continuous_snd.add (hφ.comp continuous_fst)
  change IsClosed ((fun p : X × ℝ => p.2 + φ p.1) ⁻¹' Set.Ici 0)
  exact isClosed_Ici.preimage hF

/-- Restricting a continuous exponential epigraph to an open base domain is locally closed. -/
theorem isLocallyClosed_exponentialEpigraphOn {U : Set X} (hU : IsOpen U)
    {φ : X → ℝ} (hφ : Continuous φ) :
    IsLocallyClosed (exponentialEpigraphOn U φ) := by
  change IsLocallyClosed ((Prod.fst ⁻¹' U) ∩ exponentialEpigraph φ)
  exact (hU.preimage continuous_fst).isLocallyClosed.inter
    (isClosed_exponentialEpigraph hφ).isLocallyClosed

end Topology

end GaloisForLFunctions.IrregularStokes.EnhancedEpigraph
