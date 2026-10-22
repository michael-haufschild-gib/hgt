import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerCausalConjugation

/-!
# A global actual-source splitting with both arithmetic symmetries

The polynomial-module splitting is averaged under the original Paugam reflection
and pointwise conjugation.  The averaging preserves the common invisible kernel,
the generator, and every original finite causal source.  Idempotence follows from
the common kernel and the unchanged comparison class, not from a general claim
that averages of projections are projections.
-/

namespace RHTower
noncomputable section

local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "K" => DeningerMeyerInvisible
local notation "A" => deningerMeyerCohomologyGenerator
local notation "J" => deningerMeyerStrongLogCohomologyJ
local notation "C" => deningerMeyerCohomologyConj
local notation "P" => deningerMeyerGlobalCausalProjector

theorem deningerMeyerGlobalCausalProjector_defect (u : Q) : u - P u ∈ K := by
  apply (mem_deningerMeyerInvisible_iff _).mpr
  intro rho j
  rw [map_sub, deningerMeyerGlobalCausalProjector_jets, sub_self]

theorem deningerMeyerGlobalCausalProjector_finite (u : DeningerMeyerFiniteCausalModes) :
    P u = u := by
  obtain ⟨S, c, hc⟩ := u.property
  rw [← hc, deningerMeyerGlobalCausalProjector_synthesis]

def deningerMeyerReflectedCausalProjector : Module.End ℂ Q :=
  (1 / 2 : ℂ) • (P + (J).comp ((P).comp J))

local notation "P₁" => deningerMeyerReflectedCausalProjector

theorem deningerMeyerReflectedCausalProjector_apply (u : Q) :
    P₁ u = (1 / 2 : ℂ) • (P u + J (P (J u))) := rfl

theorem deningerMeyerReflectedCausalProjector_invisible (u : K) : P₁ u = 0 := by
  rw [deningerMeyerReflectedCausalProjector_apply,
    deningerMeyerGlobalCausalProjector_invisible u,
    deningerMeyerGlobalCausalProjector_invisible ⟨J u, deningerMeyerInvisible_J_mem u⟩,
    map_zero, add_zero, smul_zero]

theorem deningerMeyerReflectedCausalProjector_defect (u : Q) : u - P₁ u ∈ K := by
  have hJ := deningerMeyerInvisible_J_mem
    ⟨J u - P (J u), deningerMeyerGlobalCausalProjector_defect (J u)⟩
  have h := (K).smul_mem (1 / 2 : ℂ)
    ((K).add_mem (deningerMeyerGlobalCausalProjector_defect u) hJ)
  convert h using 1
  rw [deningerMeyerReflectedCausalProjector_apply, map_sub,
    deningerMeyerStrongLogCohomologyJ_sq]
  module

theorem deningerMeyerReflectedCausalProjector_generator (u : Q) :
    P₁ (A u) = A (P₁ u) := by
  simp only [deningerMeyerReflectedCausalProjector_apply, map_add, map_smul,
    deningerMeyerGlobalCausalProjector_generator, deningerMeyerCohomologyJ_generator,
    map_sub]
  module

theorem deningerMeyerReflectedCausalProjector_J (u : Q) : P₁ (J u) = J (P₁ u) := by
  simp only [deningerMeyerReflectedCausalProjector_apply, map_add, map_smul,
    deningerMeyerStrongLogCohomologyJ_sq]
  module

theorem deningerMeyerReflectedCausalProjector_finite
    (u : DeningerMeyerFiniteCausalModes) : P₁ u = u := by
  rw [deningerMeyerReflectedCausalProjector_apply,
    deningerMeyerGlobalCausalProjector_finite u,
    deningerMeyerGlobalCausalProjector_finite
      ⟨J u, deningerMeyerFiniteCausalModes_J_mem u⟩,
    deningerMeyerStrongLogCohomologyJ_sq]
  module

/-- Conjugating a complex-linear map twice gives a complex-linear map. -/
def deningerMeyerConjugatedCausalProjector : Module.End ℂ Q where
  toFun u := C (P₁ (C u))
  map_add' u v := by simp only [map_add]
  map_smul' z u := by simp [LinearMap.map_smulₛₗ]

/-- One global projector commuting with the actual generator, reflection, and conjugation. -/
def deningerMeyerArithmeticCausalProjector : Module.End ℂ Q :=
  (1 / 2 : ℂ) • (P₁ + deningerMeyerConjugatedCausalProjector)

local notation "P₂" => deningerMeyerArithmeticCausalProjector

theorem deningerMeyerArithmeticCausalProjector_apply (u : Q) :
    P₂ u = (1 / 2 : ℂ) • (P₁ u + C (P₁ (C u))) := rfl

theorem deningerMeyerArithmeticCausalProjector_invisible (u : K) : P₂ u = 0 := by
  rw [deningerMeyerArithmeticCausalProjector_apply,
    deningerMeyerReflectedCausalProjector_invisible u,
    deningerMeyerReflectedCausalProjector_invisible
      ⟨C u, deningerMeyerInvisible_conj_mem u⟩, map_zero, add_zero, smul_zero]

theorem deningerMeyerArithmeticCausalProjector_defect (u : Q) : u - P₂ u ∈ K := by
  have hC := deningerMeyerInvisible_conj_mem
    ⟨C u - P₁ (C u), deningerMeyerReflectedCausalProjector_defect (C u)⟩
  have h := (K).smul_mem (1 / 2 : ℂ)
    ((K).add_mem (deningerMeyerReflectedCausalProjector_defect u) hC)
  convert h using 1
  rw [deningerMeyerArithmeticCausalProjector_apply, map_sub,
    deningerMeyerCohomologyConj_sq]
  module

theorem deningerMeyerArithmeticCausalProjector_generator (u : Q) :
    P₂ (A u) = A (P₂ u) := by
  simp only [deningerMeyerArithmeticCausalProjector_apply, map_add, map_smul,
    ← deningerMeyerCohomologyGenerator_conj, deningerMeyerReflectedCausalProjector_generator]

theorem deningerMeyerArithmeticCausalProjector_J (u : Q) : P₂ (J u) = J (P₂ u) := by
  simp only [deningerMeyerArithmeticCausalProjector_apply, map_add, map_smul,
    deningerMeyerCohomologyConj_J, deningerMeyerReflectedCausalProjector_J]

theorem deningerMeyerArithmeticCausalProjector_conj (u : Q) : P₂ (C u) = C (P₂ u) := by
  simp [deningerMeyerArithmeticCausalProjector_apply, LinearMap.map_smulₛₗ, map_ofNat]
  module

theorem deningerMeyerArithmeticCausalProjector_finite
    (u : DeningerMeyerFiniteCausalModes) : P₂ u = u := by
  rw [deningerMeyerArithmeticCausalProjector_apply,
    deningerMeyerReflectedCausalProjector_finite u,
    deningerMeyerReflectedCausalProjector_finite
      ⟨C u, deningerMeyerFiniteCausalModes_conj_mem u⟩,
    deningerMeyerCohomologyConj_sq]
  module

@[simp]
theorem deningerMeyerArithmeticCausalProjector_idempotent (u : Q) :
    P₂ (P₂ u) = P₂ u := by
  have h := deningerMeyerArithmeticCausalProjector_invisible
    ⟨u - P₂ u, deningerMeyerArithmeticCausalProjector_defect u⟩
  change P₂ (u - P₂ u) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem deningerMeyerArithmeticCausalProjector_ker : LinearMap.ker P₂ = K := by
  ext u
  change P₂ u = 0 ↔ u ∈ K
  constructor
  · intro h
    simpa only [h, sub_zero] using deningerMeyerArithmeticCausalProjector_defect u
  · intro h
    exact deningerMeyerArithmeticCausalProjector_invisible ⟨u, h⟩

theorem deningerMeyerArithmeticCausalProjector_comparison (u : Q) :
    deningerMeyerCompactOpenXiComparison (P₂ u) = deningerMeyerCompactOpenXiComparison u := by
  have h := deningerMeyerArithmeticCausalProjector_defect u
  change deningerMeyerCompactOpenXiComparison (u - P₂ u) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem deningerMeyerArithmeticCausalProjector_jets (u : Q) (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (P₂ u) =
      deningerMeyerXiSupportJetEvaluationLM rho j u := by
  have h := (mem_deningerMeyerInvisible_iff _).mp
    (deningerMeyerArithmeticCausalProjector_defect u) rho j
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem deningerMeyerArithmeticCausalProjector_absorb_old (u : Q) : P₂ (P u) = P₂ u := by
  have h := deningerMeyerArithmeticCausalProjector_invisible
    ⟨u - P u, deningerMeyerGlobalCausalProjector_defect u⟩
  change P₂ (u - P u) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem deningerMeyerGlobalCausalProjector_absorb_arithmetic (u : Q) : P (P₂ u) = P u := by
  have h := deningerMeyerGlobalCausalProjector_invisible
    ⟨u - P₂ u, deningerMeyerArithmeticCausalProjector_defect u⟩
  change P (u - P₂ u) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

end
end RHTower
