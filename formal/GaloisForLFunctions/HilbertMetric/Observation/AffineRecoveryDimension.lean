import GaloisForLFunctions.HilbertMetric.Observation.JointCommutantRecovery
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Sharp finite-dimensional bounds for observation recovery

Anchoring each observation at one coordinate removes the constant mode.
A basis selected from the remaining observation vectors recovers every
label. Thus `n+1` coordinates require at most `n` observations. Coordinate
indicator observations attain the bound. This supplies an affine-linear
realization of the finite recovery mechanism in arXiv:2610.33092.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation
open Set Submodule
noncomputable section

/-- Observation values after removing the common reference coordinate. -/
def anchoredObservation {m n : ℕ} (E : Fin m → Fin (n + 1) → ℂ)
    (b : Fin m) : Fin n → ℂ := fun j => E b j.succ - E b 0

private def anchoredRead {n : ℕ} (i : Fin (n + 1)) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  Fin.cases 0 (fun j => LinearMap.proj j) i

private theorem anchoredRead_observation {m n : ℕ} (E : Fin m → Fin (n + 1) → ℂ)
    (b : Fin m) (i : Fin (n + 1)) :
    anchoredRead i (anchoredObservation E b) = E b i - E b 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [anchoredRead]
  · rfl

/-- A spanning set of anchored observations supplies every recovery implication. -/
private theorem determines_of_anchored_span {m n : ℕ} (E : Fin m → Fin (n + 1) → ℂ)
    (S : Finset (Fin m))
    (hspan : Submodule.span ℂ (anchoredObservation E '' (S : Set (Fin m))) =
      Submodule.span ℂ (Set.range (anchoredObservation E))) :
    determinedLabels E (S : Set (Fin m)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b i j hij
  let L := anchoredRead i - anchoredRead j
  have hsub : Submodule.span ℂ (anchoredObservation E '' (S : Set (Fin m))) ≤
      LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change anchoredRead i (anchoredObservation E a) -
      anchoredRead j (anchoredObservation E a) = 0
    rw [anchoredRead_observation, anchoredRead_observation, hij a ha, sub_self]
  have hb : anchoredObservation E b ∈ LinearMap.ker L := by
    apply hsub
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self b)
  change anchoredRead i (anchoredObservation E b) -
    anchoredRead j (anchoredObservation E b) = 0 at hb
  rw [anchoredRead_observation, anchoredRead_observation] at hb
  linear_combination hb

/-- At most `n` observations recover every label on `n+1` coordinates. -/
theorem exists_small_recovering_family {m n : ℕ} (E : Fin m → Fin (n + 1) → ℂ) :
    ∃ S : Finset (Fin m), S.card ≤ n ∧
      Submodule.span ℂ (anchoredObservation E '' (S : Set (Fin m))) =
        Submodule.span ℂ (Set.range (anchoredObservation E)) ∧
      determinedLabels E (S : Set (Fin m)) = Set.univ := by
  classical
  let V := Submodule.span ℂ (Set.range (anchoredObservation E))
  obtain ⟨f, hf, hspan, hind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range (anchoredObservation E))
  choose label hlabel using hf
  let S := Finset.univ.image label
  have hs : anchoredObservation E '' (S : Set (Fin m)) = Set.range f := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨k, (hlabel k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨label k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, hlabel k⟩
  have hSspan : Submodule.span ℂ (anchoredObservation E '' (S : Set (Fin m))) = V := by
    rw [hs]
    exact hspan
  refine ⟨S, ?_, hSspan, determines_of_anchored_span E S hSspan⟩
  calc
    S.card ≤ Fintype.card (Fin (Module.finrank ℂ V)) := Finset.card_image_le
    _ = Module.finrank ℂ V := Fintype.card_fin _
    _ ≤ Module.finrank ℂ (Fin n → ℂ) := Submodule.finrank_le V
    _ = n := by simp

/-- Individual non-reference coordinates give a family requiring the whole bound. -/
def coordinateObservation (n : ℕ) (b : Fin n) (i : Fin (n + 1)) : ℂ :=
  if i = b.succ then 1 else 0

private theorem zero_ne_succ {n : ℕ} (a : Fin n) : (0 : Fin (n + 1)) ≠ a.succ := by
  intro he
  have hv := congrArg Fin.val he
  change 0 = a.val + 1 at hv
  omega

/-- No coordinate indicator can be recovered from any collection omitting it. -/
theorem coordinateObservation_closure (n : ℕ) (S : Set (Fin n)) :
    determinedLabels (coordinateObservation n) S = S := by
  classical
  apply Set.Subset.antisymm ?_ (subset_determinedLabels _ _)
  intro b hb
  by_contra hnot
  have he := hb 0 b.succ (fun a ha => ?_)
  · simpa [coordinateObservation, zero_ne_succ] using he
  · have hab : b ≠ a := by intro h; subst a; exact hnot ha
    simp [coordinateObservation, zero_ne_succ, Fin.succ_inj, hab]

/-- The `n`-observation upper bound is attained for every dimension. -/
theorem coordinateObservation_recovery_card (n : ℕ) (S : Finset (Fin n)) :
    determinedLabels (coordinateObservation n) (S : Set (Fin n)) = Set.univ ↔ S.card = n := by
  rw [coordinateObservation_closure]
  constructor
  · intro h
    have he : S = Finset.univ := by ext b; simpa using Set.ext_iff.mp h b
    rw [he, Finset.card_univ, Fintype.card_fin]
  · intro h
    have he : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using h)
    simp only [he, Finset.coe_univ]

#print axioms exists_small_recovering_family
#print axioms coordinateObservation_closure
#print axioms coordinateObservation_recovery_card
end
end GaloisForLFunctions.HilbertMetric.Observation
