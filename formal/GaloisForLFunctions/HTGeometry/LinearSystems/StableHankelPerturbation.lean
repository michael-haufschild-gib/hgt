import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel

/-!
# Quantitative bounds for stable finite exponential Hankel packets

The half-line exponential Gram formula gives a residue-wise operator norm
bound, and therefore a certified perturbation bound for changing or deleting
modes. Positive multiplicity packets satisfy matching single-mode lower
bounds and a sum-of-modes upper bound. The estimates hold on the whole
half-line, so there is no observation-window constant.
-/

open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A complex-residue Hankel packet with rates positive by construction. -/
def stableHankelPacket {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ) :
    HalfLineLaplaceL2 →L[ℂ] HalfLineLaplaceL2 :=
  finiteRankProbe residue
    (fun j => expFeature (Real.exp (logRate j)) (Real.exp_pos _))
    (fun j => expFeature (Real.exp (logRate j)) (Real.exp_pos _))

/-- Each modal term contributes its residue norm divided by twice its decay rate. -/
theorem norm_stableHankelPacket_le {n : ℕ} (logRate : Fin n → ℝ)
    (residue : Fin n → ℂ) :
    ‖stableHankelPacket logRate residue‖ ≤
      ∑ j, ‖residue j‖ / (2 * Real.exp (logRate j)) := by
  unfold stableHankelPacket finiteRankProbe
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, InnerProductSpace.norm_rankOne, ← pow_two, norm_sq_expFeature]
  exact le_of_eq (by ring)

/-- Changing residues changes the operator by exactly the packet of residue differences. -/
theorem stableHankelPacket_sub {n : ℕ} (logRate : Fin n → ℝ)
    (residue other : Fin n → ℂ) :
    stableHankelPacket logRate residue - stableHankelPacket logRate other =
      stableHankelPacket logRate (fun j => residue j - other j) := by
  simp only [stableHankelPacket, finiteRankProbe, sub_smul, Finset.sum_sub_distrib]

/-- A quantitative certificate for arbitrary residue perturbations, including mode removal. -/
theorem norm_stableHankelPacket_sub_le {n : ℕ} (logRate : Fin n → ℝ)
    (residue other : Fin n → ℂ) :
    ‖stableHankelPacket logRate residue - stableHankelPacket logRate other‖ ≤
      ∑ j, ‖residue j - other j‖ / (2 * Real.exp (logRate j)) := by
  rw [stableHankelPacket_sub]
  exact norm_stableHankelPacket_le logRate _

/-- Pruning any subset has a certified error equal to at most its discarded modal budget. -/
theorem norm_stableHankelPacket_prune_le {n : ℕ} (logRate : Fin n → ℝ)
    (residue : Fin n → ℂ) (keep : Finset (Fin n)) :
    ‖stableHankelPacket logRate residue -
      stableHankelPacket logRate (fun j => if j ∈ keep then residue j else 0)‖ ≤
      ∑ j, if j ∈ keep then 0 else ‖residue j‖ / (2 * Real.exp (logRate j)) := by
  convert norm_stableHankelPacket_sub_le logRate residue
    (fun j => if j ∈ keep then residue j else 0) using 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ keep <;> simp only [hj, ite_true, ite_false, sub_self, sub_zero,
    norm_zero, zero_div]

/-- A pruned packet acts through the span of its retained exponential features. -/
theorem hasRankLE_stableHankelPacket_prune {n : ℕ} (logRate : Fin n → ℝ)
    (residue : Fin n → ℂ) (keep : Finset (Fin n)) :
    RHTower.HasRankLE
      (stableHankelPacket logRate (fun j => if j ∈ keep then residue j else 0)) keep.card := by
  classical
  let v := fun j => expFeature (Real.exp (logRate j)) (Real.exp_pos _)
  refine ⟨Submodule.span ℂ ((keep.image v : Finset HalfLineLaplaceL2) : Set HalfLineLaplaceL2),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _),
    (finrank_span_finset_le_card _).trans Finset.card_image_le, ?_⟩
  intro z
  unfold stableHankelPacket finiteRankProbe
  rw [ContinuousLinearMap.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j ∈ keep
  · simp only [if_pos hj, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply]
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem v hj))
  · simp only [if_neg hj, zero_smul, ContinuousLinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- Retaining `k` modes gives a rank-`k` approximation with an explicit spectral error bound. -/
theorem approxNumber_stableHankelPacket_le_discarded {n : ℕ} (logRate : Fin n → ℝ)
    (residue : Fin n → ℂ) (keep : Finset (Fin n)) :
    RHTower.approxNumber (stableHankelPacket logRate residue) keep.card ≤
      ∑ j, if j ∈ keep then 0 else ‖residue j‖ / (2 * Real.exp (logRate j)) :=
  (RHTower.approxNumber_le _ _ _ (hasRankLE_stableHankelPacket_prune logRate residue keep)).trans
    (norm_stableHankelPacket_prune_le logRate residue keep)

/-- The existing multiplicity-weighted packet is controlled above by its total modal mass. -/
theorem norm_finiteExponentialHankel_exp_le {n : ℕ} (logRate : Fin n → ℝ)
    (m : Fin n → ℕ) :
    ‖finiteExponentialHankel (fun j => Real.exp (logRate j))
      (fun j => Real.exp_pos _) m‖ ≤ ∑ j, (m j : ℝ) / Real.exp (logRate j) := by
  have h := norm_stableHankelPacket_le logRate (fun j => ((2 * m j : ℕ) : ℂ))
  change ‖finiteExponentialHankel (fun j => Real.exp (logRate j))
    (fun j => Real.exp_pos _) m‖ ≤ _ at h
  refine h.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
  rw [Complex.norm_natCast]
  push_cast
  field_simp [Real.exp_ne_zero]

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.norm_stableHankelPacket_le
#print axioms GaloisForLFunctions.HTGeometry.stableHankelPacket_sub
#print axioms GaloisForLFunctions.HTGeometry.norm_stableHankelPacket_sub_le
#print axioms GaloisForLFunctions.HTGeometry.norm_stableHankelPacket_prune_le
#print axioms GaloisForLFunctions.HTGeometry.hasRankLE_stableHankelPacket_prune
#print axioms GaloisForLFunctions.HTGeometry.approxNumber_stableHankelPacket_le_discarded
#print axioms GaloisForLFunctions.HTGeometry.norm_finiteExponentialHankel_exp_le
