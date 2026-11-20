import GaloisForLFunctions.HTGeometry.Thermofield.InverseTimeSpectralSplit
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineOscillation

/-!
# Quantitative resolution of the thermofield crossover

The residual consists of the coarse replica collisions separated by the fine
spectrum. Its envelope is the inverse-window bound given by their inverse
gaps. When any collision separates, the rescaled residual visits both signs
arbitrarily late by simultaneous phase recurrence.
-/

open Filter Topology
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry.Thermofield

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

private abbrev ReplicaPair (α : Type*) := (α → ℕ) × (α → ℕ)

omit [DecidableEq α] [Nonempty α] in
private def replicaGap (E : α → ℝ) (pq : ReplicaPair α) : ℝ :=
  replicaMultiplicityEnergy E pq.1 - replicaMultiplicityEnergy E pq.2

/-- Replica pairs that collide at the coarse scale and split at the fine scale. -/
def splitReplicaPairs (E F : α → ℝ) (n : ℕ) : Finset (ReplicaPair α) :=
  (Finset.univ.piAntidiag n ×ˢ Finset.univ.piAntidiag n).filter
    fun pq => replicaGap E pq = 0 ∧ replicaGap F pq ≠ 0

omit [Nonempty α] in
theorem splitReplicaPairs_nonempty_iff (E F : α → ℝ) (n : ℕ) :
    (splitReplicaPairs E F n).Nonempty ↔
      ∃ p ∈ Finset.univ.piAntidiag n, ∃ q ∈ Finset.univ.piAntidiag n,
        replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q ∧
        replicaMultiplicityEnergy F p ≠ replicaMultiplicityEnergy F q := by
  constructor
  · rintro ⟨⟨p, q⟩, hpq⟩
    rcases Finset.mem_filter.mp hpq with ⟨hpq, hE, hF⟩
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    exact ⟨p, hp, q, hq, sub_eq_zero.mp hE, sub_ne_zero.mp hF⟩
  · rintro ⟨p, hp, q, hq, hE, hF⟩
    exact ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩,
      sub_eq_zero.mpr hE, sub_ne_zero.mpr hF⟩⟩

private def pairWeight (β : ℝ) (E : α → ℝ) (pq : ReplicaPair α) : ℝ :=
  fidelityReplicaMultiplicityWeight (finiteGibbsStateWeight β E) pq.1 pq.2

omit [DecidableEq α] in
private theorem pairWeight_pos (β : ℝ) (E : α → ℝ) (pq : ReplicaPair α) :
    0 < pairWeight β E pq :=
  fidelityReplicaMultiplicityWeight_pos (finiteGibbsStateWeight_pos β E) pq.1 pq.2

/-- The Gibbs weight of each separated collision divided by its absolute fine gap. -/
def splitReplicaInverseGapMass (β : ℝ) (E F : α → ℝ) (n : ℕ) : ℝ :=
  ∑ pq ∈ splitReplicaPairs E F n, pairWeight β E pq / |replicaGap F pq|

private def splitReplicaSineSum (β : ℝ) (E F : α → ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  ∑ pq ∈ splitReplicaPairs E F n,
    (pairWeight β E pq / replicaGap F pq) * Real.sin (τ * replicaGap F pq)

omit [Nonempty α] in
/-- Only the separated pairs appear in the residual relative to the joint plateau. -/
theorem thermalReplicaCrossover_sub_joint_eq (β : ℝ) (E F : α → ℝ) (n : ℕ) (τ : ℝ) :
    thermalReplicaCrossover β E F n τ - (jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n : ℂ) =
      ((∑ pq ∈ splitReplicaPairs E F n, pairWeight β E pq * Real.sinc (τ * replicaGap F pq) : ℝ) : ℂ) := by
  simp only [thermalReplicaCrossover, jointReplicaCollisionMass, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, ← Finset.sum_sub_distrib, splitReplicaPairs, Finset.sum_filter,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hE : replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q <;>
    by_cases hF : replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q <;>
    simp [hE, hF, replicaGap, pairWeight, sub_eq_zero]

omit [Nonempty α] in
private theorem thermalReplicaCrossover_scaled_re (β : ℝ) (E F : α → ℝ) (n : ℕ) (τ : ℝ) :
    τ * ((thermalReplicaCrossover β E F n τ).re -
      jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n) =
        splitReplicaSineSum β E F n τ := by
  have h := congrArg Complex.re (thermalReplicaCrossover_sub_joint_eq β E F n τ)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  rw [h, Finset.mul_sum, splitReplicaSineSum]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hgap : replicaGap F pq ≠ 0 := (Finset.mem_filter.mp hpq).2.2
  by_cases hτ : τ = 0
  · simp [hτ]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hτ hgap)]
    field_simp

/-- The joint plateau has an explicit inverse-window error envelope. -/
theorem thermalReplicaCrossover_scaled_norm_le (β : ℝ) (E F : α → ℝ) (n : ℕ) (τ : ℝ) :
    |τ| * ‖thermalReplicaCrossover β E F n τ -
      (jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n : ℂ)‖ ≤
        splitReplicaInverseGapMass β E F n := by
  have h := thermalReplicaCrossover_scaled_re β E F n τ
  have hre := congrArg Complex.re (thermalReplicaCrossover_sub_joint_eq β E F n τ)
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  rw [hre] at h
  rw [thermalReplicaCrossover_sub_joint_eq, Complex.norm_real, Real.norm_eq_abs, ← abs_mul, h]
  unfold splitReplicaSineSum splitReplicaInverseGapMass
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun pq _ => ?_)
  have hw := (pairWeight_pos β E pq).le
  rw [abs_mul, abs_div, abs_of_nonneg hw]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (div_nonneg hw (abs_nonneg _))

omit [Nonempty α] in
private theorem hasDerivAt_splitReplicaSineSum_zero (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    HasDerivAt (splitReplicaSineSum β E F n)
      (∑ pq ∈ splitReplicaPairs E F n, pairWeight β E pq) 0 := by
  unfold splitReplicaSineSum
  refine HasDerivAt.fun_sum fun pq hpq => ?_
  have hgap : replicaGap F pq ≠ 0 := (Finset.mem_filter.mp hpq).2.2
  have hs := (hasDerivAt_mul_const (x := (0 : ℝ)) (replicaGap F pq)).sin
  simpa only [zero_mul, Real.cos_zero, one_mul, div_mul_cancel₀ _ hgap] using
    hs.const_mul (pairWeight β E pq / replicaGap F pq)

omit [Nonempty α] in
/-- The initial slope of the rescaled residual equals the mass lost at the
punctured affine plateau. -/
theorem hasDerivAt_thermalReplicaCrossover_scaled_zero (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    HasDerivAt (fun τ => τ * ((thermalReplicaCrossover β E F n τ).re -
      jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n))
      (fidelityReplicaCollisionMass (finiteGibbsStateWeight β E) E n -
        jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n) 0 := by
  have hmass : fidelityReplicaCollisionMass (finiteGibbsStateWeight β E) E n -
      jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n =
        ∑ pq ∈ splitReplicaPairs E F n, pairWeight β E pq := by
    rw [collisionMass_sub_jointReplicaCollisionMass]
    simp only [splitReplicaPairs, Finset.sum_filter, Finset.sum_product, replicaGap,
      pairWeight, sub_eq_zero, sub_ne_zero]
  simpa only [thermalReplicaCrossover_scaled_re, hmass] using
    hasDerivAt_splitReplicaSineSum_zero β E F n

omit [Nonempty α] in
private theorem splitReplicaSineSum_neg (β : ℝ) (E F : α → ℝ) (n : ℕ) (τ : ℝ) :
    splitReplicaSineSum β E F n (-τ) = -splitReplicaSineSum β E F n τ := by
  simp only [splitReplicaSineSum, neg_mul, Real.sin_neg, mul_neg, Finset.sum_neg_distrib]

/-- If any coarse collision separates, the crossover has both signs of
error at arbitrarily large windows, with amplitudes of order inverse window. -/
theorem splitReplicaPairs_nonempty_iff_crossover_excursions (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    (splitReplicaPairs E F n).Nonempty ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, ∃ tPlus tMinus : ℝ,
        max A 0 < tPlus ∧ max A 0 < tMinus ∧
        δ < tPlus * ((thermalReplicaCrossover β E F n tPlus).re -
          jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n) ∧
        tMinus * ((thermalReplicaCrossover β E F n tMinus).re -
          jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n) < -δ := by
  simp only [thermalReplicaCrossover_scaled_re]
  constructor
  · intro hsplit
    let P := splitReplicaSineSum β E F n
    have hmass : 0 < ∑ pq ∈ splitReplicaPairs E F n, pairWeight β E pq :=
      Finset.sum_pos (fun pq _ => pairWeight_pos β E pq) hsplit
    have hPzero : P 0 = 0 := by simp [P, splitReplicaSineSum]
    have hslope := (hasDerivAt_splitReplicaSineSum_zero β E F n).tendsto_slope_zero_right
    have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s⁻¹ * P s := by
      have h := (tendsto_order.mp hslope).1 0 hmass
      change ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s⁻¹ • (P (0 + s) - P 0) at h
      simpa only [zero_add, hPzero, sub_zero, smul_eq_mul] using h
    have hstrict : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    obtain ⟨s, hspos, hPs⟩ := (hstrict.and hpos).exists
    have hvalue : 0 < P s := pos_of_mul_pos_right hPs (inv_nonneg.mpr hspos.le)
    let δ := P s / 2
    have hδ : 0 < δ := half_pos hvalue
    have hδpos : δ < P s := half_lt_self hvalue
    have hδneg : P (-s) < -δ := by
      change splitReplicaSineSum β E F n (-s) < -δ
      rw [splitReplicaSineSum_neg]
      exact neg_lt_neg hδpos
    let ι := {pq // pq ∈ splitReplicaPairs E F n}
    obtain ⟨clocks, _, hclocks, hc, hsin⟩ :=
      RHTower.exists_liClockPhaseRecurrence (fun pq : ι => replicaGap F pq.1)
    have hprofile (u : ℝ) : Tendsto (fun k => P (clocks k + u)) atTop (𝓝 (P u)) := by
      dsimp only [P, splitReplicaSineSum]
      refine tendsto_finsetSum _ fun pq hpq => ?_
      have hs := (RHTower.tendsto_cos_sin_shift_of_recurrence (hc ⟨pq, hpq⟩) (hsin ⟨pq, hpq⟩) u).2
      exact hs.const_mul (pairWeight β E pq / replicaGap F pq)
    refine ⟨δ, hδ, fun A => ?_⟩
    have hlate (u : ℝ) : ∀ᶠ k : ℕ in atTop, max A 0 < clocks k + u :=
      (tendsto_atTop_add_const_right atTop u hclocks).eventually_gt_atTop _
    obtain ⟨k, hk, hPk⟩ := ((hlate s).and ((tendsto_order.mp (hprofile s)).1 δ hδpos)).exists
    obtain ⟨l, hl, hPl⟩ := ((hlate (-s)).and ((tendsto_order.mp (hprofile (-s))).2 (-δ) hδneg)).exists
    exact ⟨clocks k + s, clocks l + (-s), hk, hl, hPk, hPl⟩
  · rintro ⟨δ, hδ, h⟩
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨tPlus, _, _, _, ht, _⟩ := h 0
    simp only [splitReplicaSineSum, he, Finset.sum_empty] at ht
    exact (not_lt_of_ge hδ.le) ht

#print axioms thermalReplicaCrossover_sub_joint_eq
#print axioms thermalReplicaCrossover_scaled_norm_le
#print axioms hasDerivAt_thermalReplicaCrossover_scaled_zero
#print axioms splitReplicaPairs_nonempty_iff_crossover_excursions

end

end GaloisForLFunctions.HTGeometry.Thermofield
