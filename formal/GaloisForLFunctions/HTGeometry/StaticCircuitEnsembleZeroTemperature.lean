import Mathlib
import GaloisForLFunctions.HTGeometry.StaticCircuitTwoMemoryOrthogonalityLaw

/-!
# Ensemble averaging and the zero-temperature replica limit of a circuit collision

Two complements to the static--circuit two-memory decomposition.

First, Bochner averaging over a Hamiltonian ensemble keeps the three-sector shape of a collision:
the universal floor is untouched, and the two memory alignments are replaced by the alignments of
the averaged memories.  On an event where some target is captured at a fixed level, the averaged
dynamical alignment is bounded below by that level times the probability of the event minus the
averaged completed baseline.

Second, a normalized finite dictionary of nonnegative scores reconstructs its maximum from its
replica collisions: the collision is squeezed between the normalizing constant times the maximal
score to the replica power and that power itself, so its `r`-th root converges to the maximum.
This is an exact zero-temperature identity at fixed dictionary, not a finite-replica estimate.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Ensemble

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Averaging a collision over an ensemble replaces each memory sector by its Bochner average and
leaves the universal floor unchanged. -/
theorem integral_twoMemory_collision
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u q : F) (cmem rmem : Ω → F)
    (hc : Integrable cmem μ) (hr : Integrable rmem μ) :
    ∫ ω, (inner ℝ u u + inner ℝ (cmem ω) q + inner ℝ (rmem ω) q) ∂μ =
      inner ℝ u u + inner ℝ (∫ ω, cmem ω ∂μ) q + inner ℝ (∫ ω, rmem ω ∂μ) q := by
  have hcI : ∫ ω, inner ℝ (cmem ω) q ∂μ = inner ℝ (∫ ω, cmem ω ∂μ) q := by
    have hswap : (fun ω => inner ℝ (cmem ω) q) = fun ω => inner ℝ q (cmem ω) := by
      funext ω; exact real_inner_comm _ _
    rw [hswap, integral_inner hc q, real_inner_comm]
  have hrI : ∫ ω, inner ℝ (rmem ω) q ∂μ = inner ℝ (∫ ω, rmem ω ∂μ) q := by
    have hswap : (fun ω => inner ℝ (rmem ω) q) = fun ω => inner ℝ q (rmem ω) := by
      funext ω; exact real_inner_comm _ _
    rw [hswap, integral_inner hr q, real_inner_comm]
  have hci : Integrable (fun ω => inner ℝ (cmem ω) q) μ := hc.inner_const q
  have hri : Integrable (fun ω => inner ℝ (rmem ω) q) μ := hr.inner_const q
  calc
    ∫ ω, (inner ℝ u u + inner ℝ (cmem ω) q + inner ℝ (rmem ω) q) ∂μ
        = (∫ ω, (inner ℝ u u + inner ℝ (cmem ω) q) ∂μ) +
            ∫ ω, inner ℝ (rmem ω) q ∂μ :=
      integral_add ((integrable_const _).add hci) hri
    _ = ((∫ _ω : Ω, inner ℝ u u ∂μ) + ∫ ω, inner ℝ (cmem ω) q ∂μ) +
            ∫ ω, inner ℝ (rmem ω) q ∂μ := by
      rw [integral_add (integrable_const _) hci]
    _ = inner ℝ u u + inner ℝ (∫ ω, cmem ω ∂μ) q + inner ℝ (∫ ω, rmem ω ∂μ) q := by
      rw [hcI, hrI, integral_const, probReal_univ, one_smul]

/-- **Ensemble realignment law.**  If some target is captured at level `level` on an event and the
complete collision stays nonnegative everywhere, then the averaged dynamical memory aligns with the
preparation memory by at least the captured mass minus the averaged completed baseline. -/
theorem integral_dynamicAlignment_ge_of_event
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : F) (rmem : Ω → F) (baseline : Ω → ℝ)
    (E : Set Ω) (hE : MeasurableSet E)
    (hr : Integrable rmem μ) (hb : Integrable baseline μ)
    {level : ℝ}
    (hEvent : ∀ ω ∈ E, level ≤ baseline ω + inner ℝ (rmem ω) q)
    (hNonneg : ∀ ω, 0 ≤ baseline ω + inner ℝ (rmem ω) q) :
    level * μ.real E - ∫ ω, baseline ω ∂μ ≤ inner ℝ (∫ ω, rmem ω ∂μ) q := by
  have hri : Integrable (fun ω => inner ℝ (rmem ω) q) μ := hr.inner_const q
  have hg : Integrable (fun ω => baseline ω + inner ℝ (rmem ω) q) μ := hb.add hri
  have hind : Integrable (E.indicator fun _ : Ω => level) μ :=
    (integrable_const level).indicator hE
  have hle : ∀ ω, E.indicator (fun _ : Ω => level) ω ≤ baseline ω + inner ℝ (rmem ω) q := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]; exact hEvent ω hω
    · rw [Set.indicator_of_notMem hω]; exact hNonneg ω
  have hmono := integral_mono hind hg hle
  have hindval : ∫ ω, E.indicator (fun _ : Ω => level) ω ∂μ = level * μ.real E := by
    rw [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_comm]
  have hsplit : ∫ ω, (baseline ω + inner ℝ (rmem ω) q) ∂μ =
      (∫ ω, baseline ω ∂μ) + inner ℝ (∫ ω, rmem ω ∂μ) q := by
    rw [integral_add hb hri]
    congr 1
    have hswap : (fun ω => inner ℝ (rmem ω) q) = fun ω => inner ℝ q (rmem ω) := by
      funext ω; exact real_inner_comm _ _
    rw [hswap, integral_inner hr q, real_inner_comm]
  rw [hindval, hsplit] at hmono
  linarith

end Ensemble

section ZeroTemperature

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Normalized replica collision of a finite dictionary of scores. -/
def finiteDictionaryReplicaCollision (f : ι → ℝ) (r : ℕ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ w, f w ^ r

/-- The complete maximum of a finite dictionary of scores. -/
def finiteDictionaryMax (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem le_finiteDictionaryMax (f : ι → ℝ) (w : ι) : f w ≤ finiteDictionaryMax f :=
  Finset.le_sup' f (Finset.mem_univ w)

theorem finiteDictionaryMax_nonneg {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) :
    0 ≤ finiteDictionaryMax f :=
  le_trans (hf (Classical.arbitrary ι)) (le_finiteDictionaryMax f _)

theorem exists_eq_finiteDictionaryMax (f : ι → ℝ) : ∃ w, f w = finiteDictionaryMax f := by
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
  exact ⟨w, hw.symm⟩

theorem finiteDictionaryReplicaCollision_nonneg {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) (r : ℕ) :
    0 ≤ finiteDictionaryReplicaCollision f r := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg ?_)
  exact fun w _ => pow_nonneg (hf w) r

/-- Upper half of the zero-temperature sandwich. -/
theorem finiteDictionaryReplicaCollision_le_pow {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) (r : ℕ) :
    finiteDictionaryReplicaCollision f r ≤ finiteDictionaryMax f ^ r := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∑ w, f w ^ r ≤ (Fintype.card ι : ℝ) * finiteDictionaryMax f ^ r := by
    calc
      ∑ w, f w ^ r ≤ ∑ _w : ι, finiteDictionaryMax f ^ r :=
        Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (hf w) (le_finiteDictionaryMax f w) r
      _ = (Fintype.card ι : ℝ) * finiteDictionaryMax f ^ r := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    finiteDictionaryReplicaCollision f r
        ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * finiteDictionaryMax f ^ r) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = finiteDictionaryMax f ^ r := by
      field_simp

/-- Lower half of the zero-temperature sandwich. -/
theorem inv_card_mul_pow_le_finiteDictionaryReplicaCollision
    {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) (r : ℕ) :
    (Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ r ≤
      finiteDictionaryReplicaCollision f r := by
  obtain ⟨w₀, hw₀⟩ := exists_eq_finiteDictionaryMax f
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    finiteDictionaryMax f ^ r = f w₀ ^ r := by rw [hw₀]
    _ ≤ ∑ w, f w ^ r :=
      Finset.single_le_sum (f := fun w => f w ^ r)
        (fun w _ => pow_nonneg (hf w) r) (Finset.mem_univ w₀)

/-- A positive constant raised to the reciprocal replica order converges to one. -/
theorem tendsto_rpow_natCast_inv_nhds_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℕ => c ^ ((r : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun r : ℕ => ((r : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have h0 : Tendsto (fun r : ℕ => Real.log c * ((r : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul (Real.log c)
  have hexp : Tendsto (fun r : ℕ => Real.exp (Real.log c * ((r : ℝ))⁻¹)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h0
  simpa [Real.rpow_def_of_pos hc] using hexp

/-- **All-replica zero-temperature reconstruction.**  The `r`-th root of the normalized replica
collision of a finite dictionary converges to the complete dictionary maximum. -/
theorem tendsto_finiteDictionaryReplicaCollision_rpow_inv
    {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) :
    Tendsto (fun r : ℕ => finiteDictionaryReplicaCollision f r ^ ((r : ℝ)⁻¹))
      atTop (𝓝 (finiteDictionaryMax f)) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hY : 0 ≤ finiteDictionaryMax f := finiteDictionaryMax_nonneg hf
  have hlow : Tendsto
      (fun r : ℕ => ((Fintype.card ι : ℝ)⁻¹) ^ ((r : ℝ)⁻¹) * finiteDictionaryMax f)
      atTop (𝓝 (finiteDictionaryMax f)) := by
    simpa using (tendsto_rpow_natCast_inv_nhds_one (c := (Fintype.card ι : ℝ)⁻¹)
      (by positivity)).mul_const (finiteDictionaryMax f)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : r ≠ 0 := by omega
    have hstep : ((Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ r) ^ ((r : ℝ)⁻¹) ≤
        finiteDictionaryReplicaCollision f r ^ ((r : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity)
        (inv_card_mul_pow_le_finiteDictionaryReplicaCollision hf r) (by positivity)
    calc
      ((Fintype.card ι : ℝ)⁻¹) ^ ((r : ℝ)⁻¹) * finiteDictionaryMax f
          = ((Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ r) ^ ((r : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.pow_rpow_inv_natCast hY hr0]
      _ ≤ finiteDictionaryReplicaCollision f r ^ ((r : ℝ)⁻¹) := hstep
  · filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : r ≠ 0 := by omega
    calc
      finiteDictionaryReplicaCollision f r ^ ((r : ℝ)⁻¹)
          ≤ (finiteDictionaryMax f ^ r) ^ ((r : ℝ)⁻¹) :=
        Real.rpow_le_rpow (finiteDictionaryReplicaCollision_nonneg hf r)
          (finiteDictionaryReplicaCollision_le_pow hf r) (by positivity)
      _ = finiteDictionaryMax f := Real.pow_rpow_inv_natCast hY hr0

end ZeroTemperature

end

end GaloisForLFunctions.HTGeometry
