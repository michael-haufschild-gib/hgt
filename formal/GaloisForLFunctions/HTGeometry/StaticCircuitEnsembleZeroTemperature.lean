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

section PositiveLinearization

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The normalized `p`-norm of a finite dictionary of scores. -/
noncomputable def finiteDictionaryLpNorm (f : ι → ℝ) (p : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ)⁻¹ * ∑ w, f w ^ p) ^ p⁻¹

/-- Upper half of the positive-linearization sandwich. -/
theorem finiteDictionaryLpNorm_le {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) {p : ℝ} (hp : 0 < p) :
    finiteDictionaryLpNorm f p ≤ finiteDictionaryMax f := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmax : 0 ≤ finiteDictionaryMax f := finiteDictionaryMax_nonneg hf
  have hsum : ∑ w, f w ^ p ≤ (Fintype.card ι : ℝ) * finiteDictionaryMax f ^ p := by
    calc ∑ w, f w ^ p ≤ ∑ _w : ι, finiteDictionaryMax f ^ p :=
          Finset.sum_le_sum fun w _ =>
            Real.rpow_le_rpow (hf w) (le_finiteDictionaryMax f w) hp.le
      _ = (Fintype.card ι : ℝ) * finiteDictionaryMax f ^ p := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hstep : (Fintype.card ι : ℝ)⁻¹ * ∑ w, f w ^ p ≤ finiteDictionaryMax f ^ p := by
    calc (Fintype.card ι : ℝ)⁻¹ * ∑ w, f w ^ p
        ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * finiteDictionaryMax f ^ p) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = finiteDictionaryMax f ^ p := by
          rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]
  have hnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ w, f w ^ p := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => ?_)
    exact Real.rpow_nonneg (hf w) p
  calc finiteDictionaryLpNorm f p ≤ (finiteDictionaryMax f ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow hnn hstep (by positivity)
    _ = finiteDictionaryMax f := Real.rpow_rpow_inv hmax hp.ne'

/-- Lower half of the positive-linearization sandwich. -/
theorem le_finiteDictionaryLpNorm {f : ι → ℝ} (hf : ∀ w, 0 ≤ f w) {p : ℝ} (hp : 0 < p) :
    (Fintype.card ι : ℝ) ^ (-p⁻¹) * finiteDictionaryMax f ≤ finiteDictionaryLpNorm f p := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmax : 0 ≤ finiteDictionaryMax f := finiteDictionaryMax_nonneg hf
  obtain ⟨w₀, hw₀⟩ := exists_eq_finiteDictionaryMax f
  have hsingle : finiteDictionaryMax f ^ p ≤ ∑ w, f w ^ p := by
    calc finiteDictionaryMax f ^ p = f w₀ ^ p := by rw [hw₀]
      _ ≤ ∑ w, f w ^ p :=
        Finset.single_le_sum (f := fun w => f w ^ p)
          (fun w _ => Real.rpow_nonneg (hf w) p) (Finset.mem_univ w₀)
  have hstep : (Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ p ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ w, f w ^ p :=
    mul_le_mul_of_nonneg_left hsingle (by positivity)
  have hnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ p := by
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hmax p)
  have hsplit : ((Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ p) ^ p⁻¹ =
      (Fintype.card ι : ℝ) ^ (-p⁻¹) * finiteDictionaryMax f := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hmax p),
      Real.rpow_rpow_inv hmax hp.ne', ← Real.rpow_neg_one ((Fintype.card ι : ℝ)),
      ← Real.rpow_mul hcard.le, neg_one_mul]
  calc (Fintype.card ι : ℝ) ^ (-p⁻¹) * finiteDictionaryMax f
      = ((Fintype.card ι : ℝ)⁻¹ * finiteDictionaryMax f ^ p) ^ p⁻¹ := hsplit.symm
    _ ≤ finiteDictionaryLpNorm f p := Real.rpow_le_rpow hnn hstep (by positivity)

/-- The one-hot dictionary saturates the lower constant of the sandwich. -/
theorem finiteDictionaryLpNorm_oneHot [DecidableEq ι] (w₀ : ι) {p : ℝ} (hp : 0 < p) :
    finiteDictionaryLpNorm (fun w => if w = w₀ then (1 : ℝ) else 0) p =
        (Fintype.card ι : ℝ) ^ (-p⁻¹) ∧
      finiteDictionaryMax (fun w => if w = w₀ then (1 : ℝ) else 0) = 1 := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ w : ι, (if w = w₀ then (1 : ℝ) else 0) ^ p = if w = w₀ then (1 : ℝ) else 0 := by
    intro w
    by_cases hw : w = w₀
    · rw [if_pos hw]
      exact Real.one_rpow p
    · rw [if_neg hw]
      exact Real.zero_rpow hp.ne'
  have hsum : ∑ w : ι, (if w = w₀ then (1 : ℝ) else 0) ^ p = 1 := by
    rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_ite_eq' Finset.univ w₀
      (fun _ => (1 : ℝ)), if_pos (Finset.mem_univ w₀)]
  constructor
  · rw [finiteDictionaryLpNorm, hsum, mul_one, ← Real.rpow_neg_one ((Fintype.card ι : ℝ)),
      ← Real.rpow_mul hcard.le, neg_one_mul]
  · refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ fun w _ => ?_
      by_cases hw : w = w₀
      · rw [if_pos hw]
      · rw [if_neg hw]
        norm_num
    · have := le_finiteDictionaryMax (fun w => if w = w₀ then (1 : ℝ) else 0) w₀
      rwa [if_pos rfl] at this

/-- **Entropy--temperature price.**  Preserving the complete maximum within a fixed multiplicative
error forces the linearization order to exceed the dictionary entropy divided by that error. -/
theorem log_card_div_le_of_exp_le {η p : ℝ} (hη : 0 < η) (hp : 0 < p)
    (h : Real.exp (-η) ≤ (Fintype.card ι : ℝ) ^ (-p⁻¹)) :
    Real.log (Fintype.card ι) / η ≤ p := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlog : -η ≤ -p⁻¹ * Real.log (Fintype.card ι) := by
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) ^ (-p⁻¹) := Real.rpow_pos_of_pos hcard _
    have := Real.log_le_log (Real.exp_pos (-η)) h
    rwa [Real.log_exp, Real.log_rpow hcard] at this
  have hlogcard : 0 ≤ Real.log (Fintype.card ι) := by
    refine Real.log_nonneg ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  rw [div_le_iff₀ hη]
  have hkey : p⁻¹ * Real.log (Fintype.card ι) ≤ η := by linarith
  have := mul_le_mul_of_nonneg_left hkey hp.le
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at this
  linarith

/-- The dictionary-entropy form of the linearization price for a word alphabet. -/
theorem mul_log_div_le_of_exp_le {M ℓ : ℕ} (hcard : Fintype.card ι = M ^ ℓ) {η p : ℝ}
    (hη : 0 < η) (hp : 0 < p) (h : Real.exp (-η) ≤ (Fintype.card ι : ℝ) ^ (-p⁻¹)) :
    (ℓ : ℝ) * Real.log M / η ≤ p := by
  have := log_card_div_le_of_exp_le hη hp h
  rwa [hcard, Nat.cast_pow, Real.log_pow] at this

/-- **Replica-order price.**  A degree-`r` positive reporter linearized by the `p`-th power has
linear moment order `r * p`, and preserving the complete maximum within its natural error forces
that order to exceed the dictionary entropy divided by the error rate. -/
theorem log_card_div_le_mul_of_exp_le {κ r p : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hp : 0 < p)
    (h : Real.exp (-(κ * r)) ≤ (Fintype.card ι : ℝ) ^ (-p⁻¹)) :
    Real.log (Fintype.card ι) / κ ≤ r * p := by
  have hbase := log_card_div_le_of_exp_le (mul_pos hκ hr) hp h
  rw [div_le_iff₀ (mul_pos hκ hr)] at hbase
  rw [div_le_iff₀ hκ]
  nlinarith [hbase]

end PositiveLinearization

end GaloisForLFunctions.HTGeometry
