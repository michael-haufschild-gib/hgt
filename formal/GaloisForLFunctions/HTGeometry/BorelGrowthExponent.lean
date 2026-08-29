import GaloisForLFunctions.HTGeometry.BorelGrowthLemma

/-!
# The Borel growth lemma at an arbitrary exponent

The dyadic band argument does not need the step to be `1/T(r)`: it works for the step `T(r)^{-α}`
for every `α > 0`, because the band `T(r) ∈ [2^k, 2^{k+1})` then sits in an interval of length
`2^{-kα}` and the geometric series still converges.  Smaller exponents give *longer* steps, so the
resulting statement is genuinely stronger than the classical `α = 1` form: outside a set of finite
measure, a nondecreasing majorant does not double across a step of length `T(r)^{-α}`.

That is the form a Wiman--Valiron parameter choice needs: the sampling window must be long compared
with `1/T`, not comparable to it.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GaloisForLFunctions.Nevanlinna

section

variable {T : ℝ → ℝ} {α : ℝ}

/-- The dyadic ratio `2^{-α}` as a real number. -/
private theorem dyadic_ratio_lt_one (hα : 0 < α) : ((2 : ℝ) ^ α)⁻¹ < 1 := by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ α :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, hα⟩)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have hmul : ((2 : ℝ) ^ α)⁻¹ * ((2 : ℝ) ^ α) = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hc0 : (0 : ℝ) < ((2 : ℝ) ^ α)⁻¹ := inv_pos.mpr hpos
  nlinarith [hmul, hc0, h2]

private theorem dyadic_ratio_pow (k : ℕ) :
    ((((2 : ℝ) ^ k) ^ α))⁻¹ = (((2 : ℝ) ^ α)⁻¹) ^ k := by
  have hbase : (0 : ℝ) ≤ 2 := by norm_num
  have h1 : ((2 : ℝ) ^ k) ^ α = ((2 : ℝ) ^ α) ^ k := by
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul hbase, mul_comm, Real.rpow_mul hbase,
      Real.rpow_natCast]
  rw [h1, inv_pow]

/-- **The Borel growth lemma at exponent `α`.**  For a nondecreasing `T ≥ 1` and any `α > 0`, the
set of `r ≥ a` at which `T` doubles across the step `T(r)^{-α}` has Lebesgue measure at most
`(1 - 2^{-α})⁻¹`. -/
theorem borel_growth_monotone_rpow (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) (hα : 0 < α) (a : ℝ) :
    volume {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r) ^ (-α))}
      ≤ (1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹))⁻¹ := by
  classical
  set c : ℝ := ((2 : ℝ) ^ α)⁻¹ with hc
  have hcpos : (0 : ℝ) < c := by
    rw [hc]
    exact inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) α)
  set E : Set ℝ := {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r) ^ (-α))} with hE
  set lvl : ℕ → Set ℝ := fun k => {r : ℝ | a ≤ r ∧ (2 : ℝ) ^ (k + 1) ≤ T r} with hlvl
  set sk : ℕ → ℝ := fun k => sInf (lvl k) with hsk
  set Ek : ℕ → Set ℝ := fun k => E ∩ {r : ℝ | (2 : ℝ) ^ k ≤ T r ∧ T r < (2 : ℝ) ^ (k + 1)} with hEk
  have hcover : E ⊆ ⋃ k, Ek k := by
    intro r hr
    obtain ⟨k, hk1, hk2⟩ := exists_dyadic_band (hT1 r)
    exact mem_iUnion.mpr ⟨k, hr, hk1, hk2⟩
  have hbandsub : ∀ k, Ek k ⊆ Icc (sk k - c ^ k) (sk k) := by
    intro k r hr
    obtain ⟨⟨har, hEr⟩, hlow, hupp⟩ := hr
    have hTrpos : 0 < T r := lt_of_lt_of_le one_pos (hT1 r)
    have hsteppos : 0 < (T r) ^ (-α) := Real.rpow_pos_of_pos hTrpos _
    have hmem : (r + (T r) ^ (-α)) ∈ lvl k := by
      refine ⟨by linarith, ?_⟩
      calc (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
        _ ≤ 2 * T r := by linarith [hlow]
        _ ≤ T (r + (T r) ^ (-α)) := hEr
    have hne : (lvl k).Nonempty := ⟨_, hmem⟩
    have hbdd : BddBelow (lvl k) := ⟨a, fun y hy => hy.1⟩
    have hskle : sk k ≤ r + (T r) ^ (-α) := csInf_le hbdd hmem
    have hstep : (T r) ^ (-α) ≤ c ^ k := by
      have hbk : (0 : ℝ) < ((2 : ℝ) ^ k) ^ α :=
        Real.rpow_pos_of_pos (by positivity) α
      have hmono' : ((2 : ℝ) ^ k) ^ α ≤ (T r) ^ α :=
        Real.rpow_le_rpow (by positivity) hlow (le_of_lt hα)
      have hinv : ((T r) ^ α)⁻¹ ≤ (((2 : ℝ) ^ k) ^ α)⁻¹ := inv_anti₀ hbk hmono'
      rw [Real.rpow_neg (le_of_lt hTrpos)]
      rw [dyadic_ratio_pow k] at hinv
      exact hinv
    have hlow2 : sk k - c ^ k ≤ r := by linarith
    have hupp2 : r ≤ sk k := by
      by_contra hcon
      obtain ⟨y, hy, hyr⟩ := exists_lt_of_csInf_lt hne (not_le.mp hcon)
      exact absurd (le_trans hy.2 (hmono hyr.le)) (not_le.mpr hupp)
    exact ⟨hlow2, hupp2⟩
  have hband_meas : ∀ k, volume (Ek k) ≤ ENNReal.ofReal (c ^ k) := by
    intro k
    refine le_trans (measure_mono (hbandsub k)) (le_of_eq ?_)
    rw [Real.volume_Icc]
    congr 1
    ring
  calc volume E ≤ ∑' k, volume (Ek k) :=
        le_trans (measure_mono hcover) (measure_iUnion_le _)
    _ ≤ ∑' k, ENNReal.ofReal (c ^ k) := ENNReal.tsum_le_tsum hband_meas
    _ = ∑' k : ℕ, (ENNReal.ofReal c) ^ k := by
        congr 1
        funext k
        exact ENNReal.ofReal_pow (le_of_lt hcpos) k
    _ = (1 - ENNReal.ofReal c)⁻¹ := ENNReal.tsum_geometric _

/-- The exceptional set at exponent `α` has finite measure. -/
theorem borel_growth_monotone_rpow_ne_top (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) (hα : 0 < α)
    (a : ℝ) : volume {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r) ^ (-α))} ≠ ⊤ := by
  have hc1 : ((2 : ℝ) ^ α)⁻¹ < 1 := dyadic_ratio_lt_one hα
  have hlt : ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹) < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hc1
  have hpos : (0 : ℝ≥0∞) < 1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹) := tsub_pos_iff_lt.mpr hlt
  have hfin : (1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt hpos)
  exact ne_top_of_le_ne_top hfin (borel_growth_monotone_rpow hmono hT1 hα a)

/-- **Good radii at exponent `α` are unbounded.**  Beyond every bound there is a radius at which the
nondecreasing majorant fails to double across the step `T(r)^{-α}` — a step far longer than the
classical `1/T(r)`. -/
theorem exists_ge_lt_two_mul_rpow (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) (hα : 0 < α) (R : ℝ) :
    ∃ r, R ≤ r ∧ T (r + (T r) ^ (-α)) < 2 * T r := by
  by_contra hcon
  have hbad : ∀ r, R ≤ r → 2 * T r ≤ T (r + (T r) ^ (-α)) := by
    intro r hr
    by_contra h
    exact hcon ⟨r, hr, not_le.mp h⟩
  have hsub : Ici R ⊆ {r : ℝ | R ≤ r ∧ 2 * T r ≤ T (r + (T r) ^ (-α))} :=
    fun r hr => ⟨hr, hbad r hr⟩
  have hfin := borel_growth_monotone_rpow_ne_top hmono hT1 hα R
  have hvol := measure_mono (μ := volume) hsub
  rw [Real.volume_Ici] at hvol
  exact hfin (top_le_iff.mp hvol)

/-- **The logarithmic form.**  Beyond every bound there is a point `x` at which the nondecreasing
function `x ↦ T(e^x)` fails to double across the step `T(e^x)^{-α}`. -/
theorem exists_ge_log_lt_two_mul_rpow (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) (hα : 0 < α)
    (R : ℝ) :
    ∃ x, R ≤ x ∧ T (Real.exp (x + (T (Real.exp x)) ^ (-α))) < 2 * T (Real.exp x) :=
  exists_ge_lt_two_mul_rpow (T := fun x => T (Real.exp x))
    (fun _ _ hxy => hmono (Real.exp_le_exp.mpr hxy)) (fun x => hT1 (Real.exp x)) hα R

end

end GaloisForLFunctions.Nevanlinna

namespace GaloisForLFunctions.Nevanlinna

open MeasureTheory Set

variable {T : ℝ → ℝ} {α : ℝ}

/-- The window length inside which the Borel growth lemma at exponent `α` always finds a good
radius: one more than the measure bound for the exceptional set. -/
noncomputable def borelWindow (α : ℝ) : ℝ :=
  ((1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹))⁻¹).toReal + 1

theorem one_le_borelWindow (α : ℝ) : 1 ≤ borelWindow α := by
  have h := ENNReal.toReal_nonneg (a := (1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹))⁻¹)
  rw [borelWindow]
  linarith

/-- **A Borel-good radius inside every window of length `borelWindow α`.**  The exceptional set has
measure at most `borelWindow α - 1`, so it cannot cover a window of that length. -/
theorem exists_mem_Icc_lt_two_mul_rpow_window (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r)
    (hα : 0 < α) (R : ℝ) :
    ∃ x ∈ Set.Icc R (R + borelWindow α), T (x + (T x) ^ (-α)) < 2 * T x := by
  by_contra hcon
  push_neg at hcon
  have hbad : Set.Icc R (R + borelWindow α)
      ⊆ {r : ℝ | R ≤ r ∧ 2 * T r ≤ T (r + (T r) ^ (-α))} := by
    intro r hr
    exact ⟨hr.1, hcon r hr⟩
  have hvol := measure_mono (μ := volume) hbad
  rw [Real.volume_Icc] at hvol
  have hle := le_trans hvol (borel_growth_monotone_rpow hmono hT1 hα R)
  have hc1 : ((2 : ℝ) ^ α)⁻¹ < 1 := dyadic_ratio_lt_one hα
  have hlt : ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹) < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hc1
  have hEne : (1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hlt))
  have hsub : R + borelWindow α - R = borelWindow α := by ring
  rw [hsub, ← ENNReal.ofReal_toReal hEne] at hle
  have hreal := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hle
  rw [borelWindow] at hreal
  linarith

end GaloisForLFunctions.Nevanlinna
