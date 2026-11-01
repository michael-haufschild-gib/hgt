import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DoublyLogarithmicVisibilityAndExcludedDepthLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AnIsolatedPairIsVisibleAboveNyquist

/-!
# The critical multiple of an isolated pair

The coordinate `K = exp(2a)` turns the exact aperture visibility law into a
power law in the local Riemann–von Mangoldt density. Once `δL ≥ 16`, the first
visible multiple lies between `(4δL)^(1/δ)` and `(6δL+1)^(1/δ)`.
-/

noncomputable section
set_option autoImplicit false
open Set Real
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Hodge defect at the aperture corresponding to a critical multiple `K`. -/
def rvmPairIndex {γ δ : ℝ} (hγ : 2 * π < γ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (K : ℝ) : ℕ∞ :=
  hodgeDefectAt (isolatedPairConfig (rvmLocalDensity_pos hγ) hδ hδ' γ) (log K / 2)

/-- The first critical multiple at which the isolated pair has a negative square. -/
def rvmPairEdge {γ δ : ℝ} (hγ : 2 * π < γ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : ℝ :=
  sInf {K : ℝ | 1 < K ∧ rvmPairIndex hγ hδ hδ' K = 1}

/-- Exact visibility in the critical-multiple coordinate, up to the Nyquist aperture. -/
theorem rvmPairIndex_eq {γ δ K : ℝ} (hγ : 2 * π < γ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hK : 1 < K) (hKL : K ≤ exp (rvmLocalDensity γ)) :
    rvmPairIndex hγ hδ hδ' K =
      if (K ^ δ - K ^ (-δ)) / (2 * δ) ≤ 2 * rvmLocalDensity γ + log K
      then 0 else 1 := by
  have hK0 := zero_lt_one.trans hK
  have ha : 0 < log K / 2 := div_pos (log_pos hK) (by norm_num)
  have haL : log K / 2 ≤ rvmLocalDensity γ / 2 := by
    have hh := log_le_log hK0 hKL
    rw [log_exp] at hh
    linarith only [hh]
  unfold rvmPairIndex
  rw [hodgeDefectAt_isolatedPair (rvmLocalDensity_pos hγ) hδ hδ' γ ha haL]
  have hsignal : sinh (2 * δ * (log K / 2)) / δ =
      (K ^ δ - K ^ (-δ)) / (2 * δ) := by
    rw [sinh_eq, rpow_def_of_pos hK0, rpow_def_of_pos hK0]
    rw [show 2 * δ * (log K / 2) = log K * δ by ring,
      show -(log K * δ) = log K * (-δ) by ring]
    ring
  rw [hsignal, show 2 * (log K / 2) = log K by ring]

private theorem log_six_mul_add_one_lt {x : ℝ} (hx : 16 ≤ x) :
    log (6 * x + 1) < x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have he := pow_div_factorial_le_exp x hx0 2
  norm_num at he
  have hquad : 6 * x + 1 < x ^ 2 / 2 := by
    nlinarith only [sq_nonneg (x - 16), hx]
  have hlt := log_lt_log (by positivity : 0 < 6 * x + 1) (hquad.trans_le he)
  rwa [log_exp] at hlt

/-- Below the lower power law every test remains nonnegative. -/
theorem rvmPairIndex_eq_zero_of_le_lower {γ δ K : ℝ} (hγ : 2 * π < γ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hdeep : 16 ≤ δ * rvmLocalDensity γ)
    (hK : 1 < K) (hKlo : K ≤ (4 * δ * rvmLocalDensity γ) ^ (1 / δ)) :
    rvmPairIndex hγ hδ hδ' K = 0 := by
  have hL := rvmLocalDensity_pos hγ
  have hb : 0 < 4 * δ * rvmLocalDensity γ := by positivity
  have hlog := log_le_log (zero_lt_one.trans hK) hKlo
  rw [log_rpow hb] at hlog
  have hloglo : log (4 * δ * rvmLocalDensity γ) < δ * rvmLocalDensity γ :=
    (log_lt_log hb (by nlinarith only [hdeep] :
      4 * δ * rvmLocalDensity γ < 6 * (δ * rvmLocalDensity γ) + 1)).trans
      (log_six_mul_add_one_lt hdeep)
  have hscale : (1 / δ) * log (4 * δ * rvmLocalDensity γ) < rvmLocalDensity γ := by
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ hδ]
    simpa only [mul_comm] using hloglo
  apply hodgeDefectAt_isolatedPair_rvmDensity_eq_zero hγ hδ hδ'
    (div_pos (log_pos hK) (by norm_num))
  · linarith only [hlog, hscale]
  · change log K / 2 ≤ (1 / (2 * δ)) * log (4 * δ * rvmLocalDensity γ)
    linarith only [hlog, show (1 / δ) * log (4 * δ * rvmLocalDensity γ) / 2 =
      (1 / (2 * δ)) * log (4 * δ * rvmLocalDensity γ) by ring]

/-- Above the upper power law the negative square persists at every larger aperture. -/
theorem rvmPairIndex_eq_one_of_upper_lt {γ δ K : ℝ} (hγ : 2 * π < γ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hdeep : 16 ≤ δ * rvmLocalDensity γ)
    (hKhi : (6 * δ * rvmLocalDensity γ + 1) ^ (1 / δ) < K) :
    rvmPairIndex hγ hδ hδ' K = 1 := by
  have hL := rvmLocalDensity_pos hγ
  have hb : 0 < 6 * δ * rvmLocalDensity γ + 1 := by positivity
  have hlog := log_lt_log (rpow_pos_of_pos hb (1 / δ)) hKhi
  rw [log_rpow hb] at hlog
  have hloghi : log (6 * δ * rvmLocalDensity γ + 1) < δ * rvmLocalDensity γ := by
    simpa only [mul_assoc] using log_six_mul_add_one_lt hdeep
  have hscale : (1 / δ) * log (6 * δ * rvmLocalDensity γ + 1) < rvmLocalDensity γ := by
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ hδ]
    simpa only [mul_comm] using hloghi
  let a := min (log K / 2) (rvmLocalDensity γ / 2)
  have ha : (1 / (2 * δ)) * log (6 * δ * rvmLocalDensity γ + 1) < a := by
    have heq : (1 / (2 * δ)) * log (6 * δ * rvmLocalDensity γ + 1) =
        ((1 / δ) * log (6 * δ * rvmLocalDensity γ + 1)) / 2 := by ring
    rw [heq]
    exact lt_min (by linarith only [hlog]) (by linarith only [hscale])
  have hone := hodgeDefectAt_isolatedPair_rvmDensity_eq_one hγ hδ hδ'
    ha (min_le_right _ _)
  have hmono := hodgeDefectAt_mono
    (isolatedPairConfig (rvmLocalDensity_pos hγ) hδ hδ' γ)
    (min_le_left (log K / 2) (rvmLocalDensity γ / 2))
  change hodgeDefectAt _ a ≤ rvmPairIndex hγ hδ hδ' K at hmono
  rw [hone] at hmono
  apply le_antisymm ?_ hmono
  exact (hodgeDefectAt_le _ (temperedConfig_isolatedPairConfig
    (rvmLocalDensity_pos hγ) hδ hδ' γ) _).trans_eq
      (encard_rightZeros_isolatedPair (rvmLocalDensity_pos hγ) hδ hδ' γ)

/-- Two explicit power laws enclose the first visible critical multiple. -/
theorem rvmPairEdge_bounds {γ δ : ℝ} (hγ : 2 * π < γ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hdeep : 16 ≤ δ * rvmLocalDensity γ) :
    (4 * δ * rvmLocalDensity γ) ^ (1 / δ) ≤ rvmPairEdge hγ hδ hδ' ∧
      rvmPairEdge hγ hδ hδ' ≤ (6 * δ * rvmLocalDensity γ + 1) ^ (1 / δ) := by
  have hL := rvmLocalDensity_pos hγ
  let U := (6 * δ * rvmLocalDensity γ + 1) ^ (1 / δ)
  have hU : 1 ≤ U := one_le_rpow (by nlinarith only [hdeep]) (by positivity)
  let S := {K : ℝ | 1 < K ∧ rvmPairIndex hγ hδ hδ' K = 1}
  have hmem : ∀ ε : ℝ, 0 < ε → U + ε ∈ S := by
    intro ε hε
    exact ⟨by linarith only [hU, hε], rvmPairIndex_eq_one_of_upper_lt hγ hδ hδ' hdeep
      (by dsimp only [U] at *; linarith only [hε])⟩
  have hne : S.Nonempty := ⟨U + 1, hmem 1 zero_lt_one⟩
  have hbelow : BddBelow S := ⟨1, fun K hK => hK.1.le⟩
  constructor
  · apply le_csInf hne
    intro K hK
    by_contra hlt
    have hz := rvmPairIndex_eq_zero_of_le_lower hγ hδ hδ' hdeep hK.1
      (le_of_lt (lt_of_not_ge hlt))
    have hone := hK.2
    rw [hz] at hone
    exact zero_ne_one hone
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact csInf_le hbelow (hmem ε hε)

/-- The pair signal root determines the edge, capped at the lattice Nyquist aperture. -/
theorem rvmPairEdge_exact {γ δ : ℝ} (hγ : 2 * π < γ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    ∃! x : ℝ, 0 < x ∧ sinh x - x = 2 * δ * rvmLocalDensity γ ∧
      rvmPairEdge hγ hδ hδ' = exp (min (x / δ) (rvmLocalDensity γ)) ∧
      ∀ K : ℝ, 1 < K →
        rvmPairIndex hγ hδ hδ' K =
          if K ≤ exp (min (x / δ) (rvmLocalDensity γ)) then 0 else 1 := by
  have hL := rvmLocalDensity_pos hγ
  let t := δ * rvmLocalDensity γ
  let u := max 16 t
  have ht : 0 < t := mul_pos hδ hL
  have htu : t ≤ u := le_max_right _ _
  have hu : 0 < u := ht.trans_le htu
  have he : 6 * u + 1 < exp u := by
    have hh := exp_lt_exp.mpr (log_six_mul_add_one_lt (show 16 ≤ u from le_max_left _ _))
    rwa [exp_log (by positivity : 0 < 6 * u + 1)] at hh
  have hn : exp (-u) ≤ 1 := by
    simpa only [exp_zero] using exp_le_exp.mpr (show -u ≤ 0 by linarith only [hu])
  have htop : 2 * t < sinh u - u := by
    rw [sinh_eq]
    linarith only [he, hn, htu]
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hu.le
    (continuous_sinh.sub continuous_id).continuousOn
    (show 2 * t ∈ Icc (sinh 0 - 0) (sinh u - u) from
      ⟨by simpa only [sinh_zero, sub_zero] using (mul_pos (by norm_num : (0 : ℝ) < 2) ht).le,
        htop.le⟩)
  change sinh x - x = 2 * t at hx
  have hx0 : 0 < x := sinh_sub_id_strictMono.lt_iff_lt.mp (by
    rw [hx, sinh_zero, sub_zero]
    positivity)
  have hE1 : 1 < exp (min (x / δ) (rvmLocalDensity γ)) :=
    one_lt_exp_iff.mpr (lt_min (div_pos hx0 hδ) hL)
  -- Below the Nyquist aperture, strict monotonicity solves the exact visibility inequality.
  have hlocal : ∀ K : ℝ, 1 < K → K ≤ exp (rvmLocalDensity γ) →
      rvmPairIndex hγ hδ hδ' K = if K ≤ exp (x / δ) then 0 else 1 := by
    intro K hK hKL
    have hK0 := zero_lt_one.trans hK
    have ha := div_pos (log_pos hK) (by norm_num : (0 : ℝ) < 2)
    have haL : log K / 2 ≤ rvmLocalDensity γ / 2 := by
      have hh := log_le_log hK0 hKL
      rw [log_exp] at hh
      linarith only [hh]
    unfold rvmPairIndex
    rw [hodgeDefectAt_isolatedPair (rvmLocalDensity_pos hγ) hδ hδ' γ ha haL]
    have hcond : sinh (2 * δ * (log K / 2)) / δ ≤
        2 * rvmLocalDensity γ + 2 * (log K / 2) ↔ δ * log K ≤ x := by
      rw [show 2 * δ * (log K / 2) = δ * log K by ring, div_le_iff₀ hδ]
      have hh : sinh (δ * log K) ≤ (2 * rvmLocalDensity γ + 2 * (log K / 2)) * δ ↔
          sinh (δ * log K) - δ * log K ≤ sinh x - x := by
        rw [hx]
        dsimp only [t]
        constructor <;> intro h <;> nlinarith only [h]
      exact hh.trans sinh_sub_id_strictMono.le_iff_le
    have hcompare : δ * log K ≤ x ↔ K ≤ exp (x / δ) := by
      rw [mul_comm δ, ← le_div_iff₀ hδ, log_le_iff_le_exp hK0]
    rw [hcond, hcompare]
  -- Above Nyquist, a difference of translates kills the lattice and exposes the pair.
  have hlaw : ∀ K : ℝ, 1 < K →
      rvmPairIndex hγ hδ hδ' K =
        if K ≤ exp (min (x / δ) (rvmLocalDensity γ)) then 0 else 1 := by
    intro K hK
    by_cases hKL : K ≤ exp (rvmLocalDensity γ)
    · have hcut : K ≤ exp (min (x / δ) (rvmLocalDensity γ)) ↔ K ≤ exp (x / δ) := by
        rw [← log_le_iff_le_exp (zero_lt_one.trans hK), le_min_iff,
          log_le_iff_le_exp (zero_lt_one.trans hK), log_le_iff_le_exp (zero_lt_one.trans hK)]
        exact and_iff_left hKL
      rw [hcut]
      exact hlocal K hK hKL
    have ha : rvmLocalDensity γ / 2 < log K / 2 := by
      have hh := log_lt_log (exp_pos _) (lt_of_not_ge hKL)
      rw [log_exp] at hh
      linarith only [hh]
    have hcut : ¬ K ≤ exp (min (x / δ) (rvmLocalDensity γ)) := fun hh =>
      hKL (hh.trans (exp_le_exp.mpr (min_le_right _ _)))
    rw [if_neg hcut]
    exact hodgeDefectAt_isolatedPair_eq_one_of_nyquist_lt hL hδ hδ' γ ha
  have hedge : rvmPairEdge hγ hδ hδ' = exp (min (x / δ) (rvmLocalDensity γ)) := by
    have hset : {K : ℝ | 1 < K ∧ rvmPairIndex hγ hδ hδ' K = 1} =
        Ioi (exp (min (x / δ) (rvmLocalDensity γ))) := by
      ext K
      constructor
      · rintro ⟨hK, hi⟩
        rw [hlaw K hK] at hi
        by_contra hh
        have hle : K ≤ exp (min (x / δ) (rvmLocalDensity γ)) := le_of_not_gt hh
        rw [if_pos hle] at hi
        exact zero_ne_one hi
      · intro hK
        have hK1 := hE1.trans hK
        exact ⟨hK1, by rw [hlaw K hK1, if_neg (not_le.mpr hK)]⟩
    unfold rvmPairEdge
    rw [hset, csInf_Ioi]
  refine ⟨x, ⟨hx0, ?_, hedge, hlaw⟩, fun y hy => ?_⟩
  · simpa only [t, mul_assoc] using hx
  · apply sinh_sub_id_strictMono.injective
    exact hy.2.1.trans (by simpa only [t, mul_assoc] using hx.symm)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairIndex_eq
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairIndex_eq_zero_of_le_lower
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairIndex_eq_one_of_upper_lt
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairEdge_bounds
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairEdge_exact
