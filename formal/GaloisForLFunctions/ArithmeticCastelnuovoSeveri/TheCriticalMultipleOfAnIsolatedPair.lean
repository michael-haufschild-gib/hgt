import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DoublyLogarithmicVisibilityAndExcludedDepthLaw

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
    (isolatedPairConfig (rvmLocalDensity_pos hγ) hδ hδ' γ) (min_le_left _ _)
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
    rw [hz] at hK
    exact zero_ne_one hK.2
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact csInf_le hbelow (hmem ε hε)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairIndex_eq
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairIndex_eq_zero_of_le_lower
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairIndex_eq_one_of_upper_lt
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.rvmPairEdge_bounds
