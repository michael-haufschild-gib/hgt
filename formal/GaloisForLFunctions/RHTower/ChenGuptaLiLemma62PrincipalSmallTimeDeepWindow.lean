import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalFarLineSharp

/-!
# Chen–Gupta–Li Lemma 6.2, principal small-time regime: the deep window, uniformly

In the principal small-time regime (`X ≥ max(1, q)`, `|t| ≤ X^ε`, cutoff `M = ⌊X^{2ε} q/N⌋`, depth
`k = ⌈(202+ε)/(2ε)⌉`, window `|v| ≤ X^{ε/2}`) the deep-line window of the far tail is

`‖∫_{|v| ≤ X^{ε/2}} FarTail_k(v) dv‖ ≤ C_ε X^{−200}`

with `C_ε` depending only on the bump and on `ε` — uniformly in `N`, `q`, `t` and `X`
(`cglLemma62_principal_smallTime_farTail_window_uniform`).

Mechanism: on the window `1 + |v − t| ≤ 3X^ε`, so the sharp far-line bound gives
`(1+|v−t|)^{2k+1/2} ≤ 3^{2k+1/2} X^{ε(2k+1/2)}`; `N M ≥ X^{2ε} q/2` gives
`N^{−2k} M^{−2k} ≤ 2^{2k} X^{−4εk} q^{−2k}`; the Euler budget `2 q^{2k+2}` leaves `q² ≤ X²`; the
window has length `2X^{ε/2}`.  The exponent is `2 + ε − 2εk ≤ −200` by the choice of `k`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

namespace CGLLemma62PrincipalSmallTimeSourceRegime

variable {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}

theorem base_pos (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) : 0 < S.base :=
  lt_of_lt_of_le zero_lt_one S.base_one

/-- On the window, `1 + |v − t| ≤ 3 X^ε`. -/
theorem one_add_abs_sub_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) {v : ℝ}
    (hv : |v| ≤ S.truncationRadius) : 1 + |v - t| ≤ 3 * S.base ^ S.epsilon := by
  have hXe : 1 ≤ S.base ^ S.epsilon := Real.one_le_rpow S.base_one S.epsilon_pos.le
  have hR : S.truncationRadius ≤ S.base ^ S.epsilon := by
    unfold truncationRadius
    exact Real.rpow_le_rpow_of_exponent_le S.base_one (by linarith [S.epsilon_pos])
  have := abs_sub_le_iff.mpr (show v - t ≤ |v| + |t| ∧ t - v ≤ |v| + |t| by
    constructor <;> linarith [le_abs_self v, neg_abs_le v, le_abs_self t, neg_abs_le t])
  linarith [S.ordinate_small]

/-- `N M ≥ X^{2ε} q / 2`. -/
theorem half_scale_le_mul_tailCutoff (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / 2 ≤ (N.value : ℝ) * S.tailCutoff.value := by
  have h := S.half_cutoffScale_le_tailCutoff
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  unfold cutoffScale at h
  have := mul_le_mul_of_nonneg_left h hN.le
  rw [show (N.value : ℝ) * (S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / N.value / 2) =
    S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / 2 by field_simp] at this
  exact this

/-- `N^{−2k} M^{−2k} q^{2k+2} ≤ 2^{2k} X^{−4εk} X²`. -/
theorem cutoff_power_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) (k : ℕ) :
    (N.value : ℝ) ^ (-2 * (k : ℝ)) * (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) *
        (Q.value : ℝ) ^ (2 * k + 2) ≤
      2 ^ (2 * (k : ℝ)) * S.base ^ (-4 * S.epsilon * k) * S.base ^ (2 : ℝ) := by
  have hX := S.base_pos
  have hq : (0 : ℝ) < Q.value := by exact_mod_cast Q.positive
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hM : (0 : ℝ) < S.tailCutoff.value := by exact_mod_cast S.tailCutoff.one_le
  have hscale := S.half_scale_le_mul_tailCutoff
  have hs0 : 0 < S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / 2 := by positivity
  have hk : -2 * (k : ℝ) ≤ 0 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  -- `(NM)^{−2k} ≤ (X^{2ε} q/2)^{−2k}`
  have h1 : (N.value : ℝ) ^ (-2 * (k : ℝ)) * (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) ≤
      (S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / 2) ^ (-2 * (k : ℝ)) := by
    rw [← Real.mul_rpow hN.le hM.le]
    exact Real.rpow_le_rpow_of_nonpos hs0 hscale hk
  have h2 : (S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / 2) ^ (-2 * (k : ℝ)) =
      S.base ^ (-4 * S.epsilon * k) * (Q.value : ℝ) ^ (-2 * (k : ℝ)) * 2 ^ (2 * (k : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity) hq.le,
      ← Real.rpow_mul hX.le, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2 <;> ring_nf
  have h3 : (Q.value : ℝ) ^ (-2 * (k : ℝ)) * (Q.value : ℝ) ^ (2 * k + 2) = (Q.value : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq]
    congr 1
    push_cast
    ring
  have hqX : (Q.value : ℝ) ^ (2 : ℝ) ≤ S.base ^ (2 : ℝ) :=
    Real.rpow_le_rpow hq.le S.modulus_le_base (by norm_num)
  have hqk : 0 ≤ (Q.value : ℝ) ^ (2 * k + 2) := by positivity
  calc (N.value : ℝ) ^ (-2 * (k : ℝ)) * (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) *
        (Q.value : ℝ) ^ (2 * k + 2)
      ≤ (S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / 2) ^ (-2 * (k : ℝ)) *
          (Q.value : ℝ) ^ (2 * k + 2) := mul_le_mul_of_nonneg_right h1 hqk
    _ = 2 ^ (2 * (k : ℝ)) * S.base ^ (-4 * S.epsilon * k) *
          ((Q.value : ℝ) ^ (-2 * (k : ℝ)) * (Q.value : ℝ) ^ (2 * k + 2)) := by rw [h2]; ring
    _ = 2 ^ (2 * (k : ℝ)) * S.base ^ (-4 * S.epsilon * k) * (Q.value : ℝ) ^ (2 : ℝ) := by
        rw [h3]
    _ ≤ _ := by gcongr

/-- `(1+|v−t|)^{2k+1/2} ≤ 3^{2k+1/2} X^{ε(2k+1/2)}` on the window. -/
theorem window_growth_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) (k : ℕ) {v : ℝ}
    (hv : |v| ≤ S.truncationRadius) :
    (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) ≤
      3 ^ (2 * (k : ℝ) + 1 / 2) * S.base ^ (S.epsilon * (2 * (k : ℝ) + 1 / 2)) := by
  have h := S.one_add_abs_sub_le hv
  calc (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) ≤ (3 * S.base ^ S.epsilon) ^ (2 * (k : ℝ) + 1 / 2) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg S.base_pos.le _),
          ← Real.rpow_mul S.base_pos.le]

end CGLLemma62PrincipalSmallTimeSourceRegime

/-- The principal small-time depth depends on `ε` only. -/
theorem CGLLemma62PrincipalSmallTimeSourceRegime.decayDepth_value
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    S.decayDepth.value = Nat.ceil ((202 + S.epsilon) / (2 * S.epsilon)) := rfl

/-- **The principal small-time deep window, uniformly.**  For every `ε > 0` there is `C ≥ 0`
(depending on the bump and `ε` only) such that every principal small-time regime with parameter
`ε` satisfies `‖∫_{|v| ≤ X^{ε/2}} FarTail_k(v) dv‖ ≤ C X^{−200}`. -/
theorem cglLemma62_principal_smallTime_farTail_window_uniform (w : CGLRealSmoothBump) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ)
      (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t), S.epsilon = ε →
      ‖∫ v in -S.truncationRadius..S.truncationRadius,
          cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  set k : ℕ := Nat.ceil ((202 + ε) / (2 * ε)) with hk
  have hkpos : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  obtain ⟨Cχ, hCχ, hχ⟩ := cglLemma62_principalRegularizedFactor_far_sharp k
  set B := cglLemma62MellinLineDecayBudget w (-2 * (k : ℝ)) 0 with hB
  have hB0 : 0 ≤ B := by
    have := cglLemma62_mellinTransform_vertical_rapidDecay w (-2 * (k : ℝ)) 0 0
    rw [pow_zero, one_mul] at this
    exact (norm_nonneg _).trans this
  set K : ℝ := B * Cχ * 2 / (2 * (k : ℝ)) * 3 ^ (2 * (k : ℝ) + 1 / 2) * 2 ^ (2 * (k : ℝ)) * 2
    with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, ?_⟩
  intro N Q t S hS
  have hdk : S.decayDepth.value = k := by rw [S.decayDepth_value, hS]
  have hX := S.base_pos
  set X := S.base with hXdef
  set e := S.epsilon with he
  have hR0 : 0 ≤ S.truncationRadius := by
    unfold CGLLemma62PrincipalSmallTimeSourceRegime.truncationRadius; positivity
  -- pointwise bound on the window
  have hχ' : ∀ z : ℂ, z.re = -2 * (S.decayDepth.value : ℝ) →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤
        Cχ * (1 + |z.im|) ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) := by
    rw [hdk]; exact hχ
  have hpt : ∀ v ∈ Set.uIoc (-S.truncationRadius) S.truncationRadius,
      ‖cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖ ≤
        K / 2 * X ^ (e * (2 * (k : ℝ) + 1 / 2) + -4 * e * k + 2) := by
    intro v hv
    have hv' : |v| ≤ S.truncationRadius := by
      rw [Set.uIoc_of_le (by linarith)] at hv
      exact abs_le.mpr ⟨hv.1.le, hv.2⟩
    have h := norm_cglLemma62PrincipalFarTailIntegrand_le w N Q t S.tailCutoff S.decayDepth hχ' v
    rw [hdk, ← hB] at h
    have hgrow := S.window_growth_le k hv'
    have hcut := S.cutoff_power_le k
    have hpowe : 0 ≤ (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) := by positivity
    have hcut0 : 0 ≤ (N.value : ℝ) ^ (-2 * (k : ℝ)) * (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) *
        (Q.value : ℝ) ^ (2 * k + 2) := by positivity
    calc ‖cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖
        ≤ B * (N.value : ℝ) ^ (-2 * (k : ℝ)) * (Cχ * (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2)) *
            (2 * (Q.value : ℝ) ^ (2 * k + 2)) *
              ((S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) / (2 * (k : ℝ))) := h
      _ = (B * Cχ * 2 / (2 * (k : ℝ))) * (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) *
            ((N.value : ℝ) ^ (-2 * (k : ℝ)) * (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) *
              (Q.value : ℝ) ^ (2 * k + 2)) := by ring
      _ ≤ (B * Cχ * 2 / (2 * (k : ℝ))) *
            (3 ^ (2 * (k : ℝ) + 1 / 2) * X ^ (e * (2 * (k : ℝ) + 1 / 2))) *
            (2 ^ (2 * (k : ℝ)) * X ^ (-4 * e * k) * X ^ (2 : ℝ)) := by
          gcongr
      _ = K / 2 * X ^ (e * (2 * (k : ℝ) + 1 / 2) + -4 * e * k + 2) := by
          rw [Real.rpow_add hX, Real.rpow_add hX, hK]
          ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hlen : |S.truncationRadius - -S.truncationRadius| = 2 * X ^ (e / 2) := by
    rw [abs_of_nonneg (by linarith)]
    unfold CGLLemma62PrincipalSmallTimeSourceRegime.truncationRadius
    ring
  rw [hlen] at hint
  have hexp : X ^ (e * (2 * (k : ℝ) + 1 / 2) + -4 * e * k + 2) * X ^ (e / 2) =
      X ^ (2 + e - 2 * e * (S.decayDepth.value : ℝ)) := by
    rw [← Real.rpow_add hX, hdk]
    congr 1
    ring
  have hdepth := S.decayDepth_source_exponent_le
  have hpow : X ^ (2 + e - 2 * e * (S.decayDepth.value : ℝ)) ≤ X ^ (-200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le S.base_one hdepth
  calc _ ≤ K / 2 * X ^ (e * (2 * (k : ℝ) + 1 / 2) + -4 * e * k + 2) * (2 * X ^ (e / 2)) := hint
    _ = K * (X ^ (e * (2 * (k : ℝ) + 1 / 2) + -4 * e * k + 2) * X ^ (e / 2)) := by ring
    _ = K * X ^ (2 + e - 2 * e * (S.decayDepth.value : ℝ)) := by rw [hexp]
    _ ≤ K * X ^ (-200 : ℝ) := mul_le_mul_of_nonneg_left hpow hK0

end RHTower

end
