import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalSmallTimeTruncation

/-!
# Chen–Gupta–Li Lemma 6.2, principal small-time regime: the assembled statement

For the principal character and every `ε > 0` there is `C_ε` (depending only on the bump and `ε`)
such that in every principal small-time regime (`X ≥ max(1,q)`, `|t| ≤ X^ε`, `M = ⌊X^{2ε}q/N⌋`)

`e^{it log N} Σ_n w(n/N)² (n/N)^{it} = Res_q(t) + (1/2π) ∫_{|v| ≤ X^{ε/2}} F_M(1/2+iv) dv + O(C_ε X^{−200})`,

`F_M` the principal finite contour integrand on the critical line
(`cglLemma62_principal_smallTime_smoothedSum_uniform`).

Proof: the exact identity `2π·phase·SmoothedSum = 2π·Res + ∫ ReflectedLine`, the exact split of the
reflected line into the critical finite line and the deep tail line (corpus), and three uniform
estimates: the critical truncation, the deep-line truncation (this module: Mellin decay of order
`2k + 3` against the sharp growth `(1+|v−t|)^{2k+1/2}`), and the deep window.
-/

set_option autoImplicit false

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- On `|v| ≥ 1`, `1 + |v − t| ≤ 3 X^ε |v|`. -/
theorem CGLLemma62PrincipalSmallTimeSourceRegime.one_add_abs_sub_le_mul
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) {v : ℝ} (hv : 1 ≤ |v|) :
    1 + |v - t| ≤ 3 * S.base ^ S.epsilon * |v| := by
  have hXe : 1 ≤ S.base ^ S.epsilon := Real.one_le_rpow S.base_one S.epsilon_pos.le
  have ht := S.ordinate_small
  have h1 : |v - t| ≤ |v| + |t| := abs_sub _ _
  nlinarith

/-- **Uniform deep-line truncation.**  For every `ε > 0` there is `C ≥ 0` such that in every
principal small-time regime with parameter `ε`,
`‖∫_ℝ FarTail_k − ∫_{|v| ≤ X^{ε/2}} FarTail_k‖ ≤ C X^{−200}`. -/
theorem cglLemma62_principal_smallTime_farTail_truncation_uniform (w : CGLRealSmoothBump) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ)
      (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t), S.epsilon = ε →
      ‖(∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v) -
          ∫ v in -S.truncationRadius..S.truncationRadius,
            cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  set k : ℕ := Nat.ceil ((202 + ε) / (2 * ε)) with hk
  have hkpos : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  obtain ⟨Cχ, hCχ, hχ⟩ := cglLemma62_principalRegularizedFactor_far_sharp k
  set n : ℕ := 2 * k + 3 with hn
  set B := cglLemma62MellinLineDecayBudget w (-2 * (k : ℝ)) n with hB
  have hB0 : 0 ≤ B := by
    have := cglLemma62_mellinTransform_vertical_rapidDecay w (-2 * (k : ℝ)) n 1
    simp only [abs_one, one_pow, one_mul] at this
    exact (norm_nonneg _).trans this
  set K : ℝ := B * Cχ * 2 / (2 * (k : ℝ)) * 3 ^ (2 * (k : ℝ) + 1 / 2) * 2 ^ (2 * (k : ℝ))
    with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K / (5 / 2 - 1), by positivity, ?_⟩
  intro N Q t S hS
  have hdk : S.decayDepth.value = k := by rw [S.decayDepth_value, hS]
  have hX := S.base_pos
  have hR1 := S.one_le_truncationRadius
  have hR0 : 0 < S.truncationRadius := by linarith
  have hχ' : ∀ z : ℂ, z.re = -2 * (S.decayDepth.value : ℝ) →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤
        Cχ * (1 + |z.im|) ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) := by
    rw [hdk]; exact hχ
  set E : ℝ := S.epsilon * (2 * (k : ℝ) + 1 / 2) + -4 * S.epsilon * k + 2 with hE
  have hpt : ∀ v : ℝ, S.truncationRadius ≤ |v| →
      ‖cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖ ≤
        (K * S.base ^ E) * |v| ^ (-(5 / 2 : ℝ)) := by
    intro v hv
    have hv1 : 1 ≤ |v| := hR1.trans hv
    have hv0 : 0 < |v| := by linarith
    have h := norm_cglLemma62PrincipalFarTailIntegrand_le_mellin w N Q t S.tailCutoff
      S.decayDepth hχ' v
    rw [hdk] at h
    -- Mellin decay of order `n` on the deep line
    have hpt' : cglLemma62FarLeftPoint S.decayDepth v =
        (((-2 * (k : ℝ)) : ℝ) : ℂ) + (v : ℂ) * I := by
      unfold cglLemma62FarLeftPoint; rw [hdk]; push_cast; ring
    have hH := cglLemma62_mellinTransform_vertical_rapidDecay w (-2 * (k : ℝ)) n v
    rw [← hpt', ← hB] at hH
    have hH' : ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint S.decayDepth v)‖ ≤
        B * |v| ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg hv0.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hv0 n), mul_comm]
      exact hH
    -- the sharp growth on `|v| ≥ 1`
    have hgrow : (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) ≤
        3 ^ (2 * (k : ℝ) + 1 / 2) * S.base ^ (S.epsilon * (2 * (k : ℝ) + 1 / 2)) *
          |v| ^ (2 * (k : ℝ) + 1 / 2) := by
      calc (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2)
          ≤ (3 * S.base ^ S.epsilon * |v|) ^ (2 * (k : ℝ) + 1 / 2) :=
            Real.rpow_le_rpow (by positivity) (S.one_add_abs_sub_le_mul hv1) (by positivity)
        _ = _ := by
            rw [Real.mul_rpow (by positivity) hv0.le, Real.mul_rpow (by norm_num)
              (Real.rpow_nonneg hX.le _), ← Real.rpow_mul hX.le]
    have hcut := S.cutoff_power_le k
    have hvpow : |v| ^ (-(n : ℝ)) * |v| ^ (2 * (k : ℝ) + 1 / 2) = |v| ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hv0, hn]
      congr 1
      push_cast
      ring
    have hχ0 : 0 ≤ Cχ * (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) := by positivity
    have hgrow0 : 0 ≤ (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) := by positivity
    have hcut0 : 0 ≤ (N.value : ℝ) ^ (-2 * (k : ℝ)) *
        (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) * (Q.value : ℝ) ^ (2 * k + 2) := by positivity
    calc ‖cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖
        ≤ ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint S.decayDepth v)‖ *
            (N.value : ℝ) ^ (-2 * (k : ℝ)) * (Cχ * (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2)) *
              (2 * (Q.value : ℝ) ^ (2 * k + 2)) *
                ((S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) / (2 * (k : ℝ))) := h
      _ = (Cχ * 2 / (2 * (k : ℝ))) *
            ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint S.decayDepth v)‖ *
            (1 + |v - t|) ^ (2 * (k : ℝ) + 1 / 2) *
            ((N.value : ℝ) ^ (-2 * (k : ℝ)) * (S.tailCutoff.value : ℝ) ^ (-2 * (k : ℝ)) *
              (Q.value : ℝ) ^ (2 * k + 2)) := by ring
      _ ≤ (Cχ * 2 / (2 * (k : ℝ))) * (B * |v| ^ (-(n : ℝ))) *
            (3 ^ (2 * (k : ℝ) + 1 / 2) * S.base ^ (S.epsilon * (2 * (k : ℝ) + 1 / 2)) *
              |v| ^ (2 * (k : ℝ) + 1 / 2)) *
            (2 ^ (2 * (k : ℝ)) * S.base ^ (-4 * S.epsilon * k) * S.base ^ (2 : ℝ)) := by
          gcongr
      _ = K * (S.base ^ (S.epsilon * (2 * (k : ℝ) + 1 / 2)) * S.base ^ (-4 * S.epsilon * k) *
            S.base ^ (2 : ℝ)) * (|v| ^ (-(n : ℝ)) * |v| ^ (2 * (k : ℝ) + 1 / 2)) := by
          rw [hK]; ring
      _ = (K * S.base ^ E) * |v| ^ (-(5 / 2 : ℝ)) := by
          rw [hvpow, ← Real.rpow_add hX, ← Real.rpow_add hX, hE]
  have htail := Sieve.norm_integral_sub_interval_le_powerTail
    (cglLemma62_principalFarTail_integrable w N Q t S.tailCutoff S.decayDepth)
    (by positivity) (by norm_num : (1 : ℝ) < 5 / 2) hR0 hpt
  have hRpow : S.truncationRadius ^ (1 - (5 / 2 : ℝ)) = S.base ^ (S.epsilon / 2 * (1 - 5 / 2)) := by
    unfold CGLLemma62PrincipalSmallTimeSourceRegime.truncationRadius
    rw [← Real.rpow_mul hX.le]
  have hdepth := S.decayDepth_source_exponent_le
  rw [hdk] at hdepth
  have hfinal : S.base ^ E * S.base ^ (S.epsilon / 2 * (1 - 5 / 2)) ≤ S.base ^ (-200 : ℝ) := by
    rw [← Real.rpow_add hX]
    refine Real.rpow_le_rpow_of_exponent_le S.base_one ?_
    rw [hE]
    nlinarith [S.epsilon_pos]
  calc _ ≤ 2 * (K * S.base ^ E) * (S.truncationRadius ^ (1 - (5 / 2 : ℝ)) / (5 / 2 - 1)) := htail
    _ = 2 * K / (5 / 2 - 1) * (S.base ^ E * S.base ^ (S.epsilon / 2 * (1 - 5 / 2))) := by
        rw [hRpow]; ring
    _ ≤ 2 * K / (5 / 2 - 1) * S.base ^ (-200 : ℝ) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)

/-- **Chen–Gupta–Li Lemma 6.2 for the principal character, small-time regime, assembled.**
For every `ε > 0` there is `C ≥ 0` (bump and `ε` only) such that in every principal small-time
regime with parameter `ε`:
`‖2π·phase·SmoothedSum − (2π·Res + ∫_{|v| ≤ X^{ε/2}} F_M(1/2+iv) dv)‖ ≤ C X^{−200}`. -/
theorem cglLemma62_principal_smallTime_smoothedSum_uniform (w : CGLRealSmoothBump) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ)
      (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t), S.epsilon = ε →
      ‖(2 * Real.pi : ℝ) •
            (cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q 1 t) -
          ((2 * Real.pi : ℝ) • cglLemma62PrincipalResidueCoefficient w N Q t +
            ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
                ((1 / 2 : ℂ) + (v : ℂ) * I))‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := cglLemma62_principal_smallTime_finiteCritical_truncation_uniform w hε
  obtain ⟨C₂, hC₂, h₂⟩ := cglLemma62_principal_smallTime_farTail_truncation_uniform w hε
  obtain ⟨C₃, hC₃, h₃⟩ := cglLemma62_principal_smallTime_farTail_window_uniform w hε
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro N Q t S hS
  rw [cglLemma62_principal_smoothedCharacterSum_eq_residue_add_reflected,
    cglLemma62_principal_reflected_integral_eq_finiteCritical_add_farTail w N Q t S.tailCutoff
      S.decayDepth]
  set A := ∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t
    S.tailCutoff.value ((1 / 2 : ℂ) + (v : ℂ) * I)
  set A' := ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
    cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
      ((1 / 2 : ℂ) + (v : ℂ) * I)
  set B := ∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value
    S.decayDepth v
  set B' := ∫ v in -S.truncationRadius..S.truncationRadius,
    cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v
  have e : (2 * Real.pi : ℝ) • cglLemma62PrincipalResidueCoefficient w N Q t + (A + B) -
      ((2 * Real.pi : ℝ) • cglLemma62PrincipalResidueCoefficient w N Q t + A') =
        (A - A') + ((B - B') + B') := by ring
  rw [e]
  calc ‖(A - A') + ((B - B') + B')‖ ≤ ‖A - A'‖ + (‖B - B'‖ + ‖B'‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ C₁ * S.base ^ (-200 : ℝ) + (C₂ * S.base ^ (-200 : ℝ) + C₃ * S.base ^ (-200 : ℝ)) :=
        add_le_add (h₁ N Q t S hS) (add_le_add (h₂ N Q t S hS) (h₃ N Q t S hS))
    _ = (C₁ + C₂ + C₃) * S.base ^ (-200 : ℝ) := by ring

/-- **The same, normalised.**  `‖phase·SmoothedSum − Res − (1/2π)∫_{window} F_M‖ ≤ C X^{−200}`. -/
theorem cglLemma62_principal_smallTime_smoothedSum_uniform' (w : CGLRealSmoothBump) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ)
      (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t), S.epsilon = ε →
      ‖cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q 1 t -
          (cglLemma62PrincipalResidueCoefficient w N Q t +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
                cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
                  ((1 / 2 : ℂ) + (v : ℂ) * I))‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, h⟩ := cglLemma62_principal_smallTime_smoothedSum_uniform w hε
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨C / (2 * Real.pi), by positivity, fun N Q t S hS => ?_⟩
  have hb := h N Q t S hS
  set Z := cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q 1 t
  set R := cglLemma62PrincipalResidueCoefficient w N Q t
  set W := ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
    cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
      ((1 / 2 : ℂ) + (v : ℂ) * I)
  have heq : (2 * Real.pi : ℝ) • Z - ((2 * Real.pi : ℝ) • R + W) =
      ((2 * Real.pi : ℝ) : ℂ) * (Z - (R + ((1 / (2 * Real.pi) : ℝ) : ℂ) * W)) := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le] at hb
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi, mul_comm]
  exact hb

end RHTower

end
