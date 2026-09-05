import GaloisForLFunctions.RHTower.HighBlockErrorBounds
import GaloisForLFunctions.RHTower.ZetaGateFromDyadicMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# The high-block dyadic law from the single sharp-energy input

`SharpEnergyInput C` (the sharp-cutoff critical energy against the displaced gate mollifier is
`≤ C`, uniformly in the head length) implies `ZetaDyadicMeanSquareLaw R c` with an explicit
`c = 2 e^{4R} C (9 + e C_v²)`, for every `R > 0`.

* Low blocks `a < U^{1/8}`: the crude bound `‖ζ‖ ≤ 5e²(1+t)(4+t)`, `‖Ψ‖ ≤ N`, absorbed by the
  slack `ε U/log U`.
* High blocks `a ≥ U^{1/8}`: the sub-block sum (`HighBlockBlockCore`) with the error bounds of
  `HighBlockErrorBounds` and the asymptotics of `HighBlockAsymptotics`.

Through `zetaMollifiedMeanSquareGate_of_dyadicLaw` this is the `ζΨ` gate of the single-input `(L)`
constant; the whole high-block law now rests on one arithmetic statement.
-/

open Complex Set Finset Filter Topology MeasureTheory

namespace RHTower

noncomputable section

theorem displacedLinePt_half_sub (σ₀ τ : ℝ) :
    displacedLinePt (1 / 2 - σ₀) τ = (σ₀ : ℂ) + (τ : ℂ) * I := by
  unfold displacedLinePt
  push_cast
  ring

/-- **Crude bound on any block** (used below `U^{1/8}`). -/
theorem integral_normSq_zeta_mul_edPoly_crude {d a v : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (ha : 2 ≤ a) (hav : a ≤ v) {b : ℕ → ℂ} {N : ℕ} (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      (v - a) * ((5 * Real.exp 2 * (1 + v) * (4 + v)) * N) ^ 2 := by
  have h1v : 0 ≤ 1 + v := by linarith
  have h4v : 0 ≤ 4 + v := by linarith
  have hM0 : 0 ≤ 5 * Real.exp 2 * (1 + v) * (4 + v) :=
    mul_nonneg (mul_nonneg (by positivity) h1v) h4v
  have hpoint : ∀ τ ∈ Set.Icc a v,
      ‖riemannZeta (displacedLinePt d τ) * edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 ≤
        ((5 * Real.exp 2 * (1 + v) * (4 + v)) * N) ^ 2 := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := by linarith [hτ.1]
    have hτ2 : 2 ≤ |τ| := by rw [abs_of_nonneg hτ0]; linarith [hτ.1]
    have hζ : ‖riemannZeta (displacedLinePt d τ)‖ ≤ 5 * Real.exp 2 * (1 + v) * (4 + v) := by
      have h := norm_riemannZeta_le_smoothAFE_strip (σ := 1 / 2 - d) (t := τ) (by linarith)
        (by linarith) hτ2
      have hpt : displacedLinePt d τ = (((1 / 2 - d : ℝ)) : ℂ) + (τ : ℂ) * I := rfl
      rw [hpt]
      refine h.trans ?_
      rw [abs_of_nonneg hτ0]
      have h1 : 1 + τ ≤ 1 + v := by linarith [hτ.2]
      have h4 : 4 + τ ≤ 4 + v := by linarith [hτ.2]
      have h1τ : 0 ≤ 1 + τ := by linarith
      have h4τ : 0 ≤ 4 + τ := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h4 h4τ
        (mul_nonneg (by positivity) h1v)
    have hΨ : ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ≤ N :=
      norm_edPoly_le_card hbn (by rw [displacedLinePt_re]; linarith)
    rw [norm_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul hζ hΨ (norm_nonneg _) hM0) 2
  have hcont : Continuous (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ) *
      edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) :=
    ((continuous_riemannZeta_displacedLinePt hd).mul
      (continuous_edPoly_displacedLinePt b N d)).norm.pow 2
  have hgint : IntervalIntegrable (fun _ : ℝ => ((5 * Real.exp 2 * (1 + v) * (4 + v)) * N) ^ 2)
      volume a v :=
    (continuous_const : Continuous (fun _ : ℝ =>
      ((5 * Real.exp 2 * (1 + v) * (4 + v)) * N) ^ 2)).intervalIntegrable a v
  have h := intervalIntegral.integral_mono_on hav (hcont.intervalIntegrable a v) hgint hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-- **The raw block bound at the concrete parameters.** The brick constants `C_v, A_f, C_t` and
their defining properties are hypotheses; this isolates the one heavy elaboration. -/
theorem highBlock_raw_bound {C R Cv Af Ct η d a v U : ℝ} (hC0 : 0 ≤ C) (hAf0 : 0 ≤ Af)
    (hCt0 : 0 ≤ Ct)
    (hCv : ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ T x : ℝ, 1 ≤ T → 0 < x → x ≤ T →
      ∀ (L N : ℕ) (b : Fin N → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ u ∈ Finset.range L,
        ∑ r : Fin (L * N), ‖Sieve.dirConv L N (sharpHead criticalHeadCoeff L u) b r‖ ^ 2 ≤ C) →
      highBlockDualEnergy d x T L N b ≤ Cv ^ 2 * C)
    (hAf : ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ x : ℝ, 0 < x → ∀ T τ : ℝ, 4 ≤ T → T ≤ τ →
      ∀ L : ℕ, ‖highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L‖ ≤
        Af * (τ - T) * T ^ (-(d + 1 / 4 + 1)) * x ^ (d + 1 / 4) *
          ∑ n ∈ Finset.range L, ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)))
    (hCt : ∀ (d x τ : ℝ), 0 < d → d ≤ 1 / 4 → 0 < x → ∀ L : ℕ, 1 ≤ L →
      ‖highBlockAFETail d x τ L‖ ≤
        Ct * (x ^ (200 : ℝ) * ((L : ℝ) ^ (1 - (1 / 2 - d + 200)) / ((1 / 2 - d + 200) - 1)) +
          (1 + |τ|) ^ (((200 : ℕ) : ℝ) + 1 / 2) * x ^ (-(1 / 2 - d + 200)) *
            ((L : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200)))
    (hη : 0 < η) (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hdU : d * Real.log U ≤ 2 * R) (hU1 : 1 ≤ U)
    (ha : 20 ≤ a) (hav : a ≤ v) (hv2 : v ≤ 2 * a) (hvU : v ≤ U) (hLU : (hbL a : ℝ) + 1 ≤ U)
    (hN2 : 2 ≤ hbN U)
    (hin : ∀ u ∈ Finset.range (hbL a),
      ∑ r : Fin (hbL a * hbN U),
        ‖Sieve.dirConv (hbL a) (hbN U) (sharpHead criticalHeadCoeff (hbL a) u)
          (fun m => highBlockMollifierCoeffNat d (hbCoeff (hbN U)) m) r‖ ^ 2 ≤ C) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly (hbCoeff (hbN U)) (Finset.Icc 1 (hbN U)) (displacedLinePt d τ)‖ ^ 2) ≤
      (1 + η) * (2 * ((v - a) * (9 * Real.exp (4 * R) * C) +
          (hbJ a U : ℝ) * (8 * ((hbL a * hbN U : ℕ) : ℝ) *
            (1 + Real.log ((hbL a * hbN U : ℕ) : ℝ))) * (9 * Real.exp (4 * R) * C)) +
        2 * (Real.exp 1 * (Cv ^ 2 * C * ((v - a) * Real.exp (4 * R)) +
          (hbJ a U : ℝ) * (8 * ((hbL a * hbN U : ℕ) : ℝ) *
            (1 + Real.log ((hbL a * hbN U : ℕ) : ℝ))) * (Cv ^ 2 * C) *
            (2 * Real.exp (4 * R))))) +
      (1 + 1 / η) * 3 * (v - a) * (((hbN U : ℝ)) ^ 2 *
        ((Real.exp 1 * Real.exp (4 * R)) *
          ((11 / 3) * Af * Real.exp (2 * R) * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2 +
        (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 +
        (Ct * (1 + 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ)) * a ^ (-(1 : ℝ))) ^ 2)) := by
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have haU : a ≤ U := hav.trans hvU
  have hx := hbX_pos ha0
  have hJ1 : 1 ≤ hbJ a U := by
    unfold hbJ
    apply Nat.ceil_pos.mpr
    positivity
  have hbn : ∀ n ∈ Finset.Icc 1 (hbN U), ‖hbCoeff (hbN U) n‖ ≤ 1 := fun n hn =>
    norm_hbCoeff_le hN2 hn
  have hEdir : highBlockDirectEnergy d (hbX a) (hbCoeff (hbN U)) (hbL a) (hbN U) ≤
      9 * Real.exp (4 * R) * C :=
    hbEdir_le hC0 hd hd4 hdU ha hLU _ hin
  have hEdual : ∀ T : ℝ, a ≤ T → T ≤ v →
      highBlockDualEnergy d (hbX a) T (hbL a) (hbN U)
        (fun m => highBlockMollifierCoeffNat d (hbCoeff (hbN U)) m) ≤ Cv ^ 2 * C :=
    fun T hTa _ => hCv d hd hd4 T (hbX a) (by linarith) hx ((hbX_le ha1).trans hTa)
      (hbL a) (hbN U) _ hC0 hin
  have hfreeze : ∀ T τ : ℝ, a ≤ T → T ≤ τ → τ ≤ v → τ - T ≤ (v - a) / hbJ a U →
      ‖highBlockDualHead d (hbX a) τ (hbL a) - highBlockDualHeadFrozen d (hbX a) T τ (hbL a)‖ ≤
        (11 / 3) * Af * Real.exp (2 * R) * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20)) :=
    fun T τ hTa hTτ hτv hh => hbFreeze_le hAf hAf0 hd hd4 hdU ha hav hv2 hvU hTa hTτ hτv hh
  have hpole : ∀ τ : ℝ, a ≤ τ → τ ≤ v →
      ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) (hbX a)‖ ≤
        Real.exp 1 * Real.exp (-(a ^ 2)) :=
    fun τ hτa _ => hbPole_le hd hd4 ha hτa
  have htail : ∀ τ : ℝ, a ≤ τ → τ ≤ v → ‖highBlockAFETail d (hbX a) τ (hbL a)‖ ≤
      Ct * (1 + 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ)) * a ^ (-(1 : ℝ)) :=
    fun τ hτa hτv => hbTail_le hCt hCt0 hd hd4 ha hτa (hτv.trans hv2)
  have hW : ∀ τ : ℝ, a ≤ τ → τ ≤ v →
      ‖zetaChi (displacedLinePt d τ)‖ ^ 2 ≤ Real.exp 1 * Real.exp (4 * R) :=
    fun τ hτa hτv => (hbChi_le hd hd4 hdU hU1 (by linarith) (hτv.trans hvU)).1
  have hw : ∀ τ : ℝ, a ≤ τ → τ ≤ v → chiModulusWeight (2 * d) τ ≤ Real.exp (4 * R) :=
    fun τ hτa hτv => (hbChi_le hd hd4 hdU hU1 (by linarith) (hτv.trans hvU)).2
  exact integral_normSq_zeta_mul_edPoly_block_le hd hd4 hx (by linarith) hav hη hJ1 hbn
    hEdir hEdual hfreeze hpole htail hW hw (by positivity)

/-- **The high-block bound.** -/
theorem exists_highBlock_bound {C R : ℝ} (hC0 : 0 ≤ C) (hR : 0 < R) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      (∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ a : ℝ, 1 ≤ a → a ≤ U → ∀ u ∈ Finset.range (hbL a),
        ∑ r : Fin (hbL a * hbN U),
          ‖Sieve.dirConv (hbL a) (hbN U) (sharpHead criticalHeadCoeff (hbL a) u)
            (fun m => highBlockMollifierCoeffNat d (hbCoeff (hbN U)) m) r‖ ^ 2 ≤ C) →
      ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → d * Real.log U ≤ 2 * R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((1 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
            edPoly (hbCoeff (hbN U)) (Finset.Icc 1 (hbN U)) (displacedLinePt d τ)‖ ^ 2) ≤
          (c₀ + ε) * (v - a) + ε * (U / Real.log U) := by
  obtain ⟨Cv, hCv0, hCv⟩ := exists_highBlockDualEnergy_le_sharp
  obtain ⟨Af, hAf0, hAf⟩ := exists_norm_highBlockDualHead_sub_frozen_le
  obtain ⟨Ct, hCt0, hCt⟩ := exists_norm_highBlockAFETail_le (A := 200) (by norm_num) (K'' := 200)
    (by norm_num)
  refine ⟨2 * (Real.exp (4 * R) * C * (9 + Real.exp 1 * Cv ^ 2)), by positivity, ?_⟩
  intro ε hε
  set c₀ : ℝ := 2 * (Real.exp (4 * R) * C * (9 + Real.exp 1 * Cv ^ 2)) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set η : ℝ := ε / (3 * (c₀ + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hη1 : 0 < 1 + 1 / η := by positivity
  set Kt : ℝ := Ct * (1 + 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ)) with hKt
  set Kf : ℝ := (11 / 3) * Af * Real.exp (2 * R) with hKf
  set K0 : ℝ := 9 * Real.exp (4 * R) * C + 2 * Real.exp 1 * (Cv ^ 2 * C) * Real.exp (4 * R)
    with hK0
  have hKt0 : 0 ≤ Kt := by positivity
  have hKf0 : 0 ≤ Kf := by positivity
  have hK00 : 0 ≤ K0 := by positivity
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 2),
    eventually_const_mul_rpow_neg_le (2 * Real.exp 1) ((44 : ℝ) / 100) (by norm_num) one_pos,
    eventually_const_mul_rpow_neg_le 4 ((49 : ℝ) / 100) (by norm_num) one_pos,
    Filter.eventually_ge_atTop ((2 : ℝ) ^ (20 : ℕ)),
    eventually_const_mul_rpow_neg_mul_log_pow_le ((1 + η) * 2 * 32 * K0) ((9 : ℝ) / 100)
      (by norm_num) 2 (by positivity : 0 < ε / 3),
    eventually_const_mul_rpow_neg_le ((1 + 1 / η) * 3 * (Real.exp 1 * Real.exp (4 * R)) * Kf ^ 2)
      ((17 : ℝ) / 1600) (by norm_num) (by positivity : 0 < ε / 9),
    eventually_rpow_mul_exp_neg_le (by positivity : 0 < ε / (9 * ((1 + 1 / η) * 3 * Real.exp 2))),
    eventually_const_mul_rpow_neg_le ((1 + 1 / η) * 3 * Kt ^ 2) ((3 : ℝ) / 20) (by norm_num)
      (by positivity : 0 < ε / 9)]
    with U hUe hLNU' hLU' hU2 hMV hF3 hF4 hF5
  intro hinput d hd hd4 hdU a v ha haU8 hav hv2 hvU
  have hU1 : (1 : ℝ) ≤ U := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith only [this, hUe]
  have hU0 : (0 : ℝ) < U := by linarith only [hU1]
  have ha1 : (1 : ℝ) ≤ a := by linarith only [ha]
  have ha0 : (0 : ℝ) < a := by linarith only [ha]
  have haU : a ≤ U := hav.trans hvU
  have hlogU : 2 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 2) hUe
    rwa [Real.log_exp] at this
  have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
  -- derived eventual facts
  have hLNU : 2 * U ^ ((56 : ℝ) / 100) * Real.exp 1 ≤ U := by
    have h : 2 * Real.exp 1 * U ^ (-((44 : ℝ) / 100)) ≤ 1 := hLNU'
    have hsplit : U ^ ((56 : ℝ) / 100) = U ^ (-((44 : ℝ) / 100)) * U := by
      rw [show ((56 : ℝ) / 100) = -((44 : ℝ) / 100) + 1 by norm_num, Real.rpow_add hU0,
        Real.rpow_one]
    rw [hsplit]
    calc 2 * (U ^ (-((44 : ℝ) / 100)) * U) * Real.exp 1
        = (2 * Real.exp 1 * U ^ (-((44 : ℝ) / 100))) * U := by ring
      _ ≤ 1 * U := mul_le_mul_of_nonneg_right h hU0.le
      _ = U := one_mul U
  have hLU : (hbL a : ℝ) + 1 ≤ U := by
    have h : 4 * U ^ (-((49 : ℝ) / 100)) ≤ 1 := hLU'
    have hsplit : U ^ ((51 : ℝ) / 100) = U ^ (-((49 : ℝ) / 100)) * U := by
      rw [show ((51 : ℝ) / 100) = -((49 : ℝ) / 100) + 1 by norm_num, Real.rpow_add hU0,
        Real.rpow_one]
    have hL : (hbL a : ℝ) ≤ a ^ ((51 : ℝ) / 100) + 1 := hbL_le ha0.le
    have h51 : a ^ ((51 : ℝ) / 100) ≤ U ^ ((51 : ℝ) / 100) :=
      Real.rpow_le_rpow ha0.le haU (by norm_num)
    have hone : (1 : ℝ) ≤ U ^ ((51 : ℝ) / 100) := by
      calc (1 : ℝ) = U ^ (0 : ℝ) := (Real.rpow_zero U).symm
        _ ≤ U ^ ((51 : ℝ) / 100) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have h4 : 4 * U ^ ((51 : ℝ) / 100) ≤ U := by
      rw [hsplit]
      calc 4 * (U ^ (-((49 : ℝ) / 100)) * U) = (4 * U ^ (-((49 : ℝ) / 100))) * U := by ring
        _ ≤ 1 * U := mul_le_mul_of_nonneg_right h hU0.le
        _ = U := one_mul U
    linarith only [hL, h51, hone, h4]
  have hN2 : 2 ≤ hbN U := by
    unfold hbN
    apply Nat.le_floor
    have h : ((2 : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) ≤ U ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact_mod_cast h
  have hNU : (hbN U : ℝ) ≤ U ^ ((1 : ℝ) / 20) := hbN_le hU0.le
  have hN2sq : ((hbN U : ℝ)) ^ 2 ≤ U ^ ((1 : ℝ) / 10) := by
    calc ((hbN U : ℝ)) ^ 2 ≤ (U ^ ((1 : ℝ) / 20)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hNU 2
      _ = U ^ ((1 : ℝ) / 10) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
  -- the raw block estimate
  have hraw := highBlock_raw_bound hC0 hAf0 hCt0 hCv hAf hCt hη hd hd4 hdU hU1 ha hav hv2 hvU
    hLU hN2 (hinput d hd hd4 a ha1 haU)
  refine hraw.trans ?_
  rw [← hKf, ← hKt]
  have hva : 0 ≤ v - a := by linarith only [hav]
  have hJMV := hbJMV_le ha1 haU hUe hLNU
  set MV : ℝ := 8 * ((hbL a * hbN U : ℕ) : ℝ) * (1 + Real.log ((hbL a * hbN U : ℕ) : ℝ)) with hMVdef
  -- (M): main term
  have hmain : (1 + η) * (2 * ((v - a) * (9 * Real.exp (4 * R) * C)) +
      2 * (Real.exp 1 * (Cv ^ 2 * C * ((v - a) * Real.exp (4 * R))))) ≤ (c₀ + ε / 3) * (v - a) := by
    have hid : (1 + η) * (2 * ((v - a) * (9 * Real.exp (4 * R) * C)) +
        2 * (Real.exp 1 * (Cv ^ 2 * C * ((v - a) * Real.exp (4 * R))))) =
        (1 + η) * c₀ * (v - a) := by
      rw [hc₀]; ring
    rw [hid]
    have hηc : η * c₀ ≤ ε / 3 := by
      rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ ε * 3 := by positivity
      linarith only [this]
    apply mul_le_mul_of_nonneg_right _ hva
    linarith only [hηc]
  -- (MV): the sub-block count times the mean-value error
  have hmv : (1 + η) * (2 * ((hbJ a U : ℝ) * MV * (9 * Real.exp (4 * R) * C)) +
      2 * (Real.exp 1 * ((hbJ a U : ℝ) * MV * (Cv ^ 2 * C) * (2 * Real.exp (4 * R))))) ≤
      ε / 3 * (U / Real.log U) := by
    have hid : (1 + η) * (2 * ((hbJ a U : ℝ) * MV * (9 * Real.exp (4 * R) * C)) +
        2 * (Real.exp 1 * ((hbJ a U : ℝ) * MV * (Cv ^ 2 * C) * (2 * Real.exp (4 * R))))) =
        (1 + η) * 2 * K0 * ((hbJ a U : ℝ) * MV) := by rw [hK0]; ring
    rw [hid]
    have h1 : (1 + η) * 2 * K0 * ((hbJ a U : ℝ) * MV) ≤
        (1 + η) * 2 * K0 * (32 * U ^ ((91 : ℝ) / 100) * Real.log U) :=
      mul_le_mul_of_nonneg_left hJMV (by positivity)
    refine h1.trans ?_
    have hsplit : U ^ ((91 : ℝ) / 100) = U ^ (-((9 : ℝ) / 100)) * U := by
      rw [show ((91 : ℝ) / 100) = -((9 : ℝ) / 100) + 1 by norm_num, Real.rpow_add hU0,
        Real.rpow_one]
    have hid2 : (1 + η) * 2 * K0 * (32 * U ^ ((91 : ℝ) / 100) * Real.log U) =
        ((1 + η) * 2 * 32 * K0 * (U ^ (-((9 : ℝ) / 100)) * Real.log U ^ 2)) * (U / Real.log U) := by
      rw [hsplit]
      field_simp
      try ring
    rw [hid2]
    exact mul_le_mul_of_nonneg_right hMV (by positivity)
  -- (E): the error group
  have hU8 : (1 : ℝ) ≤ U ^ ((1 : ℝ) / 8) := by
    calc (1 : ℝ) = U ^ (0 : ℝ) := (Real.rpow_zero U).symm
      _ ≤ U ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
  have hfr : ((hbN U : ℝ)) ^ 2 * ((Real.exp 1 * Real.exp (4 * R)) *
      (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2) ≤
      (Real.exp 1 * Real.exp (4 * R)) * Kf ^ 2 * U ^ (-((17 : ℝ) / 1600)) := by
    have ha17 : a ^ (-((17 : ℝ) / 400)) ≤ U ^ (-((17 : ℝ) / 3200)) := by
      calc a ^ (-((17 : ℝ) / 400)) ≤ (U ^ ((1 : ℝ) / 8)) ^ (-((17 : ℝ) / 400)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) haU8 (by norm_num)
        _ = U ^ (-((17 : ℝ) / 3200)) := by rw [← Real.rpow_mul hU0.le]; norm_num
    have hUU : U ^ ((1 : ℝ) / 10) * (U ^ (-((1 : ℝ) / 20))) ^ 2 = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_add hU0]
      norm_num
    have hsq : (U ^ (-((17 : ℝ) / 3200))) ^ 2 = U ^ (-((17 : ℝ) / 1600)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
    calc ((hbN U : ℝ)) ^ 2 * ((Real.exp 1 * Real.exp (4 * R)) *
          (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2)
        ≤ U ^ ((1 : ℝ) / 10) * ((Real.exp 1 * Real.exp (4 * R)) *
          (Kf * U ^ (-((17 : ℝ) / 3200)) * U ^ (-((1 : ℝ) / 20))) ^ 2) := by
          gcongr
      _ = (Real.exp 1 * Real.exp (4 * R)) * Kf ^ 2 * (U ^ (-((17 : ℝ) / 3200))) ^ 2 *
          (U ^ ((1 : ℝ) / 10) * (U ^ (-((1 : ℝ) / 20))) ^ 2) := by ring
      _ = (Real.exp 1 * Real.exp (4 * R)) * Kf ^ 2 * U ^ (-((17 : ℝ) / 1600)) := by
          rw [hUU, hsq, mul_one]
  have hpo : ((hbN U : ℝ)) ^ 2 * (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 ≤
      Real.exp 2 * (U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4)))) := by
    have ha2 : U ^ ((1 : ℝ) / 4) ≤ a ^ 2 := by
      calc U ^ ((1 : ℝ) / 4) = (U ^ ((1 : ℝ) / 8)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
        _ ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) haU8 2
    have hexp : (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 = Real.exp 2 * Real.exp (-(2 * a ^ 2)) := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [hexp]
    have h2 : Real.exp (-(2 * a ^ 2)) ≤ Real.exp (-(2 * U ^ ((1 : ℝ) / 4))) :=
      Real.exp_le_exp.mpr (by linarith)
    calc ((hbN U : ℝ)) ^ 2 * (Real.exp 2 * Real.exp (-(2 * a ^ 2)))
        ≤ U ^ ((1 : ℝ) / 10) * (Real.exp 2 * Real.exp (-(2 * U ^ ((1 : ℝ) / 4)))) := by gcongr
      _ = Real.exp 2 * (U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4)))) := by ring
  have hta : ((hbN U : ℝ)) ^ 2 * (Kt * a ^ (-(1 : ℝ))) ^ 2 ≤ Kt ^ 2 * U ^ (-((3 : ℝ) / 20)) := by
    have ha1' : a ^ (-(1 : ℝ)) ≤ U ^ (-((1 : ℝ) / 8)) := by
      calc a ^ (-(1 : ℝ)) ≤ (U ^ ((1 : ℝ) / 8)) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) haU8 (by norm_num)
        _ = U ^ (-((1 : ℝ) / 8)) := by rw [← Real.rpow_mul hU0.le]; norm_num
    have hsq : (U ^ (-((1 : ℝ) / 8))) ^ 2 = U ^ (-((1 : ℝ) / 4)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
    have hUU : U ^ ((1 : ℝ) / 10) * U ^ (-((1 : ℝ) / 4)) = U ^ (-((3 : ℝ) / 20)) := by
      rw [← Real.rpow_add hU0]; norm_num
    calc ((hbN U : ℝ)) ^ 2 * (Kt * a ^ (-(1 : ℝ))) ^ 2
        ≤ U ^ ((1 : ℝ) / 10) * (Kt * U ^ (-((1 : ℝ) / 8))) ^ 2 := by gcongr
      _ = Kt ^ 2 * (U ^ ((1 : ℝ) / 10) * (U ^ (-((1 : ℝ) / 8))) ^ 2) := by ring
      _ = Kt ^ 2 * U ^ (-((3 : ℝ) / 20)) := by rw [hsq, hUU]
  have hF4' : (1 + 1 / η) * 3 * (Real.exp 2 *
      (U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4))))) ≤ ε / 9 := by
    have hpos : 0 < (1 + 1 / η) * 3 * Real.exp 2 := by positivity
    calc (1 + 1 / η) * 3 * (Real.exp 2 * (U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4)))))
        = ((1 + 1 / η) * 3 * Real.exp 2) *
          (U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4)))) := by ring
      _ ≤ ((1 + 1 / η) * 3 * Real.exp 2) * (ε / (9 * ((1 + 1 / η) * 3 * Real.exp 2))) :=
          mul_le_mul_of_nonneg_left hF4 hpos.le
      _ = ε / 9 := by field_simp; try ring
  have hsum : (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 *
      ((Real.exp 1 * Real.exp (4 * R)) * (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2 +
        (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 + (Kt * a ^ (-(1 : ℝ))) ^ 2)) ≤ ε / 3 := by
    have e1 : (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 * ((Real.exp 1 * Real.exp (4 * R)) *
        (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2)) ≤ ε / 9 := by
      refine le_trans (mul_le_mul_of_nonneg_left hfr (by positivity)) ?_
      have := hF3
      linarith only [this]
    have e2 : (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 * (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2) ≤
        ε / 9 :=
      le_trans (mul_le_mul_of_nonneg_left hpo (by positivity)) hF4'
    have e3 : (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 * (Kt * a ^ (-(1 : ℝ))) ^ 2) ≤ ε / 9 := by
      refine le_trans (mul_le_mul_of_nonneg_left hta (by positivity)) ?_
      have := hF5
      linarith only [this]
    have hid : (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 *
        ((Real.exp 1 * Real.exp (4 * R)) *
          (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2 +
          (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 + (Kt * a ^ (-(1 : ℝ))) ^ 2)) =
        (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 * ((Real.exp 1 * Real.exp (4 * R)) *
          (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2)) +
        (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 * (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2) +
        (1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 * (Kt * a ^ (-(1 : ℝ))) ^ 2) := by ring
    rw [hid]
    linarith only [e1, e2, e3]
  have herr : (1 + 1 / η) * 3 * (v - a) * (((hbN U : ℝ)) ^ 2 *
      ((Real.exp 1 * Real.exp (4 * R)) * (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2 +
        (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 + (Kt * a ^ (-(1 : ℝ))) ^ 2)) ≤ ε / 3 * (v - a) := by
    have hid : (1 + 1 / η) * 3 * (v - a) * (((hbN U : ℝ)) ^ 2 *
        ((Real.exp 1 * Real.exp (4 * R)) *
          (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2 +
          (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 + (Kt * a ^ (-(1 : ℝ))) ^ 2)) =
        ((1 + 1 / η) * 3 * (((hbN U : ℝ)) ^ 2 *
          ((Real.exp 1 * Real.exp (4 * R)) *
            (Kf * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20))) ^ 2 +
            (Real.exp 1 * Real.exp (-(a ^ 2))) ^ 2 + (Kt * a ^ (-(1 : ℝ))) ^ 2))) * (v - a) := by
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hsum hva
  -- combine
  have hsplit_total : (1 + η) * (2 * ((v - a) * (9 * Real.exp (4 * R) * C) +
        (hbJ a U : ℝ) * MV * (9 * Real.exp (4 * R) * C)) +
      2 * (Real.exp 1 * (Cv ^ 2 * C * ((v - a) * Real.exp (4 * R)) +
        (hbJ a U : ℝ) * MV * (Cv ^ 2 * C) * (2 * Real.exp (4 * R))))) =
      (1 + η) * (2 * ((v - a) * (9 * Real.exp (4 * R) * C)) +
        2 * (Real.exp 1 * (Cv ^ 2 * C * ((v - a) * Real.exp (4 * R))))) +
      (1 + η) * (2 * ((hbJ a U : ℝ) * MV * (9 * Real.exp (4 * R) * C)) +
        2 * (Real.exp 1 * ((hbJ a U : ℝ) * MV * (Cv ^ 2 * C) * (2 * Real.exp (4 * R))))) := by
    ring
  rw [hsplit_total]
  have hUlog : 0 ≤ U / Real.log U := by positivity
  have hfinal : (c₀ + ε / 3) * (v - a) + ε / 3 * (U / Real.log U) + ε / 3 * (v - a) ≤
      (c₀ + ε) * (v - a) + ε * (U / Real.log U) := by
    have h1 : 0 ≤ ε * (v - a) := mul_nonneg hε.le hva
    have h2 : 0 ≤ ε * (U / Real.log U) := mul_nonneg hε.le hUlog
    linarith only [h1, h2]
  linarith only [hmain, hmv, herr, hfinal]

/-- **The dyadic mean-square law for `ζΨ` from the single sharp-energy input.** -/
theorem exists_zetaDyadicMeanSquareLaw_of_sharpEnergyInput {C R : ℝ} (hC0 : 0 ≤ C) (hR : 0 < R)
    (hin : SharpEnergyInput C) : ∃ c : ℝ, 0 ≤ c ∧ ZetaDyadicMeanSquareLaw R c := by
  obtain ⟨c₀, hc₀0, hblock⟩ := exists_highBlock_bound hC0 hR
  refine ⟨c₀, hc₀0, ?_⟩
  intro ε hε
  filter_upwards [hin, hblock ε hε, Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop ((2 : ℝ) ^ (20 : ℕ)),
    eventually_const_mul_rpow_neg_le 2 ((19 : ℝ) / 20) (by norm_num) one_pos,
    eventually_const_mul_rpow_neg_mul_log_pow_le (16200 * Real.exp 4) ((11 : ℝ) / 40)
      (by norm_num) 1 hε]
    with U hinU hblockU hUe hU2 hNU' hlow
  have hU1 : (1 : ℝ) ≤ U := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith only [this, hUe]
  have hU0 : (0 : ℝ) < U := by linarith only [hU1]
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith only [this]
    linarith only [this, hUe]
  have hlogU : 2 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 2) hUe
    rwa [Real.log_exp] at this
  have hN2 : 2 ≤ hbN U := by
    unfold hbN
    apply Nat.le_floor
    have h : ((2 : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) ≤ U ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact_mod_cast h
  have hN1 : 1 ≤ hbN U := by omega
  have hNU : (hbN U : ℝ) ≤ U - 1 := by
    have h : 2 * U ^ (-((19 : ℝ) / 20)) ≤ 1 := hNU'
    have hsplit : U ^ ((1 : ℝ) / 20) = U ^ (-((19 : ℝ) / 20)) * U := by
      rw [show ((1 : ℝ) / 20) = -((19 : ℝ) / 20) + 1 by norm_num, Real.rpow_add hU0,
        Real.rpow_one]
    have h2 : 2 * U ^ ((1 : ℝ) / 20) ≤ U := by
      rw [hsplit]
      calc 2 * (U ^ (-((19 : ℝ) / 20)) * U) = (2 * U ^ (-((19 : ℝ) / 20))) * U := by ring
        _ ≤ 1 * U := mul_le_mul_of_nonneg_right h hU0.le
        _ = U := one_mul U
    have := hbN_le hU0.le
    linarith only [this, h2, hU3]
  have hNpos : (1 : ℝ) ≤ (hbN U : ℝ) := by exact_mod_cast hN1
  refine ⟨(hbN U : ℝ) ^ (5 : ℕ), hbCoeff (hbN U), hbN U, hN1, hbCoeff_one hN2,
    fun n hn => norm_hbCoeff_le hN2 hn, fun n _ => conj_hbCoeff _ n,
    one_le_pow₀ hNpos, sum_norm_hbCoeff_mul_rpow_le hN2, ?_, ?_⟩
  · -- log Mb ≤ 5 log (U - 1)
    rw [Real.log_pow]
    push_cast
    have : Real.log (hbN U : ℝ) ≤ Real.log (U - 1) :=
      Real.log_le_log (by linarith only [hNpos]) hNU
    linarith only [this]
  intro σ₀ hσ₀ hσ₀' hR1 hR2 a v ha hav hv2 hvU
  have hd : 0 < 1 / 2 - σ₀ := by linarith only [hσ₀']
  have hd4 : 1 / 2 - σ₀ ≤ 1 / 4 := by linarith only [hσ₀]
  have hdU : (1 / 2 - σ₀) * Real.log U ≤ 2 * R := by
    have hlog2 : Real.log U ≤ 2 * Real.log (U - 1) := by
      have h1 : U ≤ (U - 1) ^ 2 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ U - 3) hU0.le
        nlinarith [this]
      have h2 : Real.log U ≤ Real.log ((U - 1) ^ 2) := Real.log_le_log hU0 h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2]
    calc (1 / 2 - σ₀) * Real.log U ≤ (1 / 2 - σ₀) * (2 * Real.log (U - 1)) :=
          mul_le_mul_of_nonneg_left hlog2 hd.le
      _ = 2 * ((1 / 2 - σ₀) * Real.log (U - 1)) := by ring
      _ ≤ 2 * R := by linarith only [hR2]
  have hpt : ∀ t : ℝ, (σ₀ : ℂ) + (t : ℂ) * I = displacedLinePt (1 / 2 - σ₀) t := fun t =>
    (displacedLinePt_half_sub σ₀ t).symm
  simp_rw [hpt]
  rcases le_or_gt (U ^ ((1 : ℝ) / 8)) a with hhigh | hlow'
  · have h := hblockU hinU (1 / 2 - σ₀) hd hd4 hdU a v ha hhigh hav hv2 hvU
    have : ε * (U / Real.log U) ≤ ε * (a + U / Real.log U) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith only [ha]
    linarith only [h, this]
  · -- crude bound
    have hcrude := integral_normSq_zeta_mul_edPoly_crude hd hd4 (by linarith) hav
      (fun n hn => norm_hbCoeff_le hN2 hn)
    refine hcrude.trans ?_
    have hU8 : (1 : ℝ) ≤ U ^ ((1 : ℝ) / 8) := by
      calc (1 : ℝ) = U ^ (0 : ℝ) := (Real.rpow_zero U).symm
        _ ≤ U ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have hv8 : v ≤ 2 * U ^ ((1 : ℝ) / 8) := by linarith only [hv2, hlow']
    have hva : v - a ≤ 2 * U ^ ((1 : ℝ) / 8) := by linarith only [hv8, ha]
    have h1v : 1 + v ≤ 3 * U ^ ((1 : ℝ) / 8) := by linarith only [hv8, hU8]
    have h4v : 4 + v ≤ 6 * U ^ ((1 : ℝ) / 8) := by linarith only [hv8, hU8]
    have hN : (hbN U : ℝ) ≤ U ^ ((1 : ℝ) / 20) := hbN_le hU0.le
    have hva0 : 0 ≤ v - a := by linarith only [hav]
    have h1v0 : 0 ≤ 1 + v := by linarith only [hav, ha]
    have h4v0 : 0 ≤ 4 + v := by linarith only [hav, ha]
    have hbound : (v - a) * ((5 * Real.exp 2 * (1 + v) * (4 + v)) * (hbN U : ℝ)) ^ 2 ≤
        (2 * U ^ ((1 : ℝ) / 8)) *
          ((5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8))) *
            U ^ ((1 : ℝ) / 20)) ^ 2 := by
      have hin1 : (5 * Real.exp 2 * (1 + v) * (4 + v)) * (hbN U : ℝ) ≤
          (5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8))) *
            U ^ ((1 : ℝ) / 20) := by
        have hA : 5 * Real.exp 2 * (1 + v) ≤ 5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left h1v (by positivity)
        have hB : 5 * Real.exp 2 * (1 + v) * (4 + v) ≤
            5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8)) :=
          mul_le_mul hA h4v h4v0 (by positivity)
        exact mul_le_mul hB hN (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hva (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        h1v0) h4v0) (Nat.cast_nonneg _)) hin1 2) (by positivity) (by positivity)
    refine hbound.trans ?_
    have hid : (2 * U ^ ((1 : ℝ) / 8)) *
        ((5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8))) *
          U ^ ((1 : ℝ) / 20)) ^ 2 =
        16200 * Real.exp 4 * (U ^ ((1 : ℝ) / 8) * (U ^ ((1 : ℝ) / 8)) ^ 2 * (U ^ ((1 : ℝ) / 8)) ^ 2 *
          (U ^ ((1 : ℝ) / 20)) ^ 2) := by
      rw [show Real.exp 4 = Real.exp 2 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
      ring
    have hpow : U ^ ((1 : ℝ) / 8) * (U ^ ((1 : ℝ) / 8)) ^ 2 * (U ^ ((1 : ℝ) / 8)) ^ 2 *
        (U ^ ((1 : ℝ) / 20)) ^ 2 = U ^ ((29 : ℝ) / 40) := by
      rw [← Real.rpow_natCast (U ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_natCast (U ^ ((1 : ℝ) / 20)) 2,
        ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le, ← Real.rpow_add hU0, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0]
      norm_num
    have hsplit : U ^ ((29 : ℝ) / 40) = U ^ (-((11 : ℝ) / 40)) * U := by
      rw [show ((29 : ℝ) / 40) = -((11 : ℝ) / 40) + 1 by norm_num, Real.rpow_add hU0,
        Real.rpow_one]
    rw [hid, hpow, hsplit]
    have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
    have hid2 : 16200 * Real.exp 4 * (U ^ (-((11 : ℝ) / 40)) * U) =
        (16200 * Real.exp 4 * (U ^ (-((11 : ℝ) / 40)) * Real.log U ^ 1)) * (U / Real.log U) := by
      field_simp
      try ring
    rw [hid2]
    calc (16200 * Real.exp 4 * (U ^ (-((11 : ℝ) / 40)) * Real.log U ^ 1)) * (U / Real.log U)
        ≤ ε * (U / Real.log U) := mul_le_mul_of_nonneg_right hlow (by positivity)
      _ ≤ ε * (a + U / Real.log U) := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          linarith only [ha]
      _ ≤ (c₀ + ε) * (v - a) + ε * (a + U / Real.log U) := by
          have : 0 ≤ (c₀ + ε) * (v - a) := mul_nonneg (by positivity) hva0
          linarith only [this]

end

end RHTower
