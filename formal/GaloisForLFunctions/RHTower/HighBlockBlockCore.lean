import GaloisForLFunctions.RHTower.HighBlockParameters

/-!
# High-block law: summing the sub-block estimate over a block

`[a, v]` is cut into `J` sub-blocks `[T_j, T_{j+1}]`, `T_j = a + j(v−a)/J`, and on each the
sub-block estimate is applied with the dual weight frozen at `T_j`. Summing:

`∫_a^v ‖ζΨ‖² ≤ (1+η)[2(v−a)E_dir + 2J·MV·E_dir + 2e(E_dual (v−a) w_max + 2J·MV·E_dual w_max)]
              + (1+1/η)·3(v−a)N²(W_sup E_freeze² + E_pole² + E_tail²)`,

`MV = 8LN(1+log LN)`. All inputs are hypotheses here; the bricks supply them and the asymptotic
lemma shows every term but `2(v−a)(E_dir + e E_dual w_max)` is `≤ ε(v−a) + ε U/log U`.
-/

open Complex Set Finset MeasureTheory

namespace RHTower

noncomputable section

/-- The sub-block endpoints. -/
def subBlockPt (a v : ℝ) (J : ℕ) (j : ℕ) : ℝ := a + (j : ℝ) * ((v - a) / J)

theorem subBlockPt_zero (a v : ℝ) (J : ℕ) : subBlockPt a v J 0 = a := by
  simp [subBlockPt]

theorem subBlockPt_last {a v : ℝ} {J : ℕ} (hJ : 1 ≤ J) : subBlockPt a v J J = v := by
  unfold subBlockPt
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
  field_simp
  try ring

theorem subBlockPt_succ_sub (a v : ℝ) (J : ℕ) (j : ℕ) :
    subBlockPt a v J (j + 1) - subBlockPt a v J j = (v - a) / J := by
  unfold subBlockPt
  push_cast
  ring

theorem subBlockPt_mono {a v : ℝ} {J : ℕ} (hav : a ≤ v) (j : ℕ) :
    subBlockPt a v J j ≤ subBlockPt a v J (j + 1) := by
  have := subBlockPt_succ_sub a v J j
  have h0 : 0 ≤ (v - a) / J := by positivity
  linarith

theorem le_subBlockPt {a v : ℝ} {J : ℕ} (hav : a ≤ v) (j : ℕ) : a ≤ subBlockPt a v J j := by
  unfold subBlockPt
  have : 0 ≤ (j : ℝ) * ((v - a) / J) := by positivity
  linarith

theorem subBlockPt_le {a v : ℝ} {J : ℕ} (hav : a ≤ v) {j : ℕ} (hj : j ≤ J) :
    subBlockPt a v J j ≤ v := by
  unfold subBlockPt
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    simp
    exact hav
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
  have : (j : ℝ) * ((v - a) / J) ≤ (J : ℝ) * ((v - a) / J) :=
    mul_le_mul_of_nonneg_right hjJ (by positivity)
  rw [mul_div_cancel₀ _ hJ0.ne'] at this
  linarith

/-- **Sum over sub-blocks.** -/
theorem integral_normSq_zeta_mul_edPoly_block_le
    {d x a v η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x) (ha : 4 ≤ a) (hav : a ≤ v)
    (hη : 0 < η) {b : ℕ → ℂ} {N L J : ℕ} (hJ : 1 ≤ J) (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    {Edir Edual Efreeze Epole Etail Wsup wmax : ℝ}
    (hEdir : highBlockDirectEnergy d x b L N ≤ Edir)
    (hEdual : ∀ T : ℝ, a ≤ T → T ≤ v →
      highBlockDualEnergy d x T L N (fun m => highBlockMollifierCoeffNat d b m) ≤ Edual)
    (hfreeze : ∀ T τ : ℝ, a ≤ T → T ≤ τ → τ ≤ v → τ - T ≤ (v - a) / J →
      ‖highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L‖ ≤ Efreeze)
    (hpole : ∀ τ : ℝ, a ≤ τ → τ ≤ v →
      ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x‖ ≤ Epole)
    (htail : ∀ τ : ℝ, a ≤ τ → τ ≤ v → ‖highBlockAFETail d x τ L‖ ≤ Etail)
    (hW : ∀ τ : ℝ, a ≤ τ → τ ≤ v → ‖zetaChi (displacedLinePt d τ)‖ ^ (2 : ℕ) ≤ Wsup)
    (hw : ∀ τ : ℝ, a ≤ τ → τ ≤ v → chiModulusWeight (2 * d) τ ≤ wmax) (hwmax0 : 0 ≤ wmax) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ (2 : ℕ)) ≤
      (1 + η) * (2 * ((v - a) * Edir +
          (J : ℝ) * (8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ))) * Edir) +
        2 * (Real.exp 1 * (Edual * ((v - a) * wmax) +
          (J : ℝ) * (8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ))) * Edual *
            (2 * wmax)))) +
      (1 + 1 / η) * 3 * (v - a) * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
  set MV : ℝ := 8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) with hMV
  have hMV0 : 0 ≤ MV := by
    rw [hMV]
    have := Real.log_natCast_nonneg (L * N)
    positivity
  set h : ℝ := (v - a) / J with hh
  have hh0 : 0 ≤ h := by positivity
  set T : ℕ → ℝ := subBlockPt a v J with hT
  have hT0 : T 0 = a := subBlockPt_zero a v J
  have hTJ : T J = v := subBlockPt_last hJ
  have hTsucc : ∀ j, T (j + 1) - T j = h := fun j => subBlockPt_succ_sub a v J j
  have hTmono : ∀ j, T j ≤ T (j + 1) := fun j => subBlockPt_mono hav j
  have hTge : ∀ j, a ≤ T j := fun j => le_subBlockPt hav j
  have hTle : ∀ j, j ≤ J → T j ≤ v := fun j hj => subBlockPt_le hav hj
  -- nonnegativity of the abstract constants
  have hEdir0 : 0 ≤ Edir :=
    le_trans (Finset.sum_nonneg fun _ _ => by positivity) hEdir
  have hEdual0 : 0 ≤ Edual :=
    le_trans (Finset.sum_nonneg fun _ _ => by positivity) (hEdual a le_rfl hav)
  have hEf0 : 0 ≤ Efreeze :=
    le_trans (norm_nonneg _) (hfreeze a a le_rfl le_rfl hav (by rw [sub_self]; exact hh0))
  have hEp0 : 0 ≤ Epole := le_trans (norm_nonneg _) (hpole a le_rfl hav)
  have hEt0 : 0 ≤ Etail := le_trans (norm_nonneg _) (htail a le_rfl hav)
  have hWs0 : 0 ≤ Wsup := le_trans (by positivity) (hW a le_rfl hav)
  -- the integrand is continuous, hence interval integrable on every sub-block
  set F : ℝ → ℝ := fun τ => ‖riemannZeta (displacedLinePt d τ) *
    edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ (2 : ℕ) with hF
  have hFc : Continuous F :=
    ((continuous_riemannZeta_displacedLinePt hd).mul
      (continuous_edPoly_displacedLinePt b N d)).norm.pow 2
  -- per sub-block bound (uniform form)
  have hsub : ∀ j ∈ Finset.range J,
      (∫ τ in T j..T (j + 1), F τ) ≤
        (1 + η) * (2 * (h * Edir + MV * Edir) +
          2 * (Real.exp 1 * (Edual * (∫ τ in T j..T (j + 1), chiModulusWeight (2 * d) τ) +
            MV * Edual * (2 * wmax)))) +
        (1 + 1 / η) * 3 * h * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hTj4 : 4 ≤ T j := le_trans ha (hTge j)
    have hTjv : T (j + 1) ≤ v := hTle (j + 1) (by omega)
    have hTjj := hTmono j
    have hsub' := integral_normSq_zeta_mul_edPoly_subBlock_le hd hd4 hx hTj4 hTjj hη hbn
      hEdir (hEdual (T j) (hTge j) (le_trans hTjj hTjv))
      (fun τ hτ => hfreeze (T j) τ (hTge j) hτ.1 (le_trans hτ.2 hTjv)
        (by have := hTsucc j; linarith [hτ.2]))
      (fun τ hτ => hpole τ (le_trans (hTge j) hτ.1) (le_trans hτ.2 hTjv))
      (fun τ hτ => htail τ (le_trans (hTge j) hτ.1) (le_trans hτ.2 hTjv))
      (fun τ hτ => hW τ (le_trans (hTge j) hτ.1) (le_trans hτ.2 hTjv))
    refine hsub'.trans ?_
    rw [hTsucc j]
    -- e^{2d(π/T+5/T²)} ≤ e, w(T_{j+1}) ≤ wmax
    have hexp : Real.exp (2 * d * (Real.pi / T j + 5 / T j ^ (2 : ℕ))) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      have hTpos : 0 < T j := by linarith
      have h1 : Real.pi / T j ≤ Real.pi / 4 :=
        div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hTj4
      have h2 : 5 / T j ^ (2 : ℕ) ≤ 5 / 4 ^ (2 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hTj4 2)
      have h3 : 0 ≤ Real.pi / T j + 5 / T j ^ (2 : ℕ) := by positivity
      calc 2 * d * (Real.pi / T j + 5 / T j ^ (2 : ℕ)) ≤ 2 * (1 / 4) * (Real.pi / 4 + 5 / 4 ^ (2 : ℕ)) := by
            apply mul_le_mul (by linarith) (by linarith) h3 (by norm_num)
        _ ≤ 1 := by nlinarith [Real.pi_le_four]
    have hwT : chiModulusWeight (2 * d) (T (j + 1)) ≤ wmax := hw _ (hTge _) hTjv
    have hint0 : 0 ≤ ∫ τ in T j..T (j + 1), chiModulusWeight (2 * d) τ :=
      intervalIntegral.integral_nonneg hTjj fun τ hτ =>
        (chiModulusWeight_pos (by linarith [hTge j, hτ.1])).le
    have hwT0 : 0 ≤ chiModulusWeight (2 * d) (T (j + 1)) :=
      (chiModulusWeight_pos (by linarith [hTge (j + 1)])).le
    gcongr
    all_goals positivity
  -- sum over sub-blocks
  have hsplit : (∫ τ in a..v, F τ) = ∑ j ∈ Finset.range J, ∫ τ in T j..T (j + 1), F τ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hFc.intervalIntegrable _ _),
      hT0, hTJ]
  have hwsplit : (∫ τ in a..v, chiModulusWeight (2 * d) τ) =
      ∑ j ∈ Finset.range J, ∫ τ in T j..T (j + 1), chiModulusWeight (2 * d) τ := by
    have hcont : ∀ k, k < J → IntervalIntegrable (chiModulusWeight (2 * d)) volume (T k) (T (k + 1)) := by
      intro k hk
      apply ContinuousOn.intervalIntegrable
      intro τ hτ
      rw [Set.uIcc_of_le (hTmono k)] at hτ
      have hτ0 : 0 < τ := by linarith [hTge k, hτ.1]
      exact (hasDerivAt_chiModulusWeight (α := 2 * d) hτ0).continuousAt.continuousWithinAt
    rw [intervalIntegral.sum_integral_adjacent_intervals hcont, hT0, hTJ]
  have hwint : (∫ τ in a..v, chiModulusWeight (2 * d) τ) ≤ (v - a) * wmax := by
    have hgint : IntervalIntegrable (fun _ : ℝ => wmax) volume a v :=
      (continuous_const : Continuous (fun _ : ℝ => wmax)).intervalIntegrable a v
    have := intervalIntegral.integral_mono_on hav
      (f := chiModulusWeight (2 * d)) (g := fun _ => wmax) ?_ hgint (fun τ hτ => hw τ hτ.1 hτ.2)
    · rw [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this
    · apply ContinuousOn.intervalIntegrable
      intro τ hτ
      rw [Set.uIcc_of_le hav] at hτ
      have hτ0 : 0 < τ := by linarith [hτ.1]
      exact (hasDerivAt_chiModulusWeight (α := 2 * d) hτ0).continuousAt.continuousWithinAt
  have hJh : (J : ℝ) * h = v - a := by
    rw [hh]
    have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
    field_simp
    try ring
  set I : ℕ → ℝ := fun j => ∫ τ in T j..T (j + 1), chiModulusWeight (2 * d) τ with hI
  set C₁ : ℝ := (1 + η) * (2 * (h * Edir + MV * Edir) +
      2 * (Real.exp 1 * (MV * Edual * (2 * wmax)))) +
    (1 + 1 / η) * 3 * h * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) with hC₁
  set C₂ : ℝ := (1 + η) * (2 * (Real.exp 1 * Edual)) with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hbody : ∀ j : ℕ,
      (1 + η) * (2 * (h * Edir + MV * Edir) +
        2 * (Real.exp 1 * (Edual * I j + MV * Edual * (2 * wmax)))) +
      (1 + 1 / η) * 3 * h * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) =
      C₁ + C₂ * I j := fun j => by rw [hC₁, hC₂]; ring
  calc (∫ τ in a..v, F τ)
      = ∑ j ∈ Finset.range J, ∫ τ in T j..T (j + 1), F τ := hsplit
    _ ≤ ∑ j ∈ Finset.range J, (C₁ + C₂ * I j) :=
        Finset.sum_le_sum fun j hj => (hsub j hj).trans_eq (hbody j)
    _ = (J : ℝ) * C₁ + C₂ * ∫ τ in a..v, chiModulusWeight (2 * d) τ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum, ← hwsplit]
    _ ≤ (J : ℝ) * C₁ + C₂ * ((v - a) * wmax) := by gcongr
    _ = _ := by
        rw [hC₁, hC₂, ← hJh]
        ring

end

end RHTower
