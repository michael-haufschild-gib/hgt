import GaloisForLFunctions.GrowingWindowsOfSpecZ.SpecZIsACurveOnEveryLattice
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheFirstMarginIsBornQuadratically

/-!
# The higher margins are born later

The first margin of a bump is born at order `h²` (`tendsto_levinsonErr_one_div_sq`). The higher
margins are born later, and the folded zero curve says how much later:

* **The `n`-th margin is at most the `n`-th Frobenius difference** (`levinsonErr_le_tsum_diff`):
  under RH, testing the window on `Σ_k(−1)^kC(n, k)e_k`, whose polynomial is `(1 − z)^n`
  (`sum_diffVec_mul_pow`), gives
  `E_n(φ, h) ≤ Σ_ρ w_ρ(2 − 2cos γ_ρh)^n ≤ h^{2n}Σ_ρ w_ργ_ρ^{2n}`.
* **Only the first margin is born at order `h²`** (`tendsto_levinsonErr_div_sq_of_two_le`): for
  `n ≥ 2`, `E_n(φ, h)/h² → 0`, by dominated convergence with the majorant `4w_ργ_ρ²`, summable for
  every `C²` bump (`summable_zeroTerm_mul_sq`).
* **The second-order jet law** (`tendsto_levinsonErr_div_sq`): for `n ≥ 1`,
  `h⁻²E_n(φ, h) → M₂(φ)` if `n = 1` and `→ 0` if `n ≥ 2`.

At second order the continuum canonical system of a bump is one number, the zero energy of `φ'`; the
`n`-th margin lives at order `h^{2n}`, where the jet system continues with the higher zero moments.
-/

noncomputable section

open Finset Complex Filter Topology Set

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis Zeta23 RHTower.WeilConditional

variable {φ : ℝ → ℝ}

/-- The `n`-th Frobenius difference `Σ_k(−1)^kC(n, k)e_k`. -/
def diffVec (n : ℕ) : Fin (n + 1) → ℝ := fun k => (-1) ^ (k : ℕ) * (n.choose k : ℝ)

theorem diffVec_zero (n : ℕ) : diffVec n 0 = 1 := by simp [diffVec]

/-- The polynomial of the `n`-th Frobenius difference is `(1 − z)^n`. -/
theorem sum_diffVec_mul_pow (n : ℕ) (z : ℂ) :
    ∑ k : Fin (n + 1), (diffVec n k : ℂ) * z ^ (k : ℕ) = (1 - z) ^ n := by
  refine (Fin.sum_univ_eq_sum_range
    (fun m => ((((-1 : ℝ) ^ m * (n.choose m : ℝ) : ℝ) : ℂ) * z ^ m)) (n + 1)).trans ?_
  rw [sub_eq_neg_add, add_pow]
  refine sum_congr rfl fun m _ => ?_
  push_cast
  rw [one_pow, mul_one, neg_pow]
  ring

/-- `|(1 − e^{iθ})^n|² = (2 − 2cos θ)^n`. -/
theorem norm_one_sub_cexp_pow_sq (θ : ℝ) (n : ℕ) :
    ‖(1 - cexp (θ * I)) ^ n‖ ^ 2 = (2 * (1 - Real.cos θ)) ^ n := by
  rw [norm_pow, ← pow_mul, mul_comm n 2, pow_mul, RHTower.norm_one_sub_cexp_ofReal_mul_I_sq]

/-- Under RH every lattice window of a nonzero bump is positive definite. -/
theorem posDef_weilSeq_of_rh (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {h : ℝ} (hh : 0 < h) (n : ℕ) : ToeplitzPosDef (weilSeq φ h) n := by
  rcases n with _ | m
  · intro x hx
    exact absurd (funext fun k => k.elim0) hx
  · exact (toeplitzForm_posDef_iff (weilSeq_isEven φ h) m).mpr fun k _ =>
      riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh k

/-- **The `n`-th margin is at most the `n`-th Frobenius difference** (under RH):
`E_n(φ, h) ≤ Σ_ρ w_ρ(2 − 2cos γ_ρh)^n`. -/
theorem levinsonErr_le_tsum_diff (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {h : ℝ} (hh : 0 < h) (n : ℕ) :
    levinsonErr (weilSeq φ h) n ≤
      ∑' ρ, zeroTerm (cx φ) ρ * (2 * (1 - Real.cos ((ρ : ℂ).im * h))) ^ n := by
  have hpos := fun k => riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh k
  have hle := levinsonErr_le_toeplitzForm (weilSeq_isEven φ h) (posDef_weilSeq_of_rh hRH hφ hφ0 hh n)
    (fun k _ => (hpos k).ne') (Fin.tail (diffVec n))
  rw [show (Fin.cons 1 (Fin.tail (diffVec n)) : Fin (n + 1) → ℝ) = diffVec n by
    rw [← diffVec_zero n]; exact Fin.cons_self_tail _, toeplitzForm_weilSeq_eq_tsum hRH hφ] at hle
  refine hle.trans_eq (tsum_congr fun ρ => ?_)
  rw [sum_diffVec_mul_pow, norm_one_sub_cexp_pow_sq]

/-- `0 ≤ 2(1 − cos x) ≤ x²`. -/
theorem two_mul_one_sub_cos_le (x : ℝ) : 0 ≤ 2 * (1 - Real.cos x) ∧ 2 * (1 - Real.cos x) ≤ x ^ 2 :=
  ⟨by linarith [Real.cos_le_one x], by linarith [Real.one_sub_sq_div_two_le_cos (x := x)]⟩

/-- `(2 − 2cos γh)²/h² → 0` as `h → 0⁺`. -/
theorem tendsto_diff_sq_div_sq (γ : ℝ) :
    Tendsto (fun h : ℝ => (2 * (1 - Real.cos (γ * h))) ^ 2 / h ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun h : ℝ => γ ^ 4 * h ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun h : ℝ => h ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    have := (h0.const_mul (γ ^ 4)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [mul_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun h => by positivity) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh2 : 0 < h ^ 2 := by have : (0 : ℝ) < h := hh; positivity
  obtain ⟨h1, h2⟩ := two_mul_one_sub_cos_le (γ * h)
  rw [div_le_iff₀ hh2]
  calc (2 * (1 - Real.cos (γ * h))) ^ 2 ≤ ((γ * h) ^ 2) ^ 2 := pow_le_pow_left₀ h1 h2 2
    _ = γ ^ 4 * h ^ 2 * h ^ 2 := by ring

/-- **Only the first margin is born at order `h²`** (under RH): `E_n(φ, h)/h² → 0` for `n ≥ 2`. -/
theorem tendsto_levinsonErr_div_sq_of_two_le (hRH : RiemannHypothesis) (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) n / h ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hsum := summable_zeroTerm_mul_sq hRH hφ
  -- the second Frobenius difference, divided by `h²`, tends to `0`
  have hdom : Tendsto (fun h => ∑' ρ, zeroTerm (cx φ) ρ *
      ((2 * (1 - Real.cos ((ρ : ℂ).im * h))) ^ 2 / h ^ 2)) (𝓝[>] 0)
      (𝓝 (∑' ρ : zetaZeroConfig.carrier, zeroTerm (cx φ) ρ * 0)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun ρ => 4 * (zeroTerm (cx φ) ρ * (ρ : ℂ).im ^ 2)) (hsum.mul_left 4)
      (fun ρ => (tendsto_diff_sq_div_sq _).const_mul _) ?_
    refine Eventually.of_forall fun h ρ => ?_
    have hw : 0 ≤ zeroTerm (cx φ) ρ := zeroTerm_nonneg _ _
    obtain ⟨h1, h2⟩ := two_mul_one_sub_cos_le ((ρ : ℂ).im * h)
    have h3 : 2 * (1 - Real.cos ((ρ : ℂ).im * h)) ≤ 4 := by
      linarith [Real.neg_one_le_cos ((ρ : ℂ).im * h)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (by positivity))]
    rw [show 4 * (zeroTerm (cx φ) ρ * (ρ : ℂ).im ^ 2) =
      zeroTerm (cx φ) ρ * (4 * (ρ : ℂ).im ^ 2) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hw
    rcases eq_or_ne h 0 with rfl | hne
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
    · rw [div_le_iff₀ (by positivity)]
      calc (2 * (1 - Real.cos ((ρ : ℂ).im * h))) ^ 2 ≤ 4 * (2 * (1 - Real.cos ((ρ : ℂ).im * h))) := by
            nlinarith
        _ ≤ 4 * ((ρ : ℂ).im * h) ^ 2 := by linarith
        _ = 4 * (ρ : ℂ).im ^ 2 * h ^ 2 := by ring
  simp only [mul_zero, tsum_zero] at hdom
  have hpos : ∀ h : ℝ, 0 < h → ∀ m, 0 < levinsonErr (weilSeq φ h) m := fun h hh m =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh m
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact div_nonneg (hpos h hh n).le (sq_nonneg h)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    -- `E_n ≤ E_2 ≤ Σ_ρ w_ρ(2 − 2cos γ_ρh)²`
    have hmono : levinsonErr (weilSeq φ h) n ≤ levinsonErr (weilSeq φ h) 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      induction k with
      | zero => simp
      | succ k ih => exact (levinsonErr_succ_le (hpos h hh _)).trans (ih (by omega))
    have hb := hmono.trans (levinsonErr_le_tsum_diff hRH hφ hφ0 hh 2)
    calc levinsonErr (weilSeq φ h) n / h ^ 2
        ≤ (∑' ρ, zeroTerm (cx φ) ρ * (2 * (1 - Real.cos ((ρ : ℂ).im * h))) ^ 2) / h ^ 2 :=
          div_le_div_of_nonneg_right hb (sq_nonneg h)
      _ = _ := by
          rw [← tsum_div_const]
          exact tsum_congr fun ρ => by ring

/-- **The second-order jet law** (under RH): for `n ≥ 1`, `h⁻²E_n(φ, h) → M₂(φ)` if `n = 1` and
`→ 0` if `n ≥ 2`. -/
theorem tendsto_levinsonErr_div_sq (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) n / h ^ 2) (𝓝[>] 0)
      (𝓝 (if n = 1 then zeroSecondMoment φ else 0)) := by
  split_ifs with h1
  · subst h1
    exact (tendsto_levinsonErr_one_div_sq hRH hφ hφ0).mono_left
      (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')
  · exact tendsto_levinsonErr_div_sq_of_two_le hRH hφ hφ0 (by omega)

end GaloisForLFunctions.GrowingWindowsOfSpecZ
