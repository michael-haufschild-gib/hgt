import GaloisForLFunctions.RHTower.ZetaDerivNearOneLineBound
import GaloisForLFunctions.RHTower.ZetaThreeFourOne

/-!
# A power-of-log lower bound for `ζ` on the closed half-plane `σ ≥ 1`

The three-four-one inequality bounds `ζ` from below at `σ = 1 + δ` by `δ^{3/4}(log|t|)^{-1/4}`, which
degenerates as `δ → 0`.  Sliding the estimate leftwards along the segment costs `δ` times the
derivative bound `110 (log|t|)²`, so choosing `δ = (log|t|)^{-14}` makes the transfer error
`110 (log|t|)^{-12}` while the three-four-one term is still `≫ (log|t|)^{-43/4}`.  The result is a
bound with no dependence on the abscissa at all:

`‖ζ(σ+it)‖ ≥ c (log|t|)^{-11}` for `1 ≤ σ ≤ 5/4` and `|t|` large.

This is the input a pretentious-distance lower bound for the Möbius function consumes: it converts
`∑_{p≤x}(1+cos(t log p))/p = log log x + Re ∑_{p≤x} p^{-1-it} + O(1)` into
`≥ log log x − 11 log log(|t|+2) − O(1)`.
-/

namespace RHTower

open Complex

noncomputable section

/-- The absolute constant of the three-four-one lower bound. -/
def zetaLowerLogConst : ℝ := (-22 - 3 * Real.log 2 - Real.log 4) / 4

/-- **A power-of-log lower bound for `ζ` on `1 ≤ σ ≤ 5/4`.** -/
theorem exists_lower_bound_riemannZeta_near_one_line :
    ∃ c t₀ : ℝ, 0 < c ∧ 9 ≤ t₀ ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 5 / 4 → t₀ ≤ |t| →
      c / (Real.log |t|) ^ 11 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set K : ℝ := zetaLowerLogConst with hKdef
  refine ⟨Real.exp K / 2, max 9 (Real.exp (220 * Real.exp (-K))), by positivity,
    le_max_left _ _, ?_⟩
  intro σ t hσ1 hσ2 ht
  have ht9 : (9 : ℝ) ≤ |t| := le_trans (le_max_left _ _) ht
  have ht8 : (8 : ℝ) ≤ |t| := by linarith
  have htpos : (0 : ℝ) < |t| := by linarith
  set L : ℝ := Real.log |t| with hLdef
  have hL2 : (2 : ℝ) ≤ L := two_le_log_of_eight_le ht8
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  -- the largeness of `L`
  have hLbig : 220 * Real.exp (-K) ≤ L := by
    have h1 : Real.exp (220 * Real.exp (-K)) ≤ |t| := le_trans (le_max_right _ _) ht
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  -- the shift
  set δ : ℝ := 1 / L ^ 14 with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hL14 : (2 : ℝ) ^ 14 ≤ L ^ 14 := pow_le_pow_left₀ (by norm_num) hL2 14
  have hδsmall : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL14]
  set σ' : ℝ := σ + δ with hσ'def
  have hσ'1 : (1 : ℝ) < σ' := by rw [hσ'def]; linarith
  have hσ'2 : σ' ≤ 3 / 2 := by rw [hσ'def]; linarith
  -- the real-point bound
  have hApos : (0 : ℝ) < ‖riemannZeta (σ' : ℂ)‖ := by
    refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re ?_)
    simpa using hσ'1
  have hAval : ‖riemannZeta (σ' : ℂ)‖ ≤ 2 * L ^ 14 := by
    have hx0 : (0 : ℝ) < σ' - 1 := by linarith
    have hcast : ((σ' : ℝ) : ℂ) = 1 + ((σ' - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    have hb := abs_riemannZeta_one_add_le hx0
    have hinv : 1 / (σ' - 1) ≤ L ^ 14 := by
      rw [div_le_iff₀ hx0]
      have hδle : δ ≤ σ' - 1 := by rw [hσ'def]; linarith
      have hprod : δ * L ^ 14 = 1 := by
        rw [hδdef]
        field_simp
      nlinarith [hδle, hL14, hprod]
    have hpow : (1 : ℝ) ≤ L ^ 14 := by nlinarith [hL14]
    linarith
  have hA : Real.log ‖riemannZeta (σ' : ℂ)‖ ≤ Real.log 2 + 14 * Real.log L := by
    have h := Real.log_le_log hApos hAval
    have hval : Real.log (2 * L ^ 14) = Real.log 2 + 14 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    linarith [h, hval.le, hval.ge]
  -- the doubled-frequency bound
  have hBpos : (0 : ℝ) < ‖riemannZeta ((σ' : ℂ) + (2 * t : ℂ) * Complex.I)‖ := by
    refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re ?_)
    simpa using hσ'1
  have hBim : ((σ' : ℂ) + (2 * t : ℂ) * Complex.I).im = 2 * t := by simp
  have hBre : ((σ' : ℂ) + (2 * t : ℂ) * Complex.I).re = σ' := by simp
  have hBval : ‖riemannZeta ((σ' : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ 4 * L := by
    have hle := norm_riemannZeta_le_log_add (s := (σ' : ℂ) + (2 * t : ℂ) * Complex.I)
      (by rw [hBre]; linarith) (by rw [hBre]; linarith) (by rw [hBim, abs_mul]; simp; linarith)
    rw [hBim, abs_mul] at hle
    have habs2 : |(2 : ℝ)| = 2 := by norm_num
    rw [habs2] at hle
    have hsplit : Real.log (2 * |t|) = Real.log 2 + L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt htpos)]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith [hle, hsplit.le, hsplit.ge]
  have hB : Real.log ‖riemannZeta ((σ' : ℂ) + (2 * t : ℂ) * Complex.I)‖
      ≤ Real.log 4 + Real.log L := by
    have h := Real.log_le_log hBpos hBval
    have hval : Real.log (4 * L) = Real.log 4 + Real.log L :=
      Real.log_mul (by norm_num) (ne_of_gt hL0)
    linarith [h, hval.le, hval.ge]
  -- three-four-one
  have h341 := Sieve.log_norm_zeta_shift_ge (σ := σ') (t := t) hσ'1 hA hB
  have hshift : Real.log ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * Complex.I)‖
      ≥ K - 43 / 4 * Real.log L := by
    have : (-22 - 3 * (Real.log 2 + 14 * Real.log L) - (Real.log 4 + Real.log L)) / 4
        = K - 43 / 4 * Real.log L := by
      rw [hKdef, zetaLowerLogConst]
      ring
    linarith [h341, this.le, this.ge]
  have hshiftpos : (0 : ℝ) < ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ := by
    refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re ?_)
    simpa using hσ'1
  have hmain : Real.exp K / L ^ 11
      ≤ ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hpos : (0 : ℝ) < Real.exp K / L ^ 11 := by positivity
    have hlogval : Real.log (Real.exp K / L ^ 11) = K - 11 * Real.log L := by
      rw [Real.log_div (ne_of_gt (Real.exp_pos K)) (by positivity), Real.log_exp,
        Real.log_pow]
      push_cast
      ring
    have hle : Real.log (Real.exp K / L ^ 11)
        ≤ Real.log ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [hlogval]
      linarith [hshift, hlogL0]
    exact (Real.log_le_log_iff hpos hshiftpos).mp hle
  -- the transfer along the segment
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hzdef
  set w : ℂ := (σ' : ℂ) + (t : ℂ) * Complex.I with hwdef
  have hwz : w - z = ((δ : ℝ) : ℂ) := by
    rw [hwdef, hzdef, hσ'def]
    push_cast
    ring
  have hpt : ∀ u : ℝ, z + (u : ℂ) * (w - z)
      = ((σ + u * δ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro u
    rw [hwz, hzdef]
    push_cast
    ring
  have hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, z + (u : ℂ) * (w - z) ≠ 1 := by
    intro u _ hcon
    have him := congrArg Complex.im hcon
    rw [hpt u] at him
    have ht0 : t = 0 := by simpa using him
    rw [ht0, abs_zero] at ht9
    linarith
  have hM : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv riemannZeta (z + (u : ℂ) * (w - z))‖ ≤ 110 * L ^ 2 := by
    intro u hu
    rw [hpt u]
    have hre : (((σ + u * δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = σ + u * δ := by simp
    have him : (((σ + u * δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have hu0 : (0 : ℝ) ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hud : u * δ ≤ δ := by nlinarith [hδ0]
    have hud0 : (0 : ℝ) ≤ u * δ := by positivity
    have hbound := norm_deriv_riemannZeta_le_log_sq
      (s := ((σ + u * δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; linarith)
    rw [him] at hbound
    exact hbound
  have hseg := Sieve.norm_riemannZeta_sub_le (z := z) (c := w) (M := 110 * L ^ 2) hne hM
  have hnormwz : ‖w - z‖ = δ := by
    rw [hwz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
  rw [hnormwz] at hseg
  have herr : 110 * L ^ 2 * δ * 1 = 110 / L ^ 12 := by
    rw [hδdef]
    field_simp
  rw [herr] at hseg
  -- assemble
  have hLpow : (0 : ℝ) < L ^ 11 := by positivity
  have hsplit : (110 : ℝ) / L ^ 12 = (110 / L) / L ^ 11 := by
    field_simp
  have hsmall : (110 : ℝ) / L ≤ Real.exp K / 2 := by
    rw [div_le_iff₀ hL0]
    have hexp : (0 : ℝ) < Real.exp K := Real.exp_pos K
    have hinv : Real.exp (-K) * Real.exp K = 1 := by
      rw [← Real.exp_add]
      simp
    have hstep := mul_le_mul_of_nonneg_right hLbig hexp.le
    have h220 : (220 : ℝ) ≤ L * Real.exp K := by nlinarith [hstep, hinv]
    linarith [h220]
  have hfin : Real.exp K / 2 / L ^ 11 ≤ ‖riemannZeta z‖ := by
    have hstep : Real.exp K / L ^ 11 - 110 / L ^ 12 ≤ ‖riemannZeta z‖ := by
      have hd : ‖riemannZeta w‖ - ‖riemannZeta z‖ ≤ ‖riemannZeta w - riemannZeta z‖ :=
        norm_sub_norm_le _ _
      linarith [hseg, hmain, hd]
    rw [hsplit] at hstep
    have hdiv : (110 / L) / L ^ 11 ≤ (Real.exp K / 2) / L ^ 11 :=
      div_le_div_of_nonneg_right hsmall hLpow.le
    have hhalf : Real.exp K / L ^ 11 - (Real.exp K / 2) / L ^ 11
        = (Real.exp K / 2) / L ^ 11 := by
      field_simp
      ring
    linarith [hstep, hdiv, hhalf.le, hhalf.ge]
  exact hfin

end

end RHTower
