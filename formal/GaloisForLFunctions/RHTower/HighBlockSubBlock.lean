import GaloisForLFunctions.RHTower.HighBlockFreezing
import GaloisForLFunctions.RHTower.HighBlockDirectMeanSquare
import GaloisForLFunctions.RHTower.HighBlockDualMeanSquare
import GaloisForLFunctions.RHTower.DyadicLawLowBlocks

/-!
# High-block law: the mean square on one sub-block

On a sub-block `[T, T']` the exact truncated AFE gives
`ζΨ = (D_L + χ H_T)Ψ + (χ(H_τ − H_T) − Pole + Tail)Ψ`.
The first part is two Dirichlet polynomials in `τ` (B4, B5); the second is bounded pointwise by
the freezing, pole and tail constants. With Young's `‖F+E‖² ≤ (1+η)‖F‖² + (1+1/η)‖E‖²`:

`∫_T^{T'} ‖ζΨ‖² ≤ (1+η)[2(h E_dir + MV_dir) + 2 e^{ε_T}(E_dual ∫ w + MV_dual · 2w(T'))]
                 + (1+1/η)·3h·N²(W_sup E_freeze² + E_pole² + E_tail²)`.
-/

open Complex Set Finset MeasureTheory

namespace RHTower

noncomputable section

/-! ### Continuity along the displaced line -/

theorem continuous_displacedLinePt (d : ℝ) : Continuous (fun τ : ℝ => displacedLinePt d τ) := by
  unfold displacedLinePt
  fun_prop

theorem continuous_riemannZeta_displacedLinePt {d : ℝ} (hd : 0 < d) :
    Continuous (fun τ : ℝ => riemannZeta (displacedLinePt d τ)) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have hne : displacedLinePt d τ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [displacedLinePt_re] at this
    simp at this
    linarith
  exact ContinuousAt.comp (f := fun τ : ℝ => displacedLinePt d τ)
    (differentiableAt_riemannZeta hne).continuousAt (continuous_displacedLinePt d).continuousAt

theorem continuous_edPoly_displacedLinePt (b : ℕ → ℂ) (N : ℕ) (d : ℝ) :
    Continuous (fun τ : ℝ => edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)) := by
  unfold edPoly
  refine continuous_finset_sum _ fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact_mod_cast this.ne'
  exact continuous_const.mul
    (Continuous.const_cpow (continuous_displacedLinePt d).neg (Or.inl hn0))

theorem continuous_sum_directTerm (d x : ℝ) (L : ℕ) :
    Continuous (fun τ : ℝ => ∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) := by
  refine continuous_finset_sum _ fun n _ => ?_
  unfold smoothAFEZetaDisplacedDirectTerm
  have hn0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (Continuous.const_cpow (continuous_displacedLinePt d).neg (Or.inl hn0)).mul continuous_const

theorem continuous_highBlockDualHeadFrozen (d x T : ℝ) (L : ℕ) :
    Continuous (fun τ : ℝ => highBlockDualHeadFrozen d x T τ L) := by
  unfold highBlockDualHeadFrozen
  refine continuous_finset_sum _ fun n _ => ?_
  have hn0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (Continuous.const_cpow ((continuous_displacedLinePt d).sub continuous_const)
    (Or.inl hn0)).mul continuous_const

/-! ### Elementary square inequalities -/

theorem sq_add_le_young {p q η : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hη : 0 < η) :
    (p + q) ^ (2 : ℕ) ≤ (1 + η) * p ^ (2 : ℕ) + (1 + 1 / η) * q ^ (2 : ℕ) := by
  have h : 2 * p * q ≤ η * p ^ (2 : ℕ) + (1 / η) * q ^ (2 : ℕ) := by
    have hid : η * p ^ (2 : ℕ) + (1 / η) * q ^ (2 : ℕ) - 2 * p * q = (η * p - q) ^ (2 : ℕ) / η := by
      field_simp
      ring
    have h0 : 0 ≤ (η * p - q) ^ (2 : ℕ) / η := by positivity
    linarith [hid, h0]
  have hexp : (p + q) ^ (2 : ℕ) = p ^ (2 : ℕ) + 2 * p * q + q ^ (2 : ℕ) := by ring
  linarith [h, hexp]

theorem sq_add_three_le {p q r : ℝ} (_hp : 0 ≤ p) (_hq : 0 ≤ q) (_hr : 0 ≤ r) :
    (p + q + r) ^ (2 : ℕ) ≤ 3 * (p ^ (2 : ℕ) + q ^ (2 : ℕ) + r ^ (2 : ℕ)) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]

theorem sq_add_two_le {p q : ℝ} (_hp : 0 ≤ p) (_hq : 0 ≤ q) :
    (p + q) ^ (2 : ℕ) ≤ 2 * (p ^ (2 : ℕ) + q ^ (2 : ℕ)) := by
  nlinarith [sq_nonneg (p - q)]

/-! ### The sub-block estimate -/

/-- **One sub-block.** All constants are abstract; they are supplied by the bricks. -/
theorem integral_normSq_zeta_mul_edPoly_subBlock_le
    {d x T T' η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x) (hT : 4 ≤ T) (hTT' : T ≤ T')
    (hη : 0 < η) {b : ℕ → ℂ} {N L : ℕ} (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    {Edir Edual Efreeze Epole Etail Wsup : ℝ}
    (hEdir : highBlockDirectEnergy d x b L N ≤ Edir)
    (hEdual : highBlockDualEnergy d x T L N (fun m => highBlockMollifierCoeffNat d b m) ≤ Edual)
    (hfreeze : ∀ τ ∈ Set.Icc T T',
      ‖highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L‖ ≤ Efreeze)
    (hpole : ∀ τ ∈ Set.Icc T T',
      ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x‖ ≤ Epole)
    (htail : ∀ τ ∈ Set.Icc T T', ‖highBlockAFETail d x τ L‖ ≤ Etail)
    (hW : ∀ τ ∈ Set.Icc T T', ‖zetaChi (displacedLinePt d τ)‖ ^ (2 : ℕ) ≤ Wsup) :
    (∫ τ in T..T', ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ (2 : ℕ)) ≤
      (1 + η) * (2 * ((T' - T) * Edir +
          8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edir) +
        2 * (Real.exp (2 * d * (Real.pi / T + 5 / T ^ (2 : ℕ))) *
          (Edual * (∫ τ in T..T', chiModulusWeight (2 * d) τ) +
            8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edual *
              (2 * chiModulusWeight (2 * d) T')))) +
      (1 + 1 / η) * 3 * (T' - T) *
        ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
  have hT0 : 0 < T := by linarith
  have hdhalf : d < 1 / 2 := by linarith
  set Ψ : ℝ → ℂ := fun τ => edPoly b (Finset.Icc 1 N) (displacedLinePt d τ) with hΨ
  set D : ℝ → ℂ := fun τ => ∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n with hD
  set HT : ℝ → ℂ := fun τ => highBlockDualHeadFrozen d x T τ L with hHT
  set χ : ℝ → ℂ := fun τ => zetaChi (displacedLinePt d τ) with hχ
  -- nonnegativity of the constants (from a point of the sub-block)
  have hTmem : T ∈ Set.Icc T T' := Set.left_mem_Icc.mpr hTT'
  have hEf0 : 0 ≤ Efreeze := le_trans (norm_nonneg _) (hfreeze T hTmem)
  have hEp0 : 0 ≤ Epole := le_trans (norm_nonneg _) (hpole T hTmem)
  have hEt0 : 0 ≤ Etail := le_trans (norm_nonneg _) (htail T hTmem)
  have hWs0 : 0 ≤ Wsup := le_trans (by positivity) (hW T hTmem)
  have hΨb : ∀ τ : ℝ, ‖Ψ τ‖ ≤ N := fun τ =>
    norm_edPoly_le_card hbn (by rw [displacedLinePt_re]; linarith)
  -- pointwise inequality
  have hpoint : ∀ τ ∈ Set.Icc T T',
      ‖riemannZeta (displacedLinePt d τ) * Ψ τ‖ ^ (2 : ℕ) ≤
        (1 + η) * (2 * ‖D τ * Ψ τ‖ ^ (2 : ℕ) + 2 * ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) +
        (1 + 1 / η) * 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
    intro τ hτ
    have hAFE := riemannZeta_displaced_eq_truncated hx hd hdhalf τ L
    rw [sum_highBlockDualTerm_eq] at hAFE
    -- ζ Ψ = F + E
    have hsplit : riemannZeta (displacedLinePt d τ) * Ψ τ =
        (D τ + χ τ * HT τ) * Ψ τ +
        (χ τ * (highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L) -
          smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x + highBlockAFETail d x τ L) *
          Ψ τ := by
      rw [hAFE]
      simp only [hD, hχ, hHT]
      ring
    rw [hsplit]
    set F := (D τ + χ τ * HT τ) * Ψ τ with hF
    set E := (χ τ * (highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L) -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x + highBlockAFETail d x τ L) *
        Ψ τ with hE
    have hFE : ‖F + E‖ ^ (2 : ℕ) ≤ (1 + η) * ‖F‖ ^ (2 : ℕ) + (1 + 1 / η) * ‖E‖ ^ (2 : ℕ) :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le F E) 2)
        (sq_add_le_young (norm_nonneg _) (norm_nonneg _) hη)
    have hFb : ‖F‖ ^ (2 : ℕ) ≤ 2 * ‖D τ * Ψ τ‖ ^ (2 : ℕ) + 2 * ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ) := by
      have h1 : ‖F‖ ≤ ‖D τ * Ψ τ‖ + ‖χ τ * HT τ * Ψ τ‖ := by
        rw [hF, add_mul]
        exact norm_add_le _ _
      calc ‖F‖ ^ (2 : ℕ) ≤ (‖D τ * Ψ τ‖ + ‖χ τ * HT τ * Ψ τ‖) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ 2 * (‖D τ * Ψ τ‖ ^ (2 : ℕ) + ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) :=
            sq_add_two_le (norm_nonneg _) (norm_nonneg _)
        _ = 2 * ‖D τ * Ψ τ‖ ^ (2 : ℕ) + 2 * ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ) := by ring
    have hEb : ‖E‖ ^ (2 : ℕ) ≤ 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
      have hχτ : ‖χ τ‖ ^ (2 : ℕ) ≤ Wsup := hW τ hτ
      have hχ0 : 0 ≤ ‖χ τ‖ := norm_nonneg _
      have hfr := hfreeze τ hτ
      have hpo := hpole τ hτ
      have hta := htail τ hτ
      have hΨ := hΨb τ
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h1 : ‖E‖ ≤ (‖χ τ‖ * Efreeze + Epole + Etail) * N := by
        rw [hE, norm_mul]
        refine mul_le_mul ?_ hΨ (norm_nonneg _) (by positivity)
        calc ‖χ τ * (highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L) -
              smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x + highBlockAFETail d x τ L‖
            ≤ ‖χ τ * (highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L) -
                smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x‖ +
              ‖highBlockAFETail d x τ L‖ := norm_add_le _ _
          _ ≤ (‖χ τ * (highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L)‖ +
                ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x‖) +
              ‖highBlockAFETail d x τ L‖ := by gcongr; exact norm_sub_le _ _
          _ ≤ (‖χ τ‖ * Efreeze + Epole) + Etail := by
              gcongr
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left hfr hχ0
      have h2 : ((‖χ τ‖ * Efreeze + Epole + Etail) * N) ^ (2 : ℕ) =
          (N : ℝ) ^ (2 : ℕ) * (‖χ τ‖ * Efreeze + Epole + Etail) ^ (2 : ℕ) := by ring
      calc ‖E‖ ^ (2 : ℕ) ≤ ((‖χ τ‖ * Efreeze + Epole + Etail) * N) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (N : ℝ) ^ (2 : ℕ) * (‖χ τ‖ * Efreeze + Epole + Etail) ^ (2 : ℕ) := h2
        _ ≤ (N : ℝ) ^ (2 : ℕ) * (3 * ((‖χ τ‖ * Efreeze) ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
            gcongr
            exact sq_add_three_le (by positivity) hEp0 hEt0
        _ ≤ (N : ℝ) ^ (2 : ℕ) * (3 * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by
            gcongr
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right hχτ (by positivity)
        _ = 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))) := by ring
    have h1η : 0 ≤ 1 + 1 / η := by positivity
    calc ‖F + E‖ ^ (2 : ℕ) ≤ (1 + η) * ‖F‖ ^ (2 : ℕ) + (1 + 1 / η) * ‖E‖ ^ (2 : ℕ) := hFE
      _ ≤ (1 + η) * (2 * ‖D τ * Ψ τ‖ ^ (2 : ℕ) + 2 * ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) +
          (1 + 1 / η) * (3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ)))) :=
          add_le_add (mul_le_mul_of_nonneg_left hFb (by positivity))
            (mul_le_mul_of_nonneg_left hEb h1η)
      _ = _ := by ring
  -- continuity
  have hΨc : Continuous Ψ := continuous_edPoly_displacedLinePt b N d
  have hDc : Continuous D := continuous_sum_directTerm d x L
  have hHTc : Continuous HT := continuous_highBlockDualHeadFrozen d x T L
  have hχc : Continuous χ := continuous_zetaChi_displacedLinePt_highBlockDualMeanSquare hd.le
  have hζc : Continuous (fun τ => riemannZeta (displacedLinePt d τ)) :=
    continuous_riemannZeta_displacedLinePt hd
  have hint1 : IntervalIntegrable
      (fun τ => ‖riemannZeta (displacedLinePt d τ) * Ψ τ‖ ^ (2 : ℕ)) volume T T' :=
    ((hζc.mul hΨc).norm.pow 2).intervalIntegrable T T'
  have hg1 : Continuous (fun τ => ‖D τ * Ψ τ‖ ^ (2 : ℕ)) := (hDc.mul hΨc).norm.pow 2
  have hg2 : Continuous (fun τ => ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) := ((hχc.mul hHTc).mul hΨc).norm.pow 2
  have hint2 : IntervalIntegrable (fun τ =>
      (1 + η) * (2 * ‖D τ * Ψ τ‖ ^ (2 : ℕ) + 2 * ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) +
        (1 + 1 / η) * 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))))
      volume T T' :=
    (((continuous_const.mul (hg1.const_mul 2 |>.add (hg2.const_mul 2))).add
      continuous_const)).intervalIntegrable T T'
  have hmono := intervalIntegral.integral_mono_on hTT' hint1 hint2 hpoint
  refine hmono.trans ?_
  -- evaluate the right-hand integral
  have hf1 : IntervalIntegrable
      (fun u => (1 + η) * (2 * ‖D u * Ψ u‖ ^ (2 : ℕ) + 2 * ‖χ u * HT u * Ψ u‖ ^ (2 : ℕ))) volume T T' :=
    (continuous_const.mul ((hg1.const_mul 2).add (hg2.const_mul 2))).intervalIntegrable T T'
  have hf2 : IntervalIntegrable (fun _ : ℝ =>
      (1 + 1 / η) * 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ)))) volume T T' :=
    continuous_const.intervalIntegrable T T'
  have hf3 : IntervalIntegrable (fun u => 2 * ‖D u * Ψ u‖ ^ (2 : ℕ)) volume T T' :=
    (hg1.const_mul 2).intervalIntegrable T T'
  have hf4 : IntervalIntegrable (fun u => 2 * ‖χ u * HT u * Ψ u‖ ^ (2 : ℕ)) volume T T' :=
    (hg2.const_mul 2).intervalIntegrable T T'
  rw [intervalIntegral.integral_add hf1 hf2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hf3 hf4,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- B4 and B5
  have hB4 := abs_integral_normSq_highBlockDirect_sub_le d x b L N T T'
  have hdir : (∫ τ in T..T', ‖D τ * Ψ τ‖ ^ (2 : ℕ)) ≤
      (T' - T) * Edir + 8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edir := by
    have h := (abs_le.mp hB4).2
    have hE0 : 0 ≤ highBlockDirectEnergy d x b L N :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hlog : 0 ≤ Real.log ((L * N : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hLN : (0 : ℝ) ≤ ((L * N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmv : 8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) *
        highBlockDirectEnergy d x b L N ≤
        8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edir :=
      mul_le_mul_of_nonneg_left hEdir (by positivity)
    have hmain : (T' - T) * highBlockDirectEnergy d x b L N ≤ (T' - T) * Edir :=
      mul_le_mul_of_nonneg_left hEdir (by linarith)
    simp only [hD, hΨ] at h ⊢
    linarith
  have hB5 := integral_normSq_chi_mul_highBlockDualFrozen_le hd.le hd4 hT0 hTT' x T L N
    (fun m => highBlockMollifierCoeffNat d b m)
  have hdual : (∫ τ in T..T', ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) ≤
      Real.exp (2 * d * (Real.pi / T + 5 / T ^ (2 : ℕ))) *
        (Edual * (∫ τ in T..T', chiModulusWeight (2 * d) τ) +
          8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edual *
            (2 * chiModulusWeight (2 * d) T')) := by
    have hΨeq : ∀ τ, Ψ τ = Sieve.dirPoly N (fun m => highBlockMollifierCoeffNat d b m) (-τ) :=
      fun τ => edPoly_Icc_eq_dirPoly d τ b N
    have hint : (∫ τ in T..T', ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ)) =
        ∫ τ in T..T', ‖zetaChi (displacedLinePt d τ) * highBlockDualHeadFrozen d x T τ L *
          Sieve.dirPoly N (fun m => highBlockMollifierCoeffNat d b m) (-τ)‖ ^ (2 : ℕ) := by
      refine intervalIntegral.integral_congr fun τ _ => ?_
      simp only [hχ, hHT, hΨeq]
    rw [hint]
    refine hB5.trans ?_
    have hw0 : 0 ≤ ∫ τ in T..T', chiModulusWeight (2 * d) τ :=
      intervalIntegral.integral_nonneg hTT' fun τ hτ =>
        (chiModulusWeight_pos (lt_of_lt_of_le hT0 hτ.1)).le
    have hwT' : 0 ≤ chiModulusWeight (2 * d) T' := (chiModulusWeight_pos (by linarith)).le
    have hE0 : 0 ≤ highBlockDualEnergy d x T L N (fun m => highBlockMollifierCoeffNat d b m) :=
      Finset.sum_nonneg fun _ _ => by positivity
    gcongr
  have hh : 0 ≤ T' - T := by linarith
  calc (1 + η) * (2 * (∫ τ in T..T', ‖D τ * Ψ τ‖ ^ (2 : ℕ)) + 2 * (∫ τ in T..T', ‖χ τ * HT τ * Ψ τ‖ ^ (2 : ℕ))) +
        (T' - T) • ((1 + 1 / η) * 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ))))
      ≤ (1 + η) * (2 * ((T' - T) * Edir +
            8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edir) +
          2 * (Real.exp (2 * d * (Real.pi / T + 5 / T ^ (2 : ℕ))) *
            (Edual * (∫ τ in T..T', chiModulusWeight (2 * d) τ) +
              8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) * Edual *
                (2 * chiModulusWeight (2 * d) T')))) +
        (T' - T) • ((1 + 1 / η) * 3 * ((N : ℝ) ^ (2 : ℕ) * (Wsup * Efreeze ^ (2 : ℕ) + Epole ^ (2 : ℕ) + Etail ^ (2 : ℕ)))) := by
        gcongr
    _ = _ := by
        rw [smul_eq_mul]
        ring

end

end RHTower
