import GaloisForLFunctions.RHTower.SelbergCuspMellinEstimates

/-!
# The cusp Mellin–Barnes integral on far-left lines

For `y > 0` let `g(u) = (2πy)^{-u} Γ(u) F(s + u/d)`, and consider the lines
`Re u = -K - 1/2`.  Along such a line (writing `u = -K - 1/2 + it`, `w = s + u/d`):

* `‖(2πy)^{-u}‖ = (2πy)^{K+1/2}` and `‖Γ(u)‖ ≤ π√2 e^{-π|t|/2}/Γ(K+3/2)`;
* the asymmetric functional equation gives `F(w) = ω S(w) H(w) F̄(1-w̄)`: the sine factor is at
  most `C e^{π|t|/2}`, cancelling the Gamma decay exactly; the reflected Dirichlet series is at
  most `C m₀^{-(1 - Re w)}`; and in `H(w)` every Gamma value is at most `Γ` of its real part,
  one of them with the extra Cauchy factor `(1 + Y(t)²/(X+1)²)^{-1}`.

So `‖g(u)‖ ≤ A_K (1 + Y(t)²/(X_K+1)²)^{-1}` with `A_K` independent of `t`
(`ExtendedSelbergClass.eventually_norm_cuspMellinIntegrand_left_le`), the integral over the line
is at most `π A_K (X_K+1) d/λ`, and the `K`-th root of this bound tends to `y/Δ(0)`,
`Δ(0) = d(m₀/q)^{1/d}` the cusp gap.  Hence for `0 < y < Δ(0)` the far-left integrals tend to zero
(`ExtendedSelbergClass.tendsto_integral_cuspMellinIntegrand_left`).
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SelbergClass

namespace RHTower

noncomputable section

variable (F : ExtendedSelbergClass)

/-- The base point `s - 1/(2d)` of the far-left lines. -/
def ExtendedSelbergClass.leftBase (s : ℂ) : ℂ := s - 1 / (2 * (F.gammaData.degree : ℂ))

/-- The real part of the `i`-th Gamma argument of `H` on the line `Re u = -K - 1/2`. -/
def ExtendedSelbergClass.leftGammaRe (s : ℂ) (i : Fin F.gammaData.rank ⊕ Fin F.gammaData.rank)
    (K : ℕ) : ℝ :=
  F.gammaData.pairRate i * K + (F.gammaData.pairShift (F.leftBase s) i).re

/-- The shifted base carrying the height `t`. -/
def ExtendedSelbergClass.leftBaseAt (s : ℂ) (t : ℝ) : ℂ :=
  F.leftBase s + (((t / F.gammaData.degree : ℝ)) : ℂ) * I

theorem ExtendedSelbergClass.add_leftLine_div (hd : 0 < F.gammaData.degree) (s : ℂ) (K : ℕ)
    (t : ℝ) :
    s + ((((-(K : ℝ) - 1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I) / (F.gammaData.degree : ℂ) =
      F.leftBaseAt s t - (K : ℂ) / (F.gammaData.degree : ℂ) := by
  have hdne : (F.gammaData.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  simp only [ExtendedSelbergClass.leftBaseAt, ExtendedSelbergClass.leftBase]
  push_cast
  field_simp
  ring

theorem ExtendedSelbergClass.leftBaseAt_re (s : ℂ) (t : ℝ) :
    (F.leftBaseAt s t).re = (F.leftBase s).re := by
  simp [ExtendedSelbergClass.leftBaseAt]

theorem SelbergGammaData.pairShift_re_eq_of_re_eq (G : SelbergGammaData) {b b' : ℂ}
    (h : b.re = b'.re) (i : Fin G.rank ⊕ Fin G.rank) :
    (G.pairShift b i).re = (G.pairShift b' i).re := by
  cases i with
  | inl j =>
      simp [SelbergGammaData.pairShift, SelbergGammaData.shiftUp, Complex.mul_re, h]
  | inr j =>
      simp [SelbergGammaData.pairShift, SelbergGammaData.shiftDown, Complex.mul_re, h]

theorem SelbergGammaData.pairShift_inl_im (G : SelbergGammaData) (b : ℂ) (j : Fin G.rank) :
    (G.pairShift b (Sum.inl j)).im = -(G.lambda j * b.im) - (G.mu j).im := by
  simp [SelbergGammaData.pairShift, SelbergGammaData.shiftUp, Complex.mul_im]
  ring

/-- The height function of the distinguished Gamma factor on the far-left lines. -/
def ExtendedSelbergClass.leftHeight (s : ℂ) (j₀ : Fin F.gammaData.rank) (t : ℝ) : ℝ :=
  (F.gammaData.pairShift (F.leftBaseAt s t) (Sum.inl j₀)).im

theorem ExtendedSelbergClass.leftHeight_eq (s : ℂ) (j₀ : Fin F.gammaData.rank) (t : ℝ) :
    F.leftHeight s j₀ t = (-(F.gammaData.lambda j₀ * s.im) - (F.gammaData.mu j₀).im) +
      (-(F.gammaData.lambda j₀ / F.gammaData.degree)) * t := by
  rw [ExtendedSelbergClass.leftHeight, SelbergGammaData.pairShift_inl_im]
  simp [ExtendedSelbergClass.leftBaseAt, ExtendedSelbergClass.leftBase]
  ring

/-- **Pointwise bound on the far-left lines.** -/
theorem ExtendedSelbergClass.eventually_norm_cuspMellinIntegrand_left_le
    (hd : 0 < F.gammaData.degree) (s : ℂ) {y : ℝ} (hy : 0 < y) (j₀ : Fin F.gammaData.rank) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ K : ℕ in atTop, ∀ t : ℝ,
      ‖F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)
          ((((-(K : ℝ) - 1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I)‖ ≤
        C * (2 * Real.pi * y) ^ K / Real.Gamma ((K : ℝ) + 3 / 2) *
          F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
          (F.firstIndex : ℝ) ^ (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
          (∏ i, Real.Gamma (F.leftGammaRe s i K)) *
          (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹ := by
  classical
  have hm₀pos : 0 < F.firstIndex := F.firstIndex_pos
  -- the reflected series at its first index
  have hsumm2 : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((2 : ℝ) : ℂ) n‖) :=
    (F.lSeriesSummable ((2 : ℝ) : ℂ) (by simp)).norm
  obtain ⟨Cm, hCm, hCmb⟩ := exists_bound_norm_cpow_mul_LSeries hsumm2 hm₀pos
    (fun n _ hn => F.coeff_eq_zero_of_lt_firstIndex hn)
  -- the constant
  set CS : ℝ := (2 : ℝ) ^ F.gammaData.rank *
    Real.exp (Real.pi * ∑ j, |(F.gammaData.mu j).im|) *
    Real.exp (Real.pi * (∑ j, F.gammaData.lambda j) * |s.im|) with hCS
  have hCSpos : 0 < CS := by positivity
  set C : ℝ := (2 * Real.pi * y) ^ (1 / 2 : ℝ) * (Real.pi * Real.sqrt 2) * CS *
    ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ * Cm with hC
  have hCnn : 0 ≤ C := mul_nonneg (by positivity) hCm
  refine ⟨C, hCnn, ?_⟩
  -- eventual conditions on `K`
  have hsumlam : ∑ j, F.gammaData.lambda j = F.gammaData.degree / 2 := by
    rw [SelbergGammaData.degree]; ring
  have hre_bot : Tendsto (fun K : ℕ => (F.leftBase s).re - (K : ℝ) / F.gammaData.degree)
      atTop atBot := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) / F.gammaData.degree) atTop atTop :=
      Filter.Tendsto.atTop_div_const hd tendsto_natCast_atTop_atTop
    exact (tendsto_atBot_add_const_left atTop (F.leftBase s).re
      (tendsto_neg_atTop_atBot.comp h1)).congr fun K => by simp [sub_eq_add_neg]
  have hX_top : ∀ i, Tendsto (fun K : ℕ => F.leftGammaRe s i K) atTop atTop := by
    intro i
    have hr := F.gammaData.pairRate_pos hd i
    exact tendsto_atTop_add_const_right _ _
      ((tendsto_natCast_atTop_atTop).const_mul_atTop hr)
  have hev : ∀ᶠ K : ℕ in atTop, (F.leftBase s).re - (K : ℝ) / F.gammaData.degree ≤ -1 ∧
      (∀ j, F.gammaData.lambda j * ((F.leftBase s).re - (K : ℝ) / F.gammaData.degree) <
        1 - (F.gammaData.mu j).re) ∧
      (∀ i, 0 < F.leftGammaRe s i K) := by
    refine (hre_bot.eventually_le_atBot (-1)).and ((Filter.eventually_all.2 fun j => ?_).and
      (Filter.eventually_all.2 fun i => (hX_top i).eventually_gt_atTop 0))
    have hl := F.gammaData.lambda_pos j
    filter_upwards [hre_bot.eventually_lt_atBot
      ((1 - (F.gammaData.mu j).re) / F.gammaData.lambda j)] with K hK
    rwa [lt_div_iff₀ hl, mul_comm] at hK
  filter_upwards [hev] with K ⟨hKre, hKμ, hKX⟩ t
  -- the point on the line and its image
  set u : ℂ := (((-(K : ℝ) - 1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I with hu
  set b : ℂ := F.leftBaseAt s t with hb
  have hw : s + u / (F.gammaData.degree : ℂ) = b - (K : ℂ) / (F.gammaData.degree : ℂ) :=
    F.add_leftLine_div hd s K t
  have hbre : b.re = (F.leftBase s).re := F.leftBaseAt_re s t
  have hwre : (b - (K : ℂ) / (F.gammaData.degree : ℂ)).re =
      (F.leftBase s).re - (K : ℝ) / F.gammaData.degree := by
    rw [Complex.sub_re, hbre, Complex.div_ofReal_re]
    simp
  have hbim : b.im = s.im + t / F.gammaData.degree := by
    simp [hb, ExtendedSelbergClass.leftBaseAt, ExtendedSelbergClass.leftBase]
  have hwim : (b - (K : ℂ) / (F.gammaData.degree : ℂ)).im = s.im + t / F.gammaData.degree := by
    rw [Complex.sub_im, hbim, Complex.div_ofReal_im]
    simp
  -- the functional equation at `w`
  have hFE := F.value_eq_asymmetric_of_farLeft (s := b - (K : ℂ) / (F.gammaData.degree : ℂ))
    (by rw [hwre]; linarith) (fun j => by rw [hwre]; exact hKμ j)
  -- the four factors
  have hpow : ‖(((2 * Real.pi * y : ℝ)) : ℂ) ^ (-u)‖ = (2 * Real.pi * y) ^ ((K : ℝ) + 1 / 2) := by
    rw [norm_twoPiY_cpow_neg hy]
    congr 1
    simp [hu]
    ring
  have hΓu : ‖Complex.Gamma u‖ ≤
      Real.pi * Real.sqrt 2 * Real.exp (-(Real.pi * |t| / 2)) / Real.Gamma ((K : ℝ) + 3 / 2) := by
    have := norm_Gamma_neg_half_line_le_exp K t
    have hu' : u = -(K : ℂ) - 1 / 2 + (t : ℂ) * I := by rw [hu]; push_cast; ring
    rwa [hu']
  have hS : ‖F.gammaData.asymmetricS (b - (K : ℂ) / (F.gammaData.degree : ℂ))‖ ≤
      CS * Real.exp (Real.pi * |t| / 2) := by
    refine (F.gammaData.norm_asymmetricS_le _).trans ?_
    have habs : |s.im + t / F.gammaData.degree| ≤ |s.im| + |t| / F.gammaData.degree := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hd]
    have hsumnn : 0 ≤ Real.pi * ∑ j, F.gammaData.lambda j := by
      rw [hsumlam]; positivity
    have hid : Real.pi * (∑ j, F.gammaData.lambda j) * (|t| / F.gammaData.degree) =
        Real.pi * |t| / 2 := by
      rw [hsumlam]; field_simp
    have hexpo : Real.pi * (∑ j, F.gammaData.lambda j) * |s.im + t / F.gammaData.degree| ≤
        Real.pi * (∑ j, F.gammaData.lambda j) * |s.im| + Real.pi * |t| / 2 := by
      calc Real.pi * (∑ j, F.gammaData.lambda j) * |s.im + t / F.gammaData.degree|
          ≤ Real.pi * (∑ j, F.gammaData.lambda j) * (|s.im| + |t| / F.gammaData.degree) :=
            mul_le_mul_of_nonneg_left habs hsumnn
        _ = Real.pi * (∑ j, F.gammaData.lambda j) * |s.im| + Real.pi * |t| / 2 := by
            rw [mul_add, hid]
    rw [hwim, hCS, mul_assoc _ (Real.exp (Real.pi * (∑ j, F.gammaData.lambda j) * |s.im|)),
      ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexpo) (by positivity)
  have hR : ‖selbergConjugateReflection F (b - (K : ℂ) / (F.gammaData.degree : ℂ))‖ ≤
      Cm * (F.firstIndex : ℝ) ^
        (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) := by
    rw [selbergConjugateReflection, norm_star]
    set v : ℂ := 1 - star (b - (K : ℂ) / (F.gammaData.degree : ℂ)) with hv
    have hvre : v.re = 1 - ((F.leftBase s).re - (K : ℝ) / F.gammaData.degree) := by
      rw [hv, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re, hwre]
    have hv2 : 2 ≤ v.re := by rw [hvre]; linarith
    have hval := F.lSeries_eq_value v (by linarith)
    change ‖F.continuation.value v‖ ≤ _
    rw [← hval]
    refine (hCmb v (by exact_mod_cast hv2)).trans (le_of_eq ?_)
    rw [hvre]
    congr 2
    ring
  -- the archimedean factor
  have hH : ‖F.gammaData.asymmetricH (b - (K : ℂ) / (F.gammaData.degree : ℂ))‖ ≤
      ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ *
        F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
        ((∏ i, Real.Gamma (F.leftGammaRe s i K)) *
          (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹) := by
    rw [F.gammaData.norm_asymmetricH_shift hd b K, hbre]
    have hQpos : 0 ≤ ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ *
        F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg F.gammaData.Q_pos.le _)
    refine mul_le_mul_of_nonneg_left ?_ hQpos
    have hre_i : ∀ i, (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) +
        F.gammaData.pairShift b i).re = F.leftGammaRe s i K := by
      intro i
      rw [Complex.add_re, Complex.ofReal_re, ExtendedSelbergClass.leftGammaRe,
        F.gammaData.pairShift_re_eq_of_re_eq hbre i]
    have hfac : ∀ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) +
        F.gammaData.pairShift b i)‖ ≤ Real.Gamma (F.leftGammaRe s i K) := by
      intro i
      have h := norm_Gamma_le_Gamma_re (s := ((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) +
        F.gammaData.pairShift b i) (by rw [hre_i]; exact hKX i)
      rwa [hre_i] at h
    have hfac0 : ‖Complex.Gamma (((F.gammaData.pairRate (Sum.inl j₀) * (K : ℝ) : ℝ) : ℂ) +
        F.gammaData.pairShift b (Sum.inl j₀))‖ ≤ Real.Gamma (F.leftGammaRe s (Sum.inl j₀) K) *
          (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹ := by
      have h := norm_Gamma_le_Gamma_re_div
        (z := ((F.gammaData.pairRate (Sum.inl j₀) * (K : ℝ) : ℝ) : ℂ) +
          F.gammaData.pairShift b (Sum.inl j₀)) (by rw [hre_i]; exact hKX _)
      have him : (((F.gammaData.pairRate (Sum.inl j₀) * (K : ℝ) : ℝ) : ℂ) +
          F.gammaData.pairShift b (Sum.inl j₀)).im = F.leftHeight s j₀ t := by
        rw [Complex.add_im, Complex.ofReal_im, zero_add]; rfl
      rw [hre_i, him] at h
      rwa [div_eq_mul_inv] at h
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (Sum.inl j₀)),
      ← Finset.mul_prod_erase Finset.univ (fun i => Real.Gamma (F.leftGammaRe s i K))
        (Finset.mem_univ (Sum.inl j₀))]
    have hrest : ∏ i ∈ Finset.univ.erase (Sum.inl j₀),
        ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) +
          F.gammaData.pairShift b i)‖ ≤
        ∏ i ∈ Finset.univ.erase (Sum.inl j₀), Real.Gamma (F.leftGammaRe s i K) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hfac i
    calc ‖Complex.Gamma (((F.gammaData.pairRate (Sum.inl j₀) * (K : ℝ) : ℝ) : ℂ) +
          F.gammaData.pairShift b (Sum.inl j₀))‖ *
          ∏ i ∈ Finset.univ.erase (Sum.inl j₀),
            ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) +
              F.gammaData.pairShift b i)‖
        ≤ (Real.Gamma (F.leftGammaRe s (Sum.inl j₀) K) *
            (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹) *
          ∏ i ∈ Finset.univ.erase (Sum.inl j₀), Real.Gamma (F.leftGammaRe s i K) :=
          mul_le_mul hfac0 hrest (Finset.prod_nonneg fun i _ => norm_nonneg _)
            (mul_nonneg (Real.Gamma_pos_of_pos (hKX _)).le (by positivity))
      _ = _ := by ring
  -- assemble
  rw [ExtendedSelbergClass.cuspMellinIntegrand, hw, hFE]
  simp only [norm_mul]
  rw [F.gammaData.norm_invariantRootNumber, one_mul, hpow]
  have hexp : Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t| / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hy12 : (2 * Real.pi * y) ^ ((K : ℝ) + 1 / 2) =
      (2 * Real.pi * y) ^ (1 / 2 : ℝ) * (2 * Real.pi * y) ^ K := by
    rw [Real.rpow_add (by positivity), Real.rpow_natCast]; ring
  have hΓK : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hD : 0 ≤ (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹ := by
    positivity
  have hprodnn : 0 ≤ ∏ i, Real.Gamma (F.leftGammaRe s i K) :=
    Finset.prod_nonneg fun i _ => (Real.Gamma_pos_of_pos (hKX i)).le
  calc (2 * Real.pi * y) ^ ((K : ℝ) + 1 / 2) *
        (‖Complex.Gamma u‖ *
          (‖F.gammaData.asymmetricS (b - (K : ℂ) / (F.gammaData.degree : ℂ))‖ *
            ‖F.gammaData.asymmetricH (b - (K : ℂ) / (F.gammaData.degree : ℂ))‖ *
            ‖selbergConjugateReflection F (b - (K : ℂ) / (F.gammaData.degree : ℂ))‖))
      ≤ (2 * Real.pi * y) ^ ((K : ℝ) + 1 / 2) *
        ((Real.pi * Real.sqrt 2 * Real.exp (-(Real.pi * |t| / 2)) /
            Real.Gamma ((K : ℝ) + 3 / 2)) *
          ((CS * Real.exp (Real.pi * |t| / 2)) *
            (((2 * Real.pi) ^ F.gammaData.rank)⁻¹ *
              F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
              ((∏ i, Real.Gamma (F.leftGammaRe s i K)) *
                (1 + F.leftHeight s j₀ t ^ 2 /
                  (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹)) *
            (Cm * (F.firstIndex : ℝ) ^
              (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ))))) := by
        have hSb : 0 ≤ CS * Real.exp (Real.pi * |t| / 2) :=
          mul_nonneg hCSpos.le (Real.exp_pos _).le
        have hHb : 0 ≤ ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ *
            F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
            ((∏ i, Real.Gamma (F.leftGammaRe s i K)) *
              (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹) :=
          mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg F.gammaData.Q_pos.le _))
            (mul_nonneg hprodnn hD)
        have hΓb : 0 ≤ Real.pi * Real.sqrt 2 * Real.exp (-(Real.pi * |t| / 2)) /
            Real.Gamma ((K : ℝ) + 3 / 2) := div_nonneg (by positivity) hΓK.le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul hΓu ?_ (by positivity) hΓb
        exact mul_le_mul (mul_le_mul hS hH (norm_nonneg _) hSb) hR (norm_nonneg _)
          (mul_nonneg hSb hHb)
    _ = (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t| / 2)) *
        (C * (2 * Real.pi * y) ^ K / Real.Gamma ((K : ℝ) + 3 / 2) *
          F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
          (F.firstIndex : ℝ) ^
            (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
          (∏ i, Real.Gamma (F.leftGammaRe s i K)) *
          (1 + F.leftHeight s j₀ t ^ 2 / (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ 2)⁻¹) := by
        rw [hy12, hC]
        ring
    _ = _ := by rw [hexp, one_mul]

/-- A nonnegative sequence whose `K`-th roots tend to a limit below one tends to zero. -/
theorem tendsto_zero_of_tendsto_rpow_inv_lt_one {v : ℕ → ℝ} {L : ℝ}
    (hv : ∀ᶠ K : ℕ in atTop, 0 ≤ v K) (hL : L < 1)
    (h : Tendsto (fun K : ℕ => v K ^ (1 / (K : ℝ))) atTop (𝓝 L)) :
    Tendsto v atTop (𝓝 0) := by
  set ρ : ℝ := (max L 0 + 1) / 2 with hρ
  have hLρ : L < ρ := by rw [hρ]; have := le_max_left L 0; linarith
  have hρ0 : 0 < ρ := by rw [hρ]; have := le_max_right L 0; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; have := max_lt hL (zero_lt_one' ℝ); linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
  refine squeeze_zero' hv ?_ hpow
  filter_upwards [hv, h.eventually_lt_const hLρ, eventually_ge_atTop 1] with K hK0 hK hK1
  have hKne : K ≠ 0 := by omega
  have hroot : (v K ^ (1 / (K : ℝ))) ^ K = v K := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hK0 hKne
  rw [← hroot]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hK0 _) hK.le K

/-- The far-left line `Re u = -K - 1/2`. -/
def leftLine (K : ℕ) (t : ℝ) : ℂ := (((-(K : ℝ) - 1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I

theorem ExtendedSelbergClass.exists_distinguished_index (hd : 0 < F.gammaData.degree) :
    Nonempty (Fin F.gammaData.rank) := by
  rcases Nat.eq_zero_or_pos F.gammaData.rank with h | h
  · exfalso
    have : F.gammaData.degree = 0 := by
      rw [SelbergGammaData.degree]
      have hempty : (Finset.univ : Finset (Fin F.gammaData.rank)) = ∅ := by
        rw [Finset.univ_eq_empty_iff]; rw [h]; infer_instance
      rw [hempty, Finset.sum_empty, mul_zero]
    linarith
  · exact ⟨⟨0, h⟩⟩

/-- **Integrability and size of the far-left integrals.** -/
theorem ExtendedSelbergClass.eventually_integrable_norm_integral_left_le
    (hd : 0 < F.gammaData.degree) (s : ℂ) {y : ℝ} (hy : 0 < y) (j₀ : Fin F.gammaData.rank) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ K : ℕ in atTop,
      Integrable (fun t : ℝ => F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)
        (leftLine K t)) ∧
      ‖∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) (leftLine K t)‖ ≤
        C * (2 * Real.pi * y) ^ K / Real.Gamma ((K : ℝ) + 3 / 2) *
          F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
          (F.firstIndex : ℝ) ^ (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
          (∏ i, Real.Gamma (F.leftGammaRe s i K)) *
          (Real.pi * (F.leftGammaRe s (Sum.inl j₀) K + 1) /
            (F.gammaData.lambda j₀ / F.gammaData.degree)) := by
  obtain ⟨C, hC, hev⟩ := F.eventually_norm_cuspMellinIntegrand_left_le hd s hy j₀
  refine ⟨C, hC, ?_⟩
  set x : ℂ := (((2 * Real.pi * y : ℝ)) : ℂ) with hx
  have hx0 : x ≠ 0 := by rw [hx]; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi * y).ne'
  have hX : ∀ᶠ K : ℕ in atTop, 0 < F.leftGammaRe s (Sum.inl j₀) K := by
    have hr := F.gammaData.pairRate_pos hd (Sum.inl j₀)
    exact (tendsto_atTop_add_const_right _ _
      ((tendsto_natCast_atTop_atTop).const_mul_atTop hr)).eventually_gt_atTop 0
  have hpole : ∀ᶠ K : ℕ in atTop, (-(K : ℝ) - 1 / 2) < (F.cuspPole s).re := by
    have : Tendsto (fun K : ℕ => -(K : ℝ) - 1 / 2) atTop atBot :=
      tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    exact this.eventually_lt_atBot _
  have hl := F.gammaData.lambda_pos j₀
  have hβ : -(F.gammaData.lambda j₀ / F.gammaData.degree) ≠ 0 := by
    have : 0 < F.gammaData.lambda j₀ / F.gammaData.degree := div_pos hl hd
    linarith
  filter_upwards [hev, hX, hpole] with K hK hXK hpK
  set A : ℝ := C * (2 * Real.pi * y) ^ K / Real.Gamma ((K : ℝ) + 3 / 2) *
    F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
    (F.firstIndex : ℝ) ^ (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
    (∏ i, Real.Gamma (F.leftGammaRe s i K)) with hA
  set B : ℝ := F.leftGammaRe s (Sum.inl j₀) K + 1 with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  set α : ℝ := -(F.gammaData.lambda j₀ * s.im) - (F.gammaData.mu j₀).im
  set β : ℝ := -(F.gammaData.lambda j₀ / F.gammaData.degree)
  have hprof : ∀ t : ℝ, (1 + F.leftHeight s j₀ t ^ 2 / B ^ 2)⁻¹ = (1 + (α + β * t) ^ 2 / B ^ 2)⁻¹ := by
    intro t; rw [F.leftHeight_eq]
  have hint_prof := integrable_inv_one_add_affine_sq (a := α) hβ hBpos
  -- continuity along the line
  have hcont : Continuous (fun t : ℝ => F.cuspMellinIntegrand s x (leftLine K t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : (leftLine K t).re = -(K : ℝ) - 1 / 2 := by simp [leftLine]
    have hΓ : ∀ k : ℕ, leftLine K t ≠ -(k : ℂ) := by
      intro k h
      have h1 := congrArg Complex.re h
      rw [hre] at h1
      simp at h1
      have h2 : (2 : ℝ) * ((k : ℝ) - K) = 1 := by linarith
      have h3 : (2 : ℤ) * ((k : ℤ) - K) = 1 := by exact_mod_cast h2
      omega
    have hne : leftLine K t ≠ F.cuspPole s := by
      intro h
      have := congrArg Complex.re h
      rw [hre] at this
      linarith
    have han := F.analyticAt_cuspMellinIntegrand hd s hx0 hΓ hne
    exact ContinuousAt.comp (g := F.cuspMellinIntegrand s x) (f := leftLine K) (x := t)
      han.continuousAt (by unfold leftLine; fun_prop)
  have hbound : ∀ t : ℝ, ‖F.cuspMellinIntegrand s x (leftLine K t)‖ ≤
      A * (1 + (α + β * t) ^ 2 / B ^ 2)⁻¹ := by
    intro t
    rw [← hprof t]
    exact hK t
  have hintg : Integrable (fun t : ℝ => F.cuspMellinIntegrand s x (leftLine K t)) :=
    Integrable.mono' (hint_prof.const_mul A) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨hintg, ?_⟩
  calc ‖∫ t : ℝ, F.cuspMellinIntegrand s x (leftLine K t)‖
      ≤ ∫ t : ℝ, ‖F.cuspMellinIntegrand s x (leftLine K t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, A * (1 + (α + β * t) ^ 2 / B ^ 2)⁻¹ :=
        integral_mono hintg.norm (hint_prof.const_mul A) hbound
    _ = A * (Real.pi * B / |β|) := by
        rw [integral_const_mul, integral_inv_one_add_affine_sq hβ hBpos]
    _ = _ := by
        have hβabs : |β| = F.gammaData.lambda j₀ / F.gammaData.degree := by
          rw [abs_neg, abs_of_pos (div_pos hl hd)]
        rw [hβabs, hA, hB]

/-- `(K!/Γ(K+3/2))^{1/K} → 1`. -/
theorem tendsto_factorial_div_Gamma_three_halves_rpow_inv :
    Tendsto (fun K : ℕ => ((K.factorial : ℝ) / Real.Gamma ((K : ℝ) + 3 / 2)) ^ (1 / (K : ℝ)))
      atTop (𝓝 1) := by
  refine tendsto_rpow_inv_of_polynomial_bounds (C₁ := 1 / 2) (C₂ := 1) (B := 1)
    (by norm_num) (by norm_num) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hΓ : Real.Gamma ((K : ℝ) + 3 / 2) ≤ Real.Gamma ((K : ℝ) + 2) :=
      (Real.Gamma_strictMonoOn_Ici.monotoneOn) (by rw [Set.mem_Ici]; linarith)
        (by rw [Set.mem_Ici]; linarith)
        (by linarith)
    have hΓ2 : Real.Gamma ((K : ℝ) + 2) = ((K + 1 : ℕ).factorial : ℝ) := by
      rw [show (K : ℝ) + 2 = ((K + 1 : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    have hpos : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
    rw [Real.rpow_neg_one, le_div_iff₀ hpos]
    calc 1 / 2 * (K : ℝ)⁻¹ * Real.Gamma ((K : ℝ) + 3 / 2)
        ≤ 1 / 2 * (K : ℝ)⁻¹ * ((K + 1 : ℕ).factorial : ℝ) := by rw [← hΓ2]; gcongr
      _ = 1 / 2 * (K : ℝ)⁻¹ * ((K : ℝ) + 1) * (K.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
      _ ≤ (K.factorial : ℝ) := by
          have : 1 / 2 * (K : ℝ)⁻¹ * ((K : ℝ) + 1) ≤ 1 := by
            have hKpos : (0 : ℝ) < K := by linarith
            rw [show 1 / 2 * (K : ℝ)⁻¹ * ((K : ℝ) + 1) = ((K : ℝ) + 1) / (2 * K) by field_simp,
              div_le_one (by positivity)]
            linarith
          have hf : (0 : ℝ) ≤ (K.factorial : ℝ) := by positivity
          nlinarith
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hΓ : Real.Gamma ((K : ℝ) + 1) ≤ Real.Gamma ((K : ℝ) + 3 / 2) :=
      (Real.Gamma_strictMonoOn_Ici.monotoneOn) (by rw [Set.mem_Ici]; linarith)
        (by rw [Set.mem_Ici]; linarith)
        (by linarith)
    rw [Real.Gamma_nat_eq_factorial] at hΓ
    have hpos : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
    rw [Real.rpow_one, div_le_iff₀ hpos]
    nlinarith

/-- **The far-left integrals vanish below the cusp gap.** -/
theorem ExtendedSelbergClass.tendsto_integral_cuspMellinIntegrand_left
    (hd : 0 < F.gammaData.degree) (s : ℂ) {y : ℝ} (hy : 0 < y)
    (hyΔ : y < F.gammaData.degree *
      ((F.firstIndex : ℝ) / F.gammaData.conductor) ^ (1 / F.gammaData.degree)) :
    Tendsto (fun K : ℕ =>
      ∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) (leftLine K t)) atTop
      (𝓝 0) := by
  classical
  obtain ⟨j₀⟩ := F.exists_distinguished_index hd
  obtain ⟨C, hC, hev⟩ := F.eventually_integrable_norm_integral_left_le hd s hy j₀
  have hm₀pos : (0 : ℝ) < (F.firstIndex : ℝ) := by exact_mod_cast F.firstIndex_pos
  have hl := F.gammaData.lambda_pos j₀
  have hlamd : 0 < F.gammaData.lambda j₀ / F.gammaData.degree := div_pos hl hd
  set β : Fin F.gammaData.rank ⊕ Fin F.gammaData.rank → ℂ :=
    fun i => (((F.gammaData.pairShift (F.leftBase s) i).re : ℝ) : ℂ) with hβ
  set κ₀ : ℝ := (C + 1) * Real.pi / (F.gammaData.lambda j₀ / F.gammaData.degree) with hκ₀
  have hκ₀pos : 0 < κ₀ := by rw [hκ₀]; positivity
  -- the majorant and its seven factors
  set v : ℕ → ℝ := fun K => κ₀ * (2 * Real.pi * y) ^ K *
    F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
    (F.firstIndex : ℝ) ^ (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
    ((∏ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖) /
      (K.factorial : ℝ)) *
    ((K.factorial : ℝ) / Real.Gamma ((K : ℝ) + 3 / 2)) *
    (F.leftGammaRe s (Sum.inl j₀) K + 1) with hv
  have hXev : ∀ᶠ K : ℕ in atTop, ∀ i, 0 < F.leftGammaRe s i K := by
    refine Filter.eventually_all.2 fun i => ?_
    have hr := F.gammaData.pairRate_pos hd i
    exact (tendsto_atTop_add_const_right _ _
      ((tendsto_natCast_atTop_atTop).const_mul_atTop hr)).eventually_gt_atTop 0
  have hGamma_eq : ∀ K : ℕ, (∀ i, 0 < F.leftGammaRe s i K) → ∀ i,
      Real.Gamma (F.leftGammaRe s i K) =
        ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖ := by
    intro K hK i
    have harg : (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i) =
        ((F.leftGammaRe s i K : ℝ) : ℂ) := by
      simp only [hβ, ExtendedSelbergClass.leftGammaRe]
      push_cast; ring
    rw [harg, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (hK i))]
  -- the integral is dominated by the majorant
  have hdom : ∀ᶠ K : ℕ in atTop,
      ‖∫ t : ℝ, F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) (leftLine K t)‖ ≤ v K := by
    filter_upwards [hev, hXev] with K hK hXK
    refine hK.2.trans ?_
    have hΓpos : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
    have hfact : (0 : ℝ) < (K.factorial : ℝ) := by exact_mod_cast K.factorial_pos
    have hprod : ∏ i, Real.Gamma (F.leftGammaRe s i K) =
        ∏ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖ :=
      Finset.prod_congr rfl fun i _ => hGamma_eq K hXK i
    have hXpos := hXK (Sum.inl j₀)
    rw [hprod]
    have hQnn : 0 ≤ F.gammaData.Q ^
        ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) :=
      Real.rpow_nonneg F.gammaData.Q_pos.le _
    have hmnn : 0 ≤ (F.firstIndex : ℝ) ^
        (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) :=
      Real.rpow_nonneg hm₀pos.le _
    have hPnn : 0 ≤ ∏ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖ :=
      Finset.prod_nonneg fun i _ => norm_nonneg _
    have hy0 : 0 ≤ (2 * Real.pi * y) ^ K := by positivity
    set W : ℝ := (2 * Real.pi * y) ^ K *
      F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
      (F.firstIndex : ℝ) ^ (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
      (∏ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖) *
      (F.leftGammaRe s (Sum.inl j₀) K + 1) / Real.Gamma ((K : ℝ) + 3 / 2) with hW
    have hWnn : 0 ≤ W := by
      rw [hW]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hy0 hQnn) hmnn) hPnn)
        (by linarith)) hΓpos.le
    have hlhs : C * (2 * Real.pi * y) ^ K / Real.Gamma ((K : ℝ) + 3 / 2) *
        F.gammaData.Q ^ ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) *
        (F.firstIndex : ℝ) ^ (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) *
        (∏ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖) *
        (Real.pi * (F.leftGammaRe s (Sum.inl j₀) K + 1) /
          (F.gammaData.lambda j₀ / F.gammaData.degree)) =
        C * Real.pi / (F.gammaData.lambda j₀ / F.gammaData.degree) * W := by
      rw [hW]; field_simp
    have hrhs : v K = κ₀ * W := by
      simp only [hv, hW]
      field_simp
    rw [hlhs, hrhs, hκ₀]
    apply mul_le_mul_of_nonneg_right _ hWnn
    apply div_le_div_of_nonneg_right _ hlamd.le
    nlinarith [Real.pi_pos]
  -- the roots of the seven factors
  have r1 : Tendsto (fun K : ℕ => κ₀ ^ (1 / (K : ℝ))) atTop (𝓝 1) :=
    tendsto_const_rpow_inv_nat hκ₀pos
  have r2 : Tendsto (fun K : ℕ => ((2 * Real.pi * y) ^ K) ^ (1 / (K : ℝ))) atTop
      (𝓝 (2 * Real.pi * y)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  have r3 := tendsto_rpow_linear_rpow_inv (a := 1 - 2 * (F.leftBase s).re)
    (b := 2 / F.gammaData.degree) F.gammaData.Q_pos
  have r4 := tendsto_rpow_linear_rpow_inv (a := -(1 - (F.leftBase s).re))
    (b := -(1 / F.gammaData.degree)) hm₀pos
  have r5 := tendsto_prod_norm_Gamma_div_factorial_rpow_inv (F.gammaData.pairRate_pos hd)
    (F.gammaData.sum_pairRate hd) β
  have r6 := tendsto_factorial_div_Gamma_three_halves_rpow_inv
  have r7 : Tendsto (fun K : ℕ => (F.leftGammaRe s (Sum.inl j₀) K + 1) ^ (1 / (K : ℝ))) atTop
      (𝓝 1) := by
    have hc0 := F.gammaData.pairRate_pos hd (Sum.inl j₀)
    refine tendsto_rpow_inv_of_polynomial_bounds (C₁ := 1)
      (C₂ := F.gammaData.pairRate (Sum.inl j₀) +
        |(F.gammaData.pairShift (F.leftBase s) (Sum.inl j₀)).re| + 1)
      (B := 1) (by norm_num) (by positivity) ?_ ?_
    · filter_upwards [hXev, eventually_ge_atTop 1] with K hK hK1
      have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
      have h0 := hK (Sum.inl j₀)
      rw [Real.rpow_neg_one, one_mul]
      have : (K : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK1'
      linarith
    · filter_upwards [eventually_ge_atTop 1] with K hK1
      have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
      rw [Real.rpow_one, ExtendedSelbergClass.leftGammaRe]
      have := le_abs_self (F.gammaData.pairShift (F.leftBase s) (Sum.inl j₀)).re
      nlinarith [abs_nonneg (F.gammaData.pairShift (F.leftBase s) (Sum.inl j₀)).re]
  have hprodlim := ((((((r1.mul r2).mul r3).mul r4).mul r5).mul r6).mul r7)
  have hlimval : 1 * (2 * Real.pi * y) * F.gammaData.Q ^ (2 / F.gammaData.degree) *
      (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) *
      (∏ i, F.gammaData.pairRate i ^ F.gammaData.pairRate i) * 1 * 1 =
      y * F.gammaData.conductor ^ (1 / F.gammaData.degree) *
        (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) / F.gammaData.degree := by
    have h := F.gammaData.archimedeanRootConstant_eq hd
    rw [show (1 : ℝ) * (2 * Real.pi * y) * F.gammaData.Q ^ (2 / F.gammaData.degree) *
        (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) *
        (∏ i, F.gammaData.pairRate i ^ F.gammaData.pairRate i) * 1 * 1 =
        (2 * Real.pi * y) * (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) *
          (F.gammaData.Q ^ (2 / F.gammaData.degree) *
            ∏ i, F.gammaData.pairRate i ^ F.gammaData.pairRate i) by ring, h]
    field_simp
  rw [hlimval] at hprodlim
  have hLlt : y * F.gammaData.conductor ^ (1 / F.gammaData.degree) *
      (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) / F.gammaData.degree < 1 := by
    have hq := F.gammaData.conductor_pos
    have hqd : 0 < F.gammaData.conductor ^ (1 / F.gammaData.degree) :=
      Real.rpow_pos_of_pos hq _
    have hmd : 0 < (F.firstIndex : ℝ) ^ (1 / F.gammaData.degree) :=
      Real.rpow_pos_of_pos hm₀pos _
    rw [Real.div_rpow hm₀pos.le hq.le] at hyΔ
    rw [Real.rpow_neg hm₀pos.le, div_lt_one hd]
    have hy' : y * F.gammaData.conductor ^ (1 / F.gammaData.degree) <
        F.gammaData.degree * (F.firstIndex : ℝ) ^ (1 / F.gammaData.degree) := by
      have := mul_lt_mul_of_pos_right hyΔ hqd
      rwa [mul_div_assoc', div_mul_cancel₀ _ hqd.ne'] at this
    calc y * F.gammaData.conductor ^ (1 / F.gammaData.degree) *
          ((F.firstIndex : ℝ) ^ (1 / F.gammaData.degree))⁻¹
        < F.gammaData.degree * (F.firstIndex : ℝ) ^ (1 / F.gammaData.degree) *
          ((F.firstIndex : ℝ) ^ (1 / F.gammaData.degree))⁻¹ := by
          gcongr
      _ = F.gammaData.degree := by field_simp
  have hvroot : Tendsto (fun K : ℕ => v K ^ (1 / (K : ℝ))) atTop
      (𝓝 (y * F.gammaData.conductor ^ (1 / F.gammaData.degree) *
        (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) / F.gammaData.degree)) := by
    refine hprodlim.congr' ?_
    filter_upwards [hXev] with K hXK
    have hΓpos : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
    have h2 : 0 ≤ (2 * Real.pi * y) ^ K := by positivity
    have h3 : 0 ≤ F.gammaData.Q ^
        ((1 - 2 * (F.leftBase s).re) + 2 / F.gammaData.degree * (K : ℝ)) :=
      Real.rpow_nonneg F.gammaData.Q_pos.le _
    have h4 : 0 ≤ (F.firstIndex : ℝ) ^
        (-(1 - (F.leftBase s).re) + (-(1 / F.gammaData.degree)) * (K : ℝ)) :=
      Real.rpow_nonneg hm₀pos.le _
    have h5 : 0 ≤ (∏ i, ‖Complex.Gamma (((F.gammaData.pairRate i * (K : ℝ) : ℝ) : ℂ) + β i)‖) /
        (K.factorial : ℝ) :=
      div_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (by positivity)
    have h6 : 0 ≤ (K.factorial : ℝ) / Real.Gamma ((K : ℝ) + 3 / 2) :=
      div_nonneg (by positivity) hΓpos.le
    have h7 : 0 ≤ F.leftGammaRe s (Sum.inl j₀) K + 1 := by linarith [hXK (Sum.inl j₀)]
    simp only [hv]
    rw [Real.mul_rpow (by positivity) h7, Real.mul_rpow (by positivity) h6,
      Real.mul_rpow (by positivity) h5, Real.mul_rpow (by positivity) h4,
      Real.mul_rpow (by positivity) h3, Real.mul_rpow hκ₀pos.le h2]
  have hvzero := tendsto_zero_of_tendsto_rpow_inv_lt_one
    (hdom.mono fun K hK => le_trans (norm_nonneg _) hK) hLlt hvroot
  exact squeeze_zero_norm' hdom hvzero

end

end RHTower
