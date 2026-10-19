import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialSpanTestPolarPrimeGammaBudgets
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-! Exact explicit formula for finite combinations of the literal factorial correction tails.
Complex conjugation and reflection reindex the zeta zero divisor, so the zero pairing is real
and Hermitian on real sources and splits as `W(u + iv, u + iv) = W(u, u) + W(v, v)`. The raw
Gamma density is integrable by the logarithmic Fourier bound of each tail, the mollified Gamma
channel converges by dominated convergence, and the smoothed explicit formula passes to the
limit in every channel. The complex identity follows by splitting the Gamma, polar, and
Hermitian prime channels into their real and imaginary parts. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate FourierTransform
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The archimedean energy `(1/2π) ∫ ‖F̂(r)‖² G(r) dr` of a real test. -/
def archGammaEnergy (F : ℝ → ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * EF.gammaBracket r

/-- The pole energy `2 Re(F̂(i/2) conj F̂(-i/2))` of a real test. -/
def archPoleTerm (F : ℝ → ℝ) : ℝ :=
  2 * (paperFT (fun u => (F u : ℂ)) (Complex.I / 2) *
    conj (paperFT (fun u => (F u : ℂ)) (-Complex.I / 2))).re

theorem archPoleEnergy_eq_pole_add_gamma (F : ℝ → ℝ) :
    archPoleEnergy F = archPoleTerm F + archGammaEnergy F := rfl

/-! ## Conjugation, reflection, and real-imaginary splitting -/

/-- Complex conjugation as a permutation of the zeta zero carrier. -/
def zetaZeroConjPerm : Equiv.Perm zetaZeroConfig.carrier :=
  Function.Involutive.toPerm (fun ρ => ⟨conj (ρ : ℂ), RHTower.conj_mem_zetaZeroConfig ρ.2⟩)
    (fun _ => Subtype.ext (Complex.conj_conj _))

/-- `W(u, v) = conj W(v, u)` by the reflection symmetry of the zero divisor. -/
theorem zetaZeroConfig_W_swap (f g : ℝ → ℂ) :
    zetaZeroConfig.W f g = conj (zetaZeroConfig.W g f) := by
  unfold ZeroConfig.W
  rw [Complex.conj_tsum, ← zetaZeroReflectPerm.tsum_eq]
  refine tsum_congr fun ρ => ?_
  change zetaZeroConfig.Wsummand f g (reflect (ρ : ℂ)) = conj (zetaZeroConfig.Wsummand g f ρ)
  unfold ZeroConfig.Wsummand
  rw [zetaZeroConfig.mult_reflect _ ρ.2, Tail.gammaOf_reflect, Complex.conj_conj, map_mul,
    map_mul, Complex.conj_conj, Complex.conj_natCast]
  ring

/-- For real sources the mixed zero pairing is real. -/
theorem zetaZeroConfig_W_ofReal_conj (u v : ℝ → ℝ) :
    conj (zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (v x : ℂ))) =
      zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) := by
  unfold ZeroConfig.W
  rw [Complex.conj_tsum, ← zetaZeroConjPerm.tsum_eq]
  refine tsum_congr fun ρ => ?_
  change conj (zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) (conj (ρ : ℂ))) =
    zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) ρ
  unfold ZeroConfig.Wsummand
  rw [RHTower.mult_conj_zetaZeroConfig ρ.2, RHTower.gammaOf_conj,
    EvenSector.paperFT_ofReal_neg_conj, map_neg, Complex.conj_conj,
    EvenSector.paperFT_ofReal_neg_conj]
  simp only [map_mul, Complex.conj_conj, Complex.conj_natCast]

theorem paperFT_ofReal_add_I_mul (u v : ℝ → ℝ) {s : ℂ}
    (hu : Integrable fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) * (u x : ℂ))
    (hv : Integrable fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) * (v x : ℂ)) :
    paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) (gammaOf s) =
      paperFT (fun x => (u x : ℂ)) (gammaOf s) +
        Complex.I * paperFT (fun x => (v x : ℂ)) (gammaOf s) := by
  rw [paperFT_gammaOf_eq_tilt, paperFT_gammaOf_eq_tilt, paperFT_gammaOf_eq_tilt,
    ← integral_const_mul, ← integral_add hu (hv.const_mul Complex.I)]
  congr 1
  funext x
  ring

/-- **Real–imaginary splitting of the zero pairing.** For real sources `u, v` with readouts on
the closed strip and summable zero-sampling squares,
`W(u + iv, u + iv) = W(u, u) + W(v, v)`. -/
theorem zetaZeroConfig_W_ofReal_add_I_mul (u v : ℝ → ℝ)
    (hu : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      Integrable fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) * (u x : ℂ))
    (hv : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      Integrable fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) * (v x : ℂ))
    (hZu : Summable (zetaZeroSquareSummand fun x => (u x : ℂ)))
    (hZv : Summable (zetaZeroSquareSummand fun x => (v x : ℂ))) :
    Summable (zetaZeroSquareSummand fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) ∧
    zetaZeroConfig.W (fun x => (u x : ℂ) + Complex.I * (v x : ℂ))
        (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) =
      zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) +
        zetaZeroConfig.W (fun x => (v x : ℂ)) (fun x => (v x : ℂ)) := by
  set U : ℝ → ℂ := fun x => (u x : ℂ)
  set V : ℝ → ℂ := fun x => (v x : ℂ)
  set f : ℝ → ℂ := fun x => (u x : ℂ) + Complex.I * (v x : ℂ)
  have hsp : ∀ ρ : zetaZeroConfig.carrier,
      paperFT f (gammaOf ρ) = paperFT U (gammaOf ρ) + Complex.I * paperFT V (gammaOf ρ) ∧
      paperFT f (conj (gammaOf ρ)) =
        paperFT U (conj (gammaOf ρ)) + Complex.I * paperFT V (conj (gammaOf ρ)) := by
    intro ρ
    have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
    have hr0 : 0 ≤ (reflect (ρ : ℂ)).re := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    have hr1 : (reflect (ρ : ℂ)).re ≤ 1 := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    refine ⟨paperFT_ofReal_add_I_mul u v (hu _ hρ.1 hρ.2) (hv _ hρ.1 hρ.2), ?_⟩
    rw [← Tail.gammaOf_reflect]
    exact paperFT_ofReal_add_I_mul u v (hu _ hr0 hr1) (hv _ hr0 hr1)
  have hZf : Summable (zetaZeroSquareSummand f) := by
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (fun ρ => ?_) ((hZu.add hZv).mul_left 2)
    unfold zetaZeroSquareSummand
    rw [(hsp ρ).1]
    have h := norm_add_le (paperFT U (gammaOf ρ)) (Complex.I * paperFT V (gammaOf ρ))
    rw [norm_mul, Complex.norm_I, one_mul] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    nlinarith [sq_nonneg (‖paperFT U (gammaOf ρ)‖ - ‖paperFT V (gammaOf ρ)‖)]
  refine ⟨hZf, ?_⟩
  have hpt : ∀ ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand f f ρ =
      zetaZeroConfig.Wsummand U U ρ + zetaZeroConfig.Wsummand V V ρ +
        Complex.I * (zetaZeroConfig.Wsummand V U ρ - zetaZeroConfig.Wsummand U V ρ) := by
    intro ρ
    unfold ZeroConfig.Wsummand
    rw [(hsp ρ).1, (hsp ρ).2]
    simp only [map_add, map_mul, Complex.conj_I]
    linear_combination (-(zetaZeroConfig.mult (ρ : ℂ) : ℂ) * paperFT V (gammaOf ρ) *
      conj (paperFT V (conj (gammaOf ρ)))) * Complex.I_sq
  have sUU := summable_Wsummand U U hZu hZu
  have sVV := summable_Wsummand V V hZv hZv
  have sVU := summable_Wsummand V U hZv hZu
  have sUV := summable_Wsummand U V hZu hZv
  have hW : zetaZeroConfig.W f f = zetaZeroConfig.W U U + zetaZeroConfig.W V V +
      Complex.I * (zetaZeroConfig.W V U - zetaZeroConfig.W U V) := by
    unfold ZeroConfig.W
    rw [tsum_congr hpt, (sUU.add sVV).tsum_add ((sVU.sub sUV).mul_left _), sUU.tsum_add sVV,
      tsum_mul_left, sVU.tsum_sub sUV]
  have hsym : zetaZeroConfig.W U V = zetaZeroConfig.W V U := by
    rw [zetaZeroConfig_W_swap U V, zetaZeroConfig_W_ofReal_conj v u]
  rw [hW, hsym, sub_self, mul_zero, add_zero]

/-! ## The raw Gamma channel and the explicit formula -/

theorem log_two_add_two_pi_mul_abs_le (ξ : ℝ) :
    Real.log (2 + 2 * Real.pi * |ξ|) ≤ (1 + Real.log (2 + 2 * Real.pi)) * suzukiLogWeight ξ := by
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ Real.log (2 + 2 * Real.pi) := Real.log_nonneg (by linarith)
  have hm0 : 0 ≤ max (Real.log |ξ|) 0 := le_max_right _ _
  have h1 : Real.log (2 + 2 * Real.pi * |ξ|) ≤
      Real.log (2 + 2 * Real.pi) + max (Real.log |ξ|) 0 := by
    by_cases hξ : |ξ| ≤ 1
    · have := Real.log_le_log (by positivity) (show 2 + 2 * Real.pi * |ξ| ≤ 2 + 2 * Real.pi by
        nlinarith [abs_nonneg ξ])
      linarith
    · push Not at hξ
      have hpos : 0 < |ξ| := lt_trans one_pos hξ
      have hle : 2 + 2 * Real.pi * |ξ| ≤ (2 + 2 * Real.pi) * |ξ| := by nlinarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by positivity) hpos.ne'] at h
      linarith [le_max_left (Real.log |ξ|) 0]
  have h2 : Real.log (2 + 2 * Real.pi) + max (Real.log |ξ|) 0 ≤
      (1 + Real.log (2 + 2 * Real.pi)) * (1 + max (Real.log |ξ|) 0) := by nlinarith
  exact h1.trans h2

/-- Logarithmic Fourier integrability of a raw correction tail in the `paperFT` normalization. -/
theorem integrable_norm_sq_paperFT_tail_mul_log (n : ℕ) :
    Integrable fun r : ℝ => ‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 *
      Real.log (2 + |r|) := by
  set T : ℝ → ℂ := fun x => (factorialMuntzCorrectedTail n x : ℂ) with hT
  have hσ : (1 / 2 : ℝ) ∈ FactorialSamplingAbscissa := by norm_num [FactorialSamplingAbscissa]
  have hw : (fun x : ℝ => (factorialWeightedTail n (1 / 2) x : ℂ)) = T := by
    funext x
    simp [factorialWeightedTail, hT]
  have hL := factorialTailLogFourier_integrable n ⟨1 / 2, hσ⟩
  simp only [factorialTailFourier, hw] at hL
  have hTi : Integrable T := (factorialWeightedTail_complex_integrable n ⟨1 / 2, hσ⟩).congr
    (Eventually.of_forall fun x => by simp [factorialWeightedTail, hT])
  have hFc : Continuous (𝓕 T) := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hTi
  have hH : Integrable fun ξ : ℝ => ‖𝓕 T ξ‖ ^ 2 * Real.log (2 + 2 * Real.pi * |ξ|) := by
    refine (hL.const_mul (1 + Real.log (2 + 2 * Real.pi))).mono'
      ((hFc.norm.pow 2).mul (Continuous.log (by fun_prop) fun ξ => by
        have := Real.pi_pos; positivity)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    have hlog : 0 ≤ Real.log (2 + 2 * Real.pi * |ξ|) := Real.log_nonneg (by
      nlinarith [abs_nonneg ξ, Real.pi_pos])
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hlog)]
    calc ‖𝓕 T ξ‖ ^ 2 * Real.log (2 + 2 * Real.pi * |ξ|) ≤
          ‖𝓕 T ξ‖ ^ 2 * ((1 + Real.log (2 + 2 * Real.pi)) * suzukiLogWeight ξ) :=
          mul_le_mul_of_nonneg_left (log_two_add_two_pi_mul_abs_le ξ) (sq_nonneg _)
      _ = _ := by ring
  have hfun : (fun r : ℝ => ‖paperFT T r‖ ^ 2 * Real.log (2 + |r|)) = fun r =>
      (fun ξ : ℝ => ‖𝓕 T ξ‖ ^ 2 * Real.log (2 + 2 * Real.pi * |ξ|)) (r / (-(2 * Real.pi))) := by
    funext r
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [Zeta23.EF.paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
    congr 3
    rw [abs_div, abs_neg, abs_of_pos hpi]
    field_simp
  rw [hfun]
  exact hH.comp_div (by have := Real.pi_pos; linarith)

/-- The Gamma-weighted spectral density of a raw tail combination is integrable. -/
theorem integrable_norm_sq_paperFT_factorialTailCombination_mul_gammaBracket (S : Finset ℕ)
    (d : ℕ → ℝ) :
    Integrable fun r : ℝ =>
      ‖paperFT (fun x => (factorialTailCombination S d x : ℂ)) r‖ ^ 2 * EF.gammaBracket r := by
  set g : ℝ → ℂ := fun x => (factorialTailCombination S d x : ℂ)
  have hgc : Continuous fun r : ℝ => paperFT g r :=
    RHTower.KernelStrip.continuous_paperFT_of_integrable (integrable_factorialTailCombination S d).1
  have hlin (r : ℝ) : paperFT g r =
      ∑ n ∈ S, (d n : ℂ) * paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r := by
    have h := paperFT_factorialTailCombination S d (s := 1 / 2 + Complex.I * r) (by simp; norm_num)
    rwa [gammaOf_half_add_I_mul] at h
  have hTi (n : ℕ) : Integrable fun r : ℝ =>
      ‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 := by
    have h := integrable_factorialTailCombination {n} (fun _ => 1)
    simp only [factorialTailCombination, Finset.sum_singleton, one_mul] at h
    exact RHTower.KernelStrip.integrable_norm_sq_paperFT h.1 h.2
  set K := RHTower.EvenSector.gammaLogConst with hK
  have hmaj : Integrable fun r : ℝ => (S.card : ℝ) * ∑ n ∈ S, d n ^ 2 *
      (‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 * |K| +
        ‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 * Real.log (2 + |r|)) :=
    (integrable_finsetSum _ fun n _ => (((hTi n).mul_const _).add
      (integrable_norm_sq_paperFT_tail_mul_log n)).const_mul _).const_mul _
  refine hmaj.mono' ((hgc.norm.pow 2).mul RHTower.WeilHerglotz.continuous_gammaBracket
    ).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
  have hG := RHTower.EvenSector.abs_gammaBracket_le_log r
  have hlog : 0 ≤ Real.log (2 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
  have hsq : ‖paperFT g r‖ ^ 2 ≤ S.card * ∑ n ∈ S, d n ^ 2 *
      ‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 := by
    rw [hlin]
    have h1 := norm_sum_le S fun n => (d n : ℂ) *
      paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r
    have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => ‖(d n : ℂ) *
      paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖)
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (h2.trans (le_of_eq ?_))
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  calc ‖paperFT g r‖ ^ 2 * |EF.gammaBracket r| ≤
        (S.card * ∑ n ∈ S, d n ^ 2 *
          ‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2) *
          (|K| + Real.log (2 + |r|)) :=
        mul_le_mul hsq (hG.trans (by linarith [le_abs_self K])) (abs_nonneg _) (by positivity)
    _ = _ := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring

/-- **Gamma-channel smoothing limit.** -/
theorem tendsto_archGammaEnergy_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) :
    Tendsto (fun k => archGammaEnergy (factorialTailCombinationSmoothed S d k)) atTop
      (𝓝 (archGammaEnergy (factorialTailCombination S d))) := by
  set g : ℝ → ℂ := fun x => (factorialTailCombination S d x : ℂ) with hg
  have hDi := integrable_norm_sq_paperFT_factorialTailCombination_mul_gammaBracket S d
  have hre (r : ℝ) : -1 < (1 / 2 + Complex.I * r : ℂ).re := by simp; norm_num
  have hfac (k : ℕ) (r : ℝ) :
      paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) r =
        factorialMuntzKernelReadout k (1 / 2 + Complex.I * r) * paperFT g r := by
    have h := paperFT_factorialTailCombinationSmoothed S d k (hre r)
    rwa [gammaOf_half_add_I_mul] at h
  have hκ (k : ℕ) (r : ℝ) : ‖factorialMuntzKernelReadout k (1 / 2 + Complex.I * r)‖ ≤
      Real.exp 1 := factorialMuntzKernelReadout_bound k (by simp) (by simp; norm_num)
  unfold archGammaEnergy
  refine Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence
    (fun r => Real.exp 1 ^ 2 * ‖‖paperFT g r‖ ^ 2 * EF.gammaBracket r‖) (fun k => ?_)
    (hDi.norm.const_mul _) (fun k => ?_) ?_)
  · have hc : Continuous fun r : ℝ =>
        paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) r :=
      RHTower.KernelStrip.continuous_paperFT_of_integrable
        ((factorialTailCombinationSmoothed_readout S d k
          (s := 1 / 2) (by norm_num)).2.1.congr (Eventually.of_forall fun x => by simp))
    exact ((hc.norm.pow 2).mul RHTower.WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
  · refine Eventually.of_forall fun r => ?_
    rw [hfac]
    simp only [norm_mul, norm_pow, norm_norm, mul_pow]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hκ k r) 2
    calc _ = ‖factorialMuntzKernelReadout k (1 / 2 + Complex.I * r)‖ ^ 2 *
          (‖paperFT g r‖ ^ 2 * ‖EF.gammaBracket r‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)
  · refine Eventually.of_forall fun r => ?_
    simp_rw [hfac]
    have h := (((factorialMuntzKernelReadout_tendsto (1 / 2 + Complex.I * r)).mul_const
      (paperFT g r)).norm.pow 2).mul_const (EF.gammaBracket r)
    simpa only [one_mul] using h

/-- **Explicit formula for raw real tail combinations.** The literal complete identity
`archPoleEnergy g = Re W(g, g) + T_Λ(g ⋆ g̃)` holds for every finite real combination of the
non-smooth correction tails, with the Gamma integral, both polar readouts, and the full von
Mangoldt atom series. -/
theorem archPoleEnergy_factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) :
    archPoleEnergy (factorialTailCombination S d) =
      (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ))).re +
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (factorialTailCombination S d) (factorialTailCombination S d)) := by
  have hpole : Tendsto (fun k => archPoleTerm (factorialTailCombinationSmoothed S d k)) atTop
      (𝓝 (archPoleTerm (factorialTailCombination S d))) := by
    have h0 := tendsto_paperFT_factorialTailCombinationSmoothed S d (s := 0) (by norm_num)
    have h1 := tendsto_paperFT_factorialTailCombinationSmoothed S d (s := 1) (by norm_num)
    rw [gammaOf_zero_eq] at h0
    rw [gammaOf_one_eq] at h1
    have hprod := h0.mul ((Complex.continuous_conj.tendsto _).comp h1)
    have hre := ((Complex.continuous_re.tendsto _).comp hprod).const_mul 2
    simpa only [Function.comp_def, archPoleTerm] using hre
  have hL : Tendsto (fun k => archPoleEnergy (factorialTailCombinationSmoothed S d k)) atTop
      (𝓝 (archPoleEnergy (factorialTailCombination S d))) := by
    simp only [archPoleEnergy_eq_pole_add_gamma]
    exact hpole.add (tendsto_archGammaEnergy_factorialTailCombinationSmoothed S d)
  have hR := ((Complex.continuous_re.tendsto _).comp
    (tendsto_W_factorialTailCombinationSmoothed S d)).add
      (tendsto_atomPairing_factorialTailCombinationSmoothed S d)
  exact tendsto_nhds_unique hL (hR.congr fun k =>
    (archPoleEnergy_factorialTailCombinationSmoothed S d k).symm)

/-! ## The exact Weil identity for complex coefficients -/

/-- Hermitian correlation `C_{X,Y}(y) = ∫ X(t) conj Y(t - y) dt` of complex sources. -/
def hermitianCrossCorr (X Y : ℝ → ℂ) (y : ℝ) : ℂ := ∫ t, X t * conj (Y (t - y))

/-- Complex atom series `∑_{n ≥ 2} w(n) n^{-1/2} (C(log n) + C(-log n))`. -/
def complexAtomPairing (w : ℕ → ℝ) (C : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (((if 2 ≤ n then w n / Real.sqrt n else 0 : ℝ)) : ℂ) *
    (C (Real.log n) + C (-Real.log n))

theorem integrable_factorialTailCombination_mul_translate (S : Finset ℕ) (d e : ℕ → ℝ)
    (y : ℝ) :
    Integrable fun t => factorialTailCombination S d t * factorialTailCombination S e (t - y) := by
  set Cd := factorialTailCombinationDecayConstant S d
  set Ce := factorialTailCombinationDecayConstant S e
  have hCd : 0 ≤ Cd := factorialTailCombinationDecayConstant_nonneg S d
  have hCe : 0 ≤ Ce := factorialTailCombinationDecayConstant_nonneg S e
  refine ((RHTower.EvenSector.integrable_exp_neg_rate_abs (a := 3 / 2) (by norm_num)).const_mul
    (Cd * Ce)).mono' ((measurable_factorialTailCombination S d).mul
      ((measurable_factorialTailCombination S e).comp (measurable_id.sub_const y))
      ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := abs_factorialTailCombination_le S d t
  have h2 := abs_factorialTailCombination_le S e (t - y)
  have hexp : Real.exp (-((3 / 2 : ℝ) * |t - y|)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (t - y)])
  have h2' : |factorialTailCombination S e (t - y)| ≤ Ce :=
    h2.trans (by nlinarith)
  calc |factorialTailCombination S d t| * |factorialTailCombination S e (t - y)| ≤
        (Cd * Real.exp (-((3 / 2 : ℝ) * |t|))) * Ce :=
        mul_le_mul h1 h2' (abs_nonneg _) (by positivity)
    _ = Cd * Ce * Real.exp (-((3 / 2 : ℝ) * |t|)) := by ring

/-- The Hermitian correlation of `u + iv` splits into real correlations. -/
theorem hermitianCrossCorr_factorialTailCombination (S : Finset ℕ) (du dv : ℕ → ℝ) (y : ℝ) :
    hermitianCrossCorr
        (fun x => (factorialTailCombination S du x : ℂ) +
          Complex.I * (factorialTailCombination S dv x : ℂ))
        (fun x => (factorialTailCombination S du x : ℂ) +
          Complex.I * (factorialTailCombination S dv x : ℂ)) y =
      ((crossCorr (factorialTailCombination S du) (factorialTailCombination S du) y +
          crossCorr (factorialTailCombination S dv) (factorialTailCombination S dv) y : ℝ) : ℂ) +
        Complex.I *
          ((crossCorr (factorialTailCombination S dv) (factorialTailCombination S du) y -
            crossCorr (factorialTailCombination S du) (factorialTailCombination S dv) y : ℝ) :
              ℂ) := by
  set u := factorialTailCombination S du
  set v := factorialTailCombination S dv
  have hi (a b : ℕ → ℝ) : Integrable fun t =>
      ((factorialTailCombination S a t * factorialTailCombination S b (t - y) : ℝ) : ℂ) :=
    (integrable_factorialTailCombination_mul_translate S a b y).ofReal
  have hpt : (fun t => ((u t : ℂ) + Complex.I * (v t : ℂ)) *
      conj ((u (t - y) : ℂ) + Complex.I * (v (t - y) : ℂ))) = fun t =>
      ((u t * u (t - y) : ℝ) : ℂ) + ((v t * v (t - y) : ℝ) : ℂ) +
        Complex.I * (((v t * u (t - y) : ℝ) : ℂ) - ((u t * v (t - y) : ℝ) : ℂ)) := by
    funext t
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul]
    linear_combination (-(v t : ℂ) * (v (t - y) : ℂ)) * Complex.I_sq
  have h12 : Integrable fun t =>
      ((u t * u (t - y) : ℝ) : ℂ) + ((v t * v (t - y) : ℝ) : ℂ) := (hi du du).add (hi dv dv)
  have h34 : Integrable fun t =>
      Complex.I * (((v t * u (t - y) : ℝ) : ℂ) - ((u t * v (t - y) : ℝ) : ℂ)) :=
    ((hi dv du).sub (hi du dv)).const_mul _
  have h3m : Integrable fun t =>
      ((v t * u (t - y) : ℝ) : ℂ) - ((u t * v (t - y) : ℝ) : ℂ) := (hi dv du).sub (hi du dv)
  unfold hermitianCrossCorr crossCorr
  rw [hpt, integral_add h12 h34, integral_add (hi du du) (hi dv dv), integral_const_mul,
    integral_sub (hi dv du) (hi du dv), integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]
  push_cast
  ring

/-- The symmetrized Hermitian correlation of `u + iv` is the real sum of the two real
symmetrized correlations. -/
theorem hermitianCrossCorr_factorialTailCombination_symm (S : Finset ℕ) (du dv : ℕ → ℝ)
    (y : ℝ) :
    hermitianCrossCorr
        (fun x => (factorialTailCombination S du x : ℂ) +
          Complex.I * (factorialTailCombination S dv x : ℂ))
        (fun x => (factorialTailCombination S du x : ℂ) +
          Complex.I * (factorialTailCombination S dv x : ℂ)) y +
      hermitianCrossCorr
        (fun x => (factorialTailCombination S du x : ℂ) +
          Complex.I * (factorialTailCombination S dv x : ℂ))
        (fun x => (factorialTailCombination S du x : ℂ) +
          Complex.I * (factorialTailCombination S dv x : ℂ)) (-y) =
      ((crossCorr (factorialTailCombination S du) (factorialTailCombination S du) y +
          crossCorr (factorialTailCombination S du) (factorialTailCombination S du) (-y) +
        (crossCorr (factorialTailCombination S dv) (factorialTailCombination S dv) y +
          crossCorr (factorialTailCombination S dv) (factorialTailCombination S dv) (-y)) : ℝ) :
        ℂ) := by
  rw [hermitianCrossCorr_factorialTailCombination, hermitianCrossCorr_factorialTailCombination,
    ← RHTower.crossCorr_swap (X := factorialTailCombination S dv)
      (Y := factorialTailCombination S du) y,
    ← RHTower.crossCorr_swap (X := factorialTailCombination S du)
      (Y := factorialTailCombination S dv) y]
  push_cast
  ring

/-- The complex prime series of `u + iv` is the real sum of the two real prime series. -/
theorem complexAtomPairing_factorialTailCombination (S : Finset ℕ) (du dv : ℕ → ℝ) :
    complexAtomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (hermitianCrossCorr
          (fun x => (factorialTailCombination S du x : ℂ) +
            Complex.I * (factorialTailCombination S dv x : ℂ))
          (fun x => (factorialTailCombination S du x : ℂ) +
            Complex.I * (factorialTailCombination S dv x : ℂ))) =
      ((atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (factorialTailCombination S du) (factorialTailCombination S du)) +
        atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (factorialTailCombination S dv) (factorialTailCombination S dv)) : ℝ) :
        ℂ) := by
  unfold complexAtomPairing atomPairing
  rw [← (summable_norm_atomTerm_factorialTailCombination S du).of_norm.tsum_add
    (summable_norm_atomTerm_factorialTailCombination S dv).of_norm, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [hermitianCrossCorr_factorialTailCombination_symm]
  push_cast
  ring

theorem paperFT_ofReal_im_eq_zero_of_neg_conj (u : ℝ → ℝ) {z : ℂ} (hz : -conj z = z) :
    (paperFT (fun x => (u x : ℂ)) z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  conv_rhs => rw [← hz, EvenSector.paperFT_ofReal_neg_conj, Complex.conj_conj]

theorem norm_add_I_mul_sq (a b : ℂ) :
    ‖a + Complex.I * b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (a * conj b).im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Exact Weil identity for complex coefficients.** For every finite complex family `b`, the
literal tail combination `f_b = ∑_n (b_n / a_n) T_n` has an integrable Gamma density, a real and
absolutely convergent von Mangoldt series, and
`Re W(f_b, f_b) = (1/2π) ∫ |F_b|² g + 2 Re(F_b(i/2) conj F_b(-i/2)) - T_Λ(C_b)`. -/
theorem factorialTailSpan_exact_weil_identity (S : Finset ℕ) (b : ℕ → ℂ) :
    Integrable (fun r : ℝ => ‖paperFT (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
        (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 * EF.gammaBracket r) ∧
    (complexAtomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (hermitianCrossCorr
          (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
            (factorialMuntzCorrectedTail n x : ℂ))
          (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
            (factorialMuntzCorrectedTail n x : ℂ)))).im = 0 ∧
    (zetaZeroConfig.W
        (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
          (factorialMuntzCorrectedTail n x : ℂ))
        (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
          (factorialMuntzCorrectedTail n x : ℂ))).re =
      1 / (2 * Real.pi) * (∫ r : ℝ, ‖paperFT (fun x => ∑ n ∈ S,
          b n / (factorialTailAmplitude n : ℂ) * (factorialMuntzCorrectedTail n x : ℂ)) r‖ ^ 2 *
          EF.gammaBracket r) +
        2 * (paperFT (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
            (factorialMuntzCorrectedTail n x : ℂ)) (Complex.I / 2) *
          conj (paperFT (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
            (factorialMuntzCorrectedTail n x : ℂ)) (-Complex.I / 2))).re -
        (complexAtomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (hermitianCrossCorr
            (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
              (factorialMuntzCorrectedTail n x : ℂ))
            (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
              (factorialMuntzCorrectedTail n x : ℂ)))).re := by
  set du : ℕ → ℝ := fun n => (b n / (factorialTailAmplitude n : ℂ)).re
  set dv : ℕ → ℝ := fun n => (b n / (factorialTailAmplitude n : ℂ)).im
  set u := factorialTailCombination S du with hu
  set v := factorialTailCombination S dv with hv
  have hF : (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
      (factorialMuntzCorrectedTail n x : ℂ)) =
      fun x => (u x : ℂ) + Complex.I * (v x : ℂ) := by
    funext x
    simp only [hu, hv, factorialTailCombination]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    conv_lhs => rw [← Complex.re_add_im (b n / (factorialTailAmplitude n : ℂ))]
    ring
  rw [hF]
  have hread (dd : ℕ → ℝ) {s : ℂ} (hs : -1 < s.re) :=
    (factorialTailCombinationSmoothed_readout S dd 0 hs).1
  have hlin (s : ℂ) (hs : -1 < s.re) :
      paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) (gammaOf s) =
        paperFT (fun x => (u x : ℂ)) (gammaOf s) +
          Complex.I * paperFT (fun x => (v x : ℂ)) (gammaOf s) :=
    paperFT_ofReal_add_I_mul u v (hread du hs) (hread dv hs)
  have hreal (r : ℝ) : -1 < (1 / 2 + Complex.I * r : ℂ).re := by simp; norm_num
  -- Gamma channel
  have hlinr (r : ℝ) : paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) r =
      paperFT (fun x => (u x : ℂ)) r + Complex.I * paperFT (fun x => (v x : ℂ)) r := by
    have h := hlin _ (hreal r)
    rwa [gammaOf_half_add_I_mul] at h
  set Fu : ℝ → ℂ := fun r => paperFT (fun x => (u x : ℂ)) r
  set Fv : ℝ → ℂ := fun r => paperFT (fun x => (v x : ℂ)) r
  have hneg (w : ℝ → ℝ) (r : ℝ) :
      paperFT (fun x => (w x : ℂ)) ((-r : ℝ) : ℂ) = conj (paperFT (fun x => (w x : ℂ)) r) := by
    rw [Complex.ofReal_neg, EvenSector.paperFT_ofReal_neg_conj, Complex.conj_ofReal]
  have hIu : Integrable fun r => ‖Fu r‖ ^ 2 * EF.gammaBracket r :=
    integrable_norm_sq_paperFT_factorialTailCombination_mul_gammaBracket S du
  have hIv : Integrable fun r => ‖Fv r‖ ^ 2 * EF.gammaBracket r :=
    integrable_norm_sq_paperFT_factorialTailCombination_mul_gammaBracket S dv
  have hIuv : Integrable fun r =>
      ‖Fu r‖ ^ 2 * EF.gammaBracket r + ‖Fv r‖ ^ 2 * EF.gammaBracket r := hIu.add hIv
  have hFuc : Continuous Fu := RHTower.KernelStrip.continuous_paperFT_of_integrable
    (integrable_factorialTailCombination S du).1
  have hFvc : Continuous Fv := RHTower.KernelStrip.continuous_paperFT_of_integrable
    (integrable_factorialTailCombination S dv).1
  set h : ℝ → ℝ := fun r => 2 * (Fu r * conj (Fv r)).im * EF.gammaBracket r with hh
  have hIh : Integrable h := by
    refine (hIu.norm.add hIv.norm).mono' (((Complex.continuous_im.comp
      (hFuc.mul (Complex.continuous_conj.comp hFvc))).const_mul 2).mul
        RHTower.WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    have him : |(Fu r * conj (Fv r)).im| ≤ ‖Fu r‖ * ‖Fv r‖ := by
      refine (Complex.abs_im_le_norm _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_conj]
    have hg := abs_nonneg (EF.gammaBracket r)
    show ‖h r‖ ≤ ‖‖Fu r‖ ^ 2 * EF.gammaBracket r‖ + ‖‖Fv r‖ ^ 2 * EF.gammaBracket r‖
    simp only [hh, Real.norm_eq_abs, abs_mul, abs_two, abs_pow, abs_norm]
    calc 2 * |(Fu r * conj (Fv r)).im| * |EF.gammaBracket r| ≤
          2 * (‖Fu r‖ * ‖Fv r‖) * |EF.gammaBracket r| := by gcongr
      _ ≤ (‖Fu r‖ ^ 2 + ‖Fv r‖ ^ 2) * |EF.gammaBracket r| :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖Fu r‖ - ‖Fv r‖)]) hg
      _ = _ := by ring
  have hodd (r : ℝ) : h (-r) = -h r := by
    simp only [hh, Fu, Fv, hneg, RHTower.WeilWorkPBAP.packet_gammaBracket_neg, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hh0 : ∫ r, h r = 0 := by
    have h1 := integral_neg_eq_self h (volume : Measure ℝ)
    simp only [hodd, integral_neg] at h1
    linarith
  have hdens : (fun r : ℝ => ‖paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) r‖ ^ 2 *
      EF.gammaBracket r) = fun r => (‖Fu r‖ ^ 2 * EF.gammaBracket r +
        ‖Fv r‖ ^ 2 * EF.gammaBracket r) + h r := by
    funext r
    rw [hlinr, norm_add_I_mul_sq]
    simp only [hh, Fu, Fv]
    ring
  have hGamma : (∫ r : ℝ, ‖paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) r‖ ^ 2 *
      EF.gammaBracket r) = (∫ r : ℝ, ‖Fu r‖ ^ 2 * EF.gammaBracket r) +
        ∫ r : ℝ, ‖Fv r‖ ^ 2 * EF.gammaBracket r := by
    rw [hdens, integral_add hIuv hIh, integral_add hIu hIv, hh0, add_zero]
  -- polar channel
  have hP0 := hlin 0 (by norm_num)
  have hP1 := hlin 1 (by norm_num)
  rw [gammaOf_zero_eq] at hP0
  rw [gammaOf_one_eq] at hP1
  have hc0 : -conj (Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
    ring
  have hc1 : -conj (-Complex.I / 2) = -Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, map_ofNat]
    ring
  have ru0 := paperFT_ofReal_im_eq_zero_of_neg_conj u hc0
  have rv0 := paperFT_ofReal_im_eq_zero_of_neg_conj v hc0
  have ru1 := paperFT_ofReal_im_eq_zero_of_neg_conj u hc1
  have rv1 := paperFT_ofReal_im_eq_zero_of_neg_conj v hc1
  have hPole : (paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) (Complex.I / 2) *
      conj (paperFT (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) (-Complex.I / 2))).re =
      (paperFT (fun x => (u x : ℂ)) (Complex.I / 2) *
        conj (paperFT (fun x => (u x : ℂ)) (-Complex.I / 2))).re +
      (paperFT (fun x => (v x : ℂ)) (Complex.I / 2) *
        conj (paperFT (fun x => (v x : ℂ)) (-Complex.I / 2))).re := by
    rw [hP0, hP1]
    set a0 := paperFT (fun x => (u x : ℂ)) (Complex.I / 2)
    set b0 := paperFT (fun x => (v x : ℂ)) (Complex.I / 2)
    set a1 := paperFT (fun x => (u x : ℂ)) (-Complex.I / 2)
    set b1 := paperFT (fun x => (v x : ℂ)) (-Complex.I / 2)
    simp only [map_add, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, ru0, rv0, ru1, rv1]
    ring
  -- prime channel and zero side
  rw [complexAtomPairing_factorialTailCombination]
  obtain ⟨-, hW⟩ := zetaZeroConfig_W_ofReal_add_I_mul u v
    (fun s h0 _ => hread du (by linarith)) (fun s h0 _ => hread dv (by linarith))
    (factorialTailCombination_zeroSquare_summable S du)
    (factorialTailCombination_zeroSquare_summable S dv)
  have Eu := archPoleEnergy_factorialTailCombination S du
  have Ev := archPoleEnergy_factorialTailCombination S dv
  rw [archPoleEnergy_eq_pole_add_gamma] at Eu Ev
  unfold archPoleTerm archGammaEnergy at Eu Ev
  refine ⟨?_, Complex.ofReal_im _, ?_⟩
  · rw [hdens]
    exact hIuv.add hIh
  rw [hW, Complex.add_re, Complex.ofReal_re, hGamma, hPole]
  simp only [Fu, Fv] at *
  linarith


end

end GaloisForLFunctions.ArithmeticPositivityTheory
