import GaloisForLFunctions.RHTower.EvenWeilRHCriterion
import GaloisForLFunctions.RHTower.TiltedWeilNyquistInertia
import GaloisForLFunctions.RHTower.WeilConeCriticalZeroCarriedRigidity
import GaloisForLFunctions.RHTower.WeilConeDegreePoleSandwich

/-!
# RH is the one-bound-state law for the archimedean-minus-prime Weil form

On the autocorrelation `k = f ⋆ f̃` of a test `f`, the Weil functional of `ζ` is pole plus
archimedean minus prime part. Let

`M(f) = Re[(1/2π) ∫ k̂ γ − Σ_{n ≥ 2} Λ(n) n^{−1/2} (k(log n) + k(−log n))]`

be the part without the pole (`markovEnergy`, `markovEnergy_eq_arch_sub_primes`). Off the
diagonal both of its kernels are nonpositive (`Λ ≥ 0`, and the Gamma kernel `e^{|x|/2}/sinh|x|` is positive), so `M` is a jump (Dirichlet)
form plus a diagonal term. The pole term `P(f) = 2 Re(f̂(i/2) · conj f̂(−i/2))` has signature `(1,1)`.

**Theorem** (`riemannHypothesis_iff_not_exists_negDef_markovPlane`). RH holds if and only if no
plane of `C²` compactly supported tests carries a negative definite `M`. Unconditionally `M` has a
negative direction (`exists_markovEnergy_neg`). So RH says that `M` has exactly one negative square.

* Under RH, `W = M + P ≥ 0`. Every plane contains a nonzero test with `f̂(i/2) = 0`, so
  `P(f) = 0` and `M(f) = W(f) ≥ 0`.
* Without RH, there is a smooth even real test `u` with `û(±i/2) = 0` and `Re W(u, u) = −w < 0`
  (`riemannHypothesis_iff_forall_evenPoleWeilNonneg`). The truncated Riemann kernel `Φ_L` is almost
  null for `W`, because `Φ̂ = Ξ` vanishes at every zero. Its pole term stays at least `2c²`, with
  `c = ∫₀¹ Φ(x) e^{−x/2} dx > 0`. With tail energy `E_L`, `K = (5/4) S` and `E_u` the energy of
  `u`, on the plane spanned by `Φ_L` and `u`
  `M(aΦ_L + bu) ≤ −w|b|² + 2K E_L E_u |a||b| − (2c² − K E_L²)|a|²`,
  which is negative definite once `E_L` is small.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## The archimedean-minus-prime energy -/

/-- The archimedean-minus-prime part of the Weil functional of `ζ` on the autocorrelation of `f`. -/
def markovEnergy (f : ℝ → ℂ) : ℝ :=
  (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest f f) -
    weilPoleTerm (EF.weilTest f f)).re

/-- `markovEnergy` is the archimedean integral minus the prime sum. -/
theorem markovEnergy_eq_arch_sub_primes (f : ℝ → ℂ) :
    markovEnergy f = ((1 / (2 * π) : ℂ) * (∫ r : ℝ, paperFT (EF.weilTest f f) r *
        (EF.gammaBracket r : ℂ)) -
      ∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) :
        ℂ) * (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re := by
  unfold markovEnergy weilFullFunctional weilPoleTerm
  congr 1
  ring

/-- On `C²` compactly supported tests, `M(f) = Re W(f, f) − Re P(f)`. -/
theorem markovEnergy_eq_W_sub {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    markovEnergy f = (zetaZeroConfig.W f f).re - (weilPoleTerm (EF.weilTest f f)).re := by
  unfold markovEnergy
  rw [Complex.sub_re, zeta_W_eq_weilFullFunctional hf hfc]

/-- The pole term of an autocorrelation: `P(f) = f̂(i/2) conj f̂(−i/2) + f̂(−i/2) conj f̂(i/2)`. -/
theorem weilPoleTerm_weilTest_eq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    weilPoleTerm (EF.weilTest f f) =
      paperFT f (I / 2) * (starRingEnd ℂ) (paperFT f (-I / 2)) +
        paperFT f (-I / 2) * (starRingEnd ℂ) (paperFT f (I / 2)) := by
  unfold weilPoleTerm
  rw [EF.paperFT_weilTest hf hf hfc hfc, EF.paperFT_weilTest hf hf hfc hfc, conj_I_div_two,
    conj_neg_I_div_two]

/-! ## Linearity of the transform -/

theorem integrable_mul_cexp_of_compact {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (z : ℂ) : Integrable fun u : ℝ => f u * cexp (I * z * u) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right

theorem paperFT_smul_add_smul {F G : ℝ → ℂ} (a b z : ℂ)
    (hF : Integrable fun u : ℝ => F u * cexp (I * z * u))
    (hG : Integrable fun u : ℝ => G u * cexp (I * z * u)) :
    paperFT (fun u => a * F u + b * G u) z = a * paperFT F z + b * paperFT G z := by
  unfold paperFT
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hF.const_mul a) (hG.const_mul b)]
  congr 1
  funext u
  ring

/-! ## Sums over the zeros controlled pointwise -/

/-- A family over the zeros with `‖x_ρ‖ ≤ m_ρ C/(1 + |t_ρ|)²` is summable with sum at most
`(5/4) S C`. -/
theorem summable_and_norm_tsum_le_of_zeroBound {x : zetaZeroConfig.carrier → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hx : ∀ ρ : zetaZeroConfig.carrier,
      ‖x ρ‖ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C / (1 + |(ρ : ℂ).im|) ^ 2)) :
    Summable x ∧ ‖∑' ρ, x ρ‖ ≤ 5 / 4 * zeroSumZ * C := by
  have hb : ∀ ρ : zetaZeroConfig.carrier, ‖x ρ‖ ≤
      (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    intro ρ
    have hq := one_div_one_add_abs_im_sq_le (zetaZeroConfig.strip _ ρ.2)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have h1 : C / (1 + |(ρ : ℂ).im|) ^ 2 ≤ (5 / 4) * C *
        (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
      rw [div_eq_mul_one_div]
      calc C * (1 / (1 + |(ρ : ℂ).im|) ^ 2)
          ≤ C * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
            mul_le_mul_of_nonneg_left hq hC
        _ = _ := by ring
    calc ‖x ρ‖ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C / (1 + |(ρ : ℂ).im|) ^ 2) := hx ρ
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
          ((5 / 4) * C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul_of_nonneg_left h1 hm
      _ = _ := by ring
  have hsB : Summable (fun ρ : zetaZeroConfig.carrier =>
      (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    summable_zeroSumZ.mul_left _
  have hs : Summable (fun ρ => ‖x ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsB
  refine ⟨hs.of_norm, ?_⟩
  calc ‖∑' ρ, x ρ‖ ≤ ∑' ρ, ‖x ρ‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ρ : zetaZeroConfig.carrier,
          (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        Summable.tsum_le_tsum hb hs hsB
    _ = (5 / 4) * C * zeroSumZ := by rw [tsum_mul_left]; rfl
    _ = 5 / 4 * zeroSumZ * C := by ring

/-! ## Under RH every plane has a nonnegative direction -/

/-- **Under RH, `M` is nonnegative somewhere on every plane.** A nonzero combination with
vanishing transform at `i/2` has no pole term, so its `M` is its Weil energy. -/
theorem exists_markovEnergy_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ∃ a b : ℂ, (a, b) ≠ 0 ∧ 0 ≤ markovEnergy (fun x => a * f x + b * g x) := by
  have key : ∀ a b : ℂ, a * paperFT f (I / 2) + b * paperFT g (I / 2) = 0 →
      0 ≤ markovEnergy (fun x => a * f x + b * g x) := by
    intro a b hab
    set h : ℝ → ℂ := fun x => a * f x + b * g x with hh
    have hhd : ContDiff ℝ 2 h := (contDiff_const.mul hf).add (contDiff_const.mul hg)
    have hhc : HasCompactSupport h := (hfc.mul_left).add hgc.mul_left
    have hh0 : paperFT h (I / 2) = 0 := by
      rw [hh, paperFT_smul_add_smul a b _ (integrable_mul_cexp_of_compact hf.continuous hfc _)
        (integrable_mul_cexp_of_compact hg.continuous hgc _)]
      exact hab
    have hpole : weilPoleTerm (EF.weilTest h h) = 0 := by
      rw [weilPoleTerm_weilTest_eq hhd.continuous hhc, hh0, map_zero, zero_mul, mul_zero,
        add_zero]
    have hW := (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) h hhd hhc
    rw [markovEnergy_eq_W_sub hhd hhc, hpole, Complex.zero_re, sub_zero,
      zeta_W_eq_weilFullFunctional hhd hhc]
    exact hW
  by_cases h0 : paperFT f (I / 2) = 0
  · exact ⟨1, 0, by simp, key 1 0 (by rw [h0]; ring)⟩
  · refine ⟨paperFT g (I / 2), -paperFT f (I / 2), fun h => h0 ?_, key _ _ (by ring)⟩
    have := congrArg Prod.snd h
    simpa using this

/-! ## The truncated Riemann kernel -/

theorem truncatedRiemannKernelReal_neg (L u : ℝ) :
    truncatedRiemannKernelReal L (-u) = truncatedRiemannKernelReal L u := by
  unfold truncatedRiemannKernelReal riemannKernelReal bulkCutoff
  rw [abs_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem truncatedRiemannKernel_eq_ofReal (L : ℝ) :
    truncatedRiemannKernel L = fun u => ((truncatedRiemannKernelReal L u : ℝ) : ℂ) :=
  funext (truncatedRiemannKernel_eq L)

/-- The pole value of the truncated kernel is bounded below uniformly in `L ≥ 2`. -/
theorem exists_integral_truncatedRiemannKernelReal_exp_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 2 ≤ L →
      c ≤ ∫ x, truncatedRiemannKernelReal L x * Real.exp (-(x / 2)) := by
  let g : ℝ → ℝ := fun x => riemannKernelReal x * Real.exp (-(x / 2))
  have hgc : Continuous g := continuous_riemannKernelReal.mul (by fun_prop)
  refine ⟨∫ x in (0 : ℝ)..1, g x,
    intervalIntegral.intervalIntegral_pos_of_pos_on (hgc.intervalIntegrable 0 1)
      (fun x _ => mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)) one_pos, fun L hL => ?_⟩
  have hint : Integrable (fun x => truncatedRiemannKernelReal L x * Real.exp (-(x / 2))) :=
    ((continuous_truncatedRiemannKernelReal L).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_truncatedRiemannKernelReal L).mul_right
  have hsub := setIntegral_le_integral (s := Ioc 0 1) hint
    (Eventually.of_forall fun x =>
      mul_nonneg (truncatedRiemannKernelReal_nonneg L x) (Real.exp_pos _).le)
  refine le_trans (le_of_eq ?_) hsub
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
  have hx1 : |x| ≤ L - 1 := by rw [abs_of_pos hx.1]; linarith [hx.2]
  simp only [g, truncatedRiemannKernelReal, bulkCutoff_eq_one hx1, mul_one]

/-! ## Without RH there is a negative definite plane -/

/-- Without RH there is a smooth even real pole-free test of negative Weil energy. -/
theorem exists_even_poleFree_negative_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      paperFT (fun x => (u x : ℂ)) (I / 2) = 0 ∧
      (zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))).re < 0 := by
  have h : ¬ ∀ A : ℝ, 0 < A → EvenPoleWeilNonneg A := fun h =>
    hRH (riemannHypothesis_iff_forall_evenPoleWeilNonneg.2 h)
  push Not at h
  obtain ⟨A, hA, hnot⟩ := h
  unfold EvenPoleWeilNonneg at hnot
  push Not at hnot
  obtain ⟨u, hu, hcpt, hsupp, heven, hpole, hneg⟩ := hnot
  have hut : tsupport u ⊆ Ioo (-(A + 1)) (A + 1) := by
    refine (closure_minimal (s := Function.support u) (t := Icc (-A) A) (fun x hx => ?_)
      isClosed_Icc).trans (Icc_subset_Ioo (show -(A + 1) < -A by linarith)
        (show A < A + 1 by linarith))
    by_contra hc
    have : A < |x| := by
      rw [Set.mem_Icc, not_and_or] at hc
      rcases hc with h1 | h1
      · push Not at h1; exact lt_abs.2 (Or.inr (by linarith))
      · push Not at h1; exact lt_abs.2 (Or.inl h1)
    exact hx (hsupp x this)
  refine ⟨u, hu.of_le (WithTop.coe_le_coe.2 le_top), hcpt, heven, ?_, ?_⟩
  · rw [paperFT_ofReal_I_half_eq_integral, ← integral_mul_exp_half_of_even heven, hpole,
      Complex.ofReal_zero]
  · rw [re_W_ofReal_eq_tsum_sq hu hcpt heven (by linarith) hut]
    exact hneg

/-- The pointwise remainder of `W(aΦ + bU, aΦ + bU) − |b|² W(U, U)` at a zero. -/
theorem norm_Wsummand_sub_le {Φ U : ℝ → ℂ} (a b : ℂ) {EΦ EU : ℝ} (hEΦ : 0 ≤ EΦ) (hEU : 0 ≤ EU)
    (ρ : zetaZeroConfig.carrier)
    (hΦ₁ : (1 + |(ρ : ℂ).im|) * ‖paperFT Φ (gammaOf ρ)‖ ≤ EΦ)
    (hΦ₂ : (1 + |(ρ : ℂ).im|) * ‖paperFT Φ ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ EΦ)
    (hU₁ : (1 + |(ρ : ℂ).im|) * ‖paperFT U (gammaOf ρ)‖ ≤ EU)
    (hU₂ : (1 + |(ρ : ℂ).im|) * ‖paperFT U ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ EU)
    (h₁ : paperFT (fun x => a * Φ x + b * U x) (gammaOf ρ) =
      a * paperFT Φ (gammaOf ρ) + b * paperFT U (gammaOf ρ))
    (h₂ : paperFT (fun x => a * Φ x + b * U x) ((starRingEnd ℂ) (gammaOf ρ)) =
      a * paperFT Φ ((starRingEnd ℂ) (gammaOf ρ)) + b * paperFT U ((starRingEnd ℂ) (gammaOf ρ))) :
    ‖zetaZeroConfig.Wsummand (fun x => a * Φ x + b * U x) (fun x => a * Φ x + b * U x) ρ -
        b * (starRingEnd ℂ) b * zetaZeroConfig.Wsummand U U ρ‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) *
        ((‖a‖ ^ 2 * EΦ ^ 2 + 2 * (‖a‖ * ‖b‖) * (EΦ * EU)) / (1 + |(ρ : ℂ).im|) ^ 2) := by
  set D := 1 + |(ρ : ℂ).im| with hD
  have hD0 : 0 < D := by positivity
  set φ₁ := paperFT Φ (gammaOf ρ)
  set φ₂ := paperFT Φ ((starRingEnd ℂ) (gammaOf ρ))
  set u₁ := paperFT U (gammaOf ρ)
  set u₂ := paperFT U ((starRingEnd ℂ) (gammaOf ρ))
  have hid : zetaZeroConfig.Wsummand (fun x => a * Φ x + b * U x)
        (fun x => a * Φ x + b * U x) ρ - b * (starRingEnd ℂ) b * zetaZeroConfig.Wsummand U U ρ =
      (zetaZeroConfig.mult ρ : ℂ) * (a * φ₁ * (starRingEnd ℂ) (a * φ₂ + b * u₂) +
        b * u₁ * ((starRingEnd ℂ) a * (starRingEnd ℂ) φ₂)) := by
    simp only [ZeroConfig.Wsummand, h₁, h₂, map_add, map_mul]
    ring
  rw [hid, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [le_div_iff₀ (by positivity)]
  have hn : ‖a * φ₁ * (starRingEnd ℂ) (a * φ₂ + b * u₂) +
      b * u₁ * ((starRingEnd ℂ) a * (starRingEnd ℂ) φ₂)‖ ≤
      ‖a‖ * ‖φ₁‖ * (‖a‖ * ‖φ₂‖ + ‖b‖ * ‖u₂‖) + ‖b‖ * ‖u₁‖ * (‖a‖ * ‖φ₂‖) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by
        rw [norm_mul, norm_mul])) (by positivity)
    · rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have e₁ : D * ‖φ₁‖ ≤ EΦ := hΦ₁
  have e₂ : D * ‖φ₂‖ ≤ EΦ := hΦ₂
  have e₃ : D * ‖u₁‖ ≤ EU := hU₁
  have e₄ : D * ‖u₂‖ ≤ EU := hU₂
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have p₁ : (D * ‖φ₁‖) * (D * ‖φ₂‖) ≤ EΦ * EΦ :=
    mul_le_mul e₁ e₂ (by positivity) hEΦ
  have p₂ : (D * ‖φ₁‖) * (D * ‖u₂‖) ≤ EΦ * EU :=
    mul_le_mul e₁ e₄ (by positivity) hEΦ
  have p₃ : (D * ‖u₁‖) * (D * ‖φ₂‖) ≤ EU * EΦ :=
    mul_le_mul e₃ e₂ (by positivity) hEU
  calc ‖a * φ₁ * (starRingEnd ℂ) (a * φ₂ + b * u₂) +
        b * u₁ * ((starRingEnd ℂ) a * (starRingEnd ℂ) φ₂)‖ * D ^ 2
      ≤ (‖a‖ * ‖φ₁‖ * (‖a‖ * ‖φ₂‖ + ‖b‖ * ‖u₂‖) + ‖b‖ * ‖u₁‖ * (‖a‖ * ‖φ₂‖)) * D ^ 2 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
    _ = ‖a‖ ^ 2 * ((D * ‖φ₁‖) * (D * ‖φ₂‖)) + ‖a‖ * ‖b‖ * ((D * ‖φ₁‖) * (D * ‖u₂‖)) +
          ‖a‖ * ‖b‖ * ((D * ‖u₁‖) * (D * ‖φ₂‖)) := by ring
    _ ≤ ‖a‖ ^ 2 * (EΦ * EΦ) + ‖a‖ * ‖b‖ * (EΦ * EU) + ‖a‖ * ‖b‖ * (EU * EΦ) := by
        gcongr
    _ = ‖a‖ ^ 2 * EΦ ^ 2 + 2 * (‖a‖ * ‖b‖) * (EΦ * EU) := by ring

/-- A negative definite binary form: `−w y² + 2B x y − C x² < 0` for `(x, y) ≠ 0` when `B² < wC`. -/
theorem neg_quadratic_lt_zero {w B C x y : ℝ} (hw : 0 < w) (hB : B ^ 2 < w * C)
    (hxy : x ≠ 0 ∨ y ≠ 0) : -w * y ^ 2 + 2 * B * (x * y) - C * x ^ 2 < 0 := by
  have key : w * (-w * y ^ 2 + 2 * B * (x * y) - C * x ^ 2) =
      -(w * y - B * x) ^ 2 - (w * C - B ^ 2) * x ^ 2 := by ring
  have hpos : 0 < (w * y - B * x) ^ 2 + (w * C - B ^ 2) * x ^ 2 := by
    rcases hxy with hx | hy
    · have : 0 < (w * C - B ^ 2) * x ^ 2 := mul_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg (w * y - B * x)]
    · by_cases hx : x = 0
      · subst hx
        have : 0 < (w * y) ^ 2 := by positivity
        nlinarith
      · have : 0 < (w * C - B ^ 2) * x ^ 2 := mul_pos (by linarith) (by positivity)
        nlinarith [sq_nonneg (w * y - B * x)]
  have : w * (-w * y ^ 2 + 2 * B * (x * y) - C * x ^ 2) < 0 := by rw [key]; linarith
  by_contra hcon
  push Not at hcon
  have := mul_nonneg hw.le hcon
  linarith

/-- The arithmetic closing the plane estimate. -/
theorem markov_plane_tail {W2 x y p c w K δ EU EL : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hK0 : 0 ≤ K)
    (hEU : 0 ≤ EU) (hEL0 : 0 ≤ EL) (hEL : EL ≤ δ) (hKδ2 : K * δ ^ 2 ≤ c ^ 2) (hc : 0 < c)
    (hpc : c ≤ p) (hw0 : 0 < w) (hB : (K * δ * EU) ^ 2 < w * c ^ 2) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hWre : W2 ≤ -(y ^ 2 * w) + K * (x ^ 2 * EL ^ 2 + 2 * (x * y) * (EL * EU))) :
    W2 - 2 * (x ^ 2 * p ^ 2) < 0 := by
  have hq := neg_quadratic_lt_zero hw0 hB hxy
  have hEL2 : K * EL ^ 2 ≤ c ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEL0 hEL 2) hK0) hKδ2
  have hcross : K * (EL * EU) ≤ K * δ * EU := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEL hEU) hK0
  have hxy0 : 0 ≤ x * y := mul_nonneg hx hy
  have h1 : K * (x ^ 2 * EL ^ 2) ≤ x ^ 2 * c ^ 2 := by
    rw [show K * (x ^ 2 * EL ^ 2) = x ^ 2 * (K * EL ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left hEL2 (sq_nonneg x)
  have h2 : K * (2 * (x * y) * (EL * EU)) ≤ 2 * (K * δ * EU) * (x * y) := by
    rw [show K * (2 * (x * y) * (EL * EU)) = 2 * (x * y) * (K * (EL * EU)) by ring,
      show 2 * (K * δ * EU) * (x * y) = 2 * (x * y) * (K * δ * EU) by ring]
    exact mul_le_mul_of_nonneg_left hcross (by positivity)
  have h3 : x ^ 2 * c ^ 2 ≤ x ^ 2 * p ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hpc 2) (sq_nonneg x)
  rw [mul_add] at hWre
  linarith

/-- **Without RH, the archimedean-minus-prime form is negative definite on a plane**, spanned by
a truncated Riemann kernel and a pole-free even test of negative Weil energy. -/
theorem exists_negDef_markovPlane_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ f g : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ ContDiff ℝ 2 g ∧
      HasCompactSupport g ∧ ∀ a b : ℂ, (a, b) ≠ 0 →
        markovEnergy (fun x => a * f x + b * g x) < 0 := by
  obtain ⟨u, hu, hcpt, heven, hp, hneg⟩ :=
    exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  set U : ℝ → ℂ := fun x => (u x : ℂ) with hU
  have hUd : ContDiff ℝ 2 U := Complex.ofRealCLM.contDiff.comp hu
  have hUc : HasCompactSupport U := hcpt.comp_left Complex.ofReal_zero
  have hp' : paperFT U (-I / 2) = 0 := by
    rw [neg_div, hU, paperFT_ofReal_neg_of_even heven]; exact hp
  set w := -(zetaZeroConfig.W U U).re with hw
  have hw0 : 0 < w := by linarith
  set EU := testEnergy u
  have hEU := testEnergy_nonneg u
  set K := 5 / 4 * zeroSumZ with hK
  have hK0 : 0 ≤ K := by have := zeroSumZ_nonneg; positivity
  obtain ⟨c, hc, hcL⟩ := exists_integral_truncatedRiemannKernelReal_exp_ge
  -- the tail-energy threshold
  set t := min 1 w / 2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by have := min_le_left 1 w; linarith
  have htw : t ≤ w / 2 := by have := min_le_right 1 w; linarith
  set δ := c * t / ((K + 1) * (EU + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hKδ : K * δ ≤ c * t := by
    rw [hδ, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    have : K * (c * t) ≤ c * t * ((K + 1) * (EU + 1)) := by
      have h1 : K ≤ (K + 1) * (EU + 1) := by nlinarith
      nlinarith [mul_pos hc ht0]
    linarith
  have hδc : δ ≤ c := by
    rw [hδ, div_le_iff₀ (by positivity)]
    have h1 : t ≤ (K + 1) * (EU + 1) := by nlinarith
    nlinarith
  have hKδ2 : K * δ ^ 2 ≤ c ^ 2 := by
    have : K * δ ^ 2 = (K * δ) * δ := by ring
    rw [this]
    calc (K * δ) * δ ≤ (c * t) * c := mul_le_mul hKδ hδc hδ0.le (by positivity)
      _ ≤ c ^ 2 := by nlinarith
  have hKδEU : K * δ * EU ≤ c * t := by
    rw [hδ]
    rw [show K * (c * t / ((K + 1) * (EU + 1))) * EU =
      c * t * (K * EU / ((K + 1) * (EU + 1))) by ring]
    have : K * EU / ((K + 1) * (EU + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    calc c * t * (K * EU / ((K + 1) * (EU + 1))) ≤ c * t * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c * t := by ring
  have hB : (K * δ * EU) ^ 2 < w * c ^ 2 := by
    have h0 : 0 ≤ K * δ * EU := by positivity
    calc (K * δ * EU) ^ 2 ≤ (c * t) ^ 2 := pow_le_pow_left₀ h0 hKδEU 2
      _ = c ^ 2 * (t * t) := by ring
      _ ≤ c ^ 2 * ((1 / 2) * (w / 2)) := by gcongr
      _ < w * c ^ 2 := by nlinarith [sq_pos_of_pos hc]
  obtain ⟨L₀, hL₀⟩ := WeilSpectral.exists_truncatedRiemannTailEnergy_le hδ0
  set L := max L₀ 2 with hL
  have hEL : truncatedRiemannTailEnergy L ≤ δ := hL₀ L (le_max_left _ _)
  have hEL0 := truncatedRiemannTailEnergy_nonneg L
  obtain ⟨Λd, -, hΛd⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set Φ := truncatedRiemannKernel L with hΦ
  have hΦd : ContDiff ℝ 2 Φ := contDiff_nearRadicalTest L _
  have hΦc : HasCompactSupport Φ := hasCompactSupport_truncatedRiemannKernel L
  -- the pole value of `Φ`
  set p := ∫ x, truncatedRiemannKernelReal L x * Real.exp (-(x / 2)) with hp_def
  have hpc : c ≤ p := hcL L (le_max_right _ _)
  have hΦp : paperFT Φ (I / 2) = (p : ℂ) := by
    rw [hΦ, truncatedRiemannKernel_eq_ofReal, paperFT_ofReal_I_half_eq_integral]
  have hΦp' : paperFT Φ (-I / 2) = (p : ℂ) := by
    rw [neg_div, hΦ, truncatedRiemannKernel_eq_ofReal,
      paperFT_ofReal_neg_of_even (truncatedRiemannKernelReal_neg L),
      paperFT_ofReal_I_half_eq_integral]
  refine ⟨Φ, U, hΦd, hΦc, hUd, hUc, fun a b hab => ?_⟩
  set h : ℝ → ℂ := fun x => a * Φ x + b * U x with hh
  have hhd : ContDiff ℝ 2 h := (contDiff_const.mul hΦd).add (contDiff_const.mul hUd)
  have hhc : HasCompactSupport h := (hΦc.mul_left).add hUc.mul_left
  have hlin : ∀ z : ℂ, paperFT h z = a * paperFT Φ z + b * paperFT U z := fun z =>
    paperFT_smul_add_smul a b z (integrable_mul_cexp_of_compact hΦd.continuous hΦc z)
      (integrable_mul_cexp_of_compact hUd.continuous hUc z)
  -- the pole term
  have hpole : (weilPoleTerm (EF.weilTest h h)).re = 2 * (‖a‖ ^ 2 * p ^ 2) := by
    rw [weilPoleTerm_weilTest_eq hhd.continuous hhc, hlin, hlin, hΦp, hΦp', hp, hp']
    simp only [mul_zero, add_zero, map_mul, Complex.conj_ofReal]
    have : a * (p : ℂ) * ((starRingEnd ℂ) a * (p : ℂ)) + a * (p : ℂ) * ((starRingEnd ℂ) a * (p : ℂ)) =
        ((2 * (‖a‖ ^ 2 * p ^ 2) : ℝ) : ℂ) := by
      rw [show a * (p : ℂ) * ((starRingEnd ℂ) a * (p : ℂ)) + a * (p : ℂ) * ((starRingEnd ℂ) a * (p : ℂ))
        = 2 * (a * (starRingEnd ℂ) a) * (p : ℂ) ^ 2 by ring, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [this, Complex.ofReal_re]
  -- the zero side
  have hU₁ := fun ρ => (test_zero_bound hu hcpt ρ).1
  have hU₂ := fun ρ => (test_zero_bound hu hcpt ρ).2
  have hΦ₁ := fun ρ => (truncatedRiemannKernel_zero_bound L hΛd ρ).1
  have hΦ₂ := fun ρ => (truncatedRiemannKernel_zero_bound L hΛd ρ).2
  set EL := truncatedRiemannTailEnergy L
  set Cr := ‖a‖ ^ 2 * EL ^ 2 + 2 * (‖a‖ * ‖b‖) * (EL * EU) with hCr
  have hCr0 : 0 ≤ Cr := by positivity
  obtain ⟨hRs, hRn⟩ := summable_and_norm_tsum_le_of_zeroBound hCr0 (fun ρ =>
    norm_Wsummand_sub_le a b hEL0 hEU ρ (hΦ₁ ρ) (hΦ₂ ρ) (hU₁ ρ) (hU₂ ρ) (hlin _) (hlin _))
  obtain ⟨hUs, -⟩ := summable_and_norm_tsum_le_of_zeroBound (sq_nonneg EU) (x := fun ρ =>
    zetaZeroConfig.Wsummand U U ρ) (fun ρ => by
      have h1 := hU₁ ρ
      have h2 := hU₂ ρ
      set D := 1 + |(ρ : ℂ).im|
      have hD0 : 0 < D := by positivity
      simp only [ZeroConfig.Wsummand]
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [le_div_iff₀ (by positivity)]
      calc ‖paperFT U (gammaOf ↑ρ)‖ * ‖paperFT U ((starRingEnd ℂ) (gammaOf ↑ρ))‖ * D ^ 2
          = (D * ‖paperFT U (gammaOf ↑ρ)‖) * (D * ‖paperFT U ((starRingEnd ℂ) (gammaOf ↑ρ))‖) := by
            ring
        _ ≤ EU * EU := mul_le_mul h1 h2 (by positivity) hEU
        _ = EU ^ 2 := by ring)
  have hWsplit : zetaZeroConfig.W h h = b * (starRingEnd ℂ) b * zetaZeroConfig.W U U +
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.Wsummand h h ρ -
        b * (starRingEnd ℂ) b * zetaZeroConfig.Wsummand U U ρ) := by
    unfold ZeroConfig.W
    rw [← tsum_mul_left, ← (hUs.mul_left _).tsum_add hRs]
    congr 1
    funext ρ
    ring
  have hbb : (b * (starRingEnd ℂ) b * zetaZeroConfig.W U U).re = -(‖b‖ ^ 2 * w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul, hw]
    ring
  have hRn' : ‖∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.Wsummand h h ρ -
      b * (starRingEnd ℂ) b * zetaZeroConfig.Wsummand U U ρ)‖ ≤ K * Cr := hRn
  have hWre : (zetaZeroConfig.W h h).re ≤ -(‖b‖ ^ 2 * w) + K * Cr := by
    rw [hWsplit, Complex.add_re, hbb]
    have := (Complex.re_le_norm _).trans hRn'
    linarith
  rw [markovEnergy_eq_W_sub hhd hhc, hpole]
  -- reduce to the binary form in `x = ‖a‖`, `y = ‖b‖`
  have hx := norm_nonneg a
  have hy := norm_nonneg b
  have hxy : ‖a‖ ≠ 0 ∨ ‖b‖ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hab (by rw [norm_eq_zero.mp hcon.1, norm_eq_zero.mp hcon.2]; rfl)
  exact markov_plane_tail hx hy hK0 hEU hEL0 hEL hKδ2 hc hpc hw0 hB hxy hWre

/-- The arithmetic closing the single-direction estimate. -/
theorem markov_neg_tail {W2 p c K δ EL : ℝ} (hK0 : 0 ≤ K) (hEL0 : 0 ≤ EL) (hEL : EL ≤ δ)
    (hδ0 : 0 < δ) (hδc : δ ≤ c) (hKδ : K * δ < c) (hc : 0 < c) (hpc : c ≤ p)
    (hre : W2 ≤ K * EL ^ 2) : W2 - 2 * p ^ 2 < 0 := by
  have h1 : K * EL ^ 2 ≤ K * δ * δ := by
    rw [mul_assoc, ← sq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEL0 hEL 2) hK0
  have h2 : K * δ * δ < c * c := by
    calc K * δ * δ < c * δ := mul_lt_mul_of_pos_right hKδ hδ0
      _ ≤ c * c := mul_le_mul_of_nonneg_left hδc hc.le
  have h3 : c * c ≤ p * p := mul_le_mul hpc hpc hc.le (hc.le.trans hpc)
  nlinarith

/-- **Unconditionally `M` has a negative direction**: the truncated Riemann kernel. -/
theorem exists_markovEnergy_neg :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ markovEnergy f < 0 := by
  obtain ⟨c, hc, hcL⟩ := exists_integral_truncatedRiemannKernelReal_exp_ge
  set K := 5 / 4 * zeroSumZ with hK
  have hK0 : 0 ≤ K := by have := zeroSumZ_nonneg; positivity
  set δ := c / (K + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδc : δ ≤ c := by rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  have hKδ : K * δ < c := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨L₀, hL₀⟩ := WeilSpectral.exists_truncatedRiemannTailEnergy_le hδ0
  set L := max L₀ 2 with hL
  have hEL : truncatedRiemannTailEnergy L ≤ δ := hL₀ L (le_max_left _ _)
  have hEL0 := truncatedRiemannTailEnergy_nonneg L
  obtain ⟨Λd, -, hΛd⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set Φ := truncatedRiemannKernel L with hΦ
  have hΦd : ContDiff ℝ 2 Φ := contDiff_nearRadicalTest L _
  have hΦc : HasCompactSupport Φ := hasCompactSupport_truncatedRiemannKernel L
  set p := ∫ x, truncatedRiemannKernelReal L x * Real.exp (-(x / 2)) with hp_def
  have hpc : c ≤ p := hcL L (le_max_right _ _)
  have hΦp : paperFT Φ (I / 2) = (p : ℂ) := by
    rw [hΦ, truncatedRiemannKernel_eq_ofReal, paperFT_ofReal_I_half_eq_integral]
  have hΦp' : paperFT Φ (-I / 2) = (p : ℂ) := by
    rw [neg_div, hΦ, truncatedRiemannKernel_eq_ofReal,
      paperFT_ofReal_neg_of_even (truncatedRiemannKernelReal_neg L),
      paperFT_ofReal_I_half_eq_integral]
  refine ⟨Φ, hΦd, hΦc, ?_⟩
  have hpole : (weilPoleTerm (EF.weilTest Φ Φ)).re = 2 * p ^ 2 := by
    rw [weilPoleTerm_weilTest_eq hΦd.continuous hΦc, hΦp, hΦp', Complex.conj_ofReal]
    rw [show (p : ℂ) * (p : ℂ) + (p : ℂ) * (p : ℂ) = ((2 * p ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hW : ‖zetaZeroConfig.W Φ Φ‖ ≤ K * truncatedRiemannTailEnergy L ^ 2 := by
    refine (norm_W_le_of_pointwise (sq_nonneg _) fun ρ => ?_).trans (le_of_eq (by rw [hK]))
    have h1 := (truncatedRiemannKernel_zero_bound L hΛd ρ).1
    have h2 := (truncatedRiemannKernel_zero_bound L hΛd ρ).2
    set D := 1 + |(ρ : ℂ).im|
    have hD0 : 0 < D := by positivity
    rw [le_div_iff₀ (by positivity)]
    calc ‖paperFT Φ (gammaOf ↑ρ)‖ * ‖paperFT Φ ((starRingEnd ℂ) (gammaOf ↑ρ))‖ * D ^ 2
        = (D * ‖paperFT Φ (gammaOf ↑ρ)‖) * (D * ‖paperFT Φ ((starRingEnd ℂ) (gammaOf ↑ρ))‖) := by
          ring
      _ ≤ truncatedRiemannTailEnergy L * truncatedRiemannTailEnergy L :=
          mul_le_mul h1 h2 (by positivity) hEL0
      _ = truncatedRiemannTailEnergy L ^ 2 := by ring
  rw [markovEnergy_eq_W_sub hΦd hΦc, hpole]
  have hre := (Complex.re_le_norm (zetaZeroConfig.W Φ Φ)).trans hW
  exact markov_neg_tail hK0 hEL0 hEL hδ0 hδc hKδ hc hpc hre

/-- **RH is the one-bound-state law.** RH holds if and only if no plane of `C²` compactly
supported tests carries a negative definite archimedean-minus-prime form. Together with
`exists_markovEnergy_neg`, RH says this form has exactly one negative square. -/
theorem riemannHypothesis_iff_not_exists_negDef_markovPlane :
    RiemannHypothesis ↔ ¬ ∃ f g : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ a b : ℂ, (a, b) ≠ 0 →
        markovEnergy (fun x => a * f x + b * g x) < 0 := by
  constructor
  · rintro hRH ⟨f, g, hf, hfc, hg, hgc, hneg⟩
    obtain ⟨a, b, hab, hnn⟩ := exists_markovEnergy_nonneg_of_riemannHypothesis hRH hf hfc hg hgc
    exact absurd (hneg a b hab) (not_lt.mpr hnn)
  · intro h
    by_contra hRH
    exact h (exists_negDef_markovPlane_of_not_riemannHypothesis hRH)

end

end RHTower
