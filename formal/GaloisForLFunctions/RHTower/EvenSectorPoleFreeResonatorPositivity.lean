import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.EvenSectorSechRepresentation
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.RHTower.EvenTestLaplacePositivity
import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty

/-!
# Pole-free even positivity transfers to nonnegative resonators

Let `lam` be Weil-positive at some pole weight `β` on the autocorrelations of even compactly
supported `C²` tests.  On even tests whose transform vanishes at `±i/2` the pole weight drops out.

**Theorem** (`re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenAt`).  For every even
real `C²` profile `g` of compact support with `ĝ(i/2) = 0`, all points `x_k` and all coefficients
`c_k ≥ 0`, the resonator `R = Σ_k c_k g(· − x_k)` satisfies `Re W(R ⋆ R̃) ≥ 0` (pole weight `1`,
equivalently any pole weight, since `R̂(±i/2) = 0`).  The resonator is in general not even.

Proof.
* *Growth* (`exists_abs_le_of_weilPositiveEvenAt_any`): `|lam(n)| ≤ C √n (1 + log n)` at every
  `β`, since the pole term of an even node test is at most the bound of its archimedean part.
* *Strip positivity* (`evenWeilDensity_specSq_add_pole_nonneg`): for even strip functions `Φ`,
  `L(Φ Φ^#) + 2(β − 1)|Φ(i/2)|² ≥ 0`, by truncation; the pole integrals of the truncations
  converge.  So `L(Φ Φ^#) ≥ 0` when `Φ(i/2) = 0`.
* *Cosine-shift measures* (`exists_cosineShift_measure_of_poleFree`): the cosine and sine
  combinations of a pole-free `Φ` are pole-free, so `φ_Φ` is positive definite and is the
  characteristic function of a finite positive measure `ν_Φ`.
* *Transfer.*  With `D(z) = Σ c_k e^{izx_k}` and `D̃(z) = Σ c_k e^{−izx_k}` the multiplier
  `T = D D̃ e^{−εz²}` is even, and `D D̃` is `|D|² ≥ 0` on `ℝ` and a product of two positive
  exponential sums on `iℝ`.  Hence the lift `T̃(ρ) = T((ρ² − 2)^{1/2})` is nonnegative on the whole
  real `ρ`-line, and `L(Φ Φ^# T) = ∫ T̃ dν_Φ ≥ 0` for `Φ = ĝ e^{−εz²/2}`.  This is `L` of the
  Gaussian smoothing of `R̂`; letting `ε → 0` gives `Re W(R ⋆ R̃) ≥ 0`.

The segment `ρ² < 2` carries the imaginary frequencies, where a non-even test is in general
negative: `R̂(iy) R̂(−iy)` has no sign.  Nonnegative translation coefficients restore it,
`R̂(iy) R̂(−iy) = ĝ(iy)² D(iy) D̃(iy) ≥ 0`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral SeparatedBump

/-! ## Growth at every pole weight -/

/-- The pole term of an even test is at most `2B²` when `‖f̂(σ i)‖ ≤ B` for `|σ| ≤ 1/2`. -/
theorem re_weilPoleTerm_even_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ x, f (-x) = f x) {B : ℝ}
    (hB : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖paperFT f ((σ : ℂ) * I)‖ ≤ B) :
    (weilPoleTerm (EF.weilTest f f)).re ≤ 2 * B ^ 2 := by
  rw [weilPoleTerm_even hf hfc heven, Complex.ofReal_re]
  have h := hB (1 / 2) (by norm_num [abs_of_pos])
  rw [show ((1 / 2 : ℝ) : ℂ) * I = I / 2 by push_cast; ring] at h
  have h0 := norm_nonneg (paperFT f (I / 2))
  nlinarith

/-- The pole term of an even node test is at most the bound of its archimedean part. -/
theorem re_weilPoleTerm_node_le (n : ℕ) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (heven : ∀ x, f (-x) = f x)
    (hb : ∀ r : ℝ, ‖paperFT f r‖ ≤ 4 * ‖paperFT (fun u => (nodeBump n u : ℂ)) r‖)
    (hi : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖paperFT f ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log n / 4 + 1 / 4) * ((nodeScale n)⁻¹ * bumpPoleConst)) :
    (weilPoleTerm (EF.weilTest f f)).re ≤
      32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
        8 / (Real.pi * nodeScale n) *
          ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) := by
  have hm0 := nodeScale_pos n
  have h1 := re_weilPoleTerm_even_le hf hfc heven hi
  have e1 : 2 * (4 * Real.exp (Real.log n / 4 + 1 / 4) * ((nodeScale n)⁻¹ * bumpPoleConst)) ^ 2 =
      32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
    field_simp
    ring_nf
  have hX : 0 ≤ (gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst := by
    have h2 := integral_normSq_mul_abs_gammaBracket_le n hb
    have h3 : 0 ≤ ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| :=
      integral_nonneg fun r => by positivity
    by_contra hneg
    push Not at hneg
    have : 16 / nodeScale n *
        ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have hY : 0 ≤ 8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) :=
    mul_nonneg (by positivity) hX
  linarith

theorem le_div_of_node_le {A c x B : ℝ} (hc : 0 < c) (hW : 0 ≤ A - c * x) (hA : A ≤ B) :
    x ≤ B / c := by
  rw [le_div_iff₀ hc]
  linarith

theorem pole_arch_le_of_node {A P Bd β : ℝ} (hβ : 1 ≤ β) (hA : |A| ≤ Bd) (hP : P ≤ Bd) :
    A + (β - 1) * P ≤ β * Bd := by
  have h1 := le_abs_self A
  have h2 := mul_le_mul_of_nonneg_left hP (by linarith : (0 : ℝ) ≤ β - 1)
  nlinarith

/-- **Even-positive weights grow at most like `√n log n`, at every pole weight.** -/
theorem exists_abs_le_of_weilPositiveEvenAt_any {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → |lam n| ≤ C * Real.sqrt n * (1 + Real.log n) := by
  set β₁ := max β 1 with hβ₁def
  have hβ₁ : 1 ≤ β₁ := le_max_right _ _
  have h₁ : WeilPositiveEvenAt β₁ lam := weilPositiveEvenAt_mono (le_max_left _ _) h
  have hJ : 0 < ∫ u, narrowBump 0 u ^ 2 := integral_narrowBump_sq_pos 0
  set X := 16 * Real.exp (1 / 2) * bumpPoleConst ^ 2 / (∫ u, narrowBump 0 u ^ 2) +
    4 * ((|gammaLogConst| + 3) * bumpMassConst + bumpLogConst) /
      (Real.pi * ∫ u, narrowBump 0 u ^ 2) with hX
  have hX0 : 0 ≤ X := add_nonneg (by positivity)
    (div_nonneg (by have := bumpMassConst_nonneg; have := bumpLogConst_nonneg; positivity)
      (by positivity))
  refine ⟨β₁ * X, mul_nonneg (by linarith) hX0, fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hm0 := nodeScale_pos n
  have hmeq : nodeScale n = 2 * (n : ℝ) + 3 := rfl
  set Bd := 32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
    8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) with hBd
  have hWp := h₁ (evenPlus n).1.1 (evenPlus n).1.2.1 (evenPlus n).1.2.2 (evenPlus n).2
  rw [re_weilPoleWeightFunctional_eq β₁ lam (evenPlus n).1,
    logVector_evenPlus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWp
  have hWm := h₁ (evenMinus n).1.1 (evenMinus n).1.2.1 (evenMinus n).1.2.2 (evenMinus n).2
  rw [re_weilPoleWeightFunctional_eq β₁ lam (evenMinus n).1,
    logVector_evenMinus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWm
  simp only [poleWeightArchRe, smul_eq_mul] at hWp hWm
  have hAp : |weilArchRe (EF.weilTest (evenPlus n).1.1 (evenPlus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (evenPlus n).1.2.1.continuous (evenPlus n).1.2.2
      (norm_paperFT_evenPlus_le n) fun σ hσ => norm_paperFT_evenPlus_imag_le n hσ
  have hAm : |weilArchRe (EF.weilTest (evenMinus n).1.1 (evenMinus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (evenMinus n).1.2.1.continuous (evenMinus n).1.2.2
      (norm_paperFT_evenMinus_le n) fun σ hσ => norm_paperFT_evenMinus_imag_le n hσ
  have hPp : (weilPoleTerm (EF.weilTest (evenPlus n).1.1 (evenPlus n).1.1)).re ≤ Bd :=
    re_weilPoleTerm_node_le n (evenPlus n).1.2.1.continuous (evenPlus n).1.2.2 (evenPlus n).2
      (norm_paperFT_evenPlus_le n) fun σ hσ => norm_paperFT_evenPlus_imag_le n hσ
  have hPm : (weilPoleTerm (EF.weilTest (evenMinus n).1.1 (evenMinus n).1.1)).re ≤ Bd :=
    re_weilPoleTerm_node_le n (evenMinus n).1.2.1.continuous (evenMinus n).1.2.2 (evenMinus n).2
      (norm_paperFT_evenMinus_le n) fun σ hσ => norm_paperFT_evenMinus_imag_le n hσ
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans hAp
  have hβBd : 0 ≤ β₁ * Bd := mul_nonneg (by linarith) hBd0
  have hAp' := pole_arch_le_of_node hβ₁ hAp hPp
  have hAm' := pole_arch_le_of_node hβ₁ hAm hPm
  set c₀ := 2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  -- the upper bound
  have hcp : c₀ ≤ 2 * (∫ u, evenProfile n u ^ 2) / Real.sqrt n := by
    rw [integral_evenProfile_sq_eq]
    refine div_le_div_of_nonneg_right ?_ hsq.le
    have : 0 ≤ (nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2 := by positivity
    linarith
  have hup : lam n ≤ β₁ * Bd / c₀ :=
    (le_div_of_node_le (lt_of_lt_of_le hc₀0 hcp) hWp hAp').trans
      (div_le_div_of_nonneg_left hβBd hc₀0 hcp)
  -- the lower bound
  have hcm : c₀ ≤ 2 * (∫ u, oddProfile n u ^ 2) / Real.sqrt n :=
    div_le_div_of_nonneg_right (by linarith [le_integral_oddProfile_sq n]) hsq.le
  have hWm' : 0 ≤ weilArchRe (EF.weilTest (evenMinus n).1.1 (evenMinus n).1.1) +
      (β₁ - 1) * (weilPoleTerm (EF.weilTest (evenMinus n).1.1 (evenMinus n).1.1)).re -
      2 * (∫ u, oddProfile n u ^ 2) / Real.sqrt n * (-lam n) := by linarith
  have hlo : -lam n ≤ β₁ * Bd / c₀ :=
    (le_div_of_node_le (lt_of_lt_of_le hc₀0 hcm) hWm' hAm').trans
      (div_le_div_of_nonneg_left hβBd hc₀0 hcm)
  have hfin : Bd / c₀ = Bd * (Real.sqrt n * nodeScale n / (2 * ∫ u, narrowBump 0 u ^ 2)) := by
    rw [hc₀]
    field_simp
  have hkey := node_bound_le (n := n) (J₀ := ∫ u, narrowBump 0 u ^ 2) (P := bumpPoleConst)
    (K := gammaLogConst) (I₀ := bumpMassConst) (I₁ := bumpLogConst) hn1 hJ bumpMassConst_nonneg
    bumpLogConst_nonneg
  rw [← hmeq, ← hBd, ← hfin, ← hX] at hkey
  have hfinal : β₁ * Bd / c₀ ≤ β₁ * X * Real.sqrt n * (1 + Real.log n) := by
    calc β₁ * Bd / c₀ = β₁ * (Bd / c₀) := by ring
      _ ≤ β₁ * (X * Real.sqrt n * (1 + Real.log n)) :=
          mul_le_mul_of_nonneg_left hkey (by linarith)
      _ = β₁ * X * Real.sqrt n * (1 + Real.log n) := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ## Strip positivity at pole weight `β` -/

theorem archPoleEnergy_truncTest_sub_add_pole_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (heven : ∀ x, F (-x) = F x) (L : ℝ) :
    0 ≤ archPoleEnergy (truncTest F L) -
        atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) +
      (β - 1) * (2 * (∫ u, truncTest F L u * Real.exp (-u / 2)) ^ 2) := by
  have hc : ContDiff ℝ 2 fun u => (truncTest F L u : ℂ) := contDiff_ofReal_truncTest hF L
  have hcs : HasCompactSupport fun u => (truncTest F L u : ℂ) :=
    (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  have hev : ∀ x, (fun u => (truncTest F L u : ℂ)) (-x) = (fun u => (truncTest F L u : ℂ)) x :=
    fun x => by simp only [truncTest_neg heven]
  have hpos := h _ hc hcs hev
  have hpole := weilPoleTerm_even hc.continuous hcs hev
  rw [paperFT_ofRealFun_I_div_two, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpole
  unfold WeilPoleWeight.weilPoleWeightFunctional at hpos
  rw [Complex.add_re, re_weilFullFunctional_ofReal, weilArchRe_weilTest_truncTest_eq hF L] at hpos
  have e : (((β : ℂ) - 1) *
      (paperFT (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))
          (I / 2) +
        paperFT (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))
          (-I / 2))).re =
      (β - 1) * (2 * (∫ u, truncTest F L u * Real.exp (-u / 2)) ^ 2) := by
    rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    congr 1
    have := congrArg Complex.re hpole
    rw [Complex.ofReal_re] at this
    exact this
  linarith

/-- **Strip positivity at pole weight `β`.**  `L(Φ Φ^#) + 2(β − 1)|Φ(i/2)|² ≥ 0`. -/
theorem evenWeilDensity_specSq_add_pole_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    {b ε C : ℝ} (hb : 1 < b) (hε : 0 < ε) (hΦ : StripDecay Φ b ε C)
    (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (heven : ∀ z, Φ (-z) = Φ z) :
    0 ≤ evenWeilDensity lam (specSq Φ) + (β - 1) * (2 * ‖Φ (I / 2)‖ ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hδ : 0 < b - 1 / 2 := by linarith
  rw [evenWeilDensity_specSq (by linarith) hε hΦ hsym]
  have hD := decayBound_stripTest (by linarith : 1 / 2 < b) hε hΦ
  have hE : ExpDecayTest (stripTest Φ) := hD.expDecayTest hδ
  have hFeven : ∀ x, stripTest Φ (-x) = stripTest Φ x := stripTest_neg heven
  have hdec : ∀ x, |stripTest Φ x| ≤ C * stripDecayConst b ε * Real.exp (-(b * |x|)) := by
    intro x
    have h1 := (hD.2.2 x).1
    rwa [show 1 / 2 + (b - 1 / 2) = b by ring] at h1
  have hpole : Tendsto (fun L => ∫ u, truncTest (stripTest Φ) L u * Real.exp (-u / 2)) atTop
      (𝓝 (∫ u, stripTest Φ u * Real.exp (-u / 2))) := by
    have h1 := WeilPoleWeight.tendsto_integral_truncTest_mul_exp hδ hD (c := -(1 / 2))
      (by norm_num [abs_of_pos])
    have e : ∀ u : ℝ, -(1 / 2) * u = -u / 2 := fun u => by ring
    simp_rw [e] at h1
    exact h1
  have hval : ((∫ u, stripTest Φ u * Real.exp (-u / 2) : ℝ) : ℂ) = Φ (I / 2) := by
    rw [← paperFT_ofRealFun_I_div_two]
    exact paperFT_stripTest hb0 hε hΦ hsym (by simp; linarith)
  have hnorm : ‖Φ (I / 2)‖ ^ 2 = (∫ u, stripTest Φ u * Real.exp (-u / 2)) ^ 2 := by
    rw [← hval, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hlim := ((tendsto_archPoleEnergy_truncTest hE).sub
    (tendsto_atomPairing_truncTest_of_growth hg hE hb hD.2.1 hdec)).add
    (((hpole.pow 2).const_mul 2).const_mul (β - 1))
  exact ge_of_tendsto' hlim fun L =>
    archPoleEnergy_truncTest_sub_add_pole_nonneg h hD.1 hFeven L

/-- **Pole-free strip positivity.**  At every pole weight, `L(Φ Φ^#) ≥ 0` for every even strip
function with `Φ(i/2) = 0`. -/
theorem evenWeilDensity_specSq_nonneg_of_poleFree {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hΦ0 : Φ (I / 2) = 0) : 0 ≤ evenWeilDensity lam (specSq Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  have h1 := evenWeilDensity_specSq_add_pole_nonneg h hg (by norm_num : (1 : ℝ) < 5 / 4) hε hs
    hΦ.sym hΦ.even
  simpa [hΦ0] using h1

/-! ## Cosine-shift measures of pole-free strip functions -/

theorem cosComb_I_div_two {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} (hΦ0 : Φ (I / 2) = 0) :
    cosComb t c Φ (I / 2) = 0 := by
  unfold cosComb; simp [hΦ0]

theorem sinComb_I_div_two {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} (hΦ0 : Φ (I / 2) = 0) :
    sinComb t c Φ (I / 2) = 0 := by
  unfold sinComb; simp [hΦ0]

/-- **Positive definiteness from pole-free positivity.** -/
theorem sum_sum_cosineShiftFn_nonneg_of_poleFree {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 → 0 ≤ evenWeilDensity lam (specSq A))
    {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) (hΦ0 : Φ (I / 2) = 0) {N : ℕ} (t c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) := by
  have hgood : ∀ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
      GoodDensity (rhoCosShift (t p.2 - t p.1) Φ) := fun p _ => goodDensity_cosShift _ hΦ
  have hlin := evenWeilDensity_sum hg ((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ)
    (fun p => c p.1 * c p.2) hgood
  have hsum : ∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) =
      ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
        c p.1 * c p.2 * evenWeilDensity lam (rhoCosShift (t p.2 - t p.1) Φ) := by
    rw [Finset.sum_product]; rfl
  have hA := evenStrip_cosComb t c hΦ
  have hB := evenStrip_sinComb t c hΦ
  have hcongr : evenWeilDensity lam (fun z => ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ
      Finset.univ, ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) Φ z) =
      evenWeilDensity lam (fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) := by
    have hI1 : |(I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    have hI2 : |(-I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    refine evenWeilDensity_congr ?_ ?_ fun r => ?_
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ hI1).symm
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ hI2).symm
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ
        (abs_im_lt_sqrt_two (by simp; norm_num))).symm
  rw [hsum, ← hlin, hcongr,
    evenWeilDensity_add hg (goodDensity_specSq hA) (goodDensity_specSq hB)]
  exact add_nonneg (hpos _ hA (cosComb_I_div_two t c hΦ0))
    (hpos _ hB (sinComb_I_div_two t c hΦ0))

/-- **The cosine-shift measure of a pole-free strip function.** -/
theorem exists_cosineShift_measure_of_poleFree {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 → 0 ≤ evenWeilDensity lam (specSq A))
    {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) (hΦ0 : Φ (I / 2) = 0) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y, charFun ν y = (cosineShiftFn lam Φ y : ℂ) :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefiniteOnReal_of_real (cosineShiftFn_neg lam Φ)
      fun _ t c => sum_sum_cosineShiftFn_nonneg_of_poleFree hg hpos hΦ hΦ0 t c)
    (Complex.continuous_ofReal.comp (continuous_cosineShiftFn hg hΦ))

/-- **Multipliers with a nonnegative lift are nonnegative on pole-free spectral squares.** -/
theorem evenWeilDensity_specSq_mul_multiplier_nonneg_of_poleFree {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 → 0 ≤ evenWeilDensity lam (specSq A))
    {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) (hΦ0 : Φ (I / 2) = 0) {T : ℂ → ℂ} (hT : Multiplier T)
    (hTpos : ∀ ρ : ℝ, 0 ≤ (rhoLift T ρ).re) :
    0 ≤ evenWeilDensity lam (fun z => specSq Φ z * T z) := by
  obtain ⟨ν, hfin, hν⟩ := exists_cosineShift_measure_of_poleFree hg hpos hΦ hΦ0
  rw [evenWeilDensity_specSq_mul_multiplier hg hΦ hν hT]
  exact integral_nonneg hTpos

/-! ## The translation multiplier -/

/-- The exponential sum `D(z) = Σ_k c_k e^{i z x_k}`. -/
def translateExpSum {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ s, (c k : ℂ) * cexp (I * z * x k)

/-- `D(z) D̃(z)` with `D̃(z) = Σ_k c_k e^{−i z x_k}`. -/
def translatePairExp {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (z : ℂ) : ℂ :=
  translateExpSum s c x z * translateExpSum s c (fun k => -x k) z

theorem translateExpSum_neg {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (z : ℂ) :
    translateExpSum s c x (-z) = translateExpSum s c (fun k => -x k) z := by
  unfold translateExpSum
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2; push_cast; ring

theorem translateExpSum_conj {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (z : ℂ) :
    conj (translateExpSum s c x z) = translateExpSum s c (fun k => -x k) (conj z) := by
  unfold translateExpSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

theorem translatePairExp_neg {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (z : ℂ) :
    translatePairExp s c x (-z) = translatePairExp s c x z := by
  unfold translatePairExp
  rw [translateExpSum_neg, translateExpSum_neg]
  simp only [neg_neg]
  ring

theorem translatePairExp_conj {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (z : ℂ) :
    translatePairExp s c x (conj z) = conj (translatePairExp s c x z) := by
  unfold translatePairExp
  rw [map_mul, translateExpSum_conj, translateExpSum_conj]
  simp only [neg_neg]
  ring

theorem differentiable_translatePairExp {ι : Type*} (s : Finset ι) (c x : ι → ℝ) :
    Differentiable ℂ (translatePairExp s c x) := by
  have hD : ∀ y : ι → ℝ, Differentiable ℂ (translateExpSum s c y) := fun y => by
    unfold translateExpSum
    exact Differentiable.fun_sum fun k _ => by fun_prop
  exact (hD x).mul (hD fun k => -x k)

theorem norm_translateExpSum_le {ι : Type*} (s : Finset ι) (c x : ι → ℝ) {b : ℝ} {z : ℂ}
    (hz : |z.im| ≤ b) :
    ‖translateExpSum s c x z‖ ≤ ∑ k ∈ s, |c k| * Real.exp (b * |x k|) := by
  unfold translateExpSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_abs_im_le hz (x k)) (abs_nonneg _)

/-- On the real line `D D̃ = |D|²`. -/
theorem translatePairExp_ofReal {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (r : ℝ) :
    translatePairExp s c x r = ((‖translateExpSum s c x r‖ ^ 2 : ℝ) : ℂ) := by
  unfold translatePairExp
  have h := translateExpSum_conj s c x r
  rw [Complex.conj_ofReal] at h
  rw [← h, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- On the imaginary axis `D` is a real exponential sum. -/
theorem translateExpSum_I_mul {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (y : ℝ) :
    translateExpSum s c x (I * y) = ((∑ k ∈ s, c k * Real.exp (-(y * x k)) : ℝ) : ℂ) := by
  unfold translateExpSum
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  linear_combination ((y : ℂ) * (x k : ℂ)) * Complex.I_mul_I

/-- The translation multiplier `T = D D̃ e^{−εz²}`. -/
theorem multiplier_gaussDamped_pairExp {ι : Type*} (s : Finset ι) (c x : ι → ℝ) {ε : ℝ}
    (hε : 0 < ε) : Multiplier (gaussDamped (translatePairExp s c x) ε) := by
  set M₁ := ∑ k ∈ s, |c k| * Real.exp (9 / 4 * |x k|) with hM₁
  have hM₁0 : 0 ≤ M₁ := Finset.sum_nonneg fun k _ => by positivity
  have hb : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖translatePairExp s c x z‖ ≤ M₁ * M₁ := by
    intro z hz
    unfold translatePairExp
    rw [norm_mul]
    have h2 := norm_translateExpSum_le s c (fun k => -x k) hz
    simp only [abs_neg] at h2
    exact mul_le_mul (norm_translateExpSum_le s c x hz) h2 (norm_nonneg _) hM₁0
  refine ⟨⟨1, _, one_pos, stripDecay_gaussDamped (differentiable_translatePairExp s c x)
    (mul_nonneg hM₁0 hM₁0) hb hε⟩, fun z => ?_, fun z => ?_⟩
  · unfold gaussDamped
    rw [translatePairExp_neg, neg_sq]
  · unfold gaussDamped
    rw [map_mul, translatePairExp_conj, ← Complex.exp_conj]
    congr 2
    simp [map_mul, map_neg, map_pow, Complex.conj_ofReal]

/-- **The lifted translation multiplier is nonnegative on the whole `ρ`-line.** -/
theorem re_rhoLift_gaussDamped_pairExp_nonneg {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ) (ε ρ : ℝ) :
    0 ≤ (rhoLift (gaussDamped (translatePairExp s c x) ε) ρ).re := by
  rcases le_or_gt 2 (ρ ^ 2) with hρ | hρ
  · unfold rhoLift
    rw [show (ρ : ℂ) ^ 2 - 2 = ((ρ ^ 2 - 2 : ℝ) : ℂ) by push_cast; ring,
      sqrtPrincipal_ofReal_of_nonneg (by linarith)]
    unfold gaussDamped
    rw [translatePairExp_ofReal, cexp_neg_mul_sq_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    positivity
  · rw [rhoLift_of_sq_le_two (fun z => by unfold gaussDamped; rw [translatePairExp_neg, neg_sq])
      hρ.le]
    set y := Real.sqrt (2 - ρ ^ 2)
    unfold gaussDamped translatePairExp
    rw [translateExpSum_I_mul, translateExpSum_I_mul,
      show -(ε : ℂ) * (I * (y : ℂ)) ^ 2 = ((ε * y ^ 2 : ℝ) : ℂ) by
        rw [mul_pow, Complex.I_sq]; push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h1 : 0 ≤ ∑ k ∈ s, c k * Real.exp (-(y * x k)) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk) (Real.exp_pos _).le
    have h2 : 0 ≤ ∑ k ∈ s, c k * Real.exp (-(y * -x k)) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk) (Real.exp_pos _).le
    positivity

/-! ## Resonators with nonnegative coefficients -/

theorem hasCompactSupport_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ k ∈ s, HasCompactSupport (f k)) : HasCompactSupport fun u => ∑ k ∈ s, f k u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- **Pole-free even positivity is positivity on nonnegative resonators.**  Let `g` be an even
real `C²` profile of compact support with `ĝ(i/2) = 0`.  If `L` is nonnegative on pole-free even
spectral squares, then `Re W(R ⋆ R̃) ≥ 0` for `R = Σ_k c_k g(· − x_k)` with `c_k ≥ 0`. -/
theorem re_weilFullFunctional_translateSum_nonneg {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 → 0 ≤ evenWeilDensity lam (specSq A))
    {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ)
    {g : ℝ → ℝ} (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hge : ∀ u, g (-u) = g u)
    (hg0 : paperFT (fun u => (g u : ℂ)) (I / 2) = 0) :
    0 ≤ (weilFullFunctional lam
      (EF.weilTest (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ))
        (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ)))).re := by
  set f : ℝ → ℝ := fun u => ∑ k ∈ s, c k * g (u - x k) with hfdef
  have hf2 : ContDiff ℝ 2 f :=
    ContDiff.sum fun k _ => contDiff_const.mul (hg2.comp (contDiff_id.sub contDiff_const))
  have hfc : HasCompactSupport f := hasCompactSupport_finset_sum s fun k _ =>
    (hgc.comp_homeomorph (Homeomorph.subRight (x k))).mul_left
  rw [re_weilFullFunctional_ofReal_eq_evenWeilDensity lam hf2 hfc]
  refine ge_of_tendsto (tendsto_evenWeilDensity_gaussDamped hg hf2 hfc)
    (Eventually.of_forall fun k => ?_)
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hgcc : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  set G := paperFT fun u => (g u : ℂ) with hGdef
  have hF : paperFT (fun u => (f u : ℂ)) = fun z => translateExpSum s c x z * G z := by
    funext z
    have h1 := paperFT_sum_translate s (fun k => (c k : ℂ)) x
      (contDiff_ofReal_comp hg2).continuous hgcc z
    have e : (fun u => (f u : ℂ)) = fun u => ∑ k ∈ s, (c k : ℂ) * (g (u - x k) : ℂ) := by
      funext u; simp only [hfdef]; push_cast; rfl
    rw [e, h1]
    rfl
  have hGe : ∀ z, G (-z) = G z := paperFT_neg_of_even fun u => by simp only [hge]
  have hG0' : G (-I / 2) = 0 := by rw [neg_div, hGe]; exact hg0
  have hGr : ∀ r : ℝ, (G r).im = 0 := fun r => by
    have h1 := paperFT_ofReal_neg_conj g (r : ℂ)
    rw [Complex.conj_ofReal, ← hGdef, hGe] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  -- the pole-free even profile `Φ = ĝ e^{−εz²/2}`
  set Φ := gaussDamped G (ε / 2) with hΦdef
  obtain ⟨N, hN, hb⟩ := exists_norm_paperFT_le_of_compact (contDiff_ofReal_comp hg2) hgcc (9 / 4)
  have hGb : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖G z‖ ≤ N := fun z hz =>
    (hb z hz).trans (div_le_self hN (by nlinarith [sq_nonneg ‖z‖]))
  have hS := stripDecay_gaussDamped (differentiable_paperFT_of_compact
    (contDiff_ofReal_comp hg2).continuous hgcc) hN hGb (half_pos hε)
  have hΦ : EvenStrip Φ := by
    refine ⟨⟨1, _, one_pos, fun z hz => hS.diff z (by linarith),
      fun z hz => hS.bound z (by linarith)⟩, fun z => ?_, fun r => ?_⟩
    · simp only [hΦdef, gaussDamped, hGe, neg_sq]
    · simp only [hΦdef, gaussDamped]
      rw [cexp_neg_mul_sq_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hGr r]
      ring
  have hΦ0 : Φ (I / 2) = 0 := by simp [hΦdef, gaussDamped, hg0]
  have hcongr : evenWeilDensity lam (specSq (gaussDamped (paperFT fun u => (f u : ℂ)) ε)) =
      evenWeilDensity lam (fun z => specSq Φ z * gaussDamped (translatePairExp s c x) ε z) := by
    refine evenWeilDensity_congr ?_ ?_ fun r => ?_
    · simp [specSq, gaussDamped, hF, hΦdef, hg0]
    · have hc2 : conj (-I / 2 : ℂ) = I / 2 := by
        rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
      simp only [specSq, gaussDamped, hF, hΦdef, hG0', hc2, hg0]
      simp
    · rw [specSq_gaussDamped, specSq_gaussDamped, specSq_ofReal_eq, specSq_ofReal_eq, hF]
      simp only [gaussDamped]
      rw [translatePairExp_ofReal, cexp_neg_mul_sq_ofReal, cexp_neg_mul_sq_ofReal,
        cexp_neg_mul_sq_ofReal, norm_mul, mul_pow]
      simp only [← Complex.ofReal_mul]
      congr 1
      have e : Real.exp (-(2 * ε * r ^ 2)) =
          Real.exp (-(2 * (ε / 2) * r ^ 2)) * Real.exp (-(ε * r ^ 2)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      ring
  rw [hcongr]
  exact evenWeilDensity_specSq_mul_multiplier_nonneg_of_poleFree hg hpos hΦ hΦ0
    (multiplier_gaussDamped_pairExp s c x hε) (re_rhoLift_gaussDamped_pairExp_nonneg s hc x ε)

/-- **Even positivity at any pole weight is positivity on nonnegative resonators.**  If `lam` is
Weil-positive at pole weight `β` on all even tests, then `Re W(R ⋆ R̃) ≥ 0` for every resonator
`R = Σ_k c_k g(· − x_k)` with `c_k ≥ 0` and an even real `C²` profile `g` of compact support with
`ĝ(i/2) = 0`. -/
theorem re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ) {g : ℝ → ℝ} (hg2 : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hge : ∀ u, g (-u) = g u)
    (hg0 : paperFT (fun u => (g u : ℂ)) (I / 2) = 0) :
    0 ≤ (weilFullFunctional lam
      (EF.weilTest (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ))
        (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ)))).re := by
  obtain ⟨Cg, -, hgr⟩ := exists_abs_le_of_weilPositiveEvenAt_any h
  exact re_weilFullFunctional_translateSum_nonneg hgr
    (fun A hA hA0 => evenWeilDensity_specSq_nonneg_of_poleFree h hgr hA hA0) s hc x hg2 hgc hge
    hg0

end RHTower.EvenSector

end
