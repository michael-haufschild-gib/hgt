import GaloisForLFunctions.RHTower.HerglotzWeilPositiveBridge
import GaloisForLFunctions.RHTower.WeilConePoleWeightRigidity
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.TrivialWeightBoostedProducer
import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSummatory
import GaloisForLFunctions.RHTower.WeilPositivitySummableWeightsObstruction
import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# The archimedean density caps the pole weight at the residue of `ζ`

Fix a pole weight `β` and real weights `lam` with `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`.  The Weil
function with pole weight `β` is

`Φ_β(s) = ½ψ(s/2) − ½log π + β(1/s + 1/(s − 1)) − Σ_{n≥2} lam(n) n^{−s}`  (`Re s > 1`),

i.e. `weilFunction lam + (β − 1)(1/s + 1/(s − 1))` (`poleWeightFunction`).

**Theorem** (`le_one_of_herglotz_poleWeightFunction`).  If `Φ_β` has a holomorphic continuation
with nonnegative real part to `Re s > ½`, then `β ≤ 1`.

Proof.
* *Positivity.*  The Weil functional with pole weight `β` is the line integral of `Φ_β` on
  `Re s = 5/4` (`weilPoleWeightFunctional_weilTest_eq_line`), so the Herglotz–Riesz bridge
  (`re_lineIntegral_nonneg_of_herglotz`) makes it nonnegative on every autocorrelation.  On polar
  tests (`f̂(±i/2) = 0`) the pole term vanishes, so `lam` is Weil-positive in the polar,
  level-wise sense (`weilPositive_of_herglotz_poleWeightFunction`).
* *Density ceiling.*  By the multiplicative Toeplitz bound, polar Weil positivity gives
  `A(N) = Σ_{nm ≤ N} lam(n)/(nm) ≤ (½ + ε)(log N)²` for large `N` (`weil_log_density_le`).  The
  archimedean symbol is `log N + O(1)` at the Nyquist scale, whatever the pole weight.
* *Residue.*  On `Re s > 1`, `Σ lam(n) n^{−s} = archPart(s) + (β − 1)(1/s + 1/(s−1)) − Φ(s)`, so
  `(s − 1)Σ lam(n)n^{−s} → β` as `s → 1`.
* *Abel.*  `Σ_k A(k)` is the summatory function of `(lam ⋆ 1)(k)/k`, whose Dirichlet series is
  `L_lam(1 + σ)ζ(1 + σ) ∼ β/σ²`.  The integral representation
  `L(σ) = σ ∫_1^∞ A(⌊t⌋) t^{−σ−1} dt` and the ceiling give `σ²L(σ) ≤ 1 + 2ε + O(σ²)`.  Letting
  `σ → 0` gives `β ≤ 1 + 2ε` for every `ε > 0`.

**Theorem** (`eq_one_of_herglotz_poleWeightFunction`).  Under the same hypothesis, `β = 1`.
* `β > 0` (`pos_of_herglotz_poleWeightFunction`): on the flat-top window test the functional is
  `β·pole + archimedean energy`, with nonnegative pole and negative archimedean energy.
* For `β > 0`, dividing by `β` gives a Herglotz datum with residue `1` and archimedean part
  `(Γ̃(s) + (β−1)/s)/β` (`herglotzWeilPositive_scaled`).  The summatory law then gives
  `Σ_{n ≤ N} lam(n) = βN + O(N)`, so the deviation from `Λ` has linearly bounded partial sums.
* The twisted-arc null tests exclude `β < 1` for such weights
  (`not_forall_re_weilPoleWeightFunctional_nonneg`).

So the archimedean factor of `ζ` alone fixes the pole weight of every Weil-positive datum at the
residue `1`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilPoleWeight

open Zeta23 AtomDomination WeilLineIntegral WeilAtomic Zeta23.WeilEF

/-- The Weil function with pole weight `β`: `weilFunction lam + (β − 1)(1/s + 1/(s − 1))`. -/
def poleWeightFunction (β : ℝ) (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  WeilHerglotz.weilFunction lam s + ((β : ℂ) - 1) * gPair 0 s

theorem poleWeightFunction_conj (β : ℝ) (lam : ℕ → ℝ) (s : ℂ) :
    poleWeightFunction β lam (conj s) = conj (poleWeightFunction β lam s) := by
  unfold poleWeightFunction gPair
  rw [WeilSpectral.weilFunction_conj]
  simp [map_add, map_mul, map_sub, Complex.conj_ofReal]

/-! ### Regularity of the Weil function on `Re s > 1` -/

theorem differentiableAt_weilFunction_of_summable {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (WeilHerglotz.weilFunction lam) s := by
  have habs : LSeries.abscissaOfAbsConv (WeilHerglotz.lamC lam) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      lseriesSummable_lamC hsl hy
  have hL : DifferentiableAt ℂ (LSeries (WeilHerglotz.lamC lam)) s := by
    have hlt : LSeries.abscissaOfAbsConv (WeilHerglotz.lamC lam) < s.re :=
      lt_of_le_of_lt habs (by exact_mod_cast hs)
    have hopen : IsOpen {z : ℂ | LSeries.abscissaOfAbsConv (WeilHerglotz.lamC lam) < z.re} :=
      isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)
    exact (LSeries_differentiableOn _).differentiableAt (hopen.mem_nhds hlt)
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
  have hA : DifferentiableAt ℂ RelaxedHerglotz.archPart s := by
    have hmem : s ∈ ({z : ℂ | 1 < z.re} \ {1}) := ⟨hs, hs1⟩
    have hopen : IsOpen ({z : ℂ | 1 < z.re} \ {1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    exact (RelaxedHerglotz.differentiableOn_archPart one_pos).differentiableAt
      (hopen.mem_nhds hmem)
  have heq : WeilHerglotz.weilFunction lam =
      fun z => RelaxedHerglotz.archPart z - LSeries (WeilHerglotz.lamC lam) z :=
    funext fun z => RelaxedHerglotz.weilFunction_eq_archPart_sub lam z
  rw [heq]
  exact hA.sub hL

theorem continuous_poleWeightFunction_line {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) (β : ℝ) {c : ℝ}
    (hc : 1 < c) : Continuous fun t : ℝ => poleWeightFunction β lam ((c : ℂ) + t * I) := by
  have hre : ∀ t : ℝ, 1 < ((c : ℂ) + t * I).re := fun t => by simp [hc]
  have hW : Continuous fun t : ℝ => WeilHerglotz.weilFunction lam ((c : ℂ) + t * I) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + t * I)
        (differentiableAt_weilFunction_of_summable hsl (hre t)).continuousAt (by fun_prop)
  have hg : Continuous fun t : ℝ => gPair 0 ((c : ℂ) + t * I) := by
    unfold gPair
    refine Continuous.add ?_ ?_
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp at this; linarith
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp at this; linarith
  unfold poleWeightFunction
  exact hW.add (continuous_const.mul hg)

theorem norm_gPair_zero_le {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ 1 / c + 1 / (c - 1) := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  unfold gPair
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_one, sub_zero]
    refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [hre, abs_of_pos (by linarith)] at this
    exact this
  · rw [norm_div, norm_one]
    refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I - (1 - 0))
    have hre' : ((c : ℂ) + t * I - (1 - 0)).re = c - 1 := by simp
    rw [hre', abs_of_pos (show (0 : ℝ) < c - 1 by linarith)] at this
    exact this

/-! ### The pole-weight functional as a line integral -/

/-- **Line-integral form of the pole-weight functional** on autocorrelations. -/
theorem weilPoleWeightFunctional_weilTest_eq_line {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) (β : ℝ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilPoleWeightFunctional β lam (EF.weilTest f f) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (Hfn (EF.weilTest f f) (((5 / 4 : ℝ) : ℂ) + t * I) +
        Hfn (EF.weilTest f f) (1 - ((5 / 4 : ℝ) : ℂ) - t * I)) *
        poleWeightFunction β lam (((5 / 4 : ℝ) : ℂ) + t * I) := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  set c₀ : ℝ := 5 / 4 with hc₀
  set F : ℝ → ℂ := fun t => Hfn k (c₀ + t * I) + Hfn k (1 - c₀ - t * I) with hF
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le hf hfc
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c₀ - t * I = ((1 - c₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c₀ t (by norm_num [hc₀]) (by norm_num [hc₀])
    have h2 := hD (1 - c₀) (-t) (by norm_num [hc₀]) (by norm_num [hc₀])
    rw [neg_sq] at h2
    rw [two_mul, add_div]
    exact add_le_add h1 h2
  have hkn2 : ContDiff ℝ 2 (fun u => k (-u)) := hkd.comp contDiff_neg
  have hknc : HasCompactSupport (fun u => k (-u)) := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have hFc : Continuous F := by
    have hm : ∀ t : ℝ, Hfn k (1 - c₀ - t * I) = Hfn (fun u => k (-u)) (c₀ + t * I) :=
      fun t => Hfn_mirror k c₀ t
    simp only [hF, hm]
    exact (continuous_Hfn_line hkd hkc c₀).add (continuous_Hfn_line hkn2 hknc c₀)
  obtain ⟨A, hA0, hA⟩ := norm_weilFunction_le hsl (c := c₀) (by norm_num [hc₀])
    (by norm_num [hc₀])
  have hWc : Continuous fun t : ℝ => WeilHerglotz.weilFunction lam ((c₀ : ℂ) + t * I) := by
    have hre : ∀ t : ℝ, 1 < ((c₀ : ℂ) + t * I).re := fun t => by simp [hc₀]; norm_num
    exact continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := fun t : ℝ => (c₀ : ℂ) + t * I)
        (differentiableAt_weilFunction_of_summable hsl (hre t)).continuousAt (by fun_prop)
  have hgc : Continuous fun t : ℝ => gPair 0 ((c₀ : ℂ) + t * I) := by
    have := continuous_poleWeightFunction_line hsl 1 (c := c₀) (by norm_num [hc₀])
    unfold gPair
    refine Continuous.add ?_ ?_
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp at this; norm_num [hc₀] at this
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp at this; norm_num [hc₀] at this
  have hdom : Integrable fun t : ℝ => (1 + t ^ 2)⁻¹ := integrable_inv_one_add_sq
  have hiW : Integrable fun t : ℝ => F t * WeilHerglotz.weilFunction lam ((c₀ : ℂ) + t * I) := by
    refine (hdom.const_mul (4 * D * A)).mono' (hFc.mul hWc).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    have hsq : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    have h1t : 1 + |t| ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, abs_nonneg t]
    calc ‖F t‖ * ‖WeilHerglotz.weilFunction lam ((c₀ : ℂ) + t * I)‖
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (A * (1 + |t|)) :=
          mul_le_mul (hFb t) (hA t) (norm_nonneg _) (by positivity)
      _ ≤ (2 * D / (1 + t ^ 2) ^ 2) * (A * (2 * (1 + t ^ 2))) := by gcongr
      _ = 4 * D * A * (1 + t ^ 2)⁻¹ := by field_simp; ring
  have hig : Integrable fun t : ℝ => F t * gPair 0 ((c₀ : ℂ) + t * I) := by
    refine (hdom.const_mul (2 * D * (1 / c₀ + 1 / (c₀ - 1)))).mono'
      (hFc.mul hgc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖F t‖ * ‖gPair 0 ((c₀ : ℂ) + t * I)‖
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (1 / c₀ + 1 / (c₀ - 1)) :=
          mul_le_mul (hFb t) (norm_gPair_zero_le (by norm_num [hc₀]) t) (norm_nonneg _)
            (by positivity)
      _ ≤ (2 * D / (1 + t ^ 2)) * (1 / c₀ + 1 / (c₀ - 1)) := by
          gcongr
          nlinarith [sq_nonneg t]
      _ = 2 * D * (1 / c₀ + 1 / (c₀ - 1)) * (1 + t ^ 2)⁻¹ := by ring
  have hline := weilFullFunctional_eq_line_integral hsl hkd hkc (c := c₀) (by norm_num [hc₀])
    (by norm_num [hc₀])
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hkd hkc
  have hpole : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, F t * gPair 0 (c₀ + t * I)) =
      paperFT k (I / 2) + paperFT k (-I / 2) := by
    have h := two_line_pair (differentiable_Hfn hkd hkc) (c := c₀) (C := C)
      (fun σ t h1 h2 => hC σ t (by norm_num [hc₀] at h1 ⊢; linarith)
        (by norm_num [hc₀] at h2 ⊢; linarith)) (z₀ := 0)
      (by simp; norm_num [hc₀]) (by simp; norm_num [hc₀])
    rw [sub_zero, Hfn_zero, Hfn_one] at h
    exact h
  have hsplit : (∫ t : ℝ, F t * poleWeightFunction β lam ((c₀ : ℂ) + t * I)) =
      (∫ t : ℝ, F t * WeilHerglotz.weilFunction lam ((c₀ : ℂ) + t * I)) +
        ((β : ℂ) - 1) * ∫ t : ℝ, F t * gPair 0 ((c₀ : ℂ) + t * I) := by
    rw [← integral_const_mul, ← integral_add hiW (hig.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [poleWeightFunction]
    ring
  show weilPoleWeightFunctional β lam k = (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ, F t * poleWeightFunction β lam ((c₀ : ℂ) + t * I)
  rw [hsplit, mul_add, weilPoleWeightFunctional, hline]
  congr 1
  rw [← hpole]
  ring

/-! ### Positivity from a Herglotz continuation -/

/-- **A Herglotz continuation of `Φ_β` makes the pole-weight-`β` functional nonnegative.** -/
theorem re_weilPoleWeightFunctional_nonneg_of_herglotz {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (weilPoleWeightFunctional β lam (EF.weilTest f f)).re := by
  obtain ⟨A, hA0, hA⟩ := norm_weilFunction_le hsl (c := 5 / 4) (by norm_num) (by norm_num)
  have hAβ : ∀ t : ℝ, ‖poleWeightFunction β lam (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤
      (A + |β - 1| * 5) * (1 + |t|) := by
    intro t
    unfold poleWeightFunction
    have hg := norm_gPair_zero_le (c := 5 / 4) (by norm_num) t
    have hβ : ‖((β : ℂ) - 1)‖ = |β - 1| := by
      rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hβ]
    have h1 : |β - 1| * ‖gPair 0 (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ |β - 1| * 5 :=
      mul_le_mul_of_nonneg_left (hg.trans (by norm_num)) (abs_nonneg _)
    have h2 : |β - 1| * 5 ≤ |β - 1| * 5 * (1 + |t|) :=
      le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg t])
    nlinarith [hA t]
  rw [weilPoleWeightFunctional_weilTest_eq_line hsl β hf hfc]
  exact re_lineIntegral_nonneg_of_herglotz hΦd hΦre
    (fun s hs => herglotz_conj_of hΦd hΦ (fun z _ => poleWeightFunction_conj β lam z) hs) hΦ
    (by positivity) hAβ hf hfc

/-- On polar tests the pole term of an autocorrelation vanishes. -/
theorem weilPoleWeightFunctional_weilTest_eq_of_polar (β : ℝ) (lam : ℕ → ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) :
    weilPoleWeightFunctional β lam (EF.weilTest f f) =
      weilFullFunctional lam (EF.weilTest f f) := by
  have h1 : paperFT (EF.weilTest f f) (I / 2) = 0 := by
    rw [EF.paperFT_weilTest hf hf hfc hfc, hp, zero_mul]
  have h2 : paperFT (EF.weilTest f f) (-I / 2) = 0 := by
    rw [EF.paperFT_weilTest hf hf hfc hfc, neg_div, hm, zero_mul]
  unfold weilPoleWeightFunctional
  rw [h1, h2, add_zero, mul_zero, add_zero]

/-- **A Herglotz continuation of `Φ_β` gives polar Weil positivity**, whatever `β`. -/
theorem weilPositive_of_herglotz_poleWeightFunction {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) :
    WeilPositive lam :=
  weilPositive_of_polar fun f hf hfc hp hm => by
    rw [← weilPoleWeightFunctional_weilTest_eq_of_polar β lam hf.continuous hfc hp hm]
    exact re_weilPoleWeightFunctional_nonneg_of_herglotz hsl hΦd hΦre hΦ hf hfc

/-! ### The residue of the weights -/

/-- **The pole weight is the residue of the weights.**  If `Φ_β` continues holomorphically to
`Re s > ½`, then `σ · Σ lam(n) n^{−1−σ} → β` as `σ → 0⁺`. -/
theorem tendsto_mul_LSeries_lamC_of_herglotz {lam : ℕ → ℝ} {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) :
    Tendsto (fun σ : ℝ => (σ : ℂ) * LSeries (WeilHerglotz.lamC lam) (1 + σ)) (𝓝[>] 0)
      (𝓝 (β : ℂ)) := by
  set g : ℝ → ℂ := fun σ => (σ : ℂ) * RelaxedHerglotz.archRegular (1 + σ) + 1 +
    ((β : ℂ) - 1) * ((σ : ℂ) / (1 + σ) + 1) - (σ : ℂ) * Φ (1 + σ) with hg
  have hshift : ContinuousAt (fun σ : ℝ => (1 : ℂ) + σ) 0 := by fun_prop
  have hA : ContinuousAt (fun σ : ℝ => RelaxedHerglotz.archRegular (1 + σ)) 0 :=
    RelaxedHerglotz.continuousAt_archRegular_one.comp_of_eq hshift (by simp)
  have h1 : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by simp; norm_num
  have hΦc : ContinuousAt Φ 1 :=
    (hΦd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      h1)).continuousAt
  have hP : ContinuousAt (fun σ : ℝ => Φ (1 + σ)) 0 := hΦc.comp_of_eq hshift (by simp)
  have hgc : ContinuousAt g 0 := by
    have hden : ContinuousAt (fun σ : ℝ => (σ : ℂ) / (1 + σ)) 0 :=
      (Complex.continuous_ofReal.continuousAt).div hshift (by simp)
    exact ((((Complex.continuous_ofReal.continuousAt).mul hA).add continuousAt_const).add
      (continuousAt_const.mul (hden.add continuousAt_const))).sub
      ((Complex.continuous_ofReal.continuousAt).mul hP)
  have hg0 : g 0 = β := by simp [hg]
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 (β : ℂ)) := by
    rw [← hg0]; exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun σ (hσ : 0 < σ) => ?_)
  have hre : 1 < ((1 : ℂ) + σ).re := by simp; exact hσ
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have h1σ : (1 : ℂ) + σ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hL : LSeries (WeilHerglotz.lamC lam) (1 + σ) = RelaxedHerglotz.archPart (1 + σ) +
      ((β : ℂ) - 1) * gPair 0 (1 + σ) - Φ (1 + σ) := by
    rw [hΦ _ hre, poleWeightFunction, RelaxedHerglotz.weilFunction_eq_archPart_sub]
    ring
  show g σ = (σ : ℂ) * LSeries (WeilHerglotz.lamC lam) (1 + σ)
  rw [hL]
  simp only [hg, RelaxedHerglotz.archPart, RelaxedHerglotz.archRegular, gPair, sub_zero,
    add_sub_cancel_left]
  field_simp

/-! ### The log-density sums as partial sums of a Dirichlet series -/

/-- `A(N) = Σ_{nm ≤ N, n ≥ 2} lam(n)/(nm)`, the sums of the density ceiling. -/
def logDensitySum (lam : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n / (n * m) else 0)

/-- The coefficients `(lam ⋆ 1)(k)/k`, whose partial sums are `A(N)`. -/
def lamConv (lam : ℕ → ℝ) (k : ℕ) : ℂ :=
  LSeries.convolution (WeilHerglotz.lamC lam) 1 k / k

theorem term_lamConv (lam : ℕ → ℝ) (σ : ℝ) (k : ℕ) :
    LSeries.term (lamConv lam) σ k =
      LSeries.term (LSeries.convolution (WeilHerglotz.lamC lam) 1) (1 + σ) k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [LSeries.term_of_ne_zero hk, LSeries.term_of_ne_zero hk, lamConv, div_div]
  congr 1
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [Complex.cpow_add _ _ hkC, Complex.cpow_one]

theorem LSeries_lamConv {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ} (hσ : 0 < σ) :
    LSeries (lamConv lam) σ = LSeries (WeilHerglotz.lamC lam) (1 + σ) * riemannZeta (1 + σ) := by
  have hre : 1 < ((1 : ℂ) + σ).re := by simp; exact hσ
  have h1 : LSeriesSummable (WeilHerglotz.lamC lam) (1 + σ) := by
    have := lseriesSummable_lamC hsl (c := 1 + σ) (by linarith)
    simpa using this
  have h2 : LSeriesSummable 1 (1 + σ) := LSeriesSummable_one_iff.mpr hre
  have hconv : LSeries (lamConv lam) σ =
      LSeries (LSeries.convolution (WeilHerglotz.lamC lam) 1) (1 + σ) := by
    unfold LSeries
    exact tsum_congr fun k => term_lamConv lam σ k
  rw [hconv, LSeries_convolution' h1 h2, LSeries_one_eq_riemannZeta hre]

theorem LSeriesSummable_lamConv {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ} (hσ : 0 < σ) :
    LSeriesSummable (lamConv lam) σ := by
  have hre : 1 < ((1 : ℂ) + σ).re := by simp; exact hσ
  have h1 : LSeriesSummable (WeilHerglotz.lamC lam) (1 + σ) := by
    have := lseriesSummable_lamC hsl (c := 1 + σ) (by linarith)
    simpa using this
  have h2 : LSeriesSummable 1 (1 + σ) := LSeriesSummable_one_iff.mpr hre
  have h := h1.convolution h2
  unfold LSeriesSummable at h ⊢
  exact h.congr fun k => (term_lamConv lam σ k).symm

/-- **The partial sums of `(lam ⋆ 1)(k)/k` are the log-density sums.** -/
theorem sum_Icc_lamConv (lam : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, lamConv lam k = (logDensitySum lam N : ℂ) := by
  set g : ℕ × ℕ → ℂ := fun p => WeilHerglotz.lamC lam p.1 / ((p.1 : ℂ) * p.2) with hgdef
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
    with hS
  have hleft : ∑ k ∈ Finset.Icc 1 N, lamConv lam k = ∑ p ∈ S, g p := by
    have hk : ∀ k ∈ Finset.Icc 1 N, lamConv lam k =
        ∑ p ∈ k.divisorsAntidiagonal, g p := by
      intro k _
      rw [lamConv, LSeries.convolution_def, Finset.sum_div]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hpk, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      rw [hgdef, Pi.one_apply, mul_one, ← hpk]
      push_cast
      ring
    rw [Finset.sum_congr rfl hk, Finset.sum_sigma']
    refine Finset.sum_bij' (fun x _ => x.2) (fun p _ => ⟨p.1 * p.2, p⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨k, p⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨⟨hk1, hkN⟩, hpk, -⟩ := hx
      have h1 : 1 ≤ p.1 := Nat.pos_of_ne_zero fun h => by rw [h] at hpk; omega
      have h2 : 1 ≤ p.2 := Nat.pos_of_ne_zero fun h => by rw [h] at hpk; omega
      simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, by omega⟩
      · nlinarith
      · nlinarith
    · rintro p hp
      simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨h1, -⟩, h2, -⟩, hN⟩ := hp
      have hne : p.1 * p.2 ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, hN⟩,
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hne⟩⟩
    · rintro ⟨k, p⟩ hx
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨-, hpk, -⟩ := hx
      simp [hpk]
    · intro p _; rfl
    · intro x _; rfl
  have hright : ∑ p ∈ S, g p = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then g (n, m) else 0) := by
    rw [hS, Finset.sum_filter, Finset.sum_product]
  rw [hleft, hright, logDensitySum]
  push_cast
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_left (by norm_num)
  rw [← Finset.sum_subset hsub (fun n hn hn2 => ?_)]
  · refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    split_ifs <;> simp [hgdef, WeilHerglotz.lamC, hn2]
  · have hn1 : n = 1 := by
      simp only [Finset.mem_Icc, not_and, not_le] at hn hn2
      omega
    subst hn1
    exact Finset.sum_eq_zero fun m _ => by simp [hgdef, WeilHerglotz.lamC]

/-! ### Growth of the log-density sums -/

theorem abs_logDensitySum_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |logDensitySum lam N| ≤ C * (N : ℝ) ^ r := by
  set T : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (1 + r / 2) with hT
  have hsT := hsl (1 + r / 2) (by linarith)
  have hT0 : 0 ≤ T := tsum_nonneg fun n => by positivity
  refine ⟨T * (1 + 2 / r), by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : |logDensitySum lam N| ≤ ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      |lam n| / n * (1 / m) := by
    unfold logDensitySum
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hn : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (by omega : 0 < n)
    have hm : (0 : ℝ) < m := by
      have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (by omega : 0 < m)
    split_ifs
    · rw [abs_div, abs_of_pos (mul_pos hn hm)]
      apply le_of_eq
      field_simp
    · simp only [abs_zero]
      positivity
  have h2 : ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N, |lam n| / n * (1 / m) =
      (∑ n ∈ Finset.Icc 2 N, |lam n| / n) * ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  have h3 : ∑ n ∈ Finset.Icc 2 N, |lam n| / n ≤ T * (N : ℝ) ^ (r / 2) := by
    calc ∑ n ∈ Finset.Icc 2 N, |lam n| / n
        ≤ ∑ n ∈ Finset.Icc 2 N, |lam n| / (n : ℝ) ^ (1 + r / 2) * (N : ℝ) ^ (r / 2) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
          have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          have hpow : (n : ℝ) ^ (r / 2) ≤ (N : ℝ) ^ (r / 2) :=
            Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) (by positivity)
          have hp0 : 0 < (n : ℝ) ^ (r / 2) := Real.rpow_pos_of_pos hn0 _
          rw [Real.rpow_add hn0, Real.rpow_one]
          calc |lam n| / n = |lam n| / (n * n ^ (r / 2)) * n ^ (r / 2) := by field_simp
            _ ≤ |lam n| / (n * n ^ (r / 2)) * N ^ (r / 2) :=
                mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (∑ n ∈ Finset.Icc 2 N, |lam n| / (n : ℝ) ^ (1 + r / 2)) * (N : ℝ) ^ (r / 2) := by
          rw [Finset.sum_mul]
      _ ≤ T * (N : ℝ) ^ (r / 2) := by
          gcongr
          exact hsT.sum_le_tsum _ (fun n _ => by positivity)
  have h4 : ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) ≤ (1 + 2 / r) * (N : ℝ) ^ (r / 2) := by
    have hH : ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
    rw [hH]
    have hlog := harmonic_le_one_add_log N
    have hl := Real.log_le_rpow_div hN0.le (show 0 < r / 2 by positivity)
    have hp : 1 ≤ (N : ℝ) ^ (r / 2) := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
    have he : (N : ℝ) ^ (r / 2) / (r / 2) = 2 / r * (N : ℝ) ^ (r / 2) := by field_simp
    have h2r : 0 ≤ 2 / r := by positivity
    nlinarith
  have hsq : (N : ℝ) ^ (r / 2) * (N : ℝ) ^ (r / 2) = (N : ℝ) ^ r := by
    rw [← Real.rpow_add hN0]; ring_nf
  calc |logDensitySum lam N|
      ≤ (∑ n ∈ Finset.Icc 2 N, |lam n| / n) * ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) :=
        h1.trans h2.le
    _ ≤ (T * (N : ℝ) ^ (r / 2)) * ((1 + 2 / r) * (N : ℝ) ^ (r / 2)) := by
        gcongr
    _ = T * (1 + 2 / r) * ((N : ℝ) ^ (r / 2) * (N : ℝ) ^ (r / 2)) := by ring
    _ = T * (1 + 2 / r) * (N : ℝ) ^ r := by rw [hsq]

theorem isBigO_sum_lamConv {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {r : ℝ} (hr : 0 < r) :
    (fun n => ∑ k ∈ Finset.Icc 1 n, lamConv lam k) =O[atTop] fun n => (n : ℝ) ^ r := by
  obtain ⟨C, hC0, hC⟩ := abs_logDensitySum_le hsl hr
  refine Asymptotics.IsBigO.of_bound C (eventually_atTop.mpr ⟨1, fun N hN => ?_⟩)
  rw [sum_Icc_lamConv, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ r)]
  exact hC N hN

/-! ### Two Mellin integrals -/

theorem integral_Ioi_one_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
    show -σ - 1 + 1 = -σ by ring]
  field_simp

theorem tendsto_log_pow_mul_rpow_neg {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    Tendsto (fun t : ℝ => Real.log t ^ j * t ^ (-σ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ) hσ).tendsto_div_nhds_zero
  refine h.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  have ht0 : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg ht
  show Real.log t ^ (j : ℝ) / t ^ σ = Real.log t ^ j * t ^ (-σ)
  rw [Real.rpow_natCast, Real.rpow_neg ht0.le, div_eq_mul_inv]

theorem integrableOn_log_sq_mul_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t => Real.log t ^ 2 * t ^ (-σ - 1)) (Ioi 1) := by
  have hdom : IntegrableOn (fun t : ℝ => 16 / σ ^ 2 * t ^ (-σ / 2 - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hdom.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : t ≠ 0 := by have : (1 : ℝ) < t := ht; linarith
    exact (((Real.continuousAt_log ht0).pow 2).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl ht0))).continuousWithinAt
  · have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hl := Real.log_le_rpow_div ht0.le (show 0 < σ / 4 by positivity)
    have hl' : Real.log t ≤ 4 / σ * t ^ (σ / 4) := by
      rw [show t ^ (σ / 4) / (σ / 4) = 4 / σ * t ^ (σ / 4) by field_simp] at hl
      exact hl
    have hsq : Real.log t ^ 2 ≤ 16 / σ ^ 2 * t ^ (σ / 2) := by
      have hp : t ^ (σ / 4) * t ^ (σ / 4) = t ^ (σ / 2) := by
        rw [← Real.rpow_add ht0]; ring_nf
      calc Real.log t ^ 2 = Real.log t * Real.log t := by ring
        _ ≤ (4 / σ * t ^ (σ / 4)) * (4 / σ * t ^ (σ / 4)) :=
            mul_le_mul hl' hl' hl0 (by positivity)
        _ = 16 / σ ^ 2 * (t ^ (σ / 4) * t ^ (σ / 4)) := by ring
        _ = 16 / σ ^ 2 * t ^ (σ / 2) := by rw [hp]
    have hpos : 0 ≤ Real.log t ^ 2 * t ^ (-σ - 1) := by positivity
    rw [Real.norm_of_nonneg hpos]
    have he : t ^ (σ / 2) * t ^ (-σ - 1) = t ^ (-σ / 2 - 1) := by
      rw [← Real.rpow_add ht0]; ring_nf
    calc Real.log t ^ 2 * t ^ (-σ - 1) ≤ 16 / σ ^ 2 * t ^ (σ / 2) * t ^ (-σ - 1) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 16 / σ ^ 2 * t ^ (-σ / 2 - 1) := by rw [mul_assoc, he]

theorem integral_Ioi_one_log_sq_mul_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi (1 : ℝ), Real.log t ^ 2 * t ^ (-σ - 1) = 2 / σ ^ 3 := by
  set F : ℝ → ℝ := fun t =>
    -(t ^ (-σ)) * (Real.log t ^ 2 / σ + 2 * Real.log t / σ ^ 2 + 2 / σ ^ 3) with hF
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt F (Real.log x ^ 2 * x ^ (-σ - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have : (1 : ℝ) < x := hx; linarith
    have hxp : 0 < x := by have : (1 : ℝ) < x := hx; linarith
    have hr := Real.hasDerivAt_rpow_const (x := x) (p := -σ) (Or.inl hx0)
    have hl := Real.hasDerivAt_log hx0
    have hP : HasDerivAt (fun t => Real.log t ^ 2 / σ + 2 * Real.log t / σ ^ 2 + 2 / σ ^ 3)
        ((2 * Real.log x * x⁻¹) / σ + 2 * x⁻¹ / σ ^ 2) x := by
      have := (((hl.pow 2).div_const σ).add ((hl.const_mul 2).div_const (σ ^ 2))).add_const
        (2 / σ ^ 3)
      refine this.congr_deriv ?_
      push_cast
      ring
    refine (hr.neg.mul hP).congr_deriv ?_
    rw [Real.rpow_sub_one hx0]
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 1) 1 := by
    have h1 : ContinuousAt F 1 := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (-σ)) 1 :=
        Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
      have hlog : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
      exact hc.neg.mul (((hlog.pow 2).div_const _).add ((hlog.const_mul 2).div_const _)
        |>.add continuousAt_const)
    exact h1.continuousWithinAt
  have hint := integrableOn_log_sq_mul_rpow_neg hσ
  have htend : Tendsto F atTop (𝓝 0) := by
    have h2 := tendsto_log_pow_mul_rpow_neg hσ 2
    have h1 := tendsto_log_pow_mul_rpow_neg hσ 1
    have h0 := tendsto_log_pow_mul_rpow_neg hσ 0
    have hsum := ((h2.div_const σ).add ((h1.const_mul 2).div_const (σ ^ 2))).add
      (h0.const_mul (2 / σ ^ 3))
    simp only [zero_div, mul_zero, add_zero] at hsum
    have hneg := hsum.neg
    rw [neg_zero] at hneg
    refine hneg.congr fun t => ?_
    simp only [hF, pow_one, pow_zero, one_mul]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  simp only [hF, Real.one_rpow, Real.log_one]
  ring

/-! ### The Abelian bound -/

/-- **Abel's bound.**  If `A(N) ≤ c (log N)²` for `N ≥ N₀` and `A(N) ≤ K` below `N₀`, then
`Re Σ (lam ⋆ 1)(k) k^{−1−σ} ≤ K + 2c/σ²` for every `σ > 0`. -/
theorem re_LSeries_lamConv_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {c K : ℝ} {N₀ : ℕ}
    (hc : 0 ≤ c) (hceil : ∀ N : ℕ, N₀ ≤ N → logDensitySum lam N ≤ c * Real.log N ^ 2)
    (hK : ∀ N : ℕ, N < N₀ → logDensitySum lam N ≤ K) (hK0 : 0 ≤ K) {σ : ℝ} (hσ : 0 < σ) :
    (LSeries (lamConv lam) σ).re ≤ K + 2 * c / σ ^ 2 := by
  have hrep := LSeries_eq_mul_integral (lamConv lam) (r := σ / 2) (by positivity)
    (s := (σ : ℂ)) (by simp; linarith) (LSeriesSummable_lamConv hsl hσ)
    (isBigO_sum_lamConv hsl (by positivity : (0 : ℝ) < σ / 2))
  set f : ℝ → ℝ := fun t => logDensitySum lam ⌊t⌋₊ * t ^ (-σ - 1) with hf
  have hpt : Set.EqOn (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, lamConv lam k) *
      (t : ℂ) ^ (-((σ : ℂ) + 1))) (fun t => ((f t : ℝ) : ℂ)) (Ioi 1) := by
    intro t ht
    have ht0 : 0 ≤ t := by have : (1 : ℝ) < t := ht; linarith
    simp only [hf]
    rw [sum_Icc_lamConv, show -((σ : ℂ) + 1) = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0]
    push_cast
    ring
  have hre : (LSeries (lamConv lam) σ).re = σ * ∫ t in Ioi (1 : ℝ), f t := by
    rw [hrep, setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  -- integrability of `f`
  obtain ⟨C, hC0, hC⟩ := abs_logDensitySum_le hsl (show (0 : ℝ) < σ / 2 by positivity)
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi 1)) :=
    (((measurable_from_nat (f := fun N => logDensitySum lam N)).comp Nat.measurable_floor).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  have hfi : IntegrableOn f (Ioi 1) := by
    have hdom : IntegrableOn (fun t : ℝ => C * t ^ (-σ / 2 - 1)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine hdom.mono' hfm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hfl : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht1.le
    have hfle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hA := hC ⌊t⌋₊ hfl
    have hpow : (⌊t⌋₊ : ℝ) ^ (σ / 2) ≤ t ^ (σ / 2) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hfle (by positivity)
    rw [Real.norm_eq_abs, hf, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc |logDensitySum lam ⌊t⌋₊| * t ^ (-σ - 1) ≤ C * t ^ (σ / 2) * t ^ (-σ - 1) := by
          gcongr
          exact hA.trans (mul_le_mul_of_nonneg_left hpow hC0)
      _ = C * t ^ (-σ / 2 - 1) := by rw [mul_assoc, ← Real.rpow_add ht0]; ring_nf
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have h2 := integrableOn_log_sq_mul_rpow_neg hσ
  set g : ℝ → ℝ := fun t => K * t ^ (-σ - 1) + c * (Real.log t ^ 2 * t ^ (-σ - 1)) with hg
  have hgi : IntegrableOn g (Ioi 1) := (h1.const_mul K).add (h2.const_mul c)
  have hfg : ∀ t ∈ Ioi (1 : ℝ), f t ≤ g t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hp : 0 < t ^ (-σ - 1) := Real.rpow_pos_of_pos ht0 _
    have hA : logDensitySum lam ⌊t⌋₊ ≤ K + c * Real.log t ^ 2 := by
      have hc2 : 0 ≤ c * Real.log t ^ 2 := by positivity
      rcases lt_or_ge ⌊t⌋₊ N₀ with h | h
      · have := hK _ h
        linarith
      · have h1 := hceil _ h
        have hfl : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht1.le
        have hfl' : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfl
        have hlog0 : 0 ≤ Real.log ⌊t⌋₊ := Real.log_nonneg hfl'
        have hlogle : Real.log ⌊t⌋₊ ≤ Real.log t :=
          Real.log_le_log (by linarith) (Nat.floor_le ht0.le)
        have hsq : Real.log ⌊t⌋₊ ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hlog0 hlogle 2
        have : c * Real.log ⌊t⌋₊ ^ 2 ≤ c * Real.log t ^ 2 := mul_le_mul_of_nonneg_left hsq hc
        linarith
    simp only [hf, hg]
    nlinarith
  have hJ := setIntegral_mono_on hfi hgi measurableSet_Ioi hfg
  have hJg : ∫ t in Ioi (1 : ℝ), g t = K / σ + c * (2 / σ ^ 3) := by
    simp only [hg]
    rw [integral_add (h1.const_mul K) (h2.const_mul c), integral_const_mul, integral_const_mul,
      integral_Ioi_one_rpow_neg hσ, integral_Ioi_one_log_sq_mul_rpow_neg hσ]
    ring
  rw [hre]
  calc σ * ∫ t in Ioi (1 : ℝ), f t ≤ σ * (K / σ + c * (2 / σ ^ 3)) :=
        mul_le_mul_of_nonneg_left (hJ.trans hJg.le) hσ.le
    _ = K + 2 * c / σ ^ 2 := by field_simp

/-! ### The theorem -/

theorem tendsto_mul_riemannZeta_one_add :
    Tendsto (fun σ : ℝ => (σ : ℂ) * riemannZeta (1 + σ)) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun σ : ℝ => (1 : ℂ) + σ) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall
      fun σ (hσ : 0 < σ) => ?_⟩
    · have h : Tendsto (fun σ : ℝ => (1 : ℂ) + σ) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · show (1 : ℂ) + σ ∈ ({1} : Set ℂ)ᶜ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  refine (riemannZeta_residue_one.comp hmap).congr fun σ => ?_
  simp

/-- **The archimedean density caps the pole weight at the residue.**  If the Weil function with
pole weight `β` has a holomorphic continuation with nonnegative real part to `Re s > ½`, then
`β ≤ 1`. -/
theorem le_one_of_herglotz_poleWeightFunction {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) : β ≤ 1 := by
  have hWP := weilPositive_of_herglotz_poleWeightFunction hsl hΦd hΦre hΦ
  have hprod := (tendsto_mul_LSeries_lamC_of_herglotz hΦd hΦ).mul tendsto_mul_riemannZeta_one_add
  rw [mul_one] at hprod
  have hre : Tendsto (fun σ : ℝ => ((σ : ℂ) ^ 2 * LSeries (lamConv lam) σ).re) (𝓝[>] 0)
      (𝓝 β) := by
    have h := (Complex.continuous_re.tendsto _).comp hprod
    rw [Complex.ofReal_re] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun σ (hσ : 0 < σ) => ?_)
    simp only [Function.comp_apply]
    rw [LSeries_lamConv hsl hσ]
    ring_nf
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := weil_log_density_le hWP (ε := ε / 4) (by positivity)
  set K : ℝ := ∑ N ∈ Finset.range N₀, |logDensitySum lam N| with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : ∀ N : ℕ, N < N₀ → logDensitySum lam N ≤ K := fun N hN =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun N => |logDensitySum lam N|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hN))
  have hbound : ∀ σ : ℝ, 0 < σ →
      ((σ : ℂ) ^ 2 * LSeries (lamConv lam) σ).re ≤ σ ^ 2 * K + (1 + ε / 2) := by
    intro σ hσ
    have h := re_LSeries_lamConv_le hsl (c := 1 / 2 + ε / 4) (by positivity)
      (fun N hN => hN₀ N hN) hK hK0 hσ
    rw [show ((σ : ℂ) ^ 2) = ((σ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    calc σ ^ 2 * (LSeries (lamConv lam) σ).re
        ≤ σ ^ 2 * (K + 2 * (1 / 2 + ε / 4) / σ ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = σ ^ 2 * K + (1 + ε / 2) := by field_simp; ring
  have hrhs : Tendsto (fun σ : ℝ => σ ^ 2 * K + (1 + ε / 2)) (𝓝[>] 0) (𝓝 (1 + ε / 2)) := by
    have h : Tendsto (fun σ : ℝ => σ ^ 2 * K + (1 + ε / 2)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ 2 * K + (1 + ε / 2))) :=
      (((continuous_pow 2).mul continuous_const).add continuous_const).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto hre hrhs (eventually_nhdsWithin_of_forall hbound)
  linarith

/-- **Pole-weight rigidity for linear-deviation weights.**  If the Weil function with pole weight
`β` has a Herglotz continuation to `Re s > ½` and the weights deviate from `Λ` by linearly bounded
partial sums, then `β = 1`:
the archimedean density caps `β` at `1` and the twisted-arc null tests forbid `β < 1`. -/
theorem eq_one_of_herglotz_of_linearDeviation {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) {A : ℝ}
    (hA : ∀ N : ℕ, |WeilSpectral.primeWeightPartialSum
      (fun n => lam n - ArithmeticFunction.vonMangoldt n) N|
      ≤ A * (N + 1)) : β = 1 := by
  refine le_antisymm (le_one_of_herglotz_poleWeightFunction hsl hΦd hΦre hΦ) ?_
  by_contra hlt
  push Not at hlt
  exact not_forall_re_weilPoleWeightFunctional_nonneg hlt hA fun F hF hFc =>
    re_weilPoleWeightFunctional_nonneg_of_herglotz hsl hΦd hΦre hΦ hF
      (hFc.comp_left Complex.ofReal_zero)

/-! ### No Herglotz datum with nonpositive pole weight -/

/-- On the flat-top window test the pole-weight functional is `β·pole + archimedean energy`. -/
theorem re_weilPoleWeightFunctional_fejerTest (β : ℝ) (lam : ℕ → ℝ) :
    (weilPoleWeightFunctional β lam (EF.weilTest fejerTest fejerTest)).re =
      β * (paperFT (EF.weilTest fejerTest fejerTest) (I / 2) +
        paperFT (EF.weilTest fejerTest fejerTest) (-I / 2)).re +
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT fejerTest r‖ ^ 2 * EF.gammaBracket r := by
  obtain ⟨hfc, -, hks, -, -⟩ := weilTest_self_data contDiff_fejerTest tsupport_fejerTest
  set k := EF.weilTest fejerTest fejerTest with hk
  have hfcont : Continuous fejerTest := contDiff_fejerTest.continuous
  have hatoms : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    split_ifs with hn
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hl2 := Real.log_two_gt_d9
      have hout : ∀ y : ℝ, 34 / 50 < |y| → k y = 0 := fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hmem => by
          have := hks hmem
          rw [mem_Icc] at this
          have : |y| ≤ 2 * (17 / 50) := abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
          linarith
      have h1 : k (Real.log n) = 0 := hout _ (by rw [abs_of_pos (by linarith)]; linarith)
      have h2 : k (-Real.log n) = 0 :=
        hout _ (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      rw [h1, h2, add_zero, mul_zero]
    · simp
  have hint : (∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ‖paperFT fejerTest r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hk]
    rw [EF.paperFT_weilTest hfcont hfcont hfc hfc, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  unfold weilPoleWeightFunctional weilFullFunctional
  rw [hatoms, hint]
  simp only [Complex.add_re, sub_zero,
    show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  rw [show ((1 / (2 * Real.pi) : ℂ) *
      ((∫ r : ℝ, ‖paperFT fejerTest r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ)) =
      (((1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT fejerTest r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) by
    push_cast; ring, Complex.ofReal_re]
  ring

theorem gammaBracket_eq_archimedeanWeilSymbol (r : ℝ) :
    EF.gammaBracket r = archimedeanWeilSymbol (r / (2 * Real.pi)) := by
  rw [archimedeanWeilSymbol_eq, EF.gammaBracket]
  congr 3
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **A Herglotz datum has positive pole weight.**  On the flat-top window test (support inside
`(−log 2/2, log 2/2)`, no atoms) the functional is `β·pole + archimedean energy`, the pole is
nonnegative and the archimedean energy is negative. -/
theorem pos_of_herglotz_poleWeightFunction {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) : 0 < β := by
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data contDiff_fejerTest tsupport_fejerTest
  have hpos := re_weilPoleWeightFunctional_nonneg_of_herglotz hsl hΦd hΦre hΦ contDiff_fejerTest
    hfc
  rw [re_weilPoleWeightFunctional_fejerTest] at hpos
  have hF : Continuous (flatBump (17 / 50) (17 / 1000)) := (contDiff_flatBump _ _).continuous
  have hFc : HasCompactSupport (flatBump (17 / 50) (17 / 1000)) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      have h := image_eq_zero_of_notMem_tsupport (f := fejerTest)
        (fun h => hx (tsupport_fejerTest h))
      simpa [fejerTest] using h
  have hpole := re_pole_weilTest_ofReal hF hFc
  have hpole0 : 0 ≤ (paperFT (EF.weilTest fejerTest fejerTest) (I / 2) +
      paperFT (EF.weilTest fejerTest fejerTest) (-I / 2)).re := by
    have e : fejerTest = fun u => ((flatBump (17 / 50) (17 / 1000) u : ℝ) : ℂ) := rfl
    rw [e, hpole]
    have h1 : 0 ≤ ∫ u, flatBump (17 / 50) (17 / 1000) u * Real.exp (-u / 2) :=
      integral_nonneg fun u => mul_nonneg (flatBump_nonneg u) (Real.exp_pos _).le
    have h2 : 0 ≤ ∫ u, flatBump (17 / 50) (17 / 1000) u * Real.exp (u / 2) :=
      integral_nonneg fun u => mul_nonneg (flatBump_nonneg u) (Real.exp_pos _).le
    positivity
  have harch := integral_normSq_paperFT_fejerTest_mul_arch_neg
  have heq : (∫ r : ℝ, ‖paperFT fejerTest r‖ ^ 2 * EF.gammaBracket r) =
      ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * Real.pi)) :=
    integral_congr_ae (Eventually.of_forall fun r => by
      simp only [gammaBracket_eq_archimedeanWeilSymbol])
  rw [heq] at hpos
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  by_contra hβ
  push Not at hβ
  have : β * (paperFT (EF.weilTest fejerTest fejerTest) (I / 2) +
      paperFT (EF.weilTest fejerTest fejerTest) (-I / 2)).re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hβ hpole0
  nlinarith [mul_neg_of_pos_of_neg hpi harch]

/-! ### Linear deviation is automatic, and the pole weight is the residue -/

theorem archPart_eq_zetaArchimedeanDatum (s : ℂ) :
    RelaxedHerglotz.archPart s = zetaArchimedeanDatum s + 1 / (s - 1) := by
  unfold RelaxedHerglotz.archPart zetaArchimedeanDatum
  ring

/-- The rescaled archimedean datum `(Γ̃(s) + (β − 1)/s)/β`. -/
def scaledDatum (β : ℝ) (s : ℂ) : ℂ := (zetaArchimedeanDatum s + ((β : ℂ) - 1) / s) / β

theorem LSeries_div_real (lam : ℕ → ℝ) {β : ℝ} (s : ℂ) :
    LSeries (fun n => ((((if 2 ≤ n then lam n else 0) / β : ℝ)) : ℂ)) s =
      LSeries (WeilHerglotz.lamC lam) s / β := by
  unfold LSeries
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, WeilHerglotz.lamC]
  push_cast
  ring

/-- **Rescaling a datum with pole weight `β > 0`** to the residue-one Herglotz form. -/
theorem herglotzWeilPositive_scaled {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} (hβ : 0 < β)
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) :
    HerglotzWeilPositive (fun n => (if 2 ≤ n then lam n else 0) / β) (scaledDatum β) where
  summable σ hσ := by
    refine ((hsl σ hσ).div_const β).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    rw [abs_div, abs_of_pos hβ]
    have hn : (0 : ℝ) ≤ (n : ℝ) ^ σ := by positivity
    rw [div_div, div_div, mul_comm]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    split_ifs <;> simp
  herglotz := by
    have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
    refine ⟨fun s => Φ s / β, hΦd.div_const _, fun s hs => ?_, fun s hs => ?_⟩
    · show 0 ≤ (Φ s / (β : ℂ)).re
      rw [Complex.div_ofReal_re]
      exact div_nonneg (hΦre s hs) hβ.le
    · have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
      have hs1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      show Φ s / β = scaledDatum β s + 1 / (s - 1) - LSeries _ s
      rw [LSeries_div_real, hΦ s hs, poleWeightFunction,
        RelaxedHerglotz.weilFunction_eq_archPart_sub, archPart_eq_zetaArchimedeanDatum, scaledDatum,
        gPair]
      simp only [sub_zero]
      field_simp
      ring

theorem differentiableOn_scaledDatum (β : ℝ) :
    DifferentiableOn ℂ (scaledDatum β) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := fun h => by
    have : (1 : ℝ) / 2 < s.re := hs
    rw [h, Complex.zero_re] at this; linarith
  have hz : DifferentiableAt ℂ zetaArchimedeanDatum s :=
    differentiableOn_zetaArchimedeanDatum.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 0 < s.re by have : (1 : ℝ) / 2 < s.re := hs; linarith))
  exact ((hz.add ((differentiableAt_const _).div differentiableAt_id hs0)).div_const
    _).differentiableWithinAt

theorem exists_log_bound_scaledDatum {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 →
      ‖scaledDatum β s‖ ≤ K * Real.log (|s.im| + 3) := by
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  refine ⟨(K + 2 * |β - 1|) / β, by positivity, fun s hs hs2 => ?_⟩
  have hlog : 1 ≤ Real.log (|s.im| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg s.im]
  have hsn : 1 / 2 ≤ ‖s‖ := hs.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have hfrac : ‖((β : ℂ) - 1) / s‖ ≤ 2 * |β - 1| := by
    rw [norm_div, show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (β - 1)]
  unfold scaledDatum
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ,
    div_le_iff₀ hβ]
  calc ‖zetaArchimedeanDatum s + ((β : ℂ) - 1) / s‖ ≤ K * Real.log (|s.im| + 3) + 2 * |β - 1| :=
        (norm_add_le _ _).trans (add_le_add (hAK s hs hs2) hfrac)
    _ ≤ (K + 2 * |β - 1|) * Real.log (|s.im| + 3) := by
        nlinarith [abs_nonneg (β - 1)]
    _ = (K + 2 * |β - 1|) / β * Real.log (|s.im| + 3) * β := by field_simp

/-- **The deviation from `Λ` has linearly bounded partial sums** for every Herglotz datum with
positive pole weight: the rescaled summatory law gives `Σ_{n ≤ N} lam(n) = βN + O(N)`. -/
theorem exists_abs_primeWeightPartialSum_sub_le_of_herglotz {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} (hβ : 0 < β)
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) :
    ∃ A : ℝ, ∀ N : ℕ, |WeilSpectral.primeWeightPartialSum
      (fun n => lam n - ArithmeticFunction.vonMangoldt n) N| ≤ A * (N + 1) := by
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_scaledDatum hβ
  obtain ⟨C, hC, hS⟩ := WeilSingularArithmetic.exists_sharp_source_sum_le_of_herglotz
    (herglotzWeilPositive_scaled hsl hβ hΦd hΦre hΦ) (differentiableOn_scaledDatum β) hK hAK
    (by simp) (ε := 1 / 2) (by norm_num)
  refine ⟨β * C + β + 8, fun N => ?_⟩
  have h1 := hS N
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] at h1
  set T : ℝ := ∑ n ∈ Finset.range (N + 1), (if 2 ≤ n then lam n else 0) with hT
  have hc : (∑ n ∈ Finset.range (N + 1),
      ((((if 2 ≤ n then lam n else 0) / β : ℝ)) : ℂ)) - (N : ℂ) = ((T / β - N : ℝ) : ℂ) := by
    rw [hT, Finset.sum_div]
    push_cast
    ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h1
  have hT' : |T - β * N| ≤ β * C * (N + 1) := by
    have e : T - β * N = β * (T / β - N) := by field_simp
    rw [e, abs_mul, abs_of_pos hβ]
    have := mul_le_mul_of_nonneg_left h1 hβ.le
    linarith
  have hsplit : WeilSpectral.primeWeightPartialSum
      (fun n => lam n - ArithmeticFunction.vonMangoldt n) N =
      T - ∑ m ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt m := by
    unfold WeilSpectral.primeWeightPartialSum
    rw [hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rfl
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> simp
  have hpsi := RHTower.sum_range_vonMangoldt_eq_chebyshevPsi N
  have hpsi7 := RHTower.chebyshevPsi_le_seven N
  have hpsi0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt m :=
    Finset.sum_nonneg fun m _ => ArithmeticFunction.vonMangoldt_nonneg
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hsplit, abs_le]
  have := abs_le.mp hT'
  constructor <;> nlinarith

/-- **The pole weight of a Herglotz datum is the residue of `ζ`.**  If the Weil function with pole
weight `β` has a holomorphic continuation with nonnegative real part to `Re s > ½`, then `β = 1`.
No hypothesis on the weights beyond the absolute convergence of their Dirichlet series. -/
theorem eq_one_of_herglotz_poleWeightFunction {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {β : ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = poleWeightFunction β lam s) : β = 1 := by
  have hβ := pos_of_herglotz_poleWeightFunction hsl hΦd hΦre hΦ
  obtain ⟨A, hA⟩ := exists_abs_primeWeightPartialSum_sub_le_of_herglotz hsl hβ hΦd hΦre hΦ
  exact eq_one_of_herglotz_of_linearDeviation hsl hΦd hΦre hΦ hA

end RHTower.WeilPoleWeight
