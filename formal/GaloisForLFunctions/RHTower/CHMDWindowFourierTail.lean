import GaloisForLFunctions.RHTower.CHMDLevySymbolLowerBound
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding

/-!
# The archimedean Lévy form controls high frequencies

For a compactly supported `C²` function `g`, the archimedean Lévy jump form
`Q(g) = ∫_0^∞ ω(x) ∫ (g(u) − g(u+x))² du dx` equals `(1/2π) ∫ |ĝ(r)|² (γ(r) − γ(0)) dr`
(Lévy–Khintchine plus Plancherel). Since the Lévy symbol `γ(r) − γ(0)` is nonnegative and at least
`log(T/2) − levyConst` on `|r| ≥ T`, the Fourier mass of `g` above frequency `T` is at most
`2π Q(g) / (log(T/2) − levyConst)`: a bound on the Lévy form forces a uniform high-frequency tail.
-/

open MeasureTheory Set Filter Topology Zeta23
noncomputable section
namespace RHTower.CHMDPolar

/-- The archimedean Lévy jump form of a real function. -/
def levyForm (g : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2

/-- The squared modulus of the Fourier transform of a real function at a real frequency. -/
def fourierSq (g : ℝ → ℝ) (r : ℝ) : ℝ := ‖paperFT (fun u => (g u : ℂ)) (r : ℂ)‖ ^ 2

theorem fourierSq_nonneg (g : ℝ → ℝ) (r : ℝ) : 0 ≤ fourierSq g r := sq_nonneg _

theorem continuous_fourierSq {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fourierSq g) := by
  have hint : Integrable fun u => (g u : ℂ) :=
    (Complex.continuous_ofReal.comp hg).integrable_of_hasCompactSupport
      (hgc.comp_left Complex.ofReal_zero)
  exact (WeilHerglotz.continuous_paperFT_real hint).norm.pow 2

theorem exists_fourierSq_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ r, fourierSq g r ≤ N ^ 2 / ((1 + |r|) ^ 2) ^ 2 :=
  exists_normSq_paperFT_le hg hgc

theorem integrable_one_add_abs_pow_three :
    Integrable fun r : ℝ => ((1 + |r|) ^ 3)⁻¹ := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by
    rw [Module.finrank_self]
    norm_num)
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [Real.norm_eq_abs]
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- The Fourier side of the Lévy–Khintchine identity is integrable for `C²` compact tests. -/
theorem integrable_fourierSq_mul_gammaBracket {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Integrable fun r => fourierSq g r * EF.gammaBracket r := by
  obtain ⟨N, hN0, hN⟩ := exists_fourierSq_le hg hgc
  set K : ℝ := |EvenSector.gammaLogConst| + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine (integrable_one_add_abs_pow_three.const_mul (N ^ 2 * K)).mono'
    ((continuous_fourierSq hg.continuous hgc).mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fourierSq_nonneg g r)]
  have h1 := hN r
  have h2 := EvenSector.abs_gammaBracket_le_log r
  have h3 : Real.log (2 + |r|) ≤ 1 + |r| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |r|)
    linarith
  have h4 : |EF.gammaBracket r| ≤ K * (1 + |r|) := by
    have h6 := le_abs_self EvenSector.gammaLogConst
    have h5 : 0 ≤ |r| := abs_nonneg r
    have h7 : 0 ≤ |EvenSector.gammaLogConst| * |r| := mul_nonneg (abs_nonneg _) h5
    rw [hK]
    nlinarith
  have hpos : 0 < 1 + |r| := by positivity
  calc fourierSq g r * |EF.gammaBracket r|
      ≤ N ^ 2 / ((1 + |r|) ^ 2) ^ 2 * (K * (1 + |r|)) :=
        mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
    _ = N ^ 2 * K * ((1 + |r|) ^ 3)⁻¹ := by
        rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
        field_simp

theorem integrable_fourierSq {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Integrable (fourierSq g) := by
  obtain ⟨N, hN0, hN⟩ := exists_fourierSq_le hg hgc
  refine (integrable_one_add_abs_pow_three.const_mul (N ^ 2)).mono'
    (continuous_fourierSq hg.continuous hgc).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fourierSq_nonneg g r)]
  refine (hN r).trans ?_
  have hpos : 0 < 1 + |r| := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc N ^ 2 = N ^ 2 * ((1 + |r|) ^ 3)⁻¹ * (1 + |r|) ^ 3 := by field_simp
    _ ≤ N ^ 2 * ((1 + |r|) ^ 3)⁻¹ * ((1 + |r|) ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 : 1 ≤ 1 + |r| := by linarith [abs_nonneg r]
        calc (1 + |r|) ^ 3 = (1 + |r|) ^ 3 * 1 := (mul_one _).symm
          _ ≤ (1 + |r|) ^ 3 * (1 + |r|) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ((1 + |r|) ^ 2) ^ 2 := by ring

theorem integrable_fourierSq_mul_levySymbol {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Integrable fun r => fourierSq g r * levySymbol r := by
  have h := (integrable_fourierSq_mul_gammaBracket hg hgc).sub
    ((integrable_fourierSq hg hgc).mul_const (EF.gammaBracket 0))
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.sub_apply, levySymbol]
  ring

/-- A compactly supported function vanishes outside a symmetric interval. -/
theorem exists_support_radius {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, g x ≠ 0 → -a ≤ x ∧ x ≤ a := by
  obtain ⟨a, ha0, ha⟩ := hgc.exists_pos_le_norm
  refine ⟨a, ha0, fun x hx => ?_⟩
  by_contra h
  apply hx
  apply ha
  rw [Real.norm_eq_abs]
  by_contra h'
  rw [not_le] at h'
  exact h ⟨(abs_lt.mp h').1.le, (abs_lt.mp h').2.le⟩

theorem tsupport_ofReal_subset {g : ℝ → ℝ} {a : ℝ} (hsupp : ∀ x, g x ≠ 0 → -a ≤ x ∧ x ≤ a) :
    tsupport (fun u => (g u : ℂ)) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have : g u ≠ 0 := by
    intro h
    apply hu
    simp [h]
  exact hsupp u this

/-- Plancherel for compactly supported `C²` real functions. -/
theorem integral_fourierSq_eq {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∫ r, fourierSq g r = 2 * Real.pi * ∫ u, g u ^ 2 := by
  obtain ⟨a, _, hsupp⟩ := exists_support_radius hgc
  have hf : ContDiff ℝ 2 fun u => (g u : ℂ) := Complex.ofRealCLM.contDiff.comp hg
  have h := integral_norm_sq_paperFT_eq hf (tsupport_ofReal_subset hsupp)
  unfold fourierSq
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Lévy–Khintchine with Plancherel**: `(1/2π) ∫ |ĝ|² (γ − γ(0)) = Q(g)`, together with the
integrability of the jump integrand. -/
theorem levyForm_eq_fourier {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x => archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2) (Ioi 0) ∧
      (1 / (2 * Real.pi)) * (∫ r, fourierSq g r * levySymbol r) = levyForm g := by
  have hgC := hg.continuous
  have hg1 : Integrable g := hgC.integrable_of_hasCompactSupport hgc
  have hgc2 : HasCompactSupport fun u => g u ^ 2 := by
    have h := hgc.mul_left (f := g)
    have he : (fun u => g u ^ 2) = g * g := by
      funext u
      simp [pow_two]
    rw [he]
    exact h
  have hg2 : Integrable fun u => g u ^ 2 := (hgC.pow 2).integrable_of_hasCompactSupport hgc2
  have hintR := integrable_fourierSq_mul_gammaBracket hg hgc
  unfold fourierSq at hintR
  obtain ⟨hint, heq⟩ := integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hgC hg1 hg2 hintR
  refine ⟨hint, ?_⟩
  have hsplit : (∫ r, fourierSq g r * levySymbol r) =
      (∫ r, fourierSq g r * EF.gammaBracket r) - (∫ r, fourierSq g r) * EF.gammaBracket 0 := by
    rw [← integral_mul_const, ← integral_sub (integrable_fourierSq_mul_gammaBracket hg hgc)
      ((integrable_fourierSq hg hgc).mul_const _)]
    congr 1
    funext r
    simp only [levySymbol]
    ring
  rw [hsplit, integral_fourierSq_eq hg hgc, mul_sub]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq' : (1 / (2 * Real.pi)) * (∫ r, fourierSq g r * EF.gammaBracket r) =
      EF.gammaBracket 0 * (∫ u, g u ^ 2) + levyForm g := by
    unfold fourierSq levyForm
    exact heq
  have h2π : (1 / (2 * Real.pi)) * (2 * Real.pi) = 1 := by
    field_simp
  linear_combination heq' - ((∫ u, g u ^ 2) * EF.gammaBracket 0) * h2π

theorem levyForm_nonneg {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    0 ≤ levyForm g := by
  rw [← (levyForm_eq_fourier hg hgc).2]
  exact mul_nonneg (by positivity) (integral_nonneg fun r =>
    mul_nonneg (fourierSq_nonneg g r) (levySymbol_nonneg r))

/-- The high-frequency set. -/
def highFreq (T : ℝ) : Set ℝ := {r | T ≤ |r|}

theorem measurableSet_highFreq (T : ℝ) : MeasurableSet (highFreq T) :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- **Uniform high-frequency tail**: `(log(T/2) − levyConst) ∫_{|r| ≥ T} |ĝ|² ≤ 2π Q(g)`. -/
theorem fourier_tail_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {T : ℝ}
    (hT : 4 ≤ T) :
    (Real.log (T / 2) - levyConst) * ∫ r in highFreq T, fourierSq g r ≤ 2 * Real.pi * levyForm g := by
  have hint := integrable_fourierSq_mul_levySymbol hg hgc
  have h1 : (Real.log (T / 2) - levyConst) * ∫ r in highFreq T, fourierSq g r ≤
      ∫ r in highFreq T, fourierSq g r * levySymbol r := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((integrable_fourierSq hg hgc).const_mul _).integrableOn
      hint.integrableOn (measurableSet_highFreq T) fun r hr => ?_
    have hr' : T ≤ |r| := hr
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (levySymbol_ge_log_of_le hT hr') (fourierSq_nonneg g r)
  have h2 : (∫ r in highFreq T, fourierSq g r * levySymbol r) ≤ ∫ r, fourierSq g r * levySymbol r :=
    setIntegral_le_integral hint (Eventually.of_forall fun r =>
      mul_nonneg (fourierSq_nonneg g r) (levySymbol_nonneg r))
  have h3 := (levyForm_eq_fourier hg hgc).2
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [one_div_mul_eq_div, div_eq_iff (by positivity)] at h3
  linarith

end RHTower.CHMDPolar
