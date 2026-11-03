import GaloisForLFunctions.SignedWindowCriticality.NoMarkovGroundStateOnAWindowLongerThanTheDeathWidth
import GaloisForLFunctions.ArithmeticCriticalityTheory.OddSupersolutionCriterion

/-!
# The folded criterion is void on the unit window

ACT's folded supersolution criterion (`riemannHypothesis_of_foldedSupersolution`) asks for `ω ≥ 0`
on the half-line with `𝓛_N ω ≥ Φ cosh(x/2) ω`, where `𝓛_N` is the folded (Neumann) generator.
Review-0311 §2.8 asks for such an `ω` on the unit odd window `(0, ½]` with the prime-2 jump kept.

* **The folded generator is two-sided on the even extension**
  (`foldedGenerator_eq_twoSidedGenerator_abs`): for `x ≥ 0`, `𝓛_N ω(x) = 𝓛_D(ω ∘ |·|)(x)`; the
  folded generator reads `ω` only on `[0, ∞)`.
* **Lowering a gauge away from a point raises its generator there**
  (`twoSidedGenerator_le_of_le_of_eqOn`): if `ν ≤ ω` everywhere and `ν = ω` near `x`, then
  `𝓛_D ω(x) ≤ 𝓛_D ν(x)`, every jump rate being nonnegative.
* **No-go** (`not_exists_foldedWindowSupersolution`). For `a > e^{−3/4}` no `C²_c` function `ω`,
  nonnegative on `[0, ∞)` and positive on `(0, a)`, satisfies the folded supersolution inequality on
  `(0, a)`. Cutting `ω` off near `0` and near `a` gives a two-sided Markov supersolution on an interval
  longer than `e^{−3/4}`, which `NoMarkovGroundStateOnAWindowLongerThanTheDeathWidth` excludes.
  In particular the unit odd window `(0, ½)` admits none (`not_exists_foldedWindowSupersolution_half`).

Parity of `ω` plays no role: the folded criterion certifies only the Markov part, and on the
unit window the Markov part is already indefinite on tests inside `(0, ½)`. A certificate of the
first prime stage must keep the pole (`ThePoleChargesTheSupersolution`).
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

theorem foldedShiftGenerator_eq_twoSidedShiftGenerator_abs (ω : ℝ → ℝ) {t x : ℝ} (ht : 0 ≤ t)
    (hx : 0 ≤ x) :
    foldedShiftGenerator ω t x = twoSidedShiftGenerator (fun y => ω |y|) t x := by
  unfold foldedShiftGenerator twoSidedShiftGenerator
  simp only [abs_of_nonneg hx, abs_of_nonneg (show 0 ≤ x + t by linarith)]

/-- The folded generator at `x ≥ 0` is the two-sided generator of the even extension. -/
theorem foldedGenerator_eq_twoSidedGenerator_abs (ω : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    foldedGenerator ω x = twoSidedGenerator (fun y => ω |y|) x := by
  unfold foldedGenerator twoSidedGenerator
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [foldedShiftGenerator_eq_twoSidedShiftGenerator_abs ω (le_of_lt ht) hx]
  · exact tsum_congr fun n => by
      rw [foldedShiftGenerator_eq_twoSidedShiftGenerator_abs ω (Real.log_natCast_nonneg n) hx]

/-- **Comparison.** If `ν ≤ ω` everywhere and `ν = ω` on a neighbourhood of `x`, with `ν ∈ C²_c` and
`ω − ν` bounded and continuous, then `𝓛_D ω(x) ≤ 𝓛_D ν(x)`. -/
theorem twoSidedGenerator_le_of_le_of_eqOn {ω ν : ℝ → ℝ} (hν : ContDiff ℝ 2 ν)
    (hνc : HasCompactSupport ν) (hω : Continuous ω) {Z : ℝ} (hZ : ∀ y, |ω y - ν y| ≤ Z)
    (hle : ∀ y, ν y ≤ ω y) {x η : ℝ} (hη : 0 < η) (heq : ∀ y ∈ Ioo (x - η) (x + η), ν y = ω y) :
    twoSidedGenerator ω x ≤ twoSidedGenerator ν x := by
  set d : ℝ → ℝ := fun y => ω y - ν y with hd
  have hd0 : ∀ y, 0 ≤ d y := fun y => sub_nonneg.mpr (hle y)
  have hdx : ∀ y ∈ Ioo (x - η) (x + η), d y = 0 := fun y hy => by simp [hd, heq y hy]
  have hdxx : d x = 0 := hdx x ⟨by linarith, by linarith⟩
  have hdc : Continuous d := hω.sub hν.continuous
  have hsplit : ∀ t, twoSidedShiftGenerator ω t x =
      twoSidedShiftGenerator ν t x + twoSidedShiftGenerator d t x := fun t => by
    rw [← twoSidedShiftGenerator_add]
    congr 1
    funext y; simp [hd]
  have hgen : ∀ t, twoSidedShiftGenerator d t x =
      -(riemannKernelReal x * (riemannKernelReal (x + t) * d (x + t) +
        riemannKernelReal (x - t) * d (x - t))) := fun t => by
    unfold twoSidedShiftGenerator; rw [hdxx]; ring
  have hgen_nonpos : ∀ t, twoSidedShiftGenerator d t x ≤ 0 := fun t => by
    rw [hgen t]
    have h1 := riemannKernelReal_pos x
    have h2 := riemannKernelReal_pos (x + t)
    have h3 := riemannKernelReal_pos (x - t)
    have h4 := hd0 (x + t)
    have h5 := hd0 (x - t)
    have : 0 ≤ riemannKernelReal x * (riemannKernelReal (x + t) * d (x + t) +
        riemannKernelReal (x - t) * d (x - t)) := by positivity
    linarith
  have hgen_zero : ∀ t, 0 ≤ t → t < η → twoSidedShiftGenerator d t x = 0 := fun t ht0 htη => by
    rw [hgen t, hdx (x + t) ⟨by linarith, by linarith⟩, hdx (x - t) ⟨by linarith, by linarith⟩]
    ring
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ 0)
  have hΦ0 := riemannKernelReal_pos 0
  -- the archimedean part of `d` is integrable: it vanishes below `η`
  have hη2 : 0 < η / 2 := by linarith
  have hfar : IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator d t x)
      (Ioi (η / 2)) := by
    refine ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hη2).const_mul
      (2 * Z * riemannKernelReal 0 * (2 * riemannKernelReal 0))).mono'
      ((measurable_archLevyDensity.mul ((continuous_twoSidedShiftGenerator_uncurry hdc).comp
        (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans hη2 ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht0)]
    have hb := abs_twoSidedShiftGenerator_le_kernel hZ t x
    have h1 := riemannKernelReal_le_zero_point (x + t)
    have h2 := riemannKernelReal_le_zero_point (x - t)
    have hk : 2 * Z * riemannKernelReal 0 * (riemannKernelReal (x + t) +
        riemannKernelReal (x - t)) ≤ 2 * Z * riemannKernelReal 0 * (2 * riemannKernelReal 0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hA := (archLevyDensity_pos ht0).le
    nlinarith [mul_le_mul_of_nonneg_left (hb.trans hk) hA]
  have hnear : IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator d t x)
      (Ioc 0 (η / 2)) := by
    refine (integrableOn_zero (s := Ioc (0 : ℝ) (η / 2)) (μ := volume)).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    simp only
    rw [hgen_zero t (le_of_lt ht.1) (by linarith [ht.2]), mul_zero]
  have hAd : IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator d t x) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hη2.le]
    exact hnear.union hfar
  have hAν := integrableOn_archLevy_twoSidedShiftGenerator_of_contDiff hν hνc x
  have hArch : (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator ω t x) ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator ν t x := by
    have heqi : (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator ω t x) =
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator ν t x) +
          ∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator d t x := by
      rw [← integral_add hAν hAd]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [hsplit t]; ring
    have hneg : (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator d t x) ≤ 0 :=
      setIntegral_nonpos measurableSet_Ioi fun t ht =>
        mul_nonpos_of_nonneg_of_nonpos (archLevyDensity_pos ht).le (hgen_nonpos t)
    linarith
  obtain ⟨Zν, hZν⟩ := hνc.exists_bound_of_continuous hν.continuous
  have hZν' : ∀ y, |ν y| ≤ Zν := fun y => by simpa [Real.norm_eq_abs] using hZν y
  have hPν := summable_atom_twoSidedShiftGenerator hZν' x
  have hPd := summable_atom_twoSidedShiftGenerator hZ x
  have hPrime : (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x) ≤
      ∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator ν (Real.log n) x := by
    have heqs : (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x) =
        (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator ν (Real.log n) x) +
          ∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator d (Real.log n) x := by
      rw [← hPν.tsum_add hPd]
      exact tsum_congr fun n => by rw [hsplit]; ring
    have hneg : (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator d (Real.log n) x) ≤ 0 :=
      tsum_nonpos fun n =>
        mul_nonpos_of_nonneg_of_nonpos (vonMangoldtAtom_nonneg n) (hgen_nonpos _)
    linarith
  unfold twoSidedGenerator
  linarith

/-- **No folded window supersolution past `e^{−3/4}`.** For `a > e^{−3/4}` no `C²_c` function,
nonnegative on `[0, ∞)` and positive on `(0, a)`, is a supersolution of ACT's folded generator on
`(0, a)`. -/
theorem not_exists_foldedWindowSupersolution {a : ℝ} (ha : markovDeathWidth < a) :
    ¬ ∃ ω : ℝ → ℝ, ContDiff ℝ 2 ω ∧ HasCompactSupport ω ∧ (∀ x, 0 ≤ x → 0 ≤ ω x) ∧
      (∀ x ∈ Ioo 0 a, 0 < ω x) ∧
      ∀ x ∈ Ioo 0 a, riemannKernelReal x * Real.cosh (x / 2) * ω x ≤ foldedGenerator ω x := by
  rintro ⟨ω, hω, hωc, hω0, hωpos, hsuper⟩
  set w := markovDeathWidth with hw
  have hw0 : 0 < w := markovDeathWidth_pos
  set ε := a - w with hε
  have hε0 : 0 < ε := by linarith
  set α := ε / 8
  set L := a - ε / 4
  have hL0 : 0 < L := by simp only [L]; linarith
  set η := ε / (8 * L)
  have hη0 : 0 < η := by positivity
  have hηL : η * L = ε / 8 := by simp only [η]; field_simp
  -- the cut-off `χ(y) = plateau((y − α)/L)`, equal to one on `[ε/4, a − ε/4]`
  set χ : ℝ → ℝ := fun y => SpacingScaleHarmonicAnalysis.plateau η ((y - α) / L)
  have hχc : ContDiff ℝ 2 χ :=
    (SpacingScaleHarmonicAnalysis.contDiff_plateau η).comp
      ((contDiff_id.sub contDiff_const).div_const L)
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => SpacingScaleHarmonicAnalysis.plateau_nonneg _
  have hχ1 : ∀ y, χ y ≤ 1 := fun y => SpacingScaleHarmonicAnalysis.plateau_le_one _
  have hχout : ∀ y, y ∉ Icc α (α + L) → χ y = 0 := by
    intro y hy
    refine SpacingScaleHarmonicAnalysis.plateau_eq_zero hη0 fun h => hy ⟨?_, ?_⟩
    · have := h.1; rw [le_div_iff₀ hL0] at this; linarith
    · have := h.2; rw [div_le_iff₀ hL0] at this; linarith
  have hχin : ∀ y ∈ Icc (ε / 4) (a - ε / 4), χ y = 1 := by
    intro y hy
    refine SpacingScaleHarmonicAnalysis.plateau_eq_one hη0 ⟨?_, ?_⟩
    · rw [le_div_iff₀ hL0]
      have := hy.1
      simp only [α]
      linarith [hηL]
    · rw [div_le_iff₀ hL0]
      have := hy.2
      have h1 : (1 - η) * L = L - ε / 8 := by rw [sub_mul, one_mul, hηL]
      have hLd : L = a - ε / 4 := rfl
      simp only [α]
      linarith
  set ν : ℝ → ℝ := fun y => χ y * ω y
  have hνc : ContDiff ℝ 2 ν := hχc.mul hω
  have hνout : ∀ y, y ∉ Icc α (α + L) → ν y = 0 := fun y hy => by simp [ν, hχout y hy]
  have hνcs : HasCompactSupport ν :=
    HasCompactSupport.intro (isCompact_Icc (a := α) (b := α + L)) hνout
  have hα0 : 0 < α := by simp only [α]; linarith
  have hν0 : ∀ y, 0 ≤ ν y := by
    intro y
    by_cases hy : y ∈ Icc α (α + L)
    · exact mul_nonneg (hχ0 y) (hω0 y (by linarith [hy.1]))
    · rw [hνout y hy]
  set ωe : ℝ → ℝ := fun y => ω |y|
  have hωe : Continuous ωe := hω.continuous.comp continuous_abs
  have hνle : ∀ y, ν y ≤ ωe y := by
    intro y
    by_cases hy : y ∈ Icc α (α + L)
    · have hy0 : 0 ≤ y := by linarith [hy.1]
      simp only [ν, ωe, abs_of_nonneg hy0]
      have := hω0 y hy0
      nlinarith [hχ1 y]
    · rw [hνout y hy]; exact hω0 _ (abs_nonneg y)
  obtain ⟨Zω, hZω⟩ := hωc.exists_bound_of_continuous hω.continuous
  have hZω' : ∀ y, |ω y| ≤ Zω := fun y => by simpa [Real.norm_eq_abs] using hZω y
  have hZ : ∀ y, |ωe y - ν y| ≤ 2 * Zω := by
    intro y
    have h1 : |ν y| ≤ |ω y| := by
      simp only [ν]; rw [abs_mul, abs_of_nonneg (hχ0 y)]
      nlinarith [hχ1 y, abs_nonneg (ω y)]
    have h2 := hZω' |y|
    have h3 := hZω' y
    calc |ωe y - ν y| ≤ |ωe y| + |ν y| := abs_sub _ _
      _ ≤ 2 * Zω := by simp only [ωe]; linarith
  -- the cut-off gauge is a two-sided Markov supersolution on `(ε/4, a − ε/4)`
  have hsub : ∀ x ∈ Ioo (ε / 4) (a - ε / 4),
      riemannKernelReal x * Real.cosh (x / 2) * ν x ≤ twoSidedGenerator ν x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxa : x ∈ Ioo 0 a := ⟨hx0, by linarith [hx.2]⟩
    have hνx : ν x = ω x := by simp [ν, hχin x ⟨hx.1.le, hx.2.le⟩]
    set η' := min (x - ε / 4) (a - ε / 4 - x)
    have hη' : 0 < η' := lt_min (by linarith [hx.1]) (by linarith [hx.2])
    have heq : ∀ y ∈ Ioo (x - η') (x + η'), ν y = ωe y := by
      intro y hy
      have h1 : x - ε / 4 ≥ η' := min_le_left _ _
      have h2 : a - ε / 4 - x ≥ η' := min_le_right _ _
      have hy1 : ε / 4 ≤ y := by linarith [hy.1]
      have hy2 : y ≤ a - ε / 4 := by linarith [hy.2]
      have hy0 : 0 ≤ y := by linarith
      simp only [ν, ωe, hχin y ⟨hy1, hy2⟩, one_mul, abs_of_nonneg hy0]
    have hcomp := twoSidedGenerator_le_of_le_of_eqOn hνc hνcs hωe hZ hνle hη' heq
    rw [← foldedGenerator_eq_twoSidedGenerator_abs ω hx0.le] at hcomp
    rw [hνx]
    exact (hsuper x hxa).trans hcomp
  have hpos : ∀ x ∈ Ioo (ε / 4) (a - ε / 4), 0 < ν x := by
    intro x hx
    have hνx : ν x = ω x := by simp [ν, hχin x ⟨hx.1.le, hx.2.le⟩]
    rw [hνx]
    exact hωpos x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlen : w < (a - ε / 4) - ε / 4 := by linarith
  exact not_exists_markovWindowSupersolution hlen ⟨ν, hνc, hνcs, hν0, hpos, hsub⟩

/-- **The one question, literal form: no.** The unit odd window `(0, ½)` carries no supersolution
of the folded generator. -/
theorem not_exists_foldedWindowSupersolution_half :
    ¬ ∃ ω : ℝ → ℝ, ContDiff ℝ 2 ω ∧ HasCompactSupport ω ∧ (∀ x, 0 ≤ x → 0 ≤ ω x) ∧
      (∀ x ∈ Ioo 0 (1 / 2 : ℝ), 0 < ω x) ∧
      ∀ x ∈ Ioo 0 (1 / 2 : ℝ),
        riemannKernelReal x * Real.cosh (x / 2) * ω x ≤ foldedGenerator ω x :=
  not_exists_foldedWindowSupersolution markovDeathWidth_lt_half

end GaloisForLFunctions.SignedWindowCriticality

end
