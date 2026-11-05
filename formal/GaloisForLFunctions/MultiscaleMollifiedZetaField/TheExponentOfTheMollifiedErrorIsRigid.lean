import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZeroForcesALogarithmicFloor
import GaloisForLFunctions.RHTower.MobiusWeightedLineEnergyExponentLaw
import GaloisForLFunctions.RHTower.ZetaCriticalLineWeightedSecondMoment
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# The exponent of the Möbius-mollified error is rigid

Write `E_X = ζ M_X − 1` on the critical line and `w = zetaZeroWidth`. Two bounds meet.

* **Cap.** `|E_X(½ + iu)| ≤ C_ε (1 + |u|)² X^{w+ε}` for all `X` and `u` (`exists_norm_lineError_le`): Abel summation with the increasing
  weight `n^{w+ε}` against the bounded Möbius sections on `Re s = ½ + w + ε`.
* **Floor.** A zero `ρ = ½ + δ + iγ` forces `∫ P_ρ log |E_X| ≥ δ log X − O_ρ(1)` (`TheZeroForcesALogarithmicFloor`).

A function under a cap whose mean nearly reaches the cap stays close to it in measure. So the `P_ρ`-mass of the set where
`|E_X| ≤ X^κ`, `κ < w`, is eventually at most `(w − δ)/(w − κ) + η` (`eventually_poissonMass_lowSet_le`).

**Consequences.**
* If the width is attained by a zero, then `|E_X| ≥ X^{κ}` on all but a vanishing part of every bounded window, for every `κ < w`
  (`tendsto_volume_lowSet_of_top_zero`).
* `zetaZeroWidth ≤ β` iff a uniform positive proportion of every window of length two has `|E_X| ≤ X^{β+ε}`, along arbitrarily large
  lengths that may depend on the window and on `ε` (`zetaZeroWidth_le_iff_positive_proportion`). At `β = 0` this is RH
  (`riemannHypothesis_iff_positive_proportion`). No moment and no height parameter enters.
* One moment of any order `p > 0` on every window, along sparse lengths, gives the same bound (`zetaZeroWidth_le_of_frequently_window_moment`).
* **Barrier immunity.** Restricting to a set `G`, even one depending on `X`, loses at most the small `P_ρ`-mass above:
  `X^{2κ} (P_ρ(G) − (w − δ)/(w − κ) − η) ≤ ∫_G P_ρ |E_X|²` eventually, uniformly in `G` (`eventually_restricted_secondMoment_ge`). So no
  restriction to a good event of positive `P_ρ`-mass lowers the slope `2w` when zeros approach the width.

These statements concern fixed height and growing length. They are RH equivalents or receivers and supply no bound on `M_X`.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_eq_zetaZeroAbscissa_sub_half zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### The cap -/

/-- Abel's inequality for an increasing nonnegative real weight. -/
theorem norm_sum_range_smul_le {a : ℕ → ℂ} {w : ℕ → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : Monotone w)
    {B : ℝ} (hB : ∀ k, ‖∑ i ∈ Finset.range k, a i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, w i • a i‖ ≤ 2 * w (n - 1) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Finset.sum_range_by_parts]
  have h1 : ‖w (n - 1) • ∑ i ∈ Finset.range n, a i‖ ≤ w (n - 1) * B := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 _)]
    exact mul_le_mul_of_nonneg_left (hB n) (hw0 _)
  have h2 : ‖∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ ≤
      w (n - 1) * B := by
    calc ‖∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖
        ≤ ∑ i ∈ Finset.range (n - 1),
            ‖(w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hd : 0 ≤ w (i + 1) - w i := sub_nonneg.mpr (hw (Nat.le_succ i))
          rw [norm_smul, Real.norm_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left (hB _) hd
      _ = (w (n - 1) - w 0) * B := by
          rw [← Finset.sum_mul, Finset.sum_range_sub]
      _ ≤ w (n - 1) * B := by
          have := hw0 0
          nlinarith
  calc _ ≤ ‖w (n - 1) • ∑ i ∈ Finset.range n, a i‖ +
        ‖∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ :=
        norm_sub_le _ _
    _ ≤ 2 * w (n - 1) * B := by linarith

/-- **The Möbius section on the critical line.** `|M_X(½ + iu)| ≤ 2 K (1 + |u|) X^{w+ε}`. -/
theorem exists_norm_moebiusPoly_line_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ℕ) (u : ℝ), 1 ≤ X →
      ‖moebiusPoly X (linePoint u)‖ ≤
        2 * (X : ℝ) ^ (zetaZeroWidth + ε) * (K * (1 + |u|)) := by
  have hw0 := zetaZeroWidth_nonneg
  have habs : _root_.RHTower.zetaZeroAbscissa = 1 / 2 + zetaZeroWidth := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    ring
  set r : ℝ := zetaZeroWidth + ε with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  set σ' : ℝ := 1 / 2 + r with hσ'
  have hσ : _root_.RHTower.zetaZeroAbscissa < σ' := by
    rw [habs, hσ', hr]
    linarith
  obtain ⟨K, hK0, hK⟩ := _root_.RHTower.exists_norm_edPoly_mobCoeff_line_le_of_zetaZeroAbscissa_lt hσ
  refine ⟨K, hK0, fun X u hX => ?_⟩
  set s : ℂ := (σ' : ℂ) + (u : ℂ) * I with hs
  set a : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) • _root_.RHTower.mobCoeff (i + 1) with ha
  set wt : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ r with hwt
  have hrep : moebiusPoly X (linePoint u) = ∑ i ∈ Finset.range X, wt i • a i := by
    show _root_.RHTower.edPoly _root_.RHTower.mobCoeff (Finset.Icc 1 X) (linePoint u) = _
    rw [_root_.RHTower.edPoly_mobCoeff_Icc_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hne : (((i : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hexp : -linePoint u = ((r : ℝ) : ℂ) + -s := by
      simp only [linePoint, hs, hσ']
      push_cast
      ring
    rw [hexp, Complex.cpow_add _ _ hne, ← Complex.ofReal_cpow hpos.le]
    simp only [hwt, ha, smul_eq_mul, Complex.real_smul]
    ring
  have hpartial : ∀ k, ‖∑ i ∈ Finset.range k, a i‖ ≤ K * (1 + |u|) := by
    intro k
    have h := hK k u
    rwa [_root_.RHTower.edPoly_mobCoeff_Icc_eq_sum_range] at h
  have hmono : Monotone wt := by
    refine monotone_nat_of_le_succ fun i => ?_
    refine Real.rpow_le_rpow (by positivity) ?_ hr0
    push_cast
    linarith
  have hb := norm_sum_range_smul_le (fun i => by simp only [hwt]; positivity) hmono hpartial X
  rw [hrep]
  have hcast : wt (X - 1) = (X : ℝ) ^ r := by
    simp only [hwt]
    congr 1
    rw [Nat.cast_sub hX]
    push_cast
    ring
  rwa [hcast] at hb

/-- `|ζ(½ + iu)| ≤ 18 (1 + |u|)`. -/
theorem norm_zeta_linePoint_le (u : ℝ) : ‖riemannZeta (linePoint u)‖ ≤ 18 * (1 + |u|) := by
  have hre : (1 / 2 : ℝ) ≤ (linePoint u).re := by rw [linePoint_re]
  have hsep : (1 / 2 : ℝ) ≤ ‖linePoint u - 1‖ := by
    have h := Complex.abs_re_le_norm (linePoint u - 1)
    simp only [Complex.sub_re, Complex.one_re, linePoint_re] at h
    norm_num at h
    linarith
  have h := _root_.RHTower.norm_riemannZeta_le_sqrt_norm_add_two_half hre (by norm_num) hsep
  have hn : ‖linePoint u‖ ≤ 1 / 2 + |u| := by
    unfold linePoint
    refine (norm_add_le _ _).trans ?_
    simp
  have hu := abs_nonneg u
  have hsq : Real.sqrt (‖linePoint u‖ + 2) ≤ ‖linePoint u‖ + 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg (linePoint u)]
  have hc : (2 + 1 / (1 / 2 : ℝ) + 2) = 6 := by norm_num
  rw [hc] at h
  linarith

/-- **The cap.** `|E_X(½ + iu)| ≤ C (1 + |u|)² X^{w+ε}`, with `C ≥ 1`. -/
theorem exists_norm_lineError_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : ℕ) (u : ℝ), 1 ≤ X →
      ‖lineError (moebiusPoly X) u‖ ≤ C * (1 + |u|) ^ 2 * (X : ℝ) ^ (zetaZeroWidth + ε) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_moebiusPoly_line_le hε
  refine ⟨36 * K + 1, by linarith, fun X u hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hr0 : 0 ≤ zetaZeroWidth + ε := by linarith [zetaZeroWidth_nonneg]
  set R : ℝ := (X : ℝ) ^ (zetaZeroWidth + ε) with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hr0
  have hu := abs_nonneg u
  have h1u : 1 ≤ (1 + |u|) ^ 2 := by nlinarith
  have hζ := norm_zeta_linePoint_le u
  have hM := hK X u hX
  rw [← hR] at hM
  unfold lineError
  calc ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u) - 1‖
      ≤ ‖riemannZeta (linePoint u)‖ * ‖moebiusPoly X (linePoint u)‖ + 1 := by
        have := norm_sub_le (riemannZeta (linePoint u) * moebiusPoly X (linePoint u)) 1
        rwa [norm_mul, norm_one] at this
    _ ≤ (18 * (1 + |u|)) * (2 * R * (K * (1 + |u|))) + 1 := by
        have := mul_le_mul hζ hM (norm_nonneg _) (by positivity)
        linarith
    _ = 36 * K * (1 + |u|) ^ 2 * R + 1 := by ring
    _ ≤ (36 * K + 1) * (1 + |u|) ^ 2 * R := by
        have : 1 ≤ (1 + |u|) ^ 2 * R := by
          nlinarith [mul_nonneg (sub_nonneg.mpr h1u) (sub_nonneg.mpr hR1)]
        nlinarith

theorem continuous_lineError {M : ℂ → ℂ} (hM : Differentiable ℂ M) : Continuous (lineError M) := by
  unfold lineError
  have h1 : Continuous fun u : ℝ => riemannZeta (linePoint u) :=
    continuous_iff_continuousAt.mpr fun u =>
      (differentiableAt_riemannZeta (linePoint_ne_one u)).continuousAt.comp
        continuous_linePoint.continuousAt
  exact (h1.mul (hM.continuous.comp continuous_linePoint)).sub continuous_const

/-! ### Low values and their Poisson mass -/

/-- The set of heights where `|E_X(½ + iu)| ≤ X^κ`. -/
def lowSet (X : ℕ) (κ : ℝ) : Set ℝ := {u | ‖lineError (moebiusPoly X) u‖ ≤ (X : ℝ) ^ κ}

theorem measurableSet_lowSet (X : ℕ) (κ : ℝ) : MeasurableSet (lowSet X κ) :=
  measurableSet_le (continuous_lineError (differentiable_moebiusPoly X)).norm.measurable
    measurable_const

/-- The Poisson density of the half-plane `Re z > ½` seen from `ρ`. -/
abbrev zeroPoisson (ρ : ℂ) (u : ℝ) : ℝ := halfPlanePoisson (ρ.re - 1 / 2) (u - ρ.im)

theorem continuous_poisson {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    Continuous fun u : ℝ => halfPlanePoisson δ (u - γ) :=
  (continuous_halfPlanePoisson hδ).comp (continuous_id.sub continuous_const)

/-- `log (1 + |u|)` is integrable against `P_ρ`, with mean at most `log 3 + log |ρ|`. -/
theorem integrable_and_integral_poisson_log_one_add_abs_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (γ : ℝ) :
    Integrable (fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log (1 + |u|)) ∧
      ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log (1 + |u|) ≤
        Real.log 3 + Real.log ‖offLinePoint δ γ‖ := by
  obtain ⟨hintL, hL⟩ := integrable_and_integral_poisson_log_norm_line hδ hδ1 γ
  have hP := integrable_poisson_shift hδ γ
  have hP0 : ∀ u : ℝ, 0 ≤ halfPlanePoisson δ (u - γ) := fun u => (halfPlanePoisson_pos hδ _).le
  have hpt : ∀ u : ℝ, Real.log (1 + |u|) ≤ Real.log 3 + Real.log ‖linePoint u‖ := by
    intro u
    have hn0 : ‖linePoint u‖ ≠ 0 := by
      refine norm_ne_zero_iff.mpr fun h => ?_
      have := congrArg Complex.re h
      rw [linePoint_re] at this
      norm_num at this
    have h1 : |(linePoint u).re| ≤ ‖linePoint u‖ := Complex.abs_re_le_norm _
    have h2 : |(linePoint u).im| ≤ ‖linePoint u‖ := Complex.abs_im_le_norm _
    rw [linePoint_re] at h1
    rw [linePoint_im] at h2
    norm_num at h1
    rw [← Real.log_mul (by norm_num) hn0]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hg : Integrable fun u : ℝ =>
      Real.log 3 * halfPlanePoisson δ (u - γ) +
        halfPlanePoisson δ (u - γ) * Real.log ‖linePoint u‖ :=
    (hP.const_mul _).add hintL
  have hle : ∀ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log (1 + |u|) ≤
      Real.log 3 * halfPlanePoisson δ (u - γ) +
        halfPlanePoisson δ (u - γ) * Real.log ‖linePoint u‖ := by
    intro u
    have := mul_le_mul_of_nonneg_left (hpt u) (hP0 u)
    linarith
  have hnn : ∀ u : ℝ, 0 ≤ halfPlanePoisson δ (u - γ) * Real.log (1 + |u|) := fun u =>
    mul_nonneg (hP0 u) (Real.log_nonneg (by linarith [abs_nonneg u]))
  have hmeas : Measurable fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log (1 + |u|) :=
    (continuous_poisson hδ γ).measurable.mul
      (Real.measurable_log.comp (continuous_const.add continuous_abs).measurable)
  have hint : Integrable fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log (1 + |u|) :=
    Integrable.mono' hg hmeas.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (hnn u)]
      exact hle u)
  refine ⟨hint, ?_⟩
  calc ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log (1 + |u|)
      ≤ ∫ u : ℝ, (Real.log 3 * halfPlanePoisson δ (u - γ) +
          halfPlanePoisson δ (u - γ) * Real.log ‖linePoint u‖) := integral_mono hint hg hle
    _ = Real.log 3 + Real.log ‖offLinePoint δ γ‖ := by
        rw [integral_add (hP.const_mul _) hintL, integral_const_mul, integral_poisson_shift hδ γ, hL,
          mul_one]

theorem integrable_zeroPoisson {ρ : ℂ} (hre : 1 / 2 < ρ.re) : Integrable (zeroPoisson ρ) :=
  integrable_poisson_shift (by linarith) ρ.im

theorem integral_zeroPoisson {ρ : ℂ} (hre : 1 / 2 < ρ.re) : ∫ u : ℝ, zeroPoisson ρ u = 1 :=
  integral_poisson_shift (by linarith) ρ.im

theorem zeroPoisson_nonneg {ρ : ℂ} (hre : 1 / 2 < ρ.re) (u : ℝ) : 0 ≤ zeroPoisson ρ u :=
  (halfPlanePoisson_pos (by linarith) _).le

theorem offLinePoint_re_im (ρ : ℂ) : offLinePoint (ρ.re - 1 / 2) ρ.im = ρ := by
  apply Complex.ext
  · rw [offLinePoint_re]; ring
  · rw [offLinePoint_im]

/-- **Poisson mass of low values, finite form.** For a zero `ρ` of depth `δ`, every `X ≥ 2` and `0 ≤ κ < w + ε`, the `P_ρ`-mass of
`{|E_X| ≤ X^κ}` is at most `((w + ε − δ) log X + K) / ((w + ε − κ) log X)`, with `K` depending on `ρ` and `ε` only. -/
theorem exists_poissonMass_lowSet_le {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re)
    (hre1 : ρ.re < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (X : ℕ) (κ : ℝ), 2 ≤ X → 0 ≤ κ → κ < zetaZeroWidth + ε →
      ∫ u in lowSet X κ, zeroPoisson ρ u ≤
        ((zetaZeroWidth + ε - (ρ.re - 1 / 2)) * Real.log X + K) /
          ((zetaZeroWidth + ε - κ) * Real.log X) := by
  obtain ⟨C, hC1, hC⟩ := exists_norm_lineError_le hε
  have hC0 : 0 < C := by linarith
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  have hδ1 : ρ.re - 1 / 2 < 1 / 2 := by linarith
  obtain ⟨hintQ', hQ'⟩ := integrable_and_integral_poisson_log_one_add_abs_le hδ hδ1 ρ.im
  have hintQ : Integrable fun u : ℝ => zeroPoisson ρ u * Real.log (1 + |u|) := hintQ'
  have hQ : ∫ u : ℝ, zeroPoisson ρ u * Real.log (1 + |u|) ≤ Real.log 3 + Real.log ‖ρ‖ := by
    rw [offLinePoint_re_im] at hQ'
    exact hQ'
  refine ⟨Real.log C + 2 * (Real.log 3 + Real.log ‖ρ‖) + Real.log (‖ρ‖ / ‖1 - ρ‖),
    fun X κ hX hκ0 hκ => ?_⟩
  have hX1 : 1 ≤ X := by omega
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (X : ℝ) := ⟨_, rfl⟩
  rw [← hLdef] at hL ⊢
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = zetaZeroWidth + ε := ⟨_, rfl⟩
  rw [← hr] at hκ ⊢
  have hr0 : 0 ≤ r := by rw [hr]; linarith [zetaZeroWidth_nonneg]
  obtain ⟨hintE', hfloor'⟩ := integrable_and_moebius_poisson_log_floor hX1 hζ hre hre1
  set E : ℝ → ℂ := lineError (moebiusPoly X) with hE
  have hintE : Integrable fun u : ℝ => zeroPoisson ρ u * Real.log ‖E u‖ := hintE'
  have hfloor : (ρ.re - 1 / 2) * Real.log ((X : ℝ) + 1) - Real.log (‖ρ‖ / ‖1 - ρ‖) ≤
      ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖E u‖ := hfloor'
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hlogu : ∀ u : ℝ, 0 ≤ Real.log (1 + |u|) := fun u =>
    Real.log_nonneg (by linarith [abs_nonneg u])
  have hcap : ∀ u : ℝ, Real.log ‖E u‖ ≤ Real.log C + 2 * Real.log (1 + |u|) + r * L := by
    intro u
    rcases eq_or_ne (E u) 0 with h0 | h0
    · rw [h0, norm_zero, Real.log_zero]
      have := hlogu u
      have : 0 ≤ r * L := mul_nonneg hr0 hL.le
      linarith
    · have hb : ‖E u‖ ≤ C * (1 + |u|) ^ 2 * (X : ℝ) ^ r := by
        rw [hr]
        exact hC X u hX1
      have hu1 : 0 < 1 + |u| := by linarith [abs_nonneg u]
      have hlog := Real.log_le_log (norm_pos_iff.mpr h0) hb
      rw [Real.log_mul (mul_pos hC0 (pow_pos hu1 2)).ne' (Real.rpow_pos_of_pos hX0 r).ne',
        Real.log_mul hC0.ne' (pow_pos hu1 2).ne', Real.log_pow, Real.log_rpow hX0, ← hLdef] at hlog
      push_cast at hlog
      linarith
  have hP := integrable_zeroPoisson hre
  have hP0 := zeroPoisson_nonneg hre
  set D : ℝ → ℝ := fun u => Real.log C + 2 * Real.log (1 + |u|) + r * L - Real.log ‖E u‖ with hD
  have hD0 : ∀ u, 0 ≤ D u := fun u => by simp only [hD]; linarith [hcap u]
  have hI : Integrable fun u : ℝ => (Real.log C + r * L) * zeroPoisson ρ u +
      2 * (zeroPoisson ρ u * Real.log (1 + |u|)) :=
    (hP.const_mul (Real.log C + r * L)).add (hintQ.const_mul 2)
  have heq : (fun u : ℝ => zeroPoisson ρ u * D u) = fun u =>
      (Real.log C + r * L) * zeroPoisson ρ u + 2 * (zeroPoisson ρ u * Real.log (1 + |u|)) -
        zeroPoisson ρ u * Real.log ‖E u‖ := by
    funext u
    simp only [hD]
    ring
  have hintD : Integrable fun u : ℝ => zeroPoisson ρ u * D u := by
    rw [heq]
    exact hI.sub hintE
  have hintDval : ∫ u : ℝ, zeroPoisson ρ u * D u ≤
      (r - (ρ.re - 1 / 2)) * L +
        (Real.log C + 2 * (Real.log 3 + Real.log ‖ρ‖) + Real.log (‖ρ‖ / ‖1 - ρ‖)) := by
    rw [heq, integral_sub hI hintE, integral_add (hP.const_mul _) (hintQ.const_mul 2),
      integral_const_mul, integral_const_mul, integral_zeroPoisson hre, mul_one]
    have hlog1 : L ≤ Real.log ((X : ℝ) + 1) := by
      rw [hLdef]
      exact Real.log_le_log hX0 (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hlog1 hδ.le
    linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (r - κ) * L := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by
    rw [hτ]
    exact mul_pos (by linarith) hL
  have hind : ∀ u : ℝ, (lowSet X κ).indicator (fun u => τ * zeroPoisson ρ u) u ≤
      zeroPoisson ρ u * D u := by
    intro u
    by_cases hu : u ∈ lowSet X κ
    · rw [indicator_of_mem hu, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (hP0 u)
      have hlow : Real.log ‖E u‖ ≤ κ * L := by
        rcases eq_or_ne (E u) 0 with h0 | h0
        · rw [h0, norm_zero, Real.log_zero]
          exact mul_nonneg hκ0 hL.le
        · have h1 := Real.log_le_log (norm_pos_iff.mpr h0) hu
          rwa [Real.log_rpow hX0, ← hLdef] at h1
      simp only [hD, hτ]
      have := hlogu u
      nlinarith
    · rw [indicator_of_notMem hu]
      exact mul_nonneg (hP0 u) (hD0 u)
  have hmeasS := measurableSet_lowSet X κ
  have hmono := integral_mono ((hP.const_mul τ).indicator hmeasS) hintD hind
  rw [integral_indicator hmeasS, integral_const_mul] at hmono
  have hden : (r - κ) * L = τ := hτ.symm
  rw [hden, le_div_iff₀ hτ0, mul_comm]
  exact hmono.trans hintDval

theorem zero_depth_le_width {ρ : ℂ} (hζ : riemannZeta ρ = 0) : ρ.re - 1 / 2 ≤ zetaZeroWidth := by
  rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  linarith [_root_.RHTower.re_le_zetaZeroAbscissa hζ]

theorem tendsto_log_natCast_atTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **Poisson mass of low values.** For `0 ≤ κ < w` and `η > 0`, eventually in `X` the `P_ρ`-mass of `{|E_X| ≤ X^κ}` is at most
`(w − δ)/(w − κ) + η`. -/
theorem eventually_poissonMass_lowSet_le {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re)
    (hre1 : ρ.re < 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < zetaZeroWidth) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop, ∫ u in lowSet X κ, zeroPoisson ρ u ≤
      (zetaZeroWidth - (ρ.re - 1 / 2)) / (zetaZeroWidth - κ) + η := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = zetaZeroWidth - κ := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = zetaZeroWidth - (ρ.re - 1 / 2) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; linarith [zero_depth_le_width hζ]
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η * a / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨K, hK⟩ := exists_poissonMass_lowSet_le hζ hre hre1 hε0
  rw [← ha, ← hd]
  filter_upwards [eventually_ge_atTop 2,
    tendsto_log_natCast_atTop.eventually_ge_atTop (2 * |K| / (a * η) + 1)] with X hX hLX
  have hnn : 0 ≤ 2 * |K| / (a * η) := by positivity
  have hL : 0 < Real.log (X : ℝ) := by linarith
  have hb := hK X κ hX hκ0 (by linarith)
  refine hb.trans ?_
  have hsum : zetaZeroWidth + ε - κ = a + ε := by rw [ha]; ring
  have hnum : zetaZeroWidth + ε - (ρ.re - 1 / 2) = d + ε := by rw [hd]; ring
  rw [hsum, hnum]
  have haε : 0 < a + ε := by positivity
  have hsplit : ((d + ε) * Real.log X + K) / ((a + ε) * Real.log X) =
      (d + ε) / (a + ε) + K / ((a + ε) * Real.log X) := by
    rw [add_div, mul_div_mul_right _ _ hL.ne']
  rw [hsplit]
  have h1 : (d + ε) / (a + ε) ≤ d / a + η / 2 := by
    calc (d + ε) / (a + ε) ≤ (d + ε) / a :=
          div_le_div_of_nonneg_left (by positivity) ha0 (by linarith)
      _ = d / a + η / 2 := by
          rw [add_div, hε]
          congr 1
          field_simp
  have h2 : K / ((a + ε) * Real.log X) ≤ η / 2 := by
    have hden : 0 < (a + ε) * Real.log X := mul_pos haε hL
    rw [div_le_iff₀ hden]
    have hKabs : K ≤ |K| := le_abs_self K
    have hLb : 2 * |K| / (a * η) ≤ Real.log X := by linarith
    rw [div_le_iff₀ (mul_pos ha0 hη)] at hLb
    have hextra := mul_nonneg (mul_nonneg hη.le hε0.le) hL.le
    nlinarith
  linarith

/-- A density bounded below by `p` on a window has `p` times the volume as a lower bound of its integral. -/
theorem mul_volume_le_setIntegral {P : ℝ → ℝ} (hP : Integrable P) (hP0 : ∀ u, 0 ≤ P u) {S : Set ℝ}
    (hS : MeasurableSet S) {a b p : ℝ} (hp : ∀ u ∈ Icc a b, p ≤ P u) :
    p * volume.real (S ∩ Icc a b) ≤ ∫ u in S, P u := by
  have hmeas : MeasurableSet (S ∩ Icc a b) := hS.inter measurableSet_Icc
  have hfin : volume (S ∩ Icc a b) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt (by simp [Real.volume_Icc])).ne
  have h1 : ∫ _u in S ∩ Icc a b, p ≤ ∫ u in S ∩ Icc a b, P u := by
    refine setIntegral_mono_on (integrableOn_const hfin) hP.integrableOn hmeas ?_
    intro u hu
    exact hp u hu.2
  rw [setIntegral_const, smul_eq_mul, mul_comm] at h1
  refine h1.trans ?_
  exact setIntegral_mono_set hP.integrableOn (Eventually.of_forall hP0)
    (LE.le.eventuallyLE inter_subset_left)

/-- The Poisson density is bounded below on a bounded window. -/
theorem poisson_lower_bound {δ v R : ℝ} (hδ : 0 < δ) (hv : |v| ≤ R) :
    δ / (Real.pi * (δ ^ 2 + R ^ 2)) ≤ halfPlanePoisson δ v := by
  have hπ := Real.pi_pos
  have hsq : v ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs v]
    exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  rw [halfPlanePoisson]
  refine div_le_div_of_nonneg_left hδ.le (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hπ.le

/-- **Rigidity at an attained width.** If a zero has depth exactly `w`, then for every `κ < w` the low set `{|E_X| ≤ X^κ}` has vanishing
measure in every bounded window as `X → ∞`. -/
theorem tendsto_volume_lowSet_of_top_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re)
    (hre1 : ρ.re < 1) (htop : ρ.re - 1 / 2 = zetaZeroWidth) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ < zetaZeroWidth) (a b : ℝ) :
    Tendsto (fun X : ℕ => volume.real (lowSet X κ ∩ Icc a b)) atTop (nhds 0) := by
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |a - ρ.im| + |b - ρ.im| := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (ρ.re - 1 / 2) / (Real.pi * ((ρ.re - 1 / 2) ^ 2 + R ^ 2)) := ⟨_, rfl⟩
  have hπ := Real.pi_pos
  have hp0 : 0 < p := by
    rw [hp]
    have h2 := pow_pos hδ 2
    have h3 := sq_nonneg R
    exact div_pos hδ (mul_pos hπ (by linarith))
  have hplow : ∀ u ∈ Icc a b, p ≤ zeroPoisson ρ u := by
    intro u hu
    rw [hp]
    refine poisson_lower_bound hδ ?_
    rw [abs_le, hR]
    have h1 := neg_abs_le (a - ρ.im)
    have h2 := le_abs_self (b - ρ.im)
    have h3 := abs_nonneg (a - ρ.im)
    have h4 := abs_nonneg (b - ρ.im)
    constructor
    · linarith [hu.1]
    · linarith [hu.2]
  have hP := integrable_zeroPoisson hre
  have hP0 := zeroPoisson_nonneg hre
  rw [Metric.tendsto_atTop]
  intro e he
  have hev := eventually_poissonMass_lowSet_le hζ hre hre1 hκ0 hκ
    (η := e * p / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun X hX => ?_⟩
  have hb := hN X hX
  have hzero : (zetaZeroWidth - (ρ.re - 1 / 2)) / (zetaZeroWidth - κ) = 0 := by
    rw [show zetaZeroWidth - (ρ.re - 1 / 2) = 0 by linarith, zero_div]
  rw [hzero, zero_add] at hb
  have hlow := mul_volume_le_setIntegral hP hP0 (measurableSet_lowSet X κ) hplow
  have hvol : volume.real (lowSet X κ ∩ Icc a b) ≤ e / 2 := by
    have := hlow.trans hb
    rw [mul_comm, ← le_div_iff₀ hp0] at this
    calc _ ≤ e * p / 2 / p := this
      _ = e / 2 := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-! ### The positive-proportion criterion -/

/-- **The width is read by a positive proportion of every window.** `zetaZeroWidth ≤ β` iff there is `ν > 0` such that for every height `τ`
and `ε > 0`, arbitrarily large `X` have `|{u ∈ [τ − 1, τ + 1] : |ζ M_X − 1|(½ + iu) ≤ X^{β+ε}}| ≥ ν`. -/
theorem zetaZeroWidth_le_iff_positive_proportion {β : ℝ} (hβ : 0 ≤ β) :
    zetaZeroWidth ≤ β ↔ ∃ ν : ℝ, 0 < ν ∧ ∀ τ ε : ℝ, 0 < ε → ∃ᶠ X : ℕ in atTop,
      ν ≤ volume.real (lowSet X (β + ε) ∩ Icc (τ - 1) (τ + 1)) := by
  constructor
  · intro hw
    refine ⟨1, one_pos, fun τ ε hε => ?_⟩
    refine Eventually.frequently ?_
    obtain ⟨C, hC1, hC⟩ := exists_norm_lineError_le (ε := ε / 2) (by positivity)
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = C * (2 + |τ|) ^ 2 := ⟨_, rfl⟩
    have hgrow : Tendsto (fun X : ℕ => (X : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, hgrow.eventually_ge_atTop Q] with X hX hXQ
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hsub : Icc (τ - 1) (τ + 1) ⊆ lowSet X (β + ε) := by
      intro u hu
      show ‖lineError (moebiusPoly X) u‖ ≤ (X : ℝ) ^ (β + ε)
      have hb := hC X u hX
      have huabs : |u| ≤ 1 + |τ| := by
        rw [abs_le]
        have h1 := neg_abs_le τ
        have h2 := le_abs_self τ
        constructor <;> linarith [hu.1, hu.2]
      have hu0 := abs_nonneg u
      have hτ0 := abs_nonneg τ
      have hu2 : (1 + |u|) ^ 2 ≤ (2 + |τ|) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hr : (X : ℝ) ^ (zetaZeroWidth + ε / 2) ≤ (X : ℝ) ^ (β + ε / 2) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      have hsplit : (X : ℝ) ^ (β + ε) = (X : ℝ) ^ (β + ε / 2) * (X : ℝ) ^ (ε / 2) := by
        rw [← Real.rpow_add hX0]
        congr 1
        ring
      have hC0 : 0 ≤ C := by linarith
      have hrpos : 0 < (X : ℝ) ^ (β + ε / 2) := Real.rpow_pos_of_pos hX0 _
      calc ‖lineError (moebiusPoly X) u‖
          ≤ C * (1 + |u|) ^ 2 * (X : ℝ) ^ (zetaZeroWidth + ε / 2) := hb
        _ ≤ C * (2 + |τ|) ^ 2 * (X : ℝ) ^ (β + ε / 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hu2 hC0) hr (Real.rpow_nonneg hX0.le _)
              (by positivity)
        _ = Q * (X : ℝ) ^ (β + ε / 2) := by rw [hQ]
        _ ≤ (X : ℝ) ^ (ε / 2) * (X : ℝ) ^ (β + ε / 2) :=
            mul_le_mul_of_nonneg_right hXQ hrpos.le
        _ = (X : ℝ) ^ (β + ε) := by rw [hsplit]; ring
    have hinter : lowSet X (β + ε) ∩ Icc (τ - 1) (τ + 1) = Icc (τ - 1) (τ + 1) :=
      inter_eq_right.mpr hsub
    rw [hinter, Real.volume_real_Icc_of_le (by linarith)]
    linarith
  · rintro ⟨ν, hν, h⟩
    by_contra hlt
    rw [not_le] at hlt
    have hw0 : 0 < zetaZeroWidth := by linarith
    obtain ⟨g, hg⟩ : ∃ g : ℝ, g = zetaZeroWidth - β := ⟨_, rfl⟩
    have hg0 : 0 < g := by rw [hg]; linarith
    have hπ := Real.pi_pos
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ, p₀ = (zetaZeroWidth / 2) / (Real.pi * (1 / 4 + 1)) := ⟨_, rfl⟩
    have hp₀0 : 0 < p₀ := by rw [hp₀]; positivity
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (zetaZeroWidth / 2) (p₀ * ν * g / 8) := ⟨_, rfl⟩
    have ht0 : 0 < t := by
      rw [ht]
      exact lt_min (by positivity) (by positivity)
    have habs : _root_.RHTower.zetaZeroAbscissa = 1 / 2 + zetaZeroWidth := by
      rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
      ring
    obtain ⟨ρ, hζ, hre1, hbρ⟩ := _root_.RHTower.exists_zetaZero_mem_openStrip_lt_re
      (b := 1 / 2 + zetaZeroWidth - t) (by rw [habs]; linarith)
    have ht1 : t ≤ zetaZeroWidth / 2 := by rw [ht]; exact min_le_left _ _
    have ht2 : t ≤ p₀ * ν * g / 8 := by rw [ht]; exact min_le_right _ _
    have hre : 1 / 2 < ρ.re := by linarith
    have hδ : 0 < ρ.re - 1 / 2 := by linarith
    have hδ1 : ρ.re - 1 / 2 < 1 / 2 := by linarith
    have hδw : zetaZeroWidth / 2 ≤ ρ.re - 1 / 2 := by linarith
    have hdt : zetaZeroWidth - (ρ.re - 1 / 2) ≤ t := by linarith
    have hplow : ∀ u ∈ Icc (ρ.im - 1) (ρ.im + 1), p₀ ≤ zeroPoisson ρ u := by
      intro u hu
      have habsu : |u - ρ.im| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hu.1, hu.2]
      refine le_trans ?_ (poisson_lower_bound hδ habsu)
      rw [hp₀]
      have hδsq : (ρ.re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith
      have hden : 0 < Real.pi * ((ρ.re - 1 / 2) ^ 2 + 1 ^ 2) := by
        have := sq_nonneg (ρ.re - 1 / 2)
        exact mul_pos hπ (by linarith)
      exact div_le_div₀ hδ.le hδw hden
        (mul_le_mul_of_nonneg_left (by linarith) hπ.le)
    have hP := integrable_zeroPoisson hre
    have hP0 := zeroPoisson_nonneg hre
    have hκ0 : 0 ≤ β + g / 2 := by positivity
    have hκw : β + g / 2 < zetaZeroWidth := by rw [hg]; linarith
    have hev := eventually_poissonMass_lowSet_le hζ hre hre1 hκ0 hκw
      (η := p₀ * ν / 4) (by positivity)
    have hfreq := h ρ.im (g / 2) (by positivity)
    obtain ⟨X, hX1, hX2⟩ := (hfreq.and_eventually hev).exists
    have hlow := mul_volume_le_setIntegral hP hP0 (measurableSet_lowSet X (β + g / 2)) hplow
    have hmul : p₀ * ν ≤ ∫ u in lowSet X (β + g / 2), zeroPoisson ρ u :=
      (mul_le_mul_of_nonneg_left hX1 hp₀0.le).trans hlow
    have hquot : (zetaZeroWidth - (ρ.re - 1 / 2)) / (zetaZeroWidth - (β + g / 2)) ≤
        p₀ * ν / 4 := by
      have hwκ : zetaZeroWidth - (β + g / 2) = g / 2 := by rw [hg]; ring
      rw [hwκ, div_le_iff₀ (by positivity)]
      nlinarith
    have hpos : 0 < p₀ * ν := by positivity
    linarith

/-- **RH as a positive proportion of every window.** -/
theorem riemannHypothesis_iff_positive_proportion :
    RiemannHypothesis ↔ ∃ ν : ℝ, 0 < ν ∧ ∀ τ ε : ℝ, 0 < ε → ∃ᶠ X : ℕ in atTop,
      ν ≤ volume.real (lowSet X ε ∩ Icc (τ - 1) (τ + 1)) := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl,
    zetaZeroWidth_le_iff_positive_proportion le_rfl]
  simp only [zero_add]

/-- **One moment of any order on every window suffices.** If for every height and every `ε > 0`, arbitrarily large `X` satisfy
`∫_{τ−1}^{τ+1} |E_X|^p ≤ X^{p(β+ε)}`, then `zetaZeroWidth ≤ β`. -/
theorem zetaZeroWidth_le_of_frequently_window_moment {β p : ℝ} (hβ : 0 ≤ β) (hp : 0 < p)
    (h : ∀ τ ε : ℝ, 0 < ε → ∃ᶠ X : ℕ in atTop,
      ∫ u in Icc (τ - 1) (τ + 1), ‖lineError (moebiusPoly X) u‖ ^ p ≤ (X : ℝ) ^ (p * (β + ε))) :
    zetaZeroWidth ≤ β := by
  rw [zetaZeroWidth_le_iff_positive_proportion hβ]
  refine ⟨1, one_pos, fun τ ε hε => ?_⟩
  have hfreq := (h τ (ε / 2) (by positivity)).and_eventually (eventually_ge_atTop 1)
  refine hfreq.mono fun X hX => ?_
  obtain ⟨hmom, hX1⟩ := hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < X := by linarith
  have hcont : Continuous fun u : ℝ => ‖lineError (moebiusPoly X) u‖ ^ p :=
    (continuous_lineError (differentiable_moebiusPoly X)).norm.rpow_const fun _ => Or.inr hp.le
  have hintW : IntegrableOn (fun u : ℝ => ‖lineError (moebiusPoly X) u‖ ^ p)
      (Icc (τ - 1) (τ + 1)) := hcont.integrableOn_Icc
  obtain ⟨B, hB⟩ : ∃ B : Set ℝ, B = Icc (τ - 1) (τ + 1) \ lowSet X (β + ε) := ⟨_, rfl⟩
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact measurableSet_Icc.diff (measurableSet_lowSet X (β + ε))
  have hBW : B ⊆ Icc (τ - 1) (τ + 1) := by
    rw [hB]
    exact sdiff_subset
  have hBfin : volume B ≠ ⊤ :=
    ((measure_mono hBW).trans_lt (by simp [Real.volume_Icc])).ne
  have hbig : (X : ℝ) ^ ((β + ε) * p) * volume.real B ≤
      ∫ u in Icc (τ - 1) (τ + 1), ‖lineError (moebiusPoly X) u‖ ^ p := by
    have h1 : ∫ _u in B, (X : ℝ) ^ ((β + ε) * p) ≤
        ∫ u in B, ‖lineError (moebiusPoly X) u‖ ^ p := by
      refine setIntegral_mono_on (integrableOn_const hBfin) (hintW.mono_set hBW) hBmeas ?_
      intro u hu
      rw [hB] at hu
      have hnot : ¬ ‖lineError (moebiusPoly X) u‖ ≤ (X : ℝ) ^ (β + ε) := hu.2
      rw [not_le] at hnot
      rw [Real.rpow_mul hX0.le]
      exact Real.rpow_le_rpow (by positivity) hnot.le hp.le
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h1
    refine h1.trans ?_
    exact setIntegral_mono_set hintW (Eventually.of_forall fun u => by positivity)
      (LE.le.eventuallyLE hBW)
  have hsplit : (X : ℝ) ^ ((β + ε) * p) =
      (X : ℝ) ^ (p * (β + ε / 2)) * (X : ℝ) ^ (p * (ε / 2)) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  have hone : 1 ≤ (X : ℝ) ^ (p * (ε / 2)) := Real.one_le_rpow hX1R (by positivity)
  have hpos : 0 < (X : ℝ) ^ (p * (β + ε / 2)) := Real.rpow_pos_of_pos hX0 _
  have hBnn : 0 ≤ volume.real B := measureReal_nonneg
  have hvolB : volume.real B ≤ 1 := by
    have h2 : (X : ℝ) ^ (p * (β + ε / 2)) * ((X : ℝ) ^ (p * (ε / 2)) * volume.real B) ≤
        (X : ℝ) ^ (p * (β + ε / 2)) * 1 := by
      rw [mul_one, ← mul_assoc, ← hsplit]
      exact hbig.trans hmom
    have h3 := le_of_mul_le_mul_left h2 hpos
    nlinarith
  have hcover : Icc (τ - 1) (τ + 1) ⊆
      (lowSet X (β + ε) ∩ Icc (τ - 1) (τ + 1)) ∪ B := by
    intro u hu
    by_cases hl : u ∈ lowSet X (β + ε)
    · exact Or.inl ⟨hl, hu⟩
    · refine Or.inr ?_
      rw [hB]
      exact ⟨hu, hl⟩
  have hfinI : volume (lowSet X (β + ε) ∩ Icc (τ - 1) (τ + 1)) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt (by simp [Real.volume_Icc])).ne
  have h2 := measureReal_mono hcover (measure_union_ne_top hfinI hBfin)
  have h3 := measureReal_union_le (μ := volume) (lowSet X (β + ε) ∩ Icc (τ - 1) (τ + 1)) B
  rw [Real.volume_real_Icc_of_le (by linarith)] at h2
  linarith

/-! ### Barrier immunity -/

/-- `P_ρ |E_X|²` is integrable: `|ζ(½ + iu)|²/(¼ + u²)` is, and `P_ρ` is comparable to `1/(¼ + u²)`. -/
theorem integrable_zeroPoisson_mul_normSq_lineError {ρ : ℂ} (hre : 1 / 2 < ρ.re) (X : ℕ) :
    Integrable fun u : ℝ => zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 := by
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ρ.re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = ρ.im := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact hδ
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 / 4 + 2 * γ ^ 2) / δ ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hAδ : A * δ ^ 2 = 1 / 4 + 2 * γ ^ 2 := by
    rw [hA]
    field_simp
  have hπ := Real.pi_pos
  have hkey : ∀ u : ℝ, 1 / 4 + u ^ 2 ≤ (2 + A) * (δ ^ 2 + (u - γ) ^ 2) := by
    intro u
    have h1 : u ^ 2 ≤ 2 * (u - γ) ^ 2 + 2 * γ ^ 2 := by nlinarith [sq_nonneg (u - 2 * γ)]
    have h2 := mul_nonneg hA0 (sq_nonneg (u - γ))
    have h3 := sq_nonneg δ
    nlinarith
  have hPle : ∀ u : ℝ, zeroPoisson ρ u ≤ (δ * (2 + A) / Real.pi) / (1 / 4 + u ^ 2) := by
    intro u
    show halfPlanePoisson (ρ.re - 1 / 2) (u - ρ.im) ≤ _
    rw [← hδdef, ← hγdef, halfPlanePoisson]
    have hden : 0 < δ ^ 2 + (u - γ) ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hR : δ * (2 + A) / Real.pi * (Real.pi * (δ ^ 2 + (u - γ) ^ 2)) =
        δ * ((2 + A) * (δ ^ 2 + (u - γ) ^ 2)) := by
      field_simp
    rw [hR]
    exact mul_le_mul_of_nonneg_left (hkey u) hδ0.le
  have hP := integrable_zeroPoisson hre
  have hP0 := zeroPoisson_nonneg hre
  have hZ := _root_.RHTower.integrable_and_integral_norm_sq_zeta_criticalLine.1
  have hdom : Integrable fun u : ℝ => 2 * zeroPoisson ρ u +
      (2 * (X : ℝ) ^ 2 * (δ * (2 + A) / Real.pi)) *
        (‖riemannZeta (1 / 2 + u * I)‖ ^ 2 / (1 / 4 + u ^ 2)) :=
    (hP.const_mul 2).add (hZ.const_mul _)
  have hcontE := continuous_lineError (differentiable_moebiusPoly X)
  have hcontP : Continuous (zeroPoisson ρ) := continuous_poisson hδ ρ.im
  refine Integrable.mono' hdom (hcontP.mul (hcontE.norm.pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hP0 u) (by positivity))]
  have hM : ‖moebiusPoly X (linePoint u)‖ ≤ X :=
    _root_.RHTower.norm_edPoly_mobCoeff_le X (by rw [linePoint_re]; norm_num)
  have hE : ‖lineError (moebiusPoly X) u‖ ≤ ‖riemannZeta (linePoint u)‖ * X + 1 := by
    unfold lineError
    have h1 := norm_sub_le (riemannZeta (linePoint u) * moebiusPoly X (linePoint u)) 1
    rw [norm_mul, norm_one] at h1
    have h2 := mul_le_mul_of_nonneg_left hM (norm_nonneg (riemannZeta (linePoint u)))
    linarith
  have hEsq : ‖lineError (moebiusPoly X) u‖ ^ 2 ≤ 2 + 2 * (X : ℝ) ^ 2 * ‖riemannZeta (linePoint u)‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hE 2
    nlinarith [sq_nonneg (‖riemannZeta (linePoint u)‖ * X - 1)]
  have hZnn : 0 ≤ 2 * (X : ℝ) ^ 2 * ‖riemannZeta (linePoint u)‖ ^ 2 := by positivity
  have hstep1 := mul_le_mul_of_nonneg_left hEsq (hP0 u)
  have hstep2 := mul_le_mul_of_nonneg_right (hPle u) hZnn
  have hline : linePoint u = 1 / 2 + (u : ℂ) * I := rfl
  rw [← hline]
  have hu : (0 : ℝ) < 1 / 4 + u ^ 2 := by positivity
  have hrew : (δ * (2 + A) / Real.pi) / (1 / 4 + u ^ 2) *
      (2 * (X : ℝ) ^ 2 * ‖riemannZeta (linePoint u)‖ ^ 2) =
      (2 * (X : ℝ) ^ 2 * (δ * (2 + A) / Real.pi)) *
        (‖riemannZeta (linePoint u)‖ ^ 2 / (1 / 4 + u ^ 2)) := by
    field_simp
  rw [hrew] at hstep2
  linarith

/-- **Barrier immunity.** For `0 ≤ κ < w` and `η > 0`, eventually in `X` and uniformly in the measurable set `G`,
`(P_ρ(G) − (w − δ)/(w − κ) − η) X^{2κ} ≤ ∫_G P_ρ |E_X|²`. So restricting a second moment to a set, even one chosen after `X`, does not
lower its slope unless the set has `P_ρ`-mass at most `(w − δ)/(w − κ)`. -/
theorem eventually_restricted_secondMoment_ge {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re)
    (hre1 : ρ.re < 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < zetaZeroWidth) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop, ∀ G : Set ℝ, MeasurableSet G →
      ((∫ u in G, zeroPoisson ρ u) - (zetaZeroWidth - (ρ.re - 1 / 2)) / (zetaZeroWidth - κ) - η) *
          (X : ℝ) ^ (2 * κ) ≤
        ∫ u in G, zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 := by
  filter_upwards [eventually_poissonMass_lowSet_le hζ hre hre1 hκ0 hκ hη, eventually_ge_atTop 1]
    with X hmass hX G hG
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hP := integrable_zeroPoisson hre
  have hP0 := zeroPoisson_nonneg hre
  have hS := measurableSet_lowSet X κ
  have hint := integrable_zeroPoisson_mul_normSq_lineError hre X
  have hR : (X : ℝ) ^ (2 * κ) = ((X : ℝ) ^ κ) ^ 2 := by
    rw [mul_comm 2 κ, Real.rpow_mul hX0.le, Real.rpow_two]
  have hRnn : 0 ≤ (X : ℝ) ^ (2 * κ) := Real.rpow_nonneg hX0.le _
  have hsplit := integral_inter_add_sdiff (μ := volume) (f := zeroPoisson ρ) (s := G) hS
    hP.integrableOn
  have hinter : ∫ u in G ∩ lowSet X κ, zeroPoisson ρ u ≤ ∫ u in lowSet X κ, zeroPoisson ρ u :=
    setIntegral_mono_set hP.integrableOn (Eventually.of_forall hP0)
      (LE.le.eventuallyLE inter_subset_right)
  have hdiffmeas : MeasurableSet (G \ lowSet X κ) := hG.diff hS
  have hlow : (X : ℝ) ^ (2 * κ) * ∫ u in G \ lowSet X κ, zeroPoisson ρ u ≤
      ∫ u in G \ lowSet X κ, zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hP.integrableOn.const_mul _) hint.integrableOn hdiffmeas ?_
    intro u hu
    have hnot : ¬ ‖lineError (moebiusPoly X) u‖ ≤ (X : ℝ) ^ κ := hu.2
    rw [not_le] at hnot
    have hsq : (X : ℝ) ^ (2 * κ) ≤ ‖lineError (moebiusPoly X) u‖ ^ 2 := by
      rw [hR]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hX0.le _) hnot.le 2
    calc (X : ℝ) ^ (2 * κ) * zeroPoisson ρ u
        ≤ ‖lineError (moebiusPoly X) u‖ ^ 2 * zeroPoisson ρ u :=
          mul_le_mul_of_nonneg_right hsq (hP0 u)
      _ = zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 := mul_comm _ _
  have hnn : ∀ u, 0 ≤ zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 := fun u =>
    mul_nonneg (hP0 u) (by positivity)
  have hup : ∫ u in G \ lowSet X κ, zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 ≤
      ∫ u in G, zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2 :=
    setIntegral_mono_set hint.integrableOn (Eventually.of_forall hnn)
      (LE.le.eventuallyLE sdiff_subset)
  have hmass2 : (∫ u in G, zeroPoisson ρ u) -
      (zetaZeroWidth - (ρ.re - 1 / 2)) / (zetaZeroWidth - κ) - η ≤
      ∫ u in G \ lowSet X κ, zeroPoisson ρ u := by
    linarith
  calc _ ≤ (∫ u in G \ lowSet X κ, zeroPoisson ρ u) * (X : ℝ) ^ (2 * κ) :=
        mul_le_mul_of_nonneg_right hmass2 hRnn
    _ = (X : ℝ) ^ (2 * κ) * ∫ u in G \ lowSet X κ, zeroPoisson ρ u := mul_comm _ _
    _ ≤ _ := hlow.trans hup

end GaloisForLFunctions.MultiscaleMollifiedZetaField
