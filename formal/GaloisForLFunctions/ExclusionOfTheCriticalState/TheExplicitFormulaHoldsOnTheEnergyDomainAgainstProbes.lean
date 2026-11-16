import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePairingsOfAProfileWithAProbeGrowAtMostLinearly
import GaloisForLFunctions.RHTower.XiHorizontalStripComparison
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.FermiNymanWitnessExponentZeroRigidity
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.HTGeometry.EntireDividedDifferenceContour

/-!
# The explicit formula holds on the energy domain against probes

For a profile `F` of the energy domain let `B F(p)` be the bare mixed form of `F` with the probe
`e_p` continued to the plane (`globalRemainder`): Gamma pairing, prime side and the two charges. Then

  `B F(p) - B F(1) = Σ_z L F(z) (1/(p - z) - 1/(1 - z))`   for every `p` with `ξ(½ + p) ≠ 0`,

the sum over the centred zeros `z = ρ - ½` of `ξ` with multiplicity. Nothing beyond membership of
the domain is asked of `F`, and no estimate of `ζ'/ζ` inside the strip enters.

Mechanism. The defect `E = B F(1) - B F + Z F` has two pole-free forms: right of `Re p = -½` the
Euler factor is traded for `ξ'/ξ` through `(s-1)ζ(s) = 2ξ(s)/(sΓℝ(s))` and the poles go into the
divided-difference sum; on `-2 < Re p < ½` the same is done with the reflected Euler factor. Left
of the strip there are no zeros. The forms glue to an entire function of growth `O(|p|²)`, which
vanishes at `1` and is `o(|p|)` along the negative axis; Liouville on its divided difference at `1`
gives `E = 0`.

For the critical state `B F(p) = -a L F(p - 8)`, so its transform is the Cauchy transform of its
own values at the zeros: for `Re w, Re v > -4`

  `a (L F(w) - L F(v)) = -Σ_z L F(z) (1/(w + 8 - z) - 1/(v + 8 - z))`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The completed factorisation -/

theorem re_one_half_add (p : ℂ) : ((1 : ℂ) / 2 + p).re = 1 / 2 + p.re := by
  rw [Complex.add_re, re_one_half]

theorem re_one_half_sub (p : ℂ) : ((1 : ℂ) / 2 - p).re = 1 / 2 - p.re := by
  rw [Complex.sub_re, re_one_half]

theorem norm_half_one : ‖(1 : ℂ) / 2‖ = 1 / 2 := by
  rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num)]

/-- `ξ(s) = (s/2) Γℝ(s) · (s-1)ζ(s)` on `Re s > 0`, the pole of `ζ` included. -/
theorem xi_eq_half_mul_Gammaℝ_mul_zetaEntire {s : ℂ} (hs : 0 < s.re) :
    xi s = s / 2 * (Complex.Gammaℝ s * zetaEntire s) := by
  rcases eq_or_ne s 1 with rfl | h1
  · have hz1 : zetaEntire 1 = 1 := by
      rw [zetaEntire, sub_self, zero_mul, zero_add, Complex.Gammaℝ_one, inv_one]
    rw [xi_one, Complex.Gammaℝ_one, hz1]
    norm_num
  · have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
    rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 h1 hs, zetaEntire_eq h1]
    ring

/-- The logarithmic derivative of `(s-1)ζ(s)` through `ξ`, valid at `s = 1` as well:
`((s-1)ζ)'/((s-1)ζ) = ξ'/ξ - 1/s - Γℝ'/Γℝ`. -/
theorem logDeriv_zetaEntire_eq_xi {s : ℂ} (hs : 0 < s.re) (hxi : xi s ≠ 0) :
    logDeriv zetaEntire s = logDeriv xi s - s⁻¹ - logDeriv Complex.Gammaℝ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hprod := xi_eq_half_mul_Gammaℝ_mul_zetaEntire hs
  have hz : zetaEntire s ≠ 0 := fun h => hxi (by rw [hprod, h]; ring)
  have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_Gammaℝ_of_re_pos hs
  have hzd : DifferentiableAt ℂ zetaEntire s := differentiable_zetaEntire s
  have hev : xi =ᶠ[𝓝 s] fun w => w / 2 * (Complex.Gammaℝ w * zetaEntire w) := by
    have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hs] with w hw
    exact xi_eq_half_mul_Gammaℝ_mul_zetaEntire hw
  have h1 : logDeriv xi s = logDeriv (fun w => w / 2 * (Complex.Gammaℝ w * zetaEntire w)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hid : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := (hasDerivAt_id' s).div_const 2
  have h2 : logDeriv (fun w : ℂ => w / 2) s = s⁻¹ := by
    rw [logDeriv_apply, hid.deriv]
    field_simp
  rw [h1, logDeriv_mul (f := fun w : ℂ => w / 2)
      (g := fun w => Complex.Gammaℝ w * zetaEntire w) s (div_ne_zero hs0 two_ne_zero)
      (mul_ne_zero hΓ hz) hid.differentiableAt (hΓd.mul hzd),
    logDeriv_mul s hΓ hz hΓd hzd, h2]
  ring

theorem xi_half_sub_eq (p : ℂ) : xi (1 / 2 - p) = xi (1 / 2 + p) := by
  rw [show (1 : ℂ) / 2 - p = 1 - (1 / 2 + p) by ring, xi_one_sub]

/-- `ξ(½ + p)` has no zero off the open strip `|Re p| < ½`. -/
theorem xi_ne_zero_of_half_le_abs_re {p : ℂ} (hp : 1 / 2 ≤ |p.re|) : xi (1 / 2 + p) ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
  have hz : centredZero q = p := by
    unfold centredZero
    rw [hq]
    ring
  have := abs_re_centredZero_lt q
  rw [hz] at this
  linarith

/-- The zeros of `ξ(½ + ·)` are isolated. -/
theorem eventually_xi_half_add_ne_zero (p₀ : ℂ) : ∀ᶠ p in 𝓝[≠] p₀, xi (1 / 2 + p) ≠ 0 := by
  rcases (xi_analyticAt (1 / 2 + p₀)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (xi_not_eventually_zero _)
  · have ht : Tendsto (fun p : ℂ => 1 / 2 + p) (𝓝[≠] p₀) (𝓝[≠] (1 / 2 + p₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_const.add continuous_id).tendsto p₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with p hp
        exact fun h' => hp (add_left_cancel h')
    exact ht.eventually h

/-! ### The defect and its pole-free forms -/

/-- The defect of the explicit formula at base point `1`. -/
def explicitDefect (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  globalRemainder F 1 - globalRemainder F p + zeroSum F p

/-- The defect right of `Re p = -½`: the Euler factor is replaced by `ξ'/ξ - 1/s - Γℝ'/Γℝ` at
`s = ½ + p` and `L F · ξ'/ξ` is absorbed into the divided-difference sum. -/
def rightFormDefect (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  globalRemainder F 1 - levyRegularPart F p +
    negativeHalfLineLaplace (cx F) p * ((1 / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p)) +
    dividedSum F p

/-- The defect on the strip `-2 < Re p < ½`: the same with the reflected Euler factor at
`s = ½ - p`; the two charges become divided differences of the transform at `±½`. -/
def stripFormDefect (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  globalRemainder F 1 + dividedSum F p + dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p -
    negativeHalfLineLaplace (cx F) p * logDeriv Complex.Gammaℝ (1 / 2 - p) +
    dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2)) p - levyHeadTerm F p + stateTail F p

theorem rightFormDefect_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) < p.re) (hxi : xi (1 / 2 + p) ≠ 0) :
    rightFormDefect F p = explicitDefect F p := by
  have hg : globalRemainder F p = levyRemainder F p := by
    rw [globalRemainder, if_pos hp]
  unfold rightFormDefect explicitDefect
  rw [hg, levyRemainder_eq_add, logDeriv_zetaEntire_eq_xi (by rw [re_one_half_add]; linarith) hxi,
    zeroSum_eq_dividedSum_add hF hxi]
  ring

theorem stripFormDefect_eq_sub_stripRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : p.re < 1 / 2) (hxi : xi (1 / 2 + p) ≠ 0) :
    stripFormDefect F p = globalRemainder F 1 - stripRemainder F p + zeroSum F p := by
  have hne : p ≠ 1 / 2 := fun h => by
    rw [h, re_one_half] at hp
    exact lt_irrefl _ hp
  have hxi' : xi (1 / 2 - p) ≠ 0 := by
    rw [xi_half_sub_eq]
    exact hxi
  have hld : logDeriv xi (1 / 2 - p) = -logDeriv xi (1 / 2 + p) := by
    rw [show (1 : ℂ) / 2 - p = 1 - (1 / 2 + p) by ring, logDeriv_xi_one_sub]
  have hinv : ((1 : ℂ) / 2 - p)⁻¹ = -(p - 1 / 2)⁻¹ := by
    rw [show (1 : ℂ) / 2 - p = -(p - 1 / 2) by ring, inv_neg]
  unfold stripFormDefect stripRemainder
  rw [logDeriv_zetaEntire_eq_xi (by rw [re_one_half_sub]; linarith) hxi', hld, hinv,
    zeroSum_eq_dividedSum_add hF hxi, dslope_of_ne _ hne, slope_def_field]
  ring

/-- On `-4 < Re p < ½`, off the zeros, the remainder is its strip form. -/
theorem globalRemainder_eq_stripRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp4 : -4 < p.re) (hp : p.re < 1 / 2) (hxi : xi (1 / 2 + p) ≠ 0) :
    globalRemainder F p = stripRemainder F p := by
  rcases lt_trichotomy (-(1 / 2)) p.re with h1 | h1 | h1
  · have hre1 : 0 < ((1 : ℂ) / 2 + p).re := by rw [re_one_half_add]; linarith
    have hre2 : 0 < ((1 : ℂ) / 2 - p).re := by rw [re_one_half_sub]; linarith
    have hne1 : (1 : ℂ) / 2 + p ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [re_one_half_add, Complex.one_re] at this
      linarith
    have hne2 : (1 : ℂ) / 2 - p ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [re_one_half_sub, Complex.one_re] at this
      linarith
    have hζ1 : riemannZeta (1 / 2 + p) ≠ 0 := fun h =>
      hxi ((xi_eq_zero_iff_riemannZeta_of_re_pos hre1 hne1).mpr h)
    have hζ2 : riemannZeta (1 / 2 - p) ≠ 0 := fun h => by
      have h0 := (xi_eq_zero_iff_riemannZeta_of_re_pos hre2 hne2).mpr h
      rw [xi_half_sub_eq] at h0
      exact hxi h0
    rw [globalRemainder, if_pos h1]
    exact levyRemainder_eq_stripRemainder hF (abs_lt.mpr ⟨h1, hp⟩) hζ1 hζ2
  · rw [globalRemainder, if_neg (not_lt.mpr h1.symm.le), if_neg (not_lt.mpr h1.le)]
  · rw [globalRemainder, if_neg (not_lt.mpr h1.le), if_pos h1]
    exact (stripRemainder_eq_leftRemainder hF hp4 h1).symm

theorem stripFormDefect_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp4 : -4 < p.re) (hp : p.re < 1 / 2) (hxi : xi (1 / 2 + p) ≠ 0) :
    stripFormDefect F p = explicitDefect F p := by
  rw [stripFormDefect_eq_sub_stripRemainder hF hp hxi,
    ← globalRemainder_eq_stripRemainder hF hp4 hp hxi]
  rfl

/-! ### Holomorphy of the forms -/

theorem differentiableAt_laplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -4 < p.re) : DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) p := by
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential).differentiableAt
    (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))

theorem differentiableAt_dslope_laplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {a p : ℂ} (ha : -4 < a.re) (hp : -4 < p.re) :
    DifferentiableAt ℂ (dslope (negativeHalfLineLaplace (cx F)) a) p := by
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have ha4 : {p : ℂ | -(8 / 2) < p.re} ∈ 𝓝 a :=
    hopen4.mem_nhds (by show -(8 / 2) < a.re; linarith)
  exact ((differentiableOn_dslope ha4).mpr hLap).differentiableAt
    (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))

theorem differentiableAt_rightFormDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -(1 / 2) < p.re) : DifferentiableAt ℂ (rightFormDefect F) p := by
  have hre : 0 < ((1 : ℂ) / 2 + p).re := by rw [re_one_half_add]; linarith
  have hadd : DifferentiableAt ℂ (fun p : ℂ => (1 : ℂ) / 2 + p) p :=
    (differentiableAt_const _).add differentiableAt_id
  have hinv : DifferentiableAt ℂ (fun p : ℂ => ((1 : ℂ) / 2 + p)⁻¹) p :=
    hadd.inv fun h => by
      rw [h, Complex.zero_re] at hre
      exact lt_irrefl 0 hre
  have hG : DifferentiableAt ℂ (fun p : ℂ => logDeriv Complex.Gammaℝ (1 / 2 + p)) p :=
    (differentiableAt_logDeriv_Gammaℝ hre).comp p hadd
  show DifferentiableAt ℂ (fun p => globalRemainder F 1 - levyRegularPart F p +
    negativeHalfLineLaplace (cx F) p * ((1 / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p)) +
    dividedSum F p) p
  exact (((differentiableAt_const _).sub (differentiableAt_levyRegularPart hF hp)).add
    ((differentiableAt_laplace hF (by linarith)).mul (hinv.add hG))).add
    (differentiableAt_dividedSum hF (by linarith))

theorem differentiableAt_stripFormDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp2 : -2 < p.re) (hp : p.re < 1 / 2) :
    DifferentiableAt ℂ (stripFormDefect F) p := by
  have hre : 0 < ((1 : ℂ) / 2 - p).re := by rw [re_one_half_sub]; linarith
  have hsub : DifferentiableAt ℂ (fun p : ℂ => (1 : ℂ) / 2 - p) p :=
    (differentiableAt_const _).sub differentiableAt_id
  have hG : DifferentiableAt ℂ (fun p : ℂ => logDeriv Complex.Gammaℝ (1 / 2 - p)) p :=
    (differentiableAt_logDeriv_Gammaℝ hre).comp p hsub
  have hoJ : IsOpen {p : ℂ | p.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have hoT : IsOpen {p : ℂ | -4 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hJ : DifferentiableAt ℂ (levyHeadTerm F) p :=
    (differentiableOn_levyHeadTerm hF).differentiableAt (hoJ.mem_nhds hp)
  have hT : DifferentiableAt ℂ (stateTail F) p :=
    (differentiableOn_stateTail_strip hF).differentiableAt
      (hoT.mem_nhds (by show -4 < p.re; linarith))
  show DifferentiableAt ℂ (fun p => globalRemainder F 1 + dividedSum F p +
    dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p -
    negativeHalfLineLaplace (cx F) p * logDeriv Complex.Gammaℝ (1 / 2 - p) +
    dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2)) p - levyHeadTerm F p + stateTail F p) p
  exact ((((((differentiableAt_const _).add (differentiableAt_dividedSum hF hp2)).add
    (differentiableAt_dslope_laplace hF (by rw [re_one_half]; norm_num) (by linarith))).sub
    ((differentiableAt_laplace hF (by linarith)).mul hG)).add
    (differentiableAt_dslope_laplace hF (by rw [Complex.neg_re, re_one_half]; norm_num)
      (by linarith))).sub hJ).add hT

theorem differentiableAt_explicitDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : p.re < -(1 / 2)) : DifferentiableAt ℂ (explicitDefect F) p := by
  have hxi : xi (1 / 2 + p) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    have := neg_le_abs p.re
    linarith)
  show DifferentiableAt ℂ (fun p => globalRemainder F 1 - globalRemainder F p + zeroSum F p) p
  exact ((differentiableAt_const _).sub (differentiableAt_globalRemainder hF fun h => by
    linarith)).add (differentiableAt_zeroSum hF hxi)

/-! ### Gluing -/

/-- On the strip the two pole-free forms agree, zeros included: they agree off the zeros, which
are isolated, and both are continuous. -/
theorem rightFormDefect_eq_stripFormDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (h1 : -(1 / 2) < p.re) (h2 : p.re < 1 / 2) :
    rightFormDefect F p = stripFormDefect F p := by
  have hc1 := (differentiableAt_rightFormDefect hF h1).continuousAt
  have hc2 := (differentiableAt_stripFormDefect hF (by linarith) h2).continuousAt
  have ho : IsOpen {w : ℂ | -(1 / 2) < w.re ∧ w.re < 1 / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hopen : ∀ᶠ w in 𝓝[≠] p, -(1 / 2) < w.re ∧ w.re < 1 / 2 :=
    nhdsWithin_le_nhds (ho.mem_nhds ⟨h1, h2⟩)
  have hev : rightFormDefect F =ᶠ[𝓝[≠] p] stripFormDefect F := by
    filter_upwards [eventually_xi_half_add_ne_zero p, hopen] with w hw hre
    rw [rightFormDefect_eq hF hre.1 hw, stripFormDefect_eq hF (by linarith [hre.1]) hre.2 hw]
  exact tendsto_nhds_unique_of_eventuallyEq (hc1.tendsto.mono_left nhdsWithin_le_nhds)
    (hc2.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- The entire function carrying the defect: the right form right of `Re p = -½`, the defect itself
left of it, the strip form on the line. -/
def entireDefect (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  if -(1 / 2) < p.re then rightFormDefect F p
  else if p.re < -(1 / 2) then explicitDefect F p else stripFormDefect F p

theorem entireDefect_of_gt {F : ℝ → ℝ} {p : ℂ} (hp : -(1 / 2) < p.re) :
    entireDefect F p = rightFormDefect F p := by
  rw [entireDefect, if_pos hp]

theorem entireDefect_of_lt {F : ℝ → ℝ} {p : ℂ} (hp : p.re < -(1 / 2)) :
    entireDefect F p = explicitDefect F p := by
  rw [entireDefect, if_neg (not_lt.mpr hp.le), if_pos hp]

theorem entireDefect_eq_stripFormDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp2 : -2 < p.re) (hp : p.re < 1 / 2) : entireDefect F p = stripFormDefect F p := by
  rcases lt_trichotomy (-(1 / 2)) p.re with h | h | h
  · rw [entireDefect_of_gt h, rightFormDefect_eq_stripFormDefect hF h hp]
  · rw [entireDefect, if_neg (not_lt.mpr h.symm.le), if_neg (not_lt.mpr h.le)]
  · have hxi : xi (1 / 2 + p) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
      have := neg_le_abs p.re
      linarith)
    rw [entireDefect_of_lt h, stripFormDefect_eq hF (by linarith) hp hxi]

/-- Off the zeros the entire function is the defect. -/
theorem entireDefect_eq_explicitDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hxi : xi (1 / 2 + p) ≠ 0) : entireDefect F p = explicitDefect F p := by
  rcases lt_trichotomy (-(1 / 2)) p.re with h | h | h
  · rw [entireDefect_of_gt h, rightFormDefect_eq hF h hxi]
  · rw [entireDefect, if_neg (not_lt.mpr h.symm.le), if_neg (not_lt.mpr h.le)]
    exact stripFormDefect_eq hF (by linarith) (by linarith) hxi
  · exact entireDefect_of_lt h

/-- **The defect extends to an entire function.** -/
theorem differentiable_entireDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Differentiable ℂ (entireDefect F) := by
  intro p
  rcases lt_trichotomy (-(1 / 2)) p.re with h | h | h
  · have ho : IsOpen {w : ℂ | -(1 / 2) < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine (differentiableAt_rightFormDefect hF h).congr_of_eventuallyEq ?_
    filter_upwards [ho.mem_nhds h] with w hw
    exact entireDefect_of_gt hw
  · have ho : IsOpen {w : ℂ | -2 < w.re ∧ w.re < 1 / 2} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    refine (differentiableAt_stripFormDefect hF (by linarith) (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [ho.mem_nhds ⟨by linarith, by linarith⟩] with w hw
    exact entireDefect_eq_stripFormDefect hF hw.1 hw.2
  · have ho : IsOpen {w : ℂ | w.re < -(1 / 2)} := isOpen_lt Complex.continuous_re continuous_const
    refine (differentiableAt_explicitDefect hF h).congr_of_eventuallyEq ?_
    filter_upwards [ho.mem_nhds h] with w hw
    exact entireDefect_of_lt hw

/-! ### Growth -/

theorem one_le_one_add_norm_sq (p : ℂ) : 1 ≤ (1 + ‖p‖) ^ 2 := by
  nlinarith [norm_nonneg p]

theorem one_add_norm_le_sq (p : ℂ) : 1 + ‖p‖ ≤ (1 + ‖p‖) ^ 2 := by
  nlinarith [norm_nonneg p]

/-- The right form is `O(|p|²)` on `Re p ≥ 0`. -/
theorem exists_bound_rightFormDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, 0 ≤ p.re → ‖rightFormDefect F p‖ ≤ K * (1 + ‖p‖) ^ 2 := by
  obtain ⟨KR, hKR0, hR⟩ := exists_bound_levyRegularPart hF
  obtain ⟨CΓ, hCΓ0, hΓ⟩ := exists_bound_logDeriv_Gammaℝ
  have hm0 := halfPoleMass_nonneg F
  refine ⟨‖globalRemainder F 1‖ + KR + halfPoleMass F * (2 + 2 * CΓ) +
    4 * transformMass F (-3) * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2), fun p hp => ?_⟩
  have hpn := norm_nonneg p
  have hX2 := one_le_one_add_norm_sq p
  have hXX := one_add_norm_le_sq p
  have hR' := hR p hp
  have hL := norm_laplace_le_halfPoleMass hF (by linarith : -(1 / 2) ≤ p.re)
  have hΔ := norm_dividedSum_le hF (by linarith : -2 ≤ p.re)
  have hG := hΓ (1 / 2 + p) (by rw [re_one_half_add]; linarith)
  have hsn : ‖(1 : ℂ) / 2 + p‖ ≤ 1 + ‖p‖ := by
    have h := norm_add_le ((1 : ℂ) / 2) p
    rw [norm_half_one] at h
    linarith
  have hinv : ‖((1 : ℂ) / 2 + p)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have h := Complex.abs_re_le_norm ((1 : ℂ) / 2 + p)
    have h2 := le_abs_self (((1 : ℂ) / 2 + p).re)
    rw [re_one_half_add] at h h2
    have h3 : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) / 2 + p‖ := by linarith
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h3
    norm_num at this
    exact this
  have hbr : ‖((1 : ℂ) / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p)‖ ≤
      2 + CΓ * (2 + ‖p‖) :=
    (norm_add_le _ _).trans (add_le_add hinv (hG.trans
      (mul_le_mul_of_nonneg_left (by linarith) hCΓ0)))
  have hprod : ‖negativeHalfLineLaplace (cx F) p *
      (((1 : ℂ) / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p))‖ ≤
      halfPoleMass F * (2 + CΓ * (2 + ‖p‖)) := by
    rw [norm_mul]
    exact mul_le_mul hL hbr (norm_nonneg _) hm0
  have e : rightFormDefect F p = globalRemainder F 1 + -levyRegularPart F p +
      negativeHalfLineLaplace (cx F) p *
        (((1 : ℂ) / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p)) + dividedSum F p := by
    unfold rightFormDefect
    ring
  have h4 : ‖rightFormDefect F p‖ ≤ ‖globalRemainder F 1‖ + ‖levyRegularPart F p‖ +
      ‖negativeHalfLineLaplace (cx F) p *
        (((1 : ℂ) / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p))‖ + ‖dividedSum F p‖ := by
    rw [e]
    calc ‖globalRemainder F 1 + -levyRegularPart F p + negativeHalfLineLaplace (cx F) p *
            (((1 : ℂ) / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p)) + dividedSum F p‖
        ≤ ‖globalRemainder F 1‖ + ‖-levyRegularPart F p‖ + ‖negativeHalfLineLaplace (cx F) p *
            (((1 : ℂ) / 2 + p)⁻¹ + logDeriv Complex.Gammaℝ (1 / 2 + p))‖ + ‖dividedSum F p‖ :=
          norm_add₄_le
      _ = _ := by rw [norm_neg]
  have t1 : ‖globalRemainder F 1‖ ≤ ‖globalRemainder F 1‖ * (1 + ‖p‖) ^ 2 :=
    le_mul_of_one_le_right (norm_nonneg _) hX2
  have t2 : KR * (1 + ‖p‖) ≤ KR * (1 + ‖p‖) ^ 2 := mul_le_mul_of_nonneg_left hXX hKR0
  have t3 : halfPoleMass F * (2 + CΓ * (2 + ‖p‖)) ≤
      halfPoleMass F * (2 + 2 * CΓ) * (1 + ‖p‖) ^ 2 := by
    have h1 : 2 + CΓ * (2 + ‖p‖) ≤ (2 + 2 * CΓ) * (1 + ‖p‖) := by
      nlinarith [mul_nonneg hCΓ0 hpn]
    have h2 : (2 + 2 * CΓ) * (1 + ‖p‖) ≤ (2 + 2 * CΓ) * (1 + ‖p‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hXX (by linarith)
    calc halfPoleMass F * (2 + CΓ * (2 + ‖p‖))
        ≤ halfPoleMass F * ((2 + 2 * CΓ) * (1 + ‖p‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hm0
      _ = _ := by ring
  calc ‖rightFormDefect F p‖
      ≤ ‖globalRemainder F 1‖ + KR * (1 + ‖p‖) + halfPoleMass F * (2 + CΓ * (2 + ‖p‖)) +
          4 * transformMass F (-3) * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 := by
        linarith
    _ ≤ ‖globalRemainder F 1‖ * (1 + ‖p‖) ^ 2 + KR * (1 + ‖p‖) ^ 2 +
          halfPoleMass F * (2 + 2 * CΓ) * (1 + ‖p‖) ^ 2 +
          4 * transformMass F (-3) * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 := by
        linarith
    _ = _ := by ring

/-- The strip form is `O(|p|²)` on `-1 ≤ Re p ≤ 0`. -/
theorem exists_bound_stripFormDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, -1 ≤ p.re → p.re ≤ 0 → ‖stripFormDefect F p‖ ≤ K * (1 + ‖p‖) ^ 2 := by
  obtain ⟨CΓ, hCΓ0, hΓ⟩ := exists_bound_logDeriv_Gammaℝ
  obtain ⟨KJ, hJ⟩ := exists_bound_levyHeadTerm hF
  obtain ⟨KT, hT⟩ := exists_bound_stateTail hF
  have hKJ0 : 0 ≤ KJ := (norm_nonneg _).trans (hJ 0 (by simp))
  have hKT0 : 0 ≤ KT := (norm_nonneg _).trans (hT 0 (by simp))
  have hm3 := transformMass_nonneg F (-3)
  refine ⟨‖globalRemainder F 1‖ +
    4 * transformMass F (-3) * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) +
    2 * transformMass F (-3) + transformMass F (-3) * (2 * CΓ) + KJ + KT, fun p hp1 hp0 => ?_⟩
  have hpn := norm_nonneg p
  have hX2 := one_le_one_add_norm_sq p
  have hXX := one_add_norm_le_sq p
  have hΔ := norm_dividedSum_le hF (by linarith : -2 ≤ p.re)
  have hD1 := norm_dslope_laplace_le hF (a := 1 / 2) (p := p) (by rw [re_one_half]; norm_num)
    (by linarith)
  have hD2 := norm_dslope_laplace_le hF (a := -(1 / 2)) (p := p)
    (by rw [Complex.neg_re, re_one_half]; norm_num) (by linarith)
  have hL := norm_laplace_le_transformMass hF (σ := -3) (by norm_num) (by linarith : (-3 : ℝ) ≤ p.re)
  have hG := hΓ (1 / 2 - p) (by rw [re_one_half_sub]; linarith)
  have hsn : ‖(1 : ℂ) / 2 - p‖ ≤ 1 + ‖p‖ := by
    have h := norm_sub_le ((1 : ℂ) / 2) p
    rw [norm_half_one] at h
    linarith
  have hprod : ‖negativeHalfLineLaplace (cx F) p * logDeriv Complex.Gammaℝ (1 / 2 - p)‖ ≤
      transformMass F (-3) * (CΓ * (2 + ‖p‖)) := by
    rw [norm_mul]
    exact mul_le_mul hL (hG.trans (mul_le_mul_of_nonneg_left (by linarith) hCΓ0))
      (norm_nonneg _) hm3
  have hJ' := hJ p hp0
  have hT' := hT p hp1
  have h7 : ‖stripFormDefect F p‖ ≤ ‖globalRemainder F 1‖ + ‖dividedSum F p‖ +
      ‖dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p‖ +
      ‖negativeHalfLineLaplace (cx F) p * logDeriv Complex.Gammaℝ (1 / 2 - p)‖ +
      ‖dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2)) p‖ + ‖levyHeadTerm F p‖ +
      ‖stateTail F p‖ := by
    unfold stripFormDefect
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  have t1 : ‖globalRemainder F 1‖ ≤ ‖globalRemainder F 1‖ * (1 + ‖p‖) ^ 2 :=
    le_mul_of_one_le_right (norm_nonneg _) hX2
  have t2 : 2 * transformMass F (-3) ≤ 2 * transformMass F (-3) * (1 + ‖p‖) ^ 2 :=
    le_mul_of_one_le_right (by linarith) hX2
  have t3 : transformMass F (-3) * (CΓ * (2 + ‖p‖)) ≤
      transformMass F (-3) * (2 * CΓ) * (1 + ‖p‖) ^ 2 := by
    have h1 : CΓ * (2 + ‖p‖) ≤ 2 * CΓ * (1 + ‖p‖) := by nlinarith [mul_nonneg hCΓ0 hpn]
    have h2 : 2 * CΓ * (1 + ‖p‖) ≤ 2 * CΓ * (1 + ‖p‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hXX (by linarith)
    calc transformMass F (-3) * (CΓ * (2 + ‖p‖))
        ≤ transformMass F (-3) * (2 * CΓ * (1 + ‖p‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hm3
      _ = _ := by ring
  have t4 : KJ ≤ KJ * (1 + ‖p‖) ^ 2 := le_mul_of_one_le_right hKJ0 hX2
  have t5 : KT ≤ KT * (1 + ‖p‖) ^ 2 := le_mul_of_one_le_right hKT0 hX2
  calc ‖stripFormDefect F p‖
      ≤ ‖globalRemainder F 1‖ +
          4 * transformMass F (-3) * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 +
          2 * transformMass F (-3) + transformMass F (-3) * (CΓ * (2 + ‖p‖)) + KJ + KT := by
        linarith
    _ ≤ ‖globalRemainder F 1‖ * (1 + ‖p‖) ^ 2 +
          4 * transformMass F (-3) * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 +
          2 * transformMass F (-3) * (1 + ‖p‖) ^ 2 +
          transformMass F (-3) * (2 * CΓ) * (1 + ‖p‖) ^ 2 + KJ * (1 + ‖p‖) ^ 2 +
          KT * (1 + ‖p‖) ^ 2 := by
        linarith
    _ = _ := by ring

/-- The defect is `O(|p|²)` on `Re p ≤ -1`. -/
theorem exists_bound_explicitDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, p.re ≤ -1 → ‖explicitDefect F p‖ ≤ K * (1 + ‖p‖) ^ 2 := by
  obtain ⟨KL, hLft⟩ := exists_bound_leftRemainder hF
  have hKL0 : 0 ≤ KL := (norm_nonneg _).trans (hLft (-1) (by simp))
  refine ⟨‖globalRemainder F 1‖ + KL +
    6 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2), fun p hp => ?_⟩
  have hX2 := one_le_one_add_norm_sq p
  have hlt : p.re < -(1 / 2) := by linarith
  have hg : globalRemainder F p = leftRemainder F p := by
    rw [globalRemainder, if_neg (not_lt.mpr hlt.le), if_pos hlt]
  have hZ := norm_zeroSum_le hF (p := p) (by
    have := neg_le_abs p.re
    linarith)
  have hL' := hLft p hp
  have h3 : ‖explicitDefect F p‖ ≤ ‖globalRemainder F 1‖ + ‖leftRemainder F p‖ +
      ‖zeroSum F p‖ := by
    unfold explicitDefect
    rw [hg]
    exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have t1 : ‖globalRemainder F 1‖ ≤ ‖globalRemainder F 1‖ * (1 + ‖p‖) ^ 2 :=
    le_mul_of_one_le_right (norm_nonneg _) hX2
  have t2 : KL ≤ KL * (1 + ‖p‖) ^ 2 := le_mul_of_one_le_right hKL0 hX2
  calc ‖explicitDefect F p‖
      ≤ ‖globalRemainder F 1‖ * (1 + ‖p‖) ^ 2 + KL * (1 + ‖p‖) ^ 2 +
          6 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 := by
        linarith
    _ = _ := by ring

/-- **The entire defect is `O(|p|²)` in the plane.** -/
theorem exists_bound_entireDefect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, ‖entireDefect F p‖ ≤ K * (1 + ‖p‖) ^ 2 := by
  obtain ⟨K₁, h₁⟩ := exists_bound_rightFormDefect hF
  obtain ⟨K₂, h₂⟩ := exists_bound_stripFormDefect hF
  obtain ⟨K₃, h₃⟩ := exists_bound_explicitDefect hF
  refine ⟨|K₁| + |K₂| + |K₃|, fun p => ?_⟩
  have hX : 0 ≤ (1 + ‖p‖) ^ 2 := sq_nonneg _
  have e₁ := mul_le_mul_of_nonneg_right (le_abs_self K₁) hX
  have e₂ := mul_le_mul_of_nonneg_right (le_abs_self K₂) hX
  have e₃ := mul_le_mul_of_nonneg_right (le_abs_self K₃) hX
  have a₁ := mul_nonneg (abs_nonneg K₁) hX
  have a₂ := mul_nonneg (abs_nonneg K₂) hX
  have a₃ := mul_nonneg (abs_nonneg K₃) hX
  have hsum : (|K₁| + |K₂| + |K₃|) * (1 + ‖p‖) ^ 2 =
      |K₁| * (1 + ‖p‖) ^ 2 + |K₂| * (1 + ‖p‖) ^ 2 + |K₃| * (1 + ‖p‖) ^ 2 := by ring
  rw [hsum]
  rcases le_or_gt 0 p.re with h0 | h0
  · rw [entireDefect_of_gt (by linarith)]
    have := h₁ p h0
    linarith
  · rcases le_or_gt (-1) p.re with h1 | h1
    · rw [entireDefect_eq_stripFormDefect hF (by linarith) (by linarith)]
      have := h₂ p h1 h0.le
      linarith
    · rw [entireDefect_of_lt (by linarith)]
      have := h₃ p h1.le
      linarith

/-! ### Liouville -/

theorem zeroSum_one (F : ℝ → ℝ) : zeroSum F 1 = 0 := by
  unfold zeroSum
  simp

theorem entireDefect_one {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    entireDefect F 1 = 0 := by
  have hre : -(1 / 2) < (1 : ℂ).re := by
    rw [Complex.one_re]
    norm_num
  have hxi : xi (1 / 2 + 1) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    rw [Complex.one_re, abs_one]
    norm_num)
  rw [entireDefect_of_gt hre, rightFormDefect_eq hF hre hxi]
  unfold explicitDefect
  rw [zeroSum_one]
  ring

/-- **The defect vanishes identically.** Its divided difference at `1`, reflected, is entire of
polynomial growth and tends to zero along the positive integers: the remainder is bounded on the
left and the zero sum is `o(|p|)` there. -/
theorem entireDefect_eq_zero {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (p : ℂ) :
    entireDefect F p = 0 := by
  have hE := differentiable_entireDefect hF
  have hE1 := entireDefect_one hF
  obtain ⟨K, hK⟩ := exists_bound_entireDefect hF
  obtain ⟨KL, hLft⟩ := exists_bound_leftRemainder hF
  have hD : Differentiable ℂ (dslope (entireDefect F) 1) := _root_.HTGeometry.differentiable_entire_dslope hE 1
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  have hre : ∀ n : ℕ, (-((n : ℂ) + 1)).re = -((n : ℝ) + 1) := fun n => by simp
  have hden : ∀ n : ℕ, (1 : ℂ) - -((n : ℂ) + 1) = (((n : ℝ) + 2 : ℝ) : ℂ) := fun n => by
    push_cast
    ring
  -- the remainder part of the quotient tends to zero
  have hf : Tendsto (fun n : ℕ => (globalRemainder F 1 - leftRemainder F (-((n : ℂ) + 1))) /
      (1 - -((n : ℂ) + 1))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => (‖globalRemainder F 1‖ + KL) *
      ((n : ℝ) + 2)⁻¹) (fun n => ?_) ?_
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hl := hLft (-((n : ℂ) + 1)) (by rw [hre]; linarith)
      rw [norm_div, hden, Complex.norm_real, Real.norm_of_nonneg (by linarith), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith))
        (inv_nonneg.mpr (by linarith))
    · have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      simpa using h0.const_mul (‖globalRemainder F 1‖ + KL)
  have hsum : Tendsto (fun n : ℕ => -((globalRemainder F 1 - leftRemainder F (-((n : ℂ) + 1))) /
      (1 - -((n : ℂ) + 1)) + zeroSum F (-((n : ℂ) + 1)) / (1 - -((n : ℂ) + 1)))) atTop (𝓝 0) := by
    have h := (hf.add (tendsto_zeroSum_div hF)).neg
    rwa [add_zero, neg_zero] at h
  -- the divided difference along the negative integers
  have hpt : ∀ n : ℕ, dslope (entireDefect F) 1 (-((n : ℂ) + 1)) =
      -((globalRemainder F 1 - leftRemainder F (-((n : ℂ) + 1))) / (1 - -((n : ℂ) + 1)) +
        zeroSum F (-((n : ℂ) + 1)) / (1 - -((n : ℂ) + 1))) := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hne : -((n : ℂ) + 1) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [hre, Complex.one_re] at this
      linarith
    have hlt : (-((n : ℂ) + 1)).re < -(1 / 2) := by
      rw [hre]
      linarith
    have hg : globalRemainder F (-((n : ℂ) + 1)) = leftRemainder F (-((n : ℂ) + 1)) := by
      rw [globalRemainder, if_neg (not_lt.mpr hlt.le), if_pos hlt]
    have hd' : -((n : ℂ) + 1) - 1 = -(1 - -((n : ℂ) + 1)) := by ring
    rw [dslope_of_ne _ hne, slope_def_field, hE1, sub_zero, entireDefect_of_lt hlt]
    unfold explicitDefect
    rw [hg, hd', div_neg, add_div]
  have hH : ∀ z : ℂ, dslope (entireDefect F) 1 (-z) = 0 := by
    refine eq_zero_of_polyGrowth_of_tendsto_nat (F := fun z => dslope (entireDefect F) 1 (-z))
      (hD.comp differentiable_id.neg) ⟨|C₀| + |K|, 2, fun z => ?_⟩ ?_
    · show ‖dslope (entireDefect F) 1 (-z)‖ ≤ (|C₀| + |K|) * (1 + ‖z‖) ^ 2
      have hX1 := one_le_one_add_norm_sq z
      have a1 := abs_nonneg C₀
      have a2 := abs_nonneg K
      have hsplit : (|C₀| + |K|) * (1 + ‖z‖) ^ 2 =
          |C₀| * (1 + ‖z‖) ^ 2 + |K| * (1 + ‖z‖) ^ 2 := by ring
      have b1 : |C₀| ≤ |C₀| * (1 + ‖z‖) ^ 2 := le_mul_of_one_le_right a1 hX1
      have b2 : 0 ≤ |K| * (1 + ‖z‖) ^ 2 := mul_nonneg a2 (sq_nonneg _)
      have b3 : K * (1 + ‖z‖) ^ 2 ≤ |K| * (1 + ‖z‖) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
      have b4 : 0 ≤ |C₀| * (1 + ‖z‖) ^ 2 := mul_nonneg a1 (sq_nonneg _)
      rw [hsplit]
      rcases le_or_gt ‖-z - 1‖ 1 with hnear | hfar
      · have h := hC₀ (-z) (by rw [mem_closedBall, dist_eq_norm]; exact hnear)
        have := le_abs_self C₀
        linarith
      · have hne : -z ≠ 1 := fun h => by
          rw [h, sub_self, norm_zero] at hfar
          linarith
        rw [dslope_of_ne _ hne, slope_def_field, hE1, sub_zero, norm_div]
        have hk := hK (-z)
        rw [norm_neg] at hk
        have h1 : ‖entireDefect F (-z)‖ / ‖-z - 1‖ ≤ ‖entireDefect F (-z)‖ :=
          div_le_self (norm_nonneg _) hfar.le
        linarith
    · exact Tendsto.congr (fun n => (hpt n).symm) hsum
  rcases eq_or_ne p 1 with rfl | hp1
  · exact hE1
  · have h := hH (-p)
    rw [neg_neg, dslope_of_ne _ hp1, slope_def_field, hE1, sub_zero, div_eq_zero_iff] at h
    exact h.resolve_right (sub_ne_zero.mpr hp1)

/-! ### The explicit formula -/

/-- **The explicit formula on the energy domain against probes.** For every profile of the domain
and every `p` with `ξ(½ + p) ≠ 0`,
`B F(p) - B F(1) = Σ_z L F(z) (1/(p - z) - 1/(1 - z))`. -/
theorem globalRemainder_sub_eq_zeroSum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : xi (1 / 2 + p) ≠ 0) : globalRemainder F p - globalRemainder F 1 = zeroSum F p := by
  have h0 := entireDefect_eq_zero hF p
  rw [entireDefect_eq_explicitDefect hF hp] at h0
  unfold explicitDefect at h0
  linear_combination -h0

/-- **Two-point form.** `B F(p) - B F(q) = Σ_z L F(z) (1/(p - z) - 1/(q - z))` off the zeros. -/
theorem globalRemainder_sub_eq_tsum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p q : ℂ}
    (hp : xi (1 / 2 + p) ≠ 0) (hq : xi (1 / 2 + q) ≠ 0) :
    globalRemainder F p - globalRemainder F q =
      ∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((p - centredZero c)⁻¹ - (q - centredZero c)⁻¹) := by
  obtain ⟨δ, hδ, hb⟩ := exists_zeroFree_ball hp
  obtain ⟨ε, hε, hb'⟩ := exists_zeroFree_ball hq
  have sp := summable_zeroSum_term hF hδ (hb p (mem_ball_self hδ))
  have sq := summable_zeroSum_term hF hε (hb' q (mem_ball_self hε))
  have h1 := globalRemainder_sub_eq_zeroSum hF hp
  have h2 := globalRemainder_sub_eq_zeroSum hF hq
  have h3 : globalRemainder F p - globalRemainder F q = zeroSum F p - zeroSum F q := by
    rw [← h1, ← h2]
    ring
  rw [h3]
  unfold zeroSum
  rw [← sp.tsum_sub sq]
  refine tsum_congr fun c => ?_
  ring

/-! ### The critical state -/

/-- The continuation of a profile's state transform obeys the subtracted Cauchy formula. -/
theorem stateMeromorphic_sub_eq {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ} (hw : xi (1 / 2 + (w + 8)) ≠ 0) :
    (criticalAliasCoefficient W₀ : ℂ) *
        (stateMeromorphic W₀ F w - stateMeromorphic W₀ F (-7)) = -zeroSum F (w + 8) := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have h := globalRemainder_sub_eq_zeroSum hF hw
  unfold stateMeromorphic
  rw [show (-7 : ℂ) + 8 = 1 by norm_num, ← h]
  field_simp
  ring

/-- **(★): the state is the Cauchy transform of its own values at the zeros.** For `Re w, Re v > -4`,
`a (L F(w) - L F(v)) = -Σ_z L F(z) (1/(w + 8 - z) - 1/(v + 8 - z))`. -/
theorem criticalState_starEquation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w v : ℂ} (hw : -4 < w.re)
    (hv : -4 < v.re) :
    (criticalAliasCoefficient W₀ : ℂ) *
        (negativeHalfLineLaplace (cx F) w - negativeHalfLineLaplace (cx F) v) =
      -∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((w + 8 - centredZero c)⁻¹ - (v + 8 - centredZero c)⁻¹) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have key : ∀ u : ℂ, -4 < u.re → (criticalAliasCoefficient W₀ : ℂ) *
      negativeHalfLineLaplace (cx F) u = -globalRemainder F (u + 8) := by
    intro u hu
    have h1 := levyContinuation_eq_laplace hW hthreshold hF hu
    have h2 := stateMeromorphic_eq_levyContinuation (W₀ := W₀) (F := F) (w := u) (by linarith)
    rw [← h1, ← h2]
    unfold stateMeromorphic
    field_simp
  have hxi : ∀ u : ℂ, -4 < u.re → xi (1 / 2 + (u + 8)) ≠ 0 := fun u hu =>
    xi_ne_zero_of_half_le_abs_re (by
      have h8 : (u + 8).re = u.re + 8 := by simp
      rw [h8]
      have := le_abs_self (u.re + 8)
      linarith)
  have hmain := globalRemainder_sub_eq_tsum hd (hxi w hw) (hxi v hv)
  have k1 := key w hw
  have k2 := key v hv
  linear_combination k1 - k2 - hmain

/-- The values of the state at the zeros solve a Cauchy system: for zero copies `c₁, c₂`,
`a (L F(z₁) - L F(z₂)) = -Σ_z L F(z) (1/(8 + z₁ - z) - 1/(8 + z₂ - z))`. -/
theorem criticalState_zeroValues_cauchy {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (c₁ c₂ : XiZeroCopy) :
    (criticalAliasCoefficient W₀ : ℂ) *
        (negativeHalfLineLaplace (cx F) (centredZero c₁) -
          negativeHalfLineLaplace (cx F) (centredZero c₂)) =
      -∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((centredZero c₁ + 8 - centredZero c)⁻¹ - (centredZero c₂ + 8 - centredZero c)⁻¹) :=
  criticalState_starEquation hW hthreshold hF
    (by have := (abs_lt.mp (abs_re_centredZero_lt c₁)).1; linarith)
    (by have := (abs_lt.mp (abs_re_centredZero_lt c₂)).1; linarith)

/-- **Either RH holds, or the critical state exists and is the Cauchy transform of its own values
at the zeros.** -/
theorem riemannHypothesis_or_criticalState_starEquation :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        ∀ w v : ℂ, -4 < w.re → -4 < v.re →
          (criticalAliasCoefficient W₀ : ℂ) *
              (negativeHalfLineLaplace (cx F) w - negativeHalfLineLaplace (cx F) v) =
            -∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
              ((w + 8 - centredZero c)⁻¹ - (v + 8 - centredZero c)⁻¹) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, fun w v hw hv => criticalState_starEquation hW ht hF hw hv⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
