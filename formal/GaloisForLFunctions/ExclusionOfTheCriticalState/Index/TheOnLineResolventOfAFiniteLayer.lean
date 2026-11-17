import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheSecondCriticalState
import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeSideBeyondTheWallIsTheDefectOfTheTranslatedState
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineVariationalCompactness

/-!
# Individual beyond-the-wall continuation, domain-wide zero Parseval, and the on-line resolvent

This module establishes four unconditional results on the half-line energy domain
`CriticalHalfLineEnergyDomain`:

1. **Exact individual profile criterion for beyond-the-wall continuation
   (`hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros`,
   `purePrimeHeadContinuation_profile_iff_vanish_leftZeros`).**
   For every profile `F` in the energy domain, `Φ_F(p) = primeHead F p + L F(-½)/(p + ½)` extends
   holomorphically from `Re p < -½` to `Re p < 0` (`HasBeyondTheWallPrimeContinuation F`) if and
   only if `L F(z) = 0` at every left-of-line centred zero `z` of `ζ` (`Re z < 0`), without any
   simplicity or finiteness assumption: because `ξ'/ξ` has only first-order poles, vanishing of
   `L F(z)` preserves the full multiplicity `ord_{½+z}(ξ)` in `clearedRemainder F`.

2. **Domain-wide zero Parseval and polarized Krein decomposition under `FiniteOffLine`
   (`domain_zeroParseval_of_finiteOffLine`, `bareMixedEnergy_eq_onLine_add_offLine_of_finiteOffLine`,
   `bareMixedEnergy_nonneg_of_hasBeyondTheWallPrimeContinuation`).**
   Under `FiniteOffLine`, every profile `G` in the energy domain has square-summable on-line zero
   values, and Weil's bare mixed form splits across all `F, G` in the energy domain into the
   Hermitian on-line pairing plus the finite off-line pairing. In particular, every profile satisfying
   `HasBeyondTheWallPrimeContinuation` has nonnegative bare Weil energy `B(G, G) ≥ 0`.

3. **Transfer of the Birman–Schwinger on-line resolvent to `ζ` on the energy domain
   (`exists_zetaOnLineResolvent`, `solvesZetaOnLineResolvent_ae_unique`,
   `nullVector_ae_eq_offLineResolvent_of_finiteOffLine`).**
   Under `FiniteOffLine`, for every `a > 0` and every `W₈`-square-integrable half-line target `y`,
   variational minimization on the energy domain produces an a.e.-unique profile `X` solving
   `onLineMixed X G + a W₈(X, G) = W₈(y, G)` for all `G` in the energy domain. Every confined null
   vector `(R, F)` (`R > 0`, `a = a(R)`) equals almost everywhere a finite linear combination of the
   mode resolvents attached to the off-line centred zeros.

4. **General null-vector translation defect and cross-rung wall law
   (`nullVector_bareMixedEnergy_translate`, `nullVector_crossWallLaw`,
   `nullVector_diagonalWallLaw`).**
   Extending the translated-state defect from ground states to arbitrary confined null vectors yields
   both the diagonal wall law and the cross-rung wall law between any two confined null vectors
   `(R₁, F₁)` and `(R₂, F₂)`.
-/

noncomputable section

open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### 1. Exact individual profile criterion for beyond-the-wall prime continuation -/

/-- Meromorphic quotient `clearedRemainder F p / ξ(½ + p)` extended across removable singularities by
its punctured limit. -/
def extendedGlobalRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  if xi (1 / 2 + p) ≠ 0 then clearedRemainder F p / xi (1 / 2 + p)
  else limUnder (𝓝[≠] p) fun w => clearedRemainder F w / xi (1 / 2 + w)

private theorem differentiableAt_extendedGlobalRemainder_of_order_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z₀ : ℂ}
    (hord : analyticOrderAt (fun p : ℂ => xi (1 / 2 + p)) z₀ ≤
      analyticOrderAt (clearedRemainder F) z₀) :
    DifferentiableAt ℂ (extendedGlobalRemainder F) z₀ := by
  set f : ℂ → ℂ := fun p => xi (1 / 2 + p)
  set g : ℂ → ℂ := clearedRemainder F
  have hf : AnalyticAt ℂ f z₀ := differentiable_xi_half_add.analyticAt z₀
  have hg : AnalyticAt ℂ g z₀ := (differentiable_clearedRemainder hF).analyticAt z₀
  have hf_ne_top : analyticOrderAt f z₀ ≠ ⊤ := by
    have hcomp : analyticOrderAt f z₀ = analyticOrderAt xi (1 / 2 + z₀) := by
      apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun p : ℂ => 1 / 2 + p)
        (by fun_prop)
      simp
    rw [hcomp]
    exact xi_order_ne_top _
  set m : ℕ := analyticOrderNatAt f z₀
  obtain ⟨f₁, hf₁_an, hf₁_ne, hf_eq⟩ := hf.analyticOrderAt_ne_top.mp hf_ne_top
  have hm_le : (m : ℕ∞) ≤ analyticOrderAt g z₀ := by
    rwa [Nat.cast_analyticOrderNatAt hf_ne_top]
  obtain ⟨g₁, hg₁_an, hg_eq⟩ := (natCast_le_analyticOrderAt hg).mp hm_le
  set h : ℂ → ℂ := fun w => g₁ w / f₁ w
  have hh_an : AnalyticAt ℂ h z₀ := hg₁_an.div hf₁_an hf₁_ne
  have hf₁_nhds : ∀ᶠ w in 𝓝 z₀, f₁ w ≠ 0 := hf₁_an.continuousAt.eventually_ne hf₁_ne
  have hpunc : ∀ᶠ w in 𝓝[≠] z₀, f w ≠ 0 ∧ g w / f w = h w := by
    filter_upwards [self_mem_nhdsWithin, hf_eq.filter_mono nhdsWithin_le_nhds,
      hg_eq.filter_mono nhdsWithin_le_nhds, hf₁_nhds.filter_mono nhdsWithin_le_nhds]
      with w hw hfw hgw hf₁w
    have hpow : (w - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hw)
    simp only [smul_eq_mul] at hfw hgw
    refine ⟨by rw [hfw]; exact mul_ne_zero hpow hf₁w, ?_⟩
    rw [hgw, hfw, mul_div_mul_left _ _ hpow]
  have hlim : limUnder (𝓝[≠] z₀) (fun w => g w / f w) = h z₀ := by
    refine Tendsto.limUnder_eq ?_
    exact hh_an.continuousAt.continuousWithinAt.tendsto.congr'
      (hpunc.mono fun w hw => hw.2.symm)
  have hev_eq : extendedGlobalRemainder F =ᶠ[𝓝 z₀] h := by
    by_cases hfz₀ : f z₀ ≠ 0
    · have hf_nhds : ∀ᶠ w in 𝓝 z₀, f w ≠ 0 := hf.continuousAt.eventually_ne hfz₀
      filter_upwards [hf_eq, hg_eq, hf₁_nhds, hf_nhds] with w hfw hgw hf₁w hfw_ne
      simp only [extendedGlobalRemainder, if_pos hfw_ne]
      simp only [smul_eq_mul] at hfw hgw
      have hpow : (w - z₀) ^ m ≠ 0 := fun hp0 => hfw_ne (by rw [hfw, hp0, zero_mul])
      change g w / f w = h w
      rw [hgw, hfw, mul_div_mul_left _ _ hpow]
    · push Not at hfz₀
      obtain ⟨U, hU_sub, hU_open, hz₀U⟩ := eventually_nhds_iff.mp
        (hf_eq.and (hg_eq.and hf₁_nhds))
      refine eventually_nhds_iff.mpr ⟨U, fun w hw => ?_, hU_open, hz₀U⟩
      by_cases hwz : w = z₀
      · subst hwz
        simp only [extendedGlobalRemainder, if_neg (not_not.mpr hfz₀)]
        exact hlim
      · obtain ⟨hfw, hgw, hf₁w⟩ := hU_sub w hw
        simp only [smul_eq_mul] at hfw hgw
        have hpow : (w - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hwz)
        have hfw_ne : f w ≠ 0 := by rw [hfw]; exact mul_ne_zero hpow hf₁w
        simp only [extendedGlobalRemainder, if_pos hfw_ne]
        change g w / f w = h w
        rw [hgw, hfw, mul_div_mul_left _ _ hpow]
  exact hh_an.differentiableAt.congr_of_eventuallyEq hev_eq

/-- **Exact individual profile criterion for `E-Q1`.** For every profile `F` in the half-line energy
domain, `Φ_F(p) = primeHead F p + L F(-½)/(p + ½)` extends holomorphically from `Re p < -½` to
`Re p < 0` if and only if `L F(z) = 0` at every left-of-line centred zero `z` of `ζ`. -/
theorem hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    HasBeyondTheWallPrimeContinuation F ↔
      ∀ q : XiZeroCopy, (centredZero q).re < 0 →
        negativeHalfLineLaplace (cx F) (centredZero q) = 0 := by
  constructor
  · intro hcont q hq
    by_contra hL
    exact not_wallPrimeBalance_continues_of_seen_zero hF (by norm_num : (0 : ℝ) ≤ 5 / 2) hq hL hcont
  · intro hvan
    refine ⟨fun p => extendedGlobalRemainder F p - archimedeanWallTail F p,
      fun p hp => ?_, fun p hp => ?_⟩
    · have hp' : p.re < 0 := hp
      have hdiff_ext : DifferentiableAt ℂ (extendedGlobalRemainder F) p := by
        by_cases hxi : xi (1 / 2 + p) = 0
        · obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
          have hzc : centredZero q = p := by rw [centredZero, hq]; ring
          have hLp : negativeHalfLineLaplace (cx F) p = 0 := by
            rw [← hzc]
            exact hvan q (by rwa [hzc])
          have hord := le_analyticOrderAt_clearedRemainder_of_laplace_eq_zero hF hxi hLp
          have hcomp : analyticOrderAt (fun w : ℂ => xi (1 / 2 + w)) p =
              analyticOrderAt xi (1 / 2 + p) := by
            apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun w : ℂ => 1 / 2 + w)
              (by fun_prop)
            simp
          exact differentiableAt_extendedGlobalRemainder_of_order_le hF (by rwa [hcomp])
        · have hord0 : analyticOrderAt (fun w : ℂ => xi (1 / 2 + w)) p = 0 :=
            (differentiable_xi_half_add.analyticAt p).analyticOrderAt_eq_zero.mpr hxi
          exact differentiableAt_extendedGlobalRemainder_of_order_le hF (by rw [hord0]; exact zero_le _)
      have hdiff_arch : DifferentiableAt ℂ (archimedeanWallTail F) p :=
        (differentiableOn_archimedeanWallTail hF).differentiableAt
          ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by linarith : p.re < 5 / 2))
      exact (hdiff_ext.sub hdiff_arch).differentiableWithinAt
    · have hp' : p.re < -(1 / 2) := hp
      have hxi_ne : xi (1 / 2 + p) ≠ 0 :=
        xi_ne_zero_of_half_le_abs_re (by have := neg_le_abs p.re; linarith)
      dsimp only
      rw [extendedGlobalRemainder, if_pos hxi_ne, ← clearedRemainder_eq hF hxi_ne,
        globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance hF hp']
      ring

/-- **Pole-neutral individual profile criterion.** For any pole-neutral profile `G` (`L G(-½) = 0`),
the bare prime-head series `primeHead G` extends holomorphically from `Re p < -½` to `Re p < 0` if
and only if `L G(z) = 0` at every left-of-line centred zero `z` of `ζ`. -/
theorem purePrimeHeadContinuation_profile_iff_vanish_leftZeros {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G)
    (hpole : negativeHalfLineLaplace (cx G) (-(1 / 2)) = 0) :
    (∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < 0} ∧
      EqOn H (primeHead G) {p : ℂ | p.re < -(1 / 2)}) ↔
      ∀ q : XiZeroCopy, (centredZero q).re < 0 →
        negativeHalfLineLaplace (cx G) (centredZero q) = 0 := by
  have hbal : wallPrimeBalance G = primeHead G := by
    funext p; simp [wallPrimeBalance, hpole]
  rw [← hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros hG]
  unfold HasBeyondTheWallPrimeContinuation
  rw [hbal]

/-- Under `FiniteOffLine`, `HasBeyondTheWallPrimeContinuation F` holds if and only if `L F` vanishes
on the finite set `upperLeftCentredZeros hfin`. -/
theorem hasBeyondTheWallPrimeContinuation_iff_vanish_upperLeft_of_finiteOffLine
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hfin : BacklundConverse.FiniteOffLine) :
    HasBeyondTheWallPrimeContinuation F ↔
      ∀ z ∈ upperLeftCentredZeros hfin, negativeHalfLineLaplace (cx F) z = 0 := by
  rw [hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros hF]
  constructor
  · intro h z hz
    have hmem : z ∈ leftCentredZeros hfin := (Finset.mem_filter.mp hz).1
    obtain ⟨hz_neg, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hmem
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hzc : centredZero q = z := by rw [centredZero, hq]; ring
    rw [← hzc]
    exact h q (by rwa [hzc])
  · intro h q hq
    set z := centredZero q
    have hxi : xi (1 / 2 + z) = 0 := xi_centredZero q
    have him_ne : z.im ≠ 0 := xi_half_add_im_ne_zero hxi
    rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
    · have hcz_mem : conj z ∈ upperLeftCentredZeros hfin := by
        rw [upperLeftCentredZeros, Finset.mem_filter, mem_leftCentredZeros_iff]
        refine ⟨⟨by simpa using hq, ?_⟩, by simpa using him_neg⟩
        have hc : (1 : ℂ) / 2 + conj z = conj (1 / 2 + z) := by simp
        rw [hc, xi_conj, hxi, map_zero]
      have hcz := h (conj z) hcz_mem
      have hreal : negativeHalfLineLaplace (cx F) (conj z) =
          conj (negativeHalfLineLaplace (cx F) z) := by
        simpa [cx] using negativeHalfLineLaplace_real_conj F z
      rw [hreal] at hcz
      exact conj_eq_zero.mp hcz
    · exact h z (Finset.mem_filter.mpr ⟨(mem_leftCentredZeros_iff hfin).mpr ⟨hq, hxi⟩, him_pos⟩)

/-! ### 2. Domain-wide zero Parseval and polarized Krein decomposition under `FiniteOffLine` -/

private theorem norm_cexp_eps_centredZero_sq_le {ε : ℝ} (hε : 0 < ε) (q : XiZeroCopy) :
    ‖Complex.exp ((ε : ℂ) * centredZero q ^ 2)‖ ≤
      (Real.exp (ε / 2) / ε) * ‖centredZero q‖⁻¹ ^ 2 := by
  set z := centredZero q
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (centredZero_ne_zero q)
  have hzre : |z.re| ≤ 1 / 2 := (abs_re_centredZero_lt q).le
  have hre_sq : z.re ^ 2 ≤ 1 / 4 := by
    have h1 := sq_le_sq.mpr (by simpa using hzre : |z.re| ≤ |1 / 2|)
    linarith
  have hnorm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := Complex.sq_norm z
  have hexp_re : ((ε : ℂ) * z ^ 2).re = ε * (z.re ^ 2 - z.im ^ 2) := by
    simp [sq, Complex.mul_re]
    ring
  have hdiff : z.re ^ 2 - z.im ^ 2 ≤ 1 / 2 - ‖z‖ ^ 2 := by linarith
  have hexp1 : Real.exp (ε * (z.re ^ 2 - z.im ^ 2)) ≤
      Real.exp (ε / 2) * (Real.exp (ε * ‖z‖ ^ 2))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp2 : ε * ‖z‖ ^ 2 ≤ Real.exp (ε * ‖z‖ ^ 2) := by
    linarith [Real.add_one_le_exp (ε * ‖z‖ ^ 2)]
  rw [Complex.norm_exp, hexp_re]
  calc Real.exp (ε * (z.re ^ 2 - z.im ^ 2))
      ≤ Real.exp (ε / 2) * (Real.exp (ε * ‖z‖ ^ 2))⁻¹ := hexp1
    _ ≤ Real.exp (ε / 2) * (ε * ‖z‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hexp2) (Real.exp_pos _).le
    _ = (Real.exp (ε / 2) / ε) * ‖z‖⁻¹ ^ 2 := by
        rw [mul_inv, inv_pow, div_eq_mul_inv]; ring

/-- Uniform strip bound `‖L G(z_q)‖ ≤ C_G` across all `q : XiZeroCopy` for any `G` in the domain. -/
theorem norm_laplace_pos_centredZero_le {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (q : XiZeroCopy) :
    ‖negativeHalfLineLaplace (cx G) (centredZero q)‖ ≤
      ((∫ u : ℝ, G u ^ 2 * Real.exp (-(8 * u))) + ∫ u : ℝ, probe 1 u) / 2 := by
  have hzre : -(1 / 2 : ℝ) < (centredZero q).re := (abs_lt.mp (abs_re_centredZero_lt q)).1
  have hdom : Integrable fun u : ℝ => (G u ^ 2 * Real.exp (-(8 * u)) + probe 1 u) / 2 :=
    (hG.exponential.add (integrable_probe one_pos)).div_const 2
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall fun u => ?_)).trans_eq
    (by rw [integral_div, integral_add hG.exponential (integrable_probe one_pos)])
  rcases lt_or_ge u 0 with hu | hu
  · rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.norm_real, Real.norm_eq_abs, probe_of_neg hu]
    have hsplit : Real.exp ((centredZero q).re * u) =
        Real.exp (-(4 * u)) * Real.exp (((centredZero q).re + 4) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : Real.exp (((centredZero q).re + 4) * u) ≤ Real.exp ((1 / 2) * u) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (by linarith : (1 / 2 : ℝ) ≤ (centredZero q).re + 4) hu.le)
    have hsq_G : (|G u| * Real.exp (-(4 * u))) ^ 2 = G u ^ 2 * Real.exp (-(8 * u)) := by
      rw [mul_pow, sq_abs, sq (Real.exp (-(4 * u))), ← Real.exp_add]; congr 2; ring
    have hsq_exp : Real.exp ((1 / 2) * u) ^ 2 = Real.exp (1 * u) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h1 : Real.exp ((centredZero q).re * u) * |G u| ≤
        (|G u| * Real.exp (-(4 * u))) * Real.exp ((1 / 2) * u) := by
      rw [hsplit, show Real.exp (-(4 * u)) * Real.exp (((centredZero q).re + 4) * u) * |G u| =
        (|G u| * Real.exp (-(4 * u))) * Real.exp (((centredZero q).re + 4) * u) by ring]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    nlinarith [sq_nonneg (|G u| * Real.exp (-(4 * u)) - Real.exp ((1 / 2) * u)),
      hsq_G, hsq_exp, h1]
  · simp [cx, hG.support u hu, probe_of_nonneg hu]

/-- Uniform strip bound `‖L G(-z_q)‖ ≤ C_G` across all `q : XiZeroCopy` for any `G` in the domain. -/
theorem norm_laplace_neg_centredZero_le_domain {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (q : XiZeroCopy) :
    ‖negativeHalfLineLaplace (cx G) (-centredZero q)‖ ≤
      ((∫ u : ℝ, G u ^ 2 * Real.exp (-(8 * u))) + ∫ u : ℝ, probe 1 u) / 2 := by
  set r := xiZeroCopyReflectEquiv q
  have hr : centredZero r = -centredZero q := by
    simp [r, centredZero, xiZeroCopyReflectEquiv]
    ring
  rw [← hr]
  exact norm_laplace_pos_centredZero_le hG r

/-- Absolute summability of the heated zero pairing for any two energy-domain profiles at `ε > 0`. -/
theorem summable_heatedZeroPairing_of_domain {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    {ε : ℝ} (hε : 0 < ε) :
    Summable fun q : XiZeroCopy =>
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
  set CF : ℝ := ((∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) + ∫ u : ℝ, probe 1 u) / 2
  set CG : ℝ := ((∫ u : ℝ, G u ^ 2 * Real.exp (-(8 * u))) + ∫ u : ℝ, probe 1 u) / 2
  have hCF : 0 ≤ CF := div_nonneg (add_nonneg
    (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg fun u => probe_nonneg 1 u)) (by norm_num)
  have hCG : 0 ≤ CG := div_nonneg (add_nonneg
    (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg fun u => probe_nonneg 1 u)) (by norm_num)
  refine Summable.of_norm_bounded
    (summable_inv_sq_centredZero.mul_left (CF * CG * (Real.exp (ε / 2) / ε))) fun q => ?_
  rw [norm_mul, norm_mul]
  calc ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
        ‖negativeHalfLineLaplace (cx G) (-centredZero q)‖ *
          ‖Complex.exp ((ε : ℂ) * centredZero q ^ 2)‖
      ≤ (CF * CG) * ((Real.exp (ε / 2) / ε) * ‖centredZero q‖⁻¹ ^ 2) :=
        mul_le_mul (mul_le_mul (norm_laplace_pos_centredZero_le hF q)
          (norm_laplace_neg_centredZero_le_domain hG q) (norm_nonneg _) hCF)
          (norm_cexp_eps_centredZero_sq_le hε q) (norm_nonneg _) (mul_nonneg hCF hCG)
    _ = CF * CG * (Real.exp (ε / 2) / ε) * ‖centredZero q‖⁻¹ ^ 2 := by ring

/-- **Domain-wide zero Parseval identity under `FiniteOffLine`.** Every profile `G` in the energy
domain has square-summable on-line zero values, and its on-line mass plus finite off-line sum equals
its bare Weil energy `bareMixedEnergy G G`. -/
theorem domain_zeroParseval_of_finiteOffLine {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hfin : BacklundConverse.FiniteOffLine) :
    Summable (fun q : onLineCopies => zeroValueMass G q) ∧
      ((∑' q : onLineCopies, zeroValueMass G q : ℝ) : ℂ) +
        (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx G) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q)) =
        ((bareMixedEnergy G G : ℝ) : ℂ) := by
  set L : ℂ := ∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx G) (centredZero q) *
    negativeHalfLineLaplace (cx G) (-centredZero q)
  have hL : Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ, zeroNormTerm G ε q) (𝓝[>] 0) (𝓝 L) :=
    tendsto_offLine_of_finite (compl_onLineCopies_finite_of_finiteOffLine hfin)
  have hsum_ε : ∀ {ε : ℝ}, 0 < ε → Summable (zeroNormTerm G ε) :=
    fun hε => summable_heatedZeroPairing_of_domain hG hG hε
  have htend : Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, zeroNormTerm G ε q) (𝓝[>] 0)
      (𝓝 ((bareMixedEnergy G G : ℝ) : ℂ)) :=
    tendsto_heatedZeroPairing hG hG
  let Rfn : ℝ → ℝ := fun ε => ∑' q : onLineCopies, onLineWeight ε q * zeroValueMass G q
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  set V : ℂ := ((bareMixedEnergy G G : ℝ) : ℂ)
  have hR : Tendsto (fun ε => (Rfn ε : ℂ)) (𝓝[>] 0) (𝓝 (V - L)) := by
    refine (htend.sub hL).congr' ?_
    filter_upwards [hpos] with ε hε
    rw [tsum_zeroNormTerm_eq_onLine_add (hsum_ε hε)]
    ring
  have hRre : Tendsto Rfn (𝓝[>] 0) (𝓝 (V - L).re) :=
    Tendsto.congr (fun ε => by simp only [Function.comp_apply, Complex.ofReal_re])
      ((Complex.continuous_re.tendsto _).comp hR)
  have him : (V - L).im = 0 := by
    have h := (Complex.continuous_im.tendsto _).comp hR
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  set M := (V - L).re
  have hblock : ∀ T : Finset onLineCopies, ∑ q ∈ T, zeroValueMass G q ≤ M := by
    intro T
    have hT : Tendsto (fun ε => ∑ q ∈ T, onLineWeight ε q * zeroValueMass G q) (𝓝[>] 0)
        (𝓝 (∑ q ∈ T, zeroValueMass G q)) := by
      refine tendsto_finsetSum T fun q _ => ?_
      simpa using (tendsto_onLineWeight (q : XiZeroCopy)).mul_const (zeroValueMass G q)
    refine le_of_tendsto_of_tendsto hT hRre ?_
    filter_upwards [hpos] with ε hε
    exact (summable_onLine_of_summable (hsum_ε hε)).sum_le_tsum
      T fun q _ => mul_nonneg (onLineWeight_pos ε q).le (zeroValueMass_nonneg G q)
  have hsum_on : Summable (fun q : onLineCopies => zeroValueMass G q) :=
    summable_of_sum_le (fun q => zeroValueMass_nonneg G q) hblock
  have hle : ∑' q : onLineCopies, zeroValueMass G q ≤ M :=
    Real.tsum_le_of_sum_le (fun q => zeroValueMass_nonneg G q) hblock
  have hge : M ≤ ∑' q : onLineCopies, zeroValueMass G q := by
    refine le_of_tendsto hRre ?_
    filter_upwards [hpos] with ε hε
    refine (summable_onLine_of_summable (hsum_ε hε)).tsum_le_tsum (fun q => ?_) hsum_on
    exact mul_le_of_le_one_left (zeroValueMass_nonneg G q) (onLineWeight_le_one hε.le q)
  refine ⟨hsum_on, ?_⟩
  have hM : ((M : ℝ) : ℂ) = V - L := Complex.ext (by simp [M]) (by simp [him])
  rw [le_antisymm hle hge, hM]
  ring

/-- Symmetric real bilinear pairing of on-line zero values `∑_{on} Re(L F(z_q) conj(L G(z_q)))`. -/
def onLineMixed (F G : ℝ → ℝ) : ℝ :=
  ∑' q : onLineCopies,
    (negativeHalfLineLaplace (cx F) (centredZero q) *
      conj (negativeHalfLineLaplace (cx G) (centredZero q))).re

/-- Diagonal on-line zero energy `∑_{on} ‖L G(z_q)‖²`. -/
def onLineEnergy (G : ℝ → ℝ) : ℝ :=
  ∑' q : onLineCopies, zeroValueMass G q

theorem onLineMixed_comm (F G : ℝ → ℝ) : onLineMixed F G = onLineMixed G F := by
  unfold onLineMixed
  refine tsum_congr fun q => ?_
  have h := Complex.conj_re
    (negativeHalfLineLaplace (cx F) (centredZero q) *
      conj (negativeHalfLineLaplace (cx G) (centredZero q)))
  simpa [mul_comm] using h.symm

theorem onLineMixed_self (G : ℝ → ℝ) : onLineMixed G G = onLineEnergy G := by
  unfold onLineMixed onLineEnergy zeroValueMass
  refine tsum_congr fun q => ?_
  rw [Complex.mul_conj', Complex.ofReal_re]

theorem onLineEnergy_nonneg (G : ℝ → ℝ) : 0 ≤ onLineEnergy G :=
  tsum_nonneg fun q => zeroValueMass_nonneg G q

theorem summable_onLine_pair_of_finiteOffLine {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hfin : BacklundConverse.FiniteOffLine) :
    Summable fun q : onLineCopies =>
      negativeHalfLineLaplace (cx F) (centredZero q) *
        conj (negativeHalfLineLaplace (cx G) (centredZero q)) := by
  have hsF := (domain_zeroParseval_of_finiteOffLine hF hfin).1
  have hsG := (domain_zeroParseval_of_finiteOffLine hG hfin).1
  refine Summable.of_norm_bounded ((hsF.add hsG).div_const 2) fun q => ?_
  rw [norm_mul, Complex.norm_conj]
  set a := ‖negativeHalfLineLaplace (cx F) (centredZero q)‖
  set b := ‖negativeHalfLineLaplace (cx G) (centredZero q)‖
  change a * b ≤ (a ^ 2 + b ^ 2) / 2
  nlinarith [sq_nonneg (a - b)]

theorem summable_onLine_re_pair_of_finiteOffLine {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hfin : BacklundConverse.FiniteOffLine) :
    Summable fun q : onLineCopies =>
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        conj (negativeHalfLineLaplace (cx G) (centredZero q))).re :=
  Complex.reCLM.summable (summable_onLine_pair_of_finiteOffLine hF hG hfin)

/-- **Polarized Krein decomposition of Weil's bare form on the entire energy domain.** Under
`FiniteOffLine`, for all `F, G` in the energy domain, `bareMixedEnergy F G` equals the Hermitian
on-line zero pairing plus the finite off-line zero pairing. -/
theorem bareMixedEnergy_eq_onLine_add_offLine_of_finiteOffLine {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hfin : BacklundConverse.FiniteOffLine) :
    ((bareMixedEnergy F G : ℝ) : ℂ) =
      (∑' q : onLineCopies,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          conj (negativeHalfLineLaplace (cx G) (centredZero q))) +
      (∑' q : ↑onLineCopiesᶜ,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q)) := by
  have hs_pair := summable_onLine_pair_of_finiteOffLine hF hG hfin
  have hterm_on : ∀ (ε : ℝ) (q : onLineCopies),
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero (q : XiZeroCopy) ^ 2) =
      (onLineWeight ε q : ℂ) *
        (negativeHalfLineLaplace (cx F) (centredZero q) *
          conj (negativeHalfLineLaplace (cx G) (centredZero q))) := by
    intro ε q
    have hre : (centredZero (q : XiZeroCopy)).re = 0 := q.2
    have hneg : -centredZero (q : XiZeroCopy) = conj (centredZero (q : XiZeroCopy)) := by
      apply Complex.ext <;> simp [hre]
    have hsq : (ε : ℂ) * centredZero (q : XiZeroCopy) ^ 2 =
        ((-(ε * (centredZero (q : XiZeroCopy)).im ^ 2) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [sq, hre]
    unfold onLineWeight
    rw [hneg, show cx G = fun u => (G u : ℂ) from rfl, negativeHalfLineLaplace_real_conj,
      hsq, ← Complex.ofReal_exp]
    ring
  have hon_lim : Tendsto (fun ε : ℝ => ∑' q : onLineCopies,
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero (q : XiZeroCopy) ^ 2))
      (𝓝[>] 0)
      (𝓝 (∑' q : onLineCopies,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          conj (negativeHalfLineLaplace (cx G) (centredZero q)))) := by
    refine (tendsto_tsum_of_dominated_convergence (bound := fun q : onLineCopies =>
        ‖negativeHalfLineLaplace (cx F) (centredZero q) *
          conj (negativeHalfLineLaplace (cx G) (centredZero q))‖)
      hs_pair.norm (fun q => ?_) ?_).congr fun ε => tsum_congr fun q => (hterm_on ε q).symm
    · have hw := (Complex.continuous_ofReal.tendsto 1).comp (tendsto_onLineWeight (q : XiZeroCopy))
      simpa using hw.mul_const
        (negativeHalfLineLaplace (cx F) (centredZero q) *
          conj (negativeHalfLineLaplace (cx G) (centredZero q)))
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) q
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (onLineWeight_pos ε q).le]
      exact mul_le_of_le_one_left (norm_nonneg _) (onLineWeight_le_one hε.le q)
  have hoff_lim : Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ,
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero (q : XiZeroCopy) ^ 2))
      (𝓝[>] 0)
      (𝓝 (∑' q : ↑onLineCopiesᶜ,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q))) := by
    haveI : Finite ↑onLineCopiesᶜ := (compl_onLineCopies_finite_of_finiteOffLine hfin).to_subtype
    cases nonempty_fintype ↑onLineCopiesᶜ
    simp_rw [tsum_fintype]
    refine tendsto_finsetSum Finset.univ fun q _ => ?_
    have hc : Continuous fun ε : ℝ =>
        Complex.exp ((ε : ℂ) * centredZero (q : XiZeroCopy) ^ 2) := by fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h0.const_mul
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q))
  have hsplit : Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy,
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0)
      (𝓝 ((∑' q : onLineCopies,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          conj (negativeHalfLineLaplace (cx G) (centredZero q))) +
      (∑' q : ↑onLineCopiesᶜ,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q)))) := by
    refine (hon_lim.add hoff_lim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (summable_heatedZeroPairing_of_domain hF hG hε).tsum_subtype_add_tsum_subtype_compl
      onLineCopies
  exact tendsto_nhds_unique (tendsto_heatedZeroPairing hF hG) hsplit

/-- Real-part form of the polarized Krein decomposition on the energy domain. -/
theorem bareMixedEnergy_eq_onLineMixed_add_re_offLine {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hfin : BacklundConverse.FiniteOffLine) :
    bareMixedEnergy F G = onLineMixed F G +
      (∑ q ∈ offLineCopyFinset hfin,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q)).re := by
  have h := congrArg Complex.re (bareMixedEnergy_eq_onLine_add_offLine_of_finiteOffLine hF hG hfin)
  simp only [Complex.ofReal_re, Complex.add_re] at h
  have hs := summable_onLine_pair_of_finiteOffLine hF hG hfin
  have hon : (∑' q : onLineCopies,
      negativeHalfLineLaplace (cx F) (centredZero q) *
        conj (negativeHalfLineLaplace (cx G) (centredZero q))).re = onLineMixed F G := by
    unfold onLineMixed
    exact Complex.re_tsum hs
  have hoff : (∑' q : ↑onLineCopiesᶜ,
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q)) =
      ∑ q ∈ offLineCopyFinset hfin,
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q) := by
    have hfin_set := compl_onLineCopies_finite_of_finiteOffLine hfin
    rw [tsum_subtype (onLineCopiesᶜ : Set XiZeroCopy)
      (fun q => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q))]
    rw [tsum_eq_sum (s := offLineCopyFinset hfin)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      have hmem : q ∈ onLineCopiesᶜ := (hfin_set.mem_toFinset).mp hq
      exact Set.indicator_of_mem hmem _
    · intro q hq
      have hnot : q ∉ onLineCopiesᶜ := fun hm => hq ((hfin_set.mem_toFinset).mpr hm)
      exact Set.indicator_of_notMem hnot _
  rw [hon, hoff] at h
  exact h

/-- **Every profile with beyond-the-wall continuation has nonnegative bare Weil energy** under
`FiniteOffLine`: its off-line zero pairing vanishes identically, leaving `B(G, G) = ∑_{on} ‖L G‖² ≥ 0`. -/
theorem bareMixedEnergy_nonneg_of_hasBeyondTheWallPrimeContinuation {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hfin : BacklundConverse.FiniteOffLine)
    (hcont : HasBeyondTheWallPrimeContinuation G) :
    bareMixedEnergy G G = onLineEnergy G ∧ 0 ≤ bareMixedEnergy G G := by
  have hvan := (hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros hG).mp hcont
  have heq := bareMixedEnergy_eq_onLineMixed_add_re_offLine hG hG hfin
  have hoff0 : ∑ q ∈ offLineCopyFinset hfin,
      negativeHalfLineLaplace (cx G) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hne : (centredZero q).re ≠ 0 := mem_offLineCopyFinset.mp hq
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [hvan q hneg, zero_mul]
    · set r := xiZeroCopyReflectEquiv q
      have hr : centredZero r = -centredZero q := by
        simp [r, centredZero, xiZeroCopyReflectEquiv]; ring
      have hr_neg : (centredZero r).re < 0 := by rw [hr, Complex.neg_re]; linarith
      rw [← hr, hvan r hr_neg, mul_zero]
  rw [hoff0, Complex.zero_re, add_zero, onLineMixed_self] at heq
  exact ⟨heq, heq ▸ onLineEnergy_nonneg G⟩

/-- Symmetrically, any profile in the domain vanishing on `upperRightCentredZeros hfin` has
`B(G, G) = onLineEnergy G ≥ 0`. -/
theorem bareMixedEnergy_nonneg_of_vanish_upperRight {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hfin : BacklundConverse.FiniteOffLine)
    (hvan : ∀ z ∈ upperRightCentredZeros hfin, negativeHalfLineLaplace (cx G) z = 0) :
    bareMixedEnergy G G = onLineEnergy G ∧ 0 ≤ bareMixedEnergy G G := by
  have hright : ∀ q : XiZeroCopy, 0 < (centredZero q).re →
      negativeHalfLineLaplace (cx G) (centredZero q) = 0 := by
    intro q hq
    set z := centredZero q
    have hxi : xi (1 / 2 + z) = 0 := xi_centredZero q
    have him_ne : z.im ≠ 0 := xi_half_add_im_ne_zero hxi
    rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
    · have hcz_mem : conj z ∈ upperRightCentredZeros hfin := by
        rw [upperRightCentredZeros, Finset.mem_filter, mem_rightCentredZeros_iff]
        refine ⟨⟨by simpa using hq, ?_⟩, by simpa using him_neg⟩
        have hc : (1 : ℂ) / 2 + conj z = conj (1 / 2 + z) := by simp
        rw [hc, xi_conj, hxi, map_zero]
      have hcz := hvan (conj z) hcz_mem
      have hreal : negativeHalfLineLaplace (cx G) (conj z) =
          conj (negativeHalfLineLaplace (cx G) z) := by
        simpa [cx] using negativeHalfLineLaplace_real_conj G z
      rw [hreal] at hcz
      exact conj_eq_zero.mp hcz
    · exact hvan z (Finset.mem_filter.mpr ⟨(mem_rightCentredZeros_iff hfin).mpr ⟨hq, hxi⟩, him_pos⟩)
  have heq := bareMixedEnergy_eq_onLineMixed_add_re_offLine hG hG hfin
  have hoff0 : ∑ q ∈ offLineCopyFinset hfin,
      negativeHalfLineLaplace (cx G) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hne : (centredZero q).re ≠ 0 := mem_offLineCopyFinset.mp hq
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · set r := xiZeroCopyReflectEquiv q
      have hr : centredZero r = -centredZero q := by
        simp [r, centredZero, xiZeroCopyReflectEquiv]; ring
      have hr_pos : 0 < (centredZero r).re := by rw [hr, Complex.neg_re]; linarith
      rw [← hr, hright r hr_pos, mul_zero]
    · rw [hright q hpos, zero_mul]
  rw [hoff0, Complex.zero_re, add_zero, onLineMixed_self] at heq
  exact ⟨heq, heq ▸ onLineEnergy_nonneg G⟩

/-! ### 3. Transfer of the Birman–Schwinger on-line resolvent to `ζ` on the energy domain -/

/-- A measurable half-line profile `y` square-integrable against the confinement weight `e^{-8u}`. -/
def IsW8Target (y : ℝ → ℝ) : Prop :=
  Measurable y ∧ (∀ u, 0 ≤ u → y u = 0) ∧ Integrable (fun u => y u ^ 2 * Real.exp (-(8 * u)))

/-- Confinement inner product `⟨F, G⟩_{W₈} = ∫ F(u) G(u) e^{-8u} du`. -/
def w8Pair (F G : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, F u * G u * Real.exp (-(8 * u))

/-- Confinement norm square `W₈(F) = ∫ F(u)² e^{-8u} du`. -/
def w8Mass (F : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))

theorem w8Pair_comm (F G : ℝ → ℝ) : w8Pair F G = w8Pair G F :=
  integral_congr_ae (Eventually.of_forall fun u => by ring)

theorem w8Pair_self (F : ℝ → ℝ) : w8Pair F F = w8Mass F :=
  integral_congr_ae (Eventually.of_forall fun u => by ring)

theorem w8Mass_nonneg (F : ℝ → ℝ) : 0 ≤ w8Mass F :=
  integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem isW8Target_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) : IsW8Target F :=
  ⟨hF.meas, hF.support, hF.exponential⟩

theorem isW8Target_const_mul {y : ℝ → ℝ} (hy : IsW8Target y) (c : ℝ) :
    IsW8Target (fun u => c * y u) := by
  refine ⟨hy.1.const_mul c, fun u hu => by rw [hy.2.1 u hu, mul_zero], ?_⟩
  exact (hy.2.2.const_mul (c ^ 2)).congr (Eventually.of_forall fun u => by ring)

theorem isW8Target_add {y₁ y₂ : ℝ → ℝ} (h₁ : IsW8Target y₁) (h₂ : IsW8Target y₂) :
    IsW8Target (fun u => y₁ u + y₂ u) := by
  refine ⟨h₁.1.add h₂.1, fun u hu => by rw [h₁.2.1 u hu, h₂.2.1 u hu, add_zero], ?_⟩
  refine ((h₁.2.2.add h₂.2.2).const_mul 2).mono'
    (((h₁.1.add h₂.1).pow_const 2).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  have he : 0 ≤ Real.exp (-(8 * u)) := (Real.exp_pos _).le
  nlinarith [sq_nonneg (y₁ u - y₂ u), he]

theorem integrable_w8Pair {F G : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G) :
    Integrable fun u : ℝ => F u * G u * Real.exp (-(8 * u)) := by
  refine ((hF.2.2.add hG.2.2).div_const 2).mono'
    ((hF.1.mul hG.1).mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_le]
  have he : 0 ≤ Real.exp (-(8 * u)) := (Real.exp_pos _).le
  constructor <;> nlinarith [sq_nonneg (F u + G u), sq_nonneg (F u - G u), he]

theorem w8Pair_add_left {F₁ F₂ G : ℝ → ℝ} (h₁ : IsW8Target F₁) (h₂ : IsW8Target F₂)
    (hG : IsW8Target G) :
    w8Pair (fun u => F₁ u + F₂ u) G = w8Pair F₁ G + w8Pair F₂ G := by
  unfold w8Pair
  have hfun : (fun u => (F₁ u + F₂ u) * G u * Real.exp (-(8 * u))) =
      fun u => F₁ u * G u * Real.exp (-(8 * u)) + F₂ u * G u * Real.exp (-(8 * u)) := by
    funext u; ring
  rw [hfun, integral_add (integrable_w8Pair h₁ hG) (integrable_w8Pair h₂ hG)]

theorem w8Pair_const_mul_left (c : ℝ) (F G : ℝ → ℝ) :
    w8Pair (fun u => c * F u) G = c * w8Pair F G := by
  unfold w8Pair
  have hfun : (fun u => (c * F u) * G u * Real.exp (-(8 * u))) =
      fun u => c * (F u * G u * Real.exp (-(8 * u))) := by
    funext u; ring
  rw [hfun, integral_const_mul]

theorem w8Mass_add_const_mul {F G : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G) (c : ℝ) :
    w8Mass (fun u => F u + c * G u) = w8Mass F + 2 * c * w8Pair F G + c ^ 2 * w8Mass G := by
  unfold w8Mass w8Pair
  have h1 := hF.2.2
  have h2 := (integrable_w8Pair hF hG).const_mul (2 * c)
  have h3 := hG.2.2.const_mul (c ^ 2)
  have hfun : (fun u => (F u + c * G u) ^ 2 * Real.exp (-(8 * u))) =
      fun u => (F u ^ 2 * Real.exp (-(8 * u)) +
        (2 * c) * (F u * G u * Real.exp (-(8 * u)))) +
        c ^ 2 * (G u ^ 2 * Real.exp (-(8 * u))) := by
    funext u; ring
  rw [hfun, integral_add (h1.add h2) h3, integral_add h1 h2, integral_const_mul, integral_const_mul]

theorem sq_w8Pair_le {F G : ℝ → ℝ} (hF : IsW8Target F) (hG : IsW8Target G) :
    w8Pair F G ^ 2 ≤ w8Mass F * w8Mass G := by
  set f : ℝ → ℝ := fun u => F u * Real.exp (-(4 * u))
  set g : ℝ → ℝ := fun u => G u * Real.exp (-(4 * u))
  have hf2 : (fun u => f u ^ 2) = fun u => F u ^ 2 * Real.exp (-(8 * u)) := by
    funext u; dsimp [f]; rw [mul_pow, sq (Real.exp (-(4 * u))), ← Real.exp_add]; congr 2; ring
  have hg2 : (fun u => g u ^ 2) = fun u => G u ^ 2 * Real.exp (-(8 * u)) := by
    funext u; dsimp [g]; rw [mul_pow, sq (Real.exp (-(4 * u))), ← Real.exp_add]; congr 2; ring
  have hfg : (fun u => f u * g u) = fun u => F u * G u * Real.exp (-(8 * u)) := by
    funext u; dsimp [f, g]
    have he : Real.exp (-(4 * u)) * Real.exp (-(4 * u)) = Real.exp (-(8 * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc F u * Real.exp (-(4 * u)) * (G u * Real.exp (-(4 * u)))
        = F u * G u * (Real.exp (-(4 * u)) * Real.exp (-(4 * u))) := by ring
      _ = F u * G u * Real.exp (-(8 * u)) := by rw [he]
  have hcs := sq_integral_mul_le
    (hF.1.mul (by fun_prop)).aestronglyMeasurable
    (hG.1.mul (by fun_prop)).aestronglyMeasurable
    (by rw [hf2]; exact hF.2.2) (by rw [hg2]; exact hG.2.2)
  simpa [w8Pair, w8Mass, hfg, hf2, hg2] using hcs

private theorem laplace_cx_integrable_of_domain {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ} (hw : -4 < w.re) :
    Integrable fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx F u := by
  have hdom : Integrable fun u : ℝ => |F u| * Real.exp (w.re * u) :=
    integrable_abs_mul_exp_of_domain hF hw
  refine hdom.mono' ((by fun_prop : Measurable fun u : ℝ => Complex.exp (w * (u : ℂ))).mul
    (Complex.measurable_ofReal.comp hF.meas)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.norm_real, Real.norm_eq_abs, mul_comm]

theorem laplace_cx_add {F₁ F₂ : ℝ → ℝ}
    (h₁ : CriticalHalfLineEnergyDomain F₁) (h₂ : CriticalHalfLineEnergyDomain F₂)
    {w : ℂ} (hw : -4 < w.re) :
    negativeHalfLineLaplace (cx fun u => F₁ u + F₂ u) w =
      negativeHalfLineLaplace (cx F₁) w + negativeHalfLineLaplace (cx F₂) w := by
  unfold negativeHalfLineLaplace
  have hfun : (fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx (fun x => F₁ x + F₂ x) u) =
      fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx F₁ u +
        Complex.exp (w * (u : ℂ)) * cx F₂ u := by
    funext u; simp [cx]; ring
  rw [hfun, integral_add (laplace_cx_integrable_of_domain h₁ hw)
    (laplace_cx_integrable_of_domain h₂ hw)]

theorem laplace_cx_const_mul (c : ℝ) (F : ℝ → ℝ) (w : ℂ) :
    negativeHalfLineLaplace (cx fun u => c * F u) w =
      (c : ℂ) * negativeHalfLineLaplace (cx F) w := by
  unfold negativeHalfLineLaplace
  have hfun : (fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx (fun x => c * F x) u) =
      fun u : ℝ => (c : ℂ) * (Complex.exp (w * (u : ℂ)) * cx F u) := by
    funext u; simp [cx]; ring
  rw [hfun, integral_const_mul]

theorem onLineMixed_add_left {F₁ F₂ G : ℝ → ℝ}
    (h₁ : CriticalHalfLineEnergyDomain F₁) (h₂ : CriticalHalfLineEnergyDomain F₂)
    (hG : CriticalHalfLineEnergyDomain G) (hfin : BacklundConverse.FiniteOffLine) :
    onLineMixed (fun u => F₁ u + F₂ u) G = onLineMixed F₁ G + onLineMixed F₂ G := by
  unfold onLineMixed
  rw [← (summable_onLine_re_pair_of_finiteOffLine h₁ hG hfin).tsum_add
    (summable_onLine_re_pair_of_finiteOffLine h₂ hG hfin)]
  refine tsum_congr fun q => ?_
  have hw : -4 < (centredZero (q : XiZeroCopy)).re := by
    have := (abs_lt.mp (abs_re_centredZero_lt (q : XiZeroCopy))).1; linarith
  rw [laplace_cx_add h₁ h₂ hw, add_mul, Complex.add_re]

theorem onLineMixed_const_mul_left (c : ℝ) (F G : ℝ → ℝ) :
    onLineMixed (fun u => c * F u) G = c * onLineMixed F G := by
  unfold onLineMixed
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [laplace_cx_const_mul, mul_assoc, Complex.re_ofReal_mul]

theorem onLineEnergy_add_const_mul {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hfin : BacklundConverse.FiniteOffLine) (c : ℝ) :
    onLineEnergy (fun u => F u + c * G u) =
      onLineEnergy F + 2 * c * onLineMixed F G + c ^ 2 * onLineEnergy G := by
  have hcG : CriticalHalfLineEnergyDomain (fun u => c * G u) := hG.const_mul c
  have hFG : CriticalHalfLineEnergyDomain (fun u => F u + c * G u) := hF.add_const_mul hG c
  rw [← onLineMixed_self, onLineMixed_add_left hF hcG hFG hfin,
    onLineMixed_comm F _, onLineMixed_add_left hF hcG hF hfin,
    onLineMixed_comm (fun u => c * G u) _, onLineMixed_add_left hF hcG hcG hfin,
    onLineMixed_const_mul_left, onLineMixed_const_mul_left, onLineMixed_comm G _,
    onLineMixed_const_mul_left, onLineMixed_self, onLineMixed_self, onLineMixed_comm G F]
  ring

/-- Variational weak equation defining the Birman–Schwinger on-line resolvent `X = R_a(y)` on
`CriticalHalfLineEnergyDomain`. -/
def SolvesZetaOnLineResolvent (a : ℝ) (y X : ℝ → ℝ) : Prop :=
  CriticalHalfLineEnergyDomain X ∧
    ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → onLineMixed X G + a * w8Pair X G = w8Pair y G

/-- Two energy-domain solutions of `SolvesZetaOnLineResolvent a y` (`a > 0`) under `FiniteOffLine`
agree almost everywhere. -/
theorem solvesZetaOnLineResolvent_ae_unique (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {y X₁ X₂ : ℝ → ℝ}
    (h₁ : SolvesZetaOnLineResolvent a y X₁) (h₂ : SolvesZetaOnLineResolvent a y X₂) :
    X₁ =ᵐ[volume] X₂ := by
  set D : ℝ → ℝ := fun u => X₁ u + (-1) * X₂ u
  have hD : CriticalHalfLineEnergyDomain D := h₁.1.add_const_mul h₂.1 (-1)
  have heq₁ := h₁.2 D hD
  have heq₂ := h₂.2 D hD
  have hon : onLineMixed D D = onLineMixed X₁ D + (-1) * onLineMixed X₂ D := by
    rw [onLineMixed_add_left h₁.1 (h₂.1.const_mul (-1)) hD hfin, onLineMixed_const_mul_left]
  have hw8 : w8Pair D D = w8Pair X₁ D + (-1) * w8Pair X₂ D := by
    rw [w8Pair_add_left (isW8Target_of_domain h₁.1)
      (isW8Target_const_mul (isW8Target_of_domain h₂.1) (-1)) (isW8Target_of_domain hD),
      w8Pair_const_mul_left]
  have hzero : onLineEnergy D + a * w8Mass D = 0 := by
    rw [← onLineMixed_self, ← w8Pair_self, hon, hw8]
    linarith
  have hw0 : w8Mass D = 0 := by
    nlinarith [onLineEnergy_nonneg D, w8Mass_nonneg D]
  have hae : ∀ᵐ u ∂volume, D u ^ 2 * Real.exp (-(8 * u)) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      hD.exponential).mp hw0
  filter_upwards [hae] with u hu
  have hsq0 : D u ^ 2 = 0 := (mul_eq_zero.mp hu).resolve_right (Real.exp_pos _).ne'
  have hDu : D u = 0 := sq_eq_zero_iff.mp hsq0
  dsimp [D] at hDu
  linarith

/-- Energy bound `onLineEnergy X + a W₈(X) ≤ W₈(y) / a` for any solution of the on-line resolvent. -/
theorem solvesZetaOnLineResolvent_energy_le {a : ℝ} (ha : 0 < a) {y X : ℝ → ℝ}
    (hy : IsW8Target y) (hX : SolvesZetaOnLineResolvent a y X) :
    onLineEnergy X + a * w8Mass X ≤ w8Mass y / a := by
  have heq := hX.2 X hX.1
  rw [onLineMixed_self, w8Pair_self] at heq
  have hcs := sq_w8Pair_le hy (isW8Target_of_domain hX.1)
  have h1 : (onLineEnergy X + a * w8Mass X) ^ 2 ≤ w8Mass y * w8Mass X := by linarith
  have h2 : a * (onLineEnergy X + a * w8Mass X) ^ 2 ≤
      w8Mass y * (onLineEnergy X + a * w8Mass X) := by
    have hnn := onLineEnergy_nonneg X
    have hw := w8Mass_nonneg y
    nlinarith
  have hsum_nn : 0 ≤ onLineEnergy X + a * w8Mass X :=
    add_nonneg (onLineEnergy_nonneg X) (mul_nonneg ha.le (w8Mass_nonneg X))
  rw [le_div_iff₀ ha]
  rcases eq_or_lt_of_le hsum_nn with h0 | hpos
  · rw [← h0, zero_mul]; exact w8Mass_nonneg y
  · nlinarith

/-- Weak `W₈` convergence from strong `L²` convergence and a uniform `W₈` bound on `(-∞, 0)`. -/
private theorem tendsto_w8Pair_of_L2_tendsto {U : ℕ → ℝ → ℝ} {F g : ℝ → ℝ} {M : ℝ}
    (hU : ∀ n, IsW8Target (U n)) (hF : IsW8Target F) (hg : IsW8Target g)
    (hM : 0 ≤ M) (hwU : ∀ n, w8Mass (U n) ≤ M) (hwF : w8Mass F ≤ M)
    (hL2 : Tendsto (fun n => ∫ u, (U n u - F u) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => w8Pair g (U n)) atTop (𝓝 (w8Pair g F)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail_lim : Tendsto (fun K : ℕ =>
      ∫ u : ℝ, Set.indicator (Iic (-(K : ℝ))) (fun x => g x ^ 2 * Real.exp (-(8 * x))) u)
      atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence
      (fun x => g x ^ 2 * Real.exp (-(8 * x)))
      (fun K => hg.2.2.aestronglyMeasurable.indicator measurableSet_Iic) hg.2.2
      (fun K => Eventually.of_forall fun x => by
        by_cases hx : x ∈ Iic (-(K : ℝ))
        · simp [hx, mul_nonneg (sq_nonneg _) (Real.exp_pos _).le]
        · simp [hx, mul_nonneg (sq_nonneg _) (Real.exp_pos _).le])
      (Eventually.of_forall fun x => tendsto_const_nhds.congr' <| by
        obtain ⟨N, hN⟩ := exists_nat_gt (-x)
        filter_upwards [eventually_ge_atTop N] with K hK
        have hxK : x ∉ Iic (-(K : ℝ)) := by
          rw [mem_Iic, not_le]
          have : (N : ℝ) ≤ K := by exact_mod_cast hK
          linarith
        simp [hxK])
  set δ : ℝ := (ε / (4 * (Real.sqrt M + 1))) ^ 2
  have hδ : 0 < δ := by positivity
  obtain ⟨K, hK⟩ := (htail_lim.eventually (gt_mem_nhds hδ)).exists
  set AK : ℝ := ∫ u : ℝ, Set.indicator (Iic (-(K : ℝ))) (fun x => g x ^ 2 * Real.exp (-(8 * x))) u
  have hAK_nn : 0 ≤ AK := integral_nonneg fun u =>
    Set.indicator_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) u
  have hhead_lim : Tendsto (fun n =>
      (w8Mass g * Real.exp (8 * (K : ℝ))) * ∫ u, (U n u - F u) ^ 2) atTop (𝓝 0) := by
    simpa using hL2.const_mul (w8Mass g * Real.exp (8 * (K : ℝ)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hhead_lim.eventually (gt_mem_nhds ((ε / 2) ^ 2)))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  set D : ℝ → ℝ := fun u => U n u - F u
  have hD : IsW8Target D := by
    simpa [D, sub_eq_add_neg, neg_one_mul] using isW8Target_add (hU n) (isW8Target_const_mul hF (-1))
  have hwD : w8Mass D ≤ 4 * M := by
    have h := w8Mass_add_const_mul (hU n) hF (-1)
    have hcs := sq_w8Pair_le (hU n) hF
    have habs : |w8Pair (U n) F| ≤ M := by
      have hsq : w8Pair (U n) F ^ 2 ≤ M ^ 2 :=
        hcs.trans (mul_le_mul (hwU n) hwF (w8Mass_nonneg F) hM)
      exact (abs_le_of_sq_le_sq' hsq hM).2
    have hsub : (fun u => U n u + (-1) * F u) = D := by funext u; dsimp [D]; ring
    rw [hsub] at h
    linarith [(abs_le.mp habs).1]
  have hdiff_eq : w8Pair g (U n) - w8Pair g F = w8Pair g D := by
    have h := w8Pair_add_left (hU n) (isW8Target_const_mul hF (-1)) hg
    rw [w8Pair_comm _ g, w8Pair_comm (U n) g, w8Pair_const_mul_left, w8Pair_comm F g] at h
    have hsub : (fun u => U n u + (-1) * F u) = D := by funext u; dsimp [D]; ring
    rw [hsub] at h
    linarith
  rw [hdiff_eq]
  -- Split `w8Pair g D` into `Iic (-K)` and `Ioi (-K)`
  have hint := integrable_w8Pair hg hD
  set I₁ : ℝ := ∫ u : ℝ, Set.indicator (Iic (-(K : ℝ)))
    (fun x => g x * D x * Real.exp (-(8 * x))) u
  set I₂ : ℝ := ∫ u : ℝ, Set.indicator (Ioi (-(K : ℝ)))
    (fun x => g x * D x * Real.exp (-(8 * x))) u
  have hsplit_int : w8Pair g D = I₁ + I₂ := by
    unfold w8Pair I₁ I₂
    rw [← integral_add (hint.indicator measurableSet_Iic) (hint.indicator measurableSet_Ioi)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ≤ -(K : ℝ)
    · have hnot : u ∉ Ioi (-(K : ℝ)) := not_lt.mpr hu
      simp [mem_Iic.mpr hu, hnot]
    · have hgt : u ∈ Ioi (-(K : ℝ)) := not_le.mp hu
      simp [hu, hgt]
  -- Bound `|I₁| < ε / 2`
  have hI₁_sq : I₁ ^ 2 ≤ AK * w8Mass D := by
    set f₁ : ℝ → ℝ := Set.indicator (Iic (-(K : ℝ))) (fun u => g u * Real.exp (-(4 * u)))
    set f₂ : ℝ → ℝ := fun u => D u * Real.exp (-(4 * u))
    have hf₁_sq : (fun u => f₁ u ^ 2) =
        Set.indicator (Iic (-(K : ℝ))) (fun u => g u ^ 2 * Real.exp (-(8 * u))) := by
      funext u; by_cases hu : u ∈ Iic (-(K : ℝ))
      · simp only [f₁, hu, Set.indicator_of_mem]
        rw [mul_pow, sq (Real.exp (-(4 * u))), ← Real.exp_add]; congr 2; ring
      · simp [f₁, hu]
    have hf₂_sq : (fun u => f₂ u ^ 2) = fun u => D u ^ 2 * Real.exp (-(8 * u)) := by
      funext u; dsimp [f₂]; rw [mul_pow, sq (Real.exp (-(4 * u))), ← Real.exp_add]; congr 2; ring
    have hprod : (fun u => f₁ u * f₂ u) =
        Set.indicator (Iic (-(K : ℝ))) (fun x => g x * D x * Real.exp (-(8 * x))) := by
      funext u; by_cases hu : u ∈ Iic (-(K : ℝ))
      · simp only [f₁, f₂, hu, Set.indicator_of_mem]
        have he : Real.exp (-(4 * u)) * Real.exp (-(4 * u)) = Real.exp (-(8 * u)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc g u * Real.exp (-(4 * u)) * (D u * Real.exp (-(4 * u)))
            = g u * D u * (Real.exp (-(4 * u)) * Real.exp (-(4 * u))) := by ring
          _ = g u * D u * Real.exp (-(8 * u)) := by rw [he]
      · simp [f₁, hu]
    have hcs := sq_integral_mul_le
      ((hg.1.mul (by fun_prop)).indicator measurableSet_Iic).aestronglyMeasurable
      (hD.1.mul (by fun_prop)).aestronglyMeasurable
      (by rw [hf₁_sq]; exact hg.2.2.indicator measurableSet_Iic)
      (by rw [hf₂_sq]; exact hD.2.2)
    simpa [I₁, AK, w8Mass, hprod, hf₁_sq, hf₂_sq] using hcs
  have hI₁_lt : |I₁| < ε / 2 := by
    have hsq_lt : I₁ ^ 2 < (ε / 2) ^ 2 := by
      have h1 : AK * w8Mass D ≤ δ * (4 * M) :=
        mul_le_mul hK.le hwD (w8Mass_nonneg D) hδ.le
      have h2 : δ * (4 * M) < (ε / 2) ^ 2 := by
        dsimp [δ]
        have hden : 0 < Real.sqrt M + 1 := by positivity
        have hM_sq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
        have hlt_sq : 4 * M < 4 * (Real.sqrt M + 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg M, hM_sq]
        calc (ε / (4 * (Real.sqrt M + 1))) ^ 2 * (4 * M)
            = ε ^ 2 * (4 * M) / (16 * (Real.sqrt M + 1) ^ 2) := by ring
          _ < ε ^ 2 * (4 * (Real.sqrt M + 1) ^ 2) / (16 * (Real.sqrt M + 1) ^ 2) := by
              exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt_sq (sq_pos_of_pos hε))
                (by positivity)
          _ = (ε / 2) ^ 2 := by field_simp; ring
      exact hI₁_sq.trans_lt (h1.trans_lt h2)
    exact abs_lt_of_sq_lt_sq' hsq_lt (by positivity) |>.2
  -- Bound `|I₂| < ε / 2`
  have hI₂_sq : I₂ ^ 2 ≤ (w8Mass g * Real.exp (8 * (K : ℝ))) * ∫ u, D u ^ 2 := by
    set f₁ : ℝ → ℝ := fun u => |g u| * Real.exp (-(4 * u)) * Real.exp (4 * (K : ℝ))
    set f₂ : ℝ → ℝ := fun u => |D u|
    have hf₁_sq : (fun u => f₁ u ^ 2) =
        fun u => Real.exp (8 * (K : ℝ)) * (g u ^ 2 * Real.exp (-(8 * u))) := by
      funext u; dsimp [f₁]
      rw [mul_pow, mul_pow, sq_abs, sq (Real.exp (-(4 * u))), sq (Real.exp (4 * (K : ℝ))),
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hD_sq_int : Integrable fun u => D u ^ 2 := by
      refine hD.2.2.mono' (hD.1.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      rcases le_or_gt 0 u with hu | hu
      · rw [hD.2.1 u hu]; simp
      · exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by linarith))
    have hpt : ∀ u : ℝ,
        |Set.indicator (Ioi (-(K : ℝ))) (fun x => g x * D x * Real.exp (-(8 * x))) u| ≤
          f₁ u * f₂ u := by
      intro u
      by_cases hu : u ∈ Ioi (-(K : ℝ))
      · simp only [hu, Set.indicator_of_mem, f₁, f₂]
        rcases le_or_gt 0 u with hu0 | hu0
        · rw [hD.2.1 u hu0]; simp
        · rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp : Real.exp (-(8 * u)) ≤ Real.exp (-(4 * u)) * Real.exp (4 * (K : ℝ)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith [mem_Ioi.mp hu])
          calc |g u| * |D u| * Real.exp (-(8 * u))
              ≤ |g u| * |D u| * (Real.exp (-(4 * u)) * Real.exp (4 * (K : ℝ))) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = |g u| * Real.exp (-(4 * u)) * Real.exp (4 * (K : ℝ)) * |D u| := by ring
      · simp only [hu, Set.indicator_of_notMem, abs_zero, f₁, f₂]
        positivity
    have hf₁_int : Integrable fun u => f₁ u ^ 2 := by
      rw [hf₁_sq]; exact hg.2.2.const_mul _
    have hf₂_int : Integrable fun u => f₂ u ^ 2 := by
      simpa [f₂, sq_abs] using hD_sq_int
    have hprod_int := integrable_mul_of_sq_integrable
      (((continuous_abs.measurable.comp hg.1).mul (by fun_prop)).mul measurable_const).aestronglyMeasurable
      (continuous_abs.measurable.comp hD.1).aestronglyMeasurable hf₁_int hf₂_int
    have habs_le : |I₂| ≤ ∫ u, f₁ u * f₂ u :=
      abs_integral_le_integral_abs.trans
        (integral_mono (hint.indicator measurableSet_Ioi).abs hprod_int hpt)
    have hnn_rhs : 0 ≤ ∫ u, f₁ u * f₂ u := integral_nonneg fun u => by dsimp [f₁, f₂]; positivity
    have hcs := sq_integral_mul_le
      (((continuous_abs.measurable.comp hg.1).mul (by fun_prop)).mul measurable_const).aestronglyMeasurable
      (continuous_abs.measurable.comp hD.1).aestronglyMeasurable hf₁_int hf₂_int
    calc I₂ ^ 2 = |I₂| ^ 2 := (sq_abs I₂).symm
      _ ≤ (∫ u, f₁ u * f₂ u) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs_le 2
      _ ≤ (∫ u, f₁ u ^ 2) * (∫ u, f₂ u ^ 2) := hcs
      _ = (w8Mass g * Real.exp (8 * (K : ℝ))) * ∫ u, D u ^ 2 := by
          simp_rw [hf₁_sq, f₂, sq_abs]
          rw [integral_const_mul, w8Mass, mul_comm (Real.exp _)]
  have hI₂_lt : |I₂| < ε / 2 := by
    have hsq_lt : I₂ ^ 2 < (ε / 2) ^ 2 := hI₂_sq.trans_lt (hN n hn)
    exact (abs_lt_of_sq_lt_sq' hsq_lt (by positivity)).2
  rw [hsplit_int]
  calc |I₁ + I₂| ≤ |I₁| + |I₂| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hI₁_lt hI₂_lt
    _ = ε := add_halves ε

/-- Half-line real cosine mode `e^{(Re w + 8)u} cos(Im w · u) 1_{u < 0}` representing `(L · (w)).re`
against `W₈`. -/
def modeCos (w : ℂ) : ℝ → ℝ :=
  Set.indicator (Iio (0 : ℝ)) fun u => Real.exp ((w.re + 8) * u) * Real.cos (w.im * u)

/-- Half-line real sine mode `e^{(Re w + 8)u} sin(Im w · u) 1_{u < 0}` representing `(L · (w)).im`
against `W₈`. -/
def modeSin (w : ℂ) : ℝ → ℝ :=
  Set.indicator (Iio (0 : ℝ)) fun u => Real.exp ((w.re + 8) * u) * Real.sin (w.im * u)

theorem isW8Target_modeCos {w : ℂ} (hw : -4 < w.re) : IsW8Target (modeCos w) := by
  refine ⟨((by fun_prop : Measurable fun u : ℝ =>
      Real.exp ((w.re + 8) * u) * Real.cos (w.im * u)).indicator measurableSet_Iio),
    fun u hu => Set.indicator_of_notMem (not_lt.mpr hu) _, ?_⟩
  have ha : 0 < 2 * w.re + 8 := by linarith
  have hdom : Integrable (Set.indicator (Iio (0 : ℝ)) fun u => Real.exp ((2 * w.re + 8) * u)) :=
    ((integrableOn_exp_mul_Iic ha 0).mono_set Iio_subset_Iic_self).integrable_indicator
      measurableSet_Iio
  refine hdom.mono'
    ((((by fun_prop : Measurable fun u : ℝ =>
      Real.exp ((w.re + 8) * u) * Real.cos (w.im * u)).indicator measurableSet_Iio).pow_const 2).mul
      (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  dsimp only [modeCos]
  by_cases hu : u < 0
  · simp only [mem_Iio.mpr hu, Set.indicator_of_mem,
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    have hc : Real.cos (w.im * u) ^ 2 ≤ 1 := Real.cos_sq_le_one _
    have he : Real.exp ((w.re + 8) * u) ^ 2 * Real.exp (-(8 * u)) =
        Real.exp ((2 * w.re + 8) * u) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc (Real.exp ((w.re + 8) * u) * Real.cos (w.im * u)) ^ 2 * Real.exp (-(8 * u))
        = Real.cos (w.im * u) ^ 2 * (Real.exp ((w.re + 8) * u) ^ 2 * Real.exp (-(8 * u))) := by ring
      _ ≤ 1 * Real.exp ((2 * w.re + 8) * u) := by
          rw [he]; exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = Real.exp ((2 * w.re + 8) * u) := one_mul _
  · simp [show u ∉ Iio (0 : ℝ) from hu]

theorem isW8Target_modeSin {w : ℂ} (hw : -4 < w.re) : IsW8Target (modeSin w) := by
  refine ⟨((by fun_prop : Measurable fun u : ℝ =>
      Real.exp ((w.re + 8) * u) * Real.sin (w.im * u)).indicator measurableSet_Iio),
    fun u hu => Set.indicator_of_notMem (not_lt.mpr hu) _, ?_⟩
  have ha : 0 < 2 * w.re + 8 := by linarith
  have hdom : Integrable (Set.indicator (Iio (0 : ℝ)) fun u => Real.exp ((2 * w.re + 8) * u)) :=
    ((integrableOn_exp_mul_Iic ha 0).mono_set Iio_subset_Iic_self).integrable_indicator
      measurableSet_Iio
  refine hdom.mono'
    ((((by fun_prop : Measurable fun u : ℝ =>
      Real.exp ((w.re + 8) * u) * Real.sin (w.im * u)).indicator measurableSet_Iio).pow_const 2).mul
      (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  dsimp only [modeSin]
  by_cases hu : u < 0
  · simp only [mem_Iio.mpr hu, Set.indicator_of_mem,
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    have hs : Real.sin (w.im * u) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have he : Real.exp ((w.re + 8) * u) ^ 2 * Real.exp (-(8 * u)) =
        Real.exp ((2 * w.re + 8) * u) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc (Real.exp ((w.re + 8) * u) * Real.sin (w.im * u)) ^ 2 * Real.exp (-(8 * u))
        = Real.sin (w.im * u) ^ 2 * (Real.exp ((w.re + 8) * u) ^ 2 * Real.exp (-(8 * u))) := by ring
      _ ≤ 1 * Real.exp ((2 * w.re + 8) * u) := by
          rw [he]; exact mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
      _ = Real.exp ((2 * w.re + 8) * u) := one_mul _
  · simp [show u ∉ Iio (0 : ℝ) from hu]

theorem w8Pair_modeCos_eq_re_laplace {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {w : ℂ} (hw : -4 < w.re) :
    w8Pair (modeCos w) G = (negativeHalfLineLaplace (cx G) w).re := by
  unfold negativeHalfLineLaplace w8Pair
  rw [← Complex.re_integral (laplace_cx_integrable_of_domain hG hw)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  rcases lt_or_ge u 0 with hu | hu
  · simp only [modeCos, mem_Iio.mpr hu, Set.indicator_of_mem, cx]
    have hw_split : w * (u : ℂ) = ((w.re * u : ℝ) : ℂ) + ((w.im * u : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hw_split, Complex.exp_add_mul_I, Complex.ofReal_exp]
    have he : Real.exp ((w.re + 8) * u) * Real.exp (-(8 * u)) = Real.exp (w.re * u) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.I_re, Complex.I_im]
    calc Real.exp ((w.re + 8) * u) * Real.cos (w.im * u) * G u * Real.exp (-(8 * u))
        = (Real.exp ((w.re + 8) * u) * Real.exp (-(8 * u))) * Real.cos (w.im * u) * G u := by ring
      _ = Real.exp (w.re * u) * Real.cos (w.im * u) * G u := by rw [he]
      _ = _ := by ring
  · simp [modeCos, not_lt.mpr hu, cx, hG.support u hu]

theorem w8Pair_modeSin_eq_im_laplace {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {w : ℂ} (hw : -4 < w.re) :
    w8Pair (modeSin w) G = (negativeHalfLineLaplace (cx G) w).im := by
  unfold negativeHalfLineLaplace w8Pair
  rw [← Complex.im_integral (laplace_cx_integrable_of_domain hG hw)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  rcases lt_or_ge u 0 with hu | hu
  · simp only [modeSin, mem_Iio.mpr hu, Set.indicator_of_mem, cx]
    have hw_split : w * (u : ℂ) = ((w.re * u : ℝ) : ℂ) + ((w.im * u : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hw_split, Complex.exp_add_mul_I, Complex.ofReal_exp]
    have he : Real.exp ((w.re + 8) * u) * Real.exp (-(8 * u)) = Real.exp (w.re * u) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
    calc Real.exp ((w.re + 8) * u) * Real.sin (w.im * u) * G u * Real.exp (-(8 * u))
        = (Real.exp ((w.re + 8) * u) * Real.exp (-(8 * u))) * Real.sin (w.im * u) * G u := by ring
      _ = Real.exp (w.re * u) * Real.sin (w.im * u) * G u := by rw [he]
      _ = _ := by ring
  · simp [modeSin, not_lt.mpr hu, cx, hG.support u hu]

private theorem criticalHalfLineFullEnergy_eq_bare_add {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    criticalHalfLineFullEnergy R F = bareMixedEnergy F F + criticalAliasCoefficient R * w8Mass F := by
  have h1 := criticalHalfLineFullEnergy_add_const_mul R hF hF 1
  have hfun : (fun u => F u + 1 * F u) = fun u => (2 : ℝ) * F u := by funext u; ring
  rw [hfun, criticalHalfLineFullEnergy_const_mul] at h1
  have hmix : criticalHalfLineMixedEnergy R F F = criticalHalfLineFullEnergy R F := by linarith
  rw [← hmix, criticalHalfLineMixedEnergy_eq_bare_add,
    setIntegral_Iio_confinement_eq_univ hF.support]
  unfold w8Mass
  congr 2
  exact integral_congr_ae (Eventually.of_forall fun u => by ring)

/-- **Existence of the Birman–Schwinger on-line resolvent on `ζ`.** Under `FiniteOffLine`, for every
`a > 0` and every `W₈`-square-integrable half-line target `y`, there exists `X` in the energy domain
solving `onLineMixed X G + a W₈(X, G) = W₈(y, G)` for all `G` in the energy domain. -/
theorem exists_zetaOnLineResolvent (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {y : ℝ → ℝ} (hy : IsW8Target y) :
    ∃ X : ℝ → ℝ, SolvesZetaOnLineResolvent a y X := by
  let J : (ℝ → ℝ) → ℝ := fun X => onLineEnergy X + a * w8Mass X - 2 * w8Pair y X
  have hcoercive : ∀ {X : ℝ → ℝ}, CriticalHalfLineEnergyDomain X →
      (a / 2) * w8Mass X - (2 / a) * w8Mass y ≤ J X := by
    intro X hX
    have hcs := sq_w8Pair_le hy (isW8Target_of_domain hX)
    have h2ab : 2 * w8Pair y X ≤ (a / 2) * w8Mass X + (2 / a) * w8Mass y := by
      set u := Real.sqrt (a / 2) * Real.sqrt (w8Mass X)
      set v := Real.sqrt (2 / a) * Real.sqrt (w8Mass y)
      have hu2 : u ^ 2 = (a / 2) * w8Mass X := by
        dsimp [u]; rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (w8Mass_nonneg X)]
      have hv2 : v ^ 2 = (2 / a) * w8Mass y := by
        dsimp [v]; rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (w8Mass_nonneg y)]
      have huv : (u * v) ^ 2 = w8Mass y * w8Mass X := by
        rw [mul_pow, hu2, hv2]; field_simp; ring
      have habs : |w8Pair y X| ≤ u * v := by
        refine (abs_le_of_sq_le_sq' (hcs.trans_eq huv.symm) ?_).2
        dsimp [u, v]; positivity
      nlinarith [sq_nonneg (u - v), hu2, hv2, (abs_le.mp habs).2]
    dsimp [J]
    linarith [onLineEnergy_nonneg X, h2ab]
  set S : Set ℝ := {e : ℝ | ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧ J X = e}
  have h0_dom : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) := by
    simpa using (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 5)).const_mul 0
  have hS_ne : S.Nonempty := ⟨J (fun _ => 0), (fun _ => 0), h0_dom, rfl⟩
  have hS_bdd : BddBelow S := ⟨-(2 / a) * w8Mass y, by
    rintro e ⟨X, hX, rfl⟩
    have hc := hcoercive hX
    have hw := w8Mass_nonneg X
    nlinarith⟩
  set L : ℝ := sInf S
  have hL_le_zero : L ≤ 0 := by
    have hJ0 : J (fun _ => 0) = 0 := by
      dsimp [J, onLineEnergy, zeroValueMass, w8Mass, w8Pair, cx, negativeHalfLineLaplace]
      simp
    exact (csInf_le hS_bdd ⟨fun _ => 0, h0_dom, rfl⟩).trans_eq hJ0
  have hchoose (n : ℕ) : ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧
      J X < L + 1 / ((n : ℝ) + 1) := by
    obtain ⟨b, ⟨X, hX, rfl⟩, hb⟩ := exists_lt_of_csInf_lt hS_ne
      (lt_add_of_pos_right L (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨X, hX, hb⟩
  choose X hDX hJX using hchoose
  have hJX_le_one (n : ℕ) : J (X n) ≤ 1 := by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    linarith [hJX n, hL_le_zero]
  set M₀ : ℝ := (2 / a) * (1 + (2 / a) * w8Mass y)
  have hM₀_nn : 0 ≤ M₀ := by dsimp [M₀]; have := w8Mass_nonneg y; positivity
  have hw8_X (n : ℕ) : w8Mass (X n) ≤ M₀ := by
    have hc := (hcoercive (hDX n)).trans (hJX_le_one n)
    dsimp [M₀]
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    linarith
  have hsq_X (n : ℕ) : (∫ u, X n u ^ 2) ≤ M₀ := by
    refine (integral_mono (hDX n).sq (hDX n).exponential fun u => ?_).trans (hw8_X n)
    dsimp only
    rcases le_or_gt 0 u with hu | hu
    · rw [(hDX n).support u hu]; simp
    · exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by linarith))
  have hon_X (n : ℕ) : onLineEnergy (X n) ≤ 1 + (2 / a) * w8Mass y + a * M₀ := by
    have hcs := sq_w8Pair_le hy (isW8Target_of_domain (hDX n))
    have h2ab : 2 * w8Pair y (X n) ≤ a * M₀ + (2 / a) * w8Mass y := by
      have hc := hcoercive (hDX n)
      have hw := w8Mass_nonneg (X n)
      dsimp [J] at hc
      linarith [onLineEnergy_nonneg (X n), hw8_X n, mul_le_mul_of_nonneg_left (hw8_X n) ha.le]
    have hJ := hJX_le_one n
    dsimp [J] at hJ
    linarith [w8Mass_nonneg (X n), mul_nonneg ha.le (w8Mass_nonneg (X n))]
  set P₁ : ℝ := ∫ u : ℝ, probe 1 u
  have hP₁_nn : 0 ≤ P₁ := integral_nonneg fun u => probe_nonneg 1 u
  set B₀ : ℝ := (1 + (2 / a) * w8Mass y + a * M₀) +
    (offLineCopyFinset hfin).card * ((M₀ + P₁) / 2) ^ 2 +
    criticalAliasCoefficient 1 * M₀
  have hE1_X (n : ℕ) : criticalHalfLineFullEnergy 1 (X n) ≤ B₀ := by
    rw [criticalHalfLineFullEnergy_eq_bare_add (hDX n),
      bareMixedEnergy_eq_onLineMixed_add_re_offLine (hDX n) (hDX n) hfin, onLineMixed_self]
    have hoff_le : (∑ q ∈ offLineCopyFinset hfin,
        negativeHalfLineLaplace (cx (X n)) (centredZero q) *
          negativeHalfLineLaplace (cx (X n)) (-centredZero q)).re ≤
        (offLineCopyFinset hfin).card * ((M₀ + P₁) / 2) ^ 2 := by
      refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      have hterm : ∀ q ∈ offLineCopyFinset hfin,
          ‖negativeHalfLineLaplace (cx (X n)) (centredZero q) *
            negativeHalfLineLaplace (cx (X n)) (-centredZero q)‖ ≤ ((M₀ + P₁) / 2) ^ 2 := by
        intro q _
        rw [norm_mul, sq]
        have b1 := (norm_laplace_pos_centredZero_le (hDX n) q).trans
          (by dsimp [w8Mass, P₁] at hw8_X ⊢; linarith [hw8_X n])
        have b2 := (norm_laplace_neg_centredZero_le_domain (hDX n) q).trans
          (by dsimp [w8Mass, P₁] at hw8_X ⊢; linarith [hw8_X n])
        exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      simpa using Finset.sum_le_card_nsmul (offLineCopyFinset hfin) _ _ hterm
    have ha1 := (criticalAliasCoefficient_positive one_pos).le
    dsimp [B₀]
    linarith [hon_X n, hoff_le, mul_le_mul_of_nonneg_left (hw8_X n) ha1]
  -- Rescale `X n` by `c = (Real.sqrt (M₀ + 1))⁻¹` and take window approximations
  set c : ℝ := (Real.sqrt (M₀ + 1))⁻¹
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hc_sq : c ^ 2 = (M₀ + 1)⁻¹ := by
    dsimp [c]; rw [inv_pow, Real.sq_sqrt (by positivity)]
  let Y : ℕ → ℝ → ℝ := fun n u => c * X n u
  have hDY (n : ℕ) : CriticalHalfLineEnergyDomain (Y n) := (hDX n).const_mul c
  have hmass_Y (n : ℕ) : (∫ u, Y n u ^ 2) ≤ 1 := by
    have hfun : (fun u => Y n u ^ 2) = fun u => c ^ 2 * X n u ^ 2 := by funext u; dsimp [Y]; ring
    rw [hfun, integral_const_mul, hc_sq, inv_mul_le_iff₀ (by positivity)]
    linarith [hsq_X n]
  have hw8_Y (n : ℕ) : w8Mass (Y n) ≤ 1 := by
    have hfun : (fun u => Y n u ^ 2 * Real.exp (-(8 * u))) =
        fun u => c ^ 2 * (X n u ^ 2 * Real.exp (-(8 * u))) := by funext u; dsimp [Y]; ring
    unfold w8Mass
    rw [hfun, integral_const_mul, hc_sq, inv_mul_le_iff₀ (by positivity)]
    linarith [hw8_X n]
  have hE1_Y (n : ℕ) : criticalHalfLineFullEnergy 1 (Y n) ≤ c ^ 2 * max B₀ 0 := by
    dsimp [Y]
    rw [criticalHalfLineFullEnergy_const_mul]
    exact mul_le_mul_of_nonneg_left ((hE1_X n).trans (le_max_left B₀ 0)) (sq_nonneg c)
  have hrec (n : ℕ) := exists_window_energy_recovery one_pos (hDY n) (hmass_Y n)
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose A H hA hHwin hmH hdH hH8 heH using hrec
  have hDH (n : ℕ) : CriticalHalfLineEnergyDomain (H n) :=
    criticalHalfLineEnergyDomain_of_window (hHwin n)
  have hmH1 (n : ℕ) : (∫ u, H n u ^ 2) ≤ 1 := (hmH n).trans (hmass_Y n)
  have hH8_le (n : ℕ) : (∫ u, H n u ^ 2 * Real.exp (-(8 * u))) ≤ 2 :=
    (hH8 n).trans (by unfold w8Mass at hw8_Y; linarith [hw8_Y n])
  have hE1_H (n : ℕ) : criticalHalfLineFullEnergy 1 (H n) ≤ c ^ 2 * max B₀ 0 + 1 := by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    linarith [heH n, hE1_Y n, h1]
  have hweil_H (n : ℕ) : weilQuad (H n) ≤ c ^ 2 * max B₀ 0 + 1 := by
    have h := hE1_H n
    rw [criticalHalfLineFullEnergy,
      ← weilQuad_eq_arch_sub_prime_add_pole (hHwin n).contDiff (hHwin n).hasCompactSupport] at h
    have hp : 0 ≤ criticalAliasCoefficient 1 *
        ∫ u in Iio 0, H n u ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg (criticalAliasCoefficient_positive one_pos).le
        (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    linarith
  obtain ⟨F₀, s, hs, hF₀m, hF₀i, hF₀2, _, hF₀8, hw8_F₀, hF₀s, hL2_HF₀, hL1_HF₀, -⟩ :=
    exists_strong_negative_limit_of_bounded_weilQuad
      (fun n => (hHwin n).contDiff) (fun n => (hHwin n).hasCompactSupport)
      hmH1 (by norm_num : (0 : ℝ) ≤ 2) hH8_le
      (fun n u hu => (hDH n).support u ((by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).trans hu).le)
      hweil_H
  -- Check `CriticalHalfLineEnergyDomain F₀`
  let J_int : ℝ := ∫ u : ℝ, Real.exp (-|u|)
  let C_arch : ℝ := 2 * vonMangoldtThreeHalvesMass + 2 * J_int
  have hC_arch : 0 ≤ C_arch := add_nonneg
    (mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg)
    (mul_nonneg (by norm_num) (integral_nonneg fun u => (Real.exp_pos _).le))
  have harch_H (n : ℕ) : archForm (H n) ≤ (c ^ 2 * max B₀ 0 + 1) + C_arch * 3 := by
    have hsrc : exponentialSourceMass (H n) ≤ 3 := by
      have h := (exponentialSourceMass_le_of_support (Y := 0) le_rfl
        (hDH n).meas.aestronglyMeasurable (hDH n).sq (hDH n).exponential
        (Eventually.of_forall fun u hu => (hDH n).support u hu.le)).2
      simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at h
      linarith [hmH1 n, hH8_le n]
    have hp := (le_abs_self (primeSum (H n))).trans (hDH n).prime_bound
    have hsin := (hDH n).sinh_bound
    have hsrc' := mul_le_mul_of_nonneg_left hsrc hC_arch
    have he := hE1_H n
    have hw0 : 0 ≤ criticalAliasCoefficient 1 *
        ∫ u in Iio 0, H n u ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg (criticalAliasCoefficient_positive one_pos).le
        (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    dsimp only [criticalHalfLineFullEnergy] at he
    dsimp only [C_arch, J_int] at hsrc' ⊢
    nlinarith [hp, hsin, hsrc', he, hw0, sq_nonneg (coshHalfMoment (H n))]
  have hΓ_F₀ := integrable_gamma_of_L1_limit_bounded_archForm
    (fun j => (hDH (s j)).integrable) (fun j => (hDH (s j)).sq)
    (fun j => (hDH (s j)).gamma) hF₀i hF₀2 hL1_HF₀
    (fun j => hmH1 (s j)) (fun j => harch_H (s j))
  have hDF₀ : CriticalHalfLineEnergyDomain F₀ := ⟨hF₀m, hF₀i, hF₀2, hF₀8, hF₀s, hΓ_F₀⟩
  -- Rescale back to `Xstar = c⁻¹ • F₀`
  set Xstar : ℝ → ℝ := fun u => c⁻¹ * F₀ u
  have hDXstar : CriticalHalfLineEnergyDomain Xstar := hDF₀.const_mul c⁻¹
  have herr_HY : Tendsto (fun j => ∫ u, (H (s j) u - Y (s j) u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun u => sq_nonneg _)
      (fun j => (hdH (s j)).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hs.tendsto_atTop)
  have hL2_YF₀ : Tendsto (fun j => ∫ u, (Y (s j) u - F₀ u) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun j => integral_nonneg fun u => sq_nonneg _) (fun j => ?_)
      ((herr_HY.const_mul 2).add (hL2_HF₀.const_mul 2) |>.congr'
        (Eventually.of_forall fun _ => rfl) |> fun h => by simpa using h)
    have hi1 : Integrable fun u => (H (s j) u - Y (s j) u) ^ 2 := by
      have hd : CriticalHalfLineEnergyDomain (fun u => H (s j) u + (-1) * Y (s j) u) :=
        (hDH (s j)).add_const_mul (hDY (s j)) (-1)
      exact hd.sq.congr (Eventually.of_forall fun u => by dsimp; ring)
    have hi2 : Integrable fun u => (H (s j) u - F₀ u) ^ 2 := by
      have hd : CriticalHalfLineEnergyDomain (fun u => H (s j) u + (-1) * F₀ u) :=
        (hDH (s j)).add_const_mul hDF₀ (-1)
      exact hd.sq.congr (Eventually.of_forall fun u => by dsimp; ring)
    have hdy : Integrable fun u => (Y (s j) u - F₀ u) ^ 2 := by
      have hd : CriticalHalfLineEnergyDomain (fun u => Y (s j) u + (-1) * F₀ u) :=
        (hDY (s j)).add_const_mul hDF₀ (-1)
      exact hd.sq.congr (Eventually.of_forall fun u => by dsimp; ring)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul 2) (hi2.const_mul 2)]
    refine integral_mono hdy ((hi1.const_mul 2).add (hi2.const_mul 2)) fun u => ?_
    dsimp only
    nlinarith [sq_nonneg ((H (s j) u - Y (s j) u) + (H (s j) u - F₀ u))]
  have hL2_XX : Tendsto (fun j => ∫ u, (X (s j) u - Xstar u) ^ 2) atTop (𝓝 0) := by
    have hfun : ∀ j, (∫ u, (X (s j) u - Xstar u) ^ 2) =
        (c⁻¹) ^ 2 * ∫ u, (Y (s j) u - F₀ u) ^ 2 := by
      intro j
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp [Y, Xstar]
      field_simp [hc_pos.ne']
    simpa [hfun] using hL2_YF₀.const_mul ((c⁻¹) ^ 2)
  -- Pass `J (X (s j))` to the limit `Xstar` via `tendsto_w8Pair_of_L2_tendsto`
  set M_tot : ℝ := max M₀ (w8Mass Xstar)
  have hM_tot : 0 ≤ M_tot := le_max_of_le_left hM₀_nn
  have hw8_X_tot (j : ℕ) : w8Mass (X (s j)) ≤ M_tot := (hw8_X (s j)).trans (le_max_left _ _)
  have hw8_Xstar_tot : w8Mass Xstar ≤ M_tot := le_max_right _ _
  have hy_lim : Tendsto (fun j => w8Pair y (X (s j))) atTop (𝓝 (w8Pair y Xstar)) :=
    tendsto_w8Pair_of_L2_tendsto (fun j => isW8Target_of_domain (hDX (s j)))
      (isW8Target_of_domain hDXstar) hy hM_tot hw8_X_tot hw8_Xstar_tot hL2_XX
  have hself_lim : Tendsto (fun j => w8Pair Xstar (X (s j))) atTop (𝓝 (w8Mass Xstar)) := by
    simpa [w8Pair_self] using tendsto_w8Pair_of_L2_tendsto
      (fun j => isW8Target_of_domain (hDX (s j))) (isW8Target_of_domain hDXstar)
      (isW8Target_of_domain hDXstar) hM_tot hw8_X_tot hw8_Xstar_tot hL2_XX
  have hlap_lim : ∀ q : onLineCopies,
      Tendsto (fun j => zeroValueMass (X (s j)) q) atTop (𝓝 (zeroValueMass Xstar q)) := by
    intro q
    have hw : -4 < (centredZero (q : XiZeroCopy)).re := by
      have := (abs_lt.mp (abs_re_centredZero_lt (q : XiZeroCopy))).1; linarith
    have hre_lim : Tendsto (fun j => (negativeHalfLineLaplace (cx (X (s j))) (centredZero q)).re)
        atTop (𝓝 (negativeHalfLineLaplace (cx Xstar) (centredZero q)).re) := by
      simpa [w8Pair_modeCos_eq_re_laplace (hDX _) hw, w8Pair_modeCos_eq_re_laplace hDXstar hw]
        using tendsto_w8Pair_of_L2_tendsto (fun j => isW8Target_of_domain (hDX (s j)))
          (isW8Target_of_domain hDXstar) (isW8Target_modeCos hw)
          hM_tot hw8_X_tot hw8_Xstar_tot hL2_XX
    have him_lim : Tendsto (fun j => (negativeHalfLineLaplace (cx (X (s j))) (centredZero q)).im)
        atTop (𝓝 (negativeHalfLineLaplace (cx Xstar) (centredZero q)).im) := by
      simpa [w8Pair_modeSin_eq_im_laplace (hDX _) hw, w8Pair_modeSin_eq_im_laplace hDXstar hw]
        using tendsto_w8Pair_of_L2_tendsto (fun j => isW8Target_of_domain (hDX (s j)))
          (isW8Target_of_domain hDXstar) (isW8Target_modeSin hw)
          hM_tot hw8_X_tot hw8_Xstar_tot hL2_XX
    have hsq_eq : ∀ G : ℝ → ℝ, zeroValueMass G q =
        (negativeHalfLineLaplace (cx G) (centredZero q)).re ^ 2 +
          (negativeHalfLineLaplace (cx G) (centredZero q)).im ^ 2 :=
      fun G => Complex.sq_norm _
    simpa [hsq_eq] using (hre_lim.pow 2).add (him_lim.pow 2)
  have hblock_le : ∀ T : Finset onLineCopies,
      ∑ q ∈ T, zeroValueMass Xstar q ≤ L - a * w8Mass Xstar + 2 * w8Pair y Xstar := by
    intro T
    have hT_lim : Tendsto (fun j =>
        (∑ q ∈ T, zeroValueMass (X (s j)) q) + a * (2 * w8Pair Xstar (X (s j)) - w8Mass Xstar) -
          2 * w8Pair y (X (s j))) atTop
        (𝓝 ((∑ q ∈ T, zeroValueMass Xstar q) + a * w8Mass Xstar - 2 * w8Pair y Xstar)) := by
      have h1 := tendsto_finsetSum T fun q _ => hlap_lim q
      have h2 : Tendsto (fun j => a * (2 * w8Pair Xstar (X (s j)) - w8Mass Xstar)) atTop
          (𝓝 (a * w8Mass Xstar)) := by
        have := ((hself_lim.const_mul 2).sub_const (w8Mass Xstar)).const_mul a
        simpa [two_mul] using this
      exact (h1.add h2).sub (hy_lim.const_mul 2)
    have hupper_lim : Tendsto (fun j => L + 1 / ((s j : ℝ) + 1)) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hs.tendsto_atTop)
    have hle_L : (∑ q ∈ T, zeroValueMass Xstar q) + a * w8Mass Xstar - 2 * w8Pair y Xstar ≤ L := by
      refine le_of_tendsto_of_tendsto hT_lim hupper_lim (Eventually.of_forall fun j => ?_)
      have hsum_le : ∑ q ∈ T, zeroValueMass (X (s j)) q ≤ onLineEnergy (X (s j)) :=
        (domain_zeroParseval_of_finiteOffLine (hDX (s j)) hfin).1.sum_le_tsum T
          fun q _ => zeroValueMass_nonneg _ q
      have hw8_le : 2 * w8Pair Xstar (X (s j)) - w8Mass Xstar ≤ w8Mass (X (s j)) := by
        have hdiff := w8Mass_add_const_mul (isW8Target_of_domain (hDX (s j)))
          (isW8Target_of_domain hDXstar) (-1)
        have hnn := w8Mass_nonneg (fun u => X (s j) u + (-1) * Xstar u)
        rw [w8Pair_comm] at hdiff
        linarith
      have hJ := (hJX (s j)).le
      dsimp [J] at hJ
      linarith [mul_le_mul_of_nonneg_left hw8_le ha.le]
    linarith
  have hon_le : onLineEnergy Xstar ≤ L - a * w8Mass Xstar + 2 * w8Pair y Xstar :=
    Real.tsum_le_of_sum_le (fun q => zeroValueMass_nonneg Xstar q) hblock_le
  have hJ_eq : J Xstar = L := le_antisymm (by dsimp [J]; linarith)
    (csInf_le hS_bdd ⟨Xstar, hDXstar, rfl⟩)
  -- First variation gives the weak equation
  refine ⟨Xstar, hDXstar, fun G hG => ?_⟩
  have hquad : ∀ t : ℝ,
      0 ≤ 2 * t * (onLineMixed Xstar G + a * w8Pair Xstar G - w8Pair y G) +
        t ^ 2 * (onLineEnergy G + a * w8Mass G) := by
    intro t
    have hDG : CriticalHalfLineEnergyDomain (fun u => Xstar u + t * G u) :=
      hDXstar.add_const_mul hG t
    have hmin : J Xstar ≤ J (fun u => Xstar u + t * G u) := by
      rw [hJ_eq]; exact csInf_le hS_bdd ⟨_, hDG, rfl⟩
    have hon_t := onLineEnergy_add_const_mul hDXstar hG hfin t
    have hw8_t := w8Mass_add_const_mul (isW8Target_of_domain hDXstar)
      (isW8Target_of_domain hG) t
    have hy_t : w8Pair y (fun u => Xstar u + t * G u) = w8Pair y Xstar + t * w8Pair y G := by
      rw [w8Pair_comm y, w8Pair_add_left (isW8Target_of_domain hDXstar)
        (isW8Target_const_mul (isW8Target_of_domain hG) t) hy, w8Pair_const_mul_left,
        w8Pair_comm Xstar y, w8Pair_comm G y]
    dsimp [J] at hmin
    rw [hon_t, hw8_t, hy_t] at hmin
    linarith
  have h0 := eq_zero_of_forall_quadratic_nonneg
    (add_nonneg (onLineEnergy_nonneg G) (mul_nonneg ha.le (w8Mass_nonneg G))) hquad
  linarith

/-- Canonical representative `R_a(y)` of the Birman–Schwinger on-line resolvent on `ζ`. -/
def zetaOnLineResolvent (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {y : ℝ → ℝ} (hy : IsW8Target y) : ℝ → ℝ :=
  Classical.choose (exists_zetaOnLineResolvent hfin ha hy)

theorem zetaOnLineResolvent_solves (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {y : ℝ → ℝ} (hy : IsW8Target y) :
    SolvesZetaOnLineResolvent a y (zetaOnLineResolvent hfin ha hy) :=
  Classical.choose_spec (exists_zetaOnLineResolvent hfin ha hy)

/-- Real cosine mode resolvent `Φ_{cos,a}(w) = R_a(modeCos w)` for `-4 < Re w`. -/
def zetaModeResolventCos (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : -4 < w.re) : ℝ → ℝ :=
  zetaOnLineResolvent hfin ha (isW8Target_modeCos hw)

/-- Real sine mode resolvent `Φ_{sin,a}(w) = R_a(modeSin w)` for `-4 < Re w`. -/
def zetaModeResolventSin (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : -4 < w.re) : ℝ → ℝ :=
  zetaOnLineResolvent hfin ha (isW8Target_modeSin hw)

theorem zetaModeResolventCos_solves (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : -4 < w.re) :
    CriticalHalfLineEnergyDomain (zetaModeResolventCos hfin ha hw) ∧
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        onLineMixed (zetaModeResolventCos hfin ha hw) G +
          a * w8Pair (zetaModeResolventCos hfin ha hw) G =
        (negativeHalfLineLaplace (cx G) w).re := by
  have hs := zetaOnLineResolvent_solves hfin ha (isW8Target_modeCos hw)
  exact ⟨hs.1, fun G hG => (hs.2 G hG).trans (w8Pair_modeCos_eq_re_laplace hG hw)⟩

theorem zetaModeResolventSin_solves (hfin : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : -4 < w.re) :
    CriticalHalfLineEnergyDomain (zetaModeResolventSin hfin ha hw) ∧
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        onLineMixed (zetaModeResolventSin hfin ha hw) G +
          a * w8Pair (zetaModeResolventSin hfin ha hw) G =
        (negativeHalfLineLaplace (cx G) w).im := by
  have hs := zetaOnLineResolvent_solves hfin ha (isW8Target_modeSin hw)
  exact ⟨hs.1, fun G hG => (hs.2 G hG).trans (w8Pair_modeSin_eq_im_laplace hG hw)⟩

private theorem isW8Target_finset_sum {ι : Type*} (S : Finset ι) {y : ι → ℝ → ℝ}
    (hy : ∀ i ∈ S, IsW8Target (y i)) :
    IsW8Target (fun u => ∑ i ∈ S, y i u) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0_dom : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) := by
      simpa using (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 5)).const_mul 0
    simpa using isW8Target_of_domain h0_dom
  | insert i T hi ih =>
    have hsum : (fun u => ∑ j ∈ insert i T, y j u) =
        fun u => y i u + ∑ j ∈ T, y j u := by funext u; simp [Finset.sum_insert hi]
    rw [hsum]
    exact isW8Target_add (hy i (Finset.mem_insert_self i T))
      (ih fun j hj => hy j (Finset.mem_insert_of_mem hj))

private theorem w8Pair_finset_sum_left {ι : Type*} (S : Finset ι) {y : ι → ℝ → ℝ} {G : ℝ → ℝ}
    (hy : ∀ i ∈ S, IsW8Target (y i)) (hG : IsW8Target G) :
    w8Pair (fun u => ∑ i ∈ S, y i u) G = ∑ i ∈ S, w8Pair (y i) G := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (fun u : ℝ => ∑ i ∈ (∅ : Finset ι), y i u) = fun u => (0 : ℝ) * G u := by
      funext u; simp
    rw [h0, w8Pair_const_mul_left, zero_mul, Finset.sum_empty]
  | insert i T hi ih =>
    have hsum : (fun u => ∑ j ∈ insert i T, y j u) =
        fun u => y i u + ∑ j ∈ T, y j u := by funext u; simp [Finset.sum_insert hi]
    rw [hsum, w8Pair_add_left (hy i (Finset.mem_insert_self i T))
      (isW8Target_finset_sum T fun j hj => hy j (Finset.mem_insert_of_mem hj)) hG,
      Finset.sum_insert hi, ih fun j hj => hy j (Finset.mem_insert_of_mem hj)]

private theorem solvesZetaOnLineResolvent_finset_sum {ι : Type*} (S : Finset ι)
    {a : ℝ} {y X : ι → ℝ → ℝ}
    (hfin : BacklundConverse.FiniteOffLine)
    (hy : ∀ i ∈ S, IsW8Target (y i))
    (hX : ∀ i ∈ S, SolvesZetaOnLineResolvent a (y i) (X i)) :
    SolvesZetaOnLineResolvent a (fun u => ∑ i ∈ S, y i u) (fun u => ∑ i ∈ S, X i u) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0_dom : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) := by
      simpa using (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 5)).const_mul 0
    refine ⟨by simpa using h0_dom, fun G _ => ?_⟩
    have h0X : (fun u : ℝ => ∑ i ∈ (∅ : Finset ι), X i u) = fun u => (0 : ℝ) * G u := by
      funext u; simp
    have h0y : (fun u : ℝ => ∑ i ∈ (∅ : Finset ι), y i u) = fun u => (0 : ℝ) * G u := by
      funext u; simp
    rw [h0X, onLineMixed_const_mul_left, zero_mul, w8Pair_const_mul_left, zero_mul, mul_zero,
      add_zero, h0y, w8Pair_const_mul_left, zero_mul]
  | insert i T hi ih =>
    have hsolT := ih (fun j hj => hy j (Finset.mem_insert_of_mem hj))
      (fun j hj => hX j (Finset.mem_insert_of_mem hj))
    have hyT := isW8Target_finset_sum T fun j hj => hy j (Finset.mem_insert_of_mem hj)
    have hyi := hy i (Finset.mem_insert_self i T)
    have hXi := hX i (Finset.mem_insert_self i T)
    have hsum_y : (fun u => ∑ j ∈ insert i T, y j u) =
        fun u => y i u + ∑ j ∈ T, y j u := by funext u; simp [Finset.sum_insert hi]
    have hsum_X : (fun u => ∑ j ∈ insert i T, X j u) =
        fun u => X i u + ∑ j ∈ T, X j u := by funext u; simp [Finset.sum_insert hi]
    rw [hsum_y, hsum_X]
    refine ⟨by simpa [one_mul] using hXi.1.add_const_mul hsolT.1 1, fun G hG => ?_⟩
    rw [onLineMixed_add_left hXi.1 hsolT.1 hG hfin,
      w8Pair_add_left (isW8Target_of_domain hXi.1) (isW8Target_of_domain hsolT.1)
        (isW8Target_of_domain hG),
      w8Pair_add_left hyi hyT (isW8Target_of_domain hG)]
    linarith [hXi.2 G hG, hsolT.2 G hG]

theorem neg_centredZero_re_gt_neg_four (q : XiZeroCopy) : -4 < (-centredZero q).re := by
  have := (abs_lt.mp (abs_re_centredZero_lt q)).2
  simp; linarith

/-- **Birman–Schwinger off-line resolvent formula for every confined null vector on `ζ`.** Under
`FiniteOffLine`, every confined null vector `(R, F)` (`R > 0`, `a = a(R)`) equals almost everywhere
the finite off-line linear combination of mode resolvents attached to `offLineCopyFinset hfin`. -/
theorem nullVector_ae_eq_offLineResolvent_of_finiteOffLine {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) (hfin : BacklundConverse.FiniteOffLine) :
    let ha := criticalAliasCoefficient_positive hR
    F =ᵐ[volume] fun u =>
      ∑ q ∈ offLineCopyFinset hfin,
        (-((negativeHalfLineLaplace (cx F) (centredZero q)).re) *
            zetaModeResolventCos hfin ha (neg_centredZero_re_gt_neg_four q) u +
          (negativeHalfLineLaplace (cx F) (centredZero q)).im *
            zetaModeResolventSin hfin ha (neg_centredZero_re_gt_neg_four q) u) := by
  intro ha
  set a := criticalAliasCoefficient R
  let yTerm : XiZeroCopy → ℝ → ℝ := fun q u =>
    -(negativeHalfLineLaplace (cx F) (centredZero q)).re * modeCos (-centredZero q) u +
      (negativeHalfLineLaplace (cx F) (centredZero q)).im * modeSin (-centredZero q) u
  let XTerm : XiZeroCopy → ℝ → ℝ := fun q u =>
    -(negativeHalfLineLaplace (cx F) (centredZero q)).re *
        zetaModeResolventCos hfin ha (neg_centredZero_re_gt_neg_four q) u +
      (negativeHalfLineLaplace (cx F) (centredZero q)).im *
        zetaModeResolventSin hfin ha (neg_centredZero_re_gt_neg_four q) u
  have hyTerm : ∀ q ∈ offLineCopyFinset hfin, IsW8Target (yTerm q) := fun q _ =>
    isW8Target_add
      (isW8Target_const_mul (isW8Target_modeCos (neg_centredZero_re_gt_neg_four q)) _)
      (isW8Target_const_mul (isW8Target_modeSin (neg_centredZero_re_gt_neg_four q)) _)
  have hXTerm : ∀ q ∈ offLineCopyFinset hfin, SolvesZetaOnLineResolvent a (yTerm q) (XTerm q) := by
    intro q _
    set α := -(negativeHalfLineLaplace (cx F) (centredZero q)).re
    set β := (negativeHalfLineLaplace (cx F) (centredZero q)).im
    have hw := neg_centredZero_re_gt_neg_four q
    have hc := zetaModeResolventCos_solves hfin ha hw
    have hs := zetaModeResolventSin_solves hfin ha hw
    refine ⟨(hc.1.const_mul α).add_const_mul hs.1 β, fun G hG => ?_⟩
    dsimp [XTerm, yTerm]
    rw [onLineMixed_add_left (hc.1.const_mul α) (hs.1.const_mul β) hG hfin,
      onLineMixed_const_mul_left, onLineMixed_const_mul_left,
      w8Pair_add_left (isW8Target_of_domain (hc.1.const_mul α))
        (isW8Target_of_domain (hs.1.const_mul β)) (isW8Target_of_domain hG),
      w8Pair_const_mul_left, w8Pair_const_mul_left,
      w8Pair_add_left (isW8Target_const_mul (isW8Target_modeCos hw) α)
        (isW8Target_const_mul (isW8Target_modeSin hw) β) (isW8Target_of_domain hG),
      w8Pair_const_mul_left, w8Pair_const_mul_left,
      w8Pair_modeCos_eq_re_laplace hG hw, w8Pair_modeSin_eq_im_laplace hG hw]
    linarith [hc.2 G hG, hs.2 G hG]
  have hsol_sum := solvesZetaOnLineResolvent_finset_sum (offLineCopyFinset hfin) hfin hyTerm hXTerm
  have hsol_F : SolvesZetaOnLineResolvent a (fun u => ∑ q ∈ offLineCopyFinset hfin, yTerm q u) F := by
    refine ⟨hF.1, fun G hG => ?_⟩
    have hnull := hF.2.2 G hG
    rw [criticalHalfLineMixedEnergy_eq_bare_add,
      setIntegral_Iio_confinement_eq_univ hF.1.support,
      bareMixedEnergy_eq_onLineMixed_add_re_offLine hF.1 hG hfin] at hnull
    have hw_eq : (∫ u : ℝ, F u * G u * Real.exp (-(8 * u))) = w8Pair F G := rfl
    rw [hw_eq] at hnull
    have hyG : w8Pair (fun u => ∑ q ∈ offLineCopyFinset hfin, yTerm q u) G =
        -(∑ q ∈ offLineCopyFinset hfin,
          negativeHalfLineLaplace (cx F) (centredZero q) *
            negativeHalfLineLaplace (cx G) (-centredZero q)).re := by
      rw [w8Pair_finset_sum_left (offLineCopyFinset hfin) hyTerm (isW8Target_of_domain hG),
        Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hw := neg_centredZero_re_gt_neg_four q
      dsimp [yTerm]
      rw [w8Pair_add_left
        (isW8Target_const_mul (isW8Target_modeCos hw) _)
        (isW8Target_const_mul (isW8Target_modeSin hw) _)
        (isW8Target_of_domain hG),
        w8Pair_const_mul_left, w8Pair_const_mul_left,
        w8Pair_modeCos_eq_re_laplace hG hw, w8Pair_modeSin_eq_im_laplace hG hw, Complex.mul_re]
      ring
    linarith
  exact solvesZetaOnLineResolvent_ae_unique hfin ha hsol_F hsol_sum

/-! ### 4. General null-vector translation defect and cross-rung wall law -/

private theorem alias_mul_heatedBeyondWall_eq {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    (criticalAliasCoefficient 1 : ℂ) * heatedBeyondWall ε 1 hF T =
      (criticalAliasCoefficient R : ℂ) * heatedBeyondWall ε R hF T := by
  have h1 := integral_stateHeatSymbol_mul_stateMeromorphic_left (W₀ := 1) hF hε T
    (a := -2) (by norm_num)
  have hR' := integral_stateHeatSymbol_mul_stateMeromorphic_left (W₀ := R) hF hε T
    (a := -2) (by norm_num)
  have ha1 : (criticalAliasCoefficient 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive one_pos).ne'
  have haR : (criticalAliasCoefficient R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hR).ne'
  have hint_eq : (criticalAliasCoefficient 1 : ℂ) *
      (∫ t : ℝ, stateHeatSymbol ε T ((-2 : ℝ) + t * I) *
        stateMeromorphic 1 F ((-2 : ℝ) + t * I - 8)) =
      (criticalAliasCoefficient R : ℂ) *
      (∫ t : ℝ, stateHeatSymbol ε T ((-2 : ℝ) + t * I) *
        stateMeromorphic R F ((-2 : ℝ) + t * I - 8)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    unfold stateMeromorphic
    field_simp [ha1, haR]
  rw [h1, hR'] at hint_eq
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_left_cancel₀ h2pi (by linear_combination hint_eq)

/-- Two-sided heated zero-series identity for any confined null vector `(R, F)` (`R > 0`). -/
theorem nullVector_hasSum_heated_zeroSeries {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q))
      ((criticalAliasCoefficient R : ℂ) *
        (heatedBeyondWall ε R hF.1 T - ((heatedState ε F T : ℝ) : ℂ))) := by
  have hs := hasSum_heated_zeroSeries_of_normalisedStar hF.1
    (satisfiesNormalisedStar_of_nullVector hR hF) hε T
  rwa [alias_mul_heatedBeyondWall_eq hR hF.1 hε T, ← mul_sub] at hs

/-- Heated zero pairing against a translated profile for any confined null vector `(R, F)`. -/
theorem nullVector_hasSum_zeroPairing_heated_translate {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {ε : ℝ} (hε : 0 < ε) (k : ℝ) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) * stateHeatSymbol ε k (centredZero q))
      (∫ T : ℝ, cx (fun x => G (x - k)) T * ((criticalAliasCoefficient R : ℂ) *
        (heatedBeyondWall ε R hF.1 T - ((heatedState ε F T : ℝ) : ℂ)))) := by
  have hzre : ∀ q : XiZeroCopy, (centredZero q).re < 1 / 2 := fun q =>
    (abs_lt.mp (abs_re_centredZero_lt q)).2
  have hterm : ∀ q : XiZeroCopy,
      (∫ T : ℝ, cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))) =
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          stateHeatSymbol ε k (centredZero q) := by
    intro q
    have e : (fun T : ℝ => cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε (T + k) (centredZero q))) = fun T : ℝ =>
        (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q)) *
          (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) := by
      funext T; rw [stateHeatSymbol_add]; ring
    have hL : negativeHalfLineLaplace (cx G) (-centredZero q) =
        ∫ T : ℝ, Complex.exp (-centredZero q * (T : ℂ)) * cx G T := rfl
    rw [e, integral_const_mul, hL]; ring
  have hint : ∀ q : XiZeroCopy, Integrable fun T : ℝ => cx G T *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q)) := by
    intro q
    refine ((integrable_cexp_neg_mul_cx hG (z := centredZero q) (by linarith [hzre q])).const_mul
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε k (centredZero q))).congr (Eventually.of_forall fun T => ?_)
    show negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q) *
        (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) =
      cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))
    rw [stateHeatSymbol_add]; ring
  have hGm := integrable_abs_mul_exp_of_domain hG (c := -(1 / 2)) (by norm_num)
  have hsumk := (nullVector_hasSum_heated_zeroSeries hR hF hε k).summable.norm
  have hbound : ∀ q : XiZeroCopy,
      (∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))‖) ≤
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q)‖ *
        ∫ u : ℝ, |G u| * Real.exp (-(1 / 2) * u) := by
    intro q
    rw [← integral_const_mul]
    refine integral_mono (hint q).norm (hGm.const_mul _) fun T => ?_
    have hre : (-centredZero q * (T : ℂ)).re = -(centredZero q).re * T := by simp
    have hgx : |G T| * Real.exp (-(centredZero q).re * T) ≤
        |G T| * Real.exp (-(1 / 2) * T) := by
      rcases le_or_gt 0 T with hT | hT
      · rw [hG.support T hT, abs_zero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        nlinarith [mul_pos (sub_pos.mpr (hzre q)) (neg_pos.mpr hT)]
    show ‖((G T : ℝ) : ℂ) * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))‖ ≤
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q)‖ *
        (|G T| * Real.exp (-(1 / 2) * T))
    rw [stateHeatSymbol_add, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp (-centredZero q * (T : ℂ)), hre]
    calc |G T| * (‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
          (‖stateHeatSymbol ε k (centredZero q)‖ * Real.exp (-(centredZero q).re * T)))
        = ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
            ‖stateHeatSymbol ε k (centredZero q)‖ * (|G T| * Real.exp (-(centredZero q).re * T)) := by
            ring
      _ ≤ ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
            ‖stateHeatSymbol ε k (centredZero q)‖ * (|G T| * Real.exp (-(1 / 2) * T)) :=
            mul_le_mul_of_nonneg_left hgx (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsum : Summable fun q : XiZeroCopy =>
      ∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun T => norm_nonneg _) hbound
      (hsumk.mul_right _)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ T : ℝ, (∑' q : XiZeroCopy, cx G T *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))) =
      cx G T * ((criticalAliasCoefficient R : ℂ) *
        (heatedBeyondWall ε R hF.1 (T + k) - ((heatedState ε F (T + k) : ℝ) : ℂ))) := by
    intro T
    rw [tsum_mul_left, (nullVector_hasSum_heated_zeroSeries hR hF hε (T + k)).tsum_eq]
  simp only [hterm, htsum] at h
  have e : (∫ T : ℝ, cx G T * ((criticalAliasCoefficient R : ℂ) *
        (heatedBeyondWall ε R hF.1 (T + k) - ((heatedState ε F (T + k) : ℝ) : ℂ)))) =
      ∫ T : ℝ, cx (fun x => G (x - k)) T * ((criticalAliasCoefficient R : ℂ) *
        (heatedBeyondWall ε R hF.1 T - ((heatedState ε F T : ℝ) : ℂ))) := by
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun T => ?_))
      (integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun T : ℝ => cx (fun x => G (x - k)) T * ((criticalAliasCoefficient R : ℂ) *
          (heatedBeyondWall ε R hF.1 T - ((heatedState ε F T : ℝ) : ℂ)))) k)
    show cx G T * _ = cx (fun x => G (x - k)) (T + k) * _
    rw [cx_comp_sub_add]
  rwa [e] at h

/-- **Weil's bare form at a translated confined null vector.** For any confined null vector `(R, F)`
(`R > 0`), `k ≥ 0`, and any `G` in the energy domain,
`W(τ_k F, G) = a(R) (∫_{x>0} F⁺(x) G(x − k) dx − ∫ e^{−8u} F(u) G(u − k) du)`. -/
theorem nullVector_bareMixedEnergy_translate {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {k : ℝ} (hk : 0 ≤ k) :
    ((bareMixedEnergy (fun u => F (u + k)) G : ℝ) : ℂ) =
      (criticalAliasCoefficient R : ℂ) *
        (beyondWallPairing R hF.1 (cx fun x => G (x - k)) -
          statePairing F (cx fun x => G (x - k))) := by
  have hd := hF.1
  have hc8 := measurable_confinedHalf_comp_sub hG k
  have hc2 := integrable_sq_confinedHalf_comp_sub hG k
  have hd8 := measurable_dampedProfile_comp_sub hG k
  have hd2 := integrable_sq_dampedProfile_comp_sub hG k
  have h1 := tendsto_integral_cx_mul_heatedState_of_sq hd hc8 hc2
  have h2 := tendsto_integral_cx_mul_heatedBeyondWall_of_sq R hd hd8 hd2
  have h3 := (h2.sub h1).const_mul (criticalAliasCoefficient R : ℂ)
  have h4 := tendsto_heatedZeroPairing (hd.causalTranslate hk) hG
  refine tendsto_nhds_unique h4 (h3.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hterm : ∀ q : XiZeroCopy,
      negativeHalfLineLaplace (cx fun u => F (u + k)) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) =
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          stateHeatSymbol ε k (centredZero q) := by
    intro q
    have hL : negativeHalfLineLaplace (cx fun u => F (u + k)) (centredZero q) =
        Complex.exp (-(centredZero q * (k : ℂ))) *
          negativeHalfLineLaplace (cx F) (centredZero q) :=
      laplace_shiftProfile F k (centredZero q)
    have hS : stateHeatSymbol ε k (centredZero q) =
        Complex.exp ((ε : ℂ) * centredZero q ^ 2) *
          Complex.exp (-(centredZero q * (k : ℂ))) := by
      unfold stateHeatSymbol; rw [sub_eq_add_neg, Complex.exp_add]
    rw [hL, hS]; ring
  rw [tsum_congr hterm,
    (nullVector_hasSum_zeroPairing_heated_translate hR hF hG hε k).tsum_eq,
    ← integral_sub (integrable_cx_mul_heatedBeyondWall_of_sq R hd hd8 hd2 hε)
      (integrable_cx_mul_heatedState_of_sq hd hc8 hc2 hε), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun T => ?_)
  show (criticalAliasCoefficient R : ℂ) *
      (cx (fun x => G (x - k)) T * heatedBeyondWall ε R hd T -
        cx (fun x => G (x - k)) T * ((heatedState ε F T : ℝ) : ℂ)) =
    cx (fun x => G (x - k)) T * ((criticalAliasCoefficient R : ℂ) *
      (heatedBeyondWall ε R hd T - ((heatedState ε F T : ℝ) : ℂ)))
  ring

/-- **Cross-rung wall law between any two confined null vectors.** For confined null vectors
`(R₁, F₁)` and `(R₂, F₂)` (`R₁, R₂ > 0`) and `k ≥ 0`,
`a(R₁) ∫_0^k F₁⁺(x) F₂(x − k) dx = (a(R₁) e^{−8k} − a(R₂)) ∫ F₁(u + k) F₂(u) e^{−8u} du`. -/
theorem nullVector_crossWallLaw {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : IsConfinedNullVector R₁ F₁) (hF₂ : IsConfinedNullVector R₂ F₂)
    {k : ℝ} (hk : 0 ≤ k) :
    (criticalAliasCoefficient R₁ : ℂ) * beyondWallPairing R₁ hF₁.1 (cx fun x => F₂ (x - k)) =
      ((criticalAliasCoefficient R₁ * Real.exp (-(8 * k)) - criticalAliasCoefficient R₂ : ℝ) : ℂ) *
        ((∫ u : ℝ, F₁ (u + k) * F₂ u * Real.exp (-(8 * u)) : ℝ) : ℂ) := by
  have htr : CriticalHalfLineEnergyDomain (fun u => F₁ (u + k)) := hF₁.1.causalTranslate hk
  have hnull₂ := hF₂.2.2 (fun u => F₁ (u + k)) htr
  rw [criticalHalfLineMixedEnergy_eq_bare_add, bareMixedEnergy_comm] at hnull₂
  have hc_int : (∫ u in Iio (0 : ℝ), F₂ u * F₁ (u + k) * Real.exp (-(8 * u))) =
      ∫ u : ℝ, F₁ (u + k) * F₂ u * Real.exp (-(8 * u)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [hF₂.1.support u (not_lt.mp hu), zero_mul, zero_mul]]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  rw [hc_int] at hnull₂
  have hbare : ((bareMixedEnergy (fun u => F₁ (u + k)) F₂ : ℝ) : ℂ) =
      -((criticalAliasCoefficient R₂ : ℝ) : ℂ) *
        ((∫ u : ℝ, F₁ (u + k) * F₂ u * Real.exp (-(8 * u)) : ℝ) : ℂ) := by
    have h0 : bareMixedEnergy (fun u => F₁ (u + k)) F₂ =
        -(criticalAliasCoefficient R₂ * ∫ u : ℝ, F₁ (u + k) * F₂ u * Real.exp (-(8 * u))) := by
      linarith
    rw [h0]; push_cast; ring
  have hdef := nullVector_bareMixedEnergy_translate hR₁ hF₁ hF₂.1 hk
  have hsh := integral_translate_mul_exp_eq (F := F₁) (G := F₂) hF₂.1.support k
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
    rw [hF₂.1.support u (not_lt.mp hu), mul_zero, zero_mul]] at hsh
  have hexp_inv : ((Real.exp (8 * k) : ℝ) : ℂ) * ((Real.exp (-(8 * k)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have : 8 * k + -(8 * k) = 0 := by ring
    rw [this, Real.exp_zero, Complex.ofReal_one]
  have hsp : statePairing F₁ (cx fun x => F₂ (x - k)) =
      ((Real.exp (-(8 * k)) : ℝ) : ℂ) *
        ((∫ u : ℝ, F₁ (u + k) * F₂ u * Real.exp (-(8 * u)) : ℝ) : ℂ) := by
    calc statePairing F₁ (cx fun x => F₂ (x - k))
        = (((Real.exp (8 * k) : ℝ) : ℂ) * ((Real.exp (-(8 * k)) : ℝ) : ℂ)) *
            statePairing F₁ (cx fun x => F₂ (x - k)) := by rw [hexp_inv, one_mul]
      _ = ((Real.exp (-(8 * k)) : ℝ) : ℂ) *
            (((Real.exp (8 * k) : ℝ) : ℂ) * statePairing F₁ (cx fun x => F₂ (x - k))) := by ring
      _ = ((Real.exp (-(8 * k)) : ℝ) : ℂ) *
            ((∫ u : ℝ, F₁ (u + k) * F₂ u * Real.exp (-(8 * u)) : ℝ) : ℂ) := by rw [← hsh]
  rw [hbare, hsp] at hdef
  push_cast
  linear_combination -hdef

/-- **Diagonal wall law for any confined null vector `(R, F)` (`R > 0`).** -/
theorem nullVector_diagonalWallLaw {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {k : ℝ} (hk : 0 ≤ k) :
    beyondWallPairing R hF.1 (cx fun x => F (x - k)) =
      -((1 - Real.exp (-(8 * k)) : ℝ) : ℂ) *
        ((∫ u : ℝ, F (u + k) * F u * Real.exp (-(8 * u)) : ℝ) : ℂ) := by
  have hc := nullVector_crossWallLaw hR hF hF hk
  have ha : (criticalAliasCoefficient R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hR).ne'
  apply mul_left_cancel₀ ha
  rw [hc]
  push_cast
  ring

#print axioms hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros
#print axioms bareMixedEnergy_eq_onLine_add_offLine_of_finiteOffLine
#print axioms exists_zetaOnLineResolvent
#print axioms nullVector_ae_eq_offLineResolvent_of_finiteOffLine
#print axioms nullVector_crossWallLaw

end GaloisForLFunctions.ExclusionOfTheCriticalState

