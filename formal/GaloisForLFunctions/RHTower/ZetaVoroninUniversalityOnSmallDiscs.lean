import GaloisForLFunctions.RHTower.ZetaDiscRecurrenceOnZeroFreeDiscs
import GaloisForLFunctions.RHTower.ZetaTypicalHeightApproximationExcludesZeroTargets

/-!
# Voronin universality of `ζ` on small discs of the strip

Let `z₀` and `ρ` satisfy `1/2 ≤ Re z₀`, `2ρ − 2Re z₀ < −1`, `ρ < 1 − Re z₀`, and let
`K = {|z − z₀| ≤ ρ r₁}`, `r₁ < 1`, with `1/2 < Re z₀ − 2ρr₁` and `Re z₀ + 2ρr₁ < 1`.  For every
function `g` analytic and nonvanishing on the larger disc `|z − z₀| < ρ R₂`, `R₂ > 1`, and every
`ε > 0`, the heights `τ` at which `ζ(· + iτ)` is within `ε` of `g` on `K` have positive lower
density (`exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd`).  Every point of the strip
carries such a disc (`exists_radius_zeta_universal`); in particular `ζ` comes uniformly close to
every nonzero constant on a small disc about every point of the strip
(`exists_pos_density_zetaTargetReturnSet_const`).

The proof composes three laws of the self-return lane, none of which uses a zero-free hypothesis
on `ζ`:

* universality of the finite Euler products `E_y` for the exponential targets
  `exp(L((· − z₀)/ρ))`, `L` in the Hardy space (`exists_pos_density_eulerTargetReturnSet_exp`);
* the cutoff-uniform density mechanism of the prime torus: base phases of the primes `≤ y₁` at
  which `E_{y₁}` is within `ε/2` of the target form an open set `A`, the random linear sum of the
  primes in `(y₁, y]` is small on a block event of Haar measure `≥ 1/2` independent of `A`, so the
  target phases at every stage `y ≥ y₁` have Haar measure `≥ Haar(A)/2`
  (`exists_uniform_pos_density_eulerTargetReturnSet_exp`);
* the Euler tail law: heights at which `|ζ − E_y| ≥ ε/2` somewhere on `K` have upper density at
  most `c/2` for `y` large (`eventually_eventually_volume_eulerDiscTailBadSet_le`).

The nonvanishing target has an analytic logarithm on the larger disc, which lies in the Hardy
space of the disc coordinate; the exponential target then agrees with `g` on `K`.

**The orbit-closure dichotomy** (`zeta_orbit_closure_dichotomy`).  On the universal disc about any
point of the strip, every target analytic and nonvanishing on the fourfold disc is approached by
`ζ(· + iτ)` with positive lower density of heights, and every target with a zero in the open disc
and a positive floor on its circle is approached only on a density-zero set of heights.  The
self-target `ζ|_K` is of the first kind exactly when `ζ` has no zero on the fourfold disc, which is
the local form of Bagchi's criterion: universality holds at every point of the strip, and the only
thing that can fail at a point is the admissibility of `ζ` itself as a target.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-! ## The exponential target is continuous on the disc -/

/-- The exponential target `exp(L((· − z₀)/ρ))` is continuous on the closed disc `|z − z₀| ≤ ρ r₁`. -/
theorem continuousOn_expHardyTarget (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (L : HardyDisk) {r₁ : ℝ}
    (hr₁ : r₁ < 1) :
    ContinuousOn (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ))) (closedBall z₀ (ρ * r₁)) := by
  have hmaps : MapsTo (fun z : ℂ => (z - z₀) / ρ) (closedBall z₀ (ρ * r₁)) (ball 0 1) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le,
      div_lt_one hρ]
    nlinarith
  have hinner : ContinuousOn (fun z : ℂ => hardyFun L ((z - z₀) / ρ)) (closedBall z₀ (ρ * r₁)) :=
    (differentiableOn_hardyFun L).continuousOn.comp
      ((continuousOn_id.sub continuousOn_const).div_const _) hmaps
  exact Complex.continuous_exp.comp_continuousOn hinner

/-! ## Cutoff-uniform density of the Euler-target heights for exponential targets -/

/-- **Positive lower density of the Euler-target heights, uniformly in the cutoff.**  For `L` in
the Hardy space and the target `g = exp(L((· − z₀)/ρ))` on the disc `|z − z₀| ≤ ρ r₁`, there are
`c > 0` and `y₁` such that for every `y ≥ y₁` the heights at which `E_y(· + iτ)` is within `ε` of
`g` on the disc have lower density at least `c`.  Mechanism: base phases at stage `y₁` form an open
set `A` of positive Haar measure; the primes in `(y₁, y]` contribute a random Hardy-space sum,
small on a block event of Haar measure `≥ 1/2` independent of `A`. -/
theorem exists_uniform_pos_density_eulerTargetReturnSet_exp (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : ρ < 1 - z₀.re)
    (L : HardyDisk) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (eulerTargetReturnSet y (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ)))
        (closedBall z₀ (ρ * r₁)) ε ∩ Icc 0 T) := by
  set g : ℂ → ℂ := fun z => Complex.exp (hardyFun L ((z - z₀) / ρ)) with hg
  have hK : IsCompact (closedBall z₀ (ρ * r₁)) := isCompact_closedBall _ _
  have hσ₁ : 1 / 2 < z₀.re - ρ := by linarith
  have hre : ∀ z ∈ closedBall z₀ (ρ * r₁), 0 < z.re := fun z hz => by
    have h1 := re_ge_of_mem_closedBall_center hz
    have h2 : ρ * r₁ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hr₁.le hρ.le
    linarith
  have hgc : ContinuousOn g (closedBall z₀ (ρ * r₁)) := continuousOn_expHardyTarget z₀ hρ L hr₁
  -- a bound for the target on the disc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hgc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (mem_closedBall_self (by positivity)))
  -- the constants
  set K₁ : ℝ := Real.sqrt ((1 - r₁ ^ 2)⁻¹) with hK₁
  have hK₁0 : 0 ≤ K₁ := Real.sqrt_nonneg _
  have hK₁1 : 0 < K₁ + 1 := by linarith
  set A₀ : ℝ := M + ε / 2 + 1 with hA₀
  have hA₀pos : 0 < A₀ := by rw [hA₀]; linarith
  have hA₀ne : A₀ ≠ 0 := hA₀pos.ne'
  set δ : ℝ := min ((K₁ + 1)⁻¹) (ε / (8 * A₀ * (K₁ + 1))) with hδ
  have hδpos : 0 < δ := lt_min (inv_pos.mpr hK₁1) (div_pos hε (by positivity))
  have hδ1 : (K₁ + 1) * δ ≤ 1 := by
    calc (K₁ + 1) * δ ≤ (K₁ + 1) * (K₁ + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (by rw [hδ]; exact min_le_left _ _) hK₁1.le
      _ = 1 := mul_inv_cancel₀ hK₁1.ne'
  have hδ2 : 2 * (M + ε / 2) * ((K₁ + 1) * δ) ≤ ε / 4 := by
    have h1 : (K₁ + 1) * δ ≤ ε / (8 * A₀) := by
      calc (K₁ + 1) * δ ≤ (K₁ + 1) * (ε / (8 * A₀ * (K₁ + 1))) :=
            mul_le_mul_of_nonneg_left (by rw [hδ]; exact min_le_right _ _) hK₁1.le
        _ = ε / (8 * A₀) := by field_simp
    have h2 : M + ε / 2 ≤ A₀ := by rw [hA₀]; linarith
    calc 2 * (M + ε / 2) * ((K₁ + 1) * δ) ≤ 2 * A₀ * (ε / (8 * A₀)) :=
          mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = ε / 4 := by field_simp; ring
  -- the tails
  set C : ℝ := max ((1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2) 1 with hC
  have hC0 : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCrem : (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 ≤ C := le_max_left _ _
  set δ' : ℝ := min δ (δ ^ 2 / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'le2 : δ' ≤ δ ^ 2 / 2 := min_le_right _ _
  obtain ⟨y₀, -, hy₀⟩ := exists_remainder_tail_le hσ₁ hC0 hδ'pos 0
  -- the base phases, at a stage `y₁ ≥ y₀`
  obtain ⟨y₁, hy₁, c₁, hc₁, hev₁⟩ := exists_pos_density_eulerTargetReturnSet_exp z₀ hρ hσ hρσ₁
    hρσ₂ L hr₁0 hr₁ (half_pos hε) y₀
  have hne : (eulerTargetReturnSet y₁ g (closedBall z₀ (ρ * r₁)) (ε / 2)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    obtain ⟨T, hT, hTpos⟩ := (hev₁.and (eventually_gt_atTop (0 : ℝ))).exists
    rw [hemp, Set.empty_inter, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hT
    exact absurd hT (not_le.mpr (mul_pos hc₁ hTpos))
  obtain ⟨τ₀, hτ₀⟩ := hne
  -- the base event `A`: phases of the primes `≤ y₁` approximating the target within `ε/2`
  set A : Set (UnitAddTorus Nat.Primes) := unitTorusHomeomorphCircles Nat.Primes ⁻¹'
    eulerPhaseTargetSet y₁ g (closedBall z₀ (ρ * r₁)) (ε / 2) with hA
  have hAopen : IsOpen A :=
    (Homeomorph.isOpen_preimage _).mpr (isOpen_eulerPhaseTargetSet y₁ hK hre hgc _)
  have hAne : A.Nonempty := by
    refine ⟨(unitTorusHomeomorphCircles Nat.Primes).symm (circlePhaseFlow primeFrequency τ₀), ?_⟩
    rw [hA, Set.mem_preimage, Homeomorph.apply_symm_apply]
    simp only [eulerPhaseTargetSet, Set.mem_setOf_eq]
    intro z hz
    rw [eulerPhaseProduct_circlePhaseFlow]
    exact hτ₀ z hz
  have hApos : 0 < (torusHaar Nat.Primes A).toReal :=
    ENNReal.toReal_pos (hAopen.measure_pos _ hAne).ne' (measure_ne_top _ _)
  refine ⟨(torusHaar Nat.Primes A).toReal / 4, by positivity, y₁, fun y hy => ?_⟩
  -- the block event `B_y`: the random linear sum of the primes in `(y₁, y]` is small
  set Bl : Finset Nat.Primes := primesLE y \ primesLE y₁ with hBl
  set u : Nat.Primes → HardyDisk := primeVectorOf z₀ hρ.le with hu
  set By : Set (UnitAddTorus Nat.Primes) := {x | ‖torusPrimePhaseSum Bl u x‖ < δ} with hBy
  have hByopen : IsOpen By := isOpen_lt (continuous_torusPrimePhaseSum Bl u).norm continuous_const
  have htail : ∀ N, ∑ n ∈ Finset.Ico (y₁ + 1) N, C * (n : ℝ) ^ (-(2 * (z₀.re - ρ))) ≤ δ' := by
    intro N
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_left (by omega)) fun n _ _ => by positivity) (hy₀ N)
  -- Chebyshev: `Haar(B_y) ≥ 1/2`
  have hsumsq : ∑ p ∈ Bl, ‖u p‖ ^ 2 ≤ δ ^ 2 / 2 := by
    calc ∑ p ∈ Bl, ‖u p‖ ^ 2 ≤ ∑ p ∈ Bl, C * ((p : ℕ) : ℝ) ^ (-(2 * (z₀.re - ρ))) :=
          sum_le_sum fun p _ => (norm_primeVectorOf_sq_le z₀ hρ.le p).trans
            (le_mul_of_one_le_left (by positivity) hC1)
      _ ≤ ∑ n ∈ Finset.Ico (y₁ + 1) (y + 1), C * (n : ℝ) ^ (-(2 * (z₀.re - ρ))) :=
          sum_primesLE_sdiff_le_sum_Ico
            (F := fun n : ℕ => C * (n : ℝ) ^ (-(2 * (z₀.re - ρ)))) (fun n => by positivity) y₁ y
      _ ≤ δ' := htail _
      _ ≤ δ ^ 2 / 2 := hδ'le2
  have hBy_half : ENNReal.ofReal (1 / 2) ≤ torusHaar Nat.Primes By := by
    have hcompl : torusHaar Nat.Primes Byᶜ ≤ ENNReal.ofReal (1 / 2) := by
      have hc : Byᶜ = {x | δ ≤ ‖torusPrimePhaseSum Bl u x‖} := by
        ext x
        simp [hBy, not_lt]
      rw [hc]
      refine (measure_torusPrimePhaseSum_ge_le Bl u hδpos).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h1 : torusHaar Nat.Primes By = 1 - torusHaar Nat.Primes Byᶜ := by
      rw [← prob_compl_eq_one_sub hByopen.measurableSet.compl, compl_compl]
    rw [h1]
    calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
          rw [ENNReal.ofReal_div_of_pos (two_pos : (0 : ℝ) < 2), ENNReal.ofReal_one,
            ENNReal.ofReal_ofNat, one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - torusHaar Nat.Primes Byᶜ := tsub_le_tsub_left hcompl 1
  -- `A` and `B_y` are cylinders over disjoint blocks of primes, hence independent
  have hAdet : ∀ x, blockExtendTorus (primesLE y₁) (torusBlockRestrict (primesLE y₁) x) ∈ A
      ↔ x ∈ A := by
    intro x
    have hprod : ∀ z, eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes
        (blockExtendTorus (primesLE y₁) (torusBlockRestrict (primesLE y₁) x))) z
        = eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z := by
      intro z
      unfold eulerPhaseProduct
      refine prod_congr rfl fun p hp => ?_
      rw [unitTorusHomeomorphCircles_apply_congr (blockExtendTorus_torusBlockRestrict_apply _ x hp)]
    simp only [hA, Set.mem_preimage, eulerPhaseTargetSet, Set.mem_setOf_eq, hprod]
  have hBdet : ∀ x, blockExtendTorus Bl (torusBlockRestrict Bl x) ∈ By ↔ x ∈ By := by
    intro x
    simp only [hBy, Set.mem_setOf_eq]
    rw [torusPrimePhaseSum_congr u fun p hp => blockExtendTorus_torusBlockRestrict_apply Bl x hp]
  have hAB : torusHaar Nat.Primes (A ∩ By) = torusHaar Nat.Primes A * torusHaar Nat.Primes By := by
    rw [eq_setOf_torusBlockRestrict_mem_of_determined hAdet,
      eq_setOf_torusBlockRestrict_mem_of_determined hBdet]
    exact torusHaar_inter_eq_mul_of_disjoint_blocks Finset.disjoint_sdiff
      (isOpen_blockExtendTorus_preimage _ hAopen).measurableSet
      (isOpen_blockExtendTorus_preimage _ hByopen).measurableSet
  -- `A ∩ B_y` lies in the target phases at stage `y`
  have hsub : A ∩ By ⊆ unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      eulerPhaseTargetSet y g (closedBall z₀ (ρ * r₁)) ε := by
    rintro x ⟨hxA, hxB⟩
    rw [Set.mem_preimage]
    show ∀ z ∈ closedBall z₀ (ρ * r₁),
      ‖eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) z - g z‖ < ε
    refine norm_eulerPhaseProduct_sub_lt_of_block z₀ hρ (by linarith) hr₁0 hr₁ hy x hM hxA hxB
      ?_ hδ1 hδ2 hε
    refine le_trans ?_ ((htail (y + 1)).trans hδ'le)
    refine sum_le_sum fun n _ => ?_
    exact mul_le_mul_of_nonneg_right hCrem (by positivity)
  -- the target phases at stage `y` have Haar measure at least `Haar(A)/2`
  have hUy : (torusHaar Nat.Primes A).toReal / 4
      < (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          eulerPhaseTargetSet y g (closedBall z₀ (ρ * r₁)) ε)).toReal := by
    have h1 : torusHaar Nat.Primes A * ENNReal.ofReal (1 / 2)
        ≤ torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          eulerPhaseTargetSet y g (closedBall z₀ (ρ * r₁)) ε) := by
      calc torusHaar Nat.Primes A * ENNReal.ofReal (1 / 2)
          ≤ torusHaar Nat.Primes A * torusHaar Nat.Primes By := by gcongr
        _ = torusHaar Nat.Primes (A ∩ By) := hAB.symm
        _ ≤ _ := measure_mono hsub
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h2
    linarith
  rw [eulerTargetReturnSet_eq_preimage]
  exact eventually_ofReal_mul_le_volume_preimage_primeFlow
    (isOpen_eulerPhaseTargetSet y hK hre hgc ε) hUy

/-! ## Euler-target heights that are tail-good are target heights of `ζ` -/

/-- At a tail-good height, `ζ(· + iτ) − g = (ζ − E_y)(· + iτ) + (E_y(· + iτ) − g)` is small. -/
theorem eulerTargetReturnSet_diff_eulerDiscTailBadSet_subset_zetaTargetReturnSet (y : ℕ)
    (g : ℂ → ℂ) (c : ℂ) (r ε ε' : ℝ) :
    eulerTargetReturnSet y g (closedBall c r) ε \ eulerDiscTailBadSet y c r ε' ⊆
      zetaTargetReturnSet g (closedBall c r) (ε' + ε) := by
  rintro τ ⟨htarget, hgood⟩ z hz
  have htail : ‖eulerTailFun y (z + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood ⟨z, hz, not_lt.mp hcon⟩
  have hh := htarget z hz
  have hid : riemannZeta (z + τ * I) - g z =
      eulerTailFun y (z + τ * I) + (eulerPhaseProduct y 1 (z + τ * I) - g z) := by
    unfold eulerTailFun
    ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt (add_lt_add htail hh)

/-! ## Universality of `ζ` -/

/-- **Universality of `ζ` for exponential targets.**  With the disc margins
`1/2 < Re z₀ − 2ρr₁` and `Re z₀ + 2ρr₁ < 1`, the heights at which `ζ(· + iτ)` is within `ε` of
`exp(L((· − z₀)/ρ))` on `|z − z₀| ≤ ρ r₁` have positive lower density: cutoff-uniform
Euler-target density minus the Euler tail bad set. -/
theorem exists_pos_density_zetaTargetReturnSet_exp (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : ρ < 1 - z₀.re)
    (L : HardyDisk) {r₁ : ℝ} (hr₁0 : 0 < r₁) (hr₁ : r₁ < 1)
    (h0 : 1 / 2 < z₀.re - 2 * (ρ * r₁)) (h1 : z₀.re + 2 * (ρ * r₁) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ)))
        (closedBall z₀ (ρ * r₁)) ε ∩ Icc 0 T) := by
  obtain ⟨c, hc, y₁, hy₁⟩ := exists_uniform_pos_density_eulerTargetReturnSet_exp z₀ hρ hσ hρσ₁
    hρσ₂ L hr₁0.le hr₁ (half_pos hε)
  have hbad := eventually_eventually_volume_eulerDiscTailBadSet_le (by positivity : 0 < ρ * r₁)
    h0 h1 (half_pos hε) (half_pos hc)
  obtain ⟨y, hy, hyb⟩ := ((eventually_ge_atTop y₁).and hbad).exists
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [hy₁ y hy, hyb, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := eulerTargetReturnSet_diff_eulerDiscTailBadSet_subset_zetaTargetReturnSet y
    (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ))) z₀ (ρ * r₁) (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hc hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-- **Voronin universality of `ζ` on a small disc.**  Let `g` be analytic and nonvanishing on the
disc `|z − z₀| < ρ R₂`, `R₂ > 1`.  Then for every `ε > 0` the heights at which `ζ(· + iτ)` is
within `ε` of `g` on the closed disc `|z − z₀| ≤ ρ r₁` have positive lower density.  The analytic
logarithm of `g` on the larger disc lies in the Hardy space of the disc coordinate, so `g` is an
exponential target on the smaller disc. -/
theorem exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : ρ < 1 - z₀.re)
    {R₂ : ℝ} (hR₂ : 1 < R₂) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball z₀ (ρ * R₂)))
    (hg0 : ∀ z ∈ ball z₀ (ρ * R₂), g z ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 < r₁) (hr₁ : r₁ < 1)
    (h0 : 1 / 2 < z₀.re - 2 * (ρ * r₁)) (h1 : z₀.re + 2 * (ρ * r₁) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet g (closedBall z₀ (ρ * r₁)) ε ∩ Icc 0 T) := by
  -- the analytic logarithm of `g` on the larger disc
  have hρR₂ : 0 < ρ * R₂ := by positivity
  obtain ⟨f, hf, hexpf⟩ := exists_analyticOnNhd_exp_eq_ball hρR₂ hg hg0
  -- the logarithm in the disc coordinate, on a closed disc of radius `R > 1`
  set R : ℝ := (1 + R₂) / 2 with hR
  have hR1 : 1 < R := by rw [hR]; linarith
  have hRR₂ : R < R₂ := by rw [hR]; linarith
  set F : ℂ → ℂ := fun q => f (z₀ + ρ * q) with hF
  have hmaps : MapsTo (fun q : ℂ => z₀ + ρ * q) (closedBall 0 R) (ball z₀ (ρ * R₂)) := by
    intro q hq
    rw [mem_closedBall, dist_zero_right] at hq
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
    nlinarith
  have hFdiff : DifferentiableOn ℂ F (closedBall 0 R) :=
    hf.differentiableOn.comp
      ((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)) hmaps
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hFdiff.continuousOn.mono sphere_subset_closedBall)
  have hBcirc : ∀ θ : ℝ, ‖F (circleMap 0 R θ)‖ ≤ B := fun θ =>
    hB _ (circleMap_mem_sphere _ (by linarith) θ)
  set L : HardyDisk := hardyDiskOfAnalytic F hR1 hBcirc with hL
  have hLfun : ∀ q : ℂ, ‖q‖ < 1 → hardyFun L q = F q := fun q hq =>
    hardyFun_hardyDiskOfAnalytic hR1 hFdiff hBcirc hq
  -- on the closed disc `|z − z₀| ≤ ρ r₁` the exponential target is `g`
  have htarget : ∀ z ∈ closedBall z₀ (ρ * r₁),
      Complex.exp (hardyFun L ((z - z₀) / ρ)) = g z := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hq : ‖(z - z₀) / ρ‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_lt_one hρ]
      nlinarith
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    have hz' : z₀ + ρ * ((z - z₀) / ρ) = z := by
      rw [mul_div_cancel₀ _ hρ']
      ring
    have hzball : z ∈ ball z₀ (ρ * R₂) := by
      rw [mem_ball, dist_eq_norm]
      nlinarith
    rw [hLfun _ hq, hF]
    simp only
    rw [hz']
    exact hexpf z hzball
  -- universality for the exponential target, transported to `g`
  obtain ⟨c, hc, hev⟩ :=
    exists_pos_density_zetaTargetReturnSet_exp z₀ hρ hσ hρσ₁ hρσ₂ L hr₁0 hr₁ h0 h1 hε
  refine ⟨c, hc, ?_⟩
  have hset : zetaTargetReturnSet (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ)))
      (closedBall z₀ (ρ * r₁)) ε = zetaTargetReturnSet g (closedBall z₀ (ρ * r₁)) ε := by
    ext τ
    simp only [zetaTargetReturnSet, mem_setOf_eq]
    constructor
    · intro h z hz
      rw [← htarget z hz]
      exact h z hz
    · intro h z hz
      rw [htarget z hz]
      exact h z hz
  rw [← hset]
  exact hev

/-! ## Every point of the strip carries a universal disc -/

/-- **A universal disc about every point of the strip.**  For `1/2 < Re z₀ < 1` there is `r > 0`
with `1/2 < Re z₀ − 4r` and `Re z₀ + 4r < 1` such that every `g` analytic and nonvanishing on
`|z − z₀| < 4r` is approached by `ζ(· + iτ)` on `|z − z₀| ≤ r`, within any `ε > 0`, on a set of
heights of positive lower density.  The radius is `r = ρ/2` with
`ρ = min((Re z₀ − 1/2)/3, (1 − Re z₀)/3)`, `r₁ = 1/2`, `R₂ = 2`. -/
theorem exists_radius_zeta_universal {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r > 0, 1 / 2 < z₀.re - 4 * r ∧ z₀.re + 4 * r < 1 ∧
      ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball z₀ (4 * r)) → (∀ z ∈ ball z₀ (4 * r), g z ≠ 0) →
        ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (c * T) ≤ volume (zetaTargetReturnSet g (closedBall z₀ r) ε ∩ Icc 0 T) := by
  set ρ : ℝ := min ((z₀.re - 1 / 2) / 3) ((1 - z₀.re) / 3) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ1 : ρ ≤ (z₀.re - 1 / 2) / 3 := min_le_left _ _
  have hρ2 : ρ ≤ (1 - z₀.re) / 3 := min_le_right _ _
  refine ⟨ρ * (1 / 2), by positivity, by linarith, by linarith, fun g hg hg0 ε hε => ?_⟩
  have h4 : 4 * (ρ * (1 / 2)) = ρ * 2 := by ring
  rw [h4] at hg hg0
  exact exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd z₀ hρ h1.le (by linarith)
    (by linarith) (R₂ := 2) (by norm_num) hg hg0 (by norm_num) (by norm_num)
    (by linarith) (by linarith) hε

/-- **`ζ` comes uniformly close to every nonzero constant** on a small disc about every point of
the strip, on a set of heights of positive lower density. -/
theorem exists_pos_density_zetaTargetReturnSet_const {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) {w : ℂ} (hw : w ≠ 0) :
    ∃ r > 0, ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (c * T) ≤
        volume (zetaTargetReturnSet (fun _ => w) (closedBall z₀ r) ε ∩ Icc 0 T) := by
  obtain ⟨r, hr, -, -, huniv⟩ := exists_radius_zeta_universal h1 h2
  exact ⟨r, hr, huniv _ analyticOnNhd_const fun _ _ => hw⟩

/-! ## The orbit-closure dichotomy -/

/-- **Orbit-closure dichotomy on the universal disc.**  About every point `z₀` of the strip there
is `r > 0` such that on `K = {|z − z₀| ≤ r}`: every target analytic and nonvanishing on
`|z − z₀| < 4r` is approached by `ζ(· + iτ)` with positive lower density of heights, and every
target with a zero in the open disc `|z − z₀| < r` and floor `m` on its circle is approached within
`ε ≤ m/2` only on a density-zero set of heights.  The self-target `ζ|_K` is of the first kind iff
`ζ` has no zero on `|z − z₀| < 4r` (the local Bagchi criterion). -/
theorem zeta_orbit_closure_dichotomy {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r > 0,
      (∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball z₀ (4 * r)) → (∀ z ∈ ball z₀ (4 * r), g z ≠ 0) →
        ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (c * T) ≤
            volume (zetaTargetReturnSet g (closedBall z₀ r) ε ∩ Icc 0 T)) ∧
      (∀ g : ℂ → ℂ, (∃ w ∈ ball z₀ r, g w = 0) → ∀ m ε : ℝ, (∀ z ∈ sphere z₀ r, m ≤ ‖g z‖) →
        ε ≤ m / 2 → ∀ κ > 0, ∀ᶠ T : ℝ in atTop,
          volume (zetaTargetReturnSet g (closedBall z₀ r) ε ∩ Icc 0 T) ≤
            ENNReal.ofReal (κ * T)) := by
  obtain ⟨r, hr, hr0, hr1, huniv⟩ := exists_radius_zeta_universal h1 h2
  refine ⟨r, hr, huniv, fun g hw m ε hm hε κ hκ => ?_⟩
  exact eventually_volume_zetaTargetReturnSet_le hr (by linarith) (by linarith) hw hm hε hκ

end RHTower
