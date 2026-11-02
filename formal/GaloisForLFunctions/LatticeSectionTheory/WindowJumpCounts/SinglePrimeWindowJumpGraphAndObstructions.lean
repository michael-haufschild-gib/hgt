import GaloisForLFunctions.LatticeSectionTheory.ThePrimitiveH1OfPrimeFreeCyclesIsAJumpCount
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.MeanZeroProfileVariationInequalityPastPrimeTwo
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurLendingOddWindowThreeHundredSixtyTwoThousandths
import GaloisForLFunctions.RHTower.CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality

/-!
# Single-prime window jump counts through `log 3`, `T₂`-graph decompositions, and first-prime obstructions

On a real test `f` supported in `[−a, a]` with `2a ≤ log 3`, all prime powers `n ≥ 3` satisfy
`2a ≤ log 3 ≤ log n`, so the support intersection of `f` and `f(· + log n)` is contained in `{−a}`
and `autocorr f (log n) = 0`. Only the archimedean Lévy jumps, the first prime jump `n = 2` (`T₂`,
shift `log 2`, weight `log 2 / √2`), and the pole plane survive.

* **Closed prime-free window (`2a ≤ log 2`)**: `weilPair_eq_jumpCount_add_poleSquares_of_le_log_two`
  extends the prime-free jump-count identity to the closed endpoint `2a = log 2` and resolves the
  pole cross term into `2 evenPoleMoment(f)² − 2 oddPoleMoment(f)²`.
* **Single-prime window (`2a ≤ log 3`)**: `weilPair_eq_jumpCount_add_primeTwoGraph_of_le_log_three`
  expresses `W(f, f)` through the archimedean Lévy jump count `jumpCount f`, the `T₂`-graph jump
  count `primeTwoGraphJump f = ∫ (f(u) − f(u + log 2))² du` (and in gauge coordinates `f = M g`,
  the interior strip jump `primeTwoGaugeStripJump M g`), diagonal mass, and the signed pole squares.
  Along any two-hop path `x ↔ x' ↔ y`, `path_routing_jump_identity` decomposes the weighted sum of
  squared increments into the harmonic-conductance chord jump plus one manifest square.
* **Unconditional window coercivity for `weilPair` and `primitiveH1`**:
  - all parities on `[−3/10, 3/10]` (`weilPair_ge_of_le_threeTenths`, `primitiveH1_ge_of_le_threeTenths`);
  - odd tests past `log 2` on `[−181/500, 181/500]` (`weilPair_ge_of_odd_le_oneHundredEightyOneFiveHundredths`);
  - smooth `cosh`-orthogonal (`evenPoleMoment f = 0`) tests across the entire prime-free window and
    past `p = 2` up to `2a ≤ log 2 + 1/50` (`weilPair_ge_of_evenPoleMoment_zero_past_primeTwo`).
* **Full polarized CHMD radical of individual `Θ`-translates**:
  `fullSourcePair_thetaTranslate_eq_zero` proves that every individual shift `CHMDThetaTranslate.lift b hb`
  (`|b| < ½ log 2`) annihilates the entire `SourceGraph` space under the pole-completed pairing.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts

open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.CHMDPolar Zeta23

/-! ### 1. Endpoint autocorrelation vanishing and closed prime-free / single-prime cutoffs -/

/-- The autocorrelation of a test supported in `[−a, a]` vanishes for every shift `x ≥ 2a`,
including at the boundary `x = 2a` where the overlap reduces to `{−a}`. -/
theorem autocorr_eq_zero_of_two_mul_le {f : ℝ → ℝ} {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a)
    {x : ℝ} (hx : 2 * a ≤ x) : autocorr f x = 0 := by
  unfold autocorr
  have hsingleton : ({-a} : Set ℝ) =ᵐ[volume] (∅ : Set ℝ) := by
    rw [ae_eq_empty]
    exact Real.volume_singleton
  refine integral_eq_zero_of_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := -a))] with u hu
  have hne : u ≠ -a := fun h => hu (mem_singleton_iff.mpr h)
  by_cases hfu : f u = 0
  · simp [hfu]
  · have hu_mem := hs (subset_tsupport f hfu)
    have hlt : -a < u := lt_of_le_of_ne hu_mem.1 hne.symm
    have hfux : f (u + x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h => ?_
      have hux_mem := hs h
      linarith [hux_mem.2]
    simp [hfux]

/-- The `T₂`-graph jump count `∫ (f(u) − f(u + log 2))² du` of a real test. -/
def primeTwoGraphJump (f : ℝ → ℝ) : ℝ :=
  ∫ u, (f u - f (u + Real.log 2)) ^ 2

theorem primeTwoGraphJump_nonneg (f : ℝ → ℝ) : 0 ≤ primeTwoGraphJump f :=
  integral_nonneg fun _ => sq_nonneg _

/-- Expansion of the `T₂`-graph jump count into `2 ‖f‖² − 2 autocorr f (log 2)`. -/
theorem primeTwoGraphJump_eq {f : ℝ → ℝ} (hf : f ∈ realTests) :
    primeTwoGraphJump f = 2 * (∫ u, f u ^ 2) - 2 * autocorr f (Real.log 2) := by
  have hcont : Continuous f := hf.1.continuous
  have hcomp : HasCompactSupport f := hf.2
  have i1 : Integrable (fun u => f u ^ 2) :=
    (hcont.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hcomp)
  have i2 : Integrable (fun u => f (u + Real.log 2) ^ 2) := i1.comp_add_right (Real.log 2)
  have i3 : Integrable (fun u => f u * f (u + Real.log 2)) :=
    (hcont.mul (hcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hcomp.mul_right
  unfold primeTwoGraphJump autocorr
  have hpt : (fun u => (f u - f (u + Real.log 2)) ^ 2) =
      fun u => (f u ^ 2 + f (u + Real.log 2) ^ 2) - 2 * (f u * f (u + Real.log 2)) :=
    funext fun u => by ring
  rw [hpt, integral_sub (i1.add i2) (i3.const_mul 2), integral_add i1 i2,
    integral_add_right_eq_self (fun u => f u ^ 2) (Real.log 2), integral_const_mul]
  ring

/-- The gauge-weighted `T₂`-graph jump `∫ M(u) M(u + log 2) (g(u) − g(u + log 2))² du`. -/
def primeTwoGaugeStripJump (M g : ℝ → ℝ) : ℝ :=
  ∫ u, M u * M (u + Real.log 2) * (g u - g (u + Real.log 2)) ^ 2

theorem primeTwoGaugeStripJump_nonneg {M : ℝ → ℝ} (hM : ∀ u, 0 ≤ M u) (g : ℝ → ℝ) :
    0 ≤ primeTwoGaugeStripJump M g :=
  integral_nonneg fun u => mul_nonneg (mul_nonneg (hM u) (hM (u + Real.log 2))) (sq_nonneg _)

/-- In gauge coordinates `f = M g`, `-2 autocorr (M g) (log 2)` splits into the nonnegative
`T₂`-graph jump `primeTwoGaugeStripJump M g` minus the strip potential mass. -/
theorem neg_two_mul_autocorr_gauge_eq {M g : ℝ → ℝ} (hM : Continuous M) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    -2 * autocorr (fun u => M u * g u) (Real.log 2) =
      primeTwoGaugeStripJump M g -
        ∫ u, M u * M (u + Real.log 2) * (g u ^ 2 + g (u + Real.log 2) ^ 2) := by
  have hfg : Continuous (fun u => M u * g u) := hM.mul hg
  have hfgc : HasCompactSupport (fun u => M u * g u) := hgc.mul_left
  have i_corr : Integrable (fun u => (M u * g u) * (M (u + Real.log 2) * g (u + Real.log 2))) :=
    (hfg.mul (hfg.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfgc.mul_right
  have i_jump : Integrable (fun u => M u * M (u + Real.log 2) * (g u - g (u + Real.log 2)) ^ 2) := by
    have hdiff_c : HasCompactSupport (fun u => g u - g (u + Real.log 2)) :=
      hgc.sub (hgc.comp_homeomorph (Homeomorph.addRight (Real.log 2)))
    refine ((hM.mul (hM.comp (continuous_id.add continuous_const))).mul
      ((hg.sub (hg.comp (continuous_id.add continuous_const))).pow 2)).integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_sq hdiff_c).mul_left
  have i_mass : Integrable (fun u => M u * M (u + Real.log 2) * (g u ^ 2 + g (u + Real.log 2) ^ 2)) := by
    have hsq_c : HasCompactSupport (fun u => g u ^ 2 + g (u + Real.log 2) ^ 2) :=
      (hasCompactSupport_sq hgc).add
        (hasCompactSupport_sq (hgc.comp_homeomorph (Homeomorph.addRight (Real.log 2))))
    exact ((hM.mul (hM.comp (continuous_id.add continuous_const))).mul
      ((hg.pow 2).add ((hg.comp (continuous_id.add continuous_const)).pow 2))).integrable_of_hasCompactSupport
      hsq_c.mul_left
  unfold primeTwoGaugeStripJump autocorr
  rw [← integral_sub i_jump i_mass, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

/-- Two-hop path-routing identity: routing a jump `g_x − g_y` through an intermediate vertex `g_{x'}`
(such as the `T₂` mirror `x' = log 2 − x`) yields the harmonic chord conductance plus one square. -/
theorem path_routing_jump_identity {c₁ c₂ : ℝ} (hc : c₁ + c₂ ≠ 0) (gx gx' gy : ℝ) :
    c₁ * (gx - gx') ^ 2 + c₂ * (gx' - gy) ^ 2 =
      (c₁ * c₂ / (c₁ + c₂)) * (gx - gy) ^ 2 +
        (1 / (c₁ + c₂)) * (c₁ * (gx - gx') - c₂ * (gx' - gy)) ^ 2 := by
  field_simp [hc]
  ring

/-! ### 2. Pole-square resolution and `{∞, 2}` window identities up to `log 2` and `log 3` -/

/-- For every `f ∈ realTests`, twice the truncated pole cross term at `supportScale` equals
`2 evenPoleMoment(f)² − 2 oddPoleMoment(f)²`. -/
theorem two_mul_poleCross_eq_poleSquares {f : ℝ → ℝ} (hf : f ∈ realTests) :
    2 * poleCross (toRealWeilTestFn hf).supportScale f =
      2 * evenPoleMoment f ^ 2 - 2 * oddPoleMoment f ^ 2 := by
  have hcont : Continuous f := hf.1.continuous
  have hcomp : HasCompactSupport f := hf.2
  obtain ⟨B, hFB⟩ : ∃ B : ℝ, ∀ x, f x ≠ 0 → |x| ≤ B := by
    obtain ⟨K, hK, hsub⟩ := exists_compact_iff_hasCompactSupport.mpr hcomp
    obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨B, fun x hx => ?_⟩
    have := hB (hsub (subset_tsupport f hx))
    simpa [Metric.mem_closedBall, Real.dist_eq] using this
  -- Relate `poleCross` at `supportScale` to the full half-line `polarDensity` integral.
  set N := (toRealWeilTestFn hf).supportScale
  have hc_auto : Continuous (autocorr f) :=
    RHTower.ArchimedeanExactForm.continuous_autocorr hf.1 hf.2
  have hcs_auto : HasCompactSupport (autocorr f) :=
    RHTower.ArchimedeanExactForm.hasCompactSupport_autocorr hf.2
  have hint_pol : Integrable (fun x => SignedPrimePolar.polarDensity x * autocorr f x) := by
    unfold SignedPrimePolar.polarDensity
    exact ((continuous_const.mul (by fun_prop)).mul hc_auto).integrable_of_hasCompactSupport
      hcs_auto.mul_left
  have htail := (toRealWeilTestFn hf).polar_tail_eq_zero_of_supportScale_le (le_refl N)
  rw [toRealWeilTestFn_source] at htail
  have hIcc_Ioi : poleCross N f = ∫ x in Ioi (0 : ℝ), SignedPrimePolar.polarDensity x * autocorr f x := by
    unfold poleCross
    have hL : 0 ≤ SignedPrimePolar.cutoff N := SignedPrimePolar.cutoff_nonneg N
    rw [← integral_Ioc_eq_integral_Icc, ← add_zero (∫ x in Ioc 0 _, _), ← htail,
      ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hint_pol.integrableOn hint_pol.integrableOn,
      Ioc_union_Ioi_eq_Ioi hL]
  -- Evaluate the half-line `cosh` autocorrelation integral via `expHalfMoment * expNegHalfMoment`.
  have hauto_eq : autocorr f = autoCorr f := rfl
  have hE : expHalfMoment f * expNegHalfMoment f = ∫ t, Real.cosh (t / 2) * autoCorr f t := by
    rw [← integral_exp_mul_autoCorr_eq_cosh hcont hFB]
    have hin : ∀ x, f x * Real.exp (x / 2) * expNegHalfMoment f =
        ∫ t, f x * f (x + t) * Real.exp (-(1 / 2) * t) := fun x => by
      unfold expNegHalfMoment
      rw [← integral_add_left_eq_self (fun y => f y * Real.exp (-(y / 2))) x, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      have e : Real.exp (x / 2) * Real.exp (-((x + t) / 2)) = Real.exp (-(1 / 2) * t) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination (f x * f (x + t)) * e
    unfold expHalfMoment
    rw [← integral_mul_const, integral_congr_ae (Eventually.of_forall hin),
      integral_integral_swap (f := fun x t => f x * f (x + t) * Real.exp (-(1 / 2) * t))
        (integrable_autoCorr_kernel hcont hFB (-(1 / 2))).swap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [autoCorr]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have heven_int : (∫ t, Real.cosh (t / 2) * autoCorr f t) =
      2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * autoCorr f t := by
    have hev : Function.Even (fun t => Real.cosh (t / 2) * autoCorr f t) := fun t => by
      dsimp only
      rw [show -t / 2 = -(t / 2) by ring, Real.cosh_neg, autoCorr_neg]
    have hi : Integrable (fun t => Real.cosh (t / 2) * autoCorr f t) := by
      have : (fun t => Real.cosh (t / 2) * autoCorr f t) =
          fun t => (1 / 2) * (SignedPrimePolar.polarDensity t * autocorr f t) := by
        funext t; unfold SignedPrimePolar.polarDensity; rw [hauto_eq]; ring
      rw [this]
      exact hint_pol.const_mul (1 / 2)
    have hsplit_R := integral_univ_eq_integral_Iio_add_Ioi (0 : ℝ) hi
    have hneg_Ioi : (∫ t in Iio (0 : ℝ), Real.cosh (t / 2) * autoCorr f t) =
        ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * autoCorr f t := by
      rw [← integral_comp_neg_Ioi]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hev t
    have huniv : (∫ t, Real.cosh (t / 2) * autoCorr f t) =
        ∫ t in univ, Real.cosh (t / 2) * autoCorr f t := by simp
    linarith [huniv, hsplit_R, hneg_Ioi]
  have hpol_eq : (∫ x in Ioi (0 : ℝ), SignedPrimePolar.polarDensity x * autocorr f x) =
      2 * ∫ x in Ioi (0 : ℝ), Real.cosh (x / 2) * autoCorr f x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    unfold SignedPrimePolar.polarDensity
    rw [hauto_eq]
  rw [hIcc_Ioi, hpol_eq, ← heven_int, ← hE, expHalfMoment_eq hcont hcomp,
    expNegHalfMoment_eq hcont hcomp]
  ring

/-- **Closed prime-free window identity (`2a ≤ log 2`).** On the entire closed prime-free window
`[−a, a]` with `2a ≤ log 2` (including `2a = log 2`), `weilPair f f` is the sum of the diagonal
constant, the archimedean Lévy jump count, and the signed pole squares. -/
theorem weilPair_eq_jumpCount_add_poleSquares_of_le_log_two {f : ℝ → ℝ} (hf : f ∈ realTests)
    {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a) (ha : 2 * a ≤ Real.log 2) :
    weilPair f f = EF.gammaBracket 0 * (∫ u, f u ^ 2) + jumpCount f +
      2 * evenPoleMoment f ^ 2 - 2 * oddPoleMoment f ^ 2 := by
  have hid := (toRealWeilTestFn hf).re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le
    (le_refl (toRealWeilTestFn hf).supportScale)
  have hW : weilPair f f = (RHTower.weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (toRealWeilTestFn hf).1.1 (toRealWeilTestFn hf).1.1)).re := rfl
  rw [hW, hid, ← (toRealWeilTestFn hf).autocorr_eq 0, toRealWeilTestFn_source, autocorr_zero_eq]
  have hprime : ∑ n ∈ Finset.Icc 1 ((toRealWeilTestFn hf).supportScale + 2),
      SignedPrimePolar.primeWeight n * autocorr f (Real.log n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rcases (Finset.mem_Icc.mp hn).1.lt_or_eq with h | h
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n by omega))
      rw [autocorr_eq_zero_of_two_mul_le hs (le_trans ha hlog), mul_zero]
    · subst h
      simp [SignedPrimePolar.primeWeight]
  have hpole := two_mul_poleCross_eq_poleSquares hf
  unfold SignedPrimePolar.pairing jumpCount
  unfold poleCross at hpole
  rw [hprime]
  linarith

/-- **Single-prime (`2a ≤ log 3`) jump-count and `T₂`-graph identity.** On `[−a, a]` with
`2a ≤ log 3` (including `2a = log 3`), all primes `≥ 3` and prime powers `≥ 4` drop out, and
`weilPair f f` decomposes into the archimedean Lévy jump count, the `T₂`-graph jump count
`(log 2 / √2) primeTwoGraphJump f`, the combined diagonal `(Ω(0) − √2 log 2) ∫ f²`, and the
signed pole squares `2 evenPoleMoment(f)² − 2 oddPoleMoment(f)²`. -/
theorem weilPair_eq_jumpCount_add_primeTwoGraph_of_le_log_three {f : ℝ → ℝ} (hf : f ∈ realTests)
    {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a) (ha : 2 * a ≤ Real.log 3) :
    weilPair f f =
      (EF.gammaBracket 0 - Real.sqrt 2 * Real.log 2) * (∫ u, f u ^ 2) +
        jumpCount f + (Real.log 2 / Real.sqrt 2) * primeTwoGraphJump f +
        2 * evenPoleMoment f ^ 2 - 2 * oddPoleMoment f ^ 2 := by
  have hid := (toRealWeilTestFn hf).re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le
    (le_refl (toRealWeilTestFn hf).supportScale)
  have hW : weilPair f f = (RHTower.weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (toRealWeilTestFn hf).1.1 (toRealWeilTestFn hf).1.1)).re := rfl
  rw [hW, hid, ← (toRealWeilTestFn hf).autocorr_eq 0, toRealWeilTestFn_source, autocorr_zero_eq]
  set N := (toRealWeilTestFn hf).supportScale
  have hmem2 : (2 : ℕ) ∈ Finset.Icc 1 (N + 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hprime : ∑ n ∈ Finset.Icc 1 (N + 2),
      SignedPrimePolar.primeWeight n * autocorr f (Real.log n) =
        (Real.log 2 / Real.sqrt 2) * autocorr f (Real.log 2) := by
    rw [← Finset.add_sum_erase _ _ hmem2]
    have hrest : ∑ n ∈ (Finset.Icc 1 (N + 2)).erase 2,
        SignedPrimePolar.primeWeight n * autocorr f (Real.log n) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have hne2 : n ≠ 2 := (Finset.mem_erase.mp hn).1
      have hge1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_erase.mp hn).2).1
      rcases eq_or_ne n 1 with rfl | hne1
      · simp [SignedPrimePolar.primeWeight]
      · have hge3 : 3 ≤ n := by omega
        have hlog : Real.log 3 ≤ Real.log n :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hge3)
        rw [autocorr_eq_zero_of_two_mul_le hs (le_trans ha hlog), mul_zero]
    rw [hrest, add_zero]
    unfold SignedPrimePolar.primeWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    push_cast
    rfl
  have hpole := two_mul_poleCross_eq_poleSquares hf
  have hT2 := primeTwoGraphJump_eq hf
  have hsqrt : (Real.log 2 / Real.sqrt 2) * 2 = Real.sqrt 2 * Real.log 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hne]
    nlinarith [h2]
  unfold SignedPrimePolar.pairing jumpCount
  unfold poleCross at hpole
  rw [hprime, show -2 * ((Real.log 2 / Real.sqrt 2) * autocorr f (Real.log 2) - _) =
    (Real.log 2 / Real.sqrt 2) * (-2 * autocorr f (Real.log 2)) + 2 * _ by ring]
  have hsub : -2 * autocorr f (Real.log 2) = primeTwoGraphJump f - 2 * ∫ u, f u ^ 2 := by
    linarith [hT2]
  rw [hsub]
  linear_combination hpole - hsqrt * (∫ u, f u ^ 2)

/-- Primitive `h¹` form of the `{∞, 2}` window jump-count and `T₂`-graph identity (`2a ≤ log 3`). -/
theorem primitiveH1_eq_jumpCount_add_primeTwoGraph_of_le_log_three {a : ℝ}
    (ha : 2 * a ≤ Real.log 3) (x : ℝ × ℝ × realTestsAt a) :
    primitiveH1 (scalingSubsurface (realTestsAt a)) x =
      (1 / 2) * ((EF.gammaBracket 0 - Real.sqrt 2 * Real.log 2) * (∫ u, (x.2.2.1.1 u) ^ 2) +
        jumpCount x.2.2.1.1 + (Real.log 2 / Real.sqrt 2) * primeTwoGraphJump x.2.2.1.1) +
        evenPoleMoment x.2.2.1.1 ^ 2 - oddPoleMoment x.2.2.1.1 ^ 2 := by
  rw [primitiveH1_eq, scalingSubsurface_defect_self,
    weilPair_eq_jumpCount_add_primeTwoGraph_of_le_log_three x.2.2.1.2 x.2.2.2 ha]
  ring

/-! ### 3. Unconditional window coercivity corollaries in `LatticeSectionTheory` -/

/-- `weilPair f f = fullZeroForm f` for every real test `f ∈ realTests`. -/
theorem weilPair_eq_fullZeroForm {f : ℝ → ℝ} (hf : f ∈ realTests) :
    weilPair f f = fullZeroForm f := by
  have h1 := GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional
    hf.1.continuous hf.2
  have h2 : weilPair f f = (RHTower.weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (cx f) (cx f))).re := rfl
  rw [h2, ← h1]
  rfl

/-- **All-parity coercivity up to `a ≤ 3/10`.** Every `f ∈ realTests` supported in `[−a, a]` with
`a ≤ 3/10` satisfies `W(f, f) ≥ (1/5000) ∫ f²` (extending `LatticeSectionTheory` 19.2× beyond `1/64`). -/
theorem weilPair_ge_of_le_threeTenths {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (ha : a ≤ 3 / 10) :
    (1 / 5000 : ℝ) * (∫ u, f u ^ 2) ≤ weilPair f f := by
  rw [weilPair_eq_fullZeroForm hf]
  refine fullZeroForm_ge_of_support_le_threeTenths hf.1 hf.2 fun u hu => ?_
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hs hmem
  have habs : |u| ≤ a := abs_le.mpr this
  linarith

/-- **All-parity `primitiveH1` coercivity up to `a ≤ 3/10`.** -/
theorem primitiveH1_ge_of_le_threeTenths {a : ℝ} (ha : a ≤ 3 / 10)
    (x : ℝ × ℝ × realTestsAt a) :
    (1 / 10000 : ℝ) * (∫ u, (x.2.2.1.1 u) ^ 2) ≤
      primitiveH1 (scalingSubsurface (realTestsAt a)) x := by
  rw [primitiveH1_eq, scalingSubsurface_defect_self]
  have h := weilPair_ge_of_le_threeTenths x.2.2.1.2 x.2.2.2 ha
  linarith

/-- **Odd-sector coercivity past the first prime (`a ≤ 181/500 > ½ log 2`).** Every odd
`f ∈ realTests` supported in `[−a, a]` with `a ≤ 181/500` satisfies `W(f, f) ≥ (1/1000) ∫ f²`. -/
theorem weilPair_ge_of_odd_le_oneHundredEightyOneFiveHundredths {f : ℝ → ℝ} (hf : f ∈ realTests)
    (hodd : ∀ u, f (-u) = -f u) {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a) (ha : a ≤ 181 / 500) :
    (1 / 1000 : ℝ) * (∫ u, f u ^ 2) ≤ weilPair f f := by
  rw [weilPair_eq_fullZeroForm hf]
  refine fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hf.1 hf.2 hodd fun u hu => ?_
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have habs : |u| ≤ a := abs_le.mpr (hs hmem)
  linarith

/-- **Whole prime-free window and past `p = 2` (`2a ≤ log 2 + 1/50`) on `cosh`-orthogonal smooth tests.**
For every smooth `f` supported inside `(−a, a)` with `0 < a`, `2a ≤ log 2 + 1/50` (strictly
containing `[−½ log 2, ½ log 2]` and crossing `p = 2`), and `evenPoleMoment f = 0` (with no
condition on `oddPoleMoment f`), `weilPair f f ≥ (1/1000) ∫ f²`. -/
theorem weilPair_ge_of_evenPoleMoment_zero_past_primeTwo {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) {a : ℝ} (ha0 : 0 < a)
    (hs : tsupport f ⊆ Ioo (-a) a) (ha : 2 * a ≤ Real.log 2 + 1 / 50)
    (hC : evenPoleMoment f = 0) :
    (1 / 1000 : ℝ) * (∫ u, f u ^ 2) ≤ weilPair f f := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf_mem : f ∈ realTests := ⟨hf2, hfc⟩
  rw [weilPair_eq_fullZeroForm hf_mem, fullZeroForm_eq_even_add_odd hf2 hfc,
    integral_sq_eq_even_add_odd hf.continuous hfc]
  -- Even part `evenPartReal f`: smooth, supported in `(-a, a)`, both pole moments vanish.
  have hfe : ContDiff ℝ (⊤ : ℕ∞) (evenPartReal f) := by
    unfold evenPartReal
    exact ((hf.add (hf.comp contDiff_neg)).mul contDiff_const)
  have hfec : HasCompactSupport (evenPartReal f) := hasCompactSupport_evenPartReal hfc
  have hfes : tsupport (evenPartReal f) ⊆ Ioo (-a) a := by
    have hneg_s : tsupport (fun x => f (-x)) ⊆ Ioo (-a) a := by
      have : (fun x => f (-x)) = f ∘ Homeomorph.neg ℝ := rfl
      rw [this, tsupport_comp_eq_preimage f (Homeomorph.neg ℝ)]
      intro x hx
      have := hs hx
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    unfold evenPartReal
    refine (tsupport_mul_subset_left.trans (tsupport_add _ _)).trans (union_subset hs hneg_s)
  have hCe : evenPoleMoment (evenPartReal f) = 0 := by
    unfold evenPoleMoment evenPartReal
    have i1 : Integrable (fun x => f x * Real.cosh (x / 2)) :=
      (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
    have i2 : Integrable (fun x => f (-x) * Real.cosh (x / 2)) := by
      have := i1.comp_neg
      refine this.congr (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
    have hneg_eq : (∫ x, f (-x) * Real.cosh (x / 2)) = ∫ x, f x * Real.cosh (x / 2) := by
      rw [← integral_neg_eq_self (fun x => f x * Real.cosh (x / 2))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
    have hpt : (fun x => (f x + f (-x)) * (1 / 2) * Real.cosh (x / 2)) =
        fun x => (1 / 2) * (f x * Real.cosh (x / 2) + f (-x) * Real.cosh (x / 2)) :=
      funext fun x => by ring
    rw [hpt, integral_const_mul, integral_add i1 i2, hneg_eq]
    unfold evenPoleMoment at hC
    linarith
  have hSe : oddPoleMoment (evenPartReal f) = 0 :=
    oddPoleMoment_eq_zero_of_even (evenPartReal_neg f)
  let A : SuzukiPositiveAperture := ⟨a, ha0⟩
  have heven_floor := polarGroundEnergy_mul_le_fullZeroForm A hfe hfec hfes hCe hSe
  have hμ0 : (1 / 20 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy A :=
    one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo A (by change a ≤ _; linarith)
  have hfe_nn : 0 ≤ ∫ x, evenPartReal f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have heven_ge : (1 / 20 : ℝ) * (∫ x, evenPartReal f x ^ 2) ≤ fullZeroForm (evenPartReal f) :=
    (mul_le_mul_of_nonneg_right hμ0 hfe_nn).trans heven_floor
  -- Odd part `oddPartReal f`: `a ≤ (log 2 + 1/50)/2 < 181/500`.
  have ha_odd : a ≤ 181 / 500 := by linarith [Real.log_two_lt_d9]
  have hfo2 : ContDiff ℝ 2 (oddPartReal f) := by
    unfold oddPartReal
    exact ((hf2.sub (hf2.comp contDiff_neg)).mul contDiff_const)
  have hfoc : HasCompactSupport (oddPartReal f) := hasCompactSupport_oddPartReal hfc
  have hodd_ge : (1 / 1000 : ℝ) * (∫ x, oddPartReal f x ^ 2) ≤ fullZeroForm (oddPartReal f) := by
    refine fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hfo2 hfoc
      (oddPartReal_neg f) fun x hx => ?_
    have hx_pos : a < x ∨ x < -a := by
      rcases lt_or_ge x 0 with hlt | hge
      · rw [abs_of_neg hlt] at hx; exact Or.inr (by linarith)
      · rw [abs_of_nonneg hge] at hx; exact Or.inl (by linarith)
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport fun hm => by
      have := hs hm
      rcases hx_pos with h | h <;> linarith [this.1, this.2]
    have hfnx : f (-x) = 0 := image_eq_zero_of_notMem_tsupport fun hm => by
      have := hs hm
      rcases hx_pos with h | h <;> linarith [this.1, this.2]
    simp [oddPartReal, hfx, hfnx]
  linarith [heven_ge, hodd_ge, hfe_nn]

/-! ### 4. Full polarized CHMD radical of individual `Θ`-translates -/

/-- The pole-completed bilinear pairing on `SourceGraph`, adding `2(C_p C_q − S_p S_q)` to the
pole-free CHMD pairing `sourcePair`. -/
def fullSourcePair (p q : SourceGraph) : ℝ :=
  sourcePair p q + 2 * (polarCosine p * polarCosine q - polarSine p * polarSine q)

/-- **Every individual admissible `Θ`-translate lies in the radical of `fullSourcePair`.**
While `sourcePair (lift b hb) q = −cosh(b/2)⟨q, 1⟩ + sinh(b/2)⟨q, tanh⟩` is nonzero on the two
polar modes, the pole completion `2(C_p C_q − S_p S_q)` cancels both terms identically for every
individual shift `|b| < ½ log 2` and every `q : SourceGraph`. -/
theorem fullSourcePair_thetaTranslate_eq_zero (b : ℝ) (hb : 1 < 2 * Real.exp (-2 * |b|))
    (q : SourceGraph) :
    fullSourcePair (CHMDThetaTranslate.lift b hb) q = 0 := by
  unfold fullSourcePair
  rw [sourcePair_thetaTranslate b hb q, polarCosine_thetaTranslate b hb,
    polarSine_thetaTranslate b hb, polarCosine_oneL q, polarSine_tanhL q]
  ring

end GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts

end
