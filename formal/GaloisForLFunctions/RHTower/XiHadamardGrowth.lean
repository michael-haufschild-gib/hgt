import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.HTGeometry.CanonicalProductGrowth
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Subquadratic Hadamard growth for the centered Xi canonical product

The genus-one product over the exact Xi divisor has Nevanlinna proximity `o(r^(2 : ℕ))`.  The First Main
Theorem transfers the same bound to its reciprocal, the unconditional order-one estimate transfers
it to `XiC`, and hence the entire zero-free Hadamard quotient also has proximity `o(r^(2 : ℕ))`.

Poisson, Borel--Caratheodory, and Cauchy estimates then show that any entire logarithm of that
quotient is affine.  Evenness kills its linear term, giving the unconditional multiplicity-exact
Hadamard factorization of `XiC`.
-/

open Complex Metric Set Real Filter Topology MeasureTheory
open Asymptotics

namespace RHTower

open ValueDistribution

lemma posLog_norm_exp_eq_max_re (z : ℂ) :
    Real.posLog ‖Complex.exp z‖ = max 0 z.re := by
  simp [Real.posLog_def, Complex.norm_exp]

theorem realPart_le_three_proximity_of_exp
    (q g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hexp : ∀ z, q z = Complex.exp (g z))
    {w : ℂ} {R : ℝ} (hR : 0 < R) (hw2 : 2 * ‖w‖ ≤ R) :
    (g w).re ≤ 3 * proximity q ⊤ R := by
  have hw : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    nlinarith [norm_nonneg w]
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => (g z).re)
      (closedBall (0 : ℂ) R) := by
    intro z _
    exact (hg.analyticAt z).harmonicAt_re
  have hpois := hharm.circleAverage_re_herglotzRieszKernel_smul hw
  have hqdiff : Differentiable ℂ q := by
    have heq : q = fun z => Complex.exp (g z) := funext hexp
    rw [heq]
    fun_prop
  have hleft : CircleIntegrable
      ((Complex.re ∘ herglotzRieszKernel 0 w) • fun z => (g z).re) 0 R := by
    have hker : ContinuousOn (Complex.re ∘ herglotzRieszKernel 0 w) (sphere 0 |R|) := by
      intro z hz
      apply ContinuousAt.continuousWithinAt
      have hcont : ContinuousAt (fun z => ((z + w) / (z - w)).re) z := by
        apply Complex.continuous_re.continuousAt.comp
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · intro hzw
          have hnorm : ‖z‖ = ‖w‖ := congrArg norm (sub_eq_zero.mp hzw)
          have hzR : ‖z‖ = R := by
            simpa [mem_sphere_zero_iff_norm, abs_of_pos hR] using hz
          have hwR : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hw
          linarith
      have heq : (Complex.re ∘ herglotzRieszKernel 0 w) =
          fun u => ((u + w) / (u - w)).re := by
        funext u
        simp only [Function.comp_apply, herglotzRieszKernel_def, sub_zero]
      rw [heq]
      exact hcont
    have hgcont : ContinuousOn (fun z => (g z).re) (sphere 0 |R|) :=
      (Complex.continuous_re.comp hg.continuous).continuousOn
    exact hker.smul hgcont |>.circleIntegrable'
  have hright : CircleIntegrable (fun z => 3 * Real.posLog ‖q z‖) 0 R := by
    have hqanalytic : AnalyticOnNhd ℂ q Set.univ :=
      analyticOnNhd_univ_iff_differentiable.mpr hqdiff
    have hqmerSphere : MeromorphicOn q (sphere 0 |R|) := by
      intro z _
      exact hqanalytic.meromorphicOn z (Set.mem_univ z)
    have hi : CircleIntegrable (fun z => Real.posLog ‖q z‖) 0 R :=
      hqmerSphere.circleIntegrable_posLog_norm
    simpa only [smul_eq_mul] using!
      (CircleIntegrable.const_smul (a := (3 : ℝ)) hi)
  calc
    (g w).re = Real.circleAverage
        ((Complex.re ∘ herglotzRieszKernel 0 w) • fun z => (g z).re) 0 R := hpois.symm
    _ ≤ Real.circleAverage (fun z => 3 * Real.posLog ‖q z‖) 0 R := by
      apply Real.circleAverage_mono hleft hright
      intro z hz
      have hzR : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
      have hkupper := re_herglotzRieszKernel_le hzR hw
      have hklower := le_re_herglotzRieszKernel hzR hw
      have hkrat : (R - ‖w‖) / (R + ‖w‖) ≤
          ((z - 0 + (w - 0)) / ((z - 0) - (w - 0))).re := by
        simpa using hklower
      have hwR : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hw
      have hratio_nonneg : 0 ≤ (R - ‖w‖) / (R + ‖w‖) := by
        positivity
      have hk0 : 0 ≤ (herglotzRieszKernel 0 w z).re := by
        rw [herglotzRieszKernel_def]
        exact hratio_nonneg.trans hkrat
      have hk3 : (herglotzRieszKernel 0 w z).re ≤ 3 := by
        rw [herglotzRieszKernel_def]
        calc
          ((z - 0 + (w - 0)) / (z - 0 - (w - 0))).re
              ≤ (R + ‖w‖) / (R - ‖w‖) := by simpa using hkupper
          _ ≤ 3 := by
            rw [div_le_iff₀]
            · nlinarith
            · nlinarith [norm_nonneg w]
      change (herglotzRieszKernel 0 w z).re * (g z).re ≤
        3 * Real.posLog ‖q z‖
      rw [hexp z, posLog_norm_exp_eq_max_re]
      calc
        (herglotzRieszKernel 0 w z).re * (g z).re
            ≤ (herglotzRieszKernel 0 w z).re * max 0 (g z).re := by
          gcongr
          exact le_max_right _ _
        _ ≤ 3 * max 0 (g z).re := by
          exact mul_le_mul_of_nonneg_right hk3 (le_max_left _ _)
    _ = 3 * proximity q ⊤ R := by
      rw [show (fun z => 3 * Real.posLog ‖q z‖) =
          fun z => (3 : ℝ) • Real.posLog ‖q z‖ by ext z; simp]
      rw [Real.circleAverage_fun_smul, proximity_top]
      simp

theorem proximity_zero_le_proximity_top_of_entire_one
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 = 1)
    {r : ℝ} (hr : 1 ≤ r) :
    proximity f 0 r ≤ proximity f ⊤ r := by
  have hfm : Meromorphic f := by
    intro z
    exact (hf z (Set.mem_univ z)).meromorphicAt
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have htrail : meromorphicTrailingCoeffAt f 0 = 1 := by
    rw [(hf 0 (Set.mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero]
    · exact hf0
    · rw [hf0]
      exact one_ne_zero
  have hchar := characteristic_sub_characteristic_inv_of_ne_zero hfm hr0
  rw [htrail, norm_one, Real.log_one] at hchar
  have hpoles : logCounting f ⊤ = 0 := by
    rw [logCounting_top,
      negPart_eq_zero.mpr (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)]
    simp
  have hcount : 0 ≤ logCounting f⁻¹ ⊤ r := logCounting_nonneg hr
  rw [characteristic, Pi.add_apply, hpoles, Pi.zero_apply, add_zero,
    characteristic, Pi.add_apply, proximity_inv] at hchar
  linarith

theorem proximity_zero_isLittleO_sq_of_entire_one
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 = 1)
    (htop : proximity f ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ))) :
    proximity f 0 =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [isLittleO_iff.mp htop hc, eventually_ge_atTop (1 : ℝ)] with r htopr hr
  rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r)]
  calc
    proximity f 0 r ≤ proximity f ⊤ r :=
      proximity_zero_le_proximity_top_of_entire_one f hf hf0 hr
    _ = ‖proximity f ⊤ r‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r)]
    _ ≤ c * ‖r ^ (2 : ℕ)‖ := htopr

theorem orderOneLog_envelope_div_sq_tendsto_zero (C : ℝ) :
    Tendsto (fun r : ℝ =>
      (C * (1 + |r|) * Real.log (2 + |r|)) / r ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun r : ℝ => Real.log (2 + r) / r) atTop (𝓝 0) := by
    have hbase : Tendsto (fun u : ℝ => Real.log u / (1 * u + (-2))) atTop (𝓝 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero
        |>.congr (by intro u; simp)
    have hto : Tendsto (fun r : ℝ => r + 2) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_id
    refine (hbase.comp hto).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [Function.comp_apply]
    congr 1
    · congr 1
      ring
    · ring
  have hlin : Tendsto (fun r : ℝ => (1 + r) / r) atTop (𝓝 1) := by
    have hconst : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).div_atTop tendsto_id
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hadd := hconst.add hone
    simpa only [zero_add] using hadd.congr' (by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
      field_simp)
  have hprod := (hlin.mul hlog).const_mul C
  simp only [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [abs_of_pos hr]
  field_simp

theorem orderOneLog_envelope_isLittleO_sq (C : ℝ) :
    (fun r : ℝ => C * (1 + |r|) * Real.log (2 + |r|)) =o[atTop]
      (fun r : ℝ => r ^ (2 : ℕ)) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
    intro hs
    exact (hr (sq_eq_zero_iff.mp hs)).elim
  · exact orderOneLog_envelope_div_sq_tendsto_zero C

theorem proximity_isLittleO_sq_of_orderOneLog
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ,
      ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    proximity f ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
  have hpoint : ∀ r : ℝ, proximity f ⊤ r ≤
      C * (1 + |r|) * Real.log (2 + |r|) := by
    intro r
    rw [proximity_top]
    rw [← Real.circleAverage_const
      (C * (1 + |r|) * Real.log (2 + |r|)) 0 r]
    apply Real.circleAverage_mono
    · have hfm : MeromorphicOn f (sphere 0 |r|) := by
        intro z _
        exact hf.meromorphicOn z (Set.mem_univ z)
      exact hfm.circleIntegrable_posLog_norm
    · exact circleIntegrable_const _ _ _
    · intro z hz
      have hzr : ‖z‖ = |r| := by
        simpa [mem_sphere_zero_iff_norm] using hz
      have harg : 0 ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
        have hlog : 0 ≤ Real.log (2 + ‖z‖) :=
          Real.log_nonneg (by linarith [norm_nonneg z])
        positivity
      calc
        Real.posLog ‖f z‖ ≤ Real.posLog
            (Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :=
          Real.monotoneOn_posLog (norm_nonneg _) (Real.exp_pos _).le (hbound z)
        _ = C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
          rw [Real.posLog_eq_log]
          · exact Real.log_exp _
          · rw [abs_of_pos (Real.exp_pos _)]
            exact Real.one_le_exp harg
        _ = C * (1 + |r|) * Real.log (2 + |r|) := by rw [hzr]
  have henv := orderOneLog_envelope_isLittleO_sq C
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [isLittleO_iff.mp henv hc] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r)]
  calc
    proximity f ⊤ r ≤ C * (1 + |r|) * Real.log (2 + |r|) := hpoint r
    _ = ‖C * (1 + |r|) * Real.log (2 + |r|)‖ := by
      have hlog : 0 ≤ Real.log (2 + |r|) :=
        Real.log_nonneg (by linarith [abs_nonneg r])
      have hnonneg : 0 ≤ C * (1 + |r|) * Real.log (2 + |r|) := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ c * ‖r ^ (2 : ℕ)‖ := hr

theorem xiCanonicalProduct_proximity_isLittleO_sq :
    proximity xiCanonicalProduct ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
  simpa only [xiCanonicalProduct] using
    (canonicalProductE1Indexed_proximity_isLittleO_sq xiSpectralPoint
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable)

theorem xiCanonicalProduct_proximity_zero_isLittleO_sq :
    proximity xiCanonicalProduct 0 =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) :=
  proximity_zero_isLittleO_sq_of_entire_one xiCanonicalProduct
    xiCanonicalProduct_analytic xiCanonicalProduct_zero
    xiCanonicalProduct_proximity_isLittleO_sq

theorem XiC_proximity_isLittleO_sq :
    proximity XiC ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ := XiC_order
  exact proximity_isLittleO_sq_of_orderOneLog XiC XiC_analytic C hC.le hbound

theorem xiHadamardQuotient_eq_mul_inv_codiscrete :
    xiHadamardQuotient =ᶠ[codiscrete ℂ] XiC * xiCanonicalProduct⁻¹ := by
  have hraw : xiHadamardRawQuotient =ᶠ[codiscrete ℂ] xiHadamardQuotient := by
    simpa only [xiHadamardQuotient] using!
      (toMeromorphicNFOn_eqOn_codiscrete xiHadamardRawQuotient_meromorphic)
  exact hraw.symm.trans (Filter.Eventually.of_forall fun z => by
    simp only [xiHadamardRawQuotient, Pi.div_apply, Pi.mul_apply, Pi.inv_apply,
      div_eq_mul_inv])

theorem xiHadamardQuotient_proximity_eventually_le :
    proximity xiHadamardQuotient ⊤ ≤ᶠ[atTop]
      proximity XiC ⊤ + proximity xiCanonicalProduct 0 := by
  have hXi : Meromorphic XiC := by
    intro z
    exact (XiC_analytic z (Set.mem_univ z)).meromorphicAt
  have hP : Meromorphic xiCanonicalProduct := by
    intro z
    exact (xiCanonicalProduct_analytic z (Set.mem_univ z)).meromorphicAt
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
  rw [proximity_congr_codiscrete xiHadamardQuotient_eq_mul_inv_codiscrete hr]
  calc
    proximity (XiC * xiCanonicalProduct⁻¹) ⊤ r ≤
        (proximity XiC ⊤ + proximity xiCanonicalProduct⁻¹ ⊤) r :=
      proximity_mul_top_le hXi hP.inv r
    _ = (proximity XiC ⊤ + proximity xiCanonicalProduct 0) r := by
      rw [proximity_inv]

theorem xiHadamardQuotient_proximity_isLittleO_sq :
    proximity xiHadamardQuotient ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
  have hsum := XiC_proximity_isLittleO_sq.add
    xiCanonicalProduct_proximity_zero_isLittleO_sq
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [isLittleO_iff.mp hsum hc,
    xiHadamardQuotient_proximity_eventually_le] with r hsumr hle
  rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r)]
  calc
    proximity xiHadamardQuotient ⊤ r ≤
        (proximity XiC ⊤ + proximity xiCanonicalProduct 0) r := hle
    _ = ‖(proximity XiC ⊤ + proximity xiCanonicalProduct 0) r‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact add_nonneg (proximity_nonneg r) (proximity_nonneg r)
    _ ≤ c * ‖r ^ (2 : ℕ)‖ := hsumr

/-- A zero-free entire function of subquadratic Nevanlinna proximity has an affine entire
logarithm.  This is the minimal-growth Hadamard lemma needed for genus-one products. -/
theorem entire_log_affine_of_proximity_isLittleO_sq
    (q g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hexp : ∀ z, q z = Complex.exp (g z))
    (hprox : proximity q ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ))) :
    ∀ z : ℂ, g z = g 0 + deriv g 0 * z := by
  have hsecond : ∀ c : ℂ, iteratedDeriv 2 g c = 0 := by
    intro c
    have hcauchy : ∀ r : ℝ, 0 < r →
        ‖iteratedDeriv 2 g c‖ ≤
          2 * (6 * proximity q ⊤ (2 * (1 + ‖c‖ + 2 * r)) +
            2 + 3 * ‖g c‖) / r ^ (2 : ℕ) := by
      intro r hr
      have hsph : ∀ w ∈ sphere c r,
          ‖g w‖ ≤ 6 * proximity q ⊤ (2 * (1 + ‖c‖ + 2 * r)) +
            2 + 3 * ‖g c‖ := by
        intro w hw
        let φ : ℂ → ℂ := fun z => g (c + z)
        let R : ℝ := 2 * r
        let S : ℝ := 2 * (1 + ‖c‖ + R)
        let M : ℝ := 3 * proximity q ⊤ S + 1
        have hRpos : 0 < R := by dsimp only [R]; positivity
        have hSpos : 0 < S := by dsimp only [S, R]; positivity
        have hMpos : 0 < M := by
          dsimp only [M]
          have hp : 0 ≤ proximity q (⊤ : WithTop ℂ) S := by
            simpa using (proximity_nonneg (f := q) (a := (⊤ : WithTop ℂ)) S)
          linarith
        have hφdiff : Differentiable ℂ φ := by
          dsimp only [φ]
          fun_prop
        have hmaps : MapsTo φ (ball (0 : ℂ) R) {u | u.re ≤ M} := by
          intro z hz
          rw [mem_ball_zero_iff] at hz
          simp only [mem_setOf_eq]
          have hnorm : ‖c + z‖ ≤ ‖c‖ + ‖z‖ := norm_add_le _ _
          have htwonorm : 2 * ‖c + z‖ ≤ S := by
            dsimp only [S]
            nlinarith [norm_nonneg c, norm_nonneg z]
          have hre := realPart_le_three_proximity_of_exp q g hg hexp hSpos htwonorm
          dsimp only [φ, M]
          exact hre.trans (by linarith)
        have hwsub : w - c ∈ ball (0 : ℂ) R := by
          rw [mem_ball_zero_iff]
          have hwr : ‖w - c‖ = r := mem_sphere_iff_norm.mp hw
          rw [hwr]
          dsimp only [R]
          linarith
        have hbc := Complex.borelCaratheodory hMpos hφdiff.differentiableOn
          hmaps hRpos hwsub
        have hwr : ‖w - c‖ = r := mem_sphere_iff_norm.mp hw
        have hφw : φ (w - c) = g w := by
          dsimp only [φ]
          rw [add_sub_cancel]
        have hφ0 : φ 0 = g c := by simp [φ]
        rw [hφw, hφ0, hwr] at hbc
        have hden : R - r = r := by dsimp only [R]; ring
        have hsum : R + r = 3 * r := by dsimp only [R]; ring
        rw [hden, hsum] at hbc
        have hrne : r ≠ 0 := ne_of_gt hr
        have hsimple :
            2 * M * r / r + ‖g c‖ * (3 * r) / r = 2 * M + 3 * ‖g c‖ := by
          field_simp
        rw [hsimple] at hbc
        dsimp only [M, S, R] at hbc ⊢
        nlinarith
      have hcalc :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          2 hr hg.diffContOnCl hsph
      norm_num [Nat.factorial] at hcalc
      exact hcalc
    let S : ℝ → ℝ := fun r => 2 * (1 + ‖c‖ + 2 * r)
    have hS_tendsto : Tendsto S atTop atTop := by
      have hfour : Tendsto (fun r : ℝ => 4 * r) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
      have hadd := Filter.tendsto_atTop_add_const_right _ (2 * (1 + ‖c‖)) hfour
      convert hadd using 1
      ext r
      dsimp only [S]
      ring
    have hcomp := hprox.comp_tendsto hS_tendsto
    have hSbig : (fun r : ℝ => (S r) ^ (2 : ℕ)) =O[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
      apply isBigO_iff.mpr
      let K : ℝ := 6 + 2 * ‖c‖
      refine ⟨K ^ (2 : ℕ), ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr1
      have hK0 : 0 ≤ K := by dsimp only [K]; positivity
      have hS0 : 0 ≤ S r := by dsimp only [S]; positivity
      have hr0 : 0 ≤ r := zero_le_one.trans hr1
      have hSK : S r ≤ K * r := by
        dsimp only [S, K]
        nlinarith [norm_nonneg c]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ hS0 (mul_nonneg hK0 hr0)).mpr hSK |>.trans_eq (by ring)
    have hm : (fun r : ℝ => proximity q ⊤ (S r)) =o[atTop]
        (fun r : ℝ => r ^ (2 : ℕ)) := by
      have := hcomp.trans_isBigO hSbig
      simpa only [Function.comp_apply] using! this
    have hratio : Tendsto (fun r : ℝ => proximity q ⊤ (S r) / r ^ (2 : ℕ))
        atTop (𝓝 0) := by
      apply (isLittleO_iff_tendsto' ?_).mp hm
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr0
      intro hs
      exact (hr0 (sq_eq_zero_iff.mp hs)).elim
    have htend : Tendsto (fun r : ℝ =>
        2 * (6 * proximity q ⊤ (S r) + 2 + 3 * ‖g c‖) / r ^ (2 : ℕ))
        atTop (𝓝 0) := by
      have hmain := hratio.const_mul 12
      simp only [mul_zero] at hmain
      have hconst : Tendsto (fun r : ℝ => (4 + 6 * ‖g c‖) / r ^ (2 : ℕ))
          atTop (𝓝 0) := by
        have hinv : Tendsto (fun r : ℝ => (r ^ (2 : ℕ))⁻¹) atTop (𝓝 0) :=
          Filter.Tendsto.comp tendsto_inv_atTop_zero
            (tendsto_pow_atTop (by norm_num))
        have hmul := hinv.const_mul (4 + 6 * ‖g c‖)
        simp only [mul_zero] at hmul
        simpa [div_eq_mul_inv] using hmul
      have hsum := hmain.add hconst
      simp only [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr0
      field_simp
      ring
    have hle : ‖iteratedDeriv 2 g c‖ ≤ 0 := by
      refine ge_of_tendsto htend ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      simpa only [S] using hcauchy r hr
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  have hid2 : ∀ c : ℂ, deriv (deriv g) c = 0 := by
    intro c
    have h := hsecond c
    rwa [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero] at h
  have hderiv_diff : Differentiable ℂ (deriv g) := fun z =>
    ((hg.analyticAt z).deriv).differentiableAt
  have hdg_const : ∀ x : ℂ, deriv g x = deriv g 0 :=
    fun x => is_const_of_deriv_eq_zero hderiv_diff hid2 x 0
  intro z
  let φ : ℂ → ℂ := fun w => g w - deriv g 0 * w
  have hφdiff : Differentiable ℂ φ := by
    dsimp only [φ]
    fun_prop
  have hφderiv : ∀ w : ℂ, deriv φ w = 0 := by
    intro w
    have hsub : HasDerivAt φ (deriv g w - deriv g 0 * 1) w := by
      dsimp only [φ]
      exact (hg w).hasDerivAt.sub
        (HasDerivAt.const_mul (deriv g 0) (hasDerivAt_id w))
    rw [hsub.deriv, hdg_const w]
    ring
  have hφconst : φ z = φ 0 := is_const_of_deriv_eq_zero hφdiff hφderiv z 0
  dsimp only [φ] at hφconst
  linear_combination hφconst

theorem xiHadamardQuotient_constant :
    ∀ z, xiHadamardQuotient z = xiHadamardQuotient 0 := by
  obtain ⟨g, hg, hexp⟩ := xiHadamardQuotient_has_log
  have haff := entire_log_affine_of_proximity_isLittleO_sq
    xiHadamardQuotient g hg hexp xiHadamardQuotient_proximity_isLittleO_sq
  have hfun : xiHadamardQuotient = fun z => Complex.exp (g z) := funext hexp
  have hExpDeriv : HasDerivAt (fun z => Complex.exp (g z))
      (Complex.exp (g 0) * deriv g 0) 0 := (hg 0).hasDerivAt.cexp
  have hderivEq := congrArg (fun f : ℂ → ℂ => deriv f 0) hfun
  change deriv xiHadamardQuotient 0 = deriv (fun z => Complex.exp (g z)) 0 at hderivEq
  rw [xiHadamardQuotient_deriv_zero, hExpDeriv.deriv] at hderivEq
  have hgderiv : deriv g 0 = 0 :=
    (mul_eq_zero.mp hderivEq.symm).resolve_left (Complex.exp_ne_zero _)
  intro z
  rw [hexp z, hexp 0, haff z, hgderiv, zero_mul, add_zero]

theorem xiHadamardQuotient_zero : xiHadamardQuotient 0 = XiC 0 := by
  have h := congrFun xiHadamardQuotient_mul_canonicalProduct 0
  simpa only [Pi.mul_apply, xiCanonicalProduct_zero, mul_one] using h

/-- Unconditional multiplicity-exact Hadamard product for the centered Xi function. -/
theorem XiC_eq_constant_mul_canonicalProduct :
    XiC = (fun _ => XiC 0) * xiCanonicalProduct := by
  funext z
  have h := congrFun xiHadamardQuotient_mul_canonicalProduct z
  simp only [Pi.mul_apply] at h ⊢
  rw [← h, xiHadamardQuotient_constant z, xiHadamardQuotient_zero]

end RHTower
