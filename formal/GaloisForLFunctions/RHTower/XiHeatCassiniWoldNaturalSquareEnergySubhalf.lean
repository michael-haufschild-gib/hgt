import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyHalfNoGo
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelSingularDivisorTomography
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualMertensInverseAbel

/-!
# The natural Wold square energy below one half is exactly RH

For the literal centered natural-cutoff Wold residual `R N`, the global energy at radius `t` is
`E(t) = Σ_N N^(2t-1) |R N|²`.

**Theorem** (`riemannHypothesis_iff_forall_woldNatResidualSquareEnergy_lt_half`).
RH holds iff `E(t) < ∞` for every `0 < t < 1/2`.

The transfer is lossless.  For `a < t`, AM–GM gives
`|R(N+1)| (N+1)^(a-1) ≤ ½ ((N+1)^(2t-1) R(N+1)² + (N+1)^(2(a-t)-1))`, so the first-difference Abel
current `Σ R(N+1) ((N+1)^(-s) - (N+2)^(-s))` is holomorphic on `re s > -t`.  On the sector
`-t < re s, 0 < im s` the zeta-cleared Wold continuation equals `ζ(s+1)` times the regular
continuation, by the identity theorem from `re s > 0`.  A zero `ρ` of `ζ` with `re ρ > 1 - t`
would give the singular carrier a nonzero residue at `ρ - 1`, while it agrees there with the
holomorphic regular continuation.  Taking `t` close to `1/2` excludes every zero right of the
critical line.  The converse is the strict half-power rate under RH.

Energies at `t ≥ 1/2` are impossible unconditionally (`not_woldNatResidualSquareEnergy_half`,
`not_woldNatResidualSquareEnergy_of_half_lt`), so the sub-half range is the whole content.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

local notation "R" => xiHeatCassiniWoldNatResidualLogDiscrepancy

/-! ### Energy to weighted `ℓ¹` -/

private theorem amgm_rpow {x u : ℝ} (hx : 0 < x) (a t : ℝ) :
    u * x ^ (a - 1) ≤ (x ^ (2 * t - 1) * u ^ 2 + x ^ (2 * (a - t) - 1)) / 2 := by
  have h1 : x ^ (a - 1) = x ^ (t - 1 / 2) * x ^ (a - t - 1 / 2) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have h2 : x ^ (2 * t - 1) = (x ^ (t - 1 / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring
  have h3 : x ^ (2 * (a - t) - 1) = (x ^ (a - t - 1 / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (u * x ^ (t - 1 / 2) - x ^ (a - t - 1 / 2))]

/-- **Lossless weighted `ℓ¹` transfer.**  Square energy at `t` gives absolute summability of
`|R(N+1)| (N+1)^(a-1)` for every `a < t`. -/
theorem summable_abs_woldNatResidual_mul_rpow_of_squareEnergy {t a : ℝ} (hat : a < t)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    Summable (fun N : ℕ => |R (N + 1)| * ((N : ℝ) + 1) ^ (a - 1)) := by
  have hE : Summable (fun N : ℕ => ((N : ℝ) + 1) ^ (2 * t - 1) * |R (N + 1)| ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr hEnergy
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hP : Summable (fun N : ℕ => ((N : ℝ) + 1) ^ (2 * (a - t) - 1)) := by
    have h := (Real.summable_nat_rpow.mpr (show 2 * (a - t) - 1 < -1 by linarith))
    have h' := (summable_nat_add_iff 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
    ((hE.add hP).div_const 2)
  have hx : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h := amgm_rpow (u := |R (N + 1)|) hx a t
  rw [sq_abs] at h ⊢
  simpa only [sq_abs] using h

/-! ### The Abel current below the critical wall -/

theorem norm_woldNatResidualAbelAtom_le_rpow {a : ℝ} (ha : a ≤ 1) {s : ℂ} (hsre : -a ≤ s.re)
    (N : ℕ) :
    ‖woldNatResidualAbelAtom s N‖ ≤ ‖s‖ * (|R (N + 1)| * ((N : ℝ) + 1) ^ (a - 1)) := by
  by_cases hs0 : s = 0
  · subst s
    simp [woldNatResidualAbelAtom]
  have hm : 0 < (N : ℝ) + 1 := by positivity
  have ht : (N : ℝ) + 2 ∈ Set.Icc ((N : ℝ) + 1) (((N : ℝ) + 1) + 1) := by
    constructor <;> linarith
  have hwne : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hwre : (-s).re ≤ 1 := by simp only [neg_re]; linarith
  have hinc := GaloisForLFunctions.HTGeometry.norm_ofReal_cpow_sub_le hwne hwre hm ht
  have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : ((N : ℝ) + 1) ^ ((-s).re - 1) ≤ ((N : ℝ) + 1) ^ (a - 1) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by simp only [neg_re]; linarith)
  rw [norm_sub_rev] at hinc
  have hinc' : ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) - ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
      ‖s‖ * ((N : ℝ) + 1) ^ (a - 1) := by
    calc _ ≤ ‖-s‖ * ((N : ℝ) + 1) ^ ((-s).re - 1) := hinc
      _ ≤ ‖-s‖ * ((N : ℝ) + 1) ^ (a - 1) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = ‖s‖ * ((N : ℝ) + 1) ^ (a - 1) := by rw [norm_neg]
  rw [woldNatResidualAbelAtom, norm_mul, norm_real, Real.norm_eq_abs]
  calc |R (N + 1)| * ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) - ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖
      ≤ |R (N + 1)| * (‖s‖ * ((N : ℝ) + 1) ^ (a - 1)) :=
        mul_le_mul_of_nonneg_left hinc' (abs_nonneg _)
    _ = ‖s‖ * (|R (N + 1)| * ((N : ℝ) + 1) ^ (a - 1)) := by ring

theorem summable_woldNatResidualAbelAtom_of_squareEnergy_rpow {t a : ℝ} (hat : a < t)
    (ha : a ≤ 1) (hEnergy : WoldNatResidualSquareEnergy t) {s : ℂ} (hsre : -a ≤ s.re) :
    Summable (woldNatResidualAbelAtom s) :=
  Summable.of_norm_bounded
    ((summable_abs_woldNatResidual_mul_rpow_of_squareEnergy hat hEnergy).mul_left ‖s‖)
    (norm_woldNatResidualAbelAtom_le_rpow ha hsre)

/-- Square energy at `t ≤ 1` makes the natural Abel current holomorphic on `re s > -t`. -/
theorem differentiableAt_woldNatResidualAbelCurrent_of_squareEnergy_rpow {t : ℝ} (ht1 : t ≤ 1)
    (hEnergy : WoldNatResidualSquareEnergy t) {s : ℂ} (hs : -t < s.re) :
    DifferentiableAt ℂ woldNatResidualAbelCurrent s := by
  let a : ℝ := (t - s.re) / 2
  let radius : ℝ := (t + s.re) / 4
  have hradius : 0 < radius := by dsimp only [radius]; linarith
  have hat : a < t := by dsimp only [a]; linarith
  have ha1 : a ≤ 1 := by dsimp only [a]; linarith
  let q : ℕ → ℝ := fun N => |R (N + 1)| * ((N : ℝ) + 1) ^ (a - 1)
  let bound : ℕ → ℝ := fun N => (‖s‖ + radius) * q N
  have hq : Summable q := summable_abs_woldNatResidual_mul_rpow_of_squareEnergy hat hEnergy
  have hboundSum : Summable bound := hq.mul_left (‖s‖ + radius)
  have hdiff : ∀ N : ℕ,
      DifferentiableOn ℂ (woldNatResidualAbelAtom · N) (Metric.ball s radius) := by
    intro N z _
    have hbase1 : ((((N : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
    have hbase2 : ((((N : ℝ) + 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 2 ≠ 0 by positivity)
    unfold woldNatResidualAbelAtom
    exact ((((differentiableAt_id.neg).const_cpow (Or.inl hbase1)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hbase2))).const_mul
        (R (N + 1) : ℂ)).differentiableWithinAt
  have hbound : ∀ N : ℕ, ∀ z ∈ Metric.ball s radius,
      ‖woldNatResidualAbelAtom z N‖ ≤ bound N := by
    intro N z hz
    have hdist : ‖z - s‖ < radius := by rw [Metric.mem_ball, dist_eq] at hz; exact hz
    have hreNorm : |(z - s).re| ≤ ‖z - s‖ := abs_re_le_norm (z - s)
    have hzre : -a ≤ z.re := by
      simp only [sub_re] at hreNorm
      have hleft : -‖z - s‖ ≤ z.re - s.re := (abs_le.mp hreNorm).1
      dsimp only [a, radius] at hdist ⊢
      linarith
    have hnorm : ‖z‖ ≤ ‖s‖ + radius := by
      calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
        _ ≤ ‖s‖ + radius := by linarith
    have hqnonneg : 0 ≤ q N := by dsimp only [q]; positivity
    calc ‖woldNatResidualAbelAtom z N‖ ≤ ‖z‖ * q N := by
          simpa only [q] using norm_woldNatResidualAbelAtom_le_rpow ha1 hzre N
      _ ≤ (‖s‖ + radius) * q N := mul_le_mul_of_nonneg_right hnorm hqnonneg
      _ = bound N := rfl
  change DifferentiableAt ℂ (fun z : ℂ => ∑' N : ℕ, woldNatResidualAbelAtom z N) s
  exact GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
    hradius hdiff hbound hboundSum

/-! ### The safe identity under any positive energy -/

theorem abelDirichlet_woldNatDifferenceCoeff_eq_of_squareEnergy_pos {t : ℝ} (ht : 0 < t)
    (hEnergy : WoldNatResidualSquareEnergy t) {s : ℂ} (hs : 0 < s.re) :
    abelDirichlet woldNatDifferenceCoeff s =
      woldNatResidualAbelCurrent s + (xiHeatCassiniWoldLogHolonomyConstant : ℂ) := by
  have hA := summable_woldNatResidualAbelAtom_of_squareEnergy_rpow (a := 0) ht zero_le_one
    hEnergy (by linarith : -(0 : ℝ) ≤ s.re)
  have hD := summable_naturalCpowKernel_sub_succ hs
  have hCD := hD.mul_left (xiHeatCassiniWoldLogHolonomyConstant : ℂ)
  rw [abelDirichlet, woldNatResidualAbelCurrent]
  calc
    (∑' k : ℕ, coeffPartial woldNatDifferenceCoeff (k + 1) *
        (((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) - ((((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))) =
        ∑' k : ℕ, (woldNatResidualAbelAtom s k +
          (xiHeatCassiniWoldLogHolonomyConstant : ℂ) * naturalCpowIncrement s k) := by
      apply tsum_congr
      intro k
      rw [coeffPartial_woldNatDifferenceCoeff, woldNatResidualAbelAtom, naturalCpowIncrement,
        naturalCpowKernel, naturalCpowKernel]
      push_cast
      ring_nf
    _ = (∑' k : ℕ, woldNatResidualAbelAtom s k) +
          ∑' k : ℕ, (xiHeatCassiniWoldLogHolonomyConstant : ℂ) * naturalCpowIncrement s k :=
      hA.tsum_add hCD
    _ = (∑' k : ℕ, woldNatResidualAbelAtom s k) + (xiHeatCassiniWoldLogHolonomyConstant : ℂ) := by
      rw [tsum_mul_left, tsum_naturalCpowKernel_sub_succ hs, mul_one]

theorem woldNatRegularContinuation_eq_woldLaplaceCurrent_of_squareEnergy_pos {t : ℝ} (ht : 0 < t)
    (hEnergy : WoldNatResidualSquareEnergy t) {s : ℂ} (hs : 0 < s.re) :
    woldNatRegularContinuation s = xiHeatCassiniWoldLaplaceCurrent s := by
  have h1 := abelDirichlet_woldNatDifferenceCoeff_eq_of_squareEnergy_pos ht hEnergy hs
  have h2 := abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh hs
  rw [woldNatRegularContinuation, integerLogMeshContinuation_eq_current hs]
  linear_combination h2 - h1

/-! ### Zeta-cleared identity on the sub-half sector -/

/-- The upper sector `-t < re s, 0 < im s`. -/
def woldSubhalfSector (t : ℝ) : Set ℂ := {s : ℂ | -t < s.re ∧ 0 < s.im}

theorem isOpen_woldSubhalfSector (t : ℝ) : IsOpen (woldSubhalfSector t) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem isPreconnected_woldSubhalfSector (t : ℝ) : IsPreconnected (woldSubhalfSector t) := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab
  have h1 := hx.1; have h2 := hy.1; have h3 := hx.2; have h4 := hy.2
  refine ⟨?_, ?_⟩
  · simp only [add_re, real_smul, Complex.re_ofReal_mul]
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2
    · have e1 := mul_pos h (show 0 < x.re + t by linarith)
      have e2 := mul_nonneg hb (show 0 ≤ y.re + t by linarith)
      have e3 : t * a + t * b = t := by rw [← mul_add, hab, mul_one]
      nlinarith [e1, e2, e3]
  · simp only [add_im, real_smul, Complex.im_ofReal_mul]
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h4
    · nlinarith [mul_pos h h3, mul_nonneg hb h4.le]

theorem woldSubhalfSector_subset {t : ℝ} (ht : t ≤ 1 / 2) :
    woldSubhalfSector t ⊆ xiHeatCassiniWoldResidualODESector 1 := by
  intro s hs
  change -(1 / 2 : ℝ) < s.re ∧ 0 < (1 : ℝ) * s.im
  exact ⟨by linarith [hs.1], by simpa using hs.2⟩

theorem analyticOnNhd_woldNatRegularContinuation_of_squareEnergy_subhalf {t : ℝ} (ht1 : t ≤ 1)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    AnalyticOnNhd ℂ woldNatRegularContinuation (woldSubhalfSector t) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_woldSubhalfSector t)
  intro s hs
  have hs0 : s ≠ 0 := fun h => by subst h; simp [woldSubhalfSector] at hs
  have hA := differentiableAt_woldNatResidualAbelCurrent_of_squareEnergy_rpow ht1 hEnergy hs.1
  have hL := differentiableAt_integerLogMeshContinuation (by linarith [hs.1] : -1 < s.re) hs0
  unfold woldNatRegularContinuation
  exact ((hA.add_const (xiHeatCassiniWoldLogHolonomyConstant : ℂ)).add hL).differentiableWithinAt

theorem xiHeatCassiniWoldZetaClearedContinuation_eq_mul_regular_subhalf {t : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1 / 2) (hEnergy : WoldNatResidualSquareEnergy t) :
    Set.EqOn xiHeatCassiniWoldZetaClearedContinuation
      (fun s : ℂ => riemannZeta (s + 1) * woldNatRegularContinuation s)
      (woldSubhalfSector t) := by
  have hsub := woldSubhalfSector_subset ht2
  have hL := analyticOnNhd_xiHeatCassiniWoldZetaClearedContinuation.mono hsub
  have hR : AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta (s + 1) * woldNatRegularContinuation s)
      (woldSubhalfSector t) :=
    ((analyticOnNhd_riemannZeta_add_one_residualODESector 1).mono hsub).mul
      (analyticOnNhd_woldNatRegularContinuation_of_squareEnergy_subhalf (by linarith) hEnergy)
  let q : ℂ := 1 + Complex.I
  have hq : q ∈ woldSubhalfSector t := by
    refine ⟨?_, ?_⟩ <;> simp [q]; linarith
  have hevent : xiHeatCassiniWoldZetaClearedContinuation =ᶠ[𝓝 q]
      (fun s : ℂ => riemannZeta (s + 1) * woldNatRegularContinuation s) := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp [q] : (0 : ℝ) < q.re)] with s hs
    have hz : riemannZeta (s + 1) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re]
      linarith [show (0 : ℝ) < s.re from hs]
    rw [xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical hz,
      xiHeatCassiniWoldCriticalLaplaceContinuation_eq (by linarith [show (0 : ℝ) < s.re from hs]),
      xiHeatCassiniWoldLaplaceContinuation_eq hs,
      woldNatRegularContinuation_eq_woldLaplaceCurrent_of_squareEnergy_pos ht hEnergy hs]
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR (isPreconnected_woldSubhalfSector t) hq hevent

/-! ### No zero beyond the energy abscissa -/

/-- Square energy at `0 < t ≤ 1/2` excludes every zero `ρ` with `re ρ > 1 - t` and `im ρ > 0`. -/
theorem riemannZeta_ne_zero_of_squareEnergy_subhalf {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hEnergy : WoldNatResidualSquareEnergy t) {rho : ℂ} (hre : 1 - t < rho.re)
    (him : 0 < rho.im) : riemannZeta rho ≠ 0 := by
  intro hzeta
  have hhalf : (1 / 2 : ℝ) ≤ rho.re := by linarith
  have hlt1 : rho.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hzeta
  obtain ⟨m, hm, hres⟩ := woldNatSingularAbelContinuation_zero_residue hhalf him.ne' hzeta
  set s0 : ℂ := rho - 1 with hs0
  have hs0mem : s0 ∈ woldSubhalfSector t := by
    refine ⟨?_, ?_⟩
    · simp only [hs0, sub_re, one_re]; linarith
    · simp only [hs0, sub_im, one_im, sub_zero]; exact him
  have hsectorEq := xiHeatCassiniWoldZetaClearedContinuation_eq_mul_regular_subhalf ht ht2 hEnergy
  have hzetaOff : ∀ᶠ z in 𝓝[≠] rho, riemannZeta z ≠ 0 :=
    eventually_riemannZeta_ne_zero_nhdsNE (by linarith) hlt1
  have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] s0) (𝓝[≠] rho) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun s : ℂ => s + 1) (𝓝 s0) (𝓝 (s0 + 1)) :=
        (continuous_id.add continuous_const).tendsto s0
      rw [hs0, sub_add_cancel] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      apply hs
      rw [hs0]
      linear_combination h
  have hzetaShift : ∀ᶠ s in 𝓝[≠] s0, riemannZeta (s + 1) ≠ 0 := hshift.eventually hzetaOff
  have hmem : ∀ᶠ s in 𝓝[≠] s0, s ∈ woldSubhalfSector t :=
    nhdsWithin_le_nhds ((isOpen_woldSubhalfSector t).mem_nhds hs0mem)
  have heq : ∀ᶠ s in 𝓝[≠] s0, woldNatSingularAbelContinuation s =
      woldNatResidualAbelCurrent s + (xiHeatCassiniWoldLogHolonomyConstant : ℂ) := by
    filter_upwards [hzetaShift, hmem] with s hz hs
    have hc := xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical hz
    have hr := hsectorEq hs
    have hcrit : xiHeatCassiniWoldCriticalLaplaceContinuation s = woldNatRegularContinuation s :=
      mul_left_cancel₀ hz (hc.symm.trans hr)
    rw [woldNatSingularAbelContinuation, hcrit, woldNatRegularContinuation]
    ring
  have hcurrent : ContinuousAt woldNatResidualAbelCurrent s0 :=
    (differentiableAt_woldNatResidualAbelCurrent_of_squareEnergy_rpow (by linarith) hEnergy
      hs0mem.1).continuousAt
  have hzero : Tendsto (fun s : ℂ => (s - s0) *
      (woldNatResidualAbelCurrent s + (xiHeatCassiniWoldLogHolonomyConstant : ℂ)))
      (𝓝[≠] s0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ => s - s0) (𝓝 s0) (𝓝 0) := by
      rw [← sub_self s0]
      exact tendsto_id.sub tendsto_const_nhds
    have h2 := (hcurrent.add_const (xiHeatCassiniWoldLogHolonomyConstant : ℂ)).tendsto
    simpa only [zero_mul] using (h1.mul h2).mono_left nhdsWithin_le_nhds
  have hres' : Tendsto (fun s : ℂ => (s - s0) *
      (woldNatResidualAbelCurrent s + (xiHeatCassiniWoldLogHolonomyConstant : ℂ)))
      (𝓝[≠] s0) (𝓝 (-(m : ℂ))) :=
    hres.congr' (heq.mono fun s hs => by rw [hs])
  have hm0 : -(m : ℂ) = 0 := tendsto_nhds_unique hres' hzero
  have : (m : ℂ) = 0 := neg_eq_zero.mp hm0
  have : m = 0 := by exact_mod_cast this
  omega

/-! ### The equivalence -/

/-- Square energy below one half for every radius forces RH. -/
theorem riemannHypothesis_of_forall_woldNatResidualSquareEnergy_lt_half
    (h : ∀ t : ℝ, 0 < t → t < 1 / 2 → WoldNatResidualSquareEnergy t) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_woldNatSingularAbelContinuation_strictRight_regular]
  intro rho hhalf him
  rw [differentiableAt_woldNatSingularAbelContinuation_iff hhalf.le him]
  have key : ∀ w : ℂ, 1 / 2 < w.re → 0 < w.im → riemannZeta w ≠ 0 := by
    intro w hw hwim hzw
    have hw1 : w.re < 1 := by
      by_contra hc
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hzw
    let t : ℝ := (3 / 2 - w.re) / 2
    exact riemannZeta_ne_zero_of_squareEnergy_subhalf (t := t) (by dsimp only [t]; linarith)
      (by dsimp only [t]; linarith) (h t (by dsimp only [t]; linarith) (by dsimp only [t]; linarith))
      (by dsimp only [t]; linarith) hwim hzw
  rcases lt_or_gt_of_ne him with hneg | hpos
  · intro hz
    have hc : riemannZeta (starRingEnd ℂ rho) = 0 := by rw [riemannZeta_conj, hz, map_zero]
    exact key (starRingEnd ℂ rho) (by simpa using hhalf) (by simpa using hneg) hc
  · exact key rho hhalf hpos

/-- Under RH the square energy is finite at every radius below one half. -/
theorem woldNatResidualSquareEnergy_of_riemannHypothesis (hRH : RiemannHypothesis) {t : ℝ}
    (ht0 : 0 < t) (ht : t < 1 / 2) : WoldNatResidualSquareEnergy t := by
  obtain ⟨B, hB, hrate⟩ :=
    riemannHypothesis_iff_woldNatResidualAllStrictHalfPowerRate.mp hRH ((1 / 2 - t) / 2)
      (by linarith) (by linarith)
  have hmaj : Summable (fun N : ℕ => B ^ 2 * (N : ℝ) ^ (t - 3 / 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hR2 : |R N| ^ 2 ≤ (B * (N : ℝ) ^ (-(1 / 2 - (1 / 2 - t) / 2))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hN 2
  calc (N : ℝ) ^ (2 * t - 1) * |R N| ^ 2
      ≤ (N : ℝ) ^ (2 * t - 1) * (B * (N : ℝ) ^ (-(1 / 2 - (1 / 2 - t) / 2))) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by positivity)
    _ = B ^ 2 * (N : ℝ) ^ (t - 3 / 2) := by
        rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ _), ← Real.rpow_mul hNpos.le]
        rw [mul_comm, mul_assoc, ← Real.rpow_add hNpos]
        congr 2
        push_cast
        ring

/-- **RH is exactly finiteness of the natural Wold square energy below one half.** -/
theorem riemannHypothesis_iff_forall_woldNatResidualSquareEnergy_lt_half :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 → WoldNatResidualSquareEnergy t :=
  ⟨fun hRH _ ht0 ht => woldNatResidualSquareEnergy_of_riemannHypothesis hRH ht0 ht,
    riemannHypothesis_of_forall_woldNatResidualSquareEnergy_lt_half⟩

end
end RHTower
