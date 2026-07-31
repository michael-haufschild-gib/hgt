import Mathlib
import GaloisForLFunctions.RHTower.TrivialZeroFirstDerivative
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation

/-!
# The terminal moving pole of the bounded-exponent Euler multiplier

The depth-`M` Euler multiplier of the positive dilation operator supported on integers whose
prime exponents are at most `M` is

`A_M(s) = ζ(s) / ζ((M+1) s)`.

Its denominator drags the first trivial zero of `ζ` to the point

`s_M = -2 / (M + 1) ∈ [-1, 0)`,

where the numerator does not vanish, because `ζ` has no zero on `[-1, 0)`.  Every finite depth
therefore carries a genuine simple pole, with residue

`Res_{s_M} A_M = ζ(s_M) / ((M+1) ζ'(-2))`.

As the depth grows the pole travels to the boundary `s = 0` and its residue tends to zero, but
the depth-normalized boundary record is nonzero:

`(M+1) Res_{s_M} A_M → ζ(0)/ζ'(-2) = 2π²/ζ(3)`,   `Res_{s_M} A_M / |s_M| → π²/ζ(3)`.
-/

open Complex Filter Topology

namespace RHTower

/-- Terminal pole of the depth-`M` bounded-exponent Euler multiplier. -/
noncomputable def movingPolePoint (M : ℕ) : ℂ := -2 / ((M : ℂ) + 1)

/-- Residue of the depth-`M` multiplier at its terminal pole. -/
noncomputable def movingPoleResidue (M : ℕ) : ℂ :=
  riemannZeta (movingPolePoint M) / (((M : ℂ) + 1) * deriv riemannZeta (-2))

theorem natCastAddOne_ne_zero (M : ℕ) : ((M : ℂ) + 1) ≠ 0 := by
  have h : ((M : ℂ) + 1) = ((M + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h]
  exact_mod_cast Nat.succ_ne_zero M

theorem movingPolePoint_eq_ofReal (M : ℕ) :
    movingPolePoint M = ((-2 / ((M : ℝ) + 1) : ℝ) : ℂ) := by
  rw [movingPolePoint]
  push_cast
  ring

theorem movingPolePoint_real_neg (M : ℕ) : (-2 / ((M : ℝ) + 1)) < 0 := by
  have hd : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) hd

theorem neg_one_le_movingPolePoint_real {M : ℕ} (hM : 1 ≤ M) :
    (-1 : ℝ) ≤ -2 / ((M : ℝ) + 1) := by
  have hd : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  rw [le_div_iff₀ hd]
  nlinarith

/-- The travelling pole is never the pole of `ζ` itself. -/
theorem movingPolePoint_ne_one (M : ℕ) : movingPolePoint M ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [movingPolePoint_eq_ofReal] at hre
  simp only [Complex.ofReal_re, Complex.one_re] at hre
  have := movingPolePoint_real_neg M
  linarith

/-- The numerator does not vanish at the travelling pole. -/
theorem riemannZeta_movingPolePoint_ne_zero {M : ℕ} (hM : 1 ≤ M) :
    riemannZeta (movingPolePoint M) ≠ 0 := by
  rw [movingPolePoint_eq_ofReal]
  exact riemannZeta_ne_zero_of_neg_one_le_of_lt_zero
    (neg_one_le_movingPolePoint_real hM) (movingPolePoint_real_neg M)

/-- The depth dilation sends the travelling pole exactly to the first trivial zero. -/
theorem succ_mul_movingPolePoint (M : ℕ) : ((M : ℂ) + 1) * movingPolePoint M = -2 := by
  rw [movingPolePoint]
  field_simp

theorem norm_movingPolePoint (M : ℕ) : ‖movingPolePoint M‖ = 2 / ((M : ℝ) + 1) := by
  have hd : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [movingPolePoint_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg hd.le]
  norm_num

theorem boundedExponentEulerSource_succ (M : ℕ) (s : ℂ) :
    boundedExponentEulerSource (M + 1) s = riemannZeta s / riemannZeta (((M : ℂ) + 1) * s) := by
  rw [boundedExponentEulerSource]
  push_cast
  ring_nf

/-- The dilated zeta denominator has a nonzero derivative at the travelling pole. -/
theorem hasDerivAt_zeta_depthDilation (M : ℕ) :
    HasDerivAt (fun s : ℂ => riemannZeta (((M : ℂ) + 1) * s))
      (deriv riemannZeta (-2) * ((M : ℂ) + 1)) (movingPolePoint M) := by
  have hinner : HasDerivAt (fun s : ℂ => ((M : ℂ) + 1) * s) ((M : ℂ) + 1)
      (movingPolePoint M) := by
    simpa using (hasDerivAt_id (movingPolePoint M)).const_mul ((M : ℂ) + 1)
  have houter : HasDerivAt riemannZeta (deriv riemannZeta (-2))
      (((M : ℂ) + 1) * movingPolePoint M) := by
    rw [succ_mul_movingPolePoint]
    exact (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
  exact houter.comp (movingPolePoint M) hinner

theorem deriv_zeta_depthDilation_ne_zero (M : ℕ) :
    deriv riemannZeta (-2) * ((M : ℂ) + 1) ≠ 0 :=
  mul_ne_zero deriv_riemannZeta_neg_two_ne_zero (natCastAddOne_ne_zero M)

/-- **Forced moving pole with explicit residue.**  For every finite depth the multiplier
`A_M` has a simple pole at `s_M`, with residue `ζ(s_M) / ((M+1) ζ'(-2))`. -/
theorem tendsto_movingPole_residue (M : ℕ) :
    Tendsto (fun s : ℂ => (s - movingPolePoint M) * boundedExponentEulerSource (M + 1) s)
      (𝓝[≠] (movingPolePoint M)) (𝓝 (movingPoleResidue M)) := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_zeta_depthDilation M)
  have hinv := hslope.inv₀ (deriv_zeta_depthDilation_ne_zero M)
  have hzc : Tendsto riemannZeta (𝓝[≠] (movingPolePoint M))
      (𝓝 (riemannZeta (movingPolePoint M))) :=
    ((differentiableAt_riemannZeta (movingPolePoint_ne_one M)).continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim := hzc.mul hinv
  have hval : riemannZeta (movingPolePoint M) * (deriv riemannZeta (-2) * ((M : ℂ) + 1))⁻¹
      = movingPoleResidue M := by
    rw [movingPoleResidue]
    ring
  rw [← hval]
  refine Tendsto.congr (fun s => ?_) hlim
  simp only [slope_def_field, succ_mul_movingPolePoint, riemannZeta_neg_two, sub_zero,
    boundedExponentEulerSource_succ, inv_div]
  ring

theorem movingPoleResidue_ne_zero {M : ℕ} (hM : 1 ≤ M) : movingPoleResidue M ≠ 0 := by
  rw [movingPoleResidue]
  exact div_ne_zero (riemannZeta_movingPolePoint_ne_zero hM)
    (mul_ne_zero (natCastAddOne_ne_zero M) deriv_riemannZeta_neg_two_ne_zero)

/-- The travelling singularity is a genuine pole: the multiplier blows up there. -/
theorem tendsto_norm_boundedExponentEulerSource_atTop {M : ℕ} (hM : 1 ≤ M) :
    Tendsto (fun s : ℂ => ‖boundedExponentEulerSource (M + 1) s‖)
      (𝓝[≠] (movingPolePoint M)) atTop := by
  set a : ℂ := movingPolePoint M with ha
  have hres : Tendsto (fun s : ℂ => ‖(s - a) * boundedExponentEulerSource (M + 1) s‖)
      (𝓝[≠] a) (𝓝 ‖movingPoleResidue M‖) :=
    (tendsto_movingPole_residue M).norm
  have hsub : Tendsto (fun s : ℂ => s - a) (𝓝[≠] a) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ => s - a) a := continuousAt_id.sub continuousAt_const
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun s : ℂ => ‖s - a‖) (𝓝[≠] a) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using hsub.norm, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hs)
  have hinv : Tendsto (fun s : ℂ => ‖s - a‖⁻¹) (𝓝[≠] a) atTop :=
    tendsto_inv_nhdsGT_zero.comp hnorm
  have hprod := Filter.Tendsto.atTop_mul_pos
    (norm_pos_iff.mpr (movingPoleResidue_ne_zero hM)) hinv hres
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : ‖s - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs)
  rw [norm_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The multiplier is analytic away from the travelling pole and the zeta pole. -/
theorem analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  analyticOn_riemannZeta s (by simpa using hs)

/-- **The travelling singularity is a simple pole.** -/
theorem meromorphicOrderAt_boundedExponentEulerSource {M : ℕ} (hM : 1 ≤ M) :
    meromorphicOrderAt (boundedExponentEulerSource (M + 1)) (movingPolePoint M) = -1 := by
  set a : ℂ := movingPolePoint M with ha
  have hnum : AnalyticAt ℂ riemannZeta a := analyticAt_riemannZeta_of_ne_one (movingPolePoint_ne_one M)
  have hden : AnalyticAt ℂ (fun s : ℂ => riemannZeta (((M : ℂ) + 1) * s)) a := by
    have h1 : AnalyticAt ℂ riemannZeta (((M : ℂ) + 1) * a) := by
      rw [ha, succ_mul_movingPolePoint]
      exact analyticAt_riemannZeta_of_ne_one (by norm_num)
    have h2 : AnalyticAt ℂ (fun s : ℂ => ((M : ℂ) + 1) * s) a :=
      (analyticAt_const).mul analyticAt_id
    exact h1.comp h2
  have hnumOrder : analyticOrderAt riemannZeta a = 0 :=
    hnum.analyticOrderAt_eq_zero.mpr (riemannZeta_movingPolePoint_ne_zero hM)
  have hdenVal : (fun s : ℂ => riemannZeta (((M : ℂ) + 1) * s)) a = 0 := by
    simp only [ha, succ_mul_movingPolePoint, riemannZeta_neg_two]
  have hdenDeriv : deriv (fun s : ℂ => riemannZeta (((M : ℂ) + 1) * s)) a ≠ 0 := by
    rw [(hasDerivAt_zeta_depthDilation M).deriv]
    exact deriv_zeta_depthDilation_ne_zero M
  have hdenOrder : analyticOrderAt (fun s : ℂ => riemannZeta (((M : ℂ) + 1) * s)) a = 1 :=
    hden.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hdenVal hdenDeriv
  have hfun : boundedExponentEulerSource (M + 1)
      = riemannZeta / (fun s : ℂ => riemannZeta (((M : ℂ) + 1) * s)) := by
    funext s
    rw [Pi.div_apply, boundedExponentEulerSource_succ]
  rw [hfun, meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
    hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq, hnumOrder, hdenOrder]
  rfl

/-! ## Boundary flux of the escaping pole -/

theorem tendsto_movingPolePoint_zero : Tendsto movingPolePoint atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_movingPolePoint]
  have h : Tendsto (fun M : ℕ => (2 : ℝ) * (1 / ((M : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
  rw [mul_zero] at h
  exact Tendsto.congr (fun M => by ring) h

theorem tendsto_riemannZeta_movingPolePoint :
    Tendsto (fun M : ℕ => riemannZeta (movingPolePoint M)) atTop (𝓝 (-1 / 2)) := by
  have hc : ContinuousAt riemannZeta 0 := (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have h := hc.tendsto.comp tendsto_movingPolePoint_zero
  rw [riemannZeta_zero] at h
  exact h

/-- **Nonzero boundary flux.**  The depth-normalized residue converges to `ζ(0)/ζ'(-2)`,
which equals `2π²/ζ(3)`. -/
theorem tendsto_succ_mul_movingPoleResidue :
    Tendsto (fun M : ℕ => ((M : ℂ) + 1) * movingPoleResidue M) atTop
      (𝓝 (2 * (Real.pi : ℂ) ^ 2 / riemannZeta 3)) := by
  have hz3 : riemannZeta 3 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  have hk : ∀ M : ℕ, ((M : ℂ) + 1) * movingPoleResidue M
      = riemannZeta (movingPolePoint M) / deriv riemannZeta (-2) := by
    intro M
    rw [movingPoleResidue]
    field_simp
  simp only [hk]
  have hlim := tendsto_riemannZeta_movingPolePoint.div_const (deriv riemannZeta (-2))
  have hvalue : 2 * (Real.pi : ℂ) ^ 2 / riemannZeta 3
      = (-1 / 2) / deriv riemannZeta (-2) := by
    rw [deriv_riemannZeta_neg_two]
    field_simp
    ring
  rw [hvalue]
  exact hlim

/-- **Residue against pole distance.**  The residue divided by the distance from the boundary
converges to `π²/ζ(3)`. -/
theorem tendsto_movingPoleResidue_div_dist :
    Tendsto (fun M : ℕ => movingPoleResidue M / ((‖movingPolePoint M‖ : ℝ) : ℂ)) atTop
      (𝓝 ((Real.pi : ℂ) ^ 2 / riemannZeta 3)) := by
  have hz3 : riemannZeta 3 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  have hk : ∀ M : ℕ, movingPoleResidue M / ((‖movingPolePoint M‖ : ℝ) : ℂ)
      = riemannZeta (movingPolePoint M) / (2 * deriv riemannZeta (-2)) := by
    intro M
    rw [movingPoleResidue, norm_movingPolePoint]
    have hk1 : ((M : ℂ) + 1) ≠ 0 := natCastAddOne_ne_zero M
    push_cast
    field_simp
  simp only [hk]
  have hlim := tendsto_riemannZeta_movingPolePoint.div_const (2 * deriv riemannZeta (-2))
  have hvalue : (Real.pi : ℂ) ^ 2 / riemannZeta 3
      = (-1 / 2) / (2 * deriv riemannZeta (-2)) := by
    rw [deriv_riemannZeta_neg_two]
    field_simp
    ring
  rw [hvalue]
  exact hlim

end RHTower
