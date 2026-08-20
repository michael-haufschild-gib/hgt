import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.XiRectangleZeroCount
import Mathlib

/-!
# Prime-log action condensation in the exponent normal cone

The reciprocal-zeta depth tower `B_m(s) = 1/ζ(ms)` has increments `H_m = B_{m+1} - B_m` carrying the
squarefree action spectrum: on the half-plane of absolute convergence

`H_m(s) = ∑_{n ≥ 2} μ(n)(n^{-s} - 1) n^{-ms}`,

and asymptotic deflation recovers every coefficient — no finite leading-action truncation is the
complete source.  Under the diagonal normal blow-up `s = u/(m+1)` all actions condense
simultaneously: the normalized increment converges to the Euler logarithmic connection
`-u ζ'(u)/ζ(u)`.

The mechanism is universal: for any germ holomorphic and nonvanishing at `u`,

`(1/ε)(1 - F(u)/F((1-ε)u)) → -u F'(u)/F(u)`,

which for the completed `ξ` is the completed depth connection, with residue `-dρ` at a divisor
point of multiplicity `d`.

The tail estimate behind the extraction theorem is elementary: beyond `N` every ratio power is
dominated by a geometric factor times an inverse square.
-/

set_option maxHeartbeats 1600000

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The universal analytic normal-cone law -/

/-- The normalized depth-connection quotient of a germ at `u` under the diagonal blow-up
`s = ε u`. -/
def normalConeQuotient (F : ℂ → ℂ) (u eps : ℂ) : ℂ :=
  (1 - F u / F ((1 - eps) * u)) / eps

/-- **`(15)`: the universal analytic normal-cone law.**  For any germ holomorphic and nonvanishing
at `u`, the normalized depth quotient converges to the negative logarithmic connection
`-u F'(u)/F(u)`. -/
theorem tendsto_normalConeQuotient {F : ℂ → ℂ} {u : ℂ}
    (hF : DifferentiableAt ℂ F u) (hne : F u ≠ 0) :
    Tendsto (fun eps : ℂ => normalConeQuotient F u eps) (𝓝[≠] (0 : ℂ))
      (𝓝 (-(u * (deriv F u / F u)))) := by
  set g : ℂ → ℂ := fun eps : ℂ => F ((1 - eps) * u) with hg
  have hinner : HasDerivAt (fun eps : ℂ => (1 - eps) * u) (-u) 0 := by
    have h : HasDerivAt (fun eps : ℂ => (1 - eps)) (-1 : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_sub 1)
    have h2 := h.mul_const u
    simpa using h2
  have hg0 : g 0 = F u := by
    rw [hg]
    norm_num
  have hgderiv : HasDerivAt g (-u * deriv F u) 0 := by
    have hFu : HasDerivAt F (deriv F u) ((1 - (0 : ℂ)) * u) := by
      have hval : (1 - (0 : ℂ)) * u = u := by ring
      rw [hval]
      exact hF.hasDerivAt
    have hcomp := hFu.comp 0 hinner
    rw [hg]
    refine hcomp.congr_deriv ?_
    ring
  have hslope : Tendsto (fun eps : ℂ => (g eps - g 0) / eps) (𝓝[≠] (0 : ℂ))
      (𝓝 (-u * deriv F u)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hgderiv
    refine h.congr fun eps => ?_
    rw [slope_def_field, sub_zero]
  have hgcont : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (F u)) := by
    have hc : ContinuousAt g 0 := hgderiv.continuousAt
    have h2 : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
      hc.continuousWithinAt.tendsto
    rwa [hg0] at h2
  have hginv : Tendsto (fun eps : ℂ => (g eps)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 (F u)⁻¹) :=
    hgcont.inv₀ hne
  have hprod := hslope.mul hginv
  have hval : (-u * deriv F u) * (F u)⁻¹ = -(u * (deriv F u / F u)) := by
    field_simp
  rw [hval] at hprod
  refine hprod.congr' ?_
  have hgne : ∀ᶠ eps : ℂ in 𝓝[≠] (0 : ℂ), g eps ≠ 0 := by
    have hc : ContinuousAt g 0 := hgderiv.continuousAt
    have hev : ∀ᶠ eps : ℂ in 𝓝 (0 : ℂ), g eps ≠ 0 := by
      have hcv : Tendsto g (𝓝 (0 : ℂ)) (𝓝 (F u)) := by
        have := hc.tendsto
        rwa [hg0] at this
      exact hcv.eventually_ne hne
    exact hev.filter_mono nhdsWithin_le_nhds
  filter_upwards [hgne, self_mem_nhdsWithin] with eps hgeps heps
  have heps0 : eps ≠ 0 := heps
  have hgval : F ((1 - eps) * u) = g eps := rfl
  rw [normalConeQuotient, hg0, hgval]
  field_simp

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

/-- The depth-`m` reciprocal-zeta carrier `B_m(s) = 1/ζ(ms)`. -/
def depthReciprocalZeta (m : ℕ) (s : ℂ) : ℂ := (riemannZeta ((m : ℂ) * s))⁻¹

/-- The depth increment `H_m(s) = B_{m+1}(s) - B_m(s)`. -/
def depthReciprocalZetaIncrement (m : ℕ) (s : ℂ) : ℂ :=
  depthReciprocalZeta (m + 1) s - depthReciprocalZeta m s

/-- The squarefree action coefficient `c_n(s) = μ(n)(n^{-s} - 1)`. -/
def squarefreeActionCoefficient (s : ℂ) (n : ℕ) : ℂ :=
  (moebius n : ℂ) * ((n : ℂ) ^ (-s) - 1)

/-- **`(2)`: the exact action expansion of the depth increment.**  On the half-plane where the
`m`-fold dilate converges absolutely, the depth increment is the Dirichlet series of the
squarefree action coefficients along the dilated ray. -/
theorem hasSum_depthReciprocalZetaIncrement {m : ℕ} {s : ℂ}
    (hm : 1 < ((m : ℂ) * s).re) (hm1 : 1 < (((m : ℂ) + 1) * s).re) :
    HasSum (fun n : ℕ => squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s)))
      (depthReciprocalZetaIncrement m s) := by
  have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hB1 : depthReciprocalZeta (m + 1) s
      = LSeries (fun n => (moebius n : ℂ)) (((m : ℂ) + 1) * s) := by
    rw [depthReciprocalZeta, hcast, LSeries_moebius_eq_inv_riemannZeta hm1]
  have hB0 : depthReciprocalZeta m s
      = LSeries (fun n => (moebius n : ℂ)) ((m : ℂ) * s) := by
    rw [depthReciprocalZeta, LSeries_moebius_eq_inv_riemannZeta hm]
  have hs1 : LSeriesSummable (fun n => (moebius n : ℂ)) (((m : ℂ) + 1) * s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hm1
  have hs0 : LSeriesSummable (fun n => (moebius n : ℂ)) ((m : ℂ) * s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hm
  have hsub := hs1.hasSum.sub hs0.hasSum
  rw [depthReciprocalZetaIncrement, hB1, hB0]
  refine hsub.congr_fun ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [LSeries.term_zero, LSeries.term_zero, squarefreeActionCoefficient]
    simp
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [LSeries.term_of_ne_zero (by omega : n ≠ 0),
      LSeries.term_of_ne_zero (by omega : n ≠ 0), squarefreeActionCoefficient]
    have hsplit : (n : ℂ) ^ (((m : ℂ) + 1) * s) = (n : ℂ) ^ ((m : ℂ) * s) * (n : ℂ) ^ s := by
      rw [← Complex.cpow_add _ _ hn0]
      congr 1
      ring
    have hneg : (n : ℂ) ^ (-((m : ℂ) * s)) = ((n : ℂ) ^ ((m : ℂ) * s))⁻¹ :=
      Complex.cpow_neg _ _
    have hnegs : (n : ℂ) ^ (-s) = ((n : ℂ) ^ s)⁻¹ := Complex.cpow_neg _ _
    have hne1 : (n : ℂ) ^ ((m : ℂ) * s) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      tauto
    have hne2 : (n : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      tauto
    rw [hsplit, hneg, hnegs]
    field_simp

theorem depthReciprocalZetaIncrement_eq_tsum {m : ℕ} {s : ℂ}
    (hm : 1 < ((m : ℂ) * s).re) (hm1 : 1 < (((m : ℂ) + 1) * s).re) :
    depthReciprocalZetaIncrement m s
      = ∑' n : ℕ, squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s)) :=
  (hasSum_depthReciprocalZetaIncrement hm hm1).tsum_eq.symm

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

/-- The diagonal normal blow-up scale `ε_m = 1/(m+1)`. -/
def blowUpScale (m : ℕ) : ℂ := ((m : ℂ) + 1)⁻¹

theorem blowUpScale_ne_zero (m : ℕ) : blowUpScale m ≠ 0 := by
  rw [blowUpScale]
  refine inv_ne_zero ?_
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  intro h
  apply this
  exact_mod_cast congrArg Complex.re h

theorem tendsto_blowUpScale : Tendsto blowUpScale atTop (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hreal : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      have h : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
        Filter.tendsto_atTop_add_const_right _ 1 h
      exact h1.inv_tendsto_atTop
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    rw [Complex.ofReal_zero] at hc
    refine hc.congr fun m => ?_
    rw [Function.comp_apply, blowUpScale]
    push_cast
    ring
  · exact Eventually.of_forall fun m => blowUpScale_ne_zero m

/-- `(12)`: at the blow-up scale the upper carrier is the undilated reciprocal zeta. -/
theorem depthReciprocalZeta_succ_blowUp (m : ℕ) (u : ℂ) :
    depthReciprocalZeta (m + 1) (blowUpScale m * u) = (riemannZeta u)⁻¹ := by
  rw [depthReciprocalZeta, blowUpScale]
  congr 2
  have hm : ((m : ℂ) + 1) ≠ 0 := by
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    intro h
    apply this
    exact_mod_cast congrArg Complex.re h
  push_cast
  field_simp

/-- `(12)`: at the blow-up scale the lower carrier is the shrunken reciprocal zeta. -/
theorem depthReciprocalZeta_blowUp (m : ℕ) (u : ℂ) :
    depthReciprocalZeta m (blowUpScale m * u)
      = (riemannZeta ((1 - blowUpScale m) * u))⁻¹ := by
  rw [depthReciprocalZeta, blowUpScale]
  congr 2
  have hm : ((m : ℂ) + 1) ≠ 0 := by
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    intro h
    apply this
    exact_mod_cast congrArg Complex.re h
  field_simp
  ring

/-- **`(13)`: the Euler logarithmic connection is the normalized condensation current.**  The
normalized depth increment of the reciprocal-zeta tower at the diagonal blow-up converges to
`-u ζ'(u)/ζ(u)`. -/
theorem tendsto_depthNormalizedIncrement_riemannZeta {u : ℂ} (hu : 1 < u.re) :
    Tendsto (fun m : ℕ =>
        (depthReciprocalZetaIncrement m (blowUpScale m * u)
          / depthReciprocalZeta (m + 1) (blowUpScale m * u)) / blowUpScale m)
      atTop (𝓝 (-(u * (deriv riemannZeta u / riemannZeta u)))) := by
  have hzeta : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hu)
  have hu1 : u ≠ 1 := by
    intro h
    rw [h] at hu
    simp at hu
  have hdiff : DifferentiableAt ℂ riemannZeta u := differentiableAt_riemannZeta hu1
  have hmain := tendsto_normalConeQuotient hdiff hzeta
  have hcomp := hmain.comp tendsto_blowUpScale
  refine hcomp.congr fun m => ?_
  rw [Function.comp_apply, normalConeQuotient, depthReciprocalZetaIncrement,
    depthReciprocalZeta_succ_blowUp, depthReciprocalZeta_blowUp]
  by_cases hz : riemannZeta ((1 - blowUpScale m) * u) = 0
  · rw [hz, div_zero, sub_zero, inv_zero, sub_zero, div_self (inv_ne_zero hzeta)]
  · field_simp

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

/-- **`(11)`: the unnormalized condensation limit.**  The depth increment at the blow-up scale,
divided by the scale, converges to `u (1/ζ)'(u) = -u ζ'(u)/ζ(u)²`. -/
theorem tendsto_depthIncrement_blowUp_riemannZeta {u : ℂ} (hu : 1 < u.re) :
    Tendsto (fun m : ℕ => depthReciprocalZetaIncrement m (blowUpScale m * u) / blowUpScale m)
      atTop (𝓝 (-(u * deriv riemannZeta u / (riemannZeta u) ^ 2))) := by
  have hzeta : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hu)
  have hmain := tendsto_depthNormalizedIncrement_riemannZeta hu
  have hscale := hmain.const_mul ((riemannZeta u)⁻¹)
  have hval : (riemannZeta u)⁻¹ * -(u * (deriv riemannZeta u / riemannZeta u))
      = -(u * deriv riemannZeta u / (riemannZeta u) ^ 2) := by
    field_simp
  rw [hval] at hscale
  refine hscale.congr fun m => ?_
  rw [depthReciprocalZeta_succ_blowUp] at *
  by_cases hz : depthReciprocalZetaIncrement m (blowUpScale m * u) = 0
  · rw [hz]
    simp
  · field_simp

/-- **`(17)`: the completed depth connection.**  On the safe locus the same normal-cone law gives
the completed logarithmic connection `-u ξ'(u)/ξ(u)`. -/
theorem tendsto_normalConeQuotient_xi {u : ℂ} (hxi : xi u ≠ 0) :
    Tendsto (fun eps : ℂ => normalConeQuotient xi u eps) (𝓝[≠] (0 : ℂ))
      (𝓝 (-(u * (deriv xi u / xi u)))) :=
  tendsto_normalConeQuotient (xi_analyticOnNhd_univ u (Set.mem_univ u)).differentiableAt hxi

/-- **`(18)`: the depth connection has residue `-dρ` at a divisor point of multiplicity `d`.** -/
theorem residue_depthConnection_xi (rho : ℂ) :
    residue (fun u : ℂ => -(u * logDeriv xi u)) rho
      = -(rho * (((analyticOrderAt xi rho).toNat : ℤ) : ℂ)) := by
  have hxi : AnalyticAt ℂ xi rho := xi_analyticOnNhd_univ rho (Set.mem_univ rho)
  have horder : meromorphicOrderAt xi rho = (((analyticOrderAt xi rho).toNat : ℤ)) := by
    rw [hxi.meromorphicOrderAt_eq, ← ENat.coe_toNat (xi_orderAt_ne_top rho)]
    rfl
  have hres := GaloisForLFunctions.HTGeometry.logDeriv_residue_of_meromorphicOrder
    hxi.meromorphicAt horder
  have hlin : Tendsto (fun u : ℂ => -u) (𝓝[≠] rho) (𝓝 (-rho)) := by
    exact (continuous_neg.tendsto rho).mono_left nhdsWithin_le_nhds
  have hprod := hlin.mul hres
  have hval : (-rho) * (((analyticOrderAt xi rho).toNat : ℤ) : ℂ)
      = -(rho * (((analyticOrderAt xi rho).toNat : ℤ) : ℂ)) := by ring
  rw [hval] at hprod
  refine residue_eq_of_tendsto ?_
  refine hprod.congr fun u => ?_
  ring

end

end RHTower

namespace RHTower


noncomputable section

/-! ## A uniform tail estimate for ratio powers -/

/-- The inverse-square mass of the positive integers. -/
def inverseSquareMass : ℝ := ∑' n : ℕ, (if n = 0 then 0 else ((n : ℝ) ^ 2)⁻¹)

theorem summable_inverseSquare :
    Summable fun n : ℕ => (if n = 0 then 0 else ((n : ℝ) ^ 2)⁻¹) := by
  have hbase : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
    simp only [← one_div]
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine hbase.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · positivity
  · split_ifs with h
    · positivity
    · exact le_rfl

theorem inverseSquareMass_nonneg : 0 ≤ inverseSquareMass := by
  rw [inverseSquareMass]
  refine tsum_nonneg fun n => ?_
  split_ifs with h
  · exact le_rfl
  · positivity

/-- Every ratio power beyond `N` is dominated by a geometric factor times an inverse square. -/
theorem ratioPow_le {N n : ℕ} (hN : 1 ≤ N) (hn : N < n) {a : ℝ} (ha : 2 ≤ a) :
    ((N : ℝ) / n) ^ a
      ≤ ((N : ℝ) / (N + 1)) ^ (a - 2) * ((N : ℝ) ^ 2 * ((n : ℝ) ^ 2)⁻¹) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := lt_of_le_of_lt (Nat.zero_le N) hn
    exact_mod_cast this
  have hNn : (N : ℝ) + 1 ≤ (n : ℝ) := by
    have : N + 1 ≤ n := hn
    exact_mod_cast this
  have hratio0 : (0 : ℝ) < (N : ℝ) / n := by positivity
  have hratio_le : (N : ℝ) / n ≤ (N : ℝ) / (N + 1) := by
    refine div_le_div_of_nonneg_left hN0.le (by positivity) hNn
  have hsplit : ((N : ℝ) / n) ^ a = ((N : ℝ) / n) ^ (a - 2) * ((N : ℝ) / n) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hratio0]
    congr 1
    ring
  have hfirst : ((N : ℝ) / n) ^ (a - 2) ≤ ((N : ℝ) / (N + 1)) ^ (a - 2) :=
    Real.rpow_le_rpow hratio0.le hratio_le (by linarith)
  have hsecond : ((N : ℝ) / n) ^ (2 : ℝ) = (N : ℝ) ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_two, div_pow]
    ring
  rw [hsplit, hsecond]
  refine mul_le_mul_of_nonneg_right hfirst ?_
  positivity

theorem summable_ratioPow {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 2 ≤ a) :
    Summable fun n : ℕ => (if N < n then ((N : ℝ) / n) ^ a else 0) := by
  have hdom : Summable fun n : ℕ =>
      ((N : ℝ) / (N + 1)) ^ (a - 2) * ((N : ℝ) ^ 2 * (if n = 0 then 0 else ((n : ℝ) ^ 2)⁻¹)) := by
    exact ((summable_inverseSquare.mul_left ((N : ℝ) ^ 2)).mul_left _)
  refine hdom.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · by_cases h : N < n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  · by_cases h : N < n
    · rw [if_pos h]
      have hn0 : n ≠ 0 := by omega
      rw [if_neg hn0]
      exact ratioPow_le hN h ha
    · rw [if_neg h]
      by_cases h2 : n = 0
      · rw [if_pos h2]
        norm_num
      · rw [if_neg h2]
        positivity

theorem tsum_ratioPow_le {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 2 ≤ a) :
    ∑' n : ℕ, (if N < n then ((N : ℝ) / n) ^ a else 0)
      ≤ ((N : ℝ) / (N + 1)) ^ (a - 2) * ((N : ℝ) ^ 2 * inverseSquareMass) := by
  have hdom : Summable fun n : ℕ =>
      ((N : ℝ) / (N + 1)) ^ (a - 2) * ((N : ℝ) ^ 2 * (if n = 0 then 0 else ((n : ℝ) ^ 2)⁻¹)) :=
    ((summable_inverseSquare.mul_left ((N : ℝ) ^ 2)).mul_left _)
  have hterm : ∀ n : ℕ, (if N < n then ((N : ℝ) / n) ^ a else 0)
      ≤ ((N : ℝ) / (N + 1)) ^ (a - 2) *
        ((N : ℝ) ^ 2 * (if n = 0 then 0 else ((n : ℝ) ^ 2)⁻¹)) := by
    intro n
    by_cases h : N < n
    · rw [if_pos h]
      have hn0 : n ≠ 0 := by omega
      rw [if_neg hn0]
      exact ratioPow_le hN h ha
    · rw [if_neg h]
      by_cases h2 : n = 0
      · rw [if_pos h2]
        norm_num
      · rw [if_neg h2]
        positivity
  have hle := (summable_ratioPow hN ha).tsum_le_tsum hterm hdom
  refine hle.trans_eq ?_
  rw [inverseSquareMass, ← tsum_mul_left, ← tsum_mul_left]

/-- **The uniform ratio tail vanishes.**  For every fixed `N ≥ 1` the tail
`∑_{n > N} (N/n)^a` tends to zero as the exponent grows. -/
theorem tendsto_tsum_ratioPow {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun a : ℝ => ∑' n : ℕ, (if N < n then ((N : ℝ) / n) ^ a else 0)) atTop (𝓝 0) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) ≤ (N : ℝ) / (N + 1) := by positivity
  have hr1 : (N : ℝ) / (N + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hgeo : Tendsto (fun a : ℝ => ((N : ℝ) / (N + 1)) ^ (a - 2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_atTop_of_base_lt_one ((N : ℝ) / (N + 1)) (by linarith) hr1
    exact h.comp (tendsto_atTop_add_const_right _ (-2 : ℝ) tendsto_id)
  have hmul : Tendsto (fun a : ℝ => ((N : ℝ) / (N + 1)) ^ (a - 2) *
      ((N : ℝ) ^ 2 * inverseSquareMass)) atTop (𝓝 0) := by
    have := hgeo.mul_const ((N : ℝ) ^ 2 * inverseSquareMass)
    simpa using this
  refine squeeze_zero' ?_ ?_ hmul
  · filter_upwards with a
    refine tsum_nonneg fun n => ?_
    by_cases h : N < n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
    exact tsum_ratioPow_le hN ha

end


end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

theorem norm_squarefreeActionCoefficient_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖squarefreeActionCoefficient s n‖ ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [squarefreeActionCoefficient]
    simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      have h : |moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      rw [Complex.norm_intCast]
      exact_mod_cast h
    have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      refine Real.rpow_le_one_of_one_le_of_nonpos hn1 ?_
      simp only [Complex.neg_re, neg_nonpos]
      exact hs.le
    rw [squarefreeActionCoefficient, norm_mul]
    have hsub : ‖(n : ℂ) ^ (-s) - 1‖ ≤ 2 := by
      calc ‖(n : ℂ) ^ (-s) - 1‖ ≤ ‖(n : ℂ) ^ (-s)‖ + ‖(1 : ℂ)‖ := by
            rw [sub_eq_add_neg]
            refine (norm_add_le _ _).trans_eq ?_
            rw [norm_neg]
        _ ≤ 1 + 1 := by
            simp only [norm_one]
            linarith
        _ = 2 := by norm_num
    calc ‖((moebius n : ℤ) : ℂ)‖ * ‖(n : ℂ) ^ (-s) - 1‖ ≤ 1 * 2 :=
          mul_le_mul hmu hsub (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

/-- The shifted form of the ratio tail. -/
theorem tendsto_tsum_shiftedRatioPow {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun a : ℝ => ∑' k : ℕ, ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ a) atTop (𝓝 0) := by
  have hmain := tendsto_tsum_ratioPow hN
  refine hmain.congr fun a => ?_
  have hinj : Function.Injective fun k : ℕ => N + 1 + k := by
    intro k1 k2 h
    simp only at h
    omega
  have hsupp : (Function.support fun n : ℕ => (if N < n then ((N : ℝ) / n) ^ a else 0))
      ⊆ Set.range (fun k : ℕ => N + 1 + k) := by
    intro n hn
    by_cases h : N < n
    · exact ⟨n - (N + 1), by simp only; omega⟩
    · exfalso
      apply hn
      simp only
      rw [if_neg h]
  have h := hinj.tsum_eq (f := fun n : ℕ => (if N < n then ((N : ℝ) / n) ^ a else 0)) hsupp
  rw [← h]
  refine tsum_congr fun k => ?_
  have hlt : N < N + 1 + k := by omega
  rw [if_pos hlt]
  congr 2
  push_cast
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

/-- **`(4)`, exact form.**  Above the abscissa the deflated depth increment is the `N`-th action
coefficient plus a strictly deeper tail. -/
theorem actionExtraction_eq {s : ℂ} {N m : ℕ} (hN : 2 ≤ N)
    (hm : 1 < ((m : ℂ) * s).re) (hm1 : 1 < (((m : ℂ) + 1) * s).re) :
    (N : ℂ) ^ ((m : ℂ) * s) *
      (depthReciprocalZetaIncrement m s
        - ∑ n ∈ Finset.Ico 2 N, squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s)))
      = squarefreeActionCoefficient s N
        + ∑' k : ℕ, (N : ℂ) ^ ((m : ℂ) * s) *
            (squarefreeActionCoefficient s (k + 1 + N) *
              ((k + 1 + N : ℕ) : ℂ) ^ (-((m : ℂ) * s))) := by
  classical
  set f : ℕ → ℂ := fun n => squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s)) with hf
  have hsum := hasSum_depthReciprocalZetaIncrement (m := m) (s := s) hm hm1
  have hsummable : Summable f := hsum.summable
  have hsplit : depthReciprocalZetaIncrement m s
      = (∑ i ∈ Finset.range N, f i) + ∑' k : ℕ, f (k + N) := by
    rw [← hsum.tsum_eq]
    exact (hsummable.sum_add_tsum_nat_add N).symm
  have hlow : (∑ i ∈ Finset.range N, f i)
      = ∑ n ∈ Finset.Ico 2 N, squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s)) := by
    have hrange : Finset.range N = Finset.Ico 0 N := by
      rw [Finset.range_eq_Ico]
    rw [hrange, ← Finset.sum_Ico_consecutive f (Nat.zero_le 2) (by omega : 2 ≤ N)]
    have hzero : (∑ i ∈ Finset.Ico 0 2, f i) = 0 := by
      rw [show Finset.Ico 0 2 = {0, 1} from by decide, Finset.sum_insert (by decide),
        Finset.sum_singleton, hf]
      simp [squarefreeActionCoefficient]
    rw [hzero, zero_add]
  rw [hsplit, hlow, add_sub_cancel_left, ← tsum_mul_left]
  have hzero : (N : ℂ) ^ ((m : ℂ) * s) * f (0 + N) = squarefreeActionCoefficient s N := by
    rw [hf]
    simp only [zero_add]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hne : (N : ℂ) ^ ((m : ℂ) * s) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      tauto
    rw [Complex.cpow_neg]
    field_simp
  have hshift : Summable fun k : ℕ => (N : ℂ) ^ ((m : ℂ) * s) * f (k + N) :=
    ((hsummable.comp_injective (add_left_injective N)).mul_left _)
  rw [hshift.tsum_eq_zero_add, hzero]

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology ArithmeticFunction

theorem summable_shiftedRatioPow {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 2 ≤ a) :
    Summable fun k : ℕ => ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ a := by
  have hinj : Function.Injective fun k : ℕ => N + 1 + k := by
    intro k1 k2 h
    simp only at h
    omega
  have h := (summable_ratioPow hN ha).comp_injective hinj
  refine h.congr fun k => ?_
  have hlt : N < N + 1 + k := by omega
  simp only [Function.comp_apply]
  rw [if_pos hlt]
  congr 2
  push_cast
  ring

/-- **`(4)`: every action coefficient is recoverable.**  Asymptotic deflation of the depth
increment recovers the `N`-th squarefree action coefficient exactly. -/
theorem tendsto_actionExtraction {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun m : ℕ => (N : ℂ) ^ ((m : ℂ) * s) *
        (depthReciprocalZetaIncrement m s
          - ∑ n ∈ Finset.Ico 2 N, squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s))))
      atTop (𝓝 (squarefreeActionCoefficient s N)) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  -- the exponent grows
  have hexp : Tendsto (fun m : ℕ => (m : ℝ) * s.re) atTop atTop := by
    have h : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact h.atTop_mul_const hs
  have hre : ∀ m : ℕ, ((m : ℂ) * s).re = (m : ℝ) * s.re := by
    intro m
    simp
  have hre1 : ∀ m : ℕ, (((m : ℂ) + 1) * s).re = ((m : ℝ) + 1) * s.re := by
    intro m
    simp
  have hlarge : ∀ᶠ m : ℕ in atTop, 1 < ((m : ℂ) * s).re ∧ 1 < (((m : ℂ) + 1) * s).re
      ∧ 2 ≤ (m : ℝ) * s.re := by
    have h1 : ∀ᶠ m : ℕ in atTop, 2 ≤ (m : ℝ) * s.re := hexp.eventually_ge_atTop 2
    filter_upwards [h1] with m hm
    have hm1 : (1 : ℝ) < (m : ℝ) * s.re := by linarith
    refine ⟨?_, ?_, hm⟩
    · rw [hre]; exact hm1
    · rw [hre1]
      have hmm : (m : ℝ) * s.re ≤ ((m : ℝ) + 1) * s.re := by nlinarith
      linarith
  rw [← tendsto_sub_nhds_zero_iff]
  have hbound : ∀ᶠ m : ℕ in atTop,
      ‖(N : ℂ) ^ ((m : ℂ) * s) *
          (depthReciprocalZetaIncrement m s
            - ∑ n ∈ Finset.Ico 2 N, squarefreeActionCoefficient s n * (n : ℂ) ^ (-((m : ℂ) * s)))
        - squarefreeActionCoefficient s N‖
      ≤ 2 * ∑' k : ℕ, ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ ((m : ℝ) * s.re) := by
    filter_upwards [hlarge] with m hm
    obtain ⟨hm0, hm1, hm2⟩ := hm
    rw [actionExtraction_eq hN hm0 hm1, add_sub_cancel_left]
    have hterm : ∀ k : ℕ,
        ‖(N : ℂ) ^ ((m : ℂ) * s) *
            (squarefreeActionCoefficient s (k + 1 + N) *
              ((k + 1 + N : ℕ) : ℂ) ^ (-((m : ℂ) * s)))‖
          ≤ 2 * ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ ((m : ℝ) * s.re) := by
      intro k
      have hk0 : 0 < k + 1 + N := by omega
      have hnormN : ‖(N : ℂ) ^ ((m : ℂ) * s)‖ = (N : ℝ) ^ ((m : ℝ) * s.re) := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), hre]
      have hnormk : ‖((k + 1 + N : ℕ) : ℂ) ^ (-((m : ℂ) * s))‖
          = ((k + 1 + N : ℕ) : ℝ) ^ (-((m : ℝ) * s.re)) := by
        rw [Complex.norm_natCast_cpow_of_pos hk0]
        congr 1
        rw [Complex.neg_re, hre]
      have hcoef := norm_squarefreeActionCoefficient_le hs (k + 1 + N)
      have hratio : (N : ℝ) ^ ((m : ℝ) * s.re) * ((k + 1 + N : ℕ) : ℝ) ^ (-((m : ℝ) * s.re))
          = ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ ((m : ℝ) * s.re) := by
        have hcast : ((k + 1 + N : ℕ) : ℝ) = (N : ℝ) + 1 + k := by push_cast; ring
        rw [hcast, Real.div_rpow (le_of_lt hNpos) (by positivity),
          Real.rpow_neg (by positivity), div_eq_mul_inv]
      rw [norm_mul, norm_mul, hnormN, hnormk]
      calc (N : ℝ) ^ ((m : ℝ) * s.re) *
            (‖squarefreeActionCoefficient s (k + 1 + N)‖ *
              ((k + 1 + N : ℕ) : ℝ) ^ (-((m : ℝ) * s.re)))
          ≤ (N : ℝ) ^ ((m : ℝ) * s.re) * (2 * ((k + 1 + N : ℕ) : ℝ) ^ (-((m : ℝ) * s.re))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = 2 * ((N : ℝ) ^ ((m : ℝ) * s.re) *
              ((k + 1 + N : ℕ) : ℝ) ^ (-((m : ℝ) * s.re))) := by ring
        _ = 2 * ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ ((m : ℝ) * s.re) := by rw [hratio]
    have hsummableBound : Summable fun k : ℕ =>
        2 * ((N : ℝ) / ((N : ℝ) + 1 + k)) ^ ((m : ℝ) * s.re) :=
      (summable_shiftedRatioPow hN1 hm2).mul_left 2
    have hnorm := norm_tsum_le_tsum_norm (f := fun k : ℕ => (N : ℂ) ^ ((m : ℂ) * s) *
        (squarefreeActionCoefficient s (k + 1 + N) *
          ((k + 1 + N : ℕ) : ℂ) ^ (-((m : ℂ) * s)))) ?_
    · refine hnorm.trans ?_
      have hle := Summable.tsum_le_tsum hterm ?_ hsummableBound
      · rw [tsum_mul_left] at hle
        exact hle
      · refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hsummableBound
    · refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hsummableBound
  refine squeeze_zero_norm' hbound ?_
  have hcomp := (tendsto_tsum_shiftedRatioPow hN1).comp hexp
  have hmul := hcomp.const_mul (2 : ℝ)
  rw [mul_zero] at hmul
  exact hmul

end

end RHTower
