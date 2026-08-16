import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerBalancedWallSquare
import GaloisForLFunctions.RHTower.MobiusWoldBreadthGibbsCost

/-!
# P-G105Q: Stokes-wall Hilbert--Schmidt energy floor

Every fixed transported-prime coordinate vanishes as the aperture approaches the
wall, so coordinatewise operator limits lose the full trace mass. The cubic
coherence nevertheless retains a quantitative diffuse remnant.

The scaled wall moment

`M(d) = ∑_p w_d(p) X_d(p)^6 (1-X_d(p))^3`

is an exact four-term dilation combination of the already formalized oriented
first-trace current, and therefore tends to `1/210`. A pointwise exponential
minorant for cubic Cauchy coherence gives

`64 M(d)^2 ≤ ∑_{p,q} ‖K_d(p,q)‖²`,

hence the child Hilbert--Schmidt energy is eventually at least `4/11025`.
This proves aperture-wall noncollapse at the quadratic-energy level; it does
not identify the limiting determinant with Xi.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

def routePPrimitiveGammaJuliaStokesWallCoordinate
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-2 * d)

theorem wall_weight_mul_rpow_dilation
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
        (p : ℝ) ^ (-2 * (c - 1) * d) =
      (1 / c) *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (c * d) p := by
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq (mul_pos hc hd),
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    xiMassPrimeSquareEulerWeight_eq,
    xiMassPrimeSquareEulerWeight_eq,
    abs_of_pos hd, abs_of_pos (mul_pos hc hd)]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  calc
    8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d))) *
          (p : ℝ) ^ (-2 * (c - 1) * d) =
        8 * d * Real.log (p : ℝ) *
          ((p : ℝ) ^ (-(1 + 2 * d)) *
            (p : ℝ) ^ (-2 * (c - 1) * d)) := by ring
    _ = 8 * d * Real.log (p : ℝ) *
          (p : ℝ) ^ (-(1 + 2 * (c * d))) := by
      rw [← Real.rpow_add hp]
      congr 2
      ring
    _ = 1 / c *
          (8 * (c * d) *
            (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * (c * d))))) := by
      field_simp [hc.ne']

def routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
    routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ 6 *
    (1 - routePPrimitiveGammaJuliaStokesWallCoordinate d p) ^ 3

def routePPrimitiveGammaJuliaStokesWallCoherenceMoment (d : ℝ) : ℝ :=
  ∑' p : Nat.Primes,
    routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d p

private theorem wallCoordinate_pow
    (d : ℝ) (p : Nat.Primes) (n : ℕ) :
    routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ n =
      (p : ℝ) ^ (-2 * (n : ℝ) * d) := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.pos.le
  rw [routePPrimitiveGammaJuliaStokesWallCoordinate]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hp]
  congr 1
  ring

theorem wallCoherenceMomentTerm_eq_current_combination
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d p =
      (1 / 7 : ℝ) *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (7 * d) p -
        (3 / 8 : ℝ) *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (8 * d) p +
        (1 / 3 : ℝ) *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (9 * d) p -
        (1 / 10 : ℝ) *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (10 * d) p := by
  have h7 := wall_weight_mul_rpow_dilation hd (by norm_num : (0 : ℝ) < 7) p
  have h8 := wall_weight_mul_rpow_dilation hd (by norm_num : (0 : ℝ) < 8) p
  have h9 := wall_weight_mul_rpow_dilation hd (by norm_num : (0 : ℝ) < 9) p
  have h10 := wall_weight_mul_rpow_dilation hd (by norm_num : (0 : ℝ) < 10) p
  norm_num at h7 h8 h9 h10
  rw [routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm]
  rw [show routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
      routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ 6 *
      (1 - routePPrimitiveGammaJuliaStokesWallCoordinate d p) ^ 3 =
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
            routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ 6 -
          3 * (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
            routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ 7) +
          3 * (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
            routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ 8) -
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
            routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ 9 by ring]
  rw [wallCoordinate_pow, wallCoordinate_pow, wallCoordinate_pow, wallCoordinate_pow]
  norm_num
  linear_combination h7 - 3 * h8 + 3 * h9 - h10

theorem summable_wallCoherenceMomentTerm
    {d : ℝ} (hd : 0 < d) :
    Summable (routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d) := by
  have h7 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 7 * d by positivity)
  have h8 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 8 * d by positivity)
  have h9 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 9 * d by positivity)
  have h10 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 10 * d by positivity)
  refine ((((h7.mul_left (1 / 7 : ℝ)).sub (h8.mul_left (3 / 8 : ℝ))).add
    (h9.mul_left (1 / 3 : ℝ))).sub (h10.mul_left (1 / 10 : ℝ))).congr ?_
  intro p
  exact (wallCoherenceMomentTerm_eq_current_combination hd p).symm

theorem wallCoherenceMoment_eq_current_combination
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallCoherenceMoment d =
      (1 / 7 : ℝ) *
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (7 * d) -
        (3 / 8 : ℝ) *
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (8 * d) +
        (1 / 3 : ℝ) *
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (9 * d) -
        (1 / 10 : ℝ) *
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (10 * d) := by
  have h7 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 7 * d by positivity)
  have h8 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 8 * d by positivity)
  have h9 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 9 * d by positivity)
  have h10 := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < 10 * d by positivity)
  let h7c := h7.mul_left (1 / 7 : ℝ)
  let h8c := h8.mul_left (3 / 8 : ℝ)
  let h9c := h9.mul_left (1 / 3 : ℝ)
  let h10c := h10.mul_left (1 / 10 : ℝ)
  rw [routePPrimitiveGammaJuliaStokesWallCoherenceMoment]
  calc
    (∑' p : Nat.Primes,
      routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d p) =
        ∑' p : Nat.Primes,
          ((1 / 7 : ℝ) * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (7 * d) p -
            (3 / 8 : ℝ) * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (8 * d) p +
            (1 / 3 : ℝ) * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (9 * d) p -
            (1 / 10 : ℝ) * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (10 * d) p) :=
      tsum_congr (wallCoherenceMomentTerm_eq_current_combination hd)
    _ = (1 / 7 : ℝ) *
          (∑' p : Nat.Primes, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (7 * d) p) -
        (3 / 8 : ℝ) *
          (∑' p : Nat.Primes, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (8 * d) p) +
        (1 / 3 : ℝ) *
          (∑' p : Nat.Primes, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (9 * d) p) -
        (1 / 10 : ℝ) *
          (∑' p : Nat.Primes, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (10 * d) p) := by
      rw [(((h7c.sub h8c).add h9c).tsum_sub h10c),
        (h7c.sub h8c).tsum_add h9c, h7c.tsum_sub h8c]
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    _ = _ := by
      rw [tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
          (show 0 < 7 * d by positivity),
        tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
          (show 0 < 8 * d by positivity),
        tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
          (show 0 < 9 * d by positivity),
        tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
          (show 0 < 10 * d by positivity)]

private theorem tendsto_posScale_nhdsGT_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun d : ℝ => c * d) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using
      ((tendsto_const_nhds.mul tendsto_id :
        Tendsto (fun d : ℝ => c * d) (𝓝 0) (𝓝 (c * 0))).mono_left
          nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with d hd
    exact mul_pos hc hd

theorem tendsto_wallCoherenceMoment_nhdsGT_zero :
    Tendsto routePPrimitiveGammaJuliaStokesWallCoherenceMoment
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 210 : ℝ)) := by
  let W := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
  have h7 : Tendsto (fun d : ℝ => W (7 * d)) (𝓝[>] (0 : ℝ)) (𝓝 4) :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      (tendsto_posScale_nhdsGT_zero (by norm_num : (0 : ℝ) < 7))
  have h8 : Tendsto (fun d : ℝ => W (8 * d)) (𝓝[>] (0 : ℝ)) (𝓝 4) :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      (tendsto_posScale_nhdsGT_zero (by norm_num : (0 : ℝ) < 8))
  have h9 : Tendsto (fun d : ℝ => W (9 * d)) (𝓝[>] (0 : ℝ)) (𝓝 4) :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      (tendsto_posScale_nhdsGT_zero (by norm_num : (0 : ℝ) < 9))
  have h10 : Tendsto (fun d : ℝ => W (10 * d)) (𝓝[>] (0 : ℝ)) (𝓝 4) :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      (tendsto_posScale_nhdsGT_zero (by norm_num : (0 : ℝ) < 10))
  have hcomb := (((h7.const_mul (1 / 7 : ℝ)).sub (h8.const_mul (3 / 8 : ℝ))).add
    (h9.const_mul (1 / 3 : ℝ))).sub (h10.const_mul (1 / 10 : ℝ))
  have hlim : Tendsto (fun d : ℝ =>
      (1 / 7 : ℝ) * W (7 * d) - (3 / 8 : ℝ) * W (8 * d) +
        (1 / 3 : ℝ) * W (9 * d) - (1 / 10 : ℝ) * W (10 * d))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 210 : ℝ)) := by
    convert hcomb using 1
    all_goals norm_num
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (wallCoherenceMoment_eq_current_combination hd).symm

private theorem expWallMoment_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ Real.exp (-a) ^ 6 * (1 - Real.exp (-a)) ^ 3 := by
  have hexp : Real.exp (-a) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
    (pow_nonneg (sub_nonneg.mpr hexp) _)

private theorem expWallMoment_le_rational
    {a : ℝ} (ha : 0 < a) :
    Real.exp (-a) ^ 6 * (1 - Real.exp (-a)) ^ 3 ≤
      (1 / (1 + a)) ^ 6 * a ^ 3 := by
  have hden : 0 < 1 + a := by linarith
  have hxle : Real.exp (-a) ≤ 1 / (1 + a) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos a) hden).2 (by
      simpa [add_comm] using Real.add_one_le_exp a)
  have hxpow := pow_le_pow_left₀ (Real.exp_pos (-a)).le hxle 6
  have hexpOne : Real.exp (-a) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsub0 : 0 ≤ 1 - Real.exp (-a) := sub_nonneg.mpr hexpOne
  have hsuble : 1 - Real.exp (-a) ≤ a := one_sub_exp_neg_le a
  have hsubpow := pow_le_pow_left₀ hsub0 hsuble 3
  exact mul_le_mul hxpow hsubpow (pow_nonneg hsub0 3)
    (pow_nonneg (by positivity : 0 ≤ (1 / (1 + a))) 6)

private theorem cubicCoherence_expWallMoment_lower
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    64 *
        (Real.exp (-a) ^ 6 * (1 - Real.exp (-a)) ^ 3) *
        (Real.exp (-b) ^ 6 * (1 - Real.exp (-b)) ^ 3) ≤
      routePBaseCauchyCubicNormalizedCoherenceSq a b 0 := by
  have hma := expWallMoment_le_rational ha
  have hmb := expWallMoment_le_rational hb
  have hma0 := expWallMoment_nonneg ha.le
  have hmb0 := expWallMoment_nonneg hb.le
  have hratA0 : 0 ≤ (1 / (1 + a)) ^ 6 * a ^ 3 := by positivity
  have hprod := mul_le_mul hma hmb hmb0 hratA0
  have hden : a + b ≤ (1 + a) * (1 + b) := by nlinarith [mul_pos ha hb]
  have hdenPos : 0 < a + b := add_pos ha hb
  have hwidePos : 0 < (1 + a) * (1 + b) := mul_pos (by linarith) (by linarith)
  have hpowden := pow_le_pow_left₀ hdenPos.le hden 6
  have hnum : 0 ≤ 64 * a ^ 3 * b ^ 3 := by positivity
  have hdiv := div_le_div_of_nonneg_left hnum (pow_pos hdenPos 6) hpowden
  have halg :
      64 * ((1 / (1 + a)) ^ 6 * a ^ 3) *
          ((1 / (1 + b)) ^ 6 * b ^ 3) =
        (64 * a ^ 3 * b ^ 3) / (((1 + a) * (1 + b)) ^ 6) := by
    field_simp [ne_of_gt (by linarith : 0 < 1 + a),
      ne_of_gt (by linarith : 0 < 1 + b)]
  rw [routePBaseCauchyCubicNormalizedCoherenceSq]
  norm_num
  calc
    64 * (Real.exp (-a) ^ 6 * (1 - Real.exp (-a)) ^ 3) *
          (Real.exp (-b) ^ 6 * (1 - Real.exp (-b)) ^ 3) ≤
        64 * ((1 / (1 + a)) ^ 6 * a ^ 3) *
          ((1 / (1 + b)) ^ 6 * b ^ 3) := by nlinarith
    _ = (64 * a ^ 3 * b ^ 3) / (((1 + a) * (1 + b)) ^ 6) := halg
    _ ≤ (64 * a ^ 3 * b ^ 3) / (((a + b) ^ 2) ^ 3) := by
      rw [show ((a + b) ^ 2) ^ 3 = (a + b) ^ 6 by ring]
      exact hdiv

private theorem cubicCoherence_commonScale
    {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    routePBaseCauchyCubicNormalizedCoherenceSq (s * a) (s * b) 0 =
      routePBaseCauchyCubicNormalizedCoherenceSq a b 0 := by
  rw [routePBaseCauchyCubicNormalizedCoherenceSq,
    routePBaseCauchyCubicNormalizedCoherenceSq]
  norm_num
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hs0 : s ≠ 0 := hs.ne'
  field_simp [hab, hs0]

theorem wallCoordinate_eq_exp
    (d : ℝ) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallCoordinate d p =
      Real.exp (-(2 * d * Real.log (p : ℝ))) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [routePPrimitiveGammaJuliaStokesWallCoordinate,
    Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem wallCoherenceMoment_product_le_kernel_normSq
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    64 * routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d p *
        routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d q ≤
      Complex.normSq
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, q)) := by
  let a : ℝ := 2 * d * Real.log (p : ℝ)
  let b : ℝ := 2 * d * Real.log (q : ℝ)
  have hlp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hlq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hcoh := cubicCoherence_expWallMoment_lower ha hb
  rw [cubicCoherence_commonScale (show 0 < 2 * d by positivity) hlp hlq] at hcoh
  have hcoordP : routePPrimitiveGammaJuliaStokesWallCoordinate d p = Real.exp (-a) := by
    rw [wallCoordinate_eq_exp]
  have hcoordQ : routePPrimitiveGammaJuliaStokesWallCoordinate d q = Real.exp (-b) := by
    rw [wallCoordinate_eq_exp]
  have hwp := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd p
  have hwq := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd q
  have hweighted := mul_le_mul_of_nonneg_left hcoh (mul_nonneg hwp hwq)
  rw [normSq_routePPrimitiveGammaJuliaStokesCofinalChildKernel hd]
  rw [routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm,
    routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm,
    hcoordP, hcoordQ]
  nlinarith

theorem wallCoherenceMomentTerm_nonneg
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d p := by
  let a : ℝ := 2 * d * Real.log (p : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (mul_pos (by norm_num) hd)
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
  have hcoord : routePPrimitiveGammaJuliaStokesWallCoordinate d p = Real.exp (-a) := by
    rw [wallCoordinate_eq_exp]
  rw [routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm, hcoord]
  exact mul_nonneg
    (mul_nonneg
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd p)
      (pow_nonneg (Real.exp_pos _).le 6))
    (pow_nonneg (sub_nonneg.mpr (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith))) 3)

def routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy (d : ℝ) : ℝ :=
  ∑' pq : Nat.Primes × Nat.Primes,
    Complex.normSq
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq)

theorem summable_wallHilbertSchmidtEnergy
    {d : ℝ} (hd : 0 < d) :
    Summable (fun pq : Nat.Primes × Nat.Primes =>
      Complex.normSq
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq)) := by
  have hs := routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  rw [HilbertSchmidt.IsHS] at hs
  exact hs.congr (fun pq => by rw [Complex.sq_norm])

theorem wallHilbertSchmidtEnergy_ge_moment_sq
    {d : ℝ} (hd : 0 < d) :
    64 * routePPrimitiveGammaJuliaStokesWallCoherenceMoment d ^ 2 ≤
      routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy d := by
  let m := routePPrimitiveGammaJuliaStokesWallCoherenceMomentTerm d
  have hm : Summable m := summable_wallCoherenceMomentTerm hd
  have hprod : Summable (fun pq : Nat.Primes × Nat.Primes =>
      m pq.1 * m pq.2) :=
    summable_mul_of_summable_norm hm.norm hm.norm
  have hleft : Summable (fun pq : Nat.Primes × Nat.Primes =>
      64 * (m pq.1 * m pq.2)) := hprod.mul_left 64
  have hright := summable_wallHilbertSchmidtEnergy hd
  have hsum :
      (∑' pq : Nat.Primes × Nat.Primes, 64 * (m pq.1 * m pq.2)) ≤
        ∑' pq : Nat.Primes × Nat.Primes,
          Complex.normSq
            (routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq) := by
    exact Summable.tsum_le_tsum
      (fun pq => by
        simpa [m, mul_assoc] using
          wallCoherenceMoment_product_le_kernel_normSq hd pq.1 pq.2)
      hleft hright
  have hfactor := tsum_mul_tsum_of_summable_norm hm.norm hm.norm
  calc
    64 * routePPrimitiveGammaJuliaStokesWallCoherenceMoment d ^ 2 =
        64 * ((∑' p : Nat.Primes, m p) * (∑' p : Nat.Primes, m p)) := by
      simp only [routePPrimitiveGammaJuliaStokesWallCoherenceMoment, m, pow_two]
    _ = 64 * (∑' pq : Nat.Primes × Nat.Primes, m pq.1 * m pq.2) := by
      rw [hfactor]
    _ = ∑' pq : Nat.Primes × Nat.Primes, 64 * (m pq.1 * m pq.2) := by
      rw [tsum_mul_left]
    _ ≤ _ := hsum

theorem eventually_wallHilbertSchmidtEnergy_ge :
    ∀ᶠ d in 𝓝[>] (0 : ℝ),
      (4 / 11025 : ℝ) ≤
        routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy d := by
  have hmoment : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      (1 / 420 : ℝ) < routePPrimitiveGammaJuliaStokesWallCoherenceMoment d :=
    (tendsto_order.1 tendsto_wallCoherenceMoment_nhdsGT_zero).1
      (1 / 420 : ℝ) (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hmoment] with d hd hmoment
  have henergy := wallHilbertSchmidtEnergy_ge_moment_sq hd
  nlinarith [sq_nonneg
    (routePPrimitiveGammaJuliaStokesWallCoherenceMoment d - (1 / 420 : ℝ))]

end

end RHTower

