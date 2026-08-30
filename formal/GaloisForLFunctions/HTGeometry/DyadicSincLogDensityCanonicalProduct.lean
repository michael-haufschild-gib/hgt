import GaloisForLFunctions.HTGeometry.CanonicalProductE1Divisor
import GaloisForLFunctions.HTGeometry.CanonicalProductGrowth
import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA
import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import GaloisForLFunctions.HTGeometry.InfiniteProductNonvanishing
import GaloisForLFunctions.HTGeometry.MultivariateEntireStripBound

open Complex Set Filter Topology Metric

noncomputable section

set_option maxHeartbeats 800000

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- Dyadic scale, multiplicity copy, and positive integer sinc zero. -/
abbrev DyadicSincIndex := Σ j : ℕ, Fin (2 ^ j) × ℕ

/-- Positive zero at `2^j (n+1)`, repeated `2^j` times on scale `j`. -/
def dyadicSincDivisorPoint (q : DyadicSincIndex) : ℂ :=
  ((2 ^ q.1 * (q.2.2 + 1) : ℕ) : ℂ)

theorem dyadicSincDivisorPoint_norm (q : DyadicSincIndex) :
    ‖dyadicSincDivisorPoint q‖ =
      ((2 ^ q.1 : ℕ) : ℝ) * ((q.2.2 + 1 : ℕ) : ℝ) := by
  rw [dyadicSincDivisorPoint, Complex.norm_natCast]
  push_cast
  ring

theorem dyadicSincDivisorPoint_ne_zero (q : DyadicSincIndex) :
    dyadicSincDivisorPoint q ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [dyadicSincDivisorPoint_norm]
  positivity

@[simp] theorem dyadicSincDivisorPoint_im (q : DyadicSincIndex) :
    (dyadicSincDivisorPoint q).im = 0 := by
  change ((((2 ^ q.1 * (q.2.2 + 1) : ℕ) : ℂ)).im) = 0
  exact Complex.natCast_im _

private theorem summable_one_div_nat_succ_sq' :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
  exact hshift.congr fun n => by
    push_cast
    ring

theorem dyadicSincDivisorPoint_inv_sq_summable :
    Summable (fun q : DyadicSincIndex => 1 / ‖dyadicSincDivisorPoint q‖ ^ 2) := by
  have hinner : ∀ (j : ℕ) (c : Fin (2 ^ j)), Summable (fun n : ℕ =>
      1 / ‖dyadicSincDivisorPoint ⟨j, ⟨c, n⟩⟩‖ ^ 2) := by
    intro j c
    refine (summable_one_div_nat_succ_sq'.mul_left
      (1 / (((2 ^ j : ℕ) : ℝ) ^ 2))).congr fun n => ?_
    rw [dyadicSincDivisorPoint_norm]
    dsimp
    push_cast
    field_simp
  have hscale : ∀ j : ℕ, Summable (fun q : Fin (2 ^ j) × ℕ =>
      1 / ‖dyadicSincDivisorPoint ⟨j, q⟩‖ ^ 2) := by
    intro j
    rw [summable_prod_of_nonneg (fun q => by positivity)]
    exact ⟨fun c => hinner j c, Summable.of_finite⟩
  rw [summable_sigma_of_nonneg (fun q => by positivity)]
  refine ⟨hscale, ?_⟩
  · let Z : ℝ := ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2
    have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
    have hgeom : Summable (fun j : ℕ => Z * (1 / 2 : ℝ) ^ j) :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left Z
    refine hgeom.congr fun j => ?_
    rw [(hscale j).tsum_prod, tsum_fintype]
    have hinnerEq : (∑' q : ℕ,
        1 / ‖dyadicSincDivisorPoint ⟨j, ⟨0, q⟩⟩‖ ^ 2) =
        (1 / (((2 ^ j : ℕ) : ℝ) ^ 2)) * Z := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [dyadicSincDivisorPoint_norm]
      dsimp
      push_cast
      field_simp
    have hall : ∀ c : Fin (2 ^ j), (∑' q : ℕ,
        1 / ‖dyadicSincDivisorPoint ⟨j, ⟨c, q⟩⟩‖ ^ 2) =
        (1 / (((2 ^ j : ℕ) : ℝ) ^ 2)) * Z := by
      intro c
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [dyadicSincDivisorPoint_norm]
      dsimp
      push_cast
      field_simp
    simp_rw [hall]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have htwo : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [htwo]
    rw [show Z * (1 / 2 : ℝ) ^ j * 2 ^ j = Z * ((1 / 2 : ℝ) * 2) ^ j by
      rw [mul_pow]
      ring]
    norm_num

theorem dyadicSincDivisorPoint_locallyFinite :
    GaloisForLFunctions.CountableDivisor.LocallyFiniteDivisor
      dyadicSincDivisorPoint := by
  intro r
  let S : ℝ := max r 0 + 1
  have hS : 0 < S := by
    dsimp [S]
    linarith [le_max_right r 0]
  have htend : Tendsto (fun q : DyadicSincIndex =>
      1 / ‖dyadicSincDivisorPoint q‖ ^ 2) cofinite (𝓝 0) :=
    dyadicSincDivisorPoint_inv_sq_summable.tendsto_cofinite_zero
  have hlt : ∀ᶠ q : DyadicSincIndex in cofinite,
      1 / ‖dyadicSincDivisorPoint q‖ ^ 2 < 1 / S ^ 2 :=
    htend.eventually_lt_const (by positivity)
  have hev : {q : DyadicSincIndex | S ≤ ‖dyadicSincDivisorPoint q‖} ∈
      (cofinite : Filter DyadicSincIndex) := by
    filter_upwards [hlt] with q hq
    have hpos : 0 < ‖dyadicSincDivisorPoint q‖ :=
      norm_pos_iff.mpr (dyadicSincDivisorPoint_ne_zero q)
    have hsq : S ^ 2 < ‖dyadicSincDivisorPoint q‖ ^ 2 :=
      lt_of_one_div_lt_one_div (pow_pos hpos 2) hq
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
  have hfin : {q : DyadicSincIndex | S ≤ ‖dyadicSincDivisorPoint q‖}ᶜ.Finite :=
    Filter.mem_cofinite.mp hev
  refine hfin.subset ?_
  intro q hq
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  exact lt_of_le_of_lt (hq.trans (le_max_left r 0)) (lt_add_one _)

/-- Positive-half genus-one product for the dyadic sinc divisor. -/
def dyadicSincPositiveProduct (z : ℂ) : ℂ :=
  canonicalProductE1Indexed dyadicSincDivisorPoint z

/-- FE-even dyadic cascade, pairing every positive divisor point with its negative. -/
def dyadicSincCascade (z : ℂ) : ℂ :=
  dyadicSincPositiveProduct z * dyadicSincPositiveProduct (-z)

theorem analyticOnNhd_dyadicSincPositiveProduct :
    AnalyticOnNhd ℂ dyadicSincPositiveProduct Set.univ := by
  exact canonicalProductE1Indexed_analytic _
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable

theorem analyticOnNhd_dyadicSincCascade :
    AnalyticOnNhd ℂ dyadicSincCascade Set.univ := by
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -z) Set.univ := by
    intro z hz
    fun_prop
  exact analyticOnNhd_dyadicSincPositiveProduct.mul
    (analyticOnNhd_dyadicSincPositiveProduct.comp hneg (by simp))

theorem differentiable_dyadicSincCascade : Differentiable ℂ dyadicSincCascade :=
  Complex.analyticOnNhd_univ_iff_differentiable.mp analyticOnNhd_dyadicSincCascade

theorem dyadicSincCascade_even (z : ℂ) :
    dyadicSincCascade (-z) = dyadicSincCascade z := by
  simp [dyadicSincCascade, mul_comm]

theorem dyadicSincCascade_zero : dyadicSincCascade 0 = 1 := by
  simp [dyadicSincCascade, dyadicSincPositiveProduct,
    canonicalProductE1Indexed_zero]

theorem dyadicSincCascade_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    dyadicSincCascade z ≠ 0 := by
  apply mul_ne_zero
  · apply canonicalProductE1Indexed_ne_zero dyadicSincDivisorPoint
      dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable
    intro q h
    have him := congrArg Complex.im h
    rw [dyadicSincDivisorPoint_im] at him
    exact hz him
  · apply canonicalProductE1Indexed_ne_zero dyadicSincDivisorPoint
      dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable
    intro q h
    have him := congrArg Complex.im h
    simp only [Complex.neg_im, dyadicSincDivisorPoint_im] at him
    exact hz (neg_eq_zero.mp him)

/-- Pairing opposite genus-one factors cancels their exponential regularizers. -/
theorem dyadicSinc_pairedFactor (z : ℂ) (q : DyadicSincIndex) :
    weierstrassE1 (z / dyadicSincDivisorPoint q) *
        weierstrassE1 (-z / dyadicSincDivisorPoint q) =
      1 - z ^ 2 / dyadicSincDivisorPoint q ^ 2 := by
  have ha := dyadicSincDivisorPoint_ne_zero q
  rw [weierstrassE1, weierstrassE1]
  have hexp : z / dyadicSincDivisorPoint q +
      -z / dyadicSincDivisorPoint q = 0 := by ring
  calc
    (1 - z / dyadicSincDivisorPoint q) * Complex.exp (z / dyadicSincDivisorPoint q) *
        ((1 - -z / dyadicSincDivisorPoint q) *
          Complex.exp (-z / dyadicSincDivisorPoint q)) =
        ((1 - z / dyadicSincDivisorPoint q) *
          (1 - -z / dyadicSincDivisorPoint q)) *
          (Complex.exp (z / dyadicSincDivisorPoint q) *
            Complex.exp (-z / dyadicSincDivisorPoint q)) := by ring
    _ = (1 - z / dyadicSincDivisorPoint q) *
          (1 - -z / dyadicSincDivisorPoint q) := by
      rw [← Complex.exp_add, hexp, Complex.exp_zero, mul_one]
    _ = 1 - z ^ 2 / dyadicSincDivisorPoint q ^ 2 := by
      field_simp [ha]
      ring

theorem dyadicSincCascade_eq_tprod_paired (z : ℂ) :
    dyadicSincCascade z = ∏' q : DyadicSincIndex,
      (1 - z ^ 2 / dyadicSincDivisorPoint q ^ 2) := by
  have hpos := multipliable_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable z
  have hneg := multipliable_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable (-z)
  rw [dyadicSincCascade, dyadicSincPositiveProduct, dyadicSincPositiveProduct,
    canonicalProductE1Indexed, canonicalProductE1Indexed,
    ← hpos.tprod_mul hneg]
  apply tprod_congr
  intro q
  exact dyadicSinc_pairedFactor z q

/-- Scale-by-scale form: the `j`-th scale is a `2^j`-fold Euler sinc product. -/
theorem dyadicSincCascade_eq_tprod_sinc_scales (z : ℂ) :
    dyadicSincCascade z =
      ∏' j : ℕ, HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j) := by
  let f : DyadicSincIndex → ℂ := fun q =>
    1 - z ^ 2 / dyadicSincDivisorPoint q ^ 2
  have hpos := multipliable_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable z
  have hneg := multipliable_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable (-z)
  have hmulRaw : Multipliable (fun q : DyadicSincIndex =>
      weierstrassE1 (z / dyadicSincDivisorPoint q) *
        weierstrassE1 (-z / dyadicSincDivisorPoint q)) := hpos.mul hneg
  have hmul : Multipliable f := hmulRaw.congr fun q => dyadicSinc_pairedFactor z q
  have hscale : ∀ j : ℕ, HasProd
      (fun q : Fin (2 ^ j) × ℕ => f ⟨j, q⟩)
      (HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j)) := by
    intro j
    have hdiffNorm : Summable (fun q : Fin (2 ^ j) × ℕ =>
        ‖f ⟨j, q⟩ - 1‖) := by
      rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
      refine ⟨?_, Summable.of_finite⟩
      intro c
      refine (summable_one_div_nat_succ_sq'.mul_left
        (‖z‖ ^ 2 / (((2 ^ j : ℕ) : ℝ) ^ 2))).congr fun n => ?_
      dsimp [f]
      rw [show 1 - z ^ 2 / dyadicSincDivisorPoint ⟨j, ⟨c, n⟩⟩ ^ 2 - 1 =
          -(z ^ 2 / dyadicSincDivisorPoint ⟨j, ⟨c, n⟩⟩ ^ 2) by ring,
        norm_neg, norm_div, norm_pow, norm_pow, dyadicSincDivisorPoint_norm]
      dsimp
      push_cast
      field_simp
    have hdiff : Summable (fun q : Fin (2 ^ j) × ℕ =>
        f ⟨j, q⟩ - 1) := hdiffNorm.of_norm
    have hjmul : Multipliable (fun q : Fin (2 ^ j) × ℕ => f ⟨j, q⟩) := by
      have h := Complex.multipliable_one_add_of_summable hdiff
      convert h using 1
      ext q
      ring
    have hfiber : ∀ c : Fin (2 ^ j), HasProd
        (fun n : ℕ => f ⟨j, ⟨c, n⟩⟩)
        (HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ))) := by
      intro c
      have hs := HTGeometry.hasProd_sincProduct (z / ((2 ^ j : ℕ) : ℂ))
      refine hs.congr_fun ?_
      intro n
      dsimp [f]
      rw [dyadicSincDivisorPoint]
      push_cast
      have htwo : ((2 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [htwo]
    have houter := hjmul.hasProd.prod_fiberwise hfiber
    have hfin := hasProd_fintype
      (fun _c : Fin (2 ^ j) => HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)))
    have hpow : (∏ _c : Fin (2 ^ j), HTGeometry.sincProduct
        (z / ((2 ^ j : ℕ) : ℂ))) =
        HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hpow] at hfin
    rw [← houter.unique hfin]
    exact hjmul.hasProd
  have houter := hmul.hasProd.sigma hscale
  rw [dyadicSincCascade_eq_tprod_paired]
  exact houter.tprod_eq.symm

/-! ## Sharp order-one growth -/

/-- Reciprocal-square mass of the positive integer divisor. -/
noncomputable def sincQuadraticMass : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2

theorem sincQuadraticMass_nonneg : 0 ≤ sincQuadraticMass :=
  tsum_nonneg fun _ => by positivity

theorem sincQuadraticMass_summable :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
  summable_one_div_nat_succ_sq'

/-- The Euler sinc product has its natural global quadratic bound. -/
theorem norm_sincProduct_le_exp_quadratic (z : ℂ) :
    ‖HTGeometry.sincProduct z‖ ≤
      Real.exp (sincQuadraticMass * ‖z‖ ^ 2) := by
  let u : ℕ → ℝ := fun n => ‖z‖ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2
  have husum : Summable u := by
    refine (sincQuadraticMass_summable.mul_left (‖z‖ ^ 2)).congr fun n => ?_
    dsimp [u]
    ring
  have hexpsum : Summable (fun n => Real.log (Real.exp (u n))) := by
    simpa using husum
  have hexpmult : Multipliable (fun n => Real.exp (u n)) :=
    Real.multipliable_of_summable_log (fun n => Real.exp_pos _) hexpsum
  have hs := HTGeometry.hasProd_sincProduct z
  calc
    ‖HTGeometry.sincProduct z‖ ≤ ∏' n : ℕ, Real.exp (u n) := by
      apply le_of_tendsto_of_tendsto' hs.norm hexpmult.hasProd
      intro s
      apply Finset.prod_le_prod
      · intro n _
        exact norm_nonneg _
      · intro n _
        calc
          ‖1 - z ^ 2 / ((n : ℂ) + 1) ^ 2‖ ≤
              1 + ‖z ^ 2 / ((n : ℂ) + 1) ^ 2‖ := by
            simpa only [norm_one, add_comm] using
              norm_sub_le (1 : ℂ) (z ^ 2 / ((n : ℂ) + 1) ^ 2)
          _ = 1 + u n := by
            dsimp [u]
            rw [norm_div, norm_pow, norm_pow]
            have hn : ‖(n : ℂ) + 1‖ = ((n + 1 : ℕ) : ℝ) := by
              rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
                Complex.norm_natCast]
            rw [hn]
          _ ≤ Real.exp (u n) := by
            simpa [add_comm] using Real.add_one_le_exp (u n)
    _ = Real.exp (∑' n : ℕ, u n) := by
      simpa only [Real.log_exp] using
        (Real.rexp_tsum_eq_tprod (fun n => Real.exp_pos _) hexpsum).symm
    _ = Real.exp (sincQuadraticMass * ‖z‖ ^ 2) := by
      congr 1
      rw [sincQuadraticMass, ← tsum_mul_right]
      apply tsum_congr
      intro n
      dsimp [u]
      ring

/-- A global exponential-type bound for the normalized Euler sinc product. -/
theorem norm_sincProduct_le_exp_linear (z : ℂ) :
    ‖HTGeometry.sincProduct z‖ ≤ Real.exp
      ((Real.pi + sincQuadraticMass / Real.pi) * ‖z‖) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hZ : 0 ≤ sincQuadraticMass := sincQuadraticMass_nonneg
  have hr : 0 ≤ ‖z‖ := norm_nonneg z
  by_cases hsmall : Real.pi * ‖z‖ ≤ 1
  · have hrpi : ‖z‖ ≤ 1 / Real.pi := by
      rw [le_div_iff₀ hpi]
      simpa [mul_comm] using hsmall
    refine (norm_sincProduct_le_exp_quadratic z).trans
      (Real.exp_le_exp.mpr ?_)
    have hquad : sincQuadraticMass * ‖z‖ ^ 2 ≤
        (sincQuadraticMass / Real.pi) * ‖z‖ := by
      have hsquare : ‖z‖ * ‖z‖ ≤ (1 / Real.pi) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hrpi hr
      calc
        sincQuadraticMass * ‖z‖ ^ 2 =
            sincQuadraticMass * (‖z‖ * ‖z‖) := by ring
        _ ≤ sincQuadraticMass * ((1 / Real.pi) * ‖z‖) :=
          mul_le_mul_of_nonneg_left hsquare hZ
        _ = (sincQuadraticMass / Real.pi) * ‖z‖ := by ring
    nlinarith [mul_nonneg hpi.le hr]
  · have hlarge : 1 ≤ Real.pi * ‖z‖ := le_of_lt (lt_of_not_ge hsmall)
    have hmul : ‖HTGeometry.sincProduct z‖ ≤
        Real.pi * ‖z‖ * ‖HTGeometry.sincProduct z‖ := by
      nlinarith [norm_nonneg (HTGeometry.sincProduct z)]
    have hsin : Real.pi * ‖z‖ * ‖HTGeometry.sincProduct z‖ =
        ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      rw [← HTGeometry.pi_mul_sincProduct, norm_mul, norm_mul]
      norm_num [abs_of_pos hpi]
    calc
      ‖HTGeometry.sincProduct z‖ ≤
          Real.pi * ‖z‖ * ‖HTGeometry.sincProduct z‖ := hmul
      _ = ‖Complex.sin ((Real.pi : ℂ) * z)‖ := hsin
      _ ≤ Real.exp |(((Real.pi : ℂ) * z).im)| :=
        norm_complexSin_le_exp_abs_im _
      _ ≤ Real.exp (Real.pi * ‖z‖) := by
        apply Real.exp_le_exp.mpr
        rw [Complex.mul_im]
        norm_num
        rw [abs_of_pos hpi]
        exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) hpi.le
      _ ≤ Real.exp ((Real.pi + sincQuadraticMass / Real.pi) * ‖z‖) := by
        apply Real.exp_le_exp.mpr
        have hfrac : 0 ≤ sincQuadraticMass / Real.pi := div_nonneg hZ hpi.le
        nlinarith

/-- A dyadic minimum of a constant head and a geometric tail has logarithmic mass. -/
theorem tsum_min_dyadic_le_orderOneShape
    {C Z r : ℝ} (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hr : 0 ≤ r) :
    (∑' j : ℕ, min (C * r) (Z * r ^ 2 / (2 : ℝ) ^ j)) ≤
      (2 * (C + Z) / Real.log 2) *
        ((1 + r) * Real.log (2 + r)) := by
  let M : ℕ := ⌈1 + r⌉₊
  let N : ℕ := Nat.clog 2 M
  let u : ℕ → ℝ := fun j => min (C * r) (Z * r ^ 2 / (2 : ℝ) ^ j)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMpos : 0 < M := by
    change 0 < ⌈1 + r⌉₊
    rw [Nat.ceil_pos]
    linarith
  have hrM : 1 + r ≤ (M : ℝ) := by
    simpa [M] using Nat.le_ceil (1 + r)
  have hMpowNat : M ≤ 2 ^ N := by
    exact Nat.le_pow_clog (by omega) M
  have hMpow : 1 + r ≤ (2 : ℝ) ^ N := by
    exact hrM.trans (by exact_mod_cast hMpowNat)
  have hpowUpperNat : 2 ^ N ≤ 2 * M := by
    by_cases hN0 : N = 0
    · rw [hN0]
      norm_num
      omega
    · obtain ⟨K, hNK⟩ := Nat.exists_eq_succ_of_ne_zero hN0
      have hnot : ¬ M ≤ 2 ^ K := by
        intro hMK
        have hclog : Nat.clog 2 M ≤ K :=
          (Nat.clog_le_iff_le_pow (by omega)).2 hMK
        have : N ≤ K := by simpa only [N] using hclog
        omega
      have hlt : 2 ^ K < M := Nat.lt_of_not_ge hnot
      rw [hNK, pow_succ]
      nlinarith
  have hMlt : (M : ℝ) < r + 2 := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1 + r by linarith)
    change (M : ℝ) < (1 + r) + 1 at hceil
    nlinarith
  have hNlog : (N : ℝ) * Real.log 2 ≤ 2 * Real.log (2 + r) := by
    have hpowUpper : (2 : ℝ) ^ N ≤ 2 * (M : ℝ) := by
      exact_mod_cast hpowUpperNat
    have hpowLt : (2 : ℝ) ^ N < 2 * (r + 2) :=
      hpowUpper.trans_lt (mul_lt_mul_of_pos_left hMlt (by norm_num))
    have hlogPow : Real.log ((2 : ℝ) ^ N) ≤ Real.log (2 * (r + 2)) :=
      Real.log_le_log (by positivity) hpowLt.le
    rw [Real.log_pow] at hlogPow
    have hlogMul : Real.log (2 * (r + 2)) =
        Real.log 2 + Real.log (r + 2) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    rw [hlogMul] at hlogPow
    have hlogTwoLe : Real.log 2 ≤ Real.log (r + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [show 2 + r = r + 2 by ring]
    nlinarith
  have hN : (N : ℝ) ≤ 2 * Real.log (2 + r) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa [mul_comm] using hNlog
  have hu_nonneg : ∀ j, 0 ≤ u j := by
    intro j
    exact le_min (mul_nonneg hC hr) (div_nonneg (mul_nonneg hZ (sq_nonneg r)) (by positivity))
  have huSummable : Summable u := by
    have hgeom : Summable (fun j : ℕ => Z * r ^ 2 * (1 / 2 : ℝ) ^ j) :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
        (Z * r ^ 2)
    refine Summable.of_nonneg_of_le hu_nonneg (fun j => ?_) hgeom
    calc
      u j ≤ Z * r ^ 2 / (2 : ℝ) ^ j := min_le_right _ _
      _ = Z * r ^ 2 * (1 / 2 : ℝ) ^ j := by
        rw [one_div, inv_pow]
        ring
  have hhead : (∑ j ∈ Finset.range N, u j) ≤ (N : ℝ) * (C * r) := by
    calc
      (∑ j ∈ Finset.range N, u j) ≤ ∑ _j ∈ Finset.range N, C * r := by
        exact Finset.sum_le_sum fun j _ => min_le_left _ _
      _ = (N : ℝ) * (C * r) := by simp
  have htailSummable : Summable (fun j : ℕ =>
      Z * r ^ 2 / (2 : ℝ) ^ (j + N)) := by
    refine ((summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
        (Z * r ^ 2 / (2 : ℝ) ^ N)).congr fun j => ?_
    rw [pow_add, one_div, inv_pow]
    field_simp
  have htailExact : (∑' j : ℕ, Z * r ^ 2 / (2 : ℝ) ^ (j + N)) =
      2 * Z * r ^ 2 / (2 : ℝ) ^ N := by
    rw [show (fun j : ℕ => Z * r ^ 2 / (2 : ℝ) ^ (j + N)) =
        fun j : ℕ => (Z * r ^ 2 / (2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ j by
      funext j
      rw [pow_add, one_div, inv_pow]
      field_simp]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]
    norm_num
    ring
  have htail : (∑' j : ℕ, u (j + N)) ≤ 2 * Z * r := by
    have hcomp : (∑' j : ℕ, u (j + N)) ≤
        ∑' j : ℕ, Z * r ^ 2 / (2 : ℝ) ^ (j + N) := by
      apply Summable.tsum_le_tsum
      · intro j
        exact min_le_right _ _
      · exact huSummable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
      · exact htailSummable
    rw [htailExact] at hcomp
    have hpowPos : 0 < (2 : ℝ) ^ N := by positivity
    have hrpow : r ^ 2 / (2 : ℝ) ^ N ≤ r := by
      rw [div_le_iff₀ hpowPos]
      have hrle : r ≤ (2 : ℝ) ^ N := by linarith [hMpow]
      nlinarith
    have hscale : (2 * Z) * (r ^ 2 / (2 : ℝ) ^ N) ≤ (2 * Z) * r :=
      mul_le_mul_of_nonneg_left hrpow (mul_nonneg (by norm_num) hZ)
    calc
      (∑' j : ℕ, u (j + N)) ≤ 2 * Z * r ^ 2 / (2 : ℝ) ^ N := hcomp
      _ = (2 * Z) * (r ^ 2 / (2 : ℝ) ^ N) := by ring
      _ ≤ (2 * Z) * r := hscale
      _ = 2 * Z * r := by ring
  have hsplit := huSummable.sum_add_tsum_nat_add N
  have hsum : (∑' j : ℕ, u j) ≤ (N : ℝ) * (C * r) + 2 * Z * r := by
    rw [← hsplit]
    exact add_le_add hhead htail
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hheadShape : (N : ℝ) * (C * r) ≤
      (2 * C / Real.log 2) * (r * Real.log (2 + r)) := by
    have hmul := mul_le_mul_of_nonneg_right hN (mul_nonneg hC hr)
    calc
      (N : ℝ) * (C * r) ≤
          (2 * Real.log (2 + r) / Real.log 2) * (C * r) := hmul
      _ = (2 * C / Real.log 2) * (r * Real.log (2 + r)) := by ring
  have htailShape : 2 * Z * r ≤
      (2 * Z / Real.log 2) * ((1 + r) * Real.log (2 + r)) := by
    have hlogLower : Real.log 2 ≤ Real.log (2 + r) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hshape : r * Real.log 2 ≤ (1 + r) * Real.log (2 + r) := by
      nlinarith
    have hmul : (2 * Z / Real.log 2) * (r * Real.log 2) ≤
        (2 * Z / Real.log 2) * ((1 + r) * Real.log (2 + r)) :=
      mul_le_mul_of_nonneg_left hshape
        (div_nonneg (mul_nonneg (by norm_num) hZ) hlog2.le)
    calc
      2 * Z * r = (2 * Z / Real.log 2) * (r * Real.log 2) := by field_simp
      _ ≤ (2 * Z / Real.log 2) * ((1 + r) * Real.log (2 + r)) := hmul
  change (∑' j : ℕ, u j) ≤ _
  calc
    (∑' j : ℕ, u j) ≤ (N : ℝ) * (C * r) + 2 * Z * r := hsum
    _ ≤ (2 * C / Real.log 2) * (r * Real.log (2 + r)) +
        (2 * Z / Real.log 2) * ((1 + r) * Real.log (2 + r)) :=
      add_le_add hheadShape htailShape
    _ ≤ (2 * (C + Z) / Real.log 2) *
        ((1 + r) * Real.log (2 + r)) := by
      have hrlog : 0 ≤ r * Real.log (2 + r) := mul_nonneg hr hlog
      have hle : r * Real.log (2 + r) ≤
          (1 + r) * Real.log (2 + r) := by nlinarith
      have hcoef : 0 ≤ 2 * C / Real.log 2 := div_nonneg (mul_nonneg (by norm_num) hC) hlog2.le
      have hfirst : (2 * C / Real.log 2) * (r * Real.log (2 + r)) ≤
          (2 * C / Real.log 2) * ((1 + r) * Real.log (2 + r)) :=
        mul_le_mul_of_nonneg_left hle hcoef
      calc
        (2 * C / Real.log 2) * (r * Real.log (2 + r)) +
            (2 * Z / Real.log 2) * ((1 + r) * Real.log (2 + r)) ≤
          (2 * C / Real.log 2) * ((1 + r) * Real.log (2 + r)) +
            (2 * Z / Real.log 2) * ((1 + r) * Real.log (2 + r)) :=
          add_le_add hfirst le_rfl
        _ = (2 * (C + Z) / Real.log 2) *
            ((1 + r) * Real.log (2 + r)) := by ring

theorem summable_min_dyadic {C Z r : ℝ}
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hr : 0 ≤ r) :
    Summable (fun j : ℕ => min (C * r) (Z * r ^ 2 / (2 : ℝ) ^ j)) := by
  have hgeom : Summable (fun j : ℕ => Z * r ^ 2 * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
      (Z * r ^ 2)
  refine Summable.of_nonneg_of_le (fun j => le_min (mul_nonneg hC hr)
    (div_nonneg (mul_nonneg hZ (sq_nonneg r)) (by positivity))) (fun j => ?_) hgeom
  calc
    min (C * r) (Z * r ^ 2 / (2 : ℝ) ^ j) ≤
        Z * r ^ 2 / (2 : ℝ) ^ j := min_le_right _ _
    _ = Z * r ^ 2 * (1 / 2 : ℝ) ^ j := by
      rw [one_div, inv_pow]
      ring

/-- One dyadic scale is exactly a finite power of the Euler sinc product. -/
theorem hasProd_dyadicSinc_scale (z : ℂ) (j : ℕ) : HasProd
    (fun q : Fin (2 ^ j) × ℕ =>
      1 - z ^ 2 / dyadicSincDivisorPoint ⟨j, q⟩ ^ 2)
    (HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j)) := by
  let f : (Fin (2 ^ j) × ℕ) → ℂ := fun q =>
    1 - z ^ 2 / dyadicSincDivisorPoint ⟨j, q⟩ ^ 2
  have hdiffNorm : Summable (fun q : Fin (2 ^ j) × ℕ => ‖f q - 1‖) := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨?_, Summable.of_finite⟩
    intro c
    refine (summable_one_div_nat_succ_sq'.mul_left
      (‖z‖ ^ 2 / (((2 ^ j : ℕ) : ℝ) ^ 2))).congr fun n => ?_
    dsimp [f]
    rw [show 1 - z ^ 2 / dyadicSincDivisorPoint ⟨j, ⟨c, n⟩⟩ ^ 2 - 1 =
        -(z ^ 2 / dyadicSincDivisorPoint ⟨j, ⟨c, n⟩⟩ ^ 2) by ring,
      norm_neg, norm_div, norm_pow, norm_pow, dyadicSincDivisorPoint_norm]
    dsimp
    push_cast
    field_simp
  have hdiff : Summable (fun q : Fin (2 ^ j) × ℕ => f q - 1) :=
    hdiffNorm.of_norm
  have hjmul : Multipliable f := by
    have h := Complex.multipliable_one_add_of_summable hdiff
    convert h using 1
    ext q
    ring
  have hfiber : ∀ c : Fin (2 ^ j), HasProd
      (fun n : ℕ => f ⟨c, n⟩)
      (HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ))) := by
    intro c
    have hs := HTGeometry.hasProd_sincProduct (z / ((2 ^ j : ℕ) : ℂ))
    refine hs.congr_fun ?_
    intro n
    dsimp [f]
    rw [dyadicSincDivisorPoint]
    push_cast
    have htwo : ((2 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [htwo]
  have houter := hjmul.hasProd.prod_fiberwise hfiber
  have hfin := hasProd_fintype
    (fun _c : Fin (2 ^ j) => HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)))
  have hpow : (∏ _c : Fin (2 ^ j), HTGeometry.sincProduct
      (z / ((2 ^ j : ℕ) : ℂ))) =
      HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow] at hfin
  rw [← houter.unique hfin]
  exact hjmul.hasProd

theorem multipliable_dyadicSinc_scales (z : ℂ) : Multipliable
    (fun j : ℕ => HTGeometry.sincProduct
      (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j)) := by
  let f : DyadicSincIndex → ℂ := fun q =>
    1 - z ^ 2 / dyadicSincDivisorPoint q ^ 2
  have hpos := multipliable_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable z
  have hneg := multipliable_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable (-z)
  have hmulRaw : Multipliable (fun q : DyadicSincIndex =>
      weierstrassE1 (z / dyadicSincDivisorPoint q) *
        weierstrassE1 (-z / dyadicSincDivisorPoint q)) := hpos.mul hneg
  have hmul : Multipliable f := hmulRaw.congr fun q => dyadicSinc_pairedFactor z q
  have houter := hmul.hasProd.sigma (fun j => hasProd_dyadicSinc_scale z j)
  exact houter.multipliable

private noncomputable def sincLinearType : ℝ :=
  Real.pi + sincQuadraticMass / Real.pi

private theorem sincLinearType_nonneg : 0 ≤ sincLinearType := by
  dsimp [sincLinearType]
  exact add_nonneg Real.pi_pos.le
    (div_nonneg sincQuadraticMass_nonneg Real.pi_pos.le)

private theorem sincLinearType_pos : 0 < sincLinearType := by
  dsimp [sincLinearType]
  exact add_pos_of_pos_of_nonneg Real.pi_pos
    (div_nonneg sincQuadraticMass_nonneg Real.pi_pos.le)

theorem norm_dyadicSinc_scale_le_exp_min (z : ℂ) (j : ℕ) :
    ‖HTGeometry.sincProduct (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j)‖ ≤
      Real.exp (min (sincLinearType * ‖z‖)
        (sincQuadraticMass * ‖z‖ ^ 2 / (2 : ℝ) ^ j)) := by
  let w : ℂ := z / ((2 ^ j : ℕ) : ℂ)
  have hw : ‖w‖ = ‖z‖ / (2 : ℝ) ^ j := by
    dsimp [w]
    rw [norm_div, Complex.norm_natCast]
    norm_num
  have hlin0 := norm_sincProduct_le_exp_linear w
  have hquad0 := norm_sincProduct_le_exp_quadratic w
  have hlin : ‖HTGeometry.sincProduct w ^ (2 ^ j)‖ ≤
      Real.exp (sincLinearType * ‖z‖) := by
    rw [norm_pow]
    calc
      ‖HTGeometry.sincProduct w‖ ^ (2 ^ j) ≤
          Real.exp (sincLinearType * ‖w‖) ^ (2 ^ j) :=
        pow_le_pow_left₀ (norm_nonneg _) hlin0 _
      _ = Real.exp ((2 ^ j : ℕ) * (sincLinearType * ‖w‖)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (sincLinearType * ‖z‖) := by
        congr 1
        rw [hw]
        push_cast
        field_simp
  have hquad : ‖HTGeometry.sincProduct w ^ (2 ^ j)‖ ≤
      Real.exp (sincQuadraticMass * ‖z‖ ^ 2 / (2 : ℝ) ^ j) := by
    rw [norm_pow]
    calc
      ‖HTGeometry.sincProduct w‖ ^ (2 ^ j) ≤
          Real.exp (sincQuadraticMass * ‖w‖ ^ 2) ^ (2 ^ j) :=
        pow_le_pow_left₀ (norm_nonneg _) hquad0 _
      _ = Real.exp ((2 ^ j : ℕ) * (sincQuadraticMass * ‖w‖ ^ 2)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (sincQuadraticMass * ‖z‖ ^ 2 / (2 : ℝ) ^ j) := by
        congr 1
        rw [hw]
        push_cast
        field_simp
  change ‖HTGeometry.sincProduct w ^ (2 ^ j)‖ ≤ _
  by_cases hle : sincLinearType * ‖z‖ ≤
      sincQuadraticMass * ‖z‖ ^ 2 / (2 : ℝ) ^ j
  · rw [min_eq_left hle]
    exact hlin
  · rw [min_eq_right (le_of_not_ge hle)]
    exact hquad

/-- The dyadic sinc cascade has the sharp order-one envelope `exp(O(r log r))`. -/
theorem orderOneEnvelope_dyadicSincCascade : OrderOneEnvelope dyadicSincCascade := by
  let C : ℝ := sincLinearType
  let Z : ℝ := sincQuadraticMass
  let K : ℝ := 2 * (C + Z) / Real.log 2
  have hC : 0 ≤ C := sincLinearType_nonneg
  have hZ : 0 ≤ Z := sincQuadraticMass_nonneg
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos (by norm_num)
      (add_pos_of_pos_of_nonneg sincLinearType_pos hZ))
      (Real.log_pos (by norm_num))
  refine ⟨K, hK, fun z => ?_⟩
  let u : ℕ → ℝ := fun j => min (C * ‖z‖) (Z * ‖z‖ ^ 2 / (2 : ℝ) ^ j)
  have husum : Summable u := summable_min_dyadic hC hZ (norm_nonneg z)
  have hexpsum : Summable (fun j => Real.log (Real.exp (u j))) := by
    simpa using husum
  have hexpmult : Multipliable (fun j => Real.exp (u j)) :=
    Real.multipliable_of_summable_log (fun j => Real.exp_pos _) hexpsum
  have hscales := multipliable_dyadicSinc_scales z
  rw [dyadicSincCascade_eq_tprod_sinc_scales]
  calc
    ‖∏' j : ℕ, HTGeometry.sincProduct
        (z / ((2 ^ j : ℕ) : ℂ)) ^ (2 ^ j)‖ ≤
        ∏' j : ℕ, Real.exp (u j) := by
      apply le_of_tendsto_of_tendsto' hscales.hasProd.norm hexpmult.hasProd
      intro s
      apply Finset.prod_le_prod
      · intro j _
        exact norm_nonneg _
      · intro j _
        exact norm_dyadicSinc_scale_le_exp_min z j
    _ = Real.exp (∑' j : ℕ, u j) := by
      simpa only [Real.log_exp] using
        (Real.rexp_tsum_eq_tprod (fun j => Real.exp_pos _) hexpsum).symm
    _ ≤ Real.exp (K * ((1 + ‖z‖) * Real.log (2 + ‖z‖))) := by
      apply Real.exp_le_exp.mpr
      exact tsum_min_dyadic_le_orderOneShape hC hZ (norm_nonneg z)
    _ = Real.exp (orderOneWeight K z) := by
      rw [orderOneWeight]
      ring

/-! ## Divisor multiplicity and logarithmic cumulative budget -/

/-- Physical positive node on dyadic scale `j`. -/
def dyadicSincNode (j n : ℕ) : ℂ := ((2 ^ j * (n + 1) : ℕ) : ℂ)

@[simp] theorem dyadicSincDivisorPoint_copy (j n : ℕ) (c : Fin (2 ^ j)) :
    dyadicSincDivisorPoint ⟨j, (c, n)⟩ = dyadicSincNode j n := by
  rfl

theorem dyadicSincNode_ne_zero (j n : ℕ) : dyadicSincNode j n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [dyadicSincNode, Complex.norm_natCast]
  positivity

/-- Every scale contributes all its `2^j` copies to the node fiber. -/
theorem dyadicSincDivisorPoint_fiber_ncard_ge (j n : ℕ) :
    2 ^ j ≤ ({q : DyadicSincIndex |
      dyadicSincDivisorPoint q = dyadicSincNode j n} : Set DyadicSincIndex).ncard := by
  let S : Set DyadicSincIndex := {q | dyadicSincDivisorPoint q = dyadicSincNode j n}
  have hSfin : S.Finite :=
    GaloisForLFunctions.CountableDivisor.finite_fiber
      dyadicSincDivisorPoint_locallyFinite (dyadicSincNode j n)
  letI : Fintype S := hSfin.fintype
  let e : Fin (2 ^ j) → S := fun c =>
    ⟨⟨j, (c, n)⟩, dyadicSincDivisorPoint_copy j n c⟩
  have he : Function.Injective e := by
    intro c d h
    apply Fin.ext
    exact congrArg (fun q : S => (q.1.2.1 : ℕ)) h
  calc
    2 ^ j = Nat.card (Fin (2 ^ j)) := by simp
    _ ≤ Nat.card S := Nat.card_le_card_of_injective e he
    _ = S.ncard := Nat.card_coe_set_eq S

theorem analyticOrderAt_dyadicSincCascade_ge (j n : ℕ) :
    ((2 ^ j : ℕ) : ℕ∞) ≤ analyticOrderAt dyadicSincCascade (dyadicSincNode j n) := by
  let w : ℂ := dyadicSincNode j n
  have hw : w ≠ 0 := dyadicSincNode_ne_zero j n
  have hposAnalytic : AnalyticAt ℂ dyadicSincPositiveProduct w :=
    analyticOnNhd_dyadicSincPositiveProduct w (Set.mem_univ w)
  have hnegAnalytic : AnalyticAt ℂ (fun z : ℂ => dyadicSincPositiveProduct (-z)) w := by
    have hneg : AnalyticAt ℂ (fun z : ℂ => -z) w := by fun_prop
    exact (analyticOnNhd_dyadicSincPositiveProduct (-w) (Set.mem_univ (-w))).comp hneg
  have hnegNe : dyadicSincPositiveProduct (-w) ≠ 0 := by
    apply canonicalProductE1Indexed_ne_zero dyadicSincDivisorPoint
      dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_inv_sq_summable
    intro q h
    have hre := congrArg Complex.re h
    have hwpos : 0 < w.re := by
      change 0 < ((((2 ^ j * (n + 1) : ℕ) : ℂ)).re)
      rw [Complex.natCast_re]
      exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) (Nat.succ_pos n)
    have hqpos : 0 < (dyadicSincDivisorPoint q).re := by
      change 0 < ((((2 ^ q.1 * (q.2.2 + 1) : ℕ) : ℂ)).re)
      rw [Complex.natCast_re]
      exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) (Nat.succ_pos q.2.2)
    simp only [Complex.neg_re] at hre
    linarith
  have hfirst := analyticOrderAt_canonicalProductE1Indexed
    dyadicSincDivisorPoint_ne_zero dyadicSincDivisorPoint_locallyFinite
    dyadicSincDivisorPoint_inv_sq_summable hw
  have hfiber := dyadicSincDivisorPoint_fiber_ncard_ge j n
  change ((2 ^ j : ℕ) : ℕ∞) ≤ analyticOrderAt
    (fun z : ℂ => dyadicSincPositiveProduct z * dyadicSincPositiveProduct (-z)) w
  have hfun : (fun z : ℂ => dyadicSincPositiveProduct z * dyadicSincPositiveProduct (-z)) =
      dyadicSincPositiveProduct * (fun z : ℂ => dyadicSincPositiveProduct (-z)) := rfl
  rw [hfun, analyticOrderAt_mul hposAnalytic hnegAnalytic]
  change ((2 ^ j : ℕ) : ℕ∞) ≤
    analyticOrderAt (canonicalProductE1Indexed dyadicSincDivisorPoint) w +
      analyticOrderAt (fun z : ℂ => dyadicSincPositiveProduct (-z)) w
  rw [hfirst, hnegAnalytic.analyticOrderAt_eq_zero.mpr hnegNe, add_zero]
  exact_mod_cast hfiber

/-- Cumulative independent dyadic jet weight below radius `2^K`. -/
def dyadicLogJetBudget (K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range K, 2 ^ (K - (j + 1)) * 2 ^ j

/-- The disjoint odd-multiple nodes carry exactly `K·2^(K-1)` prescribed jet weight. -/
theorem dyadicLogJetBudget_eq (K : ℕ) :
    dyadicLogJetBudget K = K * 2 ^ (K - 1) := by
  rcases K with _ | K
  · simp [dyadicLogJetBudget]
  · rw [dyadicLogJetBudget]
    have hterm : ∀ j ∈ Finset.range (K + 1),
        2 ^ (K + 1 - (j + 1)) * 2 ^ j = 2 ^ K := by
      intro j hj
      rw [← pow_add]
      congr 1
      simp only [Finset.mem_range] at hj
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    simp

end GaloisForLFunctions.HTGeometry
