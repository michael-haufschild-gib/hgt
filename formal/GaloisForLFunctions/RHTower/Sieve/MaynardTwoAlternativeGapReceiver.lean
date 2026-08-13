import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellAllAmplitudeReceiver

/-!
# Maynard's gap receiver needs only two large-value alternatives

For Route T the selected-cell reserve makes Maynard's additive-energy `R*` alternative redundant.
A large Perron error forces the cardinality to violate the logarithmically normalized first count;
the second count then cancels the amplitude exactly against the `L²` error estimate.  This module
formalizes that cancellation in the height and ambient-scale variables used by the literal count.
-/

noncomputable section
namespace RHTower.Sieve

open Filter Topology

/-- Receiver-facing two-way alternative.  The first branch includes the logarithmic factor needed
to contradict a large Perron error; the second is Maynard's `L²` count scale. -/
def IsRouteTMaynardTwoAlternative
    (q : ℕ) (R T x sigma : ℝ) : Prop :=
  R * (Real.log T) ^ q < x ^ (1 - sigma) ∨
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma)

/-- A strict height-exponent reserve converts the normalized selected-cell output to the exact
ambient-scale two-way receiver. -/
theorem routeT_two_alternative_of_reserved_height_count
    {q : ℕ} {R T x mu sigma reserve : ℝ}
    (hT : 1 < T) (hx : x = T ^ mu) (hreserve : 0 < reserve)
    (hcount :
      R * (Real.log T) ^ q ≤ T ^ (mu * (1 - sigma) - reserve / 2) ∨
        R ≤ T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * sigma) - reserve / 2)) :
    IsRouteTMaynardTwoAlternative q R T x sigma := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT.le
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have hT1 : 1 ≤ T := hT.le
  rcases hcount with hfirst | hsecond
  · left
    calc
      R * (Real.log T) ^ q ≤
          T ^ (mu * (1 - sigma) - reserve / 2) := hfirst
      _ < T ^ (mu * (1 - sigma)) := by
        exact Real.rpow_lt_rpow_of_exponent_lt hT
          (by linarith)
      _ = x ^ (1 - sigma) := by rw [hx, Real.rpow_mul hT0]
  · right
    let e : ℝ := 1 + routeTGapMomentNu - 2 * sigma
    calc
      R ≤ T ^ (1 + mu * e - reserve / 2) := by simpa only [e] using hsecond
      _ ≤ T ^ (1 + mu * e) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = T ^ (1 : ℝ) * T ^ (mu * e) := Real.rpow_add hTpos 1 (mu * e)
      _ = T * (T ^ mu) ^ e := by rw [Real.rpow_one, Real.rpow_mul hT0]
      _ = T * x ^ e := by rw [hx]
      _ = T * x ^ (1 + routeTGapMomentNu - 2 * sigma) := rfl

/-- At a genuinely large Perron error, the first alternative is impossible, so the `L²` count is
forced.  This is the point where Route T eliminates Maynard's `R*` branch. -/
theorem routeT_second_alternative_of_large_error
    {q : ℕ} {R T x sigma : ℝ}
    (hlarge : x ^ (1 - sigma) ≤ R * (Real.log T) ^ q)
    (halt : IsRouteTMaynardTwoAlternative q R T x sigma) :
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma) := by
  rcases halt with hfirst | hsecond
  · exact False.elim ((not_lt_of_ge hlarge) hfirst)
  · exact hsecond

/-- Exact amplitude cancellation in Maynard's `L²` receiver.  Multiplying the second count by the
`x^(2 sigma - 1 + eps)` bad-set factor removes `sigma` completely. -/
theorem routeT_second_count_L2_bad_measure
    {B R T x sigma eps : ℝ}
    (hT : 0 ≤ T) (hx : 0 < x) (hR : 0 ≤ R)
    (hmeasure : B ≤ x ^ (2 * sigma - 1 + eps) * R)
    (hsecond : R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma)) :
    B ≤ T * x ^ (routeTGapMomentNu + eps) := by
  have hpow0 : 0 ≤ x ^ (2 * sigma - 1 + eps) := Real.rpow_nonneg hx.le _
  calc
    B ≤ x ^ (2 * sigma - 1 + eps) * R := hmeasure
    _ ≤ x ^ (2 * sigma - 1 + eps) *
        (T * x ^ (1 + routeTGapMomentNu - 2 * sigma)) :=
      mul_le_mul_of_nonneg_left hsecond hpow0
    _ = T * (x ^ (2 * sigma - 1 + eps) *
        x ^ (1 + routeTGapMomentNu - 2 * sigma)) := by ring
    _ = T * x ^ ((2 * sigma - 1 + eps) +
        (1 + routeTGapMomentNu - 2 * sigma)) := by
      congr 1
      exact (Real.rpow_add hx _ _).symm
    _ = T * x ^ (routeTGapMomentNu + eps) := by ring

/-- Combined two-alternative receiver: a large error and the selected-cell alternatives force the
amplitude-free `L²` bad-set bound. -/
theorem routeT_large_error_L2_bad_measure
    {q : ℕ} {B R T x sigma eps : ℝ}
    (hT : 0 ≤ T) (hx : 0 < x) (hR : 0 ≤ R)
    (hlarge : x ^ (1 - sigma) ≤ R * (Real.log T) ^ q)
    (halt : IsRouteTMaynardTwoAlternative q R T x sigma)
    (hmeasure : B ≤ x ^ (2 * sigma - 1 + eps) * R) :
    B ≤ T * x ^ (routeTGapMomentNu + eps) := by
  exact routeT_second_count_L2_bad_measure hT hx hR hmeasure
    (routeT_second_alternative_of_large_error hlarge halt)

/-- Multiplication by the dyadic gap length cancels the Perron height once
`T ≤ tau * log(x)^b`. -/
theorem routeT_bad_measure_to_dyadic_gap_square
    {B D T tau x eps : ℝ} {b : ℕ}
    (htau : 0 < tau) (hx : 0 < x) (hlog : 0 ≤ Real.log x)
    (hD : D ≤ x / tau)
    (hB : B ≤ T * x ^ (routeTGapMomentNu + eps))
    (hT : T ≤ tau * (Real.log x) ^ b)
    (hB0 : 0 ≤ B) :
    D * B ≤ x ^ (1 + routeTGapMomentNu + eps) * (Real.log x) ^ b := by
  have hxpow0 : 0 ≤ x ^ (routeTGapMomentNu + eps) := Real.rpow_nonneg hx.le _
  have hheight : T * x ^ (routeTGapMomentNu + eps) ≤
      (tau * (Real.log x) ^ b) * x ^ (routeTGapMomentNu + eps) :=
    mul_le_mul_of_nonneg_right hT hxpow0
  have hB' := hB.trans hheight
  have hD0 : 0 ≤ x / tau := div_nonneg hx.le htau.le
  have hxmul : x * x ^ (routeTGapMomentNu + eps) =
      x ^ (1 + routeTGapMomentNu + eps) := by
    calc
      x * x ^ (routeTGapMomentNu + eps) =
          x ^ (1 : ℝ) * x ^ (routeTGapMomentNu + eps) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (routeTGapMomentNu + eps)) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (1 + routeTGapMomentNu + eps) := by congr 1 <;> ring
  calc
    D * B ≤ (x / tau) * B := mul_le_mul_of_nonneg_right hD hB0
    _ ≤ (x / tau) *
        ((tau * (Real.log x) ^ b) * x ^ (routeTGapMomentNu + eps)) :=
      mul_le_mul_of_nonneg_left hB' hD0
    _ = (x * x ^ (routeTGapMomentNu + eps)) * (Real.log x) ^ b := by
      field_simp [htau.ne']
    _ = x ^ (1 + routeTGapMomentNu + eps) * (Real.log x) ^ b := by
      rw [hxmul]

end RHTower.Sieve
