import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsHilbertSchmidtAboveInverseRootTwo
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# The columns of the chain in Mellin coordinates

The `k`-th column of the centred damping chain is a difference of two dilations of one source.
With `K = k + 1` and `N = n + 1`, `C_η(n, k) = (K/N) Δ_K(N)`, where
`Δ_K(x) = K^{−η} P(x/K) − (K+1)^{−η} P(x/(K+1))` and `P(x) = A_η(⌊x⌋) − ρ_η x` is the source at a
real argument (`centeredRow_eq_columnProfile`).

* **Discrete to continuous** (`sum_sq_centeredRow_le_integral`): on `[N, N+1)` the floors in `Δ_K`
  do not move, so `Σ_{n<T} C(n,k)² ≤ 8K² ∫_0^∞ Δ_K(x)² x^{−2} dx + 4K^{−2η}`.
* **Fractional-part series** (`sourceProfile_eq_tsum`): `P(x) = −Σ_d μ(d) d^{−η} {x/d}` for `x ≥ 0`;
  hence `|P(x)| ≤ ζ(1+η) x`, and with the sign-blind bound `|P(x)| ≤ B min(x^η, x^{1−η})` for
  `½ < η < 1` (`abs_sourceProfile_le_bound`).
* **Mellin transform** (`mellin_fractSeries`): on `−1 < Re s < 0`, a series `Σ_d a_d {x/(d+1)}` with
  `Σ_d |a_d| (d+1)^{Re s} < ∞` has Mellin transform `(Σ_d a_d (d+1)^s) ζ(−s)/s`.  For the source,
  `|M P(−½ + it)| ≤ ζ(η + ½) |ζ(½ − it)| / |½ − it|` (`norm_mellin_sourceProfile_le`), and the column
  multiplies it by the dilation symbol `K^{s−η} − (K+1)^{s−η}` (`mellin_columnProfile_eq`).
* **Plancherel** (`integral_sq_div_sq_eq_mellin`): a measurable profile with
  `|f(x)| ≤ B min(x^a, x^{1−a})`, `½ < a < 1`, has
  `∫_0^∞ f(x)² x^{−2} dx = (1/2π) ∫ |M f(−½ + it)|² dt`.

The only arithmetic input is `|μ| ≤ 1`: the Möbius signs are not used.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The source and the columns at a real argument -/

/-- The source at a real argument: `P_η(x) = A_η(⌊x⌋) − ρ_η x`. -/
def sourceProfile (η x : ℝ) : ℝ :=
  arithmeticDampingPrefix η ⌊x⌋₊ - (RHTower.pmPowerDampedDivisorDensity η).re * x

/-- The column profile `Δ_K(x) = K^{−η} P(x/K) − (K+1)^{−η} P(x/(K+1))`. -/
def columnProfile (η K x : ℝ) : ℝ :=
  K ^ (-η) * sourceProfile η (x / K) - (K + 1) ^ (-η) * sourceProfile η (x / (K + 1))

/-- **The column identity**: `C_η(n, k) = (K/N) Δ_K(N)` with `K = k + 1`, `N = n + 1`. -/
theorem centeredRow_eq_columnProfile (η : ℝ) (n k : ℕ) :
    arithmeticDampingCenteredRow η n k =
      ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) *
        columnProfile η ((k + 1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ) := by
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hK' : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have e1 : ((k + 1 : ℕ) : ℝ) + 1 = ((k + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
  unfold arithmeticDampingCenteredRow arithmeticDampingTransition arithmeticDampingEntrance
    columnProfile sourceProfile
  rw [e1, Nat.floor_div_eq_div, Nat.floor_div_eq_div,
    show -1 - η = -η - 1 by ring, Real.rpow_sub_one hK.ne', Real.rpow_sub_one hK'.ne']
  field_simp
  ring

theorem measurable_sourceProfile (η : ℝ) : Measurable (sourceProfile η) := by
  unfold sourceProfile
  exact ((measurable_from_nat (f := arithmeticDampingPrefix η)).comp Nat.measurable_floor).sub
    (measurable_const.mul measurable_id)

theorem measurable_columnProfile (η K : ℝ) : Measurable (columnProfile η K) := by
  unfold columnProfile
  exact (measurable_const.mul ((measurable_sourceProfile η).comp (measurable_id.div_const K))).sub
    (measurable_const.mul ((measurable_sourceProfile η).comp (measurable_id.div_const (K + 1))))

/-! ### Discrete to continuous -/

/-- On `[N, N + 1)` the floor of `x/K` does not move. -/
theorem floor_div_eq_of_mem {N K : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ x) (hx' : x < N + 1) :
    ⌊x / K⌋₊ = ⌊(N : ℝ) / K⌋₊ := by
  have h0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg N) hx
  rw [Nat.floor_div_natCast, Nat.floor_div_natCast, Nat.floor_natCast,
    (Nat.floor_eq_iff h0).2 ⟨hx, hx'⟩]

/-- Between two points with the same floor the source is linear with slope `−ρ`. -/
theorem sourceProfile_eq_of_floor_eq (η : ℝ) {x y : ℝ} (h : ⌊x⌋₊ = ⌊y⌋₊) :
    sourceProfile η x = sourceProfile η y - (RHTower.pmPowerDampedDivisorDensity η).re * (x - y) := by
  unfold sourceProfile; rw [h]; ring

/-- On `[N, N + 1)` the column profile differs from its value at `N` by a linear term. -/
theorem columnProfile_eq_of_mem (η : ℝ) {N K : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ x) (hx' : x < N + 1) :
    columnProfile η K x = columnProfile η K N -
      (RHTower.pmPowerDampedDivisorDensity η).re * (x - N) *
        ((K : ℝ) ^ (-η) / K - ((K : ℝ) + 1) ^ (-η) / ((K : ℝ) + 1)) := by
  have h1 := sourceProfile_eq_of_floor_eq η (floor_div_eq_of_mem (K := K) hx hx')
  have h2 := sourceProfile_eq_of_floor_eq η (floor_div_eq_of_mem (K := K + 1) hx hx')
  have hK1 : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
  rw [hK1] at h2
  unfold columnProfile
  rw [h1, h2]
  ring

/-- **Pointwise comparison**: for `x ∈ [N, N+1)`,
`C(n,k)² ≤ 8K² Δ_K(x)²/x² + 2(K^{−η})²/N²`. -/
theorem sq_centeredRow_le_of_mem {η : ℝ} (hη : 0 < η) (n k : ℕ) {x : ℝ}
    (hx : ((n + 1 : ℕ) : ℝ) ≤ x) (hx' : x < ((n + 1 : ℕ) : ℝ) + 1) :
    arithmeticDampingCenteredRow η n k ^ 2 ≤
      8 * ((k + 1 : ℕ) : ℝ) ^ 2 * (columnProfile η ((k + 1 : ℕ) : ℝ) x ^ 2 / x ^ 2) +
        2 * (((k + 1 : ℕ) : ℝ) ^ (-η)) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hshift := columnProfile_eq_of_mem η (N := n + 1) (K := k + 1) hx hx'
  rw [centeredRow_eq_columnProfile]
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hK : 0 < K := by linarith
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hx0 : 0 < x := by linarith
  set ρ := (RHTower.pmPowerDampedDivisorDensity η).re with hρdef
  have hρ0 : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  have hρ1 : ρ ≤ 1 := density_re_le_one hη
  have hKη : 0 ≤ K ^ (-η) := Real.rpow_nonneg hK.le _
  have hK1η : 0 ≤ (K + 1) ^ (-η) := Real.rpow_nonneg (by linarith) _
  have hmono : (K + 1) ^ (-η) ≤ K ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos hK (by linarith) (by linarith)
  set ε := K ^ (-η) / K - (K + 1) ^ (-η) / (K + 1) with hεdef
  have hε0 : 0 ≤ ε := by
    rw [hεdef, sub_nonneg, div_le_div_iff₀ (by linarith) hK]
    nlinarith [mul_le_mul_of_nonneg_right hmono hK.le]
  have hε1 : ε ≤ K ^ (-η) / K := by
    have : 0 ≤ (K + 1) ^ (-η) / (K + 1) := div_nonneg hK1η (by linarith)
    linarith
  set D := columnProfile η K N
  set Dx := columnProfile η K x
  have hD : D = Dx + ρ * (x - N) * ε := by linarith
  have hr0 : 0 ≤ ρ * (x - N) * ε := mul_nonneg (mul_nonneg hρ0.le (by linarith)) hε0
  have hr1 : ρ * (x - N) * ε ≤ K ^ (-η) / K := by
    have hxN : x - N ≤ 1 := by linarith
    have hxN0 : 0 ≤ x - N := by linarith
    calc ρ * (x - N) * ε ≤ 1 * 1 * ε := by
          apply mul_le_mul_of_nonneg_right _ hε0
          exact mul_le_mul hρ1 hxN hxN0 zero_le_one
      _ ≤ K ^ (-η) / K := by linarith
  have hD2 : D ^ 2 ≤ 2 * Dx ^ 2 + 2 * (K ^ (-η) / K) ^ 2 := by
    have h := add_sq_le_two Dx (ρ * (x - N) * ε)
    have hsq : (ρ * (x - N) * ε) ^ 2 ≤ (K ^ (-η) / K) ^ 2 := pow_le_pow_left₀ hr0 hr1 2
    rw [hD]
    linarith
  have hinv : 1 / N ^ 2 ≤ 4 / x ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos hx0 2)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * N - x) (by linarith : (0 : ℝ) ≤ 2 * N + x)]
  have hKne : K ≠ 0 := ne_of_gt hK
  have hKA : K * (K ^ (-η) / K) = K ^ (-η) := by field_simp
  calc (K / N * D) ^ 2 = K ^ 2 * D ^ 2 * (1 / N ^ 2) := by ring
    _ ≤ K ^ 2 * (2 * Dx ^ 2 + 2 * (K ^ (-η) / K) ^ 2) * (1 / N ^ 2) := by gcongr
    _ = 2 * K ^ 2 * Dx ^ 2 * (1 / N ^ 2) + 2 * (K * (K ^ (-η) / K)) ^ 2 / N ^ 2 := by ring
    _ = 2 * K ^ 2 * Dx ^ 2 * (1 / N ^ 2) + 2 * (K ^ (-η)) ^ 2 / N ^ 2 := by rw [hKA]
    _ ≤ 2 * K ^ 2 * Dx ^ 2 * (4 / x ^ 2) + 2 * (K ^ (-η)) ^ 2 / N ^ 2 := by gcongr
    _ = 8 * K ^ 2 * (Dx ^ 2 / x ^ 2) + 2 * (K ^ (-η)) ^ 2 / N ^ 2 := by ring

/-- `Σ_{n<T} 1/(n+1)² ≤ 2`, by telescoping `2(1/m − 1/(m+1))`. -/
theorem sum_range_inv_succ_sq_le_two (T : ℕ) :
    ∑ n ∈ Finset.range T, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  have h : ∀ n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 ≤
      2 * (1 / ((n + 1 : ℕ) : ℝ)) - 2 * (1 / ((n + 1 + 1 : ℕ) : ℝ)) := by
    intro n
    have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have e : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e]
    set m : ℝ := ((n + 1 : ℕ) : ℝ)
    have hm0 : 0 < m := by linarith
    have e2 : 2 * (1 / m) - 2 * (1 / (m + 1)) = 2 / (m * (m + 1)) := by
      field_simp; ring
    rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑ n ∈ Finset.range T, 1 / ((n + 1 : ℕ) : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.range T, (2 * (1 / ((n + 1 : ℕ) : ℝ)) - 2 * (1 / ((n + 1 + 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun n _ => h n
    _ = 2 * (1 / ((0 + 1 : ℕ) : ℝ)) - 2 * (1 / ((T + 1 : ℕ) : ℝ)) :=
        Finset.sum_range_sub' (fun n => 2 * (1 / ((n + 1 : ℕ) : ℝ))) T
    _ ≤ 2 := by
        have h0 : 0 ≤ 2 * (1 / ((T + 1 : ℕ) : ℝ)) := by positivity
        have h1 : (1 : ℝ) / ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        linarith

/-- **Column energy against the continuous energy**:
`Σ_{n<T} C(n,k)² ≤ 8K² ∫_0^∞ Δ_K(x)² x^{−2} dx + 4(K^{−η})²`. -/
theorem sum_sq_centeredRow_le_integral {η : ℝ} (hη : 0 < η) (k T : ℕ)
    (hint : IntegrableOn (fun x => columnProfile η ((k + 1 : ℕ) : ℝ) x ^ 2 / x ^ 2) (Ioi 0)) :
    ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
      8 * ((k + 1 : ℕ) : ℝ) ^ 2 *
          (∫ x in Ioi (0 : ℝ), columnProfile η ((k + 1 : ℕ) : ℝ) x ^ 2 / x ^ 2) +
        4 * (((k + 1 : ℕ) : ℝ) ^ (-η)) ^ 2 := by
  set f : ℝ → ℝ := fun x => columnProfile η ((k + 1 : ℕ) : ℝ) x ^ 2 / x ^ 2 with hf
  set c : ℝ := 8 * ((k + 1 : ℕ) : ℝ) ^ 2 with hc
  set e : ℝ := (((k + 1 : ℕ) : ℝ) ^ (-η)) ^ 2 with he
  have hc0 : 0 ≤ c := by positivity
  have he0 : 0 ≤ e := by positivity
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  set a : ℕ → ℝ := fun i => (i : ℝ) + 1 with ha
  have hsub : ∀ i : ℕ, Icc (a i) (a (i + 1)) ⊆ Ioi 0 := fun i x hx =>
    lt_of_lt_of_le (by simp only [ha]; positivity) hx.1
  have hii : ∀ i : ℕ, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i
    have hle : a i ≤ a (i + 1) := by simp only [ha]; push_cast; linarith
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hint.mono_set (hsub i)
  have hpt : ∀ n : ℕ, arithmeticDampingCenteredRow η n k ^ 2 ≤
      c * (∫ x in a n..a (n + 1), f x) + 2 * e / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hle : a n ≤ a (n + 1) := by simp only [ha]; push_cast; linarith
    have hlen : a (n + 1) - a n = 1 := by simp only [ha]; push_cast; ring
    have hmono : ∫ x in a n..a (n + 1),
        (arithmeticDampingCenteredRow η n k ^ 2 - 2 * e / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        ∫ x in a n..a (n + 1), c * f x := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hle intervalIntegrable_const
        ((hii n).const_mul c) fun x hx => ?_
      have hx1 : ((n + 1 : ℕ) : ℝ) ≤ x := by
        have := hx.1.le; simp only [ha] at this; push_cast; linarith
      have hx2 : x < ((n + 1 : ℕ) : ℝ) + 1 := by
        have := hx.2; simp only [ha] at this; push_cast at this ⊢; linarith
      have := sq_centeredRow_le_of_mem hη n k hx1 hx2
      simp only [hf, hc, he]
      linarith
    rw [intervalIntegral.integral_const, hlen, one_smul, intervalIntegral.integral_const_mul]
      at hmono
    exact sub_le_iff_le_add.mp hmono
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := a) (n := T) fun i _ => hii i
  have h0T : a 0 ≤ a T := by simp only [ha]; push_cast; linarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)]
  have htail : ∫ x in a 0..a T, f x ≤ ∫ x in Ioi (0 : ℝ), f x := by
    rw [intervalIntegral.integral_of_le h0T]
    refine setIntegral_mono_set hint (ae_of_all _ fun x => hf0 x) ?_
    exact LE.le.eventuallyLE (show Ioc (a 0) (a T) ≤ Ioi (0 : ℝ) from fun x hx =>
      lt_trans (by simp only [ha]; norm_num) hx.1)
  have hinv := sum_range_inv_succ_sq_le_two T
  calc ∑ n ∈ Finset.range T, arithmeticDampingCenteredRow η n k ^ 2
      ≤ ∑ n ∈ Finset.range T, (c * (∫ x in a n..a (n + 1), f x) +
          2 * e / ((n + 1 : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum fun n _ => hpt n
    _ = c * (∫ x in a 0..a T, f x) +
          2 * e * ∑ n ∈ Finset.range T, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ c * (∫ x in Ioi (0 : ℝ), f x) + 2 * e * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left htail hc0)
          (mul_le_mul_of_nonneg_left hinv (by linarith))
    _ = _ := by simp only [hc, he, hf]; ring

/-! ### The source as a fractional-part series -/

/-- `|μ(d)| ≤ 1` as a real number. -/
theorem abs_moebius_real_le_one (d : ℕ) : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- The coefficient `a_d = −μ(d+1)(d+1)^{−η}` of the fractional-part expansion of the source. -/
def sourceCoeff (η : ℝ) (d : ℕ) : ℝ :=
  -(ArithmeticFunction.moebius (d + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-η)

theorem abs_sourceCoeff_le (η : ℝ) (d : ℕ) : |sourceCoeff η d| ≤ ((d + 1 : ℕ) : ℝ) ^ (-η) := by
  unfold sourceCoeff
  rw [abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_moebius_real_le_one _)

/-- `(d+1)^{−η}/(d+1) = (d+1)^{−(1+η)}`. -/
theorem rpow_neg_div_self (η : ℝ) (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) ^ (-η) / ((d + 1 : ℕ) : ℝ) = ((d : ℝ) + 1) ^ (-(1 + η)) := by
  have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  rw [show -(1 + η) = -η - 1 by ring, ← Real.rpow_sub_one hd.ne' (-η)]
  push_cast; ring_nf

/-- **The source is a fractional-part series**: `P(x) = Σ_d a_d {x/(d+1)}` for `x ≥ 0`. -/
theorem sourceProfile_eq_tsum {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : 0 ≤ x) :
    sourceProfile η x = ∑' d : ℕ, sourceCoeff η d * Int.fract (x / ((d + 1 : ℕ) : ℝ)) := by
  set m := ⌊x⌋₊ with hm
  have hρ := density_re_eq_tsum hη
  -- the Möbius density series, shifted to start at `d = 1`
  have hzs : Summable fun d : ℕ => ((d : ℝ) + 1) ^ (-(1 + η)) :=
    RHTower.summable_realZetaTerm (by linarith)
  have hρs : Summable fun d : ℕ =>
      (ArithmeticFunction.moebius (d + 1) : ℝ) * ((d : ℝ) + 1) ^ (-(1 + η)) := by
    refine Summable.of_norm_bounded hzs fun d => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (by positivity) (abs_moebius_real_le_one _)
  have hρshift : (RHTower.pmPowerDampedDivisorDensity η).re =
      ∑' d : ℕ, (ArithmeticFunction.moebius (d + 1) : ℝ) * ((d : ℝ) + 1) ^ (-(1 + η)) := by
    rw [hρ]
    have hs : Summable fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) := by
      rw [← summable_nat_add_iff 1]
      refine hρs.congr fun d => ?_
      rw [Nat.cast_succ]
    rw [hs.tsum_eq_zero_add]
    simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, zero_add]
    exact tsum_congr fun d => by rw [Nat.cast_succ]
  -- the floor part has finite support
  set F : ℕ → ℝ := fun d =>
    (ArithmeticFunction.moebius (d + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-η) * ((m / (d + 1) : ℕ) : ℝ)
    with hF
  have hFsupp : ∀ d ∉ Finset.range m, F d = 0 := by
    intro d hd
    have : m / (d + 1) = 0 := Nat.div_eq_of_lt (by simp at hd; omega)
    simp [hF, this]
  have hFs : Summable F := summable_of_ne_finset_zero hFsupp
  have hFsum : ∑' d, F d = ∑ d ∈ Finset.Icc 1 m,
      (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-η) * ((m / d : ℕ) : ℝ) := by
    rw [tsum_eq_sum hFsupp, Finset.range_eq_Ico]
    have : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.sub_zero, Nat.add_sub_cancel, hF, zero_add]
    exact Finset.sum_congr rfl fun d _ => by rw [add_comm 1 d]
  -- the linear part
  set L : ℕ → ℝ := fun d =>
    (ArithmeticFunction.moebius (d + 1) : ℝ) * ((d : ℝ) + 1) ^ (-(1 + η)) * x with hL
  have hLs : Summable L := hρs.mul_right x
  -- each term
  have hterm : ∀ d : ℕ, sourceCoeff η d * Int.fract (x / ((d + 1 : ℕ) : ℝ)) = F d - L d := by
    intro d
    have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hq : 0 ≤ x / ((d + 1 : ℕ) : ℝ) := div_nonneg hx hd.le
    have hfl : ((⌊x / ((d + 1 : ℕ) : ℝ)⌋ : ℤ) : ℝ) = ((m / (d + 1) : ℕ) : ℝ) := by
      rw [← Nat.cast_floor_eq_int_floor hq, Nat.floor_div_natCast]
    rw [Int.fract, hfl]
    simp only [sourceCoeff, hF, hL]
    rw [← rpow_neg_div_self η d]
    ring
  rw [tsum_congr hterm, hFs.tsum_sub hLs, hFsum, tsum_mul_right, ← hρshift]
  have hA := arithmeticDampingPrefix_eq η m
  rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum] at hA
  unfold sourceProfile
  rw [show arithmeticDampingPrefix η ⌊x⌋₊ = arithmeticDampingPrefix η m from rfl, hA]
  ring

/-- `0 ≤ {y} ≤ y` for `y ≥ 0`. -/
theorem fract_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Int.fract y ≤ y := by
  have := Int.floor_nonneg.mpr hy
  unfold Int.fract
  have : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast this
  linarith

/-- `|P(x)| ≤ ζ(1+η) x` for `x ≥ 0`. -/
theorem abs_sourceProfile_le_mul {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : 0 ≤ x) :
    |sourceProfile η x| ≤ RHTower.realZetaSeries (1 + η) * x := by
  have hzs : Summable fun d : ℕ => ((d : ℝ) + 1) ^ (-(1 + η)) :=
    RHTower.summable_realZetaTerm (by linarith)
  have hb : ∀ d : ℕ, ‖sourceCoeff η d * Int.fract (x / ((d + 1 : ℕ) : ℝ))‖ ≤
      ((d : ℝ) + 1) ^ (-(1 + η)) * x := by
    intro d
    have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hq : 0 ≤ x / ((d + 1 : ℕ) : ℝ) := div_nonneg hx hd.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
    calc |sourceCoeff η d| * Int.fract (x / ((d + 1 : ℕ) : ℝ))
        ≤ ((d + 1 : ℕ) : ℝ) ^ (-η) * (x / ((d + 1 : ℕ) : ℝ)) :=
          mul_le_mul (abs_sourceCoeff_le η d) (fract_le_self_of_nonneg hq)
            (Int.fract_nonneg _) (Real.rpow_nonneg hd.le _)
      _ = ((d : ℝ) + 1) ^ (-(1 + η)) * x := by
          rw [← rpow_neg_div_self η d]; ring
  have hs : Summable fun d : ℕ => ((d : ℝ) + 1) ^ (-(1 + η)) * x := hzs.mul_right x
  rw [sourceProfile_eq_tsum hη hx, ← Real.norm_eq_abs]
  calc ‖∑' d, sourceCoeff η d * Int.fract (x / ((d + 1 : ℕ) : ℝ))‖
      ≤ ∑' d, ((d : ℝ) + 1) ^ (-(1 + η)) * x :=
        tsum_of_norm_bounded hs.hasSum hb
    _ = RHTower.realZetaSeries (1 + η) * x := by rw [tsum_mul_right]; rfl

/-- `|P(x)| ≤ C x^{1−η} + 1` for `x ≥ 0`, `0 < η < 1`. -/
theorem abs_sourceProfile_le_rpow_add_one {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {x : ℝ}
    (hx : 0 ≤ x) :
    |sourceProfile η x| ≤ (1 + 1 / (1 - η) + 1 / η) * x ^ (1 - η) + 1 := by
  have hA := arithmeticDampingPrefix_eq η ⌊x⌋₊
  have hfl := Nat.floor_le hx
  have hfl' := Nat.lt_floor_add_one x
  have hρ0 := RHTower.pmPowerDampedDivisorDensity_re_pos h0
  have hρ1 := density_re_le_one h0
  have hP := abs_centeredPrefix_le_rpow h0 h1 ⌊x⌋₊
  have hpow : ((⌊x⌋₊ : ℕ) : ℝ) ^ (1 - η) ≤ x ^ (1 - η) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hfl (by linarith)
  have hC : 0 ≤ 1 + 1 / (1 - η) + 1 / η := by
    have : 0 < 1 - η := by linarith
    positivity
  unfold sourceProfile
  rw [hA]
  have e : (RHTower.pmPowerDampedDivisorDensity η).re * ((⌊x⌋₊ : ℕ) : ℝ) +
      RHTower.pmPowerDampedCenteredDivisorPrefix η ⌊x⌋₊ - (RHTower.pmPowerDampedDivisorDensity η).re * x =
      RHTower.pmPowerDampedCenteredDivisorPrefix η ⌊x⌋₊ +
        (RHTower.pmPowerDampedDivisorDensity η).re * (((⌊x⌋₊ : ℕ) : ℝ) - x) := by ring
  rw [e]
  have hlin : |(RHTower.pmPowerDampedDivisorDensity η).re * (((⌊x⌋₊ : ℕ) : ℝ) - x)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hρ0, abs_of_nonpos (by linarith)]
    nlinarith
  calc _ ≤ |RHTower.pmPowerDampedCenteredDivisorPrefix η ⌊x⌋₊| +
        |(RHTower.pmPowerDampedDivisorDensity η).re * (((⌊x⌋₊ : ℕ) : ℝ) - x)| := abs_add_le _ _
    _ ≤ (1 + 1 / (1 - η) + 1 / η) * x ^ (1 - η) + 1 := by
        have := mul_le_mul_of_nonneg_left hpow hC
        linarith

/-- The constant `B_η = ζ(1+η) + C_η + 1` of the two-sided source bound. -/
def sourceBound (η : ℝ) : ℝ := RHTower.realZetaSeries (1 + η) + (1 + 1 / (1 - η) + 1 / η) + 1

/-- **Two-sided source bound**: `|P(y)| ≤ B y^η` and `|P(y)| ≤ B y^{1−η}` for `y > 0`,
`½ < η < 1`. -/
theorem abs_sourceProfile_le_bound {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) {y : ℝ} (hy : 0 < y) :
    |sourceProfile η y| ≤ sourceBound η * y ^ η ∧
      |sourceProfile η y| ≤ sourceBound η * y ^ (1 - η) := by
  have hη0 : 0 < η := by linarith
  have hZ : 1 ≤ RHTower.realZetaSeries (1 + η) := RHTower.one_le_realZetaSeries (by linarith)
  have hC : 0 ≤ 1 + 1 / (1 - η) + 1 / η := by
    have : 0 < 1 - η := by linarith
    positivity
  have hB : RHTower.realZetaSeries (1 + η) ≤ sourceBound η := by unfold sourceBound; linarith
  have hB' : 1 + 1 / (1 - η) + 1 / η + 1 ≤ sourceBound η := by unfold sourceBound; linarith
  rcases le_total y 1 with hy1 | hy1
  · have hlin := abs_sourceProfile_le_mul hη0 hy.le
    have ha : y ≤ y ^ η := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hy hy1 h1.le
    have hb : y ≤ y ^ (1 - η) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith : 1 - η ≤ 1)
    have hZ0 : 0 ≤ RHTower.realZetaSeries (1 + η) := by linarith
    constructor
    · calc |sourceProfile η y| ≤ RHTower.realZetaSeries (1 + η) * y := hlin
        _ ≤ sourceBound η * y ^ η := mul_le_mul hB ha hy.le (by linarith)
    · calc |sourceProfile η y| ≤ RHTower.realZetaSeries (1 + η) * y := hlin
        _ ≤ sourceBound η * y ^ (1 - η) := mul_le_mul hB hb hy.le (by linarith)
  · have hpow := abs_sourceProfile_le_rpow_add_one hη0 h1 hy.le
    have h1p : 1 ≤ y ^ (1 - η) := Real.one_le_rpow hy1 (by linarith)
    have hb : |sourceProfile η y| ≤ sourceBound η * y ^ (1 - η) := by
      calc |sourceProfile η y| ≤ (1 + 1 / (1 - η) + 1 / η) * y ^ (1 - η) + 1 * y ^ (1 - η) := by
            linarith
        _ = (1 + 1 / (1 - η) + 1 / η + 1) * y ^ (1 - η) := by ring
        _ ≤ sourceBound η * y ^ (1 - η) := mul_le_mul_of_nonneg_right hB' (by linarith)
    refine ⟨le_trans hb ?_, hb⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))
      (by linarith)

/-- **Two-sided column bound**: `|Δ_K(x)| ≤ 2B x^η` and `|Δ_K(x)| ≤ 2B x^{1−η}` for `K ≥ 1`. -/
theorem abs_columnProfile_le_bound {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) {K : ℝ} (hK : 1 ≤ K)
    {x : ℝ} (hx : 0 < x) :
    |columnProfile η K x| ≤ 2 * sourceBound η * x ^ η ∧
      |columnProfile η K x| ≤ 2 * sourceBound η * x ^ (1 - η) := by
  have hK0 : 0 < K := by linarith
  have hK10 : 0 < K + 1 := by linarith
  have hB0 : 0 ≤ sourceBound η := by
    have := (abs_sourceProfile_le_bound h0 h1 one_pos).1
    simp at this
    linarith [abs_nonneg (sourceProfile η 1)]
  have hKη : K ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK (by linarith)
  have hK1η : (K + 1) ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hxK : x / K ≤ x := div_le_self hx.le hK
  have hxK1 : x / (K + 1) ≤ x := div_le_self hx.le (by linarith)
  have hq : 0 < x / K := div_pos hx hK0
  have hq1 : 0 < x / (K + 1) := div_pos hx hK10
  -- each dilated piece is bounded by the undilated power
  have piece : ∀ {c : ℝ}, 1 ≤ c → ∀ e : ℝ, 0 ≤ e →
      |c ^ (-η) * sourceProfile η (x / c)| ≤ sourceBound η * (x / c) ^ e →
      |c ^ (-η) * sourceProfile η (x / c)| ≤ sourceBound η * x ^ e := by
    intro c hc e he h
    have hc0 : 0 < c := by linarith
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_pos hx hc0).le (div_le_self hx.le hc) he) hB0)
  have bound : ∀ {c : ℝ}, 1 ≤ c → ∀ e : ℝ,
      |sourceProfile η (x / c)| ≤ sourceBound η * (x / c) ^ e →
      |c ^ (-η) * sourceProfile η (x / c)| ≤ sourceBound η * (x / c) ^ e := by
    intro c hc e h
    have hc0 : 0 < c := by linarith
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hc0.le _)]
    have hcη : c ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by linarith)
    calc c ^ (-η) * |sourceProfile η (x / c)| ≤ 1 * |sourceProfile η (x / c)| :=
          mul_le_mul_of_nonneg_right hcη (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h
  have hK1 : 1 ≤ K + 1 := by linarith
  have bA := abs_sourceProfile_le_bound h0 h1 hq
  have bB := abs_sourceProfile_le_bound h0 h1 hq1
  unfold columnProfile
  constructor
  · calc _ ≤ |K ^ (-η) * sourceProfile η (x / K)| +
          |(K + 1) ^ (-η) * sourceProfile η (x / (K + 1))| := abs_sub _ _
      _ ≤ sourceBound η * x ^ η + sourceBound η * x ^ η :=
          add_le_add (piece hK η (by linarith) (bound hK η bA.1))
            (piece hK1 η (by linarith) (bound hK1 η bB.1))
      _ = 2 * sourceBound η * x ^ η := by ring
  · calc _ ≤ |K ^ (-η) * sourceProfile η (x / K)| +
          |(K + 1) ^ (-η) * sourceProfile η (x / (K + 1))| := abs_sub _ _
      _ ≤ sourceBound η * x ^ (1 - η) + sourceBound η * x ^ (1 - η) :=
          add_le_add (piece hK (1 - η) (by linarith) (bound hK (1 - η) bA.2))
            (piece hK1 (1 - η) (by linarith) (bound hK1 (1 - η) bB.2))
      _ = 2 * sourceBound η * x ^ (1 - η) := by ring

/-! ### Mellin transforms on the line `Re s = −½` -/

/-- A profile with `|f(x)| ≤ B min(x^a, x^{1−a})`, `½ < a < 1`, is Mellin convergent on
`Re s = −½`. -/
theorem mellinConvergent_of_two_sided {f : ℝ → ℝ} (hf : Measurable f) {a B : ℝ}
    (ha0 : 1 / 2 < a) (ha1 : a < 1)
    (h1 : ∀ x, 0 < x → |f x| ≤ B * x ^ a) (h2 : ∀ x, 0 < x → |f x| ≤ B * x ^ (1 - a)) (t : ℝ) :
    MellinConvergent (fun x => (f x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hre : (s - 1).re = -3 / 2 := by norm_num [hs]
  have hmeas : Measurable (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((f x : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.pow_const (s - 1)).smul (Complex.measurable_ofReal.comp hf)
  have hnorm : ∀ x : ℝ, 0 < x →
      ‖(x : ℂ) ^ (s - 1) • ((f x : ℝ) : ℂ)‖ = x ^ (-3 / 2 : ℝ) * |f x| := by
    intro x hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Complex.norm_real,
      Real.norm_eq_abs]
  have hp1 : IntegrableOn (fun x : ℝ => B * x ^ (a - 3 / 2)) (Ioc 0 1) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := a - 3 / 2)
      (by linarith)
    exact Integrable.const_mul ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h) B
  have hp2 : IntegrableOn (fun x : ℝ => B * x ^ (-1 / 2 - a)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) B
  have hI1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((f x : ℝ) : ℂ)) (Ioc 0 1) := by
    refine hp1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [hnorm x hx.1]
    calc x ^ (-3 / 2 : ℝ) * |f x| ≤ x ^ (-3 / 2 : ℝ) * (B * x ^ a) :=
          mul_le_mul_of_nonneg_left (h1 x hx.1) (Real.rpow_nonneg hx.1.le _)
      _ = B * x ^ (a - 3 / 2) := by
          rw [mul_left_comm, ← Real.rpow_add hx.1, show (-3 / 2 : ℝ) + a = a - 3 / 2 by ring]
  have hI2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((f x : ℝ) : ℂ)) (Ioi 1) := by
    refine hp2.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [hnorm x hx0]
    calc x ^ (-3 / 2 : ℝ) * |f x| ≤ x ^ (-3 / 2 : ℝ) * (B * x ^ (1 - a)) :=
          mul_le_mul_of_nonneg_left (h2 x hx0) (Real.rpow_nonneg hx0.le _)
      _ = B * x ^ (-1 / 2 - a) := by
          rw [mul_left_comm, ← Real.rpow_add hx0,
            show (-3 / 2 : ℝ) + (1 - a) = -1 / 2 - a by ring]
  have := hI1.union hI2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

/-- **Mellin–Plancherel at abscissa `−½`.**  A measurable profile with
`|f(x)| ≤ B min(x^a, x^{1−a})`, `½ < a < 1`, has `f(x)²/x²` integrable and
`∫_0^∞ f(x)² x^{−2} dx = (1/2π) ∫ |M f(−½ + it)|² dt`. -/
theorem integral_sq_div_sq_eq_mellin {f : ℝ → ℝ} (hf : Measurable f) {a B : ℝ}
    (ha0 : 1 / 2 < a) (ha1 : a < 1)
    (h1 : ∀ x, 0 < x → |f x| ≤ B * x ^ a) (h2 : ∀ x, 0 < x → |f x| ≤ B * x ^ (1 - a)) :
    IntegrableOn (fun x => f x ^ 2 / x ^ 2) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), f x ^ 2 / x ^ 2 =
        1 / (2 * Real.pi) *
          ∫ t : ℝ, ‖mellin (fun x => (f x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
  have hB : 0 ≤ B := by
    have := h1 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    linarith [abs_nonneg (f 1)]
  -- integrability on `(0, ∞)`
  have hsq : ∀ x : ℝ, 0 < x → ∀ e : ℝ, |f x| ≤ B * x ^ e →
      f x ^ 2 / x ^ 2 ≤ B ^ 2 * x ^ (2 * e - 2) := by
    intro x hx e h
    have h' : f x ^ 2 ≤ (B * x ^ e) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc f x ^ 2 / x ^ 2 ≤ (B * x ^ e) ^ 2 / x ^ 2 :=
          div_le_div_of_nonneg_right h' (by positivity)
      _ = B ^ 2 * x ^ (2 * e - 2) := by
          rw [mul_pow, sq_rpow_eq hx, Real.rpow_sub hx, Real.rpow_two]; ring
  have hmeas2 : Measurable (fun x : ℝ => f x ^ 2 / x ^ 2) :=
    (hf.pow_const 2).div (measurable_id.pow_const 2)
  have hI1 : IntegrableOn (fun x => f x ^ 2 / x ^ 2) (Ioc 0 1) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * a - 2)
      (by linarith)
    have hp := Integrable.const_mul
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h) (B ^ 2)
    refine hp.mono' hmeas2.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsq x hx.1 a (h1 x hx.1)
  have hI2 : IntegrableOn (fun x => f x ^ 2 / x ^ 2) (Ioi 1) := by
    have hp := Integrable.const_mul (integrableOn_Ioi_rpow_of_lt
      (by linarith : 2 * (1 - a) - 2 < -1) one_pos) (B ^ 2)
    refine hp.mono' hmeas2.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsq x hx0 (1 - a) (h2 x hx0)
  have hint : IntegrableOn (fun x => f x ^ 2 / x ^ 2) (Ioi 0) := by
    have := hI1.union hI2
    rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this
  refine ⟨hint, ?_⟩
  -- the logarithmic source `g(u) = e^{u/2} f(e^{−u})`
  set r : ℝ := a - 1 / 2 with hr
  have hr0 : 0 < r := by linarith
  set g : ℝ → ℂ := fun u => Real.exp (u / 2) • ((f (Real.exp (-u)) : ℝ) : ℂ) with hg
  have hgnorm : ∀ u, ‖g u‖ = Real.exp (u / 2) * |f (Real.exp (-u))| := by
    intro u
    show ‖Real.exp (u / 2) • ((f (Real.exp (-u)) : ℝ) : ℂ)‖ = _
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, Complex.norm_real, Real.norm_eq_abs]
  have hgb : ∀ u, ‖g u‖ ≤ B * Real.exp (-r * |u|) := by
    intro u
    rw [hgnorm]
    have hx := Real.exp_pos (-u)
    rcases le_total 0 u with hu | hu
    · have h := h1 _ hx
      rw [← Real.exp_mul] at h
      rw [abs_of_nonneg hu]
      calc Real.exp (u / 2) * |f (Real.exp (-u))| ≤
            Real.exp (u / 2) * (B * Real.exp (-u * a)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = B * Real.exp (-r * u) := by
            rw [mul_left_comm, ← Real.exp_add, hr]; congr 2; ring
    · have h := h2 _ hx
      rw [← Real.exp_mul] at h
      rw [abs_of_nonpos hu]
      calc Real.exp (u / 2) * |f (Real.exp (-u))| ≤
            Real.exp (u / 2) * (B * Real.exp (-u * (1 - a))) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = B * Real.exp (-r * -u) := by
            rw [mul_left_comm, ← Real.exp_add, hr]; congr 2; ring
  have hexp : Integrable (fun u : ℝ => Real.exp (-r * |u|)) := by
    have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hr0
    simpa using h
  have hexp2 : Integrable (fun u : ℝ => Real.exp (-(2 * r) * |u|)) := by
    have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (by linarith : 0 < 2 * r)
    simpa using h
  have hgmeas : Measurable g := by
    simp only [hg]
    exact (Real.measurable_exp.comp (measurable_id.div_const 2)).smul
      (Complex.measurable_ofReal.comp (hf.comp (Real.measurable_exp.comp measurable_neg)))
  have hgint : Integrable g :=
    (hexp.const_mul B).mono' hgmeas.aestronglyMeasurable (ae_of_all _ hgb)
  have hgL2 : MemLp g 2 := by
    rw [memLp_two_iff_integrable_sq_norm hgmeas.aestronglyMeasurable]
    refine (hexp2.const_mul (B ^ 2)).mono' (hgmeas.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖g u‖ ^ 2 ≤ (B * Real.exp (-r * |u|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hgb u) 2
      _ = B ^ 2 * Real.exp (-(2 * r) * |u|) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  -- the Mellin transform on the line is the Fourier transform of `g`
  have hline : ∀ t : ℝ, mellin (fun x => (f x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) =
      𝓕 g (t / (2 * Real.pi)) := by
    intro t
    have hre : (((-1 / 2 : ℝ) : ℂ) + t * I).re = -1 / 2 := by simp
    have him : (((-1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
    rw [mellin_eq_fourier]
    simp only [hre, him]
    refine congrArg (fun φ => 𝓕 φ (t / (2 * Real.pi))) ?_
    funext u
    simp only [hg]
    rw [show -(-1 / 2 : ℝ) * u = u / 2 by ring]
  have hscale0 : ∫ t : ℝ, ‖𝓕 g (t / (2 * Real.pi))‖ ^ 2 =
      |2 * Real.pi| • ∫ ξ : ℝ, ‖𝓕 g ξ‖ ^ 2 :=
    Measure.integral_comp_div (fun ξ => ‖𝓕 g ξ‖ ^ 2) (2 * Real.pi)
  have hscale : ∫ t : ℝ, ‖𝓕 g (t / (2 * Real.pi))‖ ^ 2 =
      2 * Real.pi * ∫ ξ : ℝ, ‖𝓕 g ξ‖ ^ 2 := by
    rw [hscale0, abs_of_pos (by positivity), smul_eq_mul]
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hgint hgL2
  have hsub0 : ∫ x in Ioi (0 : ℝ), ‖g (-Real.log x)‖ ^ 2 * x⁻¹ = ∫ u : ℝ, ‖g u‖ ^ 2 :=
    GaloisForLFunctions.HTGeometry.integral_Ioi_comp_neg_log_div (fun u => ‖g u‖ ^ 2)
  have hsub : ∫ u : ℝ, ‖g u‖ ^ 2 = ∫ x in Ioi (0 : ℝ), f x ^ 2 / x ^ 2 := by
    rw [← hsub0]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [hgnorm, neg_neg, Real.exp_log hx0, mul_pow, sq_abs]
    have he : Real.exp (-Real.log x / 2) ^ 2 = x⁻¹ := by
      rw [← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * (-Real.log x / 2) = -Real.log x by push_cast; ring,
        Real.exp_neg, Real.exp_log hx0]
    rw [he]
    field_simp
  simp_rw [hline]
  rw [hscale, hP, hsub, ← mul_assoc, one_div_mul_cancel (by positivity), one_mul]

/-- **The Mellin transform of the fractional part**: for `−1 < Re s < 0`,
`M[{·}](s) = ζ(−s)/s`. -/
theorem mellin_fract_eq {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    MellinConvergent (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) s ∧
      mellin (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) s = riemannZeta (-s) / s := by
  have hw0 : 0 < (-s).re := by rw [Complex.neg_re]; linarith
  have hw1 : (-s).re < 1 := by rw [Complex.neg_re]; linarith
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((Int.fract t : ℝ) : ℂ)) =
      fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(-s + 1)) := by
    funext u; rw [smul_eq_mul, mul_comm, show s - 1 = -(-s + 1) by ring]
  refine ⟨?_, ?_⟩
  · unfold MellinConvergent
    rw [hfun]
    exact RHTower.integrableOn_Ioi_zero_fract_cpow hw0 hw1
  · unfold mellin
    rw [hfun, RHTower.integral_Ioi_zero_fract_cpow hw0 hw1, div_neg, neg_neg]

/-- `(c⁻¹)^{−s} = c^s` for `c > 0`. -/
theorem ofReal_inv_cpow_neg {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ((c⁻¹ : ℝ) : ℂ) ^ (-s) = (c : ℂ) ^ s := by
  have harg : (c : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

/-- **The Mellin transform of a fractional-part series.**  On `−1 < Re s < 0`, if
`F(x) = Σ_d a_d {x/(d+1)}` for `x > 0` and `Σ_d |a_d| (d+1)^{Re s} < ∞`, then
`M F(s) = (Σ_d a_d (d+1)^s) ζ(−s)/s`.  The series is integrated term by term. -/
theorem mellin_fractSeries {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) {a : ℕ → ℝ}
    (hsum : Summable fun d : ℕ => |a d| * ((d + 1 : ℕ) : ℝ) ^ s.re) {F : ℝ → ℝ}
    (hF : ∀ x, 0 < x → F x = ∑' d, a d * Int.fract (x / ((d + 1 : ℕ) : ℝ))) :
    mellin (fun x => (F x : ℂ)) s =
      (∑' d, (a d : ℂ) * ((((d + 1 : ℕ) : ℝ) : ℂ)) ^ s) * (riemannZeta (-s) / s) := by
  obtain ⟨hZc, hZ⟩ := mellin_fract_eq hs0 hs1
  set σ := s.re with hσ
  set c : ℕ → ℝ := fun d => ((d + 1 : ℕ) : ℝ) with hcdef
  have hc : ∀ d, 0 < c d := fun d => by simp only [hcdef]; positivity
  have hdil : ∀ d, (fun x : ℝ => ((Int.fract (x / c d) : ℝ) : ℂ)) =
      fun x => (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) ((c d)⁻¹ * x) := by
    intro d; funext x; rw [div_eq_inv_mul]
  have hdilConv : ∀ d, MellinConvergent (fun x : ℝ => ((Int.fract (x / c d) : ℝ) : ℂ)) s := by
    intro d
    rw [hdil d, MellinConvergent.comp_mul_left (inv_pos.2 (hc d))]
    exact hZc
  have hdilMellin : ∀ d, mellin (fun x : ℝ => ((Int.fract (x / c d) : ℝ) : ℂ)) s =
      ((c d : ℝ) : ℂ) ^ s * (riemannZeta (-s) / s) := by
    intro d
    rw [hdil d, mellin_comp_mul_left _ _ (inv_pos.2 (hc d)), hZ, smul_eq_mul,
      ofReal_inv_cpow_neg (hc d)]
  set T : ℕ → ℝ → ℂ := fun d x => (x : ℂ) ^ (s - 1) • ((a d * Int.fract (x / c d) : ℝ) : ℂ)
    with hT
  have hTeq : ∀ d, T d =
      fun x => (x : ℂ) ^ (s - 1) • ((a d : ℂ) • ((Int.fract (x / c d) : ℝ) : ℂ)) := by
    intro d; funext x; simp only [hT, smul_eq_mul, Complex.ofReal_mul]; try ring
  have hTint : ∀ d, Integrable (T d) (volume.restrict (Ioi 0)) := by
    intro d; rw [hTeq d]; exact (hdilConv d).const_smul (a d : ℂ)
  have hTval : ∀ d, ∫ x in Ioi (0 : ℝ), T d x =
      (a d : ℂ) * (((c d : ℝ) : ℂ) ^ s * (riemannZeta (-s) / s)) := by
    intro d
    calc ∫ x in Ioi (0 : ℝ), T d x =
          mellin (fun x : ℝ => (a d : ℂ) • ((Int.fract (x / c d) : ℝ) : ℂ)) s := by
          rw [hTeq d]; rfl
      _ = _ := by rw [mellin_const_smul, hdilMellin d, smul_eq_mul]
  -- the absolute integrals, by the substitution `x = c y`
  set Z₀ : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * Int.fract x with hZ₀
  have hTnorm : ∀ d, ∫ x in Ioi (0 : ℝ), ‖T d x‖ = |a d| * (c d ^ σ * Z₀) := by
    intro d
    have hcd := hc d
    have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖T d x‖ = |a d| * (x ^ (σ - 1) * Int.fract (x / c d)) := by
      intro x hx
      have hre : (s - 1).re = σ - 1 := by simp [hσ]
      simp only [hT]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < x from hx), hre,
        Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
    congr 1
    have hsubst : ∫ x in Ioi (0 : ℝ), (c d * x) ^ (σ - 1) * Int.fract (c d * x / c d) =
        (c d)⁻¹ • ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * Int.fract (x / c d) := by
      have h := integral_comp_mul_left_Ioi (fun y : ℝ => y ^ (σ - 1) * Int.fract (y / c d)) 0 hcd
      rw [mul_zero] at h
      exact h
    have hleft : ∫ x in Ioi (0 : ℝ), (c d * x) ^ (σ - 1) * Int.fract (c d * x / c d) =
        c d ^ (σ - 1) * Z₀ := by
      rw [hZ₀, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.mul_rpow hcd.le hx0.le, mul_div_cancel_left₀ _ hcd.ne']
      ring
    rw [hleft, smul_eq_mul] at hsubst
    calc ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * Int.fract (x / c d)
        = c d * ((c d)⁻¹ * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * Int.fract (x / c d)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hcd.ne', one_mul]
      _ = c d * (c d ^ (σ - 1) * Z₀) := by rw [← hsubst]
      _ = c d ^ σ * Z₀ := by
          rw [Real.rpow_sub_one hcd.ne', ← mul_assoc, mul_div_cancel₀ _ hcd.ne']
  have hNsum : Summable fun d => ∫ x in Ioi (0 : ℝ), ‖T d x‖ := by
    simp_rw [hTnorm, ← mul_assoc]
    exact hsum.mul_right Z₀
  have hptsum : ∀ x ∈ Ioi (0 : ℝ), ∑' d, T d x = (x : ℂ) ^ (s - 1) • ((F x : ℝ) : ℂ) := by
    intro x hx
    rw [hF x hx, Complex.ofReal_tsum, smul_eq_mul, ← tsum_mul_left]
    simp only [hT, hcdef, smul_eq_mul]
  calc mellin (fun x => (F x : ℂ)) s = ∫ x in Ioi (0 : ℝ), ∑' d, T d x := by
        unfold mellin
        exact setIntegral_congr_fun measurableSet_Ioi fun x hx => (hptsum x hx).symm
    _ = ∑' d, ∫ x in Ioi (0 : ℝ), T d x :=
        (integral_tsum_of_summable_integral_norm hTint hNsum).symm
    _ = ∑' d, (a d : ℂ) * (((c d : ℝ) : ℂ) ^ s * (riemannZeta (-s) / s)) := tsum_congr hTval
    _ = _ := by
        rw [← tsum_mul_right]
        exact tsum_congr fun d => by simp only [hcdef]; ring

/-- **The Mellin transform of the source on `Re s = −½`**:
`|M P(−½ + it)| ≤ ζ(η + ½) |ζ(½ − it)| / |−½ + it|`.  Only `|μ| ≤ 1` is used. -/
theorem norm_mellin_sourceProfile_le {η : ℝ} (hη : 1 / 2 < η) (t : ℝ) :
    ‖mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      RHTower.realZetaSeries (η + 1 / 2) *
        (‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ /
          ‖((-1 / 2 : ℝ) : ℂ) + t * I‖) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hre : s.re = -1 / 2 := by simp [hs]
  have hη0 : 0 < η := by linarith
  have hzs : Summable fun d : ℕ => ((d : ℝ) + 1) ^ (-(η + 1 / 2)) :=
    RHTower.summable_realZetaTerm (by linarith)
  have hcoef : ∀ d : ℕ, |sourceCoeff η d| * ((d + 1 : ℕ) : ℝ) ^ s.re ≤
      ((d : ℝ) + 1) ^ (-(η + 1 / 2)) := by
    intro d
    have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    rw [hre]
    calc |sourceCoeff η d| * ((d + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤
          ((d + 1 : ℕ) : ℝ) ^ (-η) * ((d + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (abs_sourceCoeff_le η d) (Real.rpow_nonneg hd.le _)
      _ = ((d : ℝ) + 1) ^ (-(η + 1 / 2)) := by
          rw [← Real.rpow_add hd, show -η + -1 / 2 = -(η + 1 / 2) by ring, Nat.cast_succ]
  have hsum : Summable fun d : ℕ => |sourceCoeff η d| * ((d + 1 : ℕ) : ℝ) ^ s.re :=
    Summable.of_nonneg_of_le (fun d => by positivity) hcoef hzs
  have hM := mellin_fractSeries (s := s) (by rw [hre]; norm_num) (by rw [hre]; norm_num) hsum
    (F := sourceProfile η) (fun x hx => sourceProfile_eq_tsum hη0 hx.le)
  have hneg : -s = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    rw [hs]; apply Complex.ext <;> simp <;> ring
  rw [hM, norm_mul, hneg, norm_div]
  have hnb : ∀ d, ‖(sourceCoeff η d : ℂ) * ((((d + 1 : ℕ) : ℝ) : ℂ)) ^ s‖ ≤
      ((d : ℝ) + 1) ^ (-(η + 1 / 2)) := by
    intro d
    have hd : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hd]
    exact hcoef d
  have hT : ‖∑' d, (sourceCoeff η d : ℂ) * ((((d + 1 : ℕ) : ℝ) : ℂ)) ^ s‖ ≤
      RHTower.realZetaSeries (η + 1 / 2) := tsum_of_norm_bounded hzs.hasSum hnb
  exact mul_le_mul_of_nonneg_right hT (by positivity)

/-- **The column multiplies the source by its dilation symbol**:
`M Δ_K(s) = (K^{s−η} − (K+1)^{s−η}) M P(s)` on `Re s = −½`. -/
theorem mellin_columnProfile_eq {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) {K : ℝ} (hK : 1 ≤ K)
    (t : ℝ) :
    mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) =
      ((K : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - η) -
          ((K + 1 : ℝ) : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - η)) *
        mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hconv : MellinConvergent (fun x => (sourceProfile η x : ℂ)) s :=
    mellinConvergent_of_two_sided (measurable_sourceProfile η) h0 h1
      (fun x hx => (abs_sourceProfile_le_bound h0 h1 hx).1)
      (fun x hx => (abs_sourceProfile_le_bound h0 h1 hx).2) t
  have hdil : ∀ c : ℝ, (fun x : ℝ => ((sourceProfile η (x / c) : ℝ) : ℂ)) =
      fun x => (fun y : ℝ => ((sourceProfile η y : ℝ) : ℂ)) (c⁻¹ * x) := by
    intro c; funext x; rw [div_eq_inv_mul]
  have hcv : ∀ c : ℝ, 0 < c →
      MellinConvergent (fun x : ℝ => ((sourceProfile η (x / c) : ℝ) : ℂ)) s := by
    intro c hc; rw [hdil c, MellinConvergent.comp_mul_left (inv_pos.2 hc)]; exact hconv
  have hmv : ∀ c : ℝ, 0 < c → mellin (fun x : ℝ => ((sourceProfile η (x / c) : ℝ) : ℂ)) s =
      (c : ℂ) ^ s * mellin (fun x => (sourceProfile η x : ℂ)) s := by
    intro c hc
    rw [hdil c, mellin_comp_mul_left _ _ (inv_pos.2 hc), smul_eq_mul, ofReal_inv_cpow_neg hc]
  have hK0 : (0 : ℝ) < K := by linarith
  have hK10 : (0 : ℝ) < K + 1 := by linarith
  have e1 := integral_const_mul (μ := volume.restrict (Ioi (0 : ℝ))) ((K ^ (-η) : ℝ) : ℂ)
    (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((sourceProfile η (x / K) : ℝ) : ℂ))
  have e2 := integral_const_mul (μ := volume.restrict (Ioi (0 : ℝ))) (((K + 1) ^ (-η) : ℝ) : ℂ)
    (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((sourceProfile η (x / (K + 1)) : ℝ) : ℂ))
  have hcvI : ∀ c : ℝ, 0 < c → Integrable
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((sourceProfile η (x / c) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := fun c hc => hcv c hc
  have e3 := integral_sub ((hcvI K hK0).const_mul ((K ^ (-η) : ℝ) : ℂ))
    ((hcvI (K + 1) hK10).const_mul (((K + 1) ^ (-η) : ℝ) : ℂ))
  have hlin : mellin (fun x => (columnProfile η K x : ℂ)) s =
      ((K ^ (-η) : ℝ) : ℂ) * mellin (fun x => (sourceProfile η (x / K) : ℂ)) s -
        (((K + 1) ^ (-η) : ℝ) : ℂ) * mellin (fun x => (sourceProfile η (x / (K + 1)) : ℂ)) s := by
    unfold mellin
    rw [← e1, ← e2, ← e3]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [columnProfile, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  have hpow : ∀ c : ℝ, 0 < c → ((c ^ (-η) : ℝ) : ℂ) * (c : ℂ) ^ s = (c : ℂ) ^ (s - η) := by
    intro c hc
    rw [Complex.ofReal_cpow hc.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hc.ne')]
    congr 1; push_cast; ring
  rw [hlin, hmv K hK0, hmv (K + 1) hK10, ← mul_assoc, ← mul_assoc, hpow K hK0, hpow (K + 1) hK10]
  ring

/-- **Column energy in Mellin coordinates**:
`∫_0^∞ Δ_K(x)² x^{−2} dx = (1/2π) ∫ |M Δ_K(−½ + it)|² dt`. -/
theorem integral_columnProfile_sq_eq {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) {K : ℝ}
    (hK : 1 ≤ K) :
    IntegrableOn (fun x => columnProfile η K x ^ 2 / x ^ 2) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), columnProfile η K x ^ 2 / x ^ 2 =
        1 / (2 * Real.pi) *
          ∫ t : ℝ, ‖mellin (fun x => (columnProfile η K x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 :=
  integral_sq_div_sq_eq_mellin (measurable_columnProfile η K) h0 h1
    (fun x hx => (abs_columnProfile_le_bound h0 h1 hK hx).1)
    (fun x hx => (abs_columnProfile_le_bound h0 h1 hK hx).2)

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
