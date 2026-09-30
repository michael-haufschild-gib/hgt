import GaloisForLFunctions.RHTower.SelbergPrimeRangeCascade
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxHighMoments

/-!
# Exponentially rare large values of the prime part, through a cascade of prime ranges

Let `L = log T`, `x = T^{1/30000}`, `u = 2T^{1/15000} ≥ N_x`, and cut the primes at
`c_j = u^{2^{−j}}` (`cascadeCut`). On the range `(c_{j+1}, c_j]` take `m_j = 3750·2^j` moments: then
`c_j^{m_j} = u^{3750}` for every `j` (`cascadeCut_pow`), so the mean-value length stays below
`T^{1/4+o(1)}`, while the energy on `Re z ≥ 1/2 + R/2` is `≤ c_{j+1}^{−R/2}·80/R²
≤ e^{−κ 2^{−j−2}/15000}·80/R²` with `κ = R log T`. With thresholds `M_j = (εL/100)(3/4)^j` the
`m_j`-th moment gives `(q_j e^{−κ2^{−j−2}/15000})^{m_j} ≤ e^{−κ/16}` whenever
`q_j = 3·10⁹(32/9)^j/(κ²ε²) ≤ 1` (`large_range_tail_le`). The last range `(0, c_{J+1}]` has energy
`≤ C₃ (log c_{J+1})²` and `m_{J+1} = 3750·2^{J+1}` moments, which gives
`((2/3)C₃(8/9)^{J+1}/ε²)^{m_{J+1}} ≤ e^{−m_{J+1}}` (`small_range_tail_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-! ## The cutoffs -/

/-- The top cutoff `u = 2 e^{L/15000}`. -/
def cascadeBase (L : ℝ) : ℝ := 2 * Real.exp (L / 15000)

/-- The cutoffs `c_j = u^{2^{−j}}`. -/
def cascadeCut (L : ℝ) (j : ℕ) : ℝ := cascadeBase L ^ ((1 / 2 : ℝ) ^ j)

theorem one_le_cascadeBase {L : ℝ} (hL : 0 ≤ L) : 1 ≤ cascadeBase L := by
  unfold cascadeBase
  have := Real.one_le_exp (show 0 ≤ L / 15000 by positivity)
  linarith

theorem one_le_cascadeCut {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : 1 ≤ cascadeCut L j :=
  Real.one_le_rpow (one_le_cascadeBase hL) (by positivity)

theorem cascadeCut_zero (L : ℝ) : cascadeCut L 0 = cascadeBase L := by
  simp [cascadeCut]

theorem cascadeCut_antitone {L : ℝ} (hL : 0 ≤ L) : Antitone (cascadeCut L) := by
  refine antitone_nat_of_succ_le fun j => ?_
  unfold cascadeCut
  refine Real.rpow_le_rpow_of_exponent_le (one_le_cascadeBase hL) ?_
  rw [pow_succ]
  have : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  linarith

theorem cascadeCut_pow {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    cascadeCut L j ^ (3750 * 2 ^ j) = cascadeBase L ^ (3750 : ℕ) := by
  unfold cascadeCut
  have hu : 0 ≤ cascadeBase L := le_trans zero_le_one (one_le_cascadeBase hL)
  have e : (1 / 2 : ℝ) ^ j * ((3750 * 2 ^ j : ℕ) : ℝ) = ((3750 : ℕ) : ℝ) := by
    push_cast
    rw [mul_comm, mul_assoc, ← mul_pow]
    norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu, e, Real.rpow_natCast]

theorem exp_le_cascadeCut (L : ℝ) (j : ℕ) :
    Real.exp (L * (1 / 2) ^ j / 15000) ≤ cascadeCut L j := by
  unfold cascadeCut cascadeBase
  have h1 : Real.exp (L / 15000) ≤ 2 * Real.exp (L / 15000) := by
    have := Real.exp_pos (L / 15000); linarith
  have h2 : Real.exp (L * (1 / 2) ^ j / 15000) = Real.exp (L / 15000) ^ ((1 / 2 : ℝ) ^ j) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [h2]
  exact Real.rpow_le_rpow (Real.exp_pos _).le h1 (by positivity)

theorem log_cascadeCut_le {L : ℝ} (hL : 15000 ≤ L) (j : ℕ) :
    Real.log (cascadeCut L j) ≤ (1 / 2) ^ j * (L / 7500) := by
  unfold cascadeCut
  have hu : 0 < cascadeBase L := lt_of_lt_of_le zero_lt_one (one_le_cascadeBase (by linarith))
  rw [Real.log_rpow hu]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold cascadeBase
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

theorem selbergPolyLength_le_cascadeBase {L : ℝ} (hL : 0 ≤ L) :
    (selbergPolyLength (Real.exp (L / 30000)) : ℝ) ≤ cascadeBase L := by
  set x := Real.exp (L / 30000) with hx
  have hx2 : x ^ 2 = Real.exp (L / 15000) := by
    rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx21 : 1 ≤ x ^ 2 := by rw [hx2]; exact Real.one_le_exp (by positivity)
  have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x ^ 2 by positivity)
  unfold selbergPolyLength cascadeBase
  rw [← hx2]
  linarith

/-! ## The tails -/

/-- The volume bound in the form `≤ (4140/π) T (mV/M²)^m`. -/
theorem volume_tail_le_pow {T S V M : ℝ} {m : ℕ} (hS0 : 0 ≤ S) (hS : S ≤ 3 * T)
    (hV : 0 ≤ V) (hM : 0 < M) :
    1380 * (m.factorial * V ^ m * S) / (Real.pi * (M ^ m) ^ 2) ≤
      4140 / Real.pi * T * (m * V / M ^ 2) ^ m := by
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hMm : 0 < (M ^ m) ^ 2 := by positivity
  have e : (m * V / M ^ 2) ^ m = (m : ℝ) ^ m * V ^ m / (M ^ m) ^ 2 := by
    rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 m]
  rw [e]
  have h1 : (m.factorial : ℝ) * V ^ m * S ≤ (m : ℝ) ^ m * V ^ m * (3 * T) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hfac (by positivity)) hS hS0 (by positivity)
  have hπ := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have e2 : 4140 / Real.pi * T * ((m : ℝ) ^ m * V ^ m / (M ^ m) ^ 2) * (Real.pi * (M ^ m) ^ 2) =
      1380 * ((m : ℝ) ^ m * V ^ m * (3 * T)) := by
    field_simp; ring
  rw [e2]
  linarith

/-- **A large range costs `e^{−κ/16}`.** -/
theorem large_range_tail_le {R L ε c : ℝ} {j : ℕ} (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε)
    (hc : Real.exp (L * (1 / 2) ^ (j + 1) / 15000) ≤ c)
    (hq : 3 * 10 ^ 9 * (32 / 9) ^ j ≤ (R * L) ^ 2 * ε ^ 2) :
    ((3750 * 2 ^ j : ℕ) * (c ^ (-(R / 2)) * (80 / R ^ 2)) /
        (ε * L / 100 * (3 / 4) ^ j) ^ 2) ^ (3750 * 2 ^ j) ≤ Real.exp (-(R * L / 16)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos _) hc
  set e₀ := Real.exp (L * (1 / 2) ^ (j + 1) / 15000) with he₀
  have hcR : c ^ (-(R / 2)) ≤ Real.exp (-(R * L * (1 / 2) ^ (j + 2) / 15000)) := by
    have h1 : c ^ (-(R / 2)) ≤ e₀ ^ (-(R / 2)) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hc (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [he₀, ← Real.exp_mul]; congr 1; ring
  have hq' : (3750 * 2 ^ j : ℕ) * (80 / R ^ 2) / (ε * L / 100 * (3 / 4) ^ j) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    push_cast
    have hkey : (32 / 9 : ℝ) ^ j * ((3 / 4 : ℝ) ^ j) ^ 2 = 2 ^ j := by
      rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]; norm_num
    have e : (3750 : ℝ) * 2 ^ j * (80 / R ^ 2) =
        3 * 10 ^ 9 * (32 / 9) ^ j * ((ε * L / 100 * (3 / 4) ^ j) ^ 2 / ((R * L) ^ 2 * ε ^ 2)) := by
      have e1 : 3 * 10 ^ 9 * (32 / 9 : ℝ) ^ j * ((ε * L / 100 * (3 / 4) ^ j) ^ 2 /
          ((R * L) ^ 2 * ε ^ 2)) = 3 * 10 ^ 5 * ((32 / 9) ^ j * ((3 / 4) ^ j) ^ 2) / R ^ 2 := by
        field_simp; ring
      rw [e1, hkey]; ring
    rw [e]
    have hpos : 0 < (ε * L / 100 * (3 / 4) ^ j) ^ 2 := by positivity
    calc 3 * 10 ^ 9 * (32 / 9) ^ j * ((ε * L / 100 * (3 / 4) ^ j) ^ 2 / ((R * L) ^ 2 * ε ^ 2))
        ≤ (R * L) ^ 2 * ε ^ 2 * ((ε * L / 100 * (3 / 4) ^ j) ^ 2 / ((R * L) ^ 2 * ε ^ 2)) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = (ε * L / 100 * (3 / 4) ^ j) ^ 2 := by field_simp
  have hbase : (3750 * 2 ^ j : ℕ) * (c ^ (-(R / 2)) * (80 / R ^ 2)) /
      (ε * L / 100 * (3 / 4) ^ j) ^ 2 ≤ Real.exp (-(R * L * (1 / 2) ^ (j + 2) / 15000)) := by
    have e : (3750 * 2 ^ j : ℕ) * (c ^ (-(R / 2)) * (80 / R ^ 2)) /
        (ε * L / 100 * (3 / 4) ^ j) ^ 2 =
        ((3750 * 2 ^ j : ℕ) * (80 / R ^ 2) / (ε * L / 100 * (3 / 4) ^ j) ^ 2) * c ^ (-(R / 2)) := by
      ring
    rw [e]
    have hcR0 : 0 ≤ c ^ (-(R / 2)) := Real.rpow_nonneg hc0.le _
    calc ((3750 * 2 ^ j : ℕ) * (80 / R ^ 2) / (ε * L / 100 * (3 / 4) ^ j) ^ 2) * c ^ (-(R / 2))
        ≤ 1 * c ^ (-(R / 2)) := mul_le_mul_of_nonneg_right hq' hcR0
      _ ≤ _ := by rw [one_mul]; exact hcR
  have hb0 : 0 ≤ (3750 * 2 ^ j : ℕ) * (c ^ (-(R / 2)) * (80 / R ^ 2)) /
      (ε * L / 100 * (3 / 4) ^ j) ^ 2 := by
    have := Real.rpow_nonneg hc0.le (-(R / 2)); positivity
  calc _ ≤ Real.exp (-(R * L * (1 / 2) ^ (j + 2) / 15000)) ^ (3750 * 2 ^ j) :=
        pow_le_pow_left₀ hb0 hbase _
    _ = Real.exp ((3750 * 2 ^ j : ℕ) * -(R * L * (1 / 2) ^ (j + 2) / 15000)) :=
        (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(R * L / 16)) := by
        congr 1
        push_cast
        rw [show (1 / 2 : ℝ) ^ (j + 2) = (1 / 2) ^ j * (1 / 4) by rw [pow_add]; norm_num]
        have h2 : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
        linear_combination (-(R * L) / 16) * h2

/-- **The last range costs `e^{−m}`** once `(2/3) C₃ (8/9)^{J+1}/ε² ≤ e^{−1}`. -/
theorem small_range_tail_le {L ε C₃ ℓ : ℝ} {J : ℕ} (hL : 0 < L) (hε : 0 < ε) (hC₃ : 0 ≤ C₃)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ (1 / 2) ^ (J + 1) * (L / 7500))
    (hsmall : 2 / 3 * C₃ * (8 / 9) ^ (J + 1) / ε ^ 2 ≤ Real.exp (-1)) :
    ((3750 * 2 ^ (J + 1) : ℕ) * (C₃ * ℓ ^ 2) / (ε * L / 100 * (3 / 4) ^ (J + 1)) ^ 2) ^
        (3750 * 2 ^ (J + 1)) ≤ Real.exp (-(3750 * 2 ^ (J + 1) : ℕ)) := by
  set k := J + 1 with hk
  have hbase : (3750 * 2 ^ k : ℕ) * (C₃ * ℓ ^ 2) / (ε * L / 100 * (3 / 4) ^ k) ^ 2 ≤
      Real.exp (-1) := by
    refine le_trans ?_ hsmall
    have hℓ2 : ℓ ^ 2 ≤ ((1 / 2) ^ k * (L / 7500)) ^ 2 := pow_le_pow_left₀ hℓ0 hℓ 2
    have hden : 0 < (ε * L / 100 * (3 / 4) ^ k) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have k1 : (8 / 9 : ℝ) ^ k * ((3 / 4 : ℝ) ^ k) ^ 2 = (1 / 2) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]; norm_num
    have k2 : (2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 2) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]; norm_num
    have e : 2 / 3 * C₃ * (8 / 9) ^ k / ε ^ 2 * (ε * L / 100 * (3 / 4) ^ k) ^ 2 =
        (3750 * 2 ^ k : ℕ) * (C₃ * ((1 / 2) ^ k * (L / 7500)) ^ 2) := by
      have e1 : 2 / 3 * C₃ * (8 / 9 : ℝ) ^ k / ε ^ 2 * (ε * L / 100 * (3 / 4) ^ k) ^ 2 =
          2 / 3 * C₃ * L ^ 2 / 10 ^ 4 * ((8 / 9) ^ k * ((3 / 4) ^ k) ^ 2) := by
        field_simp; ring
      have e2 : ((3750 * 2 ^ k : ℕ) : ℝ) * (C₃ * ((1 / 2) ^ k * (L / 7500)) ^ 2) =
          3750 * C₃ * L ^ 2 / 7500 ^ 2 * (2 ^ k * ((1 / 2) ^ k) ^ 2) := by
        push_cast; ring
      rw [e1, e2, k1, k2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hℓ2 hC₃
    have h0 : (0 : ℝ) ≤ (3750 * 2 ^ k : ℕ) := Nat.cast_nonneg _
    nlinarith
  have hb0 : 0 ≤ (3750 * 2 ^ k : ℕ) * (C₃ * ℓ ^ 2) / (ε * L / 100 * (3 / 4) ^ k) ^ 2 := by
    positivity
  calc _ ≤ Real.exp (-1) ^ (3750 * 2 ^ k) := pow_le_pow_left₀ hb0 hbase _
    _ = Real.exp ((3750 * 2 ^ k : ℕ) * -1) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(3750 * 2 ^ k : ℕ)) := by congr 1; ring

/-! ## One range at a time -/

/-- The length term of every range: `8 b^m (1 + log b^m) ≤ 8u^{3750}(1 + 3750 log u)` when
`b ≤ c` and `c^m = u^{3750}`. -/
theorem length_term_le_of_floor {c u : ℝ} {m : ℕ} (hc : 0 ≤ c) (hu : 1 ≤ u)
    (hcm : c ^ m = u ^ (3750 : ℕ)) :
    8 * ((⌊c⌋₊ ^ m : ℕ) : ℝ) * (1 + Real.log ((⌊c⌋₊ ^ m : ℕ) : ℝ)) ≤
      8 * u ^ (3750 : ℕ) * (1 + 3750 * Real.log u) := by
  have hb : ((⌊c⌋₊ ^ m : ℕ) : ℝ) ≤ u ^ (3750 : ℕ) := by
    rw [Nat.cast_pow, ← hcm]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hc) m
  have hlog : Real.log ((⌊c⌋₊ ^ m : ℕ) : ℝ) ≤ 3750 * Real.log u := by
    rcases Nat.eq_zero_or_pos (⌊c⌋₊ ^ m) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg (by norm_num) (Real.log_nonneg hu)
    · have hpos' : (0 : ℝ) < ((⌊c⌋₊ ^ m : ℕ) : ℝ) := by exact_mod_cast hpos
      have := Real.log_le_log hpos' hb
      rwa [Real.log_pow] at this
  have hlog0 : 0 ≤ 1 + Real.log ((⌊c⌋₊ ^ m : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (⌊c⌋₊ ^ m) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; norm_num
    · have := Real.log_nonneg (show (1 : ℝ) ≤ ((⌊c⌋₊ ^ m : ℕ) : ℝ) by exact_mod_cast hpos)
      linarith
  have h1 : 0 ≤ ((⌊c⌋₊ ^ m : ℕ) : ℝ) := Nat.cast_nonneg _
  calc 8 * ((⌊c⌋₊ ^ m : ℕ) : ℝ) * (1 + Real.log ((⌊c⌋₊ ^ m : ℕ) : ℝ))
      ≤ 8 * u ^ (3750 : ℕ) * (1 + 3750 * Real.log u) :=
        mul_le_mul (by linarith) (by linarith) hlog0 (by positivity)

/-- **A large range: large values on measure `≤ (4140/π) T e^{−κ/16}`.** -/
theorem cascade_large_range_volume_le {T L R ε x : ℝ} {j : ℕ} (hT : 0 < T) (hL0 : 0 < L)
    (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hε : 0 < ε) (hx : 1 < x)
    (hlen : 8 * cascadeBase L ^ (3750 : ℕ) * (1 + 3750 * Real.log (cascadeBase L)) ≤ T)
    (h17 : 17 * R ≤ T) (hq : 3 * 10 ^ 9 * (32 / 9) ^ j ≤ (R * L) ^ 2 * ε ^ 2) :
    volume (largeNearBox (selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j)) T
        (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (ε * L / 100 * (3 / 4) ^ j)) ≤
      ENNReal.ofReal (4140 / Real.pi * T * Real.exp (-(R * L / 16))) := by
  have hfun : selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j) =
      edPoly (⇑(selbergPrimeRangeCoeff x (cascadeCut L (j + 1)) (cascadeCut L j)))
        (Finset.Icc 1 ⌊cascadeCut L j⌋₊) := funext (selbergPrimeRangePoly_eq hx)
  rw [hfun]
  set c := cascadeCut L (j + 1) with hc
  have hc1 : 1 ≤ c := one_le_cascadeCut hL0.le _
  set V : ℝ := c ^ (-(R / 2)) * (80 / R ^ 2) with hV
  have hV0 : 0 ≤ V := by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ c) (-(R / 2)); positivity
  have hVb : ∀ δ : ℝ, R / 2 ≤ δ → δ ≤ 1 →
      ∑ n ∈ Finset.Icc 1 ⌊cascadeCut L j⌋₊,
        ‖selbergPrimeRangeCoeff x c (cascadeCut L j) n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤ V := by
    intro δ hδ hδ1
    have hδ0 : 0 < δ := by linarith
    refine (sum_selbergPrimeRangeCoeff_sq_le_rpow hx hc1 hδ0 hδ1 _).trans ?_
    have h1 : c ^ (-δ) ≤ c ^ (-(R / 2)) := Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
    have h2 : 20 / δ ^ 2 ≤ 80 / R ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    exact mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg (by linarith) _)
  have hm : 1 ≤ 3750 * 2 ^ j := by have := Nat.one_le_two_pow (n := j); omega
  refine (volume_largeNearBox_edPoly_primeSupported_le (fun k hk =>
    (selbergPrimeRangeCoeff_support hx k hk).1)
    (fun k hk => Nat.le_floor (selbergPrimeRangeCoeff_support hx k hk).2.2.1) hT hR hR16
    (by positivity : 0 < ε * L / 100 * (3 / 4) ^ j) hm hVb).trans (ENNReal.ofReal_le_ofReal ?_)
  have hlen' := length_term_le_of_floor (m := 3750 * 2 ^ j)
    (by linarith [one_le_cascadeCut hL0.le j]) (one_le_cascadeBase hL0.le) (cascadeCut_pow hL0.le j)
  have hS0 : 0 ≤ T + 17 * R + 8 * ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ) *
      (1 + Real.log ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ)) := by
    have := length_term_le_of_floor (m := 3750 * 2 ^ j)
      (by linarith [one_le_cascadeCut hL0.le j]) (one_le_cascadeBase hL0.le)
      (cascadeCut_pow hL0.le j)
    have h8 : 0 ≤ 8 * ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ) *
        (1 + Real.log ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j)) with h0 | hpos
      · rw [h0]; simp
      · have := Real.log_nonneg (show (1 : ℝ) ≤ ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ) by
          exact_mod_cast hpos)
        positivity
    linarith
  have hS3 : T + 17 * R + 8 * ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ) *
      (1 + Real.log ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ)) ≤ 3 * T := by
    set X := 8 * ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ) *
      (1 + Real.log ((⌊cascadeCut L j⌋₊ ^ (3750 * 2 ^ j) : ℕ) : ℝ)) with hX
    set Y := 8 * cascadeBase L ^ (3750 : ℕ) * (1 + 3750 * Real.log (cascadeBase L)) with hY
    have h1 : X ≤ Y := hlen'
    have h2 : Y ≤ T := hlen
    linarith
  refine (volume_tail_le_pow hS0 hS3 hV0 (by positivity)).trans ?_
  have htail := large_range_tail_le hR hL0 hε (exp_le_cascadeCut L (j + 1)) hq
  exact mul_le_mul_of_nonneg_left htail (by positivity)

/-- The energy of the last range is at most `C₃ (log c)²`. -/
theorem sum_selbergPrimeRangeCoeff_sq_le_sq_log {C : ℝ}
    (hC : ∀ {x A B δ : ℝ}, 1 < x → 0 ≤ δ → ∀ b : ℕ, 1 ≤ b →
      ∑ n ∈ Finset.Icc 1 b, ‖selbergPrimeRangeCoeff x A B n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
        Real.log b * (Real.log b + C))
    {x A c δ : ℝ} (hx : 1 < x) (hδ : 0 ≤ δ) (hc : 1 ≤ c) :
    ∑ n ∈ Finset.Icc 1 ⌊c⌋₊, ‖selbergPrimeRangeCoeff x A c n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
      (1 + |C| / Real.log 2) * Real.log c ^ 2 := by
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hC3 : 0 ≤ 1 + |C| / Real.log 2 := by positivity
  set b := ⌊c⌋₊ with hb
  have hb1 : 1 ≤ b := Nat.le_floor (by exact_mod_cast hc)
  have hbc : (b : ℝ) ≤ c := Nat.floor_le (by linarith)
  rcases Nat.lt_or_ge b 2 with hb2 | hb2
  · -- only `n = 1`, which is not prime
    have hb' : b = 1 := by omega
    rw [hb', show Finset.Icc 1 1 = {1} from rfl, Finset.sum_singleton,
      selbergPrimeRangeCoeff_apply]
    simp only [Nat.not_prime_one, false_and, if_false, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  · have hlogb : Real.log 2 ≤ Real.log b :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hb2)
    have hlogb0 : 0 < Real.log b := lt_of_lt_of_le hlog2 hlogb
    have hlogc : Real.log b ≤ Real.log c :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < b)) hbc
    refine (hC hx hδ b hb1).trans ?_
    have h1 : Real.log b + C ≤ (1 + |C| / Real.log 2) * Real.log b := by
      have : |C| ≤ |C| / Real.log 2 * Real.log b := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlogb (abs_nonneg C)
      have := le_abs_self C
      nlinarith
    calc Real.log b * (Real.log b + C) ≤ Real.log b * ((1 + |C| / Real.log 2) * Real.log b) :=
          mul_le_mul_of_nonneg_left h1 hlogb0.le
      _ = (1 + |C| / Real.log 2) * Real.log b ^ 2 := by ring
      _ ≤ (1 + |C| / Real.log 2) * Real.log c ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogb0.le hlogc 2) hC3

/-- **The last range: large values on measure `≤ (4140/π) T e^{−m}`**, `m = 3750·2^{J+1}`. -/
theorem cascade_small_range_volume_le {C : ℝ}
    (hC : ∀ {x A B δ : ℝ}, 1 < x → 0 ≤ δ → ∀ b : ℕ, 1 ≤ b →
      ∑ n ∈ Finset.Icc 1 b, ‖selbergPrimeRangeCoeff x A B n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
        Real.log b * (Real.log b + C))
    {T L R ε x : ℝ} {J : ℕ} (hT : 0 < T) (hL : 15000 ≤ L) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hε : 0 < ε) (hx : 1 < x)
    (hlen : 8 * cascadeBase L ^ (3750 : ℕ) * (1 + 3750 * Real.log (cascadeBase L)) ≤ T)
    (h17 : 17 * R ≤ T)
    (hsmall : 2 / 3 * (1 + |C| / Real.log 2) * (8 / 9) ^ (J + 1) / ε ^ 2 ≤ Real.exp (-1)) :
    volume (largeNearBox (selbergPrimeRangePoly x 0 (cascadeCut L (J + 1))) T
        (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (ε * L / 100 * (3 / 4) ^ (J + 1))) ≤
      ENNReal.ofReal (4140 / Real.pi * T * Real.exp (-((3750 * 2 ^ (J + 1) : ℕ) : ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hfun : selbergPrimeRangePoly x 0 (cascadeCut L (J + 1)) =
      edPoly (⇑(selbergPrimeRangeCoeff x 0 (cascadeCut L (J + 1))))
        (Finset.Icc 1 ⌊cascadeCut L (J + 1)⌋₊) := funext (selbergPrimeRangePoly_eq hx)
  rw [hfun]
  set c := cascadeCut L (J + 1) with hc
  have hc1 : 1 ≤ c := one_le_cascadeCut hL0.le _
  set C₃ := 1 + |C| / Real.log 2 with hC₃
  have hC₃0 : 0 ≤ C₃ := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  set ℓ := Real.log c with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hc1
  have hℓle : ℓ ≤ (1 / 2) ^ (J + 1) * (L / 7500) := log_cascadeCut_le hL (J + 1)
  have hVb : ∀ δ : ℝ, R / 2 ≤ δ → δ ≤ 1 →
      ∑ n ∈ Finset.Icc 1 ⌊c⌋₊, ‖selbergPrimeRangeCoeff x 0 c n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
        C₃ * ℓ ^ 2 := fun δ hδ _ =>
    sum_selbergPrimeRangeCoeff_sq_le_sq_log hC hx (by linarith) hc1
  have hm : 1 ≤ 3750 * 2 ^ (J + 1) := by have := Nat.one_le_two_pow (n := J + 1); omega
  refine (volume_largeNearBox_edPoly_primeSupported_le (fun k hk =>
    (selbergPrimeRangeCoeff_support hx k hk).1)
    (fun k hk => Nat.le_floor (selbergPrimeRangeCoeff_support hx k hk).2.2.1) hT hR hR16
    (by positivity : 0 < ε * L / 100 * (3 / 4) ^ (J + 1)) hm hVb).trans
      (ENNReal.ofReal_le_ofReal ?_)
  have hlen' := length_term_le_of_floor (m := 3750 * 2 ^ (J + 1)) (by linarith)
    (one_le_cascadeBase hL0.le) (cascadeCut_pow hL0.le (J + 1))
  set X := 8 * ((⌊c⌋₊ ^ (3750 * 2 ^ (J + 1)) : ℕ) : ℝ) *
    (1 + Real.log ((⌊c⌋₊ ^ (3750 * 2 ^ (J + 1)) : ℕ) : ℝ)) with hX
  set Y := 8 * cascadeBase L ^ (3750 : ℕ) * (1 + 3750 * Real.log (cascadeBase L)) with hY
  have h1 : X ≤ Y := hlen'
  have h2 : Y ≤ T := hlen
  have hX0 : 0 ≤ X := by
    rw [hX]
    rcases Nat.eq_zero_or_pos (⌊c⌋₊ ^ (3750 * 2 ^ (J + 1))) with h0 | hpos
    · rw [h0]; simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ ((⌊c⌋₊ ^ (3750 * 2 ^ (J + 1)) : ℕ) : ℝ) by
        exact_mod_cast hpos)
      positivity
  have hS0 : 0 ≤ T + 17 * R + X := by linarith
  have hS3 : T + 17 * R + X ≤ 3 * T := by linarith
  have hV0 : 0 ≤ C₃ * ℓ ^ 2 := by positivity
  refine (volume_tail_le_pow hS0 hS3 hV0 (by positivity)).trans ?_
  exact mul_le_mul_of_nonneg_left (small_range_tail_le hL0 hε hC₃0 hℓ0 hℓle hsmall)
    (by positivity)

/-- Large values of a sum of two functions. -/
theorem largeNearBox_add_subset (F G : ℂ → ℂ) {T a b R M M₁ M₂ : ℝ} (hM : M₁ + M₂ ≤ M) :
    largeNearBox (fun z => F z + G z) T a b R M ⊆
      largeNearBox F T a b R M₁ ∪ largeNearBox G T a b R M₂ := by
  rintro t ⟨ht, z, h1, h2, h3, hz⟩
  by_contra hno
  simp only [mem_union, not_or] at hno
  have hF : ‖F z‖ ≤ M₁ := by
    by_contra hlt; exact hno.1 ⟨ht, z, h1, h2, h3, not_le.mp hlt⟩
  have hG : ‖G z‖ ≤ M₂ := by
    by_contra hlt; exact hno.2 ⟨ht, z, h1, h2, h3, not_le.mp hlt⟩
  have := norm_add_le (F z) (G z)
  linarith

/-- The cascade length: `8u^{3750}(1 + 3750 log u) ≤ T` for all large `T`, `u = 2T^{1/15000}`. -/
theorem eventually_cascade_length_le :
    ∀ᶠ T in atTop, 8 * cascadeBase (Real.log T) ^ (3750 : ℕ) *
      (1 + 3750 * Real.log (cascadeBase (Real.log T))) ≤ T := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 ^ 3750 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hE := eventually_mul_log_add_pow_le_exp 1 (8 * B * 3751)
    (show (0 : ℝ) < 3 / 4 by norm_num)
  filter_upwards [hE, eventually_ge_atTop 2] with T hE hT2
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hu : cascadeBase L ^ (3750 : ℕ) = B * Real.exp (1 / 4 * L) := by
    unfold cascadeBase
    rw [mul_pow, ← hB, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hlogu : Real.log (cascadeBase L) ≤ 1 + L := by
    unfold cascadeBase
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlogu0 : 0 ≤ Real.log (cascadeBase L) := Real.log_nonneg (one_le_cascadeBase hL0.le)
  rw [pow_one] at hE
  have hT : T = Real.exp (1 / 4 * L) * Real.exp (3 / 4 * L) := by
    rw [← Real.exp_add, show 1 / 4 * L + 3 / 4 * L = L by ring, hLdef, Real.exp_log hT0]
  rw [hu]
  have h1 : 1 + 3750 * Real.log (cascadeBase L) ≤ 3751 * (L + 3) := by nlinarith
  calc 8 * (B * Real.exp (1 / 4 * L)) * (1 + 3750 * Real.log (cascadeBase L))
      ≤ 8 * (B * Real.exp (1 / 4 * L)) * (3751 * (L + 3)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (1 / 4 * L) * (8 * B * 3751 * (L + 3)) := by ring
    _ ≤ Real.exp (1 / 4 * L) * Real.exp (3 / 4 * L) :=
        mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
    _ = T := hT.symm

/-! ## The number of ranges -/

/-- The facts about `J = log₄ ⌊κ²ε²/(3·10⁹)⌋`. -/
theorem cascade_J_facts {κ ε : ℝ} {K₀ J : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hκ : 3 * 10 ^ 9 * ((4 : ℝ) ^ K₀ + 1) ≤ κ ^ 2 * ε ^ 2)
    (hJ : J = Nat.log 4 ⌊κ ^ 2 * ε ^ 2 / (3 * 10 ^ 9)⌋₊) :
    K₀ ≤ J ∧ (∀ j ≤ J, 3 * 10 ^ 9 * (32 / 9 : ℝ) ^ j ≤ κ ^ 2 * ε ^ 2) ∧
      |κ| * ε / 15 ≤ ((3750 * 2 ^ (J + 1) : ℕ) : ℝ) ∧ ((J + 1 : ℕ) : ℝ) ≤ κ ^ 2 := by
  set y := κ ^ 2 * ε ^ 2 / (3 * 10 ^ 9) with hy
  have hy1 : (4 : ℝ) ^ K₀ + 1 ≤ y := by rw [hy, le_div_iff₀ (by norm_num)]; linarith
  set Q := ⌊y⌋₊ with hQdef
  have hQ : 4 ^ K₀ ≤ Q := Nat.le_floor (by push_cast; linarith)
  have hQ0 : Q ≠ 0 := by have := Nat.one_le_pow K₀ 4 (by norm_num); omega
  have hQy : (Q : ℝ) ≤ y := Nat.floor_le (by positivity)
  have hyQ : y < Q + 1 := Nat.lt_floor_add_one y
  have hKJ : K₀ ≤ J := by rw [hJ]; exact Nat.le_log_of_pow_le (by norm_num) hQ
  have h4J : 4 ^ J ≤ Q := by rw [hJ]; exact Nat.pow_log_le_self 4 hQ0
  have h4J1 : Q < 4 ^ (J + 1) := by rw [hJ]; exact Nat.lt_pow_succ_log_self (by norm_num) Q
  have h4Jr : (4 : ℝ) ^ J ≤ y := le_trans (by exact_mod_cast h4J) hQy
  refine ⟨hKJ, fun j hj => ?_, ?_, ?_⟩
  · have h1 : (32 / 9 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have h2 : (4 : ℝ) ^ j ≤ 4 ^ J := pow_le_pow_right₀ (by norm_num) hj
    have h3 : 3 * 10 ^ 9 * y = κ ^ 2 * ε ^ 2 := by rw [hy]; field_simp
    nlinarith
  · have h1 : y < (4 : ℝ) ^ (J + 1) := by
      have : ((Q + 1 : ℕ) : ℝ) ≤ ((4 ^ (J + 1) : ℕ) : ℝ) := by exact_mod_cast h4J1
      push_cast at this
      linarith
    have h2 : (4 : ℝ) ^ (J + 1) = ((2 : ℝ) ^ (J + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hsq : (|κ| * ε) ^ 2 ≤ (15 * ((3750 * 2 ^ (J + 1) : ℕ) : ℝ)) ^ 2 := by
      have e1 : (|κ| * ε) ^ 2 = 3 * 10 ^ 9 * y := by rw [mul_pow, sq_abs, hy]; field_simp
      have e2 : (15 * ((3750 * 2 ^ (J + 1) : ℕ) : ℝ)) ^ 2 = 3164062500 * 4 ^ (J + 1) := by
        push_cast; rw [h2]; ring
      rw [e1, e2]
      have : (0 : ℝ) ≤ 4 ^ (J + 1) := by positivity
      nlinarith
    have h0 : (0 : ℝ) ≤ 15 * ((3750 * 2 ^ (J + 1) : ℕ) : ℝ) := by positivity
    have := (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    linarith
  · have h1 : J + 1 ≤ 4 ^ J := Nat.lt_pow_self (by norm_num)
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ y := le_trans (by exact_mod_cast h1.trans h4J) hQy
    have h3 : y ≤ κ ^ 2 := by
      rw [hy, div_le_iff₀ (by norm_num)]
      have : ε ^ 2 ≤ 1 := by nlinarith
      have := mul_le_mul_of_nonneg_left this (sq_nonneg κ)
      nlinarith [sq_nonneg κ]
    linarith

/-- **Exponentially rare large values of the prime part.** For `0 < ε ≤ 1` there is `κ₁ ≥ 1` such
that for all large `T` and every scale `0 < R ≤ 1/16` with `κ = R log T ≥ κ₁`, at `x = T^{1/30000}`
the heights near which `|P_x| > ε log T/8` on the box have measure
`≤ (4140/π) T (κ² e^{−κ/16} + e^{−κε/15})`. -/
theorem exists_volume_largeNearBox_selbergPrimePoly_cascade_le {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ κ₁ : ℝ, 1 ≤ κ₁ ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → κ₁ ≤ R * Real.log T →
      volume (largeNearBox (selbergPrimePoly (Real.exp (Real.log T / 30000))) T
          (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (ε * Real.log T / 8)) ≤
        ENNReal.ofReal (4140 / Real.pi * T * ((R * Real.log T) ^ 2 *
          Real.exp (-(R * Real.log T / 16)) + Real.exp (-(R * Real.log T * ε / 15)))) := by
  obtain ⟨C, hC⟩ := exists_sum_selbergPrimeRangeCoeff_sq_le_log
  set C₃ := 1 + |C| / Real.log 2 with hC₃
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hC₃1 : 1 ≤ C₃ := by have : 0 ≤ |C| / Real.log 2 := by positivity
                           linarith
  set K₀ : ℕ := ⌈9 * (Real.log (2 * C₃ / ε ^ 2) + 1)⌉₊ with hK₀
  refine ⟨3 * 10 ^ 9 * ((4 : ℝ) ^ K₀ + 1) / ε ^ 2, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : ε ^ 2 ≤ 1 := by nlinarith
    have : (1 : ℝ) ≤ 4 ^ K₀ := one_le_pow₀ (by norm_num)
    nlinarith
  filter_upwards [eventually_cascade_length_le, eventually_ge_atTop (Real.exp 15000),
    eventually_ge_atTop 64] with T hlen hTe hT64
  intro R hR hR16 hκ
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hκ hlen ⊢
  have hL : 15000 ≤ L := by
    rw [hLdef]; have := Real.log_le_log (Real.exp_pos _) hTe; rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  set κ := R * L with hκdef
  have hκ1 : 1 ≤ κ := by
    refine le_trans ?_ hκ
    rw [le_div_iff₀ (by positivity)]
    have : ε ^ 2 ≤ 1 := by nlinarith
    have : (1 : ℝ) ≤ 4 ^ K₀ := one_le_pow₀ (by norm_num)
    nlinarith
  have hκε : 3 * 10 ^ 9 * ((4 : ℝ) ^ K₀ + 1) ≤ κ ^ 2 * ε ^ 2 := by
    have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hκ
    have h2 : κ ≤ κ ^ 2 := by nlinarith
    nlinarith [sq_nonneg ε]
  obtain ⟨J, hJ⟩ : ∃ J, J = Nat.log 4 ⌊κ ^ 2 * ε ^ 2 / (3 * 10 ^ 9)⌋₊ := ⟨_, rfl⟩
  obtain ⟨hKJ, hq, hms, hJκ⟩ := cascade_J_facts hε hε1 hκε hJ
  rw [abs_of_pos (by linarith)] at hms
  -- the small-range condition
  have hsmall : 2 / 3 * C₃ * (8 / 9) ^ (J + 1) / ε ^ 2 ≤ Real.exp (-1) := by
    have h89 : (8 / 9 : ℝ) ≤ Real.exp (-(1 / 9)) := by
      have := Real.add_one_le_exp (-(1 / 9)); linarith
    have hpow : (8 / 9 : ℝ) ^ (J + 1) ≤ Real.exp (-((J + 1 : ℕ) / 9 : ℝ)) := by
      calc (8 / 9 : ℝ) ^ (J + 1) ≤ Real.exp (-(1 / 9)) ^ (J + 1) :=
            pow_le_pow_left₀ (by norm_num) h89 _
        _ = Real.exp ((J + 1 : ℕ) * -(1 / 9)) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-((J + 1 : ℕ) / 9 : ℝ)) := by congr 1; ring
    have hK : 9 * (Real.log (2 * C₃ / ε ^ 2) + 1) ≤ ((J + 1 : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil (9 * (Real.log (2 * C₃ / ε ^ 2) + 1))
      rw [← hK₀] at h1
      have h2 : (K₀ : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K₀ ≤ J + 1)
      linarith
    have hexp : Real.exp (-((J + 1 : ℕ) / 9 : ℝ)) ≤
        Real.exp (-(Real.log (2 * C₃ / ε ^ 2) + 1)) := Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log (2 * C₃ / ε ^ 2) + 1)) = ε ^ 2 / (2 * C₃) * Real.exp (-1) := by
      rw [show -(Real.log (2 * C₃ / ε ^ 2) + 1) = -Real.log (2 * C₃ / ε ^ 2) + -1 by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hC0 : 0 < C₃ := by linarith
    calc 2 / 3 * C₃ * (8 / 9) ^ (J + 1) / ε ^ 2
        ≤ 2 / 3 * C₃ * (ε ^ 2 / (2 * C₃) * Real.exp (-1)) / ε ^ 2 := by
          gcongr
          exact hpow.trans (hexp.trans hval.le)
      _ = Real.exp (-1) / 3 := by field_simp
      _ ≤ Real.exp (-1) := by have := Real.exp_pos (-1); linarith
  -- the decomposition
  set x := Real.exp (L / 30000) with hx
  have hx1 : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
  set F : ℂ → ℂ := fun z => ∑ j ∈ Finset.range (J + 1),
    selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j) z with hF
  set G : ℂ → ℂ := selbergPrimeRangePoly x 0 (cascadeCut L (J + 1)) with hG
  have hdec : selbergPrimePoly x = fun z => F z + G z := by
    funext z
    simp only [hF, hG]
    exact selbergPrimePoly_eq_sum_range hx1 (cascadeCut_antitone hL0.le)
      (fun j => le_trans zero_le_one (one_le_cascadeCut hL0.le j))
      (by rw [cascadeCut_zero]; exact selbergPolyLength_le_cascadeBase hL0.le) (J + 1) z
  have h17 : 17 * R ≤ T := by linarith
  set M : ℕ → ℝ := fun j => ε * L / 100 * (3 / 4) ^ j with hM
  have hgeo : ∑ j ∈ Finset.range (J + 2), (3 / 4 : ℝ) ^ j ≤ 4 := by
    rw [Finset.range_eq_Ico]
    refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans ?_
    norm_num
  have hMsum : ∑ j ∈ Finset.range (J + 1), M j + M (J + 1) ≤ ε * L / 8 := by
    rw [← Finset.sum_range_succ]
    simp only [hM]
    rw [← Finset.mul_sum]
    have : 0 ≤ ε * L / 100 := by positivity
    nlinarith
  have hsub := largeNearBox_add_subset F G (T := T) (a := 1 / 2 + 3 * R / 4)
    (b := 1 / 2 + 6 * R) (R := R) hMsum
  rw [← hdec] at hsub
  have hsub2 : largeNearBox F T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R
      (∑ j ∈ Finset.range (J + 1), M j) ⊆
      ⋃ j ∈ Finset.range (J + 1), largeNearBox
        (selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j)) T
        (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (M j) :=
    largeNearBox_sum_subset (Finset.range (J + 1))
      (fun j => selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j)) M le_rfl
  have hlarge : ∀ j ∈ Finset.range (J + 1),
      volume (largeNearBox (selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j)) T
        (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (M j)) ≤
      ENNReal.ofReal (4140 / Real.pi * T * Real.exp (-(R * L / 16))) := fun j hj =>
    cascade_large_range_volume_le hT0 hL0 hR hR16 hε hx1 hlen h17
      (hq j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have hsmallv := cascade_small_range_volume_le hC (J := J) hT0 hL hR hR16 hε hx1 hlen h17 hsmall
  have hexps : Real.exp (-((3750 * 2 ^ (J + 1) : ℕ) : ℝ)) ≤ Real.exp (-(κ * ε / 15)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc volume (largeNearBox (selbergPrimePoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R
        (ε * L / 8))
      ≤ volume (⋃ j ∈ Finset.range (J + 1), largeNearBox
          (selbergPrimeRangePoly x (cascadeCut L (j + 1)) (cascadeCut L j)) T
          (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (M j)) +
        volume (largeNearBox (selbergPrimeRangePoly x 0 (cascadeCut L (J + 1))) T
          (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (M (J + 1))) :=
        (measure_mono (hsub.trans (Set.union_subset_union_left _ hsub2))).trans
          (measure_union_le _ _)
    _ ≤ (∑ j ∈ Finset.range (J + 1),
          ENNReal.ofReal (4140 / Real.pi * T * Real.exp (-(R * L / 16)))) +
        ENNReal.ofReal (4140 / Real.pi * T * Real.exp (-(κ * ε / 15))) := by
        gcongr
        · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hlarge)
        · exact hsmallv.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left hexps (by positivity)))
    _ = ENNReal.ofReal ((J + 1 : ℕ) * (4140 / Real.pi * T * Real.exp (-(R * L / 16))) +
          4140 / Real.pi * T * Real.exp (-(κ * ε / 15))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg (J + 1)), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4140 / Real.pi * T * (κ ^ 2 * Real.exp (-(R * L / 16)) +
          Real.exp (-(R * L * ε / 15)))) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 := mul_le_mul_of_nonneg_right hJκ
          (show 0 ≤ 4140 / Real.pi * T * Real.exp (-(R * L / 16)) by positivity)
        have e : 4140 / Real.pi * T * (κ ^ 2 * Real.exp (-(R * L / 16)) +
            Real.exp (-(R * L * ε / 15))) = κ ^ 2 * (4140 / Real.pi * T *
              Real.exp (-(R * L / 16))) + 4140 / Real.pi * T * Real.exp (-(κ * ε / 15)) := by
          rw [hκdef]; ring
        rw [e]
        linarith

/-! ## The box bound at one scale with an exponential rate -/

/-- The four exceptional measures at one scale, with the prime part through the cascade. -/
theorem scale_terms_cascade_le {T L R ε A Kw C₀ x S P : ℝ} (hT64 : 64 ≤ T)
    (hL : Real.log T = L) (hR : 0 < R) (hκ : 30000 ≤ R * L) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hA : 0 < A) (hC₀ : 0 < C₀) (hx : x = Real.exp (L / 30000)) (hP : 0 ≤ P)
    (hE5 : 144 * Kw / Real.pi * (L + 3) ^ 2 ≤ Real.exp ((1 / 2 - 1 / 10000) * L))
    (hS0 : 0 ≤ S)
    (hS : S ≤ 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) +
      144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi) :
    ENNReal.ofReal S +
        ENNReal.ofReal (4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
          (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153))) +
        ENNReal.ofReal (4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
          (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4)) +
        ENNReal.ofReal (4140 / Real.pi * T * P) ≤
      ENNReal.ofReal ((336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ +
          1600000 * Real.pi * C₀ + 4140 / Real.pi + 1) * T *
          (Real.exp (-(R * L / 120000)) / ε + P) +
        (336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ + 1600000 * Real.pi * C₀ +
          4140 / Real.pi + 1) * T ^ ((1 : ℝ) / 2)) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by rw [← hL]; exact Real.log_pos (by linarith)
  have hlx : Real.log x = L / 30000 := by rw [hx, Real.log_exp]
  have hx1 : 1 < x := by rw [hx]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hlx0 := Real.log_pos hx1
  have hκ1 : 1 ≤ R * L := by linarith
  have hΦ0 : 0 ≤ Real.log (4 * T + 5) := Real.log_nonneg (by linarith)
  have hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L := by
    have h1 : Real.log (4 * T + 5) ≤ 2 * L := by
      have : Real.log (4 * T + 5) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow, hL] at this
      push_cast at this
      linarith
    have h3 : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ C₀ * (5 * T) * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₀.le) h1 hΦ0 (by positivity)
    linarith
  have ha := window_term_le hT0 hL hκ hε hε1 hA hlx hE5 hS
  have hb := lorentz_term_le (x := x) hT0 hL0 hR hε hC₀ hκ1 hlx hΦ
  have hc := far_term_le (x := x) hT0 hL0 hR hε hC₀ hκ1 hlx hΦ hΦ0
  have hnb : 0 ≤ 4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
      (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153)) := by positivity
  have hnc : 0 ≤ 4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
      (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4) := by positivity
  rw [← ENNReal.ofReal_add hS0 hnb, ← ENNReal.ofReal_add (by positivity) hnc,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (four_terms_combine_pow hA.le (by positivity) (by positivity)
    hT0.le (Real.exp_pos _).le hε (by positivity) hP ha hb hc le_rfl)

/-- **Typical `ζ'/ζ` box bound at one scale, exponential rate.** For `0 < ε ≤ 1` there are `C` and
`κ₁ ≥ 1` such that for all large `T` and every scale `0 < R ≤ 1/16` with `κ = R log T ≥ κ₁`, the
heights `t ∈ [T, 2T]` without log-derivative scale data at level `ε log T` have measure
`≤ C T (e^{−κ/120000}/ε + κ² e^{−κ/16} + e^{−κε/15}) + C T^{1/2}`. -/
theorem exists_volume_not_zetaLogDerivScaleData_le_exp {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C κ₁ : ℝ, 0 < C ∧ 1 ≤ κ₁ ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 →
      κ₁ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          ((R * Real.log T) ^ 2 * Real.exp (-(R * Real.log T / 16)) +
            Real.exp (-(R * Real.log T * ε / 15)))) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨KE, hKE, hEFall⟩ := exists_selberg_explicit_formula_at_height
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hKE)
  obtain ⟨A, Kw, hA, hKw, hwin⟩ := exists_sum_selbergRightWindow_le
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_sum_mult_selbergMidZeros_le
  obtain ⟨κc, hκc1, hcas⟩ := exists_volume_largeNearBox_selbergPrimePoly_cascade_le hε hε1
  refine ⟨336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ + 1600000 * Real.pi * C₀ +
    4140 / Real.pi + 1, max κc (max 30000 (384 / ε)), by positivity,
    le_trans hκc1 (le_max_left _ _), ?_⟩
  have hE2 := eventually_mul_log_add_pow_le_exp 40 1 (show (0 : ℝ) < 1 / 30000 by norm_num)
  have hE3 := Real.tendsto_log_atTop.eventually_ge_atTop (4 / ε)
  have hE5 := eventually_mul_log_add_pow_le_exp 2 (144 * Kw / Real.pi)
    (show (0 : ℝ) < 1 / 2 - 1 / 10000 by norm_num)
  filter_upwards [hwin, eventually_ge_atTop (max t₀ 64), hE2, hE3, hE5, hcas] with T hTwin hTt
    hE2 hE3 hE5 hcasT
  intro R hR hR16 hκ
  have hκc : κc ≤ R * Real.log T := le_trans (le_max_left _ _) hκ
  have hκ30 : 30000 ≤ R * Real.log T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hκ
  have hκε : 384 / ε ≤ R * Real.log T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hκ
  have hT64 : 64 ≤ T := le_of_max_le_right hTt
  have hcasR := hcasT R hR hR16 hκc
  set L := Real.log T with hLdef
  have hL4 : 4 ≤ L := le_trans (by rw [le_div_iff₀ hε]; linarith) hE3
  have hL0 : 0 < L := by linarith
  set x := Real.exp (L / 30000) with hxdef
  have hlx : Real.log x = L / 30000 := Real.log_exp _
  have hx : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
  have hRx : 1 ≤ 36 * R * Real.log x := by
    rw [hlx]
    have : 36 * R * (L / 30000) = 36 * (R * L) / 30000 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    linarith
  have hEF := selberg_explicit_formula_block hEFall ht₀ hT64 (le_of_max_le_left hTt) hx
    (by rw [hxdef, show L / 30000 = 1 / 30000 * L by ring]; linarith)
    (by rw [hlx]; linarith)
  have hcL0 : 0 < 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 := by
    have := Real.log_pos hx; positivity
  have hεL : 0 < ε * L / 4 := by positivity
  have hε4 : 4 ≤ ε * L := by
    have := (div_le_iff₀ hε).mp hE3
    linarith
  have h96 : 96 / R ≤ ε * L / 4 := by
    rw [div_le_iff₀ hR]
    have := (div_le_iff₀ hε).mp hκε
    nlinarith
  have hbox := volume_not_zetaLogDerivScaleData_le_of_largeNearBox (B := ε * L) (C₀ := C₀)
    (M_D := ε * L / 4) (M_L := ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) /
      Real.log x * 1153)) (M_F := ε * L / 4) hT64 hx hR hR16 hRx hEF (hC₀ T (by linarith))
    (div_pos hεL hcL0) hεL (by rw [mul_div_cancel₀ _ hcL0.ne']; linarith)
  have hsubD := largeNearBox_selbergVonMangoldtPoly_subset_prime (T := T) hx hR hR16 h96
  rw [show ε * L / 4 / 2 = ε * L / 8 by ring] at hsubD
  have hD := (measure_mono hsubD).trans hcasR
  refine hbox.trans (le_trans ?_ (scale_terms_cascade_le hT64 hLdef.symm hR hκ30 hε hε1 hA
    hC₀pos hxdef (by positivity) hE5
    (Finset.sum_nonneg fun w _ => by have := selbergRightWindow_pos (x := x) hR w; positivity)
    (hTwin x R hx hR (by linarith) (by linarith) (by
      rw [hlx, show 6 * (L / 30000) / L = 1 / 5000 by field_simp; ring]; norm_num))))
  gcongr

end RHTower
