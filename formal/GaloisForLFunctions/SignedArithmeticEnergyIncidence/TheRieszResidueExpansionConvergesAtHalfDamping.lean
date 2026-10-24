import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheReceiverIsContinuousAtHalfDamping
import GaloisForLFunctions.RHTower.RieszMoebiusMeansOnTheOneLine

/-!
# The Riesz residue expansion converges at half damping

At half damping the receiver `u_{½} = C_{½} r` is the `ℓ²` limit of its Riesz-weighted finite
residue expansions
`S_N = Σ_{d ≤ N} μ(d) (1 − d/X) d^{−½} v_d`, `X = N + ½` (`rieszResidueSum_l2_tendsto_half`),
while the same weights on the sign-blind series `Σ_d d^{−½} v_d` give horizon energies exceeding
every bound (`rieszTwin_energy_unbounded`).  So the receiver at half damping is approximable in the
receiver norm by finite combinations of residue modes whose coefficients are the Möbius values, and
this uses the signs of `μ`.

**Proof.**  A finite residue combination `R_b = Σ_{d ≤ D} b_d d^{−½} v_d` is
`R_b(n) = P_b(n+1)/(n+1)` for the bounded profile `P_b(x) = −Σ b_d d^{−½} {x/d}`
(`finiteResidueSum_eq_profile`), linear with slope `−τ_b` between integers
(`finiteResidueProfile_eq_of_floor_eq`), so `‖R_b‖² ≤ 8 ∫ P_b² x^{−2} + 4 τ_b²`
(`sum_sq_finiteResidueSum_le`).  On `Re s = −½` its Mellin transform is
`−(Σ b_d d^{−1+it}) ζ(½ − it)/(−½ + it)` (`integral_sq_finiteResidueProfile_eq`).  For the Riesz
coefficients the symbol is the Riesz mean `Q_N(1 − it)` of `Σ μ(n) n^{−1+it}`; it converges to
`1/ζ(1 − it)` with a bound uniform in `N` (`RHTower.tendsto_moebiusRieszPoly_one_line`,
`RHTower.exists_norm_moebiusRieszPoly_one_line_le`), so dominated convergence makes `S_N` Cauchy in
`ℓ²`, and its coordinates converge to those of `u_{½}`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Finite residue combinations -/

/-- A finite residue combination `R_b(n) = Σ_{d ≤ D} b_d d^{−½} v_d(n)`. -/
def finiteResidueSum (D : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, b d * (d : ℝ) ^ (-(1 / 2 : ℝ)) * normalizedResidueProfile d n

/-- Its profile `P_b(x) = −Σ_{d ≤ D} b_d d^{−½} {x/d}`. -/
def finiteResidueProfile (D : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  -∑ d ∈ Finset.Icc 1 D, b d * (d : ℝ) ^ (-(1 / 2 : ℝ)) * Int.fract (x / d)

/-- The slope `τ_b = Σ_{d ≤ D} b_d d^{−3/2}`. -/
def finiteResidueSlope (D : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, b d * (d : ℝ) ^ (-(1 / 2 : ℝ)) / d

/-- The critical symbol `B_b(t) = Σ_{d ≤ D} b_d d^{−(1 − it)}`. -/
def finiteResidueSymbol (D : ℕ) (b : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, (b d : ℂ) * (d : ℂ) ^ (-(1 - (t : ℂ) * I))

/-- `v_d(n) = −{(n+1)/d}/(n+1)`. -/
theorem normalizedResidueProfile_eq_neg_fract {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    normalizedResidueProfile d n = -Int.fract (((n : ℝ) + 1) / d) / ((n : ℝ) + 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfl : (((n + 1) / d : ℕ) : ℝ) = ((n : ℝ) + 1) / d - Int.fract (((n : ℝ) + 1) / d) := by
    rw [← Nat.floor_div_eq_div (K := ℝ), natCast_floor_eq_intCast_floor (by positivity)]
    · push_cast
      rw [← Int.self_sub_floor]
      ring
  unfold normalizedResidueProfile
  rw [hfl]
  push_cast
  field_simp
  ring

theorem finiteResidueSum_eq_profile (D : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    finiteResidueSum D b n = finiteResidueProfile D b ((n : ℝ) + 1) / ((n : ℝ) + 1) := by
  unfold finiteResidueSum finiteResidueProfile
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [normalizedResidueProfile_eq_neg_fract (Finset.mem_Icc.mp hd).1]
  ring

/-- Between consecutive integers no multiple of `d` is crossed: `{x/d} = {N/d} + (x − N)/d`. -/
theorem fract_div_eq_of_mem {N : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ x) (hx' : x < (N : ℝ) + 1) {d : ℕ}
    (hd : 1 ≤ d) : Int.fract (x / d) = Int.fract ((N : ℝ) / d) + (x - N) / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hfl : ⌊x / d⌋ = ⌊(N : ℝ) / d⌋ := by
    rw [Int.floor_eq_iff]
    constructor
    · exact (Int.floor_le _).trans (div_le_div_of_nonneg_right hx hd0.le)
    · set q := ⌊(N : ℝ) / d⌋
      have h1 : (N : ℝ) / d < q + 1 := Int.lt_floor_add_one _
      rw [div_lt_iff₀ hd0] at h1
      have h2 : (N : ℤ) < (q + 1) * d := by exact_mod_cast h1
      have h3 : (N : ℤ) + 1 ≤ (q + 1) * d := h2
      have h4 : (N : ℝ) + 1 ≤ ((q : ℝ) + 1) * d := by exact_mod_cast h3
      rw [div_lt_iff₀ hd0]
      linarith
  rw [← Int.self_sub_floor, ← Int.self_sub_floor, hfl]
  field_simp
  ring

/-- **Between integers the profile is linear** with slope `−τ_b`. -/
theorem finiteResidueProfile_eq_of_mem (D : ℕ) (b : ℕ → ℝ) {N : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ x)
    (hx' : x < (N : ℝ) + 1) :
    finiteResidueProfile D b x =
      finiteResidueProfile D b N - (x - N) * finiteResidueSlope D b := by
  unfold finiteResidueProfile finiteResidueSlope
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [fract_div_eq_of_mem hx hx' (Finset.mem_Icc.mp hd).1]
  ring

theorem abs_finiteResidueProfile_le (D : ℕ) (b : ℕ → ℝ) {x : ℝ} (hx : 0 < x) :
    |finiteResidueProfile D b x| ≤
        (∑ d ∈ Finset.Icc 1 D, |b d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) * x ^ (3 / 4 : ℝ) ∧
      |finiteResidueProfile D b x| ≤
        (∑ d ∈ Finset.Icc 1 D, |b d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) * x ^ (1 - 3 / 4 : ℝ) := by
  set β := ∑ d ∈ Finset.Icc 1 D, |b d| * (d : ℝ) ^ (-(1 / 2 : ℝ)) with hβ
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun d _ => by positivity
  -- `|P_b| ≤ β min(1, x)`
  have hbound : ∀ e : ℝ, (1 ≤ x → 1 ≤ x ^ e) → (x < 1 → x ≤ x ^ e) →
      |finiteResidueProfile D b x| ≤ β * x ^ e := by
    intro e h1 h2
    unfold finiteResidueProfile
    rw [abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hβ, Finset.sum_mul]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hf0 := Int.fract_nonneg (x / d)
    have hf1 := Int.fract_lt_one (x / d)
    rw [abs_mul, abs_mul, abs_of_nonneg hf0,
      abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) ^ (-(1 / 2 : ℝ)))]
    rcases le_or_gt 1 x with hx1 | hx1
    · have := h1 hx1
      have hp : 0 ≤ |b d| * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
      nlinarith
    · have hfx : Int.fract (x / d) = x / d := by
        rw [Int.fract_eq_self]
        exact ⟨by positivity, by rw [div_lt_one hd0]; linarith [(by exact_mod_cast hd1 : (1 : ℝ) ≤ d)]⟩
      rw [hfx]
      have hxd : x / d ≤ x := div_le_self hx.le (by exact_mod_cast hd1)
      have := h2 hx1
      have hp : 0 ≤ |b d| * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
      nlinarith
  refine ⟨hbound _ (fun h => Real.one_le_rpow h (by norm_num)) (fun h => ?_),
    hbound _ (fun h => Real.one_le_rpow h (by norm_num)) (fun h => ?_)⟩
  · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx h.le (by norm_num)
  · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (1 - 3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx h.le (by norm_num)

theorem measurable_finiteResidueProfile (D : ℕ) (b : ℕ → ℝ) :
    Measurable (finiteResidueProfile D b) := by
  unfold finiteResidueProfile
  refine (Finset.measurable_sum _ fun d _ => ?_).neg
  exact measurable_const.mul (measurable_fract.comp (measurable_id.div_const _))

/-! ### The receiver norm against the critical line -/

/-- **Integers against the half-line**: `Σ_{n<T} R_b(n)² ≤ 8 ∫_0^∞ P_b² x^{−2} + 4 τ_b²`. -/
theorem sum_sq_finiteResidueSum_le (D : ℕ) (b : ℕ → ℝ) (T : ℕ)
    (hint : IntegrableOn (fun x => finiteResidueProfile D b x ^ 2 / x ^ 2) (Ioi 0)) :
    ∑ n ∈ Finset.range T, finiteResidueSum D b n ^ 2 ≤
      8 * (∫ x in Ioi (0 : ℝ), finiteResidueProfile D b x ^ 2 / x ^ 2) +
        4 * finiteResidueSlope D b ^ 2 := by
  set Δ := finiteResidueSlope D b with hΔ
  set f : ℝ → ℝ := fun x => finiteResidueProfile D b x ^ 2 / x ^ 2 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  set a : ℕ → ℝ := fun i => (i : ℝ) + 1 with ha
  have hii : ∀ i : ℕ, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i
    have hle : a i ≤ a (i + 1) := by simp only [ha]; push_cast; linarith
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hint.mono_set fun x hx => lt_of_lt_of_le (by simp only [ha]; positivity) hx.1
  have hpt : ∀ n : ℕ, ∀ x : ℝ, (n : ℝ) + 1 ≤ x → x < (n : ℝ) + 2 →
      finiteResidueSum D b n ^ 2 ≤ 8 * f x + 2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    intro n x hx hx'
    have hx0 : 0 < x := by linarith
    have hmem := finiteResidueProfile_eq_of_mem D b (N := n + 1) (x := x) (by push_cast; linarith)
      (by push_cast; linarith)
    push_cast at hmem
    set P := finiteResidueProfile D b ((n : ℝ) + 1) with hP
    have hPx : P = finiteResidueProfile D b x + (x - ((n : ℝ) + 1)) * Δ := by rw [hmem]; ring
    have hsmall : ((x - ((n : ℝ) + 1)) * Δ) ^ 2 ≤ Δ ^ 2 := by
      have h0 : 0 ≤ x - ((n : ℝ) + 1) := by linarith
      have h1 : x - ((n : ℝ) + 1) ≤ 1 := by linarith
      rw [mul_pow]
      nlinarith [sq_nonneg Δ, mul_le_mul h1 h1 h0 zero_le_one]
    have hP2 : P ^ 2 ≤ 2 * finiteResidueProfile D b x ^ 2 + 2 * Δ ^ 2 := by
      rw [hPx]
      nlinarith [add_sq_le_two (finiteResidueProfile D b x) ((x - ((n : ℝ) + 1)) * Δ)]
    have hinv : 1 / ((n : ℝ) + 1) ^ 2 ≤ 4 / x ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (pow_pos hx0 2)]
      nlinarith
    rw [finiteResidueSum_eq_profile]
    calc (P / ((n : ℝ) + 1)) ^ 2 = P ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
          rw [div_pow, div_eq_mul_inv, one_div]
      _ ≤ (2 * finiteResidueProfile D b x ^ 2 + 2 * Δ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hP2 (by positivity)
      _ = 2 * finiteResidueProfile D b x ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) +
            2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by ring
      _ ≤ 2 * finiteResidueProfile D b x ^ 2 * (4 / x ^ 2) + 2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by
          gcongr
      _ = 8 * f x + 2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by simp only [hf]; ring
  have hpt' : ∀ n : ℕ, finiteResidueSum D b n ^ 2 ≤
      8 * (∫ x in a n..a (n + 1), f x) + 2 * Δ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hle : a n ≤ a (n + 1) := by simp only [ha]; push_cast; linarith
    have hlen : a (n + 1) - a n = 1 := by simp only [ha]; push_cast; ring
    have hmono : ∫ x in a n..a (n + 1),
        (finiteResidueSum D b n ^ 2 - 2 * Δ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        ∫ x in a n..a (n + 1), 8 * f x := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hle intervalIntegrable_const
        ((hii n).const_mul 8) fun x hx => ?_
      have hx1 : (n : ℝ) + 1 ≤ x := by have := hx.1.le; simp only [ha] at this; exact this
      have hx2 : x < (n : ℝ) + 2 := by
        have := hx.2; simp only [ha] at this; push_cast at this; linarith
      have := hpt n x hx1 hx2
      push_cast
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
  have hΔ0 : 0 ≤ Δ ^ 2 := sq_nonneg _
  calc ∑ n ∈ Finset.range T, finiteResidueSum D b n ^ 2
      ≤ ∑ n ∈ Finset.range T, (8 * (∫ x in a n..a (n + 1), f x) +
          2 * Δ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum fun n _ => hpt' n
    _ = 8 * (∫ x in a 0..a T, f x) +
          2 * Δ ^ 2 * ∑ n ∈ Finset.range T, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ 8 * (∫ x in Ioi (0 : ℝ), f x) + 2 * Δ ^ 2 * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num))
          (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = 8 * (∫ x in Ioi (0 : ℝ), f x) + 4 * Δ ^ 2 := by ring

/-! ### Plancherel for finite residue combinations -/

theorem sum_Icc_one_eq_sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (D : ℕ) :
    ∑ d ∈ Finset.Icc 1 D, f d = ∑ d ∈ Finset.range D, f (d + 1) := by
  induction D with
  | zero => simp
  | succ D ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The critical-line weight `w(t) = |ζ(½ − it)/(−½ + it)|²`. -/
def zetaHalfWeight (t : ℝ) : ℝ :=
  ‖riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I)) / (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2

/-- **Plancherel for a finite residue combination**:
`∫_0^∞ P_b² x^{−2} = (1/2π) ∫ |B_b(t)|² w(t) dt`. -/
theorem integral_sq_finiteResidueProfile_eq (D : ℕ) (b : ℕ → ℝ) :
    IntegrableOn (fun x => finiteResidueProfile D b x ^ 2 / x ^ 2) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), finiteResidueProfile D b x ^ 2 / x ^ 2 =
        1 / (2 * Real.pi) * ∫ t : ℝ, ‖finiteResidueSymbol D b t‖ ^ 2 * zetaHalfWeight t := by
  obtain ⟨hint, heq⟩ := integral_sq_div_sq_eq_mellin (measurable_finiteResidueProfile D b)
    (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (fun x hx => (abs_finiteResidueProfile_le D b hx).1)
    (fun x hx => (abs_finiteResidueProfile_le D b hx).2)
  refine ⟨hint, heq.trans ?_⟩
  congr 2
  funext t
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hs0 : -1 < s.re := by simp [hs]; norm_num
  have hs1 : s.re < 0 := by simp [hs]; norm_num
  set a : ℕ → ℝ := fun d => if d < D then -(b (d + 1) * ((d + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
    else 0 with ha
  have hsupp : ∀ d ∉ Finset.range D, a d = 0 := fun d hd => by
    simp only [ha, Finset.mem_range] at hd ⊢; simp [hd]
  have hsum : Summable fun d : ℕ => |a d| * ((d + 1 : ℕ) : ℝ) ^ s.re :=
    summable_of_ne_finset_zero (s := Finset.range D) fun d hd => by rw [hsupp d hd]; simp
  have hF : ∀ x, 0 < x → finiteResidueProfile D b x =
      ∑' d, a d * Int.fract (x / ((d + 1 : ℕ) : ℝ)) := by
    intro x _
    rw [tsum_eq_sum (s := Finset.range D) fun d hd => by rw [hsupp d hd, zero_mul]]
    unfold finiteResidueProfile
    rw [sum_Icc_one_eq_sum_range', ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [ha, Finset.mem_range.mp hd, if_true]
    push_cast
    ring
  have hm := mellin_fractSeries hs0 hs1 hsum hF
  rw [hm, norm_mul, mul_pow]
  unfold zetaHalfWeight
  congr 2
  -- the Dirichlet factor is `−B_b(t)`
  have hsym : ∑' d, (a d : ℂ) * ((((d + 1 : ℕ) : ℝ) : ℂ)) ^ s = -finiteResidueSymbol D b t := by
    rw [tsum_eq_sum (s := Finset.range D) fun d hd => by rw [hsupp d hd]; simp]
    unfold finiteResidueSymbol
    rw [sum_Icc_one_eq_sum_range', ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [ha, Finset.mem_range.mp hd, if_true]
    have hd0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hd0' : (((d + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have e : ((-(1 / 2 : ℝ) : ℝ) : ℂ) + s = -(1 - (t : ℂ) * I) := by rw [hs]; push_cast; ring
    rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_cpow hd0.le, neg_mul, mul_assoc,
      ← Complex.cpow_add _ _ hd0', e]
    push_cast
    ring
  rw [hsym, norm_neg]

/-! ### Riesz coefficients -/

/-- The Riesz coefficients `μ(d)(1 − d/X)` for `d ≤ N`, `X = N + ½`. -/
def rieszCoeff (N d : ℕ) : ℝ :=
  if d ≤ N then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1 - d / RHTower.perronLength N) else 0

/-- The Riesz-weighted residue expansion `S_N = Σ_{d ≤ N} μ(d)(1 − d/X) d^{−½} v_d`. -/
def rieszResidueSum (N n : ℕ) : ℝ := finiteResidueSum N (rieszCoeff N) n

theorem finiteResidueSum_rieszCoeff_of_le {N D : ℕ} (h : N ≤ D) (n : ℕ) :
    finiteResidueSum D (rieszCoeff N) n = rieszResidueSum N n := by
  unfold rieszResidueSum finiteResidueSum
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right h) fun d hd hdN => ?_).symm
  have : ¬ d ≤ N := fun h' => hdN (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, h'⟩)
  simp [rieszCoeff, this]

theorem finiteResidueSlope_rieszCoeff_of_le {N D : ℕ} (h : N ≤ D) :
    finiteResidueSlope D (rieszCoeff N) = finiteResidueSlope N (rieszCoeff N) := by
  unfold finiteResidueSlope
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right h) fun d hd hdN => ?_).symm
  have : ¬ d ≤ N := fun h' => hdN (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, h'⟩)
  simp [rieszCoeff, this]

/-- The symbol of the Riesz coefficients is the Riesz mean `Q_N(1 − it)`. -/
theorem finiteResidueSymbol_rieszCoeff_of_le {N D : ℕ} (h : N ≤ D) (t : ℝ) :
    finiteResidueSymbol D (rieszCoeff N) t =
      RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) := by
  unfold finiteResidueSymbol RHTower.moebiusRieszPoly
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right h) fun d hd hdN => by
    have : ¬ d ≤ N := fun h' => hdN (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, h'⟩)
    simp [rieszCoeff, this]]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
  simp only [rieszCoeff, hdN, if_true]
  push_cast
  ring_nf

theorem finiteResidueSum_sub (D : ℕ) (b c : ℕ → ℝ) (n : ℕ) :
    finiteResidueSum D (b - c) n = finiteResidueSum D b n - finiteResidueSum D c n := by
  unfold finiteResidueSum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp only [Pi.sub_apply]; ring

theorem finiteResidueSlope_sub (D : ℕ) (b c : ℕ → ℝ) :
    finiteResidueSlope D (b - c) = finiteResidueSlope D b - finiteResidueSlope D c := by
  unfold finiteResidueSlope
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp only [Pi.sub_apply]; ring

theorem finiteResidueSymbol_sub (D : ℕ) (b c : ℕ → ℝ) (t : ℝ) :
    finiteResidueSymbol D (b - c) t = finiteResidueSymbol D b t - finiteResidueSymbol D c t := by
  unfold finiteResidueSymbol
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp only [Pi.sub_apply]; push_cast; ring

/-! ### Dominated convergence for the Riesz symbols -/

/-- `w(t) ≤ M (1 + t²)^{−5/8}`, from convexity on the critical line. -/
theorem exists_zetaHalfWeight_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, zetaHalfWeight t ≤ M * (1 + t ^ 2) ^ (-(5 / 8 : ℝ)) := by
  obtain ⟨C, hC, hhi⟩ := exists_norm_zeta_half_le
  obtain ⟨Z, hZ, hlo⟩ := exists_norm_zeta_half_box_le 8
  refine ⟨4 * Z ^ 2 * 65 + 2 * C ^ 2, by positivity, fun t => ?_⟩
  have hneg : -(((-1 / 2 : ℝ) : ℂ) + t * I) = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    push_cast; ring
  have hsn : ‖((-1 / 2 : ℝ) : ℂ) + t * I‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hz : ‖riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I))‖ =
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    rw [hneg, norm_zeta_half_neg]
  have hP : 0 < (1 + t ^ 2) ^ (-(5 / 8 : ℝ)) := by positivity
  unfold zetaHalfWeight
  rw [norm_div, div_pow, hz, hsn]
  rcases le_total |t| 8 with ht | ht
  · have h1 := hlo t ht
    have h2 : (1 + 64 : ℝ) ^ (-(5 / 8 : ℝ)) ≤ (1 + t ^ 2) ^ (-(5 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_abs t, abs_nonneg t])
        (by norm_num)
    have h3 : (1 : ℝ) / 65 ≤ (1 + 64 : ℝ) ^ (-(5 / 8 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), one_div]
      apply inv_anti₀ (by positivity)
      calc (1 + 64 : ℝ) ^ (5 / 8 : ℝ) ≤ (1 + 64) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 65 := by norm_num
    have hz2 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ Z ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2)
        ≤ Z ^ 2 / (1 / 4) := div_le_div₀ (by positivity) hz2 (by norm_num) (by nlinarith)
      _ = 4 * Z ^ 2 * 65 * (1 / 65) := by ring
      _ ≤ 4 * Z ^ 2 * 65 * (1 + t ^ 2) ^ (-(5 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left (h3.trans h2) (by positivity)
      _ ≤ (4 * Z ^ 2 * 65 + 2 * C ^ 2) * (1 + t ^ 2) ^ (-(5 / 8 : ℝ)) := by
          nlinarith [sq_nonneg C]
  · have h1 := hhi t ht
    have hz2 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C ^ 2 * |t| ^ (3 / 4 : ℝ) := by
      calc _ ≤ (C * |t| ^ (3 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = C ^ 2 * |t| ^ (3 / 4 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast (|t| ^ (3 / 8 : ℝ)), ← Real.rpow_mul (abs_nonneg t)]
          norm_num
    set a := |t| with hadef
    have ha8 : 8 ≤ a := ht
    have ht2 : t ^ 2 = a ^ 2 := (sq_abs t).symm
    rw [ht2]
    -- `a^{3/4}/a² = (a²)^{−5/8} ≤ 2 (1 + a²)^{−5/8}`
    have hexp : a ^ (3 / 4 : ℝ) / a ^ 2 = (a ^ 2) ^ (-(5 / 8 : ℝ)) := by
      have ha0 : 0 < a := by linarith
      rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha0.le, ← Real.rpow_sub ha0]
      norm_num
    have hcmp : (a ^ 2) ^ (-(5 / 8 : ℝ)) ≤ 2 * (1 + a ^ 2) ^ (-(5 / 8 : ℝ)) := by
      have h2 : 1 + a ^ 2 ≤ 2 * a ^ 2 := by nlinarith
      have hm := Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by norm_num : -(5 / 8 : ℝ) ≤ 0)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at hm
      have h29 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(5 / 8 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), one_div]
        apply inv_anti₀ (by positivity)
        calc (2 : ℝ) ^ (5 / 8 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have hp : 0 ≤ (a ^ 2) ^ (-(5 / 8 : ℝ)) := by positivity
      nlinarith
    calc _ ≤ C ^ 2 * a ^ (3 / 4 : ℝ) / (1 / 4 + a ^ 2) :=
          div_le_div_of_nonneg_right hz2 (by positivity)
      _ ≤ C ^ 2 * a ^ (3 / 4 : ℝ) / a ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = C ^ 2 * (a ^ 2) ^ (-(5 / 8 : ℝ)) := by rw [mul_div_assoc, hexp]
      _ ≤ C ^ 2 * (2 * (1 + a ^ 2) ^ (-(5 / 8 : ℝ))) := by gcongr
      _ ≤ (4 * Z ^ 2 * 65 + 2 * C ^ 2) * (1 + a ^ 2) ^ (-(5 / 8 : ℝ)) := by
          have hPa : 0 < (1 + a ^ 2) ^ (-(5 / 8 : ℝ)) := by positivity
          nlinarith [mul_nonneg (sq_nonneg Z) hPa.le]

theorem continuous_zetaHalfWeight : Continuous zetaHalfWeight := by
  unfold zetaHalfWeight
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hz : -(((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hs0 : ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have c1 : ContinuousAt (fun t : ℝ => riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I))) t :=
    ((differentiableAt_riemannZeta hz).continuousAt).comp (f := fun t : ℝ =>
      -(((-1 / 2 : ℝ) : ℂ) + t * I)) (by fun_prop)
  exact ((c1.div (by fun_prop) hs0).norm).pow 2

theorem continuous_moebiusRieszPoly_line (N : ℕ) :
    Continuous fun t : ℝ => RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) := by
  unfold RHTower.moebiusRieszPoly
  refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact continuous_const.cpow (by fun_prop) fun _ => Or.inl (by
    rw [Complex.natCast_re]
    exact Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega))

theorem continuous_invZetaCont_line :
    Continuous fun t : ℝ => RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I) :=
  continuous_iff_continuousAt.2 fun t =>
    (RHTower.differentiableAt_invZetaCont_of_one_le_re (by simp)).continuousAt.comp
      (f := fun t : ℝ => 1 + ((-t : ℝ) : ℂ) * I) (by fun_prop)

/-- A majorant for the weighted Riesz symbols, uniform in `N`. -/
theorem exists_rieszSymbol_majorant :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (N : ℕ) (t : ℝ), ‖RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) -
      RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I)‖ ^ 2 * zetaHalfWeight t ≤
        G * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
  obtain ⟨C, hC, hQ⟩ := RHTower.exists_norm_moebiusRieszPoly_one_line_le
  obtain ⟨K, hK, hI⟩ := RHTower.exists_norm_invZetaCont_le_rpow
  obtain ⟨M, hM, hw⟩ := exists_zetaHalfWeight_le
  set C' := max C K with hC'
  refine ⟨4 * C' ^ 2 * 5 ^ (1 / 16 : ℝ) * M, by positivity, fun N t => ?_⟩
  have hq : (|-t| + 4) ^ (1 / 32 : ℝ) = (|t| + 4) ^ (1 / 32 : ℝ) := by rw [abs_neg]
  have h1 := hQ N (-t)
  have h2 := hI 1 (-t) le_rfl (by norm_num)
  rw [hq] at h1 h2
  rw [show ((1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = 1 + ((-t : ℝ) : ℂ) * I by push_cast; ring] at h2
  set q := (|t| + 4) ^ (1 / 32 : ℝ) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hnorm : ‖RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) -
      RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I)‖ ^ 2 ≤ 4 * C' ^ 2 * q ^ 2 := by
    have hs := norm_sub_le (RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I))
      (RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I))
    have hC1 : C ≤ C' := le_max_left _ _
    have hK1 : K ≤ C' := le_max_right _ _
    have : ‖RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) -
        RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I)‖ ≤ 2 * C' * q := by
      nlinarith [mul_le_mul_of_nonneg_right hC1 hq0, mul_le_mul_of_nonneg_right hK1 hq0]
    calc _ ≤ (2 * C' * q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = 4 * C' ^ 2 * q ^ 2 := by ring
  have hq2 : q ^ 2 ≤ 5 ^ (1 / 16 : ℝ) * (1 + t ^ 2) ^ (1 / 16 : ℝ) := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.mul_rpow (by norm_num) (by positivity)]
    refine (Real.rpow_le_rpow (by positivity) (?_ : |t| + 4 ≤ 5 * (1 + t ^ 2))
      (by norm_num)).trans_eq' (by norm_num)
    nlinarith [sq_abs t, abs_nonneg t]
  have hcomb : (1 + t ^ 2) ^ (1 / 16 : ℝ) * (1 + t ^ 2) ^ (-(5 / 8 : ℝ)) =
      (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have hw0 : 0 ≤ zetaHalfWeight t := by unfold zetaHalfWeight; positivity
  calc _ ≤ (4 * C' ^ 2 * q ^ 2) * (M * (1 + t ^ 2) ^ (-(5 / 8 : ℝ))) :=
        mul_le_mul hnorm (hw t) hw0 (by positivity)
    _ ≤ (4 * C' ^ 2 * (5 ^ (1 / 16 : ℝ) * (1 + t ^ 2) ^ (1 / 16 : ℝ))) *
          (M * (1 + t ^ 2) ^ (-(5 / 8 : ℝ))) := by gcongr
    _ = 4 * C' ^ 2 * 5 ^ (1 / 16 : ℝ) * M *
          ((1 + t ^ 2) ^ (1 / 16 : ℝ) * (1 + t ^ 2) ^ (-(5 / 8 : ℝ))) := by ring
    _ = _ := by rw [hcomb]

/-- **The Riesz symbols converge in the weighted mean square**:
`∫ |Q_N(1 − it) − 1/ζ(1 − it)|² w(t) dt → 0`. -/
theorem tendsto_integral_rieszSymbol :
    Tendsto (fun N : ℕ => ∫ t : ℝ, ‖RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) -
        RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I)‖ ^ 2 * zetaHalfWeight t) atTop (𝓝 0) := by
  obtain ⟨G, hG, hbound⟩ := exists_rieszSymbol_majorant
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (N : ℕ) (t : ℝ) => ‖RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) -
        RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I)‖ ^ 2 * zetaHalfWeight t) (f := fun _ => 0)
    (fun t => G * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)))
    (Eventually.of_forall fun N => ((((continuous_moebiusRieszPoly_line N).sub
      continuous_invZetaCont_line).norm.pow 2).mul continuous_zetaHalfWeight).aestronglyMeasurable)
    (Eventually.of_forall fun N => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold zetaHalfWeight; positivity)]
      exact hbound N t)
    (integrable_critical_majorant.const_mul _)
    (ae_of_all _ fun t => by
      have h := ((((continuous_norm.tendsto _).comp
        ((RHTower.tendsto_moebiusRieszPoly_one_line (-t)).sub
          (tendsto_const_nhds (x := RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I))))).pow 2).mul_const
        (zetaHalfWeight t))
      simpa using h)
  simpa using hconv

/-! ### Coordinates of the Riesz expansion -/

theorem abs_one_sub_div_perronLength_le {N d : ℕ} (hd : d ≤ N) :
    |1 - (d : ℝ) / RHTower.perronLength N| ≤ 1 := by
  have hX : 0 < RHTower.perronLength N := RHTower.perronLength_pos N
  have h0 : 0 ≤ (d : ℝ) / RHTower.perronLength N := by positivity
  have h1 : (d : ℝ) / RHTower.perronLength N ≤ 1 := by
    rw [div_le_one hX]
    unfold RHTower.perronLength
    have : (d : ℝ) ≤ N := by exact_mod_cast hd
    linarith
  rw [abs_le]; constructor <;> linarith

theorem tendsto_one_sub_div_perronLength (d : ℕ) :
    Tendsto (fun N : ℕ => 1 - (d : ℝ) / RHTower.perronLength N) atTop (𝓝 1) := by
  have hX : Tendsto (fun N : ℕ => RHTower.perronLength N) atTop atTop := by
    unfold RHTower.perronLength
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hX.const_div_atTop (d : ℝ))
  rwa [sub_zero] at h

/-- A Riesz-weighted finite sum of a summable family converges to its sum. -/
theorem tendsto_riesz_sum_of_summable {g : ℕ → ℝ} (hg0 : g 0 = 0)
    (hb : ∀ d, |g d| ≤ (d : ℝ) ^ (-(3 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, (1 - (d : ℝ) / RHTower.perronLength N) * g d)
      atTop (𝓝 (∑' d, g d)) := by
  have hrw : ∀ N : ℕ, ∑ d ∈ Finset.Icc 1 N, (1 - (d : ℝ) / RHTower.perronLength N) * g d =
      ∑' d, (if d ≤ N then (1 - (d : ℝ) / RHTower.perronLength N) * g d else 0) := by
    intro N
    have hz : ∀ d ∉ Finset.Icc 1 N,
        (if d ≤ N then (1 - (d : ℝ) / RHTower.perronLength N) * g d else 0) = 0 := by
      intro d hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp [hg0]
      · have : ¬ d ≤ N := fun h => hd (Finset.mem_Icc.mpr ⟨hd0, h⟩)
        simp [this]
    rw [tsum_eq_sum hz]
    exact Finset.sum_congr rfl fun d hd => by simp [(Finset.mem_Icc.mp hd).2]
  simp only [hrw]
  refine tendsto_tsum_of_dominated_convergence (bound := fun d : ℕ => (d : ℝ) ^ (-(3 / 2 : ℝ)))
    (Real.summable_nat_rpow.mpr (by norm_num)) (fun d => ?_) (Eventually.of_forall fun N d => ?_)
  · have h := (tendsto_one_sub_div_perronLength d).mul_const (g d)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop d] with N hN
    simp [hN]
  · split_ifs with hd
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (abs_one_sub_div_perronLength_le hd) (hb d) (abs_nonneg _)
        zero_le_one).trans_eq (one_mul _)
    · simp only [norm_zero]; positivity

theorem abs_residueTerm_half_le (d n : ℕ) : |residueTerm (1 / 2) d n| ≤ (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [residueTerm]
  unfold residueTerm
  have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  have h := abs_rpow_mul_normalizedResidueProfile_le (η := 1 / 2) hd n
  rw [show (-1 - 1 / 2 : ℝ) = -(3 / 2) by norm_num] at h
  rw [mul_assoc, abs_mul]
  exact (mul_le_mul hμ h (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- **The Riesz expansion converges coordinatewise** to the receiver. -/
theorem tendsto_rieszResidueSum (n : ℕ) :
    Tendsto (fun N => rieszResidueSum N n) atTop (𝓝 (orbitCoord (1 / 2) n)) := by
  have hu : orbitCoord (1 / 2) n = ∑' d, residueTerm (1 / 2) d n := by
    rw [← centeredOperator_reciprocal_eq_orbitCoord (by norm_num : (0 : ℝ) < 1 / 2),
      centeredOperator_reciprocal_eq_tsum]
  rw [hu]
  have h := tendsto_riesz_sum_of_summable (g := fun d => residueTerm (1 / 2) d n)
    (by simp [residueTerm]) (fun d => abs_residueTerm_half_le d n)
  refine h.congr fun N => ?_
  unfold rieszResidueSum finiteResidueSum
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [rieszCoeff, (Finset.mem_Icc.mp hd).2, if_true, residueTerm]
  ring

/-- The Riesz slopes converge. -/
theorem tendsto_rieszSlope :
    Tendsto (fun N => finiteResidueSlope N (rieszCoeff N)) atTop
      (𝓝 (∑' d, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) / d)) := by
  have hb : ∀ d : ℕ, |((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) / d| ≤
      (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have he : (d : ℝ) ^ (-(1 / 2 : ℝ)) / d = (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hd0]; norm_num
    rw [mul_div_assoc, abs_mul, he, abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) ^ (-(3 / 2 : ℝ)))]
    exact (mul_le_mul_of_nonneg_right hμ (by positivity)).trans_eq (one_mul _)
  have h := tendsto_riesz_sum_of_summable (by simp) hb
  refine h.congr fun N => ?_
  unfold finiteResidueSlope
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [rieszCoeff, (Finset.mem_Icc.mp hd).2, if_true]
  ring

/-! ### The receiver at half damping -/

/-- **The Riesz residue expansion converges at half damping**: `S_N → u_{½}` in `ℓ²`; for every
`ε > 0`, eventually `Σ_{n<T} (S_N − u_{½})(n)² ≤ ε` at every horizon `T`. -/
theorem rieszResidueSum_l2_tendsto_half :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ T : ℕ,
      ∑ n ∈ Finset.range T, (rieszResidueSum N n - orbitCoord (1 / 2) n) ^ 2 ≤ ε := by
  intro ε hε
  obtain ⟨G, hG, hmaj⟩ := exists_rieszSymbol_majorant
  set Q : ℕ → ℝ → ℂ := fun N t => RHTower.moebiusRieszPoly N (1 + ((-t : ℝ) : ℂ) * I) with hQ
  set J : ℝ → ℂ := fun t => RHTower.invZetaCont (1 + ((-t : ℝ) : ℂ) * I) with hJ
  set Φ : ℕ → ℝ := fun N => ∫ t : ℝ, ‖Q N t - J t‖ ^ 2 * zetaHalfWeight t with hΦ
  set τ : ℕ → ℝ := fun N => finiteResidueSlope N (rieszCoeff N) with hτ
  set τinf := ∑' d, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) / d
  have hΦ0 : Tendsto Φ atTop (𝓝 0) := tendsto_integral_rieszSymbol
  have hτc : Tendsto τ atTop (𝓝 τinf) := tendsto_rieszSlope
  have hw0 : ∀ t, 0 ≤ zetaHalfWeight t := fun t => by unfold zetaHalfWeight; positivity
  have hmajI : Integrable fun t : ℝ => G * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) :=
    integrable_critical_majorant.const_mul G
  have hintΦ : ∀ N, Integrable fun t : ℝ => ‖Q N t - J t‖ ^ 2 * zetaHalfWeight t := fun N =>
    hmajI.mono' ((((continuous_moebiusRieszPoly_line N).sub
      continuous_invZetaCont_line).norm.pow 2).mul continuous_zetaHalfWeight).aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 t))]
        exact hmaj N t)
  -- the Cauchy estimate between two Riesz expansions
  have hcauchy : ∀ N M T : ℕ, ∑ n ∈ Finset.range T, (rieszResidueSum N n - rieszResidueSum M n) ^ 2 ≤
      8 * (1 / (2 * Real.pi) * (2 * Φ N + 2 * Φ M)) + 4 * (τ N - τ M) ^ 2 := by
    intro N M T
    set D := N + M
    set b := rieszCoeff N - rieszCoeff M
    have hS : ∀ n, rieszResidueSum N n - rieszResidueSum M n = finiteResidueSum D b n := fun n => by
      rw [finiteResidueSum_sub, finiteResidueSum_rieszCoeff_of_le (by omega),
        finiteResidueSum_rieszCoeff_of_le (by omega)]
    have hsl : finiteResidueSlope D b = τ N - τ M := by
      rw [finiteResidueSlope_sub, finiteResidueSlope_rieszCoeff_of_le (by omega),
        finiteResidueSlope_rieszCoeff_of_le (by omega)]
    have hsym : ∀ t, finiteResidueSymbol D b t = Q N t - Q M t := fun t => by
      rw [finiteResidueSymbol_sub, finiteResidueSymbol_rieszCoeff_of_le (by omega),
        finiteResidueSymbol_rieszCoeff_of_le (by omega)]
    obtain ⟨hint, heq⟩ := integral_sq_finiteResidueProfile_eq D b
    have hA := sum_sq_finiteResidueSum_le D b T hint
    rw [heq, hsl] at hA
    simp only [hS]
    have hI : ∫ t : ℝ, ‖finiteResidueSymbol D b t‖ ^ 2 * zetaHalfWeight t ≤ 2 * Φ N + 2 * Φ M := by
      simp only [hsym]
      rw [show 2 * Φ N + 2 * Φ M = ∫ t : ℝ, (2 * (‖Q N t - J t‖ ^ 2 * zetaHalfWeight t) +
          2 * (‖Q M t - J t‖ ^ 2 * zetaHalfWeight t)) by
        rw [integral_add ((hintΦ N).const_mul 2) ((hintΦ M).const_mul 2), integral_const_mul,
          integral_const_mul]]
      have hpt : ∀ t, ‖Q N t - Q M t‖ ^ 2 * zetaHalfWeight t ≤
          2 * (‖Q N t - J t‖ ^ 2 * zetaHalfWeight t) + 2 * (‖Q M t - J t‖ ^ 2 * zetaHalfWeight t) := by
        intro t
        have e : Q N t - Q M t = (Q N t - J t) - (Q M t - J t) := by ring
        have h2 : ‖Q N t - Q M t‖ ^ 2 ≤ 2 * ‖Q N t - J t‖ ^ 2 + 2 * ‖Q M t - J t‖ ^ 2 := by
          rw [e]
          calc _ ≤ (‖Q N t - J t‖ + ‖Q M t - J t‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
            _ ≤ _ := by nlinarith [sq_nonneg (‖Q N t - J t‖ - ‖Q M t - J t‖)]
        nlinarith [hw0 t]
      refine integral_mono_of_nonneg (ae_of_all _ fun t => mul_nonneg (sq_nonneg _) (hw0 t))
        (((hintΦ N).const_mul 2).add ((hintΦ M).const_mul 2)) (ae_of_all _ hpt)
    calc _ ≤ 8 * (1 / (2 * Real.pi) *
          ∫ t : ℝ, ‖finiteResidueSymbol D b t‖ ^ 2 * zetaHalfWeight t) + 4 * (τ N - τ M) ^ 2 := hA
      _ ≤ _ := by gcongr
  set δ : ℝ := ε / (16 / Real.pi + 8) with hδ
  have hδ0 : 0 < δ := by positivity
  have hτδ : ∀ᶠ N in atTop, (τ N - τinf) ^ 2 < δ := by
    have h := (hτc.sub (tendsto_const_nhds (x := τinf))).pow 2
    rw [sub_self, zero_pow two_ne_zero] at h
    exact h.eventually (gt_mem_nhds hδ0)
  filter_upwards [hΦ0.eventually (gt_mem_nhds hδ0), hτδ] with N hΦN hτN
  intro T
  have hlimL : Tendsto (fun M => ∑ n ∈ Finset.range T, (rieszResidueSum N n - rieszResidueSum M n) ^ 2)
      atTop (𝓝 (∑ n ∈ Finset.range T, (rieszResidueSum N n - orbitCoord (1 / 2) n) ^ 2)) :=
    tendsto_finsetSum _ fun n _ => (tendsto_const_nhds.sub (tendsto_rieszResidueSum n)).pow 2
  have hlimR : Tendsto (fun M => 8 * (1 / (2 * Real.pi) * (2 * Φ N + 2 * Φ M)) + 4 * (τ N - τ M) ^ 2)
      atTop (𝓝 (8 * (1 / (2 * Real.pi) * (2 * Φ N + 2 * 0)) + 4 * (τ N - τinf) ^ 2)) :=
    (((tendsto_const_nhds.add (hΦ0.const_mul 2)).const_mul _).const_mul 8).add
      (((tendsto_const_nhds.sub hτc).pow 2).const_mul 4)
  have hle := le_of_tendsto_of_tendsto hlimL hlimR (Eventually.of_forall fun M => hcauchy N M T)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsplit : 8 * (1 / (2 * Real.pi) * (2 * Φ N + 2 * 0)) + 4 * (τ N - τinf) ^ 2 =
      (8 / Real.pi) * Φ N + 4 * (τ N - τinf) ^ 2 := by field_simp; ring
  have hfin : (8 / Real.pi) * δ + 4 * δ ≤ ε := by
    rw [hδ]
    have e : (8 / Real.pi) * (ε / (16 / Real.pi + 8)) + 4 * (ε / (16 / Real.pi + 8)) = ε / 2 := by
      field_simp; ring
    linarith
  calc _ ≤ _ := hle
    _ = _ := hsplit
    _ ≤ (8 / Real.pi) * δ + 4 * δ := by gcongr
    _ ≤ ε := hfin

/-- The Riesz expansion converges to the orbit of the reciprocal: `S_N → C_{½} r` in `ℓ²`. -/
theorem rieszResidueSum_l2_tendsto_centeredOperator :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ T : ℕ,
      ∑ n ∈ Finset.range T, (rieszResidueSum N n -
        arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2)
          reciprocalObservable n) ^ 2 ≤ ε := by
  intro ε hε
  filter_upwards [rieszResidueSum_l2_tendsto_half ε hε] with N h T
  simp only [centeredOperator_reciprocal_eq_orbitCoord]
  exact h T

/-! ### The sign-blind Riesz expansion diverges -/

/-- The Riesz-weighted positive twin `Σ_{d ≤ N} (1 − d/X) d^{−½} v_d`. -/
def rieszTwin (N n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (1 - (d : ℝ) / RHTower.perronLength N) *
    ((d : ℝ) ^ (-(1 / 2 : ℝ)) * normalizedResidueProfile d n)

theorem tendsto_rieszTwin (n : ℕ) :
    Tendsto (fun N => rieszTwin N n) atTop (𝓝 (positiveTwin (1 / 2) n)) := by
  unfold positiveTwin
  refine tendsto_riesz_sum_of_summable (by simp) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h := abs_rpow_mul_normalizedResidueProfile_le (η := 1 / 2) hd n
  rwa [show (-1 - 1 / 2 : ℝ) = -(3 / 2) by norm_num] at h

/-- **The sign-blind Riesz expansion diverges at half damping**: for every `B`, eventually some
horizon energy of `Σ_{d ≤ N} (1 − d/X) d^{−½} v_d` exceeds `B`. -/
theorem rieszTwin_energy_unbounded (B : ℝ) :
    ∀ᶠ N in atTop, ∃ T : ℕ, B < ∑ n ∈ Finset.range T, rieszTwin N n ^ 2 := by
  have hns := not_summable_positiveTwin (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => sq_nonneg _).mp hns
  obtain ⟨T, hT⟩ := (htend.eventually (eventually_gt_atTop (B + 1))).exists
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range T, rieszTwin N n ^ 2) atTop
      (𝓝 (∑ n ∈ Finset.range T, positiveTwin (1 / 2) n ^ 2)) :=
    tendsto_finsetSum _ fun n _ => (tendsto_rieszTwin n).pow 2
  filter_upwards [hlim.eventually (eventually_gt_nhds (show B < _ by linarith))] with N hN
  exact ⟨T, hN⟩

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
