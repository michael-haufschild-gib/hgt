import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrefixEnergyLinearityAndBandNonCommutation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ReceiverRowParsevalSpectrumAndHorizonUniformVariance
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedAutocorrelationAndClockInvisibility

/-!
# Linear dissipation of the damped defect at an exact rate

The dissipation rate of the damped Möbius row converges: the Bézout form is diagonal with the
bounded multipliers `μ(e)`, so `Q_Bez(N; c_ε) → Σ_e μ(e) w_ε(e)²`, and with the cofinal Selberg limit

`R_N(c_ε) → R(ε) = E[τ_ε²] - Σ_e μ(e) w_ε(e)² = Σ_{e ≥ 2} (φ(e) - μ(e)) w_ε(e)² > 0`.

For a periodic response the Cesàro mean of the successor energy is twice the dissipation rate. The
complete damped divisor function is not periodic, but it is approximated in mean square by the
periodic responses `s_{N₀}` (the trans-horizon gcd tail), which transfers the Cesàro law:

`(1/X) Σ_{k ≤ X} (τ_ε(k+1) - τ_ε(k))² → 2R(ε)`.

On the linear window `k ≤ (B+1)N` the damped response is uniformly within `O(N^{-ε})` of `τ_ε`, so
its gradient energy is `2(B+1)N R(ε) + o(N)` and, by the Dirichlet polarization,

`D̃_N((B+1)N; c_ε)/N → -(B+1) R(ε)`:

the renormalized defect of the damped row dissipates linearly in the window, at an exact rate equal
to the Haar dissipation of `τ_ε`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The cofinal dissipation rate -/

/-- The Bézout limit `Σ_e μ(e) w_ε(e)²`. -/
def dampedBezoutLimit (ε : ℝ) : ℝ := ∑' e : ℕ, moebiusReal e * dampedRamanujanCoeff ε e ^ 2

/-- The Haar dissipation rate `R(ε) = E[τ_ε²] - Σ_e μ(e) w_ε(e)²`. -/
def dampedDissipationRate (ε : ℝ) : ℝ :=
  RHTower.pmPowerDampedSecondDensity ε - dampedBezoutLimit ε

/-- **Cofinal Bézout form.** `Q_Bez(N; c_ε) → Σ_e μ(e) w_ε(e)²`. -/
theorem tendsto_bezoutCoprimeQuadraticForm_pmPowerDamped {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => bezoutCoprimeQuadraticForm N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (dampedBezoutLimit ε)) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  set G : ℕ → ℕ → ℝ := fun N e =>
    if e ∈ Icc 1 N then moebiusReal e * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2
    else 0
  have hfin : ∀ N, bezoutCoprimeQuadraticForm N (pmPowerDampedRealWeight ε) = ∑' e, G N e := by
    intro N
    rw [tsum_eq_sum (s := Icc 1 N) (fun e he => by simp only [G]; rw [if_neg he]),
      bezoutCoprimeQuadraticForm_eq_moebius_diagonal]
    exact sum_congr rfl fun e he => by simp only [G]; rw [if_pos he]
  simp_rw [hfin]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun e => Z ^ 2 * (e : ℝ) ^ (-2 - 2 * ε))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) (fun e => ?_) ?_
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [G, moebiusReal]
    · refine ((tendsto_selbergMultiplesCoord_pmPowerDamped hε (e := e) he).pow 2
        |>.const_mul (moebiusReal e)).congr' ?_
      filter_upwards [eventually_ge_atTop e] with N hN
      simp only [G, mem_Icc, show 1 ≤ e from he, hN, and_self, if_true]
  · filter_upwards with N e
    simp only [G]
    split_ifs with he
    · have he0 : 0 < e := (mem_Icc.mp he).1
      have heR : (0 : ℝ) < e := by exact_mod_cast he0
      have hY : |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e| ≤ (e : ℝ) ^ (-1 - ε) * Z :=
        (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ =>
          abs_pmPowerDampedRealWeight_div_le d).trans (sum_multiples_rpow_le hε N e he0))
      have hpow : ((e : ℝ) ^ (-1 - ε)) ^ 2 = (e : ℝ) ^ (-2 - 2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul heR.le]; push_cast; ring_nf
      have hμ : |moebiusReal e| ≤ 1 := by
        unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      calc |moebiusReal e| * |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e| ^ 2
          ≤ 1 * ((e : ℝ) ^ (-1 - ε) * Z) ^ 2 :=
            mul_le_mul hμ (pow_le_pow_left₀ (abs_nonneg _) hY 2) (sq_nonneg _) zero_le_one
        _ = Z ^ 2 * (e : ℝ) ^ (-2 - 2 * ε) := by rw [one_mul, mul_pow, hpow]; ring
    · rw [norm_zero]
      exact mul_nonneg (sq_nonneg Z) (Real.rpow_nonneg (Nat.cast_nonneg e) _)

/-- **Cofinal dissipation rate.** `R_N(c_ε) → R(ε)`. -/
theorem tendsto_sieveSuccessorReserve_pmPowerDamped {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => sieveSuccessorReserve N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (dampedDissipationRate ε)) :=
  (tendsto_selbergTotientDiagonalForm_pmPowerDamped hε).sub
    (tendsto_bezoutCoprimeQuadraticForm_pmPowerDamped hε)

/-- `R(ε) > 0`: the mode `e = 2` alone dissipates `2 w_ε(2)² > 0`. -/
theorem dampedDissipationRate_pos {ε : ℝ} (hε : 0 < ε) : 0 < dampedDissipationRate ε := by
  -- each summand `(φ(e) - μ(e)) w²` is nonnegative and the limit is a limit of `R_N`
  have hR := tendsto_sieveSuccessorReserve_pmPowerDamped hε
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hw2 : dampedRamanujanCoeff ε 2 ≠ 0 := by
    rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε 2
    push_cast
    exact div_ne_zero (mul_ne_zero hρ.ne' (by norm_num)) hD.ne'
  -- `R_N ≥ 2 Y_N(2)²` for `N ≥ 2`, and `Y_N(2) → w_ε(2)`
  have hlow : ∀ N, 2 ≤ N → 2 * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 2 ^ 2 ≤
      sieveSuccessorReserve N (pmPowerDampedRealWeight ε) := by
    intro N hN
    unfold sieveSuccessorReserve
    rw [selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm_eq_moebius_diagonal, ← sum_sub_distrib]
    have hterm : ∀ e ∈ Icc 1 N, 0 ≤ (Nat.totient e : ℝ) *
        selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ (2 : ℕ) -
        moebiusReal e * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ (2 : ℕ) := by
      intro e he
      have he1 : 1 ≤ e := (mem_Icc.mp he).1
      have hμ : |moebiusReal e| ≤ 1 := by
        unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rcases eq_or_lt_of_le he1 with h | h
      · subst h; simp [moebiusReal]
      · have hφ : (1 : ℝ) ≤ Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr (by omega)
        have hd : 0 ≤ (Nat.totient e : ℝ) - moebiusReal e := by
          linarith [(le_abs_self (moebiusReal e)).trans hμ]
        have := mul_nonneg hd (sq_nonneg (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e))
        linarith
    have h2 : (2 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by norm_num, hN⟩
    have := single_le_sum hterm h2
    simp only [Nat.totient_two, Nat.cast_one, one_mul] at this
    have hμ2 : moebiusReal 2 = -1 := by
      simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    rw [hμ2] at this
    linarith
  have hlim : 2 * dampedRamanujanCoeff ε 2 ^ 2 ≤ dampedDissipationRate ε :=
    le_of_tendsto_of_tendsto (((tendsto_selbergMultiplesCoord_pmPowerDamped hε
      (by norm_num : 0 < 2)).pow 2).const_mul 2) hR
      (eventually_atTop.mpr ⟨2, fun N hN => hlow N hN⟩)
  have : 0 < 2 * dampedRamanujanCoeff ε 2 ^ 2 := by positivity
  linarith

/-! ### Cesàro law of the successor energy -/

/-- For every horizon, `(1/X) Σ_{k ≤ X} (s_N(k+1) - s_N(k))² → 2R_N`. -/
theorem tendsto_mean_successor_energy (N : ℕ) (c : ℕ → ℝ) :
    Tendsto (fun X : ℕ => (∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / X) atTop
      (𝓝 (2 * sieveSuccessorReserve N c)) := by
  set L := N.factorial
  have hL0 : 0 < L := Nat.factorial_pos N
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  set R := sieveSuccessorReserve N c
  set S := ∑ d ∈ Icc 1 N, |c d|
  have hstep : ∀ k, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 ≤ (2 * S) ^ 2 := fun k => by
    have h1 := abs_sieveSeq_le_sum_abs N c (k + 1)
    have h2 := abs_sieveSeq_le_sum_abs N c k
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith)) 2
  -- complete periods
  have hper : ∀ X : ℕ, ∑ k ∈ Icc 1 (X / L * L), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 =
      2 * ((X / L * L : ℕ) : ℝ) * R := by
    intro X
    have hL' : ∀ d ∈ Icc 1 N, d ∣ X / L * L := fun d hd =>
      Dvd.dvd.mul_left (Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2) _
    simpa using sum_addDiff_sieveSeq_sq_sliding_period_eq hL' c 0
  have hbound : ∀ X : ℕ, 0 < X →
      |(∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / X - 2 * R| ≤
        (2 * |R| * L + L * (2 * S) ^ 2) / X := by
    intro X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hjL : X / L * L ≤ X := Nat.div_mul_le_self X L
    have hgap : X - X / L * L < L := by
      have := Nat.lt_div_mul_add (a := X) hL0; omega
    have hsplit : ∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 =
        ∑ k ∈ Icc 1 (X / L * L), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 +
          ∑ k ∈ Ioc (X / L * L) X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 := by
      have hI : Icc 1 X = Ioc 0 X := by ext; simp only [mem_Icc, mem_Ioc]; omega
      have hI' : Icc 1 (X / L * L) = Ioc 0 (X / L * L) := by
        ext; simp only [mem_Icc, mem_Ioc]; omega
      rw [hI, hI', sum_Ioc_consecutive _ (Nat.zero_le _) hjL]
    have hpart0 : 0 ≤ ∑ k ∈ Ioc (X / L * L) X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    have hpart : ∑ k ∈ Ioc (X / L * L) X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 ≤
        L * (2 * S) ^ 2 := by
      calc _ ≤ ∑ k ∈ Ioc (X / L * L) X, (2 * S) ^ 2 := sum_le_sum fun k _ => hstep k
        _ = ((X - X / L * L : ℕ) : ℝ) * (2 * S) ^ 2 := by
            rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
        _ ≤ L * (2 * S) ^ 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hgap.le) (sq_nonneg _)
    have hgapR : (X : ℝ) - ((X / L * L : ℕ) : ℝ) ≤ L := by
      have : ((X - X / L * L : ℕ) : ℝ) = (X : ℝ) - ((X / L * L : ℕ) : ℝ) := by
        rw [Nat.cast_sub hjL]
      rw [← this]; exact_mod_cast hgap.le
    have hjLR : ((X / L * L : ℕ) : ℝ) ≤ X := by exact_mod_cast hjL
    set P := ∑ k ∈ Ioc (X / L * L) X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2
    set J : ℝ := ((X / L * L : ℕ) : ℝ)
    have hE : (∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / X - 2 * R =
        (2 * R * (J - X) + P) / X := by
      rw [hsplit, hper]; field_simp; ring
    rw [hE, abs_div, abs_of_pos hXR]
    refine div_le_div_of_nonneg_right ?_ hXR.le
    have h1 : |2 * R * (J - X)| ≤ 2 * |R| * L := by
      rw [abs_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hjLR)]
      exact mul_le_mul_of_nonneg_left hgapR (by positivity)
    calc |2 * R * (J - X) + P| ≤ |2 * R * (J - X)| + |P| := abs_add_le _ _
      _ ≤ 2 * |R| * L + L * (2 * S) ^ 2 := by rw [abs_of_nonneg hpart0]; linarith
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * |R| * L + L * (2 * S) ^ 2))
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [Real.norm_eq_abs]
  exact hbound X hX

/-- An approximation principle: uniform approximation by convergent sequences whose limits converge. -/
private theorem tendsto_of_uniform_approx {a : ℕ → ℝ} {b : ℕ → ℕ → ℝ} {β D : ℕ → ℝ} {l : ℝ}
    (hb : ∀ n, Tendsto (b n) atTop (𝓝 (β n))) (hβ : Tendsto β atTop (𝓝 l))
    (hD : Tendsto D atTop (𝓝 0)) (happ : ∀ n X, 1 ≤ X → |a X - b n X| ≤ D n) :
    Tendsto a atTop (𝓝 l) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨n, hn1, hn2⟩ := ((hD.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 3 by linarith))).and
    (hβ.eventually (Metric.ball_mem_nhds l (show 0 < δ / 3 by linarith)))).exists
  obtain ⟨X₀, hX₀⟩ := Metric.tendsto_atTop.mp (hb n) (δ / 3) (by linarith)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have h1 := happ n X (le_of_max_le_right hX)
  have h2 := hX₀ X (le_of_max_le_left hX)
  rw [Real.dist_eq] at h2 hn2 ⊢
  calc |a X - l| ≤ |a X - b n X| + |b n X - β n| + |β n - l| := by
        have := abs_sub_le (a X) (b n X) l
        have := abs_sub_le (b n X) (β n) l
        linarith
    _ < δ / 3 + δ / 3 + δ / 3 := by linarith
    _ = δ := by ring

/-- **Cesàro law for the damped divisor function.** `(1/X) Σ_{k ≤ X} (τ_ε(k+1) - τ_ε(k))² → 2R(ε)`. -/
theorem tendsto_mean_divisorCoeff_successor_energy {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℕ => (∑ k ∈ Icc 1 X,
        (RHTower.pmPowerDampedDivisorCoeff ε (k + 1) - RHTower.pmPowerDampedDivisorCoeff ε k) ^ 2) / X)
      atTop (𝓝 (2 * dampedDissipationRate ε)) := by
  set τ := RHTower.pmPowerDampedDivisorCoeff ε
  set c := pmPowerDampedRealWeight ε
  set T := dampedGcdTail ε
  have hT0 := dampedGcdTail_nonneg ε
  -- the adapted comparison parameter and the approximation error
  set η : ℕ → ℝ := fun N => Real.sqrt (T N) + 1 / ((N : ℝ) + 1)
  have hη : ∀ N, 0 < η N := fun N => by simp only [η]; positivity
  set K : ℕ → ℝ := fun N => (1 + 1 / η N) * (8 * T N)
  have hK : ∀ N, K N ≤ 8 * T N + 8 * Real.sqrt (T N) := fun N => by
    have hdiv : T N / η N ≤ Real.sqrt (T N) := by
      rw [div_le_iff₀ (hη N)]
      have h1 := Real.mul_self_sqrt (hT0 N)
      have h3 : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      simp only [η]; nlinarith [Real.sqrt_nonneg (T N)]
    simp only [K]
    have : (1 + 1 / η N) * (8 * T N) = 8 * T N + 8 * (T N / η N) := by ring
    linarith
  set D : ℕ → ℝ := fun N => η N * (1 + η N + K N) + K N
  have hsqrt : Tendsto (fun N => Real.sqrt (T N)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_dampedGcdTail hε)
    rwa [Real.sqrt_zero] at this
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := hsqrt.add h2
    rw [add_zero] at h3
    exact h3
  have hKlim : Tendsto K atTop (𝓝 0) := by
    refine squeeze_zero (fun N => mul_nonneg (by have := hη N; positivity) (by linarith [hT0 N])) hK ?_
    simpa using ((tendsto_dampedGcdTail hε).const_mul 8).add (hsqrt.const_mul 8)
  have hDlim : Tendsto D atTop (𝓝 0) := by
    simpa using (hηlim.mul ((hηlim.const_add 1).add hKlim)).add hKlim
  refine tendsto_of_uniform_approx (b := fun N X =>
      (∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / X)
    (fun N => tendsto_mean_successor_energy N c)
    ((tendsto_sieveSuccessorReserve_pmPowerDamped hε).const_mul 2) hDlim ?_
  intro N X hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  set a := (∑ k ∈ Icc 1 X, (τ (k + 1) - τ k) ^ 2) / X
  set b := (∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / X
  set u : ℕ → ℝ := fun k => τ k - sieveSeq N c k
  -- the mean square of the approximation gradient
  have hu : ∑ k ∈ Icc 1 X, (u (k + 1) - u k) ^ 2 ≤ X * (8 * T N) := by
    have h1 : ∑ k ∈ Icc 1 (X + 1), u k ^ 2 ≤ ((X + 1 : ℕ) : ℝ) * T N :=
      (sum_sq_divisorCoeff_sub_sieveSeq_le ε N (X + 1)).trans
        (mul_le_mul_of_nonneg_left (sum_box_le_dampedGcdTail hε N (X + 1)) (Nat.cast_nonneg _))
    have hshift : ∑ k ∈ Icc 1 X, u (k + 1) ^ 2 ≤ ∑ k ∈ Icc 1 (X + 1), u k ^ 2 := by
      have : ∑ k ∈ Icc 1 X, u (k + 1) ^ 2 = ∑ k ∈ Icc 2 (X + 1), u k ^ 2 := by
        refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_ <;> intro k hk <;>
          simp only [mem_Icc] at hk ⊢ <;> omega
      rw [this]
      exact sum_le_sum_of_subset_of_nonneg (fun k hk => by simp only [mem_Icc] at hk ⊢; omega)
        fun _ _ _ => sq_nonneg _
    have hbase : ∑ k ∈ Icc 1 X, u k ^ 2 ≤ ∑ k ∈ Icc 1 (X + 1), u k ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (fun k hk => by simp only [mem_Icc] at hk ⊢; omega)
        fun _ _ _ => sq_nonneg _
    calc ∑ k ∈ Icc 1 X, (u (k + 1) - u k) ^ 2 ≤ ∑ k ∈ Icc 1 X, (2 * u (k + 1) ^ 2 + 2 * u k ^ 2) :=
          sum_le_sum fun k _ => by nlinarith [sq_nonneg (u (k + 1) + u k)]
      _ = 2 * ∑ k ∈ Icc 1 X, u (k + 1) ^ 2 + 2 * ∑ k ∈ Icc 1 X, u k ^ 2 := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ 4 * (((X + 1 : ℕ) : ℝ) * T N) := by linarith
      _ ≤ X * (8 * T N) := by
          push_cast
          have : (X : ℝ) + 1 ≤ 2 * X := by
            have : (1 : ℝ) ≤ X := by exact_mod_cast hX
            linarith
          nlinarith [hT0 N]
  -- the two comparison inequalities
  have hηN := hη N
  have hcmp1 : a ≤ (1 + η N) * b + K N := by
    have hpt : ∀ k ∈ Icc 1 X, (τ (k + 1) - τ k) ^ 2 ≤ (1 + η N) *
        (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 + (1 + 1 / η N) * (u (k + 1) - u k) ^ 2 :=
      fun k _ => by
        have := sq_add_le_weighted (sieveSeq N c (k + 1) - sieveSeq N c k) (u (k + 1) - u k) hηN
        have key : τ (k + 1) - τ k =
            (sieveSeq N c (k + 1) - sieveSeq N c k) + (u (k + 1) - u k) := by simp only [u]; ring
        rw [key]; exact this
    have hs := sum_le_sum hpt
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
    simp only [a, b, K]
    rw [div_le_iff₀ hXR]
    have : (1 + 1 / η N) * ∑ k ∈ Icc 1 X, (u (k + 1) - u k) ^ 2 ≤ (1 + 1 / η N) * (X * (8 * T N)) :=
      mul_le_mul_of_nonneg_left hu (by have := hη N; positivity)
    have hexp : ((1 + η N) * ((∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / X) +
        (1 + 1 / η N) * (8 * T N)) * X = (1 + η N) *
          (∑ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) +
        (1 + 1 / η N) * (X * (8 * T N)) := by field_simp
    rw [hexp]; linarith
  have hcmp2 : b ≤ (1 + η N) * a + K N := by
    have hpt : ∀ k ∈ Icc 1 X, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 ≤ (1 + η N) *
        (τ (k + 1) - τ k) ^ 2 + (1 + 1 / η N) * (u (k + 1) - u k) ^ 2 := fun k _ => by
      have := sq_add_le_weighted (τ (k + 1) - τ k) (-(u (k + 1) - u k)) hηN
      rw [neg_sq] at this
      have key : sieveSeq N c (k + 1) - sieveSeq N c k =
          (τ (k + 1) - τ k) + -(u (k + 1) - u k) := by simp only [u]; ring
      rw [key]; exact this
    have hs := sum_le_sum hpt
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
    simp only [a, b, K]
    rw [div_le_iff₀ hXR]
    have : (1 + 1 / η N) * ∑ k ∈ Icc 1 X, (u (k + 1) - u k) ^ 2 ≤ (1 + 1 / η N) * (X * (8 * T N)) :=
      mul_le_mul_of_nonneg_left hu (by have := hη N; positivity)
    have hexp : ((1 + η N) * ((∑ k ∈ Icc 1 X, (τ (k + 1) - τ k) ^ 2) / X) +
        (1 + 1 / η N) * (8 * T N)) * X = (1 + η N) * (∑ k ∈ Icc 1 X, (τ (k + 1) - τ k) ^ 2) +
        (1 + 1 / η N) * (X * (8 * T N)) := by field_simp
    rw [hexp]; linarith
  -- `a ≤ 1` since `0 ≤ τ ≤ 1`
  have ha1 : a ≤ 1 := by
    simp only [a]
    rw [div_le_one hXR]
    calc ∑ k ∈ Icc 1 X, (τ (k + 1) - τ k) ^ 2 ≤ ∑ k ∈ Icc 1 X, (1 : ℝ) := sum_le_sum fun k _ => by
          have h1 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le (k + 1)
          have h2 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le (k + 1)
          have h3 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le k
          have h4 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le k
          nlinarith
      _ = X := by simp
  have ha0 : 0 ≤ a := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hXR.le
  have hK0 : 0 ≤ K N := mul_nonneg (by have := hη N; positivity) (by linarith [hT0 N])
  have hb1 : b ≤ 1 + η N + K N := by nlinarith
  have hηb : η N * b ≤ η N * (1 + η N + K N) := mul_le_mul_of_nonneg_left hb1 hηN.le
  have hηa : η N * a ≤ η N * (1 + η N + K N) := by
    apply mul_le_mul_of_nonneg_left _ hηN.le; linarith
  simp only [D]
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The linear defect -/

/-- **Exact linear dissipation.** For every `ε > 0` and band `B`,
`D̃_N((B+1)N; c_ε)/N → -(B+1) R(ε)`. -/
theorem tendsto_sieveRenormalizedPrefixDefect_pmPowerDamped_linear {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    Tendsto (fun N : ℕ =>
        sieveRenormalizedPrefixDefect N ((B + 1) * N) (pmPowerDampedRealWeight ε) / N)
      atTop (𝓝 (-((B : ℝ) + 1) * dampedDissipationRate ε)) := by
  set c := pmPowerDampedRealWeight ε
  set τ := RHTower.pmPowerDampedDivisorCoeff ε
  set δ : ℕ → ℝ := fun N => ((B + 1 : ℕ) : ℝ) * ((N : ℝ) + 1) ^ (-ε)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-ε)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hε).comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have h2 := h.const_mul ((B + 1 : ℕ) : ℝ)
    rw [mul_zero] at h2
    exact h2
  -- uniform approximation on `[1, (B+1)N + 1] ⊆ [1, (B+2)N]`
  have happ : ∀ N, 1 ≤ N → ∀ k, 1 ≤ k → k ≤ (B + 1) * N + 1 → |τ k - sieveSeq N c k| ≤ δ N := by
    intro N hN k hk1 hk
    exact abs_divisorCoeff_sub_sieveSeq_le hε.le (B := B + 1) hk1 (by nlinarith)
  -- the Cesàro gradient energy of `τ` on the window
  have hX : Tendsto (fun N : ℕ => (B + 1) * N) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega : 0 < B + 1)
  have hces := ((tendsto_mean_divisorCoeff_successor_energy hε).comp hX).const_mul ((B : ℝ) + 1)
  have hGτ : Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 ((B + 1) * N), (τ (k + 1) - τ k) ^ 2) / N) atTop
      (𝓝 (((B : ℝ) + 1) * (2 * dampedDissipationRate ε))) := by
    refine hces.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Function.comp_apply, τ]
    push_cast
    field_simp
  -- compare the gradient energies of `s_N` and `τ`
  have hGdiff : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((B + 1) * N), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) / N -
        (∑ k ∈ Icc 1 ((B + 1) * N), (τ (k + 1) - τ k) ^ 2) / N) atTop (𝓝 0) := by
    have hbnd : Tendsto (fun N : ℕ => ((B : ℝ) + 1) * (2 * δ N * (2 + 2 * δ N))) atTop (𝓝 0) := by
      simpa using ((hδlim.const_mul 2).mul ((hδlim.const_mul 2).const_add 2)).const_mul ((B : ℝ) + 1)
    refine squeeze_zero_norm' ?_ hbnd
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hδ0 : 0 ≤ δ N := by simp only [δ]; positivity
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hNR, div_le_iff₀ hNR, ← sum_sub_distrib]
    calc |∑ k ∈ Icc 1 ((B + 1) * N), ((sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2 -
          (τ (k + 1) - τ k) ^ 2)|
        ≤ ∑ k ∈ Icc 1 ((B + 1) * N), 2 * δ N * (2 + 2 * δ N) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
          obtain ⟨hk1, hkX⟩ := mem_Icc.mp hk
          have e1 := happ N hN k hk1 (by omega)
          have e2 := happ N hN (k + 1) (by omega) (by omega)
          have hτ1 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le (k + 1)
          have hτ2 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le (k + 1)
          have hτ3 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le k
          have hτ4 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le k
          set x := sieveSeq N c (k + 1) - sieveSeq N c k
          set y := τ (k + 1) - τ k
          have hxy : |x - y| ≤ 2 * δ N := by
            rw [abs_le] at e1 e2 ⊢; simp only [x, y]; constructor <;> linarith
          have hy : |y| ≤ 1 := by rw [abs_le]; simp only [y]; constructor <;> linarith
          have hxpy : |x + y| ≤ 2 + 2 * δ N := by
            calc |x + y| = |(x - y) + 2 * y| := by ring_nf
              _ ≤ |x - y| + |2 * y| := abs_add_le _ _
              _ ≤ 2 * δ N + 2 := by rw [abs_mul]; norm_num; linarith
              _ = 2 + 2 * δ N := by ring
          rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
          exact mul_le_mul hxy hxpy (abs_nonneg _) (by linarith)
      _ = ((B + 1) * N : ℕ) * (2 * δ N * (2 + 2 * δ N)) := by
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ = ((B : ℝ) + 1) * (2 * δ N * (2 + 2 * δ N)) * N := by push_cast; ring
  -- boundary terms
  have hbdry : Tendsto (fun N : ℕ =>
      (sieveSeq N c ((B + 1) * N + 1) ^ 2 - sieveSeq N c 1 ^ 2) / N) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => 2 * (1 + δ N) ^ 2 / N) atTop (𝓝 0) := by
      have h := ((hδlim.const_add 1).pow 2).const_mul 2
      simp only [add_zero, one_pow, mul_one] at h
      exact h.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hδ0 : 0 ≤ δ N := by simp only [δ]; positivity
    have hsb : ∀ k, 1 ≤ k → k ≤ (B + 1) * N + 1 → |sieveSeq N c k| ≤ 1 + δ N := by
      intro k hk1 hk
      have e := happ N hN k hk1 hk
      have h1 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le k
      have h2 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le k
      rw [abs_le] at e ⊢; constructor <;> linarith
    have b1 := hsb ((B + 1) * N + 1) (by omega) le_rfl
    have b2 := hsb 1 le_rfl (by omega)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hNR]
    refine div_le_div_of_nonneg_right ?_ hNR.le
    have q1 : sieveSeq N c ((B + 1) * N + 1) ^ 2 ≤ (1 + δ N) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b1 2
    have q2 : sieveSeq N c 1 ^ 2 ≤ (1 + δ N) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b2 2
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (sieveSeq N c ((B + 1) * N + 1)),
      sq_nonneg (sieveSeq N c 1)]
  -- assemble the polarization identity
  have h := ((hbdry.sub (hGdiff.add hGτ)).div_const 2)
  rw [zero_add, show ((0 : ℝ) - ((B : ℝ) + 1) * (2 * dampedDissipationRate ε)) / 2 =
    -((B : ℝ) + 1) * dampedDissipationRate ε by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hpol := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary N ((B + 1) * N) c
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
