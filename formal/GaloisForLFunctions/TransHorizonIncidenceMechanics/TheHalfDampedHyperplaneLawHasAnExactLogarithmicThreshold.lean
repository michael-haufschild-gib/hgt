import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The half-damped hyperplane law has an exact logarithmic threshold

Let `K(s) = Σ_j k(j) j^{-s}`. Below half damping the paid perturbations `k ⋆ d^{-ε}` of the critical
Wiener algebra `Σ_j |k(j)| j^{-1/2} < ∞` form the hyperplane `K(1 − ε) = 0`
(`receiverBounded_dirichletConv_unit_iff_critical`). At half damping the law changes:

* **The little-o pole law.** If `Σ_d |c(d)| d^{-θ} < ∞` for every `θ > 1/2` and the receiver of `c`
  is bounded, then `√u · |C(1/2 + u) − m| → 0` as `u ↓ 0`, `C(σ) = Σ_d c(d) d^{-σ}`, `m = Σ_d c(d)/d`
  (`tendsto_sqrt_mul_abs_dirichletSeries_sub_mean`). The Mellin pairing splits into a finite head,
  bounded in `u`, and a tail of size `√(tail energy) · O(u^{-1/2})`; `|ζ(σ)| ≥ 1` on `[1/2, 1)`.
* **The positive half.** At half damping a pole-free dilation `b_j` has energy `O((1 + log j)/j)`:
  below `j` the power sum `Σ_{n<j} n^{-2ε}` becomes the harmonic sum. On the `√log`-weighted algebra
  `Σ_j |k(j)| j^{-1/2} √(1 + log j) < ∞` the receiver of `k ⋆ d^{-1/2}` is therefore paid iff
  `K(1/2) = 0` (`receiverBounded_dirichletConv_unit_half_iff`).
* **The lacunary kernel.** `k = Σ_r 2^{-(r+1)} J_r^{1/2} δ_{J_r} − δ_1`, `J_r = 2^{4^{r+1}}`, has
  `K(1/2) = 0` and lies in `Σ_j |k(j)| j^{-1/2} (1 + log j)^α < ∞` for every `0 ≤ α < 1/2`. Its
  Dirichlet series is `K(1/2 + u) Σ_d d^{-1-u}` with `−K(1/2 + u) = Σ_r 2^{-(r+1)} (1 − J_r^{-u})`.
  At the probe `u_R = 4^{-(R+1)}`, where `J_R^{-u_R} = 1/2`, this is `≥ 2^R = u_R^{-1/2}/2`, so the
  little-o law refutes payment (`not_receiverBounded_dirichletConv_lacunaryKernel`).

Hence the hyperplane law holds on the whole critical Wiener algebra exactly below half damping
(`criticalWiener_hyperplaneLaw_iff_lt_half`), and at half damping exactly on the `√log`-weighted
algebra: no smaller power of the logarithm suffices
(`halfDamped_hyperplaneLaw_logarithmic_threshold`).
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The little-o pole law -/

/-- A Mellin cell is at most `1`. -/
theorem mellinCell_le_one {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) : mellinCell σ n ≤ 1 := by
  have h1 : 0 ≤ ((n : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have h2 : (n : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  unfold mellinCell
  linarith

/-- **Head–tail bound.** At `σ = 1/2 + u`, `0 < u ≤ 1/2`, if the energy of `A` beyond `N` is at
most `R`, then `√u |Σ_n A(n) Δ_n(σ)| ≤ √u Σ_{n ≤ N} |A(n)| + 2√R`. -/
theorem sqrt_mul_abs_tsum_mul_mellinCell_le {A : ℕ → ℝ} (hA0 : A 0 = 0) {u : ℝ} (hu : 0 < u)
    (hu1 : u ≤ 1 / 2) (hs : Summable (fun n => A n * mellinCell (1 / 2 + u) n)) (N : ℕ) {R : ℝ}
    (hR : ∀ T, ∑ n ∈ Icc 1 T, (if N < n then A n else 0) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ R) :
    Real.sqrt u * |∑' n, A n * mellinCell (1 / 2 + u) n| ≤
      Real.sqrt u * ∑ n ∈ range (N + 1), |A n| + 2 * Real.sqrt R := by
  have hσ : (1 : ℝ) / 2 < 1 / 2 + u := by linarith
  have hσ0 : (0 : ℝ) < 1 / 2 + u := by linarith
  have hbd : ∀ B : ℕ → ℝ, (∀ n, |B n| ≤ |A n|) →
      Summable (fun n => B n * mellinCell (1 / 2 + u) n) := fun B hB =>
    hs.abs.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
  have htail := hbd (fun n => if N < n then A n else 0) fun n => by split_ifs <;> simp
  have hhead := hbd (fun n => if N < n then 0 else A n) fun n => by split_ifs <;> simp
  have hsplit : ∀ n, A n * mellinCell (1 / 2 + u) n =
      (if N < n then A n else 0) * mellinCell (1 / 2 + u) n +
        (if N < n then 0 else A n) * mellinCell (1 / 2 + u) n := fun n => by
    split_ifs <;> ring
  -- the head is a finite sum of size at most `Σ_{n ≤ N} |A(n)|`
  have hheadsum : ∑' n, (if N < n then 0 else A n) * mellinCell (1 / 2 + u) n =
      ∑ n ∈ range (N + 1), (if N < n then 0 else A n) * mellinCell (1 / 2 + u) n :=
    tsum_eq_sum fun n hn => by
      rw [mem_range, not_lt] at hn
      rw [if_pos (by omega), zero_mul]
  have hheadle : |∑ n ∈ range (N + 1), (if N < n then 0 else A n) * mellinCell (1 / 2 + u) n| ≤
      ∑ n ∈ range (N + 1), |A n| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hA0]
    · have hΔ := mellinCell_nonneg hσ0 hn
      have h1 : |if N < n then 0 else A n| ≤ |A n| := by split_ifs <;> simp
      rw [abs_mul, abs_of_nonneg hΔ]
      calc |if N < n then 0 else A n| * mellinCell (1 / 2 + u) n ≤ |A n| * 1 :=
            mul_le_mul h1 (mellinCell_le_one hσ0 hn) hΔ (abs_nonneg _)
        _ = |A n| := mul_one _
  -- the tail is paid by its energy
  have htaille := abs_tsum_mul_mellinCell_le hσ (f := fun n => if N < n then A n else 0)
    (by simp) htail hR
  -- `u · 2σ²(1 + 1/(2σ − 1)) = σ²(2u + 1) ≤ 4`
  have hcell : Real.sqrt u *
      Real.sqrt (2 * (1 / 2 + u) ^ 2 * (1 + 1 / (2 * (1 / 2 + u) - 1))) ≤ 2 := by
    have hu0 : u ≠ 0 := hu.ne'
    rw [← Real.sqrt_mul hu.le, show 2 * (1 / 2 + u) - 1 = 2 * u by ring]
    have heq : u * (2 * (1 / 2 + u) ^ 2 * (1 + 1 / (2 * u))) = (1 / 2 + u) ^ 2 * (2 * u + 1) := by
      field_simp
    have h1 : (1 / 2 + u) ^ 2 ≤ 1 := by nlinarith
    have h2 := mul_le_mul h1 (show 2 * u + 1 ≤ 2 by linarith) (by linarith) zero_le_one
    rw [heq]
    calc Real.sqrt ((1 / 2 + u) ^ 2 * (2 * u + 1)) ≤ Real.sqrt (2 ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 2 := Real.sqrt_sq (by norm_num)
  rw [tsum_congr hsplit, htail.tsum_add hhead, hheadsum]
  have hsR := Real.sqrt_nonneg R
  have hsu := Real.sqrt_nonneg u
  calc Real.sqrt u * |∑' n, (if N < n then A n else 0) * mellinCell (1 / 2 + u) n +
        ∑ n ∈ range (N + 1), (if N < n then 0 else A n) * mellinCell (1 / 2 + u) n|
      ≤ Real.sqrt u * (Real.sqrt R *
          Real.sqrt (2 * (1 / 2 + u) ^ 2 * (1 + 1 / (2 * (1 / 2 + u) - 1))) +
          ∑ n ∈ range (N + 1), |A n|) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add htaille hheadle)) hsu
    _ = Real.sqrt R * (Real.sqrt u *
          Real.sqrt (2 * (1 / 2 + u) ^ 2 * (1 + 1 / (2 * (1 / 2 + u) - 1)))) +
          Real.sqrt u * ∑ n ∈ range (N + 1), |A n| := by ring
    _ ≤ Real.sqrt R * 2 + Real.sqrt u * ∑ n ∈ range (N + 1), |A n| := by gcongr
    _ = Real.sqrt u * ∑ n ∈ range (N + 1), |A n| + 2 * Real.sqrt R := by ring

/-- **A paid sequence has a Mellin transform of size `o(u^{-1/2})` at the critical point.** If
the pronic energies of `A`, `A(0) = 0`, are bounded, then `√u |Σ_n A(n) Δ_n(1/2 + u)| → 0` as
`u ↓ 0`: the tail energies beyond `N` tend to `0`, and the head up to `N` is bounded in `u`. -/
theorem tendsto_sqrt_mul_abs_tsum_mul_mellinCell {A : ℕ → ℝ} (hA0 : A 0 = 0) {E : ℝ}
    (hE : ∀ T, ∑ n ∈ Icc 1 T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E)
    (hs : ∀ u : ℝ, 0 < u → u < 1 / 2 → Summable (fun n => A n * mellinCell (1 / 2 + u) n)) :
    Tendsto (fun u : ℝ => Real.sqrt u * |∑' n, A n * mellinCell (1 / 2 + u) n|) (𝓝[>] 0)
      (𝓝 0) := by
  have he0 : ∀ n : ℕ, 0 ≤ A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := fun n => by positivity
  have hesum : Summable (fun n : ℕ => A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    refine summable_of_sum_range_le he0 (c := E) fun T => ?_
    calc ∑ n ∈ range T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ range (T + 1), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ T))
            fun n _ _ => he0 n
      _ = ∑ n ∈ Icc 1 T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          sum_range_succ_eq_sum_Icc_one (by simp [hA0]) T
      _ ≤ E := hE T
  -- the tail energies `Σ_{n > N} A(n)²/(n(n+1))` tend to `0`
  have hite : ∀ N : ℕ, Summable (fun n : ℕ =>
      if N < n then A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) := fun N =>
    hesum.of_nonneg_of_le (fun n => by split_ifs <;> simp [he0 n])
      (fun n => by split_ifs <;> simp [he0 n])
  have hR : Tendsto (fun N : ℕ => ∑' n : ℕ,
      if N < n then A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (N n : ℕ) => if N < n then A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) else 0)
      (g := fun _ => (0 : ℝ)) hesum
      (fun n => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop n] with N hN
        simp [not_lt.mpr hN]))
      (Eventually.of_forall fun N n => by
        split_ifs
        · rw [Real.norm_eq_abs, abs_of_nonneg (he0 n)]
        · simp [he0 n])
    simpa only [tsum_zero] using h
  have hRs := hR.sqrt
  rw [Real.sqrt_zero] at hRs
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun u => ha.trans_le (by positivity),
    fun a ha => ?_⟩
  obtain ⟨N, hN⟩ := (hRs.eventually (gt_mem_nhds (show (0 : ℝ) < a / 4 by positivity))).exists
  have hhead : Tendsto (fun u : ℝ => Real.sqrt u * ∑ n ∈ range (N + 1), |A n|) (𝓝[>] 0)
      (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).mul_const
      (∑ n ∈ range (N + 1), |A n|)
    rwa [Real.sqrt_zero, zero_mul] at h
  filter_upwards [hhead.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by positivity)),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with u hu hu'
  have hb := sqrt_mul_abs_tsum_mul_mellinCell_le hA0 hu'.1 hu'.2.le (hs u hu'.1 hu'.2) N
    (R := ∑' n : ℕ, if N < n then A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) fun T => by
      calc ∑ n ∈ Icc 1 T, (if N < n then A n else 0) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
          = ∑ n ∈ Icc 1 T, (if N < n then A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) :=
            sum_congr rfl fun n _ => by split_ifs <;> simp
        _ ≤ _ := (hite N).sum_le_tsum _ fun n _ => by split_ifs <;> simp [he0 n]
  linarith

/-- **The little-o pole law at half damping.** Let `Σ_d |c(d)| d^{-θ} < ∞` for every `θ > 1/2`. If
the receiver of `c` is bounded, then `√u · |C(1/2 + u) − m| → 0` as `u ↓ 0`, where
`C(σ) = Σ_d c(d) d^{-σ}` and `m = Σ_d c(d)/d`: the Mellin pairing is `ζ(σ)(C(σ) − m)` and
`|ζ(σ)| ≥ 1` on `[1/2, 1)`. -/
theorem tendsto_sqrt_mul_abs_dirichletSeries_sub_mean {c : ℕ → ℝ}
    (hc : ∀ θ : ℝ, 1 / 2 < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hB : ReceiverBounded c) :
    Tendsto (fun u : ℝ => Real.sqrt u *
      |(∑' d : ℕ, c d * (d : ℝ) ^ (-(1 / 2 + u))) - ∑' d : ℕ, c d / d|) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨E, hE⟩ := hB
  have hpair : ∀ u : ℝ, 0 < u → u < 1 / 2 →
      Summable (fun n =>
        weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell (1 / 2 + u) n) ∧
      |(∑' d : ℕ, c d * (d : ℝ) ^ (-(1 / 2 + u))) - ∑' d : ℕ, c d / d| ≤
        |∑' n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell (1 / 2 + u) n| := by
    intro u hu hu2
    obtain ⟨hsA, hid⟩ := mellinPairing_eq_zeta_mul_of_summable (θ := 1 / 2 + u / 2)
      (σ := 1 / 2 + u) (by linarith) (by linarith) (by linarith) (hc _ (by linarith))
    refine ⟨hsA, ?_⟩
    have hnorm : |∑' n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell (1 / 2 + u) n| =
        ‖riemannZeta ((1 / 2 + u : ℝ) : ℂ)‖ *
          |(∑' d : ℕ, c d * (d : ℝ) ^ (-(1 / 2 + u))) - ∑' d : ℕ, c d / d| := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hid, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
    have hz := div_le_norm_riemannZeta (σ := 1 / 2 + u) (by linarith) (by linarith)
    have h1 : 1 ≤ (1 / 2 + u) / (1 - (1 / 2 + u)) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    rw [hnorm]
    exact le_mul_of_one_le_left (abs_nonneg _) (h1.trans hz)
  have hlim := tendsto_sqrt_mul_abs_tsum_mul_mellinCell
    (A := weightCenteredPrefix c (∑' d : ℕ, c d / d)) (weightCenteredPrefix_zero c _) hE
    fun u hu hu2 => (hpair u hu hu2).1
  refine squeeze_zero' (Eventually.of_forall fun u => by positivity) ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with u hu
  exact mul_le_mul_of_nonneg_left (hpair u hu.1 hu.2).2 (Real.sqrt_nonneg u)

/-! ### The positive half: the `√log`-weighted algebra -/

/-- `1 + log j ≥ 1` on the naturals (`log 0 = 0`). -/
theorem one_le_one_add_log_natCast (j : ℕ) : 1 ≤ 1 + Real.log j := by
  have := Real.log_natCast_nonneg j
  linarith

/-- **At half damping a pole-free dilation has receiver energy `O((1 + log j)/j)`.** Below `j`
the prefix is `−j^{-1/2} A_q(n) − m_q n/j` with `|A_q(n)| ≤ 5√n`, whose pronic energy is a
harmonic sum; beyond `j` the bound `O(1/j)` holds at every damping. -/
theorem exists_weightPronicEnergy_poleFreeDilation_half_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 1 ≤ j → ∀ T : ℕ,
      weightPronicEnergy (poleFreeDilation (1 / 2) j) (poleFreeMean (1 / 2) j) T ≤
        C * (1 + Real.log j) / j := by
  set Z := ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d with hZ
  set Cb : ℝ := 8 + 2 * (2 / (1 - 1 / 2) + 4) ^ 2 * (1 + 1 / (1 / 2)) with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; norm_num
  have hZ0 : 0 ≤ Z := tsum_nonneg fun d => by
    simp only [dampedSignWeight, unitSign, one_mul]; positivity
  refine ⟨50 + 2 * Z ^ 2 + Cb, by positivity, fun j hj T => ?_⟩
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj0' : (j : ℝ) ≠ 0 := hj0.ne'
  have hL := one_le_one_add_log_natCast j
  set A := weightCenteredPrefix (poleFreeDilation (1 / 2) j) (poleFreeMean (1 / 2) j) with hAdef
  rw [weightPronicEnergy, ← sum_filter_add_sum_filter_not (Icc 1 T) (· < j)]
  -- below the dilation: `A(n)²/(n(n+1)) ≤ 50/(jn) + 2Z²/j²`
  have hlow : ∑ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (50 * (1 + Real.log j) + 2 * Z ^ 2) / j := by
    have hterm : ∀ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        50 / j * (1 / (n : ℝ)) + 2 * Z ^ 2 / (j : ℝ) ^ 2 := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
      have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
      have hb := abs_weightCenteredPrefix_poleFreeDilation_le_of_lt (ε := 1 / 2) (by norm_num)
        (by norm_num) hn.1.1 hn.2
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        show (1 : ℝ) + 1 / (1 / 2) + 1 / (1 / 2) = 5 by norm_num] at hb
      have hjs : ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / j := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hj0.le, show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by
          norm_num, Real.rpow_neg_one, one_div]
      have hns : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
      have hsq : A n ^ 2 ≤ 50 * n / j + 2 * Z ^ 2 * (n : ℝ) ^ 2 / (j : ℝ) ^ 2 := by
        have h1 : A n ^ 2 ≤
            ((j : ℝ) ^ (-(1 / 2 : ℝ)) * (5 * (n : ℝ) ^ (1 / 2 : ℝ)) + Z * n / j) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have key : ∀ X Y : ℝ, (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := fun X Y => by
          nlinarith [sq_nonneg (X - Y)]
        have h2 : ((j : ℝ) ^ (-(1 / 2 : ℝ)) * (5 * (n : ℝ) ^ (1 / 2 : ℝ))) ^ 2 = 25 * n / j := by
          rw [mul_pow, mul_pow, hjs, hns]; ring
        have h3 : (Z * n / j) ^ 2 = Z ^ 2 * (n : ℝ) ^ 2 / (j : ℝ) ^ 2 := by ring
        calc A n ^ 2 ≤ _ := h1
          _ ≤ _ := key _ _
          _ = 50 * n / j + 2 * Z ^ 2 * (n : ℝ) ^ 2 / (j : ℝ) ^ 2 := by rw [h2, h3]; ring
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      rw [div_le_iff₀ hpr]
      have e1 : (50 / j * (1 / (n : ℝ)) + 2 * Z ^ 2 / (j : ℝ) ^ 2) * ((n : ℝ) * ((n : ℝ) + 1)) =
          50 * ((n : ℝ) + 1) / j + 2 * Z ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) / (j : ℝ) ^ 2 := by
        field_simp
      rw [e1]
      have e2 : 50 * (n : ℝ) / j ≤ 50 * ((n : ℝ) + 1) / j := by gcongr; linarith
      have e3 : 2 * Z ^ 2 * (n : ℝ) ^ 2 / (j : ℝ) ^ 2 ≤
          2 * Z ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) / (j : ℝ) ^ 2 := by
        gcongr; nlinarith
      linarith
    have hsub : (Icc 1 T).filter (· < j) ⊆ Icc 1 j := fun n hn => by
      simp only [mem_filter, mem_Icc] at hn ⊢; omega
    have hcard : (((Icc 1 T).filter (· < j)).card : ℝ) ≤ j := by
      have := card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hharm : ∑ n ∈ (Icc 1 T).filter (· < j), 1 / (n : ℝ) ≤ 1 + Real.log j :=
      (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity).trans
        (RHTower.Sieve.sum_Icc_one_div_le_one_add_log j)
    calc ∑ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ (Icc 1 T).filter (· < j), (50 / j * (1 / (n : ℝ)) + 2 * Z ^ 2 / (j : ℝ) ^ 2) :=
          sum_le_sum hterm
      _ = 50 / j * ∑ n ∈ (Icc 1 T).filter (· < j), 1 / (n : ℝ) +
            (((Icc 1 T).filter (· < j)).card : ℝ) * (2 * Z ^ 2 / (j : ℝ) ^ 2) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ 50 / j * (1 + Real.log j) + (j : ℝ) * (2 * Z ^ 2 / (j : ℝ) ^ 2) := by gcongr
      _ = (50 * (1 + Real.log j) + 2 * Z ^ 2) / j := by field_simp
  -- beyond the dilation
  have hhigh : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      Cb / j := by
    have hfil : (Icc 1 T).filter (fun n => ¬ n < j) = Icc j T := by
      ext n; simp only [mem_filter, mem_Icc, not_lt]; omega
    rw [hfil, hCb]
    exact sum_Icc_sq_poleFreeDilation_beyond_le (by norm_num) (by norm_num) hj T
  calc _ ≤ (50 * (1 + Real.log j) + 2 * Z ^ 2) / j + Cb / j := add_le_add hlow hhigh
    _ = (50 * (1 + Real.log j) + 2 * Z ^ 2 + Cb) / j := by ring
    _ ≤ (50 + 2 * Z ^ 2 + Cb) * (1 + Real.log j) / j := by
        gcongr
        nlinarith [mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg Z))
          hCb0) (sub_nonneg.mpr hL)]

/-- A critical Wiener kernel converges absolutely against `j^{-σ}` for every `σ ≥ 1/2`. -/
theorem CriticalWiener.summable_abs_mul_rpow {k : ℕ → ℝ} (hk : CriticalWiener k) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-σ)) :=
  hk.of_nonneg_of_le (fun j => by positivity) fun j => by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [Nat.cast_zero, Real.zero_rpow (show -σ ≠ 0 by intro h; linarith),
        Real.zero_rpow (show -(1 / 2 : ℝ) ≠ 0 by norm_num), le_refl]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)

/-- The `√log`-weighted algebra lies in the critical Wiener algebra. -/
theorem criticalWiener_of_sqrt_log {k : ℕ → ℝ}
    (hk : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log j))) :
    CriticalWiener k :=
  hk.of_nonneg_of_le (fun j => by positivity) fun j =>
    le_mul_of_one_le_right (by positivity) (Real.one_le_sqrt.mpr (one_le_one_add_log_natCast j))

/-- **On the `√log`-weighted algebra a vanishing pole value pays the half-damped smooth power.**
Minkowski over the pole-free dilations with weights `√C j^{-1/2} √(1 + log j)`. -/
theorem receiverBounded_dirichletConv_unit_half_of_sqrt_log {k : ℕ → ℝ}
    (hk : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log j)))
    (hK : ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 / 2 : ℝ)) = 0) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) := by
  obtain ⟨C, hC0, hC⟩ := exists_weightPronicEnergy_poleFreeDilation_half_le
  have hCW : CriticalWiener k := criticalWiener_of_sqrt_log hk
  have hhalf : -(1 - 1 / 2 : ℝ) = -(1 / 2) := by norm_num
  refine receiverBounded_dirichletConv_unit_of_poleFree (ε := 1 / 2) (by norm_num) (by norm_num)
    (w := fun j => Real.sqrt C * ((j : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log j)))
    (fun j hj T => ?_) (fun j => by positivity)
    ((hk.mul_left (Real.sqrt C)).congr fun j => by ring) ?_ hCW.summable_abs_div ?_
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hL : 0 ≤ 1 + Real.log j := by linarith [one_le_one_add_log_natCast j]
    have hpow : ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / j := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0.le, show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by
        norm_num, Real.rpow_neg_one, one_div]
    rw [mul_pow, mul_pow, Real.sq_sqrt hC0, hpow, Real.sq_sqrt hL]
    calc _ ≤ C * (1 + Real.log j) / j := hC j hj T
      _ = C * (1 / j * (1 + Real.log j)) := by ring
  · rw [hhalf]
    refine hCW.of_norm_bounded fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
  · rw [hhalf]
    exact hK

/-- **The half-damped hyperplane law on the `√log`-weighted algebra.** If
`Σ_j |k(j)| j^{-1/2} √(1 + log j) < ∞`, the receiver of `k ⋆ d^{-1/2}` is bounded iff
`K(1/2) = Σ_j k(j) j^{-1/2} = 0`. -/
theorem receiverBounded_dirichletConv_unit_half_iff {k : ℕ → ℝ}
    (hk : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log j))) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) ↔
      ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := by
  refine ⟨fun hB => ?_, receiverBounded_dirichletConv_unit_half_of_sqrt_log hk⟩
  by_contra hK
  have hK' : ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - 1 / 2 : ℝ)) ≠ 0 := by
    rw [show -(1 - 1 / 2 : ℝ) = -(1 / 2) by norm_num]; exact hK
  exact not_receiverBounded_dirichletConv_of_drift_critical (by norm_num) le_rfl
    (q := dampedSignWeight unitSign (1 / 2))
    (fun d => by simp [dampedSignWeight, unitSign, Real.rpow_nonneg])
    (dampedClass_unit (1 / 2)) (κ := (2 : ℝ) ^ (-(1 + 1 / 2 : ℝ))) (by positivity)
    (by filter_upwards [eventually_ge_atTop 1] with n hn using unit_drift (by norm_num) hn)
    (criticalWiener_of_sqrt_log hk) hK' hB

/-! ### The lacunary kernel -/

/-- The lacunary nodes `J_r = 2^{4^{r+1}}`. -/
def lacunaryNode (r : ℕ) : ℕ := 2 ^ 4 ^ (r + 1)

/-- The lacunary amplitudes `a_r = 2^{-(r+1)} J_r^{1/2}`. -/
def lacunaryAmp (r : ℕ) : ℝ := (1 / 2 : ℝ) ^ (r + 1) * (lacunaryNode r : ℝ) ^ (1 / 2 : ℝ)

/-- The lacunary kernel `k = Σ_r a_r δ_{J_r} − δ_1`. -/
def lacunaryKernel (j : ℕ) : ℝ :=
  Function.extend lacunaryNode lacunaryAmp 0 j - if j = 1 then 1 else 0

theorem lacunaryNode_injective : Function.Injective lacunaryNode := by
  intro r s h
  unfold lacunaryNode at h
  have h1 : 4 ^ (r + 1) = 4 ^ (s + 1) := Nat.pow_right_injective le_rfl h
  have h2 : r + 1 = s + 1 := Nat.pow_right_injective (by norm_num) h1
  omega

theorem one_lt_lacunaryNode (r : ℕ) : (1 : ℝ) < lacunaryNode r := by
  have h : 1 < lacunaryNode r := Nat.one_lt_two_pow (by positivity)
  exact_mod_cast h

/-- `a_r J_r^{-σ} = 2^{-(r+1)} J_r^{-(σ − 1/2)}`. -/
theorem lacunaryAmp_mul_rpow (r : ℕ) (σ : ℝ) :
    lacunaryAmp r * (lacunaryNode r : ℝ) ^ (-σ) =
      (1 / 2 : ℝ) ^ (r + 1) * (lacunaryNode r : ℝ) ^ (-(σ - 1 / 2)) := by
  have hJ : (0 : ℝ) < lacunaryNode r := by linarith [one_lt_lacunaryNode r]
  rw [lacunaryAmp, mul_assoc, ← Real.rpow_add hJ, show (1 / 2 : ℝ) + -σ = -(σ - 1 / 2) by ring]

/-- Extension by zero commutes with multiplication by a weight. -/
theorem extend_mul_eq {J : ℕ → ℕ} (hJ : Function.Injective J) (a g : ℕ → ℝ) :
    (fun j => Function.extend J a 0 j * g j) = Function.extend J (fun r => a r * g (J r)) 0 := by
  funext j
  by_cases h : ∃ r, J r = j
  · obtain ⟨r, rfl⟩ := h
    rw [hJ.extend_apply, hJ.extend_apply]
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Pi.zero_apply, zero_mul]

/-- `|extend a| · g = extend (|a| · g ∘ J)`. -/
theorem abs_extend_mul_eq {J : ℕ → ℕ} (hJ : Function.Injective J) (a g : ℕ → ℝ) (j : ℕ) :
    |Function.extend J a 0 j| * g j = Function.extend J (fun r => |a r| * g (J r)) 0 j := by
  by_cases h : ∃ r, J r = j
  · obtain ⟨r, rfl⟩ := h
    rw [hJ.extend_apply, hJ.extend_apply]
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Pi.zero_apply, abs_zero,
      zero_mul]

/-- `Σ_r 2^{-(r+1)} = 1`. -/
theorem hasSum_half_pow_succ : HasSum (fun r : ℕ => (1 / 2 : ℝ) ^ (r + 1)) 1 := by
  have h := hasSum_geometric_two.mul_left (1 / 2 : ℝ)
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num] at h
  have e : (fun r : ℕ => (1 / 2 : ℝ) ^ (r + 1)) = fun r => 1 / 2 * (1 / 2) ^ r := by
    funext r; ring
  rw [e]
  exact h

/-- **The Dirichlet series of the lacunary kernel**: for `σ ≥ 1/2`,
`K(σ) = Σ_r 2^{-(r+1)} J_r^{-(σ − 1/2)} − 1`. -/
theorem hasSum_lacunaryKernel_mul_rpow {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    HasSum (fun j : ℕ => lacunaryKernel j * (j : ℝ) ^ (-σ))
      ((∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (lacunaryNode r : ℝ) ^ (-(σ - 1 / 2))) - 1) := by
  have hsum : Summable (fun r : ℕ =>
      (1 / 2 : ℝ) ^ (r + 1) * (lacunaryNode r : ℝ) ^ (-(σ - 1 / 2))) :=
    hasSum_half_pow_succ.summable.of_nonneg_of_le (fun r => by positivity) fun r =>
      mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos (one_lt_lacunaryNode r).le (by linarith))
  have h1 : HasSum (fun j : ℕ => Function.extend lacunaryNode lacunaryAmp 0 j * (j : ℝ) ^ (-σ))
      (∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (lacunaryNode r : ℝ) ^ (-(σ - 1 / 2))) := by
    rw [extend_mul_eq lacunaryNode_injective lacunaryAmp (fun j : ℕ => (j : ℝ) ^ (-σ)),
      hasSum_extend_zero lacunaryNode_injective]
    simp_rw [lacunaryAmp_mul_rpow]
    exact hsum.hasSum
  have h2 : HasSum (fun j : ℕ => (if j = 1 then (1 : ℝ) else 0) * (j : ℝ) ^ (-σ)) 1 := by
    have e : (fun j : ℕ => (if j = 1 then (1 : ℝ) else 0) * (j : ℝ) ^ (-σ)) =
        fun j => if j = 1 then (1 : ℝ) else 0 := by
      funext j
      split_ifs with h
      · subst h; simp
      · simp
    rw [e]
    exact hasSum_ite_eq 1 (1 : ℝ)
  have e : (fun j : ℕ => lacunaryKernel j * (j : ℝ) ^ (-σ)) = fun j =>
      Function.extend lacunaryNode lacunaryAmp 0 j * (j : ℝ) ^ (-σ) -
        (if j = 1 then (1 : ℝ) else 0) * (j : ℝ) ^ (-σ) := by
    funext j
    simp only [lacunaryKernel, sub_mul]
  rw [e]
  exact h1.sub h2

/-- **The pole value vanishes**: `K(1/2) = 0`. -/
theorem tsum_lacunaryKernel_half : ∑' j : ℕ, lacunaryKernel j * (j : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := by
  rw [(hasSum_lacunaryKernel_mul_rpow le_rfl).tsum_eq]
  simp only [sub_self, neg_zero, Real.rpow_zero, mul_one]
  rw [hasSum_half_pow_succ.tsum_eq, sub_self]

/-- **The kernel stays below the pole**: at `σ = 1/2 + u`,
`K(σ) ≤ −2^{-(R+1)} (1 − J_R^{-u})` for every `R`. -/
theorem tsum_lacunaryKernel_le {u : ℝ} (hu : 0 ≤ u) (R : ℕ) :
    ∑' j : ℕ, lacunaryKernel j * (j : ℝ) ^ (-(1 / 2 + u)) ≤
      -((1 / 2 : ℝ) ^ (R + 1) * (1 - (lacunaryNode R : ℝ) ^ (-u))) := by
  rw [(hasSum_lacunaryKernel_mul_rpow (by linarith)).tsum_eq, show 1 / 2 + u - 1 / 2 = u by ring]
  have hle : ∀ r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (lacunaryNode r : ℝ) ^ (-u) ≤ (1 / 2 : ℝ) ^ (r + 1) :=
    fun r => mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (one_lt_lacunaryNode r).le (by linarith))
  have hS := (hasSum_half_pow_succ.summable.of_nonneg_of_le (fun r => by positivity) hle).hasSum
  have hgap := hasSum_half_pow_succ.sub hS
  have h := le_hasSum hgap R fun r _ => by linarith [hle r]
  linarith

/-- At the probe `u_R = (2^{-(R+1)})²`, `J_R^{-u_R} = 1/2`. -/
theorem lacunaryNode_rpow_probe (R : ℕ) :
    (lacunaryNode R : ℝ) ^ (-(((1 / 2 : ℝ) ^ (R + 1)) ^ 2)) = 1 / 2 := by
  have hcast : (lacunaryNode R : ℝ) = (2 : ℝ) ^ ((4 ^ (R + 1) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; simp [lacunaryNode]
  have h1 : (4 : ℝ) ^ (R + 1) * ((1 / 2 : ℝ) ^ (R + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (R + 1) 2, pow_mul, ← mul_pow]; norm_num
  have h2 : ((4 ^ (R + 1) : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (R + 1)) ^ 2 = 1 := by push_cast; exact h1
  rw [hcast, ← Real.rpow_mul (by norm_num), mul_neg, h2, Real.rpow_neg_one]
  norm_num

/-- `Σ_d d^{-1/2} d^{-(1/2 + u)} ≥ 1/u` for `u > 0`. -/
theorem one_div_le_tsum_unit_half {u : ℝ} (hu : 0 < u) :
    1 / u ≤ ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d * (d : ℝ) ^ (-(1 / 2 + u)) := by
  have hs := summable_mul_rpow_of_dampedClass (by norm_num) (dampedClass_unit (1 / 2))
    (show 1 - 1 / 2 < 1 / 2 + u by linarith)
  have h := HTGeometry.tsum_shift_rpow_ge (q := -u) (by linarith) 0
  simp only [Nat.cast_zero, zero_add, Real.one_rpow, neg_neg] at h
  rw [hs.tsum_eq_zero_add]
  have h0 : dampedSignWeight unitSign (1 / 2) 0 * ((0 : ℕ) : ℝ) ^ (-(1 / 2 + u)) = 0 := by
    simp [dampedSignWeight]
  rw [h0, zero_add]
  refine h.trans (le_of_eq (tsum_congr fun d => ?_))
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  simp only [dampedSignWeight, unitSign, one_mul]
  push_cast
  rw [← Real.rpow_add hd, add_comm (1 : ℝ) (d : ℝ)]
  congr 1
  ring

/-- **The lacunary kernel lies in every log-weighted Wiener algebra below `√log`**:
`Σ_j |k(j)| j^{-1/2} (1 + log j)^α < ∞` for `0 ≤ α < 1/2`. On the node `J_r` the weight is
`2^{-(r+1)} (1 + 4^{r+1} log 2)^α ≤ 2^α (4^α/2)^{r+1}`. -/
theorem summable_lacunaryKernel_log {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1 / 2) :
    Summable (fun j : ℕ => |lacunaryKernel j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) *
      (1 + Real.log j) ^ α) := by
  have h4 : (4 : ℝ) ^ α < 2 := by
    calc (4 : ℝ) ^ α < (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hα
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
  have hρ0 : 0 ≤ (4 : ℝ) ^ α / 2 := by positivity
  have hρ1 : (4 : ℝ) ^ α / 2 < 1 := by rw [div_lt_one (by norm_num)]; exact h4
  -- the weight `w(j) = j^{-1/2} (1 + log j)^α`
  have hw0 : ∀ j : ℕ, 0 ≤ (j : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log j) ^ α := fun j =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)
      (Real.rpow_nonneg (by linarith [one_le_one_add_log_natCast j]) _)
  have hnode : ∀ r : ℕ, |lacunaryAmp r| * ((lacunaryNode r : ℝ) ^ (-(1 / 2 : ℝ)) *
      (1 + Real.log (lacunaryNode r)) ^ α) ≤ (2 : ℝ) ^ α * ((4 : ℝ) ^ α / 2) ^ (r + 1) := by
    intro r
    have hamp : |lacunaryAmp r| * (lacunaryNode r : ℝ) ^ (-(1 / 2 : ℝ)) =
        (1 / 2 : ℝ) ^ (r + 1) := by
      rw [abs_of_nonneg (by unfold lacunaryAmp; positivity), lacunaryAmp_mul_rpow, sub_self,
        neg_zero, Real.rpow_zero, mul_one]
    have hlog : 1 + Real.log (lacunaryNode r) ≤ 2 * (4 : ℝ) ^ (r + 1) := by
      have hcast : (lacunaryNode r : ℝ) = (2 : ℝ) ^ (4 ^ (r + 1)) := by simp [lacunaryNode]
      rw [hcast, Real.log_pow]
      push_cast
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
        linarith
      have h1 : (1 : ℝ) ≤ 4 ^ (r + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hlog0 : 0 ≤ 1 + Real.log (lacunaryNode r) := by
      linarith [one_le_one_add_log_natCast (lacunaryNode r)]
    calc |lacunaryAmp r| * ((lacunaryNode r : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 + Real.log (lacunaryNode r)) ^ α)
        = (1 / 2 : ℝ) ^ (r + 1) * (1 + Real.log (lacunaryNode r)) ^ α := by
          rw [← mul_assoc, hamp]
      _ ≤ (1 / 2 : ℝ) ^ (r + 1) * (2 * (4 : ℝ) ^ (r + 1)) ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog0 hlog hα0) (by positivity)
      _ = (2 : ℝ) ^ α * ((4 : ℝ) ^ α / 2) ^ (r + 1) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (4 : ℝ) (r + 1),
            ← Real.rpow_mul (by norm_num), mul_comm ((r + 1 : ℕ) : ℝ) α,
            Real.rpow_mul (by norm_num), Real.rpow_natCast, div_pow, div_pow, one_pow]
          ring
  have hgeom : Summable (fun r : ℕ => (2 : ℝ) ^ α * ((4 : ℝ) ^ α / 2) ^ (r + 1)) :=
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ((2 : ℝ) ^ α * ((4 : ℝ) ^ α / 2))).congr
      fun r => by ring
  have hext : Summable (Function.extend lacunaryNode (fun r => |lacunaryAmp r| *
      ((lacunaryNode r : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log (lacunaryNode r)) ^ α)) 0) :=
    (summable_extend_zero lacunaryNode_injective).2 (hgeom.of_nonneg_of_le
      (fun r => mul_nonneg (abs_nonneg _) (hw0 _)) hnode)
  have hone : Summable (fun j : ℕ => if j = 1 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 1 (1 : ℝ)).summable
  refine (hext.add hone).of_nonneg_of_le (fun j => by
      rw [mul_assoc]; exact mul_nonneg (abs_nonneg _) (hw0 j)) fun j => ?_
  rw [mul_assoc]
  calc |lacunaryKernel j| * ((j : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log j) ^ α)
      ≤ (|Function.extend lacunaryNode lacunaryAmp 0 j| + |if j = 1 then (1 : ℝ) else 0|) *
          ((j : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log j) ^ α) :=
        mul_le_mul_of_nonneg_right (abs_sub _ _) (hw0 j)
    _ = Function.extend lacunaryNode (fun r => |lacunaryAmp r| *
          ((lacunaryNode r : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log (lacunaryNode r)) ^ α)) 0 j +
        |if j = 1 then (1 : ℝ) else 0| * ((j : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log j) ^ α) := by
        rw [add_mul, abs_extend_mul_eq lacunaryNode_injective lacunaryAmp
          (fun j : ℕ => (j : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log j) ^ α)]
    _ ≤ Function.extend lacunaryNode (fun r => |lacunaryAmp r| *
          ((lacunaryNode r : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log (lacunaryNode r)) ^ α)) 0 j +
        if j = 1 then (1 : ℝ) else 0 := by
        refine add_le_add le_rfl ?_
        split_ifs with h
        · subst h; simp
        · simp

/-- The lacunary kernel lies in the critical Wiener algebra. -/
theorem criticalWiener_lacunaryKernel : CriticalWiener lacunaryKernel :=
  (summable_lacunaryKernel_log (α := 0) le_rfl (by norm_num)).congr fun j => by
    rw [Real.rpow_zero, mul_one]

/-- **At a probe the Dirichlet series is large.** At `u = t²`, `t = 2^{-(R+1)}`, the Dirichlet
series of `k ⋆ d^{-1/2}` is `K(1/2 + u) Q(1/2 + u)` with `−K ≥ t/2` and `Q ≥ 1/t²`, so
`t · |C(1/2 + u)| ≥ 1/2`. -/
theorem half_le_mul_abs_dirichletSeries_lacunaryKernel (R : ℕ) :
    1 / 2 ≤ (1 / 2 : ℝ) ^ (R + 1) * |∑' d : ℕ, RHTower.dirichletConv lacunaryKernel
      (dampedSignWeight unitSign (1 / 2)) d * (d : ℝ) ^ (-(1 / 2 + ((1 / 2 : ℝ) ^ (R + 1)) ^ 2))| := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (1 / 2 : ℝ) ^ (R + 1) := ⟨_, rfl⟩
  have hK := tsum_lacunaryKernel_le (sq_nonneg ((1 / 2 : ℝ) ^ (R + 1))) R
  have hprobe := lacunaryNode_rpow_probe R
  rw [← ht] at hK hprobe ⊢
  rw [hprobe] at hK
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht0' : t ≠ 0 := ht0.ne'
  have hu : 0 < t ^ 2 := by positivity
  have hprod := hasSum_dirichletConv_mul_rpow (k := lacunaryKernel)
    (q := dampedSignWeight unitSign (1 / 2)) (σ := 1 / 2 + t ^ 2) (by positivity)
    (criticalWiener_lacunaryKernel.summable_abs_mul_rpow (by linarith))
    (summable_abs_mul_rpow_of_dampedClass (by norm_num) (dampedClass_unit (1 / 2)) (by linarith))
  rw [hprod.tsum_eq]
  have hQ := one_div_le_tsum_unit_half hu
  have hK' : t / 2 ≤ -∑' j : ℕ, lacunaryKernel j * (j : ℝ) ^ (-(1 / 2 + t ^ 2)) := by linarith
  have h1 : t / 2 * (1 / t ^ 2) ≤ (-∑' j : ℕ, lacunaryKernel j * (j : ℝ) ^ (-(1 / 2 + t ^ 2))) *
      ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d * (d : ℝ) ^ (-(1 / 2 + t ^ 2)) :=
    mul_le_mul hK' hQ (by positivity) (by linarith)
  have h2 : t * (t / 2 * (1 / t ^ 2)) = 1 / 2 := by field_simp
  have h3 := neg_le_abs ((∑' j : ℕ, lacunaryKernel j * (j : ℝ) ^ (-(1 / 2 + t ^ 2))) *
      ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d * (d : ℝ) ^ (-(1 / 2 + t ^ 2)))
  rw [← neg_mul] at h3
  calc (1 : ℝ) / 2 = t * (t / 2 * (1 / t ^ 2)) := h2.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h3) ht0.le

/-- **The lacunary kernel is not paid at half damping.** If it were, the little-o pole law would
give `√u_R |C(1/2 + u_R) − m| → 0` along the probes `u_R = 4^{-(R+1)} → 0`, while
`√u_R |C(1/2 + u_R)| ≥ 1/2`. -/
theorem not_receiverBounded_dirichletConv_lacunaryKernel :
    ¬ ReceiverBounded (RHTower.dirichletConv lacunaryKernel (dampedSignWeight unitSign (1 / 2))) := by
  intro hB
  have hc : ∀ θ : ℝ, 1 / 2 < θ → Summable (fun d : ℕ => |RHTower.dirichletConv lacunaryKernel
      (dampedSignWeight unitSign (1 / 2)) d| * (d : ℝ) ^ (-θ)) := by
    intro θ hθ
    have hk' := criticalWiener_lacunaryKernel.summable_abs_mul_rpow hθ.le
    have hq' := summable_abs_mul_rpow_of_dampedClass (by norm_num) (dampedClass_unit (1 / 2))
      (show 1 - 1 / 2 < θ by linarith)
    have h := hasSum_dirichletConv_mul_rpow (k := fun j => |lacunaryKernel j|)
      (q := fun d => |dampedSignWeight unitSign (1 / 2) d|) (σ := θ) (by linarith)
      (by simpa only [abs_abs] using hk') (by simpa only [abs_abs] using hq')
    refine h.summable.of_nonneg_of_le (fun d => by positivity) fun d => ?_
    exact mul_le_mul_of_nonneg_right (abs_dirichletConv_le _ _ d)
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hlim := tendsto_sqrt_mul_abs_dirichletSeries_sub_mean hc hB
  have hpow : Tendsto (fun R : ℕ => (1 / 2 : ℝ) ^ (R + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hu : Tendsto (fun R : ℕ => ((1 / 2 : ℝ) ^ (R + 1)) ^ 2) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun R => ?_⟩
    · have h := hpow.pow 2
      rwa [zero_pow two_ne_zero] at h
    · exact Set.mem_Ioi.mpr (by positivity)
  have hm := hpow.mul_const |∑' d : ℕ,
      RHTower.dirichletConv lacunaryKernel (dampedSignWeight unitSign (1 / 2)) d / d|
  rw [zero_mul] at hm
  have hsum := (hlim.comp hu).add hm
  rw [zero_add] at hsum
  have hge : ∀ R : ℕ, (1 : ℝ) / 2 ≤ Real.sqrt (((1 / 2 : ℝ) ^ (R + 1)) ^ 2) *
      |(∑' d : ℕ, RHTower.dirichletConv lacunaryKernel (dampedSignWeight unitSign (1 / 2)) d *
        (d : ℝ) ^ (-(1 / 2 + ((1 / 2 : ℝ) ^ (R + 1)) ^ 2))) - ∑' d : ℕ,
          RHTower.dirichletConv lacunaryKernel (dampedSignWeight unitSign (1 / 2)) d / d| +
      (1 / 2 : ℝ) ^ (R + 1) * |∑' d : ℕ,
        RHTower.dirichletConv lacunaryKernel (dampedSignWeight unitSign (1 / 2)) d / d| := by
    intro R
    rw [Real.sqrt_sq (by positivity)]
    have h := half_le_mul_abs_dirichletSeries_lacunaryKernel R
    have htri := abs_sub_abs_le_abs_sub (∑' d : ℕ, RHTower.dirichletConv lacunaryKernel
      (dampedSignWeight unitSign (1 / 2)) d * (d : ℝ) ^ (-(1 / 2 + ((1 / 2 : ℝ) ^ (R + 1)) ^ 2)))
      (∑' d : ℕ, RHTower.dirichletConv lacunaryKernel (dampedSignWeight unitSign (1 / 2)) d / d)
    have ht0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (R + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htri ht0]
  have h := ge_of_tendsto' hsum hge
  norm_num at h

/-! ### The thresholds -/

/-- **The hyperplane law on the critical Wiener algebra holds exactly below half damping.** For
`0 < ε ≤ 1/2`, "every `k` with `Σ_j |k(j)| j^{-1/2} < ∞` has `k ⋆ d^{-ε}` paid iff
`K(1 − ε) = 0`" holds iff `ε < 1/2`. -/
theorem criticalWiener_hyperplaneLaw_iff_lt_half {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ k : ℕ → ℝ, CriticalWiener k →
      (ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ↔
        ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) = 0)) ↔ ε < 1 / 2 := by
  refine ⟨fun h => ?_, fun hlt k hk => receiverBounded_dirichletConv_unit_iff_critical hε hlt hk⟩
  by_contra hlt
  obtain rfl : ε = 1 / 2 := le_antisymm hε2 (not_lt.mp hlt)
  refine not_receiverBounded_dirichletConv_lacunaryKernel
    ((h lacunaryKernel criticalWiener_lacunaryKernel).2 ?_)
  rw [show -(1 - 1 / 2 : ℝ) = -(1 / 2) by norm_num]
  exact tsum_lacunaryKernel_half

/-- **The exact logarithmic threshold at half damping.** On the `√log`-weighted algebra
`Σ_j |k(j)| j^{-1/2} √(1 + log j) < ∞` the receiver of `k ⋆ d^{-1/2}` is paid iff `K(1/2) = 0`;
no smaller power of the logarithm suffices: the lacunary kernel lies in every
`Σ_j |k(j)| j^{-1/2} (1 + log j)^α < ∞`, `0 ≤ α < 1/2`, has `K(1/2) = 0`, and is not paid. -/
theorem halfDamped_hyperplaneLaw_logarithmic_threshold :
    (∀ k : ℕ → ℝ,
      Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log j)) →
        (ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) ↔
          ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 / 2 : ℝ)) = 0)) ∧
    ∃ k : ℕ → ℝ, (∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
        Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log j) ^ α)) ∧
      ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 / 2 : ℝ)) = 0 ∧
      ¬ ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) :=
  ⟨fun _ hk => receiverBounded_dirichletConv_unit_half_iff hk,
    lacunaryKernel, fun _ hα0 hα => summable_lacunaryKernel_log hα0 hα, tsum_lacunaryKernel_half,
    not_receiverBounded_dirichletConv_lacunaryKernel⟩

/-- The lacunary kernel is not in the `√log`-weighted algebra. -/
theorem not_summable_lacunaryKernel_sqrt_log :
    ¬ Summable (fun j : ℕ => |lacunaryKernel j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.sqrt (1 + Real.log j)) := fun h =>
  not_receiverBounded_dirichletConv_lacunaryKernel
    ((receiverBounded_dirichletConv_unit_half_iff h).2 tsum_lacunaryKernel_half)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
