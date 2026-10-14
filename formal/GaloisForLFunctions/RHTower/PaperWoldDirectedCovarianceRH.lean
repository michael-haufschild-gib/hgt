import GaloisForLFunctions.RHTower.PaperWoldDirectedCovarianceEnergy
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergySubhalf

/-!
# Route TT's signed directed covariance is exactly RH

For `0 < t < 1/2` let `D_t(N) = Σ_{n<N} (n+1)^(2t) d_n Σ_{n<j<N} d_j` be the directed covariance
of the literal natural Wold increments `d_n = R(n+2) - R(n+1)`, and `Q_t(N)` its weighted diagonal.

**Theorem** (`riemannHypothesis_iff_forall_directedCovariance_bdd`).  RH holds iff for every
`0 < t < 1/2` the sums `D_t(N) + Q_t(N)/2` are bounded above in `N`.

`D_t + Q_t/2` is half the endpoint energy `w₀(R_N - R_1)² + Σ (w_{n+1}-w_n)(R_N - R_{n+2})²`.
Concavity of `x ↦ x^(2t)` traps the weight increments between `2t(n+2)^(2t-1)` and
`2t(n+1)^(2t-1)`, so the endpoint energy is comparable to the natural square energy plus the
boundary term `(N+1)^(2t) R(N+1)²`, which RH keeps bounded.  The square energy below one half is
exactly RH (`riemannHypothesis_iff_forall_woldNatResidualSquareEnergy_lt_half`).
-/

namespace RHTower
noncomputable section
open Filter Topology Finset
open scoped BigOperators

local notation "R" => xiHeatCassiniWoldNatResidualLogDiscrepancy

/-- Tangent-line bound for a concave power. -/
private theorem rpow_le_tangent {x y p : ℝ} (hx : 0 < x) (hy : 0 < y) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : y ^ p ≤ x ^ p + p * (x ^ p / x) * (y - x) := by
  have hs : -1 ≤ y / x - 1 := by have : 0 < y / x := div_pos hy hx; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  rw [add_sub_cancel, Real.div_rpow hy.le hx.le] at hb
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  rw [div_le_iff₀ hxp] at hb
  calc y ^ p ≤ (1 + p * (y / x - 1)) * x ^ p := hb
    _ = x ^ p + p * (x ^ p / x) * (y - x) := by field_simp

private theorem natCast_add_one_rpow_div {n : ℕ} {p : ℝ} :
    ((n : ℝ) + 1) ^ p / ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (p - 1) :=
  (Real.rpow_sub_one (by positivity) p).symm

theorem woldPowerWeight_succ_sub_ge {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) (n : ℕ) :
    2 * t * ((n : ℝ) + 2) ^ (2 * t - 1) ≤ woldPowerWeight t (n + 1) - woldPowerWeight t n := by
  unfold woldPowerWeight
  have h := rpow_le_tangent (x := (n : ℝ) + 2) (y := (n : ℝ) + 1) (p := 2 * t) (by positivity)
    (by positivity) (by linarith) (by linarith)
  have hdiv : ((n : ℝ) + 2) ^ (2 * t) / ((n : ℝ) + 2) = ((n : ℝ) + 2) ^ (2 * t - 1) :=
    (Real.rpow_sub_one (by positivity) _).symm
  rw [hdiv] at h
  push_cast
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  linarith

theorem woldPowerWeight_succ_sub_le {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) (n : ℕ) :
    woldPowerWeight t (n + 1) - woldPowerWeight t n ≤ 2 * t * ((n : ℝ) + 1) ^ (2 * t - 1) := by
  unfold woldPowerWeight
  have h := rpow_le_tangent (x := (n : ℝ) + 1) (y := (n : ℝ) + 2) (p := 2 * t) (by positivity)
    (by positivity) (by linarith) (by linarith)
  rw [natCast_add_one_rpow_div] at h
  push_cast
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  linarith

/-- Neighbouring powers with a nonpositive exponent above `-1` differ by at most a factor `2`. -/
private theorem rpow_succ_le_two_mul {e : ℝ} (he0 : e ≤ 0) (he1 : -1 ≤ e) (n : ℕ) :
    ((n : ℝ) + 1) ^ e ≤ 2 * ((n : ℝ) + 2) ^ e := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbase : (2 * ((n : ℝ) + 1)) ^ e ≤ ((n : ℝ) + 2) ^ e :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he0
  rw [Real.mul_rpow (by norm_num) h1.le] at hbase
  have h2e : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ e :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
  rw [Real.rpow_neg_one] at h2e
  have hpos : 0 ≤ ((n : ℝ) + 1) ^ e := Real.rpow_nonneg h1.le e
  nlinarith [mul_le_mul_of_nonneg_right h2e hpos]

theorem woldNatResidualSquareEnergy_iff_shift_two {t : ℝ} :
    WoldNatResidualSquareEnergy t ↔
      Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (2 * t - 1) * R (n + 2) ^ 2) := by
  unfold WoldNatResidualSquareEnergy
  rw [← summable_nat_add_iff 2]
  simp only [Nat.cast_add, Nat.cast_ofNat, sq_abs]

/-- **Square energy plus a matching decay rate bounds the signed covariance.**  For
`0 < t < 1/2`, finite square energy at radius `t` and a residual rate `|R N| ≤ B N^(-c)` with
`c ≥ t` bound `D_t(N) + Q_t(N)/2` uniformly in `N`. -/
theorem exists_directedCovariance_bdd_of_squareEnergy {t c : ℝ} (ht0 : 0 < t) (ht : t < 1 / 2)
    (htc : t ≤ c) (hE : WoldNatResidualSquareEnergy t)
    (hrate : ∃ B : ℝ, ∀ᶠ N : ℕ in atTop, |R N| ≤ B * (N : ℝ) ^ (-c)) :
    ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N +
        incrementDiagonal (woldPowerWeight t) woldShiftedResidual N / 2 ≤ C := by
  have hsum := woldNatResidualSquareEnergy_iff_shift_two.mp hE
  -- the logarithmic energy is summable
  have hlog : Summable (fun n : ℕ => (woldPowerWeight t (n + 1) - woldPowerWeight t n) *
      woldShiftedResidual (n + 1) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg
        (sub_nonneg.mpr (monotone_woldPowerWeight ht0.le (Nat.le_succ n))) (sq_nonneg _))
      (fun n => ?_) ((hsum.mul_left (2 * t * 2)))
    have hd := woldPowerWeight_succ_sub_le ht0 ht.le n
    have hr := rpow_succ_le_two_mul (e := 2 * t - 1) (n := n) (by linarith) (by linarith)
    have hsq : 0 ≤ woldShiftedResidual (n + 1) ^ 2 := sq_nonneg _
    simp only [woldShiftedResidual] at hsq ⊢
    calc (woldPowerWeight t (n + 1) - woldPowerWeight t n) * R (n + 1 + 1) ^ 2
        ≤ 2 * t * ((n : ℝ) + 1) ^ (2 * t - 1) * R (n + 1 + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hd hsq
      _ ≤ 2 * t * (2 * ((n : ℝ) + 2) ^ (2 * t - 1)) * R (n + 1 + 1) ^ 2 := by
          gcongr
      _ = 2 * t * 2 * (((n : ℝ) + 2) ^ (2 * t - 1) * R (n + 2) ^ 2) := by ring
  -- the boundary term is bounded by the decay rate
  obtain ⟨B, hrate⟩ := hrate
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hrate
  let u : ℕ → ℝ := fun N => woldPowerWeight t N * woldShiftedResidual N ^ 2
  have hu0 : ∀ N, 0 ≤ u N := fun N => by
    dsimp only [u, woldPowerWeight]; positivity
  have hubound : ∀ N, u N ≤ (∑ k ∈ range N₀, u k) + B ^ 2 := by
    intro N
    rcases lt_or_ge N N₀ with hN | hN
    · have := single_le_sum (fun k _ => hu0 k) (mem_range.mpr hN)
      linarith [sq_nonneg B]
    · have hR := hN₀ (N + 1) (by omega)
      have hx1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
      have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by linarith
      have hsq : R (N + 1) ^ 2 ≤ (B * ((N + 1 : ℕ) : ℝ) ^ (-c)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hR 2
      have hw : woldPowerWeight t N = ((N + 1 : ℕ) : ℝ) ^ (2 * t) := by
        simp [woldPowerWeight]
      have hprod : ((N + 1 : ℕ) : ℝ) ^ (2 * t) * (B * ((N + 1 : ℕ) : ℝ) ^ (-c)) ^ 2 =
          B ^ 2 * ((N + 1 : ℕ) : ℝ) ^ (2 * t - 2 * c) := by
        rw [mul_pow, ← Real.rpow_natCast (((N + 1 : ℕ) : ℝ) ^ _), ← Real.rpow_mul hx.le,
          mul_left_comm, ← Real.rpow_add hx]
        rw [show 2 * t + -c * ((2 : ℕ) : ℝ) = 2 * t - 2 * c by push_cast; ring]
      have hle1 : ((N + 1 : ℕ) : ℝ) ^ (2 * t - 2 * c) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
      have hmain : u N ≤ B ^ 2 := by
        dsimp only [u, woldShiftedResidual]
        rw [hw]
        calc ((N + 1 : ℕ) : ℝ) ^ (2 * t) * R (N + 1) ^ 2
            ≤ ((N + 1 : ℕ) : ℝ) ^ (2 * t) * (B * ((N + 1 : ℕ) : ℝ) ^ (-c)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = B ^ 2 * ((N + 1 : ℕ) : ℝ) ^ (2 * t - 2 * c) := hprod
          _ ≤ B ^ 2 * 1 := mul_le_mul_of_nonneg_left hle1 (sq_nonneg B)
          _ = B ^ 2 := mul_one _
      linarith [sum_nonneg fun k (_ : k ∈ range N₀) => hu0 k]
  refine ⟨woldPowerWeight t 0 * woldShiftedResidual 0 ^ 2 +
    ((∑ k ∈ range N₀, u k) + B ^ 2) + ∑' n, (woldPowerWeight t (n + 1) - woldPowerWeight t n) *
      woldShiftedResidual (n + 1) ^ 2, fun N => ?_⟩
  have hid := directedCovariance_add_half_diagonal (woldPowerWeight t) woldShiftedResidual N
  have hend := endpointEnergy_le (monotone_woldPowerWeight ht0.le)
    (by unfold woldPowerWeight; positivity) (r := woldShiftedResidual) N
  have hpart : ∑ n ∈ range N, (woldPowerWeight t (n + 1) - woldPowerWeight t n) *
      woldShiftedResidual (n + 1) ^ 2 ≤ ∑' n, (woldPowerWeight t (n + 1) - woldPowerWeight t n) *
        woldShiftedResidual (n + 1) ^ 2 :=
    hlog.sum_le_tsum _ fun n _ => mul_nonneg
      (sub_nonneg.mpr (monotone_woldPowerWeight ht0.le (Nat.le_succ n))) (sq_nonneg _)
  have huN := hubound N
  dsimp only [u] at huN
  rw [hid]
  linarith

/-- **A bounded signed covariance forces the square energy** at the same radius `0 < t ≤ 1/2`. -/
theorem woldNatResidualSquareEnergy_of_directedCovariance_bdd {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ 1 / 2) (hC : ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N +
        incrementDiagonal (woldPowerWeight t) woldShiftedResidual N / 2 ≤ C) :
    WoldNatResidualSquareEnergy t := by
  obtain ⟨C, hC⟩ := hC
  have hlog := summable_woldEnergy_of_directedCovariance_bdd ht0.le hC
  refine woldNatResidualSquareEnergy_iff_shift_two.mpr ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hlog.div_const (2 * t))
  have hd := woldPowerWeight_succ_sub_ge ht0 ht n
  have hsq : 0 ≤ R (n + 2) ^ 2 := sq_nonneg _
  rw [le_div_iff₀ (by linarith)]
  simp only [woldShiftedResidual]
  calc ((n : ℝ) + 2) ^ (2 * t - 1) * R (n + 2) ^ 2 * (2 * t)
      = 2 * t * ((n : ℝ) + 2) ^ (2 * t - 1) * R (n + 1 + 1) ^ 2 := by ring
    _ ≤ (woldPowerWeight t (n + 1) - woldPowerWeight t n) * R (n + 1 + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hd hsq

/-- **Route TT's signed covariance need is exactly RH.** -/
theorem riemannHypothesis_iff_forall_directedCovariance_bdd :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 → ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N +
        incrementDiagonal (woldPowerWeight t) woldShiftedResidual N / 2 ≤ C := by
  rw [riemannHypothesis_iff_forall_woldNatResidualSquareEnergy_lt_half]
  constructor
  · intro hE t ht0 ht
    obtain ⟨B, -, hrate⟩ :=
      (riemannHypothesis_iff_woldNatResidualAllStrictHalfPowerRate.mp
        (riemannHypothesis_of_forall_woldNatResidualSquareEnergy_lt_half hE)) (1 / 2 - t)
        (by linarith) (by linarith)
    refine exists_directedCovariance_bdd_of_squareEnergy (c := t) ht0 ht le_rfl (hE t ht0 ht)
      ⟨B, ?_⟩
    have hrate' : ∀ᶠ N : ℕ in atTop, |R N| ≤ B * (N : ℝ) ^ (-(1 / 2 - (1 / 2 - t))) := hrate
    simpa only [show -(1 / 2 - (1 / 2 - t)) = -t by ring] using hrate'
  · intro hC t ht0 ht
    exact woldNatResidualSquareEnergy_of_directedCovariance_bdd ht0 ht.le (hC t ht0 ht)

end
end RHTower
