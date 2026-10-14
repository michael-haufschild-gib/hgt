import GaloisForLFunctions.RHTower.PaperWoldIncrementSignBlind

/-!
# The directed Wold covariance is an endpoint variance energy

For any real sequence `r` with increments `d n = r (n+1) - r n` and any weights `w`, the directed
covariance `D N = Σ_{n<N} w n · d n · Σ_{n<j<N} d j` satisfies the exact identity

`D N + ½ Σ_{n<N} w n · (d n)² = ½ (w 0 · (r N - r 0)² + Σ_{n<N} (w (n+1) - w n) · (r N - r (n+1))²)`.

Termwise, `a b + ½ a² = ½ ((a+b)² - b²)` with `a = d n`, `b = r N - r (n+1)`; Abel summation then
moves the weights onto the squared distances to the endpoint.  For nondecreasing nonnegative
weights every term on the right is nonnegative: the signed directed covariance has no sign problem
and only measures size.

For the literal natural Wold residual and weights `w n = (n+1)^(2t)`, `t ≥ 0`, the residual tends to
zero, so boundedness of `D + ½ Q` forces summability of the energy
`Σ ((n+2)^(2t) - (n+1)^(2t)) R(n+2)²`.  The arithmetic content of the directed covariance is the
logarithmic Plancherel energy of the residual and nothing else.
-/

namespace RHTower
noncomputable section
open Filter Topology Finset
open scoped BigOperators

/-- Increments of a real sequence. -/
def seqIncrement (r : ℕ → ℝ) (n : ℕ) : ℝ := r (n + 1) - r n

/-- Directed covariance of the increments of `r` with row weights `w`, up to the cutoff `N`. -/
def directedCovariance (w r : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, w n * seqIncrement r n * ∑ j ∈ Ioo n N, seqIncrement r j

/-- Weighted diagonal of the increments. -/
def incrementDiagonal (w r : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, w n * seqIncrement r n ^ 2

/-- Endpoint variance energy. -/
def endpointEnergy (w r : ℕ → ℝ) (N : ℕ) : ℝ :=
  w 0 * (r N - r 0) ^ 2 + ∑ n ∈ range N, (w (n + 1) - w n) * (r N - r (n + 1)) ^ 2

theorem sum_Ioo_seqIncrement (r : ℕ → ℝ) {n N : ℕ} (h : n < N) :
    ∑ j ∈ Ioo n N, seqIncrement r j = r N - r (n + 1) := by
  rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ range (N - (n + 1)), seqIncrement r (n + 1 + k)
      = ∑ k ∈ range (N - (n + 1)), (r (n + 1 + (k + 1)) - r (n + 1 + k)) :=
        sum_congr rfl fun k _ => by simp only [seqIncrement, add_assoc]
    _ = r (n + 1 + (N - (n + 1))) - r (n + 1 + 0) :=
        Finset.sum_range_sub (fun k => r (n + 1 + k)) _
    _ = r N - r (n + 1) := by
        rw [add_zero, show n + 1 + (N - (n + 1)) = N by omega]

/-- Abel summation with a vanishing endpoint term. -/
private theorem abel_endpoint (w A : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, w n * (A n - A (n + 1)) =
      w 0 * A 0 + ∑ n ∈ range N, (w (n + 1) - w n) * A (n + 1) - w N * A N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- **Endpoint variance identity** for the directed covariance. -/
theorem directedCovariance_add_half_diagonal (w r : ℕ → ℝ) (N : ℕ) :
    directedCovariance w r N + incrementDiagonal w r N / 2 = endpointEnergy w r N / 2 := by
  have hterm : ∀ n ∈ range N,
      w n * seqIncrement r n * ∑ j ∈ Ioo n N, seqIncrement r j + w n * seqIncrement r n ^ 2 / 2 =
        w n * ((r N - r n) ^ 2 - (r N - r (n + 1)) ^ 2) / 2 := by
    intro n hn
    rw [sum_Ioo_seqIncrement r (mem_range.mp hn)]
    simp only [seqIncrement]
    ring
  have habel := abel_endpoint w (fun n => (r N - r n) ^ 2) N
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at habel
  unfold directedCovariance incrementDiagonal endpointEnergy
  rw [sum_div, ← sum_add_distrib, sum_congr rfl hterm, ← sum_div]
  rw [show (∑ n ∈ range N, w n * ((r N - r n) ^ 2 - (r N - r (n + 1)) ^ 2)) =
      ∑ n ∈ range N, w n * ((r N - r n) ^ 2 - (r N - r (n + 1)) ^ 2) from rfl, habel]

theorem endpointEnergy_nonneg {w r : ℕ → ℝ} (hw0 : 0 ≤ w 0) (hmono : Monotone w) (N : ℕ) :
    0 ≤ endpointEnergy w r N := by
  unfold endpointEnergy
  exact add_nonneg (mul_nonneg hw0 (sq_nonneg _))
    (sum_nonneg fun n _ => mul_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ n))) (sq_nonneg _))

/-- **Bounded endpoint energy forces the logarithmic energy.**  If `r` tends to zero, the weights
are nondecreasing, and the endpoint energies are bounded by `C`, then the energy
`Σ (w (n+1) - w n) r (n+1)²` is summable with sum at most `C`. -/
theorem summable_energy_of_endpointEnergy_bdd {w r : ℕ → ℝ} (hmono : Monotone w)
    (hr : Tendsto r atTop (𝓝 0)) {C : ℝ} (hC : ∀ N, endpointEnergy w r N ≤ C)
    (hw0 : 0 ≤ w 0) :
    Summable (fun n => (w (n + 1) - w n) * r (n + 1) ^ 2) := by
  have hnn : ∀ n, 0 ≤ (w (n + 1) - w n) * r (n + 1) ^ 2 :=
    fun n => mul_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ n))) (sq_nonneg _)
  refine summable_of_sum_range_le hnn (c := C) fun M => ?_
  have hlim : Tendsto (fun N => ∑ n ∈ range M, (w (n + 1) - w n) * (r N - r (n + 1)) ^ 2)
      atTop (𝓝 (∑ n ∈ range M, (w (n + 1) - w n) * (0 - r (n + 1)) ^ 2)) :=
    tendsto_finsetSum _ fun n _ => ((hr.sub_const _).pow 2).const_mul _
  simp only [zero_sub, neg_sq] at hlim
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨M, fun N hN => ?_⟩)
  have hsub : ∑ n ∈ range M, (w (n + 1) - w n) * (r N - r (n + 1)) ^ 2 ≤
      ∑ n ∈ range N, (w (n + 1) - w n) * (r N - r (n + 1)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
      fun n _ _ => mul_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ n))) (sq_nonneg _)
  have h0 : 0 ≤ w 0 * (r N - r 0) ^ 2 := mul_nonneg hw0 (sq_nonneg _)
  exact hsub.trans ((le_add_of_nonneg_left h0).trans (hC N))

/-- Endpoint energy is at most twice the boundary value plus twice the energy. -/
theorem endpointEnergy_le {w r : ℕ → ℝ} (hmono : Monotone w) (hw0 : 0 ≤ w 0) (N : ℕ) :
    endpointEnergy w r N ≤
      2 * w 0 * r 0 ^ 2 + 2 * w N * r N ^ 2 +
        2 * ∑ n ∈ range N, (w (n + 1) - w n) * r (n + 1) ^ 2 := by
  unfold endpointEnergy
  have htel : ∑ n ∈ range N, (w (n + 1) - w n) = w N - w 0 := sum_range_sub w N
  have hterm : ∀ n ∈ range N, (w (n + 1) - w n) * (r N - r (n + 1)) ^ 2 ≤
      (w (n + 1) - w n) * (2 * r N ^ 2) + 2 * ((w (n + 1) - w n) * r (n + 1) ^ 2) := by
    intro n _
    have hd : 0 ≤ w (n + 1) - w n := sub_nonneg.mpr (hmono (Nat.le_succ n))
    nlinarith [sq_nonneg (r N + r (n + 1)), mul_nonneg hd (sq_nonneg (r N + r (n + 1)))]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← sum_mul, htel, ← mul_sum] at hsum
  nlinarith [sq_nonneg (r N + r 0), mul_nonneg hw0 (sq_nonneg (r N + r 0)),
    mul_nonneg hw0 (sq_nonneg (r N - r 0))]

/-! ### The literal natural Wold residual -/

/-- The shifted natural Wold residual `r n = R (n+1)`; its increments are the literal increments. -/
def woldShiftedResidual (n : ℕ) : ℝ := xiHeatCassiniWoldNatResidualLogDiscrepancy (n + 1)

theorem seqIncrement_woldShiftedResidual (n : ℕ) :
    seqIncrement woldShiftedResidual n = xiHeatCassiniWoldNatIncrement n := rfl

/-- The power weights `(n+1)^(2t)`. -/
def woldPowerWeight (t : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (2 * t)

theorem monotone_woldPowerWeight {t : ℝ} (ht : 0 ≤ t) : Monotone (woldPowerWeight t) := by
  intro a b hab
  unfold woldPowerWeight
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    (by linarith)

theorem tendsto_woldShiftedResidual : Tendsto woldShiftedResidual atTop (𝓝 0) :=
  tendsto_xiHeatCassiniWoldNatResidualLogDiscrepancy_zero.comp (tendsto_add_atTop_nat 1)

/-- **The directed Wold covariance measures only the logarithmic energy.**  For `t ≥ 0`, if the
directed covariance plus half its diagonal is bounded at every cutoff, then the logarithmic energy
`Σ ((n+2)^(2t) - (n+1)^(2t)) R(n+2)²` of the literal residual is summable. -/
theorem summable_woldEnergy_of_directedCovariance_bdd {t : ℝ} (ht : 0 ≤ t) {C : ℝ}
    (hC : ∀ N, directedCovariance (woldPowerWeight t) woldShiftedResidual N +
      incrementDiagonal (woldPowerWeight t) woldShiftedResidual N / 2 ≤ C) :
    Summable (fun n => (woldPowerWeight t (n + 1) - woldPowerWeight t n) *
      woldShiftedResidual (n + 1) ^ 2) := by
  have hw0 : 0 ≤ woldPowerWeight t 0 := by unfold woldPowerWeight; positivity
  refine summable_energy_of_endpointEnergy_bdd (monotone_woldPowerWeight ht)
    tendsto_woldShiftedResidual (C := 2 * C) (fun N => ?_) hw0
  have h := directedCovariance_add_half_diagonal (woldPowerWeight t) woldShiftedResidual N
  linarith [hC N]

end
end RHTower
