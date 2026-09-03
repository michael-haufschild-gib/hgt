import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteTwoFifthsNoGo
import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance

/-!
# General pole-factor growth at every real interior witness

For every real `x>1`, both exterior binomial coefficient sequences in the rational Cayley
square-root approximant have successive-ratio limit `x`. The `(1/2)` partial sums tend to
`-∞`. The two parity subsequences of the alternating `(-1/2)` partial sums tend respectively to
`+∞` and `-∞`. Consequently the norm of their product is eventually at least one.

At every real `σ` with `1/2<σ<1`, the shifted Cayley coordinate is `-(2/σ-1)`, whose magnitude is
strictly greater than one. This removes point-specific arithmetic cutoffs from the interior
unboundedness argument and is the reusable pole-factor input for a parameterized Hermite
low-depth obstruction.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

def poleExteriorWeight (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) * (x / 4) ^ k

def poleNegHalfExteriorSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * poleExteriorWeight x k

def poleHalfExteriorTerm (x : ℝ) (k : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) k * (-x) ^ k

def poleHalfExteriorSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, poleHalfExteriorTerm x k

def poleHalfExteriorMagnitude (x : ℝ) (k : ℕ) : ℝ :=
  -poleHalfExteriorTerm x k

theorem poleExteriorWeight_pos {x : ℝ} (hx : 0 < x) (k : ℕ) :
    0 < poleExteriorWeight x k := by
  unfold poleExteriorWeight
  exact mul_pos (by exact_mod_cast Nat.centralBinom_pos k)
    (pow_pos (div_pos hx (by norm_num)) k)

theorem poleExteriorWeight_succ_eq {x : ℝ} (hx : 0 < x) (k : ℕ) :
    poleExteriorWeight x (k + 1) =
      (x * (2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) * poleExteriorWeight x k := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold poleExteriorWeight
  rw [pow_succ]
  field_simp
  nlinarith

theorem poleExteriorWeight_succ_div {x : ℝ} (hx : 0 < x) (k : ℕ) :
    poleExteriorWeight x (k + 1) / poleExteriorWeight x k =
      x * (2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1)) := by
  rw [poleExteriorWeight_succ_eq hx]
  field_simp [ne_of_gt (poleExteriorWeight_pos hx k)]

private theorem tendsto_centralBinom_ratio_factor :
    Tendsto (fun k : ℕ => (2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1)))
      atTop (nhds 1) := by
  have hden : Tendsto (fun k : ℕ => (2 * (k : ℝ) + 2)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 2
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
  have hinv : Tendsto (fun k : ℕ => (2 * (k : ℝ) + 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hinv
  convert hsub using 1
  · funext k
    have hk : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

theorem tendsto_poleExteriorWeight_ratio {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k : ℕ => poleExteriorWeight x (k + 1) / poleExteriorWeight x k)
      atTop (nhds x) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x)).mul
    tendsto_centralBinom_ratio_factor
  convert h using 1
  · funext k
    rw [poleExteriorWeight_succ_div hx]
    ring
  · ring

theorem tendsto_poleExteriorWeight_atTop {x : ℝ} (hx : 1 < x) :
    Tendsto (poleExteriorWeight x) atTop atTop := by
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < poleExteriorWeight x k :=
    Filter.Eventually.of_forall (poleExteriorWeight_pos (zero_lt_one.trans hx))
  have hdiv := GaloisForLFunctions.tendsto_div_natCast_atTop_of_ratio_tendsto_gt_one
    hpos (tendsto_poleExteriorWeight_ratio (zero_lt_one.trans hx)) hx
  refine tendsto_atTop_mono' atTop ?_ hdiv
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hw := (poleExteriorWeight_pos (zero_lt_one.trans hx) k).le
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact div_le_self hw hkreal

theorem poleHalfExteriorTerm_neg {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 1 ≤ k) :
    poleHalfExteriorTerm x k < 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [poleHalfExteriorTerm, hx]
  | succ k hk ih =>
      have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
          Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
        rw [eq_div_iff (ne_of_gt hk1)]
        simpa [mul_comm] using hrec
      have hterm : poleHalfExteriorTerm x (k + 1) =
          poleHalfExteriorTerm x k *
            (x * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
        unfold poleHalfExteriorTerm
        rw [hchoose, pow_succ]
        ring
      rw [hterm]
      exact mul_neg_of_neg_of_pos ih
        (div_pos (mul_pos hx hkpos) hk1)

theorem poleHalfExteriorMagnitude_pos {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 1 ≤ k) :
    0 < poleHalfExteriorMagnitude x k := by
  exact neg_pos.mpr (poleHalfExteriorTerm_neg hx hk)

theorem poleHalfExteriorMagnitude_succ_eq {x : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    poleHalfExteriorMagnitude x (k + 1) =
      (x * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) * poleHalfExteriorMagnitude x k := by
  have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
      Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hk1)]
    simpa [mul_comm] using hrec
  unfold poleHalfExteriorMagnitude poleHalfExteriorTerm
  rw [hchoose, pow_succ]
  ring

theorem poleHalfExteriorMagnitude_succ_div {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 1 ≤ k) :
    poleHalfExteriorMagnitude x (k + 1) / poleHalfExteriorMagnitude x k =
      x * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1) := by
  rw [poleHalfExteriorMagnitude_succ_eq hk]
  field_simp [ne_of_gt (poleHalfExteriorMagnitude_pos hx hk)]

private theorem tendsto_half_ratio_factor :
    Tendsto (fun k : ℕ => ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1))
      atTop (nhds 1) := by
  have hden : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hmul := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (3 / 2 : ℝ)) atTop (nhds (3 / 2))).mul hinv
  have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hmul
  convert hsub using 1
  · funext k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

theorem tendsto_poleHalfExteriorMagnitude_ratio {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun k : ℕ => poleHalfExteriorMagnitude x (k + 1) /
        poleHalfExteriorMagnitude x k)
      atTop (nhds x) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x)).mul
    tendsto_half_ratio_factor
  simpa only [mul_one] using h.congr' (by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [poleHalfExteriorMagnitude_succ_div hx hk]
    ring)

theorem tendsto_poleHalfExteriorMagnitude_atTop {x : ℝ} (hx : 1 < x) :
    Tendsto (poleHalfExteriorMagnitude x) atTop atTop := by
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < poleHalfExteriorMagnitude x k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact poleHalfExteriorMagnitude_pos (zero_lt_one.trans hx) hk
  have hdiv := GaloisForLFunctions.tendsto_div_natCast_atTop_of_ratio_tendsto_gt_one
    hpos (tendsto_poleHalfExteriorMagnitude_ratio (zero_lt_one.trans hx)) hx
  refine tendsto_atTop_mono' atTop ?_ hdiv
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hw := (poleHalfExteriorMagnitude_pos (zero_lt_one.trans hx) hk).le
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact div_le_self hw hkreal

theorem poleHalfExteriorSum_le_one {x : ℝ} (hx : 0 < x) (N : ℕ) :
    poleHalfExteriorSum x N ≤ 1 := by
  induction N with
  | zero => simp [poleHalfExteriorSum]
  | succ N ih =>
      rw [poleHalfExteriorSum, Finset.sum_range_succ, ← poleHalfExteriorSum]
      rcases N with _ | N
      · norm_num [poleHalfExteriorTerm, poleHalfExteriorSum]
      · exact (add_le_of_nonpos_right
          (le_of_lt (poleHalfExteriorTerm_neg hx (by omega)))).trans ih

theorem poleHalfExteriorSum_succ_le_one_sub_magnitude {x : ℝ} (hx : 0 < x)
    (k : ℕ) :
    poleHalfExteriorSum x (k + 1) ≤ 1 - poleHalfExteriorMagnitude x k := by
  rw [poleHalfExteriorSum, Finset.sum_range_succ, ← poleHalfExteriorSum,
    poleHalfExteriorMagnitude]
  linarith [poleHalfExteriorSum_le_one hx k]

theorem eventually_poleHalfExteriorSum_le_neg_one {x : ℝ} (hx : 1 < x) :
    ∀ᶠ N : ℕ in atTop, poleHalfExteriorSum x N ≤ -1 := by
  have hmag := (tendsto_poleHalfExteriorMagnitude_atTop hx).comp
    (tendsto_sub_atTop_nat 1)
  filter_upwards [hmag.eventually_ge_atTop 2, eventually_ge_atTop 2] with N hmagN hN
  simp only [Function.comp_apply] at hmagN
  have hsum := poleHalfExteriorSum_succ_le_one_sub_magnitude
    (zero_lt_one.trans hx) (N - 1)
  rw [show N - 1 + 1 = N by omega] at hsum
  linarith

theorem eventually_one_le_abs_poleHalfExteriorSum {x : ℝ} (hx : 1 < x) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ |poleHalfExteriorSum x N| := by
  filter_upwards [eventually_poleHalfExteriorSum_le_neg_one hx] with N hN
  rw [abs_of_nonpos (hN.trans (by norm_num))]
  linarith

/-- A real sequence with eventual increments at least one diverges to `+∞`. -/
theorem tendsto_atTop_of_eventually_one_le_sub_succ {u : ℕ → ℝ}
    (hinc : ∀ᶠ n : ℕ in atTop, 1 ≤ u (n + 1) - u n) :
    Tendsto u atTop atTop := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hinc
  have hbound : ∀ k : ℕ, u M + (k : ℝ) ≤ u (M + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := hM (M + k) (by omega)
        calc
          u M + ((k + 1 : ℕ) : ℝ) = (u M + (k : ℝ)) + 1 := by
            push_cast
            ring
          _ ≤ u (M + k) + 1 := by linarith
          _ ≤ u (M + k + 1) := by linarith
          _ = u (M + (k + 1)) := by rw [Nat.add_assoc]
  have hlower : Tendsto (fun n : ℕ => u M + ((n - M : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop (u M)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_sub_atTop_nat M))
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [eventually_ge_atTop M] with n hn
  simpa [show M + (n - M) = n by omega] using hbound (n - M)

theorem poleNegHalfExteriorSum_add_two (x : ℝ) (N : ℕ) :
    poleNegHalfExteriorSum x (N + 2) =
      poleNegHalfExteriorSum x N +
        (-1 : ℝ) ^ N * poleExteriorWeight x N +
        (-1 : ℝ) ^ (N + 1) * poleExteriorWeight x (N + 1) := by
  rw [show N + 2 = (N + 1) + 1 by omega,
    poleNegHalfExteriorSum, Finset.sum_range_succ,
    show ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * poleExteriorWeight x k =
      poleNegHalfExteriorSum x N + (-1 : ℝ) ^ N * poleExteriorWeight x N by
        rw [poleNegHalfExteriorSum, Finset.sum_range_succ]]

theorem poleNegHalfExteriorSum_odd_succ (x : ℝ) (m : ℕ) :
    poleNegHalfExteriorSum x (2 * (m + 1) + 1) -
        poleNegHalfExteriorSum x (2 * m + 1) =
      poleExteriorWeight x (2 * m + 2) - poleExteriorWeight x (2 * m + 1) := by
  rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
    poleNegHalfExteriorSum_add_two]
  have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  have heven : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]
    norm_num
  rw [hodd, heven]
  ring

theorem poleNegHalfExteriorSum_even_succ (x : ℝ) (m : ℕ) :
    poleNegHalfExteriorSum x (2 * (m + 1) + 2) -
        poleNegHalfExteriorSum x (2 * m + 2) =
      poleExteriorWeight x (2 * m + 2) - poleExteriorWeight x (2 * m + 3) := by
  rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
    poleNegHalfExteriorSum_add_two]
  have heven : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
    rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
    norm_num
  have hodd : (-1 : ℝ) ^ (2 * m + 2 + 1) = -1 := by
    rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  rw [heven, hodd]
  ring

private theorem eventually_poleExteriorWeight_ge_midpoint_mul {x : ℝ} (hx : 1 < x) :
    ∀ᶠ k : ℕ in atTop,
      ((1 + x) / 2) * poleExteriorWeight x k ≤ poleExteriorWeight x (k + 1) := by
  have hmid : (1 + x) / 2 < x := by linarith
  have hratio := (tendsto_poleExteriorWeight_ratio (zero_lt_one.trans hx)).eventually
    (Ioi_mem_nhds hmid)
  filter_upwards [hratio] with k hk
  rw [lt_div_iff₀ (poleExteriorWeight_pos (zero_lt_one.trans hx) k)] at hk
  exact hk.le

theorem tendsto_poleNegHalfExteriorSum_odd_atTop {x : ℝ} (hx : 1 < x) :
    Tendsto (fun m : ℕ => poleNegHalfExteriorSum x (2 * m + 1)) atTop atTop := by
  let q : ℝ := (1 + x) / 2
  have hq1 : 1 < q := by dsimp [q]; linarith
  have hindex : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hlarge : ∀ᶠ m : ℕ in atTop,
      1 ≤ (q - 1) * poleExteriorWeight x (2 * m + 1) :=
    ((tendsto_poleExteriorWeight_atTop hx).comp hindex).const_mul_atTop
      (sub_pos.mpr hq1) |>.eventually_ge_atTop 1
  have hgrowth := hindex.eventually (eventually_poleExteriorWeight_ge_midpoint_mul hx)
  apply tendsto_atTop_of_eventually_one_le_sub_succ
  filter_upwards [hlarge, hgrowth] with m hlargeM hgrowthM
  rw [poleNegHalfExteriorSum_odd_succ]
  dsimp [q] at hlargeM
  nlinarith

theorem tendsto_neg_poleNegHalfExteriorSum_even_atTop {x : ℝ} (hx : 1 < x) :
    Tendsto (fun m : ℕ => -poleNegHalfExteriorSum x (2 * m + 2)) atTop atTop := by
  let q : ℝ := (1 + x) / 2
  have hq1 : 1 < q := by dsimp [q]; linarith
  have hindex : Tendsto (fun m : ℕ => 2 * m + 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hlarge : ∀ᶠ m : ℕ in atTop,
      1 ≤ (q - 1) * poleExteriorWeight x (2 * m + 2) :=
    ((tendsto_poleExteriorWeight_atTop hx).comp hindex).const_mul_atTop
      (sub_pos.mpr hq1) |>.eventually_ge_atTop 1
  have hgrowth := hindex.eventually (eventually_poleExteriorWeight_ge_midpoint_mul hx)
  apply tendsto_atTop_of_eventually_one_le_sub_succ
  filter_upwards [hlarge, hgrowth] with m hlargeM hgrowthM
  rw [show -poleNegHalfExteriorSum x (2 * (m + 1) + 2) -
      -poleNegHalfExteriorSum x (2 * m + 2) =
    -(poleNegHalfExteriorSum x (2 * (m + 1) + 2) -
      poleNegHalfExteriorSum x (2 * m + 2)) by ring,
    poleNegHalfExteriorSum_even_succ]
  dsimp [q] at hlargeM
  nlinarith

theorem eventually_one_le_abs_poleNegHalfExteriorSum {x : ℝ} (hx : 1 < x) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ |poleNegHalfExteriorSum x N| := by
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_poleNegHalfExteriorSum_odd_atTop hx).eventually_ge_atTop 1)
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
    ((tendsto_neg_poleNegHalfExteriorSum_even_atTop hx).eventually_ge_atTop 1)
  let M := max M₁ M₂
  refine Filter.eventually_atTop.2 ⟨2 * (M + 1) + 1, fun N hN => ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm : M + 1 ≤ m := by omega
    let k := m - 1
    have hkM₂ : M₂ ≤ k := by dsimp [k, M] at *; omega
    have hneg := hM₂ k hkM₂
    have hindex : 2 * k + 2 = 2 * m := by dsimp [k]; omega
    rw [hindex] at hneg
    rw [abs_of_nonpos (by linarith)]
    exact hneg
  · have hm : M₁ ≤ m := by dsimp [M] at *; omega
    have hpos := hM₁ m hm
    rw [abs_of_nonneg (by linarith)]
    exact hpos

private theorem poleBinomialPartialSum_eq_sum_choose_real
    (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

theorem complex_poleHalfExteriorPartialSum_eq (x : ℝ) (N : ℕ) :
    (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-(x : ℂ)) =
      (poleHalfExteriorSum x N : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    show -(x : ℂ) = ((-x : ℝ) : ℂ) by simp,
    complex_binomialPartialSum_ofReal,
    poleBinomialPartialSum_eq_sum_choose_real]
  rfl

theorem complex_poleNegHalfExteriorPartialSum_eq (x : ℝ) (N : ℕ) :
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (x : ℂ) =
      (poleNegHalfExteriorSum x N : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    poleBinomialPartialSum_eq_sum_choose_real]
  congr 1
  unfold poleNegHalfExteriorSum poleExteriorWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [GaloisForLFunctions.choose_neg_half]
  calc
    (-1 : ℝ) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k * x ^ k =
        (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ) ^ k)⁻¹ * x ^ k := by ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ)⁻¹ * x) ^ k := by
      rw [← inv_pow, mul_pow]
      ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k * (x / 4) ^ k := by
      congr 1
      ring
  ring

theorem eventually_one_le_norm_poleHalfExteriorPartialSum {x : ℝ} (hx : 1 < x) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-(x : ℂ))‖ := by
  filter_upwards [eventually_one_le_abs_poleHalfExteriorSum hx] with N hN
  rw [complex_poleHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  exact hN

theorem eventually_one_le_norm_poleNegHalfExteriorPartialSum {x : ℝ} (hx : 1 < x) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (x : ℂ)‖ := by
  filter_upwards [eventually_one_le_abs_poleNegHalfExteriorSum hx] with N hN
  rw [complex_poleNegHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  exact hN

theorem eventually_one_le_norm_poleFactorSqrtApprox_of_cayley_eq_neg_real
    (s : ℂ) {x : ℝ} (hx : 1 < x)
    (hcayley : poleFactorCayley s = -(x : ℂ)) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ ‖poleFactorSqrtApprox N s‖ := by
  filter_upwards [eventually_one_le_norm_poleHalfExteriorPartialSum hx,
    eventually_one_le_norm_poleNegHalfExteriorPartialSum hx] with N hhalf hneg
  rw [poleFactorSqrtApprox, hcayley, neg_neg, norm_mul]
  nlinarith [norm_nonneg
    ((binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-(x : ℂ))),
    norm_nonneg ((binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (x : ℂ))]

theorem poleFactorCayley_real_eq_neg_two_div_sub_one {sigma : ℝ} (hsigma : 0 < sigma) :
    poleFactorCayley (sigma : ℂ) = -((2 / sigma - 1 : ℝ) : ℂ) := by
  apply Complex.ext
  · norm_num [poleFactorCayley, GaloisForLFunctions.HTGeometry.cayleyRight]
    field_simp [ne_of_gt hsigma]
    ring
  · norm_num [poleFactorCayley, GaloisForLFunctions.HTGeometry.cayleyRight]

/-- Every real point in the open critical strip has eventually nonvanishing Cayley square-root
approximants, uniformly in the cutoff tail. -/
theorem eventually_one_le_norm_poleFactorSqrtApprox_realInterior
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ ‖poleFactorSqrtApprox N (sigma : ℂ)‖ := by
  have hsigma : 0 < sigma := by linarith
  have hx : 1 < 2 / sigma - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hsigma]
    nlinarith
  exact eventually_one_le_norm_poleFactorSqrtApprox_of_cayley_eq_neg_real
    (sigma : ℂ) hx (poleFactorCayley_real_eq_neg_two_div_sub_one hsigma)

theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_realInterior
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ ≤ C := by
  simpa using
    (not_eventually_bounded_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
      (sigma := sigma) hhalf hone)

/-- At every real point in the open critical strip, local boundedness of a cofinal corrected
family forces its counterterm to have no bounded tail. -/
theorem counterterm_not_eventually_bounded_at_realInterior_of_cofinal_locallyBounded
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N (sigma : ℂ)‖ ≤ B := by
  have hsigma_mem : (sigma : ℂ) ∈ rightHalf := by
    rw [mem_rightHalf]
    norm_num
    linarith
  obtain ⟨R, hR, _, C, hC⟩ := hloc (sigma : ℂ) hsigma_mem
  have hcenter : (sigma : ℂ) ∈ ball (sigma : ℂ) R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N (sigma : ℂ)‖ ≤ C :=
    fun N => hC N (sigma : ℂ) hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_one_le_norm_poleFactorSqrtApprox_realInterior hhalf hone))
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_realInterior hhalf hone
  let Q : ℝ := C * ‖squarefreeCarlemanHalfDet (sigma : ℂ)‖
  refine ⟨Q + B, max N₀ M₀, fun N hN => ?_⟩
  have hNkappa : 1 ≤ ‖poleFactorSqrtApprox (kappa N) (sigma : ℂ)‖ :=
    hN₀ N ((le_max_left N₀ M₀).trans hN)
  have hNM : M₀ ≤ N := (le_max_right N₀ M₀).trans hN
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet (sigma : ℂ)‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero (sigma : ℂ))
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) (sigma : ℂ)‖ *
          ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
            counterterm N (sigma : ℂ)‖ ≤ Q := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hcorrected :
      ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
        counterterm N (sigma : ℂ)‖ ≤ Q := by
    calc
      _ = 1 * ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
          counterterm N (sigma : ℂ)‖ := by ring
      _ ≤ ‖poleFactorSqrtApprox (kappa N) (sigma : ℂ)‖ *
          ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
            counterterm N (sigma : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hNkappa (norm_nonneg _)
      _ ≤ Q := hprod
  calc
    ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ =
        ‖(squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
          counterterm N (sigma : ℂ)) - counterterm N (sigma : ℂ)‖ := by ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
          counterterm N (sigma : ℂ)‖ + ‖counterterm N (sigma : ℂ)‖ := norm_sub_le _ _
    _ ≤ Q + B := add_le_add hcorrected (hB N hNM)

theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_realInterior
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm : Tendsto (fun N => counterterm N (sigma : ℂ)) atTop (nhds 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  apply counterterm_not_eventually_bounded_at_realInterior_of_cofinal_locallyBounded
    hhalf hone hkappa hloc
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

end

end RHTower
