import GaloisForLFunctions.RHTower.CausalMobiusThetaRamareForm
import GaloisForLFunctions.RHTower.EulerDeletionPhysicalCellMoebiusIdentity

/-!
# The causal tail is a Gaussian observation of the Euler-deletion physical source

With the theta seed `g(u) = (4π²u⁴ − 6πu²) e^{−πu²}`, the truncated divisor field
`D_N(r) = Σ_{d|r, d≤N} μ(d)`, `H_N = Σ_{d≤N} μ(d)/d` and the physical cell source
`C_N(r) = Σ_{d≤N} μ(d){r/d} = r H_N − Σ_{j≤r} D_N(j)`:

* the atom formula `k(log(n/N))/√n = N^{−1/2} Σ_m g(mn/N)`;
* **(11)** `B(N) = −N^{−1/2} Σ_{r>N} g(r/N) D_N(r)`;
* **(13)** `Σ_r g(r/N) = √N k(log N) = N Σ_m g(mN)` (completed theta reflection);
* **(12)** summation by parts across all physical cells;
* **(14)–(15)** `B(N) = Σ_{r≥1} C_N(r) q_N(r)/(r(r+1)) + e_N` with the smooth complete-cell
  wavelet `q_N(r) = r(r+1)(g(r/N) − g((r+1)/N))/√N`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Gaussian moment bounds for the seed -/

theorem exists_abs_pow_mul_exp_neg_pi_sq_le (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ^ k * Real.exp (-Real.pi * x ^ 2) ≤ M := by
  refine ⟨Real.exp Real.pi * (k.factorial / Real.pi ^ k), by positivity, fun x => ?_⟩
  have h := one_add_pow_mul_exp_neg_le Real.pi_pos k (sq_nonneg x)
  have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]
  calc |x| ^ k * Real.exp (-Real.pi * x ^ 2) ≤ (1 + x ^ 2) ^ k * Real.exp (-(Real.pi * x ^ 2)) := by
        rw [neg_mul]; gcongr
    _ ≤ _ := h

theorem thetaCuspSeed_zero : thetaCuspSeed 0 = 0 := by simp [thetaCuspSeed]

theorem abs_thetaCuspSeed_le_poly (x : ℝ) :
    |thetaCuspSeed x| ≤ (4 * Real.pi ^ 2 * |x| ^ 4 + 6 * Real.pi * |x| ^ 2) *
      Real.exp (-Real.pi * x ^ 2) := by
  have h4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [thetaCuspSeed, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hb : |2 * Real.pi * x ^ 4 - 3 * x ^ 2| ≤ 2 * Real.pi * |x| ^ 4 + 3 * |x| ^ 2 := by
    rw [← h4, ← h2, abs_le]
    have : 0 ≤ x ^ 4 := by positivity
    have : 0 ≤ x ^ 2 := by positivity
    constructor <;> nlinarith [Real.pi_pos]
  calc 2 * Real.pi * |2 * Real.pi * x ^ 4 - 3 * x ^ 2| ≤
        2 * Real.pi * (2 * Real.pi * |x| ^ 4 + 3 * |x| ^ 2) := by gcongr
    _ = _ := by ring

/-- `|g(x)| ≤ C x²`. -/
theorem exists_abs_thetaCuspSeed_le_sq : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |thetaCuspSeed x| ≤ C * x ^ 2 := by
  obtain ⟨M2, hM2, h2⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le 2
  refine ⟨4 * Real.pi ^ 2 * M2 + 6 * Real.pi, by positivity, fun x => ?_⟩
  refine (abs_thetaCuspSeed_le_poly x).trans ?_
  have he : Real.exp (-Real.pi * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h2x := h2 x
  calc (4 * Real.pi ^ 2 * |x| ^ 4 + 6 * Real.pi * |x| ^ 2) * Real.exp (-Real.pi * x ^ 2)
      = |x| ^ 2 * (4 * Real.pi ^ 2 * (|x| ^ 2 * Real.exp (-Real.pi * x ^ 2)) +
          6 * Real.pi * Real.exp (-Real.pi * x ^ 2)) := by ring
    _ ≤ |x| ^ 2 * (4 * Real.pi ^ 2 * M2 + 6 * Real.pi * 1) := by gcongr
    _ = _ := by rw [hx2]; ring

/-- `|g(x)| ≤ C x^{−3}` for `x > 0`. -/
theorem exists_abs_thetaCuspSeed_le_inv_cube :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → |thetaCuspSeed x| ≤ C * (x ^ 3)⁻¹ := by
  obtain ⟨M7, hM7, h7⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le 7
  obtain ⟨M5, hM5, h5⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le 5
  refine ⟨4 * Real.pi ^ 2 * M7 + 6 * Real.pi * M5, by positivity, fun x hx => ?_⟩
  rw [le_mul_inv_iff₀ (by positivity)]
  have h := abs_thetaCuspSeed_le_poly x
  have h7 := h7 x
  have h5 := h5 x
  rw [abs_of_pos hx] at h h7 h5
  calc |thetaCuspSeed x| * x ^ 3 ≤ (4 * Real.pi ^ 2 * x ^ 4 + 6 * Real.pi * x ^ 2) *
        Real.exp (-Real.pi * x ^ 2) * x ^ 3 := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 4 * Real.pi ^ 2 * (x ^ 7 * Real.exp (-Real.pi * x ^ 2)) +
        6 * Real.pi * (x ^ 5 * Real.exp (-Real.pi * x ^ 2)) := by ring
    _ ≤ 4 * Real.pi ^ 2 * M7 + 6 * Real.pi * M5 := by gcongr

theorem abs_thetaCuspSeedDeriv_le_poly (x : ℝ) :
    |thetaCuspSeedDeriv x| ≤ 2 * Real.pi * (4 * Real.pi ^ 2 * |x| ^ 5 + 14 * Real.pi * |x| ^ 3 + 6 * |x|) *
      Real.exp (-Real.pi * x ^ 2) := by
  rw [thetaCuspSeedDeriv, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (Real.exp_pos _).le
  calc |-(4 * Real.pi ^ 2) * x ^ 5 + 14 * Real.pi * x ^ 3 - 6 * x|
      ≤ |-(4 * Real.pi ^ 2) * x ^ 5| + |14 * Real.pi * x ^ 3| + |6 * x| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = _ := by simp [abs_mul, abs_pow, abs_of_pos Real.pi_pos]

/-- `|g'(x)| ≤ K |x|`. -/
theorem exists_abs_thetaCuspSeedDeriv_le_mul : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |thetaCuspSeedDeriv x| ≤ K * |x| := by
  obtain ⟨M4, hM4, h4⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le 4
  obtain ⟨M2, hM2, h2⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le 2
  refine ⟨2 * Real.pi * (4 * Real.pi ^ 2 * M4 + 14 * Real.pi * M2 + 6), by positivity, fun x => ?_⟩
  refine (abs_thetaCuspSeedDeriv_le_poly x).trans ?_
  have he : Real.exp (-Real.pi * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hx := abs_nonneg x
  calc 2 * Real.pi * (4 * Real.pi ^ 2 * |x| ^ 5 + 14 * Real.pi * |x| ^ 3 + 6 * |x|) * Real.exp (-Real.pi * x ^ 2)
      = 2 * Real.pi * |x| * (4 * Real.pi ^ 2 * (|x| ^ 4 * Real.exp (-Real.pi * x ^ 2)) +
          14 * Real.pi * (|x| ^ 2 * Real.exp (-Real.pi * x ^ 2)) + 6 * Real.exp (-Real.pi * x ^ 2)) := by ring
    _ ≤ 2 * Real.pi * |x| * (4 * Real.pi ^ 2 * M4 + 14 * Real.pi * M2 + 6 * 1) := by
        gcongr
        · exact h4 x
        · exact h2 x
    _ = _ := by ring

/-- `|g'(x)| ≤ K (1+x)^{−3}` for `x ≥ 0`. -/
theorem exists_abs_thetaCuspSeedDeriv_le_inv_cube :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → |thetaCuspSeedDeriv x| ≤ K * ((1 + x) ^ 3)⁻¹ := by
  obtain ⟨M, hM, hMk⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ k ∈ ({1, 3, 4, 5, 6, 8} : Finset ℕ), ∀ x : ℝ,
      |x| ^ k * Real.exp (-Real.pi * x ^ 2) ≤ M := by
    choose M hM0 hM using exists_abs_pow_mul_exp_neg_pi_sq_le
    have := hM0 1; have := hM0 3; have := hM0 4; have := hM0 5; have := hM0 6; have := hM0 8
    refine ⟨M 1 + M 3 + M 4 + M 5 + M 6 + M 8, by linarith, fun k hk x => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith [hM 1 x, hM 3 x, hM 4 x, hM 5 x, hM 6 x, hM 8 x]
  refine ⟨4 * 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) * 2 * M, by positivity, fun x hx => ?_⟩
  rw [le_mul_inv_iff₀ (by positivity)]
  have hcube : (1 + x) ^ 3 ≤ 4 * (1 + x ^ 3) := by nlinarith [sq_nonneg (1 - x), hx]
  have h := abs_thetaCuspSeedDeriv_le_poly x
  rw [abs_of_nonneg hx] at h
  have hk : ∀ k ∈ ({1, 3, 4, 5, 6, 8} : Finset ℕ), x ^ k * Real.exp (-Real.pi * x ^ 2) ≤ M := by
    intro k hk'
    have := hMk k hk' x
    rwa [abs_of_nonneg hx] at this
  have e1 := hk 1 (by simp); have e3 := hk 3 (by simp); have e4 := hk 4 (by simp)
  have e5 := hk 5 (by simp); have e6 := hk 6 (by simp); have e8 := hk 8 (by simp)
  have hE := Real.exp_pos (-Real.pi * x ^ 2)
  calc |thetaCuspSeedDeriv x| * (1 + x) ^ 3 ≤ 2 * Real.pi * (4 * Real.pi ^ 2 * x ^ 5 + 14 * Real.pi * x ^ 3 + 6 * x) *
        Real.exp (-Real.pi * x ^ 2) * (4 * (1 + x ^ 3)) :=
        mul_le_mul h hcube (by positivity) (by positivity)
    _ = 4 * 2 * Real.pi * (4 * Real.pi ^ 2 * (x ^ 5 * Real.exp (-Real.pi * x ^ 2) + x ^ 8 * Real.exp (-Real.pi * x ^ 2)) +
        14 * Real.pi * (x ^ 3 * Real.exp (-Real.pi * x ^ 2) + x ^ 6 * Real.exp (-Real.pi * x ^ 2)) +
        6 * (x ^ 1 * Real.exp (-Real.pi * x ^ 2) + x ^ 4 * Real.exp (-Real.pi * x ^ 2))) := by ring
    _ ≤ 4 * 2 * Real.pi * (4 * Real.pi ^ 2 * (M + M) + 14 * Real.pi * (M + M) + 6 * (M + M)) := by
        gcongr
    _ = _ := by ring

/-! ## The atom formula -/

/-- `n^{−1/2} k(log(n/N)) = N^{−1/2} Σ_m g(mn/N)`. -/
theorem causalAmplitude_eq_tsum_seed {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    causalAmplitude N n = (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑' m : ℕ, thetaCuspSeed (m * n / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [causalAmplitude, thetaCuspFullSource, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [thetaCuspSourceTerm, Real.exp_log (div_pos hnR hNR)]
  have hsqrt : Real.exp (Real.log (n / N) / 2) = (n : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.log_div hnR.ne' hNR.ne', Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hNR, ← Real.exp_add]
    ring_nf
  rw [hsqrt, show (m : ℝ) * (n / N) = m * n / N by ring]
  have : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hnR]; norm_num
  calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspSeed (m * n / N))
      = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ)) * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspSeed (m * n / N)) := by ring
    _ = _ := by rw [this, one_mul]

/-! ## The truncated divisor field

`D_N = truncMoebiusDivisorSum N`, `C_N = cell μ N` and the identity
`C_N(r) = r H_N − Σ_{j≤r} D_N(j)` are those of the Euler-deletion physical cells
(`physical_moebius_cell_eq_truncated_divisor_tail`). -/

/-- `H_N = Σ_{d≤N} μ(d)/d`. -/
def moebiusHarmonic (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d

/-- The physical cell source `C_N(r) = Σ_{d≤N} μ(d){r/d}`. -/
abbrev moebiusCell (N r : ℕ) : ℝ :=
  DeletionCoefficientTransfer.cell (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N r

theorem truncMoebiusDivisorSum_eq_sum_divisors_filter (N : ℕ) {r : ℕ} (hr : r ≠ 0) :
    truncMoebiusDivisorSum N r =
      ∑ d ∈ r.divisors.filter (· ≤ N), ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
  rw [truncMoebiusDivisorSum]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨⟨h3, hr⟩, h2⟩
  · rintro ⟨⟨h3, -⟩, h2⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos h3 (Nat.pos_of_ne_zero hr), h2⟩, h3⟩

theorem abs_truncMoebiusDivisorSum_le (N r : ℕ) : |truncMoebiusDivisorSum N r| ≤ N := by
  rw [truncMoebiusDivisorSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ Finset.filter (fun d => d ∣ r) (Finset.Icc 1 N), |((ArithmeticFunction.moebius d : ℤ) : ℝ)|
      ≤ ∑ d ∈ Finset.filter (fun d => d ∣ r) (Finset.Icc 1 N), (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => zero_le_one
    _ = N := by simp

theorem moebiusCell_eq (N r : ℕ) :
    moebiusCell N r = r * moebiusHarmonic N - ∑ j ∈ Finset.Icc 1 r, truncMoebiusDivisorSum N j :=
  physical_moebius_cell_eq_truncated_divisor_tail N r

theorem moebiusCell_zero (N : ℕ) : moebiusCell N 0 = 0 := by
  rw [moebiusCell_eq]; simp

/-- `D_N(r) = H_N − (C_N(r) − C_N(r−1))` for `r ≥ 1`. -/
theorem truncMoebiusDivisorSum_eq_harmonic_sub (N : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    truncMoebiusDivisorSum N r = moebiusHarmonic N - (moebiusCell N r - moebiusCell N (r - 1)) := by
  rw [moebiusCell_eq, moebiusCell_eq]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

theorem abs_moebiusCell_le (N r : ℕ) : |moebiusCell N r| ≤ N := by
  have h := DeletionCoefficientTransfer.abs_cell_le_mass
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N r
  refine h.trans ?_
  rw [DeletionCoefficientTransfer.mass]
  calc ∑ i ∈ Finset.range N, |((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ)| ≤
        ∑ i ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = N := by simp

/-! ## (11) The Gaussian observation of the truncated divisor field -/

/-- The fiber of `(n, m) ↦ nm` over `r ≠ 0`, read through the divisors of `r`. -/
theorem tsum_mulFiber_eq_sum_divisors (f : ℕ × ℕ → ℝ) {r : ℕ} (hr : r ≠ 0) :
    ∑' b : (fun nm : ℕ × ℕ => nm.1 * nm.2) ⁻¹' {r}, f b = ∑ n ∈ r.divisors, f (n, r / n) := by
  rw [tsum_subtype ((fun nm : ℕ × ℕ => nm.1 * nm.2) ⁻¹' {r}) f]
  have hinj : Set.InjOn (fun n : ℕ => (n, r / n)) r.divisors := fun a _ b _ h => by
    simpa using congrArg Prod.fst h
  rw [tsum_eq_sum (s := r.divisors.image fun n => (n, r / n)), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnr := Nat.dvd_of_mem_divisors hn
    rw [Set.indicator_of_mem (show (n, r / n) ∈ (fun nm : ℕ × ℕ => nm.1 * nm.2) ⁻¹' {r} from
      by simp [Nat.mul_div_cancel' hnr])]
  · intro b hb
    by_cases hmem : b ∈ (fun nm : ℕ × ℕ => nm.1 * nm.2) ⁻¹' {r}
    · exfalso; apply hb
      have hbn : b.1 * b.2 = r := hmem
      have hb1 : b.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hbn; exact hr hbn.symm
      rw [Finset.mem_image]
      refine ⟨b.1, Nat.mem_divisors.2 ⟨⟨b.2, hbn.symm⟩, hr⟩, ?_⟩
      ext
      · rfl
      · simp only; rw [← hbn, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb1)]
    · exact Set.indicator_of_notMem hmem _

/-- **(11)** `B(N) = −N^{−1/2} Σ_{r>N} g(r/N) D_N(r)` for `N ≥ 1`. -/
theorem causalMobiusThetaTail_natCast_eq {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N = -((N : ℝ) ^ (-(1 / 2 : ℝ)) *
      ∑' r : ℕ, if N < r then thetaCuspSeed (r / N) * truncMoebiusDivisorSum N r else 0) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set F : ℕ × ℕ → ℝ := fun nm => if N < nm.1 then
    ((ArithmeticFunction.moebius nm.1 : ℤ) : ℝ) * thetaCuspSeed (nm.2 * nm.1 / N) else 0
  obtain ⟨Cg, hCg0, hCg⟩ := exists_abs_thetaCuspSeed_le_inv_cube
  have hFb : ∀ nm : ℕ × ℕ, |F nm| ≤ Cg * N ^ 3 * (((nm.1 : ℝ) ^ 3)⁻¹ * ((nm.2 : ℝ) ^ 3)⁻¹) := by
    intro nm
    simp only [F]
    split_ifs with h
    · rcases Nat.eq_zero_or_pos nm.2 with h2 | h2
      · rw [h2]; simp [thetaCuspSeed_zero]
      have h1 : (0 : ℝ) < nm.1 := by exact_mod_cast (show 0 < nm.1 by omega)
      have h2' : (0 : ℝ) < nm.2 := by exact_mod_cast h2
      have hx : (0 : ℝ) < nm.2 * nm.1 / N := by positivity
      have hμ : |((ArithmeticFunction.moebius nm.1 : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rw [abs_mul]
      calc |((ArithmeticFunction.moebius nm.1 : ℤ) : ℝ)| * |thetaCuspSeed (nm.2 * nm.1 / N)|
          ≤ 1 * (Cg * ((nm.2 * nm.1 / N : ℝ) ^ 3)⁻¹) :=
            mul_le_mul hμ (hCg _ hx) (abs_nonneg _) zero_le_one
        _ = _ := by field_simp
    · rw [abs_zero]; positivity
  have hcube : Summable fun n : ℕ => ((n : ℝ) ^ 3)⁻¹ := Real.summable_nat_pow_inv.2 (by norm_num)
  have hprod : Summable fun nm : ℕ × ℕ => ((nm.1 : ℝ) ^ 3)⁻¹ * ((nm.2 : ℝ) ^ 3)⁻¹ := by
    have hn : Summable fun n : ℕ => ‖((n : ℝ) ^ 3)⁻¹‖ := hcube.norm
    exact summable_mul_of_summable_norm (f := fun n : ℕ => ((n : ℝ) ^ 3)⁻¹)
      (g := fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) hn hn
  have hFs : Summable F := Summable.of_norm_bounded (hprod.mul_left (Cg * N ^ 3)) fun nm => by
    rw [Real.norm_eq_abs]; exact hFb nm
  -- each term of the tail
  have hterm : ∀ n : ℕ, causalMobiusThetaTerm N n = (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑' m : ℕ, F (n, m) := by
    intro n
    by_cases hn : N < n
    · have hn0 : 0 < n := by omega
      rw [causalMobiusThetaTerm, Set.indicator_of_mem (show (N : ℝ) ∈ Ioo 0 (n : ℝ) from
        ⟨hNR, by exact_mod_cast hn⟩)]
      have := causalAmplitude_eq_tsum_seed (Nat.pos_of_ne_zero (by omega)) hn0 (N := N)
      rw [causalAmplitude] at this
      rw [mul_assoc, this]
      simp only [F, if_pos hn]
      rw [tsum_mul_left, ← mul_assoc, mul_comm (((ArithmeticFunction.moebius n : ℤ) : ℝ)), mul_assoc,
        ← tsum_mul_left]
    · rw [causalMobiusThetaTerm, Set.indicator_of_notMem (fun h => hn (by exact_mod_cast h.2))]
      simp [F, hn]
  have hfib := hFs.hasSum.tsum_fiberwise (fun nm : ℕ × ℕ => nm.1 * nm.2)
  have hfiber : ∀ r : ℕ, ∑' b : (fun nm : ℕ × ℕ => nm.1 * nm.2) ⁻¹' {r}, F b =
      -(if N < r then thetaCuspSeed (r / N) * truncMoebiusDivisorSum N r else 0) := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [if_neg (by omega), neg_zero, tsum_subtype]
      refine (tsum_congr fun b => ?_).trans tsum_zero
      by_cases hmem : b ∈ (fun nm : ℕ × ℕ => nm.1 * nm.2) ⁻¹' {0}
      · rw [Set.indicator_of_mem hmem]
        have hb : b.1 * b.2 = 0 := hmem
        simp only [F]
        split_ifs with h
        · rcases Nat.mul_eq_zero.1 hb with h1 | h2
          · omega
          · rw [h2]; simp [thetaCuspSeed_zero]
        · rfl
      · exact Set.indicator_of_notMem hmem _
    rw [tsum_mulFiber_eq_sum_divisors F hr.ne']
    have hdiv : ∀ n ∈ r.divisors, F (n, r / n) =
        if N < n then ((ArithmeticFunction.moebius n : ℤ) : ℝ) * thetaCuspSeed (r / N) else 0 := by
      intro n hn
      simp only [F]
      split_ifs
      · rw [show ((r / n : ℕ) : ℝ) * n = r by
          rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hn)]]
      · rfl
    rw [Finset.sum_congr rfl hdiv, ← Finset.sum_filter, ← Finset.sum_mul]
    by_cases hNr : N < r
    · rw [if_pos hNr]
      have hsplit := Finset.sum_filter_add_sum_filter_not r.divisors (fun n => N < n)
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
      rw [Sieve.sum_divisors_moebius_real, if_neg (by omega)] at hsplit
      have hD : truncMoebiusDivisorSum N r = ∑ n ∈ r.divisors.filter (fun n => ¬ N < n),
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
        rw [truncMoebiusDivisorSum_eq_sum_divisors_filter N hr.ne']; congr 1; ext d; simp [not_lt]
      rw [hD]
      have : ∑ n ∈ r.divisors.filter (fun n => N < n), ((ArithmeticFunction.moebius n : ℤ) : ℝ) =
          -∑ n ∈ r.divisors.filter (fun n => ¬ N < n), ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
        linarith
      rw [this]; ring
    · rw [if_neg hNr, neg_zero]
      rw [Finset.filter_false_of_mem fun n hn h => hNr (lt_of_lt_of_le h (Nat.divisor_le hn))]
      simp
  rw [funext hfiber] at hfib
  rw [causalMobiusThetaTail, tsum_congr hterm, tsum_mul_left,
    ← hFs.tsum_prod' fun n => hFs.prod_factor n, hfib.tsum_eq.symm, tsum_neg]
  ring

/-! ## Summability of the seed samples -/

theorem abs_thetaCuspSeed_natCast_div_le {Cg : ℝ}
    (hCg : ∀ x : ℝ, 0 < x → |thetaCuspSeed x| ≤ Cg * (x ^ 3)⁻¹) {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    |thetaCuspSeed (r / N)| ≤ Cg * N ^ 3 * ((r : ℝ) ^ 3)⁻¹ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [thetaCuspSeed_zero]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  refine (hCg _ (div_pos hrR hNR)).trans (le_of_eq ?_)
  field_simp

theorem summable_abs_thetaCuspSeed_div {N : ℕ} (hN : 1 ≤ N) :
    Summable fun r : ℕ => |thetaCuspSeed (r / N)| := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_abs_thetaCuspSeed_le_inv_cube
  refine Summable.of_nonneg_of_le (fun r => abs_nonneg _) (abs_thetaCuspSeed_natCast_div_le hCg hN)
    ((Real.summable_nat_pow_inv.2 (by norm_num)).mul_left _)

theorem summable_thetaCuspSeed_div {N : ℕ} (hN : 1 ≤ N) :
    Summable fun r : ℕ => thetaCuspSeed (r / N) :=
  (summable_abs_thetaCuspSeed_div hN).of_abs

theorem summable_natCast_mul_abs_thetaCuspSeed_div {N : ℕ} (hN : 1 ≤ N) :
    Summable fun r : ℕ => (r : ℝ) * |thetaCuspSeed (r / N)| := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_abs_thetaCuspSeed_le_inv_cube
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
    ((Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2)).mul_left (Cg * N ^ 3))
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  calc (r : ℝ) * |thetaCuspSeed (r / N)| ≤ r * (Cg * N ^ 3 * ((r : ℝ) ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left (abs_thetaCuspSeed_natCast_div_le hCg hN r) hrR.le
    _ = Cg * N ^ 3 * ((r : ℝ) ^ 2)⁻¹ := by field_simp

theorem summable_bounded_mul_thetaCuspSeed_div {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℝ} {A : ℝ}
    (ha : ∀ r, |a r| ≤ A) : Summable fun r : ℕ => thetaCuspSeed (r / N) * a r :=
  Summable.of_norm_bounded ((summable_abs_thetaCuspSeed_div hN).mul_right A) fun r => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (ha r) (abs_nonneg _)

theorem summable_bounded_mul_thetaCuspSeed_succ_div {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℝ} {A : ℝ}
    (ha : ∀ r, |a r| ≤ A) : Summable fun r : ℕ => thetaCuspSeed (((r : ℝ) + 1) / N) * a r := by
  have h := (summable_nat_add_iff 1).2 (summable_abs_thetaCuspSeed_div hN)
  refine Summable.of_norm_bounded (h.mul_right A) fun r => ?_
  rw [Real.norm_eq_abs, abs_mul]
  push_cast
  exact mul_le_mul_of_nonneg_left (ha r) (abs_nonneg _)

/-! ## (13) The lattice zero-mean law of the seed -/

theorem exp_log_div_two_eq_sqrt {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

theorem thetaCuspFullSource_log_eq {N : ℕ} (hN : 1 ≤ N) :
    thetaCuspFullSource (Real.log N) = Real.sqrt N * ∑' m : ℕ, thetaCuspSeed (m * N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [thetaCuspFullSource, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [thetaCuspSourceTerm, Real.exp_log hNR, exp_log_div_two_eq_sqrt hNR]

/-- `Σ_r g(r/N) = √N k(log N)`: the completed theta reflection `k(−x) = k(x)`. -/
theorem tsum_thetaCuspSeed_div_eq {N : ℕ} (hN : 1 ≤ N) :
    ∑' r : ℕ, thetaCuspSeed (r / N) = Real.sqrt N * thetaCuspFullSource (Real.log N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have h := thetaCuspFullSource_neg (Real.log N)
  rw [thetaCuspFullSource] at h
  have hterm : ∀ m : ℕ, thetaCuspSourceTerm (-Real.log N) m =
      (Real.sqrt N)⁻¹ * thetaCuspSeed (m / N) := by
    intro m
    rw [thetaCuspSourceTerm, Real.exp_neg, Real.exp_log hNR, neg_div, Real.exp_neg,
      exp_log_div_two_eq_sqrt hNR, div_eq_mul_inv]
  rw [tsum_congr hterm, tsum_mul_left] at h
  rw [← h]
  field_simp

/-- **(13)** `Σ_{r≥1} g(r/N) = N Σ_{m≥1} g(mN)`. -/
theorem tsum_thetaCuspSeed_div_eq_lattice {N : ℕ} (hN : 1 ≤ N) :
    ∑' r : ℕ, thetaCuspSeed (r / N) = N * ∑' m : ℕ, thetaCuspSeed (m * N) := by
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [tsum_thetaCuspSeed_div_eq hN, thetaCuspFullSource_log_eq hN, ← mul_assoc,
    Real.mul_self_sqrt hNR]

/-! ## (12) Summation by parts across all physical cells -/

/-- **(12)** `B(N) = N^{−1/2}[g(1/N) − H_N Σ_r g_r + Σ_r (g_r − g_{r+1}) C_N(r)]`. -/
theorem causalMobiusThetaTail_natCast_eq_summation_by_parts {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N = (N : ℝ) ^ (-(1 / 2 : ℝ)) *
      (thetaCuspSeed (1 / N) - moebiusHarmonic N * ∑' r : ℕ, thetaCuspSeed (r / N) +
        ∑' r : ℕ, (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) * moebiusCell N r) := by
  set G : ℕ → ℝ := fun r => thetaCuspSeed (r / N) with hG
  set D : ℕ → ℝ := fun r => truncMoebiusDivisorSum N r with hD
  set C : ℕ → ℝ := fun r => moebiusCell N r with hC
  have hD_le : ∀ r, |D r| ≤ N := fun r => abs_truncMoebiusDivisorSum_le N r
  have hC_le : ∀ r, |C r| ≤ N := fun r => abs_moebiusCell_le N r
  have hC1_le : ∀ r, |C (r - 1)| ≤ N := fun r => abs_moebiusCell_le N (r - 1)
  have hG0 : G 0 = 0 := by simp [G, thetaCuspSeed_zero]
  have hGD : Summable fun r => G r * D r := summable_bounded_mul_thetaCuspSeed_div hN hD_le
  have hGC : Summable fun r => G r * C r := summable_bounded_mul_thetaCuspSeed_div hN hC_le
  have hGC1 : Summable fun r => G r * C (r - 1) := summable_bounded_mul_thetaCuspSeed_div hN hC1_le
  have hG1C : Summable fun r : ℕ => thetaCuspSeed (((r : ℝ) + 1) / N) * C r :=
    summable_bounded_mul_thetaCuspSeed_succ_div hN hC_le
  -- step 1: the initial cells contribute exactly `g(1/N)`
  have hsplit : ∀ r, G r * D r = (if N < r then G r * D r else 0) + (if r = 1 then G 1 else 0) := by
    intro r
    by_cases hr : N < r
    · rw [if_pos hr, if_neg (by omega), add_zero]
    · rw [if_neg hr, zero_add]
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · rw [hG0, zero_mul, if_neg (by omega)]
      · have := truncMoebiusDivisorSum_of_le hr0 (not_lt.1 hr)
        simp only [D, this]
        split_ifs with h1 <;> simp [h1]
  have htail : Summable fun r => if N < r then G r * D r else 0 :=
    Summable.of_norm_bounded hGD.norm fun r => by split_ifs <;> simp; positivity
  have h1 : ∑' r, G r * D r = (∑' r, if N < r then G r * D r else 0) + G 1 := by
    rw [tsum_congr hsplit, Summable.tsum_add htail (summable_of_ne_finset_zero (s := {1})
      (fun r hr => by rw [if_neg (by simpa using hr)])), tsum_ite_eq]
  -- step 2: summation by parts
  have hpoint : ∀ r, G r * D r = moebiusHarmonic N * G r - (G r * C r - G r * C (r - 1)) := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [hG0]; ring
    · simp only [D, C]
      rw [truncMoebiusDivisorSum_eq_harmonic_sub N hr0]
      ring
  have hshift : ∑' r, G r * C (r - 1) = ∑' r : ℕ, thetaCuspSeed (((r : ℝ) + 1) / N) * C r := by
    rw [hGC1.tsum_eq_zero_add, hG0, zero_mul, zero_add]
    refine tsum_congr fun r => ?_
    simp only [G, Nat.add_sub_cancel]
    push_cast
    rfl
  have h2 : ∑' r, G r * D r = moebiusHarmonic N * ∑' r, G r -
      ∑' r : ℕ, (G r - thetaCuspSeed (((r : ℝ) + 1) / N)) * C r := by
    rw [tsum_congr hpoint, Summable.tsum_sub ((summable_thetaCuspSeed_div hN).mul_left _)
      (hGC.sub hGC1), tsum_mul_left, Summable.tsum_sub hGC hGC1, hshift]
    congr 1
    rw [← Summable.tsum_sub hGC hG1C]
    exact tsum_congr fun r => by ring
  rw [causalMobiusThetaTail_natCast_eq hN]
  have h11 : (∑' r : ℕ, if N < r then thetaCuspSeed (r / N) * truncMoebiusDivisorSum N r else 0) =
      ∑' r, G r * D r - G 1 := by rw [h1]; ring
  rw [h11, h2]
  simp only [G, Nat.cast_one]
  ring

/-! ## (14)–(15) The smooth complete-cell wavelet -/

/-- **(14)** The smooth complete-cell wavelet `q_N(r) = r(r+1)(g(r/N) − g((r+1)/N))/√N`. -/
def thetaCellWavelet (N r : ℕ) : ℝ :=
  r * (r + 1) * (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) / Real.sqrt N

/-- **(14)** The scalar defect `e_N = g(1/N)/√N − H_N k(log N)`. -/
def thetaCellDefect (N : ℕ) : ℝ :=
  thetaCuspSeed (1 / N) / Real.sqrt N - moebiusHarmonic N * thetaCuspFullSource (Real.log N)

theorem thetaCellWavelet_mul_cellWeight (N j : ℕ) :
    thetaCellWavelet N (j + 1) * DeletionResidueMartingale.cellWeight j =
      (thetaCuspSeed (((j + 1 : ℕ) : ℝ) / N) - thetaCuspSeed ((((j + 1 : ℕ) : ℝ) + 1) / N)) /
        Real.sqrt N := by
  rw [thetaCellWavelet, DeletionResidueMartingale.cellWeight]
  have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **(15)**, cell form: `B(N) = Σ_{r≥1} C_N(r) q_N(r)/(r(r+1)) + e_N`. -/
theorem causalMobiusThetaTail_natCast_eq_cell_pairing {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N = (∑' j : ℕ, moebiusCell N (j + 1) * thetaCellWavelet N (j + 1) *
      DeletionResidueMartingale.cellWeight j) + thetaCellDefect N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hsum : Summable fun r : ℕ =>
      (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) * moebiusCell N r :=
    by
      have hC_le : ∀ r, |moebiusCell N r| ≤ N := fun r => abs_moebiusCell_le N r
      simpa only [sub_mul] using (summable_bounded_mul_thetaCuspSeed_div hN hC_le).sub
        (summable_bounded_mul_thetaCuspSeed_succ_div hN hC_le)
  have hcell : (∑' j : ℕ, moebiusCell N (j + 1) * thetaCellWavelet N (j + 1) *
      DeletionResidueMartingale.cellWeight j) = (Real.sqrt N)⁻¹ *
        ∑' r : ℕ, (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) * moebiusCell N r := by
    rw [hsum.tsum_eq_zero_add, moebiusCell_zero, mul_zero, zero_add, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [mul_assoc, thetaCellWavelet_mul_cellWeight]
    push_cast
    field_simp
  rw [causalMobiusThetaTail_natCast_eq_summation_by_parts hN, hcell, thetaCellDefect,
    tsum_thetaCuspSeed_div_eq hN, natCast_rpow_neg_half_eq_inv_sqrt]
  field_simp
  ring

end

end RHTower
