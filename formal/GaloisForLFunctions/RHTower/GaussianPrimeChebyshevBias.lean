import GaloisForLFunctions.RHTower.GaussianGapSignAbscissa
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Chebyshev's bias for the Gaussian prime sum

Let `C(y) = ∫₁^∞ u^{-1/2} e^{-yu²} du` and split the central Gaussian prime mass
`P(y) = Σ Λ(n) n^{-1/2} e^{-yn²}` into its primes and its higher prime powers,

`P(y) = Π(y) + D(y)`,  `Π(y) = Σ_p (log p) p^{-1/2} e^{-yp²}`.

* **Gaussian quartic Mertens law** (`abs_gaussianQuarticMertensMass_sub_log_le`).  The mass
  `Q(y) = Σ Λ(m) m^{-1} e^{-ym⁴}` satisfies `|Q(y) − ¼ log(1/y)| ≤ K` on `(0, 1]`.  The lower bound
  truncates at `N = ⌊y^{-1/4}⌋` and uses `e^{-v} ≥ 1 − v` with Chebyshev's `ψ(N) = O(N)`; the
  upper bound splits the tail into dyadic blocks `(N2^k, N2^{k+1}]`, each of Mertens mass
  `log 2 + O(1)` and Gaussian weight `≤ e^{-k}`.
* **Prime-power sandwich** (`gaussianQuarticMertensMass_le_primePowerDefect`,
  `primePowerDefect_le_two_mul_gaussianQuarticMertensMass`).  `Q ≤ D ≤ 2Q`: the squares `m²` of
  prime powers carry exactly `Q`, and every odd prime power `p^{2j+1}` (`j ≥ 1`) is the image of
  `m = p^j` under the injection `m ↦ minFac(m)·m²`, with a smaller term.
* **Gaussian Chebyshev conjecture** (`riemannHypothesis_iff_tendsto_gaussianPrimeOnlyGap_atBot`).
  RH holds iff `Π(y) − C(y) → −∞` as `y → 0⁺`.  Under RH, `Π(y) − C(y) ≤ K − ¼ log(1/y)`; conversely
  an eventual upper bound for `Π − C` bounds `P − C` by `O(log(1/y))`, and the growth law gives RH.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The masses -/

/-- The Gaussian prime mass at the centre: `Π(y) = Σ_p (log p) p^{-1/2} e^{-yp²}`. -/
def gaussianCentralPrimeOnlyMass (y : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2))
    else 0

/-- The higher-prime-power part of the central Gaussian prime mass. -/
def gaussianCentralPrimePowerDefect (y : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then 0 else Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2))

/-- The Gaussian quartic Mertens mass `Q(y) = Σ Λ(m) m^{-1} e^{-ym⁴}`. -/
def gaussianQuarticMertensMass (y : ℝ) : ℝ :=
  ∑' m : ℕ, Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4))

theorem vonMangoldt_le_self (n : ℕ) : Λ n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (ArithmeticFunction.vonMangoldt_le_log).trans
      (Real.log_le_self (by exact_mod_cast hn.le))

theorem exp_neg_mul_pow_le_geometric {y : ℝ} (hy : 0 < y) (n k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-(y * (n : ℝ) ^ k)) ≤ Real.exp (-y) ^ n := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_pow (show k ≠ 0 by omega), mul_zero, neg_zero, zero_mul]
    exact le_refl _
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ≤ (n : ℝ) ^ k := by
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ k := pow_le_pow_right₀ hn1 hk
    nlinarith

theorem gaussianCentralTerm_nonneg (y : ℝ) (n : ℕ) :
    0 ≤ Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2)) :=
  mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (Real.exp_pos _).le

theorem gaussianCentralTerm_le {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2)) ≤
      (n : ℝ) ^ 1 * Real.exp (-y) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hr : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    have he := exp_neg_mul_pow_le_geometric hy n 2 (by norm_num)
    have hΛ := vonMangoldt_le_self n
    rw [pow_one]
    calc Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2))
        ≤ (n : ℝ) * 1 * Real.exp (-y) ^ n := by
          gcongr
      _ = (n : ℝ) * Real.exp (-y) ^ n := by ring

theorem summable_gaussianCentralTerm {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2)) := by
  have hr : ‖Real.exp (-y)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  exact Summable.of_nonneg_of_le (gaussianCentralTerm_nonneg y) (gaussianCentralTerm_le hy)
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr)

theorem quarticTerm_nonneg (y : ℝ) (m : ℕ) :
    0 ≤ Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) :=
  mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (inv_nonneg.2 (Nat.cast_nonneg m))) (Real.exp_pos _).le

theorem summable_quarticTerm {y : ℝ} (hy : 0 < y) :
    Summable fun m : ℕ => Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) := by
  have hr0 : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
  have hr1 : Real.exp (-y) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  refine Summable.of_nonneg_of_le (quarticTerm_nonneg y) (fun m => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hΛ : Λ m * (m : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hm0]
      exact vonMangoldt_le_self m
    have he := exp_neg_mul_pow_le_geometric hy m 4 (by norm_num)
    calc Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) ≤ 1 * Real.exp (-y) ^ m := by
          gcongr
      _ = _ := one_mul _

/-! ## The Gaussian quartic Mertens law -/

/-- Mertens' theorem on `Ioc 0 n`. -/
theorem abs_sum_Ioc_vonMangoldt_div_sub_log_le {n : ℕ} (hn : 1 ≤ n) :
    |(∑ d ∈ Finset.Ioc 0 n, Λ d * (d : ℝ)⁻¹) - Real.log n| ≤ Real.log 4 + 4 := by
  have h := Mertens.mertens_first n hn
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc] at h
  simpa only [div_eq_mul_inv] using h

/-- Chebyshev on `Ioc 0 n`: `ψ(n) ≤ (log 4 + 4) n`. -/
theorem sum_Ioc_vonMangoldt_le (n : ℕ) :
    ∑ d ∈ Finset.Ioc 0 n, Λ d ≤ (Real.log 4 + 4) * n := by
  have h := Mertens.sum_vonMangoldt_Icc_le n
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rwa [hIcc] at h

/-- The truncation point `N = ⌊y^{-1/4}⌋` of the quartic Gaussian. -/
theorem quarticTruncation_facts {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    1 ≤ ⌊y ^ (-(1 / 4 : ℝ))⌋₊ ∧
      y * ((⌊y ^ (-(1 / 4 : ℝ))⌋₊ : ℕ) : ℝ) ^ 4 ≤ 1 ∧
      1 / 16 ≤ y * ((⌊y ^ (-(1 / 4 : ℝ))⌋₊ : ℕ) : ℝ) ^ 4 ∧
      Real.log (1 / y) / 4 - Real.log 2 ≤ Real.log ((⌊y ^ (-(1 / 4 : ℝ))⌋₊ : ℕ) : ℝ) ∧
      Real.log ((⌊y ^ (-(1 / 4 : ℝ))⌋₊ : ℕ) : ℝ) ≤ Real.log (1 / y) / 4 := by
  set X : ℝ := y ^ (-(1 / 4 : ℝ)) with hX
  set N : ℕ := ⌊X⌋₊ with hN
  have hX1 : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by norm_num)
  have hX0 : 0 < X := by linarith
  have hX4 : y * X ^ 4 = 1 := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hy.ne']
  have hNle : (N : ℝ) ≤ X := Nat.floor_le hX0.le
  have hNlt : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
  have hN1 : 1 ≤ N := by
    rw [hN]; exact Nat.le_floor (by simpa using hX1)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hX2N : X ≤ 2 * N := by linarith
  have hlogX : Real.log X = Real.log (1 / y) / 4 := by
    have hinv : Real.log (1 / y) = -Real.log y := by rw [one_div, Real.log_inv]
    rw [hX, Real.log_rpow hy, hinv]; ring
  refine ⟨hN1, ?_, ?_, ?_, ?_⟩
  · have : (N : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ hN0.le hNle 4
    nlinarith
  · have h1 : X ^ 4 ≤ (2 * N) ^ 4 := pow_le_pow_left₀ hX0.le hX2N 4
    nlinarith
  · have h1 : Real.log (X / 2) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hX0.ne' two_ne_zero, hlogX] at h1
    exact h1
  · rw [← hlogX]
    exact Real.log_le_log hN0 hNle

/-- **Lower Gaussian quartic Mertens bound**: `Q(y) ≥ ¼ log(1/y) − log 2 − 2(log 4 + 4)`. -/
theorem gaussianQuarticMertensMass_ge {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.log (1 / y) / 4 - Real.log 2 - 2 * (Real.log 4 + 4) ≤ gaussianQuarticMertensMass y := by
  obtain ⟨hN1, hyN, -, hlogN, -⟩ := quarticTruncation_facts hy hy1
  set N : ℕ := ⌊y ^ (-(1 / 4 : ℝ))⌋₊ with hN
  set c : ℝ := Real.log 4 + 4 with hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hfin : ∑ m ∈ Finset.Ioc 0 N, Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) ≤
      gaussianQuarticMertensMass y :=
    (summable_quarticTerm hy).sum_le_tsum _ (fun m _ => quarticTerm_nonneg y m)
  have hterm : ∀ m ∈ Finset.Ioc 0 N, Λ m * (m : ℝ)⁻¹ - y * (Λ m * (N : ℝ) ^ 3) ≤
      Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm.2
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    have he : 1 - y * (m : ℝ) ^ 4 ≤ Real.exp (-(y * (m : ℝ) ^ 4)) := by
      linarith [Real.add_one_le_exp (-(y * (m : ℝ) ^ 4))]
    have hm3 : (m : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hm0.le hmN 3
    have hkey : Λ m * (m : ℝ)⁻¹ * (1 - y * (m : ℝ) ^ 4) = Λ m * (m : ℝ)⁻¹ - y * (Λ m * (m : ℝ) ^ 3) := by
      field_simp
    calc Λ m * (m : ℝ)⁻¹ - y * (Λ m * (N : ℝ) ^ 3)
        ≤ Λ m * (m : ℝ)⁻¹ - y * (Λ m * (m : ℝ) ^ 3) := by
          have : y * (Λ m * (m : ℝ) ^ 3) ≤ y * (Λ m * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm3 hΛ) hy.le
          linarith
      _ = Λ m * (m : ℝ)⁻¹ * (1 - y * (m : ℝ) ^ 4) := hkey.symm
      _ ≤ Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hΛ (inv_nonneg.2 hm0.le))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hmert := (abs_le.1 (abs_sum_Ioc_vonMangoldt_div_sub_log_le hN1)).1
  have hcheb := sum_Ioc_vonMangoldt_le N
  have hc0 : 0 ≤ c := by rw [hc]; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hψ : y * ((∑ m ∈ Finset.Ioc 0 N, Λ m) * (N : ℝ) ^ 3) ≤ c := by
    calc y * ((∑ m ∈ Finset.Ioc 0 N, Λ m) * (N : ℝ) ^ 3) ≤ y * ((c * N) * (N : ℝ) ^ 3) := by
          gcongr
      _ = c * (y * (N : ℝ) ^ 4) := by ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hyN hc0
      _ = c := mul_one c
  linarith

/-- The dyadic decomposition `Σ_{(0, N2^K]} = Σ_{(0,N]} + Σ_{k<K} Σ_{(N2^k, N2^{k+1}]}`. -/
theorem sum_Ioc_dyadic (f : ℕ → ℝ) (N K : ℕ) :
    ∑ i ∈ Finset.Ioc 0 (N * 2 ^ K), f i = ∑ i ∈ Finset.Ioc 0 N, f i +
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ioc (N * 2 ^ k) (N * 2 ^ (k + 1)), f i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih,
      Finset.sum_Ioc_consecutive f (Nat.zero_le _)
        (Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)))]

/-- Mertens on a dyadic block: `Σ_{(a, 2a]} Λ(m)/m ≤ log 2 + 2(log 4 + 4)`. -/
theorem sum_Ioc_vonMangoldt_div_dyadic_le {a : ℕ} (ha : 1 ≤ a) :
    ∑ d ∈ Finset.Ioc a (2 * a), Λ d * (d : ℝ)⁻¹ ≤ Real.log 2 + 2 * (Real.log 4 + 4) := by
  have h2a : 1 ≤ 2 * a := by omega
  have hsplit := Finset.sum_Ioc_consecutive (fun d => Λ d * (d : ℝ)⁻¹) (Nat.zero_le a)
    (show a ≤ 2 * a by omega)
  have hA := (abs_le.1 (abs_sum_Ioc_vonMangoldt_div_sub_log_le ha)).1
  have hB := (abs_le.1 (abs_sum_Ioc_vonMangoldt_div_sub_log_le h2a)).2
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hlog : Real.log ((2 * a : ℕ) : ℝ) = Real.log 2 + Real.log a := by
    push_cast
    rw [Real.log_mul two_ne_zero ha0.ne']
  rw [hlog] at hB
  linarith

/-- `e^{-k}`-decay of the dyadic Gaussian weights: `16^k/16 ≥ k`. -/
theorem nat_le_sixteen_pow_div (k : ℕ) : (k : ℝ) ≤ 16 ^ k / 16 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h : j + 1 ≤ 16 ^ j := Nat.lt_pow_self (by norm_num)
    have h' : ((j + 1 : ℕ) : ℝ) ≤ (16 : ℝ) ^ j := by exact_mod_cast h
    rw [pow_succ]
    push_cast at h' ⊢
    linarith

/-- **Upper Gaussian quartic Mertens bound**:
`Q(y) ≤ ¼ log(1/y) + (log 4 + 4) + 2(log 2 + 2(log 4 + 4))`. -/
theorem gaussianQuarticMertensMass_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    gaussianQuarticMertensMass y ≤
      Real.log (1 / y) / 4 + (Real.log 4 + 4) + 2 * (Real.log 2 + 2 * (Real.log 4 + 4)) := by
  obtain ⟨hN1, -, hyN16, -, hlogN⟩ := quarticTruncation_facts hy hy1
  set N : ℕ := ⌊y ^ (-(1 / 4 : ℝ))⌋₊ with hN
  set c : ℝ := Real.log 4 + 4 with hc
  set B : ℝ := Real.log 2 + 2 * c with hB
  have hB0 : 0 ≤ B := by
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    rw [hB, hc]; linarith
  set f : ℕ → ℝ := fun m => Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) with hf
  have hf0 : ∀ m, 0 ≤ f m := quarticTerm_nonneg y
  have hfle : ∀ m, f m ≤ Λ m * (m : ℝ)⁻¹ := fun m => by
    have := Real.exp_le_one_iff.2 (show -(y * (m : ℝ) ^ 4) ≤ 0 by
      have : 0 ≤ y * (m : ℝ) ^ 4 := by positivity
      linarith)
    have h0 : 0 ≤ Λ m * (m : ℝ)⁻¹ :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (inv_nonneg.2 (Nat.cast_nonneg m))
    exact mul_le_of_le_one_right h0 this
  -- the head
  have hhead : ∑ i ∈ Finset.Ioc 0 N, f i ≤ Real.log (1 / y) / 4 + c := by
    have h := (abs_le.1 (abs_sum_Ioc_vonMangoldt_div_sub_log_le hN1)).2
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.Ioc 0 N) => hfle i
    linarith
  -- the dyadic blocks
  have hblock : ∀ k : ℕ, ∑ i ∈ Finset.Ioc (N * 2 ^ k) (N * 2 ^ (k + 1)), f i ≤
      B * Real.exp (-1) ^ k := by
    intro k
    have ha : 1 ≤ N * 2 ^ k := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hw : ∀ i ∈ Finset.Ioc (N * 2 ^ k) (N * 2 ^ (k + 1)),
        f i ≤ Λ i * (i : ℝ)⁻¹ * Real.exp (-1) ^ k := by
      intro i hi
      rw [Finset.mem_Ioc] at hi
      have hai : ((N * 2 ^ k : ℕ) : ℝ) ≤ i := by exact_mod_cast hi.1.le
      have ha0 : (0 : ℝ) ≤ ((N * 2 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpow : ((N * 2 ^ k : ℕ) : ℝ) ^ 4 ≤ (i : ℝ) ^ 4 := pow_le_pow_left₀ ha0 hai 4
      have hval : y * ((N * 2 ^ k : ℕ) : ℝ) ^ 4 = y * (N : ℝ) ^ 4 * 16 ^ k := by
        have h16 : ((2 : ℝ) ^ k) ^ 4 = 16 ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        push_cast
        rw [mul_pow, h16]; ring
      have hk := nat_le_sixteen_pow_div k
      have h16 : (0 : ℝ) ≤ 16 ^ k := by positivity
      have hexp : -(y * (i : ℝ) ^ 4) ≤ -(k : ℝ) := by
        have : (k : ℝ) ≤ y * ((N * 2 ^ k : ℕ) : ℝ) ^ 4 := by
          rw [hval]
          nlinarith
        nlinarith
      have he : Real.exp (-(y * (i : ℝ) ^ 4)) ≤ Real.exp (-1) ^ k := by
        rw [← Real.exp_nat_mul, show (k : ℝ) * -1 = -(k : ℝ) by ring]
        exact Real.exp_le_exp.2 hexp
      exact mul_le_mul_of_nonneg_left he
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (inv_nonneg.2 (Nat.cast_nonneg i)))
    calc ∑ i ∈ Finset.Ioc (N * 2 ^ k) (N * 2 ^ (k + 1)), f i
        ≤ ∑ i ∈ Finset.Ioc (N * 2 ^ k) (N * 2 ^ (k + 1)), Λ i * (i : ℝ)⁻¹ * Real.exp (-1) ^ k :=
          Finset.sum_le_sum hw
      _ = (∑ i ∈ Finset.Ioc (N * 2 ^ k) (2 * (N * 2 ^ k)), Λ i * (i : ℝ)⁻¹) *
            Real.exp (-1) ^ k := by
          rw [← Finset.sum_mul, show N * 2 ^ (k + 1) = 2 * (N * 2 ^ k) by ring]
      _ ≤ B * Real.exp (-1) ^ k :=
          mul_le_mul_of_nonneg_right (sum_Ioc_vonMangoldt_div_dyadic_le ha) (by positivity)
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hgeom : ∀ K : ℕ, ∑ k ∈ Finset.range K, Real.exp (-1) ^ k ≤ 2 := by
    intro K
    have hsum := summable_geometric_of_lt_one hr0 (by linarith)
    calc ∑ k ∈ Finset.range K, Real.exp (-1) ^ k ≤ ∑' k : ℕ, Real.exp (-1) ^ k :=
          hsum.sum_le_tsum _ (fun k _ => pow_nonneg hr0 k)
      _ = (1 - Real.exp (-1))⁻¹ := tsum_geometric_of_lt_one hr0 (by linarith)
      _ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
  refine Real.tsum_le_of_sum_range_le hf0 (fun M => ?_)
  have hMK : M ≤ N * 2 ^ M + 1 := by
    have h1 : M < 2 ^ M := Nat.lt_two_pow_self
    have h2 : 2 ^ M ≤ N * 2 ^ M := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hsub : Finset.range M ⊆ insert 0 (Finset.Ioc 0 (N * 2 ^ M)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hf00 : f 0 = 0 := by simp [hf]
  calc ∑ i ∈ Finset.range M, f i ≤ ∑ i ∈ insert 0 (Finset.Ioc 0 (N * 2 ^ M)), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf0 i)
    _ = ∑ i ∈ Finset.Ioc 0 (N * 2 ^ M), f i := by
        rw [Finset.sum_insert (by simp), hf00, zero_add]
    _ = ∑ i ∈ Finset.Ioc 0 N, f i +
          ∑ k ∈ Finset.range M, ∑ i ∈ Finset.Ioc (N * 2 ^ k) (N * 2 ^ (k + 1)), f i :=
        sum_Ioc_dyadic f N M
    _ ≤ (Real.log (1 / y) / 4 + c) + ∑ k ∈ Finset.range M, B * Real.exp (-1) ^ k :=
        add_le_add hhead (Finset.sum_le_sum fun k _ => hblock k)
    _ ≤ (Real.log (1 / y) / 4 + c) + B * 2 := by
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (hgeom M) hB0
        linarith
    _ = _ := by rw [hB]; ring

/-- **Gaussian quartic Mertens law**: `|Q(y) − ¼ log(1/y)| ≤ 2(log 2 + 3(log 4 + 4))` on
`(0, 1]`. -/
theorem abs_gaussianQuarticMertensMass_sub_log_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    |gaussianQuarticMertensMass y - Real.log (1 / y) / 4| ≤
      2 * (Real.log 2 + 3 * (Real.log 4 + 4)) := by
  have h1 := gaussianQuarticMertensMass_ge hy hy1
  have h2 := gaussianQuarticMertensMass_le hy hy1
  have hl2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have hl4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-! ## The prime-power sandwich `Q ≤ D ≤ 2Q` -/

/-- The prime summand of the central Gaussian mass. -/
def primeOnlyTerm (y : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2)) else 0

/-- The higher-prime-power summand of the central Gaussian mass. -/
def primePowerDefectTerm (y : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then 0 else Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2))

theorem gaussianCentralTerm_eq (y : ℝ) (n : ℕ) :
    Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2)) =
      primeOnlyTerm y n + primePowerDefectTerm y n := by
  unfold primeOnlyTerm primePowerDefectTerm
  by_cases hn : n.Prime
  · rw [if_pos hn, if_pos hn, ArithmeticFunction.vonMangoldt_apply_prime hn, add_zero]
  · rw [if_neg hn, if_neg hn, zero_add]

theorem primeOnlyTerm_nonneg (y : ℝ) (n : ℕ) : 0 ≤ primeOnlyTerm y n := by
  unfold primeOnlyTerm
  split_ifs with hn
  · have := gaussianCentralTerm_nonneg y n
    rwa [ArithmeticFunction.vonMangoldt_apply_prime hn] at this
  · exact le_rfl

theorem primePowerDefectTerm_nonneg (y : ℝ) (n : ℕ) : 0 ≤ primePowerDefectTerm y n := by
  unfold primePowerDefectTerm
  split_ifs
  · exact le_rfl
  · exact gaussianCentralTerm_nonneg y n

theorem primePowerDefectTerm_le (y : ℝ) (n : ℕ) :
    primePowerDefectTerm y n ≤ Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y * (n : ℝ) ^ 2)) := by
  rw [gaussianCentralTerm_eq]
  linarith [primeOnlyTerm_nonneg y n]

theorem summable_primeOnlyTerm {y : ℝ} (hy : 0 < y) : Summable (primeOnlyTerm y) :=
  Summable.of_nonneg_of_le (primeOnlyTerm_nonneg y)
    (fun n => by rw [gaussianCentralTerm_eq]; linarith [primePowerDefectTerm_nonneg y n])
    (summable_gaussianCentralTerm hy)

theorem summable_primePowerDefectTerm {y : ℝ} (hy : 0 < y) : Summable (primePowerDefectTerm y) :=
  Summable.of_nonneg_of_le (primePowerDefectTerm_nonneg y) (primePowerDefectTerm_le y)
    (summable_gaussianCentralTerm hy)

/-- `P(y) = Π(y) + D(y)`. -/
theorem gaussianWeightedPrimeMass_half_eq {y : ℝ} (hy : 0 < y) :
    gaussianWeightedPrimeMass (1 / 2) y =
      gaussianCentralPrimeOnlyMass y + gaussianCentralPrimePowerDefect y := by
  have h := (summable_primeOnlyTerm hy).tsum_add (summable_primePowerDefectTerm hy)
  rw [gaussianWeightedPrimeMass, gaussianCentralPrimeOnlyMass, gaussianCentralPrimePowerDefect]
  change _ = (∑' n, primeOnlyTerm y n) + ∑' n, primePowerDefectTerm y n
  rw [← h]
  exact tsum_congr fun n => gaussianCentralTerm_eq y n

theorem not_prime_sq (m : ℕ) : ¬ (m ^ 2).Prime := by
  rw [sq]
  by_cases hm : m = 1
  · subst hm; exact Nat.not_prime_one
  · exact Nat.not_prime_mul hm hm

/-- The defect term at a square is the quartic Mertens term. -/
theorem primePowerDefectTerm_sq (y : ℝ) (m : ℕ) :
    primePowerDefectTerm y (m ^ 2) = Λ m * (m : ℝ)⁻¹ * Real.exp (-(y * (m : ℝ) ^ 4)) := by
  unfold primePowerDefectTerm
  rw [if_neg (not_prime_sq m), ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]
  have hr : ((m ^ 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (m : ℝ)⁻¹ := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    norm_num
    exact Real.rpow_neg_one _
  rw [hr]
  congr 2
  push_cast
  ring

/-- `m ↦ minFac(m)·m²` is injective. -/
theorem minFac_mul_sq_injective : Function.Injective (fun m : ℕ => m.minFac * m ^ 2) := by
  intro a b hab
  simp only at hab
  have big : ∀ c : ℕ, 2 ≤ c → 8 ≤ c.minFac * c ^ 2 := by
    intro c hc
    have h1 := (Nat.minFac_prime (show c ≠ 1 by omega)).two_le
    have h2 : 4 ≤ c ^ 2 := by nlinarith
    nlinarith
  rcases Nat.lt_or_ge a 2 with ha | ha <;> rcases Nat.lt_or_ge b 2 with hb | hb
  · interval_cases a <;> interval_cases b <;> simp_all
  · have h8 := big b hb
    rw [← hab] at h8
    interval_cases a <;> simp at h8
  · have h8 := big a ha
    rw [hab] at h8
    interval_cases b <;> simp at h8
  · have hp := Nat.minFac_prime (show a ≠ 1 by omega)
    have hq := Nat.minFac_prime (show b ≠ 1 by omega)
    have hpq : a.minFac = b.minFac := by
      have h1 : a.minFac ∣ b.minFac * b ^ 2 := hab ▸ dvd_mul_right _ _
      have h2 : b.minFac ∣ a.minFac * a ^ 2 := hab.symm ▸ dvd_mul_right _ _
      rcases hp.dvd_mul.1 h1 with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).1 h
      · have hle1 : b.minFac ≤ a.minFac := Nat.minFac_le_of_dvd hp.two_le (hp.dvd_of_dvd_pow h)
        rcases hq.dvd_mul.1 h2 with h' | h'
        · exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 h').symm
        · have hle2 : a.minFac ≤ b.minFac :=
            Nat.minFac_le_of_dvd hq.two_le (hq.dvd_of_dvd_pow h')
          omega
    rw [hpq] at hab
    exact Nat.pow_left_injective two_ne_zero (Nat.eq_of_mul_eq_mul_left hq.pos hab)

/-- The odd higher prime power `minFac(m)·m²` carries at most the square term of `m`. -/
theorem primePowerDefectTerm_minFac_mul_sq_le {y : ℝ} (hy : 0 < y) (m : ℕ) :
    primePowerDefectTerm y (m.minFac * m ^ 2) ≤ primePowerDefectTerm y (m ^ 2) := by
  refine (primePowerDefectTerm_le y _).trans ?_
  by_cases hΛ : Λ (m.minFac * m ^ 2) = 0
  · rw [hΛ, zero_mul, zero_mul]
    exact primePowerDefectTerm_nonneg y _
  have hpp : IsPrimePow (m.minFac * m ^ 2) := by
    by_contra h
    exact hΛ (ArithmeticFunction.vonMangoldt_eq_zero_iff.2 h)
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp only [Nat.minFac_one, one_pow, mul_one] at hpp
    exact not_isPrimePow_one hpp
  have hm : IsPrimePow m := hpp.dvd (Dvd.dvd.mul_left (dvd_pow_self m two_ne_zero) _) hm1
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff m).1 hm
  rw [Nat.Prime.pow_minFac hp hj.ne', primePowerDefectTerm_sq, ← pow_mul, ← pow_succ',
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow : ((p ^ j : ℕ) : ℝ) ^ 2 ≤ ((p ^ (j * 2 + 1) : ℕ) : ℝ) := by
    push_cast
    rw [← pow_mul, pow_succ]
    nlinarith [pow_pos hp0 (j * 2)]
  have hpj : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos j
  have hpos : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) ^ 2 := pow_pos hpj 2
  have hr : ((p ^ (j * 2 + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (((p ^ j : ℕ) : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hpow (by norm_num)
  have hr' : (((p ^ j : ℕ) : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) = ((p ^ j : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
    exact Real.rpow_neg_one _
  have he : Real.exp (-(y * ((p ^ (j * 2 + 1) : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (-(y * ((p ^ j : ℕ) : ℝ) ^ 4)) := by
    apply Real.exp_le_exp.2
    have h4 : ((p ^ j : ℕ) : ℝ) ^ 4 = (((p ^ j : ℕ) : ℝ) ^ 2) ^ 2 := by ring
    rw [h4]
    have := pow_le_pow_left₀ hpos.le hpow 2
    nlinarith
  rw [← hr']
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := p)
  calc Λ p * ((p ^ (j * 2 + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(y * ((p ^ (j * 2 + 1) : ℕ) : ℝ) ^ 2))
      ≤ Λ p * (((p ^ j : ℕ) : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(y * ((p ^ j : ℕ) : ℝ) ^ 4)) := by
        gcongr
    _ = _ := rfl

/-- **Lower sandwich** `Q(y) ≤ D(y)`: the squares of prime powers carry exactly `Q`. -/
theorem gaussianQuarticMertensMass_le_primePowerDefect {y : ℝ} (hy : 0 < y) :
    gaussianQuarticMertensMass y ≤ gaussianCentralPrimePowerDefect y := by
  rw [gaussianQuarticMertensMass, gaussianCentralPrimePowerDefect]
  have h := tsum_comp_le_tsum_of_inj (summable_primePowerDefectTerm hy)
    (primePowerDefectTerm_nonneg y) (Nat.pow_left_injective two_ne_zero)
  refine le_of_eq_of_le (tsum_congr fun m => ?_) h
  exact (primePowerDefectTerm_sq y m).symm

/-- **Upper sandwich** `D(y) ≤ 2 Q(y)`: the non-square higher prime powers `p^{2j+1}` are the
images of `p^j` under `m ↦ minFac(m)·m²`. -/
theorem primePowerDefect_le_two_mul_gaussianQuarticMertensMass {y : ℝ} (hy : 0 < y) :
    gaussianCentralPrimePowerDefect y ≤ 2 * gaussianQuarticMertensMass y := by
  set g := primePowerDefectTerm y with hg
  have hgs := summable_primePowerDefectTerm hy
  have hg0 := primePowerDefectTerm_nonneg y
  set f₁ : ℕ → ℝ := fun n => if IsSquare n then g n else 0 with hf₁
  set f₂ : ℕ → ℝ := fun n => if IsSquare n then 0 else g n with hf₂
  have hsplit : ∀ n, g n = f₁ n + f₂ n := fun n => by
    simp only [hf₁, hf₂]; split_ifs <;> simp
  have hf₁0 : ∀ n, 0 ≤ f₁ n := fun n => by simp only [hf₁]; split_ifs; exact hg0 n; exact le_rfl
  have hf₂0 : ∀ n, 0 ≤ f₂ n := fun n => by simp only [hf₂]; split_ifs; exact le_rfl; exact hg0 n
  have hf₁s : Summable f₁ := Summable.of_nonneg_of_le hf₁0
    (fun n => by have := hsplit n; linarith [hf₂0 n]) hgs
  have hf₂s : Summable f₂ := Summable.of_nonneg_of_le hf₂0
    (fun n => by have := hsplit n; linarith [hf₁0 n]) hgs
  have hQ : gaussianQuarticMertensMass y = ∑' m : ℕ, g (m ^ 2) := by
    rw [gaussianQuarticMertensMass]
    exact tsum_congr fun m => (primePowerDefectTerm_sq y m).symm
  have hqs : Summable fun m : ℕ => g (m ^ 2) := by
    simpa only [hg, primePowerDefectTerm_sq] using summable_quarticTerm hy
  -- the square part is `Q`
  have h1 : ∑' n : ℕ, f₁ n = ∑' m : ℕ, g (m ^ 2) := by
    rw [← (Nat.pow_left_injective two_ne_zero).tsum_eq (f := f₁)]
    · refine tsum_congr fun m => ?_
      simp only [hf₁]
      rw [if_pos ⟨m, sq m⟩]
    · intro n hn
      simp only [Function.mem_support, hf₁] at hn
      split_ifs at hn with hsq
      · obtain ⟨r, rfl⟩ := hsq
        exact ⟨r, sq r⟩
      · exact absurd rfl hn
  -- the non-square part is at most `Q`
  have h2 : ∑' n : ℕ, f₂ n ≤ ∑' m : ℕ, g (m ^ 2) := by
    rw [← minFac_mul_sq_injective.tsum_eq (f := f₂)]
    · have hle : ∀ m : ℕ, f₂ (m.minFac * m ^ 2) ≤ g (m ^ 2) := fun m => by
        simp only [hf₂]
        split_ifs
        · exact hg0 _
        · exact primePowerDefectTerm_minFac_mul_sq_le hy m
      exact Summable.tsum_le_tsum hle
        (Summable.of_nonneg_of_le (fun m => hf₂0 _) hle hqs) hqs
    · intro n hn
      simp only [Function.mem_support, hf₂] at hn
      split_ifs at hn with hsq
      · exact absurd rfl hn
      · have hnp : ¬ n.Prime := by
          intro hp; simp [hg, primePowerDefectTerm, hp] at hn
        have hΛ : Λ n ≠ 0 := by
          intro h0; simp [hg, primePowerDefectTerm, hnp, h0] at hn
        have hpp : IsPrimePow n := by
          by_contra h; exact hΛ (ArithmeticFunction.vonMangoldt_eq_zero_iff.2 h)
        obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
        have hk1 : k ≠ 1 := by rintro rfl; exact hnp (by simpa using hp)
        have hkodd : k % 2 = 1 := by
          by_contra hev
          apply hsq
          refine ⟨p ^ (k / 2), ?_⟩
          rw [← pow_add]
          congr 1
          omega
        refine ⟨p ^ (k / 2), ?_⟩
        simp only
        rw [Nat.Prime.pow_minFac hp (by omega), ← pow_mul, ← pow_succ']
        congr 1
        omega
  have hD : gaussianCentralPrimePowerDefect y = ∑' n : ℕ, g n := rfl
  rw [hD, tsum_congr hsplit, hf₁s.tsum_add hf₂s, h1, hQ]
  linarith

/-! ## The Gaussian Chebyshev conjecture -/

/-- **Chebyshev bias under RH.**  Under RH, `Π(y) − C(y) ≤ K − ¼ log(1/y)` on `(0, 1]`: the central
budget `P ≤ C + K₀` and the prime squares `D ≥ Q ≥ ¼ log(1/y) − O(1)`. -/
theorem exists_gaussianPrimeOnlyGap_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianCentralPrimeOnlyMass y - gaussianWeightedContinuumMass (1 / 2) y ≤
        K - Real.log (1 / y) / 4 := by
  obtain ⟨K₀, hK₀⟩ := riemannHypothesis_iff_gaussianCentralPrimeBudget.1 hRH
  refine ⟨K₀ + (Real.log 2 + 2 * (Real.log 4 + 4)), fun y hy hy1 => ?_⟩
  have hP := hK₀ y hy hy1
  have hsplit := gaussianWeightedPrimeMass_half_eq hy
  have hQD := gaussianQuarticMertensMass_le_primePowerDefect hy
  have hQ := gaussianQuarticMertensMass_ge hy hy1
  linarith

/-- **Converse.**  An eventual upper bound `Π(y) − C(y) ≤ B` implies RH: with `D ≤ 2Q` the full
central gap is `O(log(1/y)) = O(y^{-ε})`, and the growth law excludes zeros right of `½ + 2ε`. -/
theorem riemannHypothesis_of_eventually_gaussianPrimeOnlyGap_le {B : ℝ}
    (h : ∀ᶠ y in 𝓝[>] 0,
      gaussianCentralPrimeOnlyMass y - gaussianWeightedContinuumMass (1 / 2) y ≤ B) :
    RiemannHypothesis := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  have hδ0 : (0 : ℝ) < δ := hδ
  set KU : ℝ := (Real.log 4 + 4) + 2 * (Real.log 2 + 2 * (Real.log 4 + 4)) with hKU
  have hKU0 : 0 ≤ KU := by
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    rw [hKU]; linarith
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  have hs' := mem_rightHalf.1 hs
  set ε : ℝ := min ((s.re - 1 / 2) / 4) 1 with hε
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεs : 1 / 2 + 2 * ε < s.re := by
    have := min_le_left ((s.re - 1 / 2) / 4) 1
    linarith
  set A : ℝ := (Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ) with hA
  set Bε : ℝ := (|B| + 2 * KU + 1 / (2 * ε)) + A with hBε
  refine xi_ne_zero_of_gaussianPrimeGrowthBudget (σ := 1 / 2) (by norm_num) (η := 1) (Or.inl rfl)
    hε0.le hε1 (B := Bε) (fun y hy hy1 => ?_) hεs hzero
  rw [one_mul]
  have hY1 : 1 ≤ y ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hC0 : 0 ≤ |B| + 2 * KU + 1 / (2 * ε) := by positivity
  by_cases hyδ : y < δ
  · have hPi : gaussianCentralPrimeOnlyMass y - gaussianWeightedContinuumMass (1 / 2) y ≤ B :=
      hsub ⟨hy, hyδ⟩
    have hsplit := gaussianWeightedPrimeMass_half_eq hy
    have hD := primePowerDefect_le_two_mul_gaussianQuarticMertensMass hy
    have hQ := gaussianQuarticMertensMass_le hy hy1
    have hlog : Real.log (1 / y) ≤ y ^ (-ε) / ε := by
      have h := Real.log_le_rpow_div (x := 1 / y) (by positivity) hε0
      rw [one_div, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at h
      rwa [one_div]
    have hPC : gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤
        |B| + 2 * KU + Real.log (1 / y) / 2 := by
      have := le_abs_self B
      rw [hKU]
      linarith
    have h1 : |B| + 2 * KU ≤ (|B| + 2 * KU) * y ^ (-ε) :=
      le_mul_of_one_le_right (by positivity) hY1
    have h2 : Real.log (1 / y) / 2 ≤ 1 / (2 * ε) * y ^ (-ε) := by
      have heq : 1 / (2 * ε) * y ^ (-ε) = (y ^ (-ε) / ε) / 2 := by
        field_simp
      rw [heq]
      linarith
    have h3 : A ≤ A * y ^ (-ε) := le_mul_of_one_le_right hA0 hY1
    calc gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y
        ≤ (|B| + 2 * KU) * y ^ (-ε) + 1 / (2 * ε) * y ^ (-ε) := by linarith
      _ ≤ Bε * y ^ (-ε) := by rw [hBε]; nlinarith
  · push Not at hyδ
    have habs := (abs_le.1 (abs_gaussianWeightedGap_le_of_ge (σ := 1 / 2) (by norm_num) hδ0
      hyδ hy1)).2
    have h3 : A ≤ A * y ^ (-ε) := le_mul_of_one_le_right hA0 hY1
    have h4 : 0 ≤ (|B| + 2 * KU + 1 / (2 * ε)) * y ^ (-ε) := by positivity
    calc gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤ A := habs
      _ ≤ Bε * y ^ (-ε) := by rw [hBε]; nlinarith

/-- **The Gaussian Chebyshev conjecture.**  RH holds iff
`Σ_p (log p) p^{-1/2} e^{-yp²} − ∫₁^∞ u^{-1/2} e^{-yu²} du → −∞` as `y → 0⁺`. -/
theorem riemannHypothesis_iff_tendsto_gaussianPrimeOnlyGap_atBot :
    RiemannHypothesis ↔ Tendsto (fun y : ℝ =>
      gaussianCentralPrimeOnlyMass y - gaussianWeightedContinuumMass (1 / 2) y) (𝓝[>] 0) atBot := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := exists_gaussianPrimeOnlyGap_le_of_riemannHypothesis hRH
    have hlog : Tendsto (fun y : ℝ => K + Real.log y / 4) (𝓝[>] 0) atBot :=
      tendsto_atBot_add_const_left _ K (Real.tendsto_log_nhdsGT_zero.atBot_div_const (by norm_num))
    refine tendsto_atBot_mono' _ ?_ hlog
    have hy1 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ≤ 1 := nhdsWithin_le_nhds (Iic_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, hy1] with y hy hy1
    have := hK y hy hy1
    have hl : Real.log (1 / y) = -Real.log y := by rw [one_div, Real.log_inv]
    rw [hl] at this
    linarith
  · intro h
    exact riemannHypothesis_of_eventually_gaussianPrimeOnlyGap_le (B := 0) (tendsto_atBot.1 h 0)

/-- **Prime sign law.**  RH holds iff `Σ_p (log p) p^{-1/2} e^{-yp²} < ∫₁^∞ u^{-1/2} e^{-yu²} du`
for all sufficiently small `y > 0`. -/
theorem riemannHypothesis_iff_eventually_gaussianPrimeOnlyMass_lt :
    RiemannHypothesis ↔ ∀ᶠ y in 𝓝[>] 0,
      gaussianCentralPrimeOnlyMass y < gaussianWeightedContinuumMass (1 / 2) y := by
  constructor
  · intro hRH
    filter_upwards [tendsto_atBot.1
      (riemannHypothesis_iff_tendsto_gaussianPrimeOnlyGap_atBot.1 hRH) (-1)] with y hy
    linarith
  · intro h
    exact riemannHypothesis_of_eventually_gaussianPrimeOnlyGap_le (B := 0)
      (h.mono fun y hy => by linarith)

end

end RHTower
