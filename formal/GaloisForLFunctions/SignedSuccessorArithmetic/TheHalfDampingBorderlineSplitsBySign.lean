import GaloisForLFunctions.SignedSuccessorArithmetic.TheForwardDilatedHypercubeForm
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicLogRate
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.ElementaryHarmonicBounds

/-!
# The half-damping borderline (`ε = 1/2`, `σ = 1`) splits by sign

Above half damping (`ε > 1/2`), every bounded-sign dilation Dirichlet form is uniformly bounded in
its cutoff (`sizeHypercubeForm_le_of_one_lt`, `signedDilationDirichletForm_le_tsum_sq_of_half_lt`),
while below half damping (`0 ≤ ε < 1/2`) the prime-divisor hypercube form and its `+1` parity twin
share a sign-blind threshold (`hypercubeDilationDirichletForm_threshold`).

At the critical-strip boundary `ε = 1/2` (`σ = 1`), the size-truncated Möbius form and its parity
twin separate unconditionally for **every** modulus `r > 1`:
1. **Unconditional cutoff-uniform boundedness of `sizeHypercubeForm hr (1/2) D`
   (`sizeHypercubeForm_half_bounded`):** In forward-dilated coordinates (`u = 1/x`), decomposing
   `G_{1/2,D}(1/u)` across the `K = ⌊(log u)²⌋₊ + 1` floor shells `⌊d / u⌋₊ = k` and bounding each
   shell via antitone Abel summation against `deningerMertensM_log_pow_four_rate` gives
   `|G_{1/2,D}(1/u)| ≤ C_r / (√u log u)` uniformly in `D` for `u > e²`, whose square integrates on
   `(e², ∞)` against `du` to `C_r² / 2`. This bounds the full spectral form (both receiver head and
   trans-cutoff tail `n > D`).
2. **Unconditional logarithmic divergence of the parity twin at `ε = 1/2` for every `r > 1`:**
   Testing the `+1` primitive `Ψ⁺(n) = ∑_{d ∈ S} d^{−1/2} Re C_r(⌊n / d⌋)` against
   `δ(n) = 1/√n − 1/√(n + 1)` cancels the `2√(X / (d a))` leading Euler–Maclaurin term identically
   via `∑_{b ∣ r} μ(b) = 0` (`r > 1`), isolating the strictly positive constant defect
   `c₀ √r ∏_{p ∣ r} (1 − p^{−1/2}) > 0` times the harmonic sum `∑_{d ∈ S, d ≤ X} 1 / d`.
   Cauchy–Schwarz yields `signedDilationDirichletForm 1 (1/2) S r hr ≥ c_r log X − O_r(1)` for both:
   * `S = Icc 1 X` (`tendsto_sizeTwinHypercubeForm_half_atTop`), and
   * `S = (roughPrimeProd r X).divisors` over squarefree `P` coprime to `r`
     (`tendsto_hypercubeTwinDilationDirichletForm_half_roughPrimeProd`,
     `not_bddAbove_hypercubeTwinDilationDirichletForm_half`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Filter Topology
open _root_.RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators ArithmeticFunction.Moebius

/-- Size-truncated parity-twin hypercube form (every Möbius sign replaced by `+1`). -/
noncomputable def sizeTwinHypercubeForm {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) : ℝ :=
  signedDilationDirichletForm (fun _ => 1) ε (Finset.Icc 1 D) r hr

/-- Product of all primes in `(r, X]`, squarefree and coprime to `r`. -/
def roughPrimeProd (r X : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Ioc r X).filter Nat.Prime, p

/-! ## §1. Antitone Abel summation and forward-dilated shell bound at `ε = 1/2` -/

private theorem abs_abelMertens_le_nat (n : ℕ) :
    |CubicGamma.abelMertens n| ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [DiscretePacket.abelMertens_zero]
  rw [← DiscretePacket.sum_range_succ_moebius]
  have hsplit : ∑ j ∈ Finset.range (n + 1), ((μ j : ℤ) : ℝ) =
      ∑ j ∈ Finset.Icc 1 n, ((μ j : ℤ) : ℝ) := by
    have : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [this, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
  rw [hsplit]
  calc |∑ j ∈ Finset.Icc 1 n, ((μ j : ℤ) : ℝ)|
      ≤ ∑ j ∈ Finset.Icc 1 n, |((μ j : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j)
    _ = (n : ℝ) := by simp

private theorem exists_abs_abelMertens_log_pow_four_le :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ n : ℕ, 2 ≤ n →
      |CubicGamma.abelMertens n| ≤ M₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
  obtain ⟨B₀, hB₀, hev⟩ := RHTower.Sieve.deningerMertensM_log_pow_four_rate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  set K := max N₀ 2
  refine ⟨B₀ + (Real.log (K : ℝ)) ^ 4, by positivity, fun n hn2 => ?_⟩
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlog4 : 0 < (Real.log (n : ℝ)) ^ 4 := pow_pos hlog 4
  by_cases hge : N₀ ≤ n
  · have hrate := hN₀ n hge
    rw [CubicGamma.abelMertens_eq_mertensM]
    refine hrate.trans ?_
    rw [div_le_div_iff_of_pos_right hlog4]
    have : 0 ≤ (Real.log (K : ℝ)) ^ 4 * (n : ℝ) := by positivity
    linarith
  · have hnK : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show n ≤ max N₀ 2 by omega)
    have hlogK : Real.log (n : ℝ) ≤ Real.log (K : ℝ) :=
      Real.log_le_log (by positivity) hnK
    have hpowK : (Real.log (n : ℝ)) ^ 4 ≤ (Real.log (K : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hlog.le hlogK 4
    calc |CubicGamma.abelMertens n|
        ≤ (n : ℝ) := abs_abelMertens_le_nat n
      _ = (Real.log (n : ℝ)) ^ 4 * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
          rw [mul_div_cancel_left₀ _ hlog4.ne']
      _ ≤ (B₀ + (Real.log (K : ℝ)) ^ 4) * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
          rw [div_le_div_iff_of_pos_right hlog4]
          exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-- Antitone Abel summation: if `|M(n)| ≤ L` on `[a, b]` and `g ≥ 0` is nonincreasing on `[a+1, b]`,
then `|∑_{a < n ≤ b} μ(n) g(n)| ≤ 2 L g(a + 1)`. -/
private theorem abs_sum_Ioc_moebiusReal_mul_le_of_antitone (g : ℕ → ℝ) {a b : ℕ} (hab : a < b)
    {L : ℝ} (hM : ∀ n, a ≤ n → n ≤ b → |CubicGamma.abelMertens n| ≤ L)
    (hgb : 0 ≤ g b) (hanti : ∀ n, a + 1 ≤ n → n < b → g (n + 1) ≤ g n) :
    |∑ n ∈ Finset.Ioc a b, moebiusReal n * g n| ≤ 2 * L * g (a + 1) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hM a le_rfl hab.le)
  have hchain : ∀ c, a + 1 ≤ c → c ≤ b → g b ≤ g c := by
    intro c hac hcb
    have hstep : ∀ d, c ≤ d → d ≤ b → g d ≤ g c := by
      intro d hcd
      induction d, hcd using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ d hcd ih =>
        intro hdb
        exact (hanti d (by omega) (by omega)).trans (ih (by omega))
    exact hstep b hcb le_rfl
  have hga : 0 ≤ g (a + 1) := hgb.trans (hchain (a + 1) le_rfl hab)
  have hab_step := DiscretePacket.abs_sum_Ioc_moebius_mul_le g hab
  unfold moebiusReal
  have h1 : |g b| * |CubicGamma.abelMertens b| ≤ g b * L := by
    rw [abs_of_nonneg hgb]; exact mul_le_mul_of_nonneg_left (hM b hab.le le_rfl) hgb
  have h2 : |g (a + 1)| * |CubicGamma.abelMertens a| ≤ g (a + 1) * L := by
    rw [abs_of_nonneg hga]; exact mul_le_mul_of_nonneg_left (hM a le_rfl hab.le) hga
  have h3 : ∑ n ∈ Finset.Ioc a (b - 1), |g (n + 1) - g n| * |CubicGamma.abelMertens n| ≤
      (g (a + 1) - g b) * L := by
    calc ∑ n ∈ Finset.Ioc a (b - 1), |g (n + 1) - g n| * |CubicGamma.abelMertens n|
        ≤ ∑ n ∈ Finset.Ioc a (b - 1), (-(g (n + 1) - g n)) * L := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' := Finset.mem_Ioc.mp hn
          have hle := hanti n (by omega) (by omega)
          rw [abs_of_nonpos (by linarith)]
          exact mul_le_mul_of_nonneg_left (hM n (by omega) (by omega)) (by linarith)
      _ = (-(∑ n ∈ Finset.Ioc a (b - 1), (g (n + 1) - g n))) * L := by
          rw [← Finset.sum_neg_distrib, ← Finset.sum_mul]
      _ = (g (a + 1) - g b) * L := by
          rw [DiscretePacket.sum_Ioc_telescope g (by omega : a ≤ b - 1),
            Nat.sub_add_cancel (by omega : 1 ≤ b)]
          ring
  linarith

private theorem sum_Ioc_chain (f : ℕ → ℝ) (b : ℕ → ℕ) {K : ℕ}
    (hmono : ∀ k, 1 ≤ k → k ≤ K → b k ≤ b (k + 1)) :
    ∑ d ∈ Finset.Ioc (b 1) (b (K + 1)), f d =
      ∑ k ∈ Finset.Icc 1 K, ∑ d ∈ Finset.Ioc (b k) (b (k + 1)), f d := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hb1 : ∀ k, 1 ≤ k → k ≤ K + 1 → b 1 ≤ b k := by
      intro k hk1
      induction k, hk1 using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hk1 ihk =>
        intro hkK
        exact (ihk (by omega)).trans (hmono k hk1 (by omega))
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1),
      ← ih (fun k hk1 hkK => hmono k hk1 (by omega)),
      Finset.sum_Ioc_consecutive f (hb1 (K + 1) (by omega) le_rfl) (hmono (K + 1) (by omega) le_rfl)]

private theorem exp_two_ge_four : (4 : ℝ) ≤ Real.exp 2 := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

/-- Uniform decay `|G_{1/2,D}(1/u)| ≤ C / (√u log u)` on `u > e²`, uniform in `D`. -/
private theorem abs_forwardDilatedPrimitive_half_inv_le {r : ℕ} (hr : 1 < r) {M₁ : ℝ}
    (hM₁0 : 0 ≤ M₁)
    (hM₁ : ∀ n : ℕ, 2 ≤ n →
      |CubicGamma.abelMertens n| ≤ M₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 4)
    (D : ℕ) {u : ℝ} (hu : Real.exp 2 < u) :
    |forwardDilatedPrimitive r (1 / 2) D u⁻¹| ≤
      pmRamanujanPrimitiveBound r * (64 * M₁ + 2) / (Real.sqrt u * Real.log u) := by
  have hu4 : 4 < u := lt_of_le_of_lt exp_two_ge_four hu
  have hu0 : 0 < u := by linarith
  have hsu0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hlogu : 2 < Real.log u := by
    rw [← Real.log_exp 2]
    exact Real.log_lt_log (Real.exp_pos 2) hu
  have hlogu0 : 0 < Real.log u := by linarith
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
    (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
  set K : ℕ := ⌊(Real.log u) ^ 2⌋₊ + 1
  have hK1 : 1 ≤ K := by omega
  have hK_gt : (Real.log u) ^ 2 < (K : ℝ) := by
    dsimp [K]; push_cast; exact Nat.lt_floor_add_one _
  have hK_le : (K : ℝ) ≤ 2 * (Real.log u) ^ 2 := by
    have hf : (⌊(Real.log u) ^ 2⌋₊ : ℝ) ≤ (Real.log u) ^ 2 := Nat.floor_le (by positivity)
    have h4 : 4 < (Real.log u) ^ 2 := by nlinarith
    dsimp [K]; push_cast; linarith
  set a : ℕ → ℕ := fun k => ⌈(k : ℝ) * u⌉₊
  set b : ℕ → ℕ := fun k => min D (a k - 1)
  have ha_ge5 : ∀ k, 1 ≤ k → 5 ≤ a k := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h4lt : ((4 : ℕ) : ℝ) < (k : ℝ) * u := by push_cast; nlinarith
    exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr h4lt)
  have ha_mono : ∀ k₁ k₂, k₁ ≤ k₂ → a k₁ ≤ a k₂ := fun k₁ k₂ hk =>
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu0.le)
  have hb_mono : ∀ k₁ k₂, k₁ ≤ k₂ → b k₁ ≤ b k₂ := fun k₁ k₂ hk => by
    have := ha_mono k₁ k₂ hk; dsimp [b]; omega
  set term : ℕ → ℝ := fun d =>
    moebiusReal d * (d : ℝ) ^ (-1 - (1 / 2 : ℝ)) * (pmRamanujanPrimitive r ⌊(d : ℝ) * u⁻¹⌋₊).re
  have hIcc : Finset.Icc 1 D = Finset.Ioc 0 D := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hb01 : 0 ≤ b 1 := Nat.zero_le _
  have hb1K : b 1 ≤ b (K + 1) := hb_mono 1 (K + 1) (by omega)
  have hbKD : b (K + 1) ≤ D := Nat.min_le_left _ _
  have hsplit : forwardDilatedPrimitive r (1 / 2) D u⁻¹ =
      (∑ d ∈ Finset.Ioc 0 (b 1), term d) +
        (∑ d ∈ Finset.Ioc (b 1) (b (K + 1)), term d) +
        (∑ d ∈ Finset.Ioc (b (K + 1)) D, term d) := by
    unfold forwardDilatedPrimitive
    rw [hIcc, ← Finset.sum_Ioc_consecutive term (hb01.trans hb1K) hbKD,
      ← Finset.sum_Ioc_consecutive term hb01 hb1K]
  have hhead0 : ∑ d ∈ Finset.Ioc 0 (b 1), term d = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    have hd' := Finset.mem_Ioc.mp hd
    have ha1 := ha_ge5 1 le_rfl
    have hlt_a1 : d < a 1 := by
      have : d ≤ a 1 - 1 := hd'.2.trans (Nat.min_le_right _ _)
      omega
    have hdu : (d : ℝ) < u := by
      have := Nat.lt_ceil.mp hlt_a1
      simpa using this
    have hdu1 : (d : ℝ) * u⁻¹ < 1 := (mul_inv_lt_iff₀ hu0).mpr (by linarith)
    have hfl : ⌊(d : ℝ) * u⁻¹⌋₊ = 0 := Nat.floor_eq_zero.mpr hdu1
    simp [term, hfl, pmRamanujanPrimitive]
  have hmid : |∑ d ∈ Finset.Ioc (b 1) (b (K + 1)), term d| ≤
      pmRamanujanPrimitiveBound r * (64 * M₁) / (Real.sqrt u * Real.log u) := by
    rw [sum_Ioc_chain term b (fun k hk1 hkK => hb_mono k (k + 1) (by omega))]
    have hshell : ∀ k ∈ Finset.Icc 1 K,
        |∑ d ∈ Finset.Ioc (b k) (b (k + 1)), term d| ≤
          pmRamanujanPrimitiveBound r * (64 * M₁ / (Real.sqrt u * (Real.log u) ^ 4)) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hconst : ∑ d ∈ Finset.Ioc (b k) (b (k + 1)), term d =
          (pmRamanujanPrimitive r k).re *
            ∑ d ∈ Finset.Ioc (b k) (b (k + 1)), moebiusReal d * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd' := Finset.mem_Ioc.mp hd
        have hak5 := ha_ge5 k hk1
        have hak15 := ha_ge5 (k + 1) (by omega)
        have hbkD : b (k + 1) ≤ D := Nat.min_le_left _ _
        have hge_ak : a k ≤ d := by
          have : b k = min D (a k - 1) := rfl
          omega
        have hlt_ak1 : d < a (k + 1) := by
          have : d ≤ a (k + 1) - 1 := hd'.2.trans (Nat.min_le_right _ _)
          omega
        have hku_le : (k : ℝ) * u ≤ (d : ℝ) := Nat.ceil_le.mp hge_ak
        have hd_lt : (d : ℝ) < ((k + 1 : ℕ) : ℝ) * u := Nat.lt_ceil.mp hlt_ak1
        have hfl : ⌊(d : ℝ) * u⁻¹⌋₊ = k := by
          refine (Nat.floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
          · exact (le_mul_inv_iff₀ hu0).mpr hku_le
          · rw [mul_inv_lt_iff₀ hu0]; push_cast at hd_lt; exact hd_lt
        simp only [term, hfl, show (-1 - (1 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
        ring
      rw [hconst, abs_mul]
      have hC : |(pmRamanujanPrimitive r k).re| ≤ pmRamanujanPrimitiveBound r :=
        (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr k)
      rcases le_or_gt (b (k + 1)) (b k) with hle | hlt
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero, mul_zero]
        positivity
      · have hbk_eq : b k = a k - 1 := by
          have : b (k + 1) ≤ D := Nat.min_le_left _ _
          have : b k = min D (a k - 1) := rfl
          omega
        have hak5 := ha_ge5 k hk1
        have hak15 := ha_ge5 (k + 1) (by omega)
        set L : ℝ := 32 * M₁ * (k : ℝ) * u / (Real.log u) ^ 4
        have hM_on : ∀ n, b k ≤ n → n ≤ b (k + 1) →
            |CubicGamma.abelMertens n| ≤ L := by
          intro n hna hnb
          have hn2 : 2 ≤ n := by omega
          have hsu_lt_n : Real.sqrt u < (n : ℝ) := by
            have hsu2 : 2 < Real.sqrt u := by
              rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
              exact Real.sqrt_lt_sqrt (by norm_num) hu4
            have hu_sq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
            have hku : u ≤ (a k : ℝ) := by
              have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
              exact (by nlinarith : u ≤ (k : ℝ) * u).trans (Nat.le_ceil _)
            have hn_ge : (a k : ℝ) - 1 ≤ (n : ℝ) := by
              have : a k - 1 ≤ n := by omega
              have h1 : ((a k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
              rw [Nat.cast_sub (by omega)] at h1; simpa using h1
            nlinarith
          have hlog_n : Real.log u / 2 ≤ Real.log (n : ℝ) := by
            have := Real.log_lt_log hsu0 hsu_lt_n
            rw [Real.log_sqrt hu0.le] at this
            linarith
          have hlog4_ge : (Real.log u) ^ 4 / 16 ≤ (Real.log (n : ℝ)) ^ 4 := by
            have h1 : (Real.log u / 2) ^ 4 ≤ (Real.log (n : ℝ)) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hlog_n 4
            linarith [show (Real.log u / 2) ^ 4 = (Real.log u) ^ 4 / 16 by ring]
          have hn_upper : (n : ℝ) ≤ 2 * (k : ℝ) * u := by
            have hnb' : n ≤ a (k + 1) - 1 := hnb.trans (Nat.min_le_right _ _)
            have hlt_ceil : ((a (k + 1) - 1 : ℕ) : ℝ) < ((k + 1 : ℕ) : ℝ) * u := by
              by_contra hge
              have hce := Nat.ceil_le.mpr (not_lt.mp hge)
              change a (k + 1) ≤ a (k + 1) - 1 at hce
              omega
            have hnR : (n : ℝ) ≤ ((a (k + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hnb'
            have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
            push_cast at hlt_ceil
            nlinarith
          calc |CubicGamma.abelMertens n|
              ≤ M₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := hM₁ n hn2
            _ ≤ M₁ * (2 * (k : ℝ) * u) / ((Real.log u) ^ 4 / 16) := by
                have hnum : M₁ * (n : ℝ) ≤ M₁ * (2 * (k : ℝ) * u) :=
                  mul_le_mul_of_nonneg_left hn_upper hM₁0
                exact div_le_div₀ (by positivity) hnum (by positivity) hlog4_ge
            _ = L := by dsimp [L]; ring
        have hanti : ∀ n, b k + 1 ≤ n → n < b (k + 1) →
            ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          intro n hn1 _
          have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
          rw [Real.rpow_neg (by positivity), Real.rpow_neg hn0.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hn0 _)
            (Real.rpow_le_rpow hn0.le (by exact_mod_cast (Nat.le_succ n)) (by norm_num))
        have hab := abs_sum_Ioc_moebiusReal_mul_le_of_antitone
          (fun n => (n : ℝ) ^ (-(3 / 2 : ℝ))) hlt hM_on
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) hanti
        have hba1 : b k + 1 = a k := by omega
        have hak_ge : (k : ℝ) * u ≤ ((b k + 1 : ℕ) : ℝ) := by
          rw [hba1]; exact Nat.le_ceil _
        have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        have hku0 : 0 < (k : ℝ) * u := by positivity
        have hg_le : ((b k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((k : ℝ) * u) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_neg hku0.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hku0 _)
            (Real.rpow_le_rpow hku0.le hak_ge (by norm_num))
        have hku_rpow : (k : ℝ) * u * ((k : ℝ) * u) ^ (-(3 / 2 : ℝ)) =
            (Real.sqrt k * Real.sqrt u)⁻¹ := by
          have : (k : ℝ) * u * ((k : ℝ) * u) ^ (-(3 / 2 : ℝ)) = ((k : ℝ) * u) ^ (-(1 / 2 : ℝ)) := by
            rw [show (k : ℝ) * u * ((k : ℝ) * u) ^ (-(3 / 2 : ℝ)) =
              ((k : ℝ) * u) ^ (1 : ℝ) * ((k : ℝ) * u) ^ (-(3 / 2 : ℝ)) by rw [Real.rpow_one],
              ← Real.rpow_add hku0]
            norm_num
          rw [this, Real.rpow_neg hku0.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity)]
        have hsk1 : (1 : ℝ) ≤ Real.sqrt k := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hkR
        have h2Lg : 2 * L * ((b k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤
            64 * M₁ / (Real.sqrt u * (Real.log u) ^ 4) := by
          have hL0 : 0 ≤ L := by positivity
          calc 2 * L * ((b k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
              ≤ 2 * L * ((k : ℝ) * u) ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hg_le (by positivity)
            _ = 64 * M₁ / (Real.log u) ^ 4 * ((k : ℝ) * u * ((k : ℝ) * u) ^ (-(3 / 2 : ℝ))) := by
                dsimp [L]; ring
            _ = 64 * M₁ / (Real.log u) ^ 4 * (Real.sqrt k * Real.sqrt u)⁻¹ := by rw [hku_rpow]
            _ ≤ 64 * M₁ / (Real.log u) ^ 4 * (1 * Real.sqrt u)⁻¹ := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hsk1 hsu0.le)
            _ = 64 * M₁ / (Real.sqrt u * (Real.log u) ^ 4) := by
                rw [one_mul]; field_simp
        exact mul_le_mul hC (hab.trans h2Lg) (abs_nonneg _) hB0
    calc |∑ k ∈ Finset.Icc 1 K, ∑ d ∈ Finset.Ioc (b k) (b (k + 1)), term d|
        ≤ ∑ k ∈ Finset.Icc 1 K, |∑ d ∈ Finset.Ioc (b k) (b (k + 1)), term d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 K,
            pmRamanujanPrimitiveBound r * (64 * M₁ / (Real.sqrt u * (Real.log u) ^ 4)) :=
          Finset.sum_le_sum hshell
      _ = (K : ℝ) * (pmRamanujanPrimitiveBound r * (64 * M₁ / (Real.sqrt u * (Real.log u) ^ 4))) := by
          simp
      _ ≤ (2 * (Real.log u) ^ 2) *
            (pmRamanujanPrimitiveBound r * (64 * M₁ / (Real.sqrt u * (Real.log u) ^ 4))) :=
          mul_le_mul_of_nonneg_right hK_le (by positivity)
      _ = pmRamanujanPrimitiveBound r * (128 * M₁) / (Real.sqrt u * (Real.log u) ^ 2) := by
          field_simp; ring
      _ ≤ pmRamanujanPrimitiveBound r * (64 * M₁) / (Real.sqrt u * Real.log u) := by
          have hden : 2 * (Real.sqrt u * Real.log u) ≤ Real.sqrt u * (Real.log u) ^ 2 := by
            calc 2 * (Real.sqrt u * Real.log u)
                = (Real.sqrt u * Real.log u) * 2 := mul_comm _ _
              _ ≤ (Real.sqrt u * Real.log u) * Real.log u :=
                  mul_le_mul_of_nonneg_left hlogu.le (by positivity)
              _ = Real.sqrt u * (Real.log u) ^ 2 := by ring
          have h1 : pmRamanujanPrimitiveBound r * (128 * M₁) / (Real.sqrt u * (Real.log u) ^ 2) ≤
              pmRamanujanPrimitiveBound r * (128 * M₁) / (2 * (Real.sqrt u * Real.log u)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          refine h1.trans_eq ?_
          field_simp; ring
  have htail : |∑ d ∈ Finset.Ioc (b (K + 1)) D, term d| ≤
      pmRamanujanPrimitiveBound r * 2 / (Real.sqrt u * Real.log u) := by
    rcases le_or_gt D (a (K + 1) - 1) with hDle | hDgt
    · have hbK_eq : b (K + 1) = D := Nat.min_eq_left hDle
      rw [hbK_eq, Finset.Ioc_self, Finset.sum_empty, abs_zero]
      positivity
    · have hbK_eq : b (K + 1) = a (K + 1) - 1 := Nat.min_eq_right hDgt.le
      rw [hbK_eq]
      set U := a (K + 1) - 1
      have haK5 := ha_ge5 (K + 1) (by omega)
      have hU1 : 1 ≤ U := by omega
      have hU_ge : (Real.log u) ^ 2 * u ≤ (U : ℝ) := by
        have hce : ((K + 1 : ℕ) : ℝ) * u ≤ (a (K + 1) : ℝ) := Nat.le_ceil _
        have hcast : (U : ℝ) = (a (K + 1) : ℝ) - 1 := by
          dsimp [U]; rw [Nat.cast_sub (by omega)]; simp
        push_cast at hce
        nlinarith
      have hsU : Real.sqrt u * Real.log u ≤ Real.sqrt (U : ℝ) := by
        have h1 : Real.sqrt ((Real.log u) ^ 2 * u) ≤ Real.sqrt (U : ℝ) :=
          Real.sqrt_le_sqrt hU_ge
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hlogu0.le, mul_comm] at h1
        exact h1
      calc |∑ d ∈ Finset.Ioc U D, term d|
          ≤ ∑ d ∈ Finset.Ioc U D, |term d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Ioc U D,
              pmRamanujanPrimitiveBound r * (d : ℝ) ^ (-((1 / 2 : ℝ) + 1)) := by
            refine Finset.sum_le_sum fun d _ => ?_
            dsimp [term]
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
              show (-1 - (1 / 2 : ℝ)) = -((1 / 2 : ℝ) + 1) by norm_num]
            have hμ : |moebiusReal d| ≤ 1 := by
              unfold moebiusReal
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
            have hC : |(pmRamanujanPrimitive r ⌊(d : ℝ) * u⁻¹⌋₊).re| ≤
                pmRamanujanPrimitiveBound r :=
              (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
            calc |moebiusReal d| * (d : ℝ) ^ (-((1 / 2 : ℝ) + 1)) *
                  |(pmRamanujanPrimitive r ⌊(d : ℝ) * u⁻¹⌋₊).re|
                ≤ 1 * (d : ℝ) ^ (-((1 / 2 : ℝ) + 1)) * pmRamanujanPrimitiveBound r :=
                  mul_le_mul (mul_le_mul_of_nonneg_right hμ (by positivity)) hC
                    (abs_nonneg _) (by positivity)
              _ = pmRamanujanPrimitiveBound r * (d : ℝ) ^ (-((1 / 2 : ℝ) + 1)) := by ring
        _ = pmRamanujanPrimitiveBound r *
              ∑ d ∈ Finset.Ioc U D, (d : ℝ) ^ (-((1 / 2 : ℝ) + 1)) := (Finset.mul_sum _ _ _).symm
        _ ≤ pmRamanujanPrimitiveBound r * ((U : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (DiscretePacket.sum_Ioc_rpow_neg_le (by norm_num) hU1 D) hB0
        _ = pmRamanujanPrimitiveBound r * 2 / Real.sqrt (U : ℝ) := by
            rw [Real.rpow_neg (Nat.cast_nonneg U), ← Real.sqrt_eq_rpow]
            field_simp
        _ ≤ pmRamanujanPrimitiveBound r * 2 / (Real.sqrt u * Real.log u) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hsU
  rw [hsplit, hhead0, zero_add]
  calc |(∑ d ∈ Finset.Ioc (b 1) (b (K + 1)), term d) + ∑ d ∈ Finset.Ioc (b (K + 1)) D, term d|
      ≤ |∑ d ∈ Finset.Ioc (b 1) (b (K + 1)), term d| +
          |∑ d ∈ Finset.Ioc (b (K + 1)) D, term d| := abs_add_le _ _
    _ ≤ pmRamanujanPrimitiveBound r * (64 * M₁) / (Real.sqrt u * Real.log u) +
          pmRamanujanPrimitiveBound r * 2 / (Real.sqrt u * Real.log u) := add_le_add hmid htail
    _ = pmRamanujanPrimitiveBound r * (64 * M₁ + 2) / (Real.sqrt u * Real.log u) := by ring

private theorem hasDerivAt_neg_inv_log {u : ℝ} (hu1 : 1 < u) :
    HasDerivAt (fun x => -(Real.log x)⁻¹) (1 / (u * (Real.log u) ^ 2)) u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu1
  have hlog : 0 < Real.log u := Real.log_pos hu1
  have hd := ((Real.hasDerivAt_log hu0.ne').inv hlog.ne').neg
  refine hd.congr_deriv ?_
  field_simp

private theorem tendsto_neg_inv_log_atTop :
    Tendsto (fun x : ℝ => -(Real.log x)⁻¹) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).neg

private theorem integrableOn_Ioi_inv_mul_log_sq :
    IntegrableOn (fun u : ℝ => 1 / (u * (Real.log u) ^ 2)) (Set.Ioi (Real.exp 2)) := by
  have he1 : 1 < Real.exp 2 := by linarith [exp_two_ge_four]
  exact integrableOn_Ioi_deriv_of_nonneg
    (hasDerivAt_neg_inv_log he1).continuousAt.continuousWithinAt
    (fun u hu => hasDerivAt_neg_inv_log (lt_trans he1 hu))
    (fun u hu => by have := lt_trans zero_lt_one (lt_trans he1 hu); positivity)
    tendsto_neg_inv_log_atTop

/-- **Unconditional cutoff-uniform boundedness of `sizeHypercubeForm` at half damping (`ε = 1/2`).**
For every modulus `r > 1`, `sizeHypercubeForm hr (1 / 2) D` (the full spectral integral including
both the receiver head `n ≤ D` and the trans-cutoff tail `n > D`) is bounded uniformly in `D`. -/
theorem sizeHypercubeForm_half_bounded {r : ℕ} (hr : 1 < r) :
    ∃ B : ℝ, ∀ D : ℕ, sizeHypercubeForm hr (1 / 2) D ≤ B := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_abs_abelMertens_log_pow_four_le
  set C₀ : ℝ := pmRamanujanPrimitiveBound r * ∑' d : ℕ, ((d : ℝ) ^ (1 + (1 / 2 : ℝ)))⁻¹
  set C₁ : ℝ := pmRamanujanPrimitiveBound r * (64 * M₁ + 2)
  set I_tail : ℝ := ∫ u in Set.Ioi (Real.exp 2), C₁ ^ 2 * (1 / (u * (Real.log u) ^ 2))
  refine ⟨C₀ ^ 2 * Real.exp 2 + I_tail + C₀ ^ 2, fun D => ?_⟩
  refine (sizeHypercubeForm_le_forwardDilated_Ioo_add_const hr (by norm_num) D).trans ?_
  refine add_le_add ?_ le_rfl
  set f : ℝ → ℝ := fun u => forwardDilatedPrimitive r (1 / 2) D u⁻¹ ^ 2
  have hf_meas : Measurable f :=
    ((measurable_forwardDilatedPrimitive r (1 / 2) D).comp measurable_inv).pow_const 2
  have hf_bdd : ∀ u : ℝ, f u ≤ C₀ ^ 2 := fun u => by
    dsimp [f]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_forwardDilatedPrimitive_le hr (by norm_num) D u⁻¹) 2
  have hint_f : IntegrableOn f (Set.Ioo (1 : ℝ) D) := by
    refine (integrableOn_const (hs := measure_Ioo_lt_top.ne) (C := C₀ ^ 2)).mono'
      hf_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hf_bdd u
  have hsub : Set.Ioo (1 : ℝ) D ⊆ Set.Ioc (1 : ℝ) (Real.exp 2) ∪ Set.Ioi (Real.exp 2) := by
    intro u hu
    rcases le_or_gt u (Real.exp 2) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr hgt
  set S₁ := Set.Ioo (1 : ℝ) D ∩ Set.Ioc (1 : ℝ) (Real.exp 2)
  set S₂ := Set.Ioo (1 : ℝ) D ∩ Set.Ioi (Real.exp 2)
  have hpart : Set.Ioo (1 : ℝ) D = S₁ ∪ S₂ := by
    ext u
    simp only [S₁, S₂, Set.mem_union, Set.mem_inter_iff]
    exact ⟨fun hu => (hsub hu).elim (fun h1 => Or.inl ⟨hu, h1⟩) (fun h2 => Or.inr ⟨hu, h2⟩),
      fun h => h.elim And.left And.left⟩
  have hdisj : Disjoint S₁ S₂ :=
    (Set.Ioc_disjoint_Ioi le_rfl).mono Set.inter_subset_right Set.inter_subset_right
  have hmS₂ : MeasurableSet S₂ := measurableSet_Ioo.inter measurableSet_Ioi
  rw [hpart, setIntegral_union hdisj hmS₂
    (hint_f.mono_set Set.inter_subset_left) (hint_f.mono_set Set.inter_subset_left)]
  have hI₁ : (∫ u in S₁, f u) ≤ C₀ ^ 2 * Real.exp 2 := by
    have h1 : (∫ u in S₁, f u) ≤ ∫ _u in Set.Ioc (1 : ℝ) (Real.exp 2), C₀ ^ 2 := by
      calc (∫ u in S₁, f u)
          ≤ ∫ _u in S₁, C₀ ^ 2 := setIntegral_mono_on (hint_f.mono_set Set.inter_subset_left)
              (integrableOn_const ((measure_mono Set.inter_subset_right).trans_lt
                measure_Ioc_lt_top).ne)
              (measurableSet_Ioo.inter measurableSet_Ioc) fun u _ => hf_bdd u
        _ ≤ ∫ _u in Set.Ioc (1 : ℝ) (Real.exp 2), C₀ ^ 2 :=
            setIntegral_mono_set (integrableOn_const measure_Ioc_lt_top.ne)
              (Eventually.of_forall fun _ => sq_nonneg C₀)
              (Eventually.of_forall fun _ hx => hx.2)
    refine h1.trans ?_
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith [exp_two_ge_four]), smul_eq_mul]
    nlinarith [sq_nonneg C₀]
  have hI₂ : (∫ u in S₂, f u) ≤ I_tail := by
    have hint_dom : IntegrableOn (fun u : ℝ => C₁ ^ 2 * (1 / (u * (Real.log u) ^ 2)))
        (Set.Ioi (Real.exp 2)) := integrableOn_Ioi_inv_mul_log_sq.const_mul (C₁ ^ 2)
    calc (∫ u in S₂, f u)
        ≤ ∫ u in S₂, C₁ ^ 2 * (1 / (u * (Real.log u) ^ 2)) := by
          refine setIntegral_mono_on (hint_f.mono_set Set.inter_subset_left)
            (hint_dom.mono_set Set.inter_subset_right) hmS₂ fun u hu => ?_
          have hue : Real.exp 2 < u := hu.2
          have hu0 : 0 < u := lt_of_le_of_lt (by linarith [exp_two_ge_four]) hue
          have hpt := abs_forwardDilatedPrimitive_half_inv_le hr hM₁0 hM₁ D hue
          have hsq := pow_le_pow_left₀ (abs_nonneg _) hpt 2
          rw [sq_abs] at hsq
          refine hsq.trans_eq ?_
          dsimp [f, C₁]
          rw [div_pow, mul_pow (Real.sqrt u) (Real.log u) 2, Real.sq_sqrt hu0.le]
          ring
      _ ≤ I_tail := setIntegral_mono_set hint_dom
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have : 0 < u := lt_of_le_of_lt (by linarith [exp_two_ge_four]) hu
            positivity)
          (Eventually.of_forall fun _ hx => Set.inter_subset_right hx)
  exact add_le_add hI₁ hI₂

/-! ## §2. Exact Euler–Maclaurin constant defect and parity-twin divergence at `ε = 1/2` -/

/-- Step defect `2(√j − √(j − 1)) − 1/√j` of the square-root harmonic sum (`j ≥ 1`). -/
noncomputable def sqrtStepDefect (j : ℕ) : ℝ :=
  if j = 0 then 0 else 2 * (Real.sqrt j - Real.sqrt ((j - 1 : ℕ) : ℝ)) - 1 / Real.sqrt j

private theorem sqrtStepDefect_eq_div {j : ℕ} (hj : 1 ≤ j) :
    sqrtStepDefect j =
      1 / (Real.sqrt j * (Real.sqrt j + Real.sqrt ((j - 1 : ℕ) : ℝ)) ^ 2) := by
  unfold sqrtStepDefect
  rw [if_neg (by omega : j ≠ 0)]
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hsj0 : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
  have hsj1 : 0 ≤ Real.sqrt ((j - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsum0 : 0 < Real.sqrt j + Real.sqrt ((j - 1 : ℕ) : ℝ) := by linarith
  have hsqj : Real.sqrt (j : ℝ) ^ 2 = (j : ℝ) := Real.sq_sqrt hj0.le
  have hsqj1 : Real.sqrt ((j - 1 : ℕ) : ℝ) ^ 2 = (j : ℝ) - 1 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_sub hj, Nat.cast_one]
  have hdiff : (Real.sqrt j - Real.sqrt ((j - 1 : ℕ) : ℝ)) *
      (Real.sqrt j + Real.sqrt ((j - 1 : ℕ) : ℝ)) = 1 := by nlinarith
  field_simp
  nlinarith

private theorem sqrtStepDefect_nonneg (j : ℕ) : 0 ≤ sqrtStepDefect j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [sqrtStepDefect]
  · rw [sqrtStepDefect_eq_div hj]; positivity

private theorem sqrtStepDefect_le_rpow {j : ℕ} (hj : 1 ≤ j) :
    sqrtStepDefect j ≤ (j : ℝ) ^ (-((1 / 2 : ℝ) + 1)) := by
  rw [sqrtStepDefect_eq_div hj]
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hsj0 : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
  have hsj1 : 0 ≤ Real.sqrt ((j - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hden : (j : ℝ) * Real.sqrt j ≤
      Real.sqrt j * (Real.sqrt j + Real.sqrt ((j - 1 : ℕ) : ℝ)) ^ 2 := by
    have h1 : (j : ℝ) ≤ (Real.sqrt j + Real.sqrt ((j - 1 : ℕ) : ℝ)) ^ 2 := by
      have := Real.sq_sqrt hj0.le
      nlinarith
    nlinarith
  calc 1 / (Real.sqrt j * (Real.sqrt j + Real.sqrt ((j - 1 : ℕ) : ℝ)) ^ 2)
      ≤ 1 / ((j : ℝ) * Real.sqrt j) := one_div_le_one_div_of_le (by positivity) hden
    _ = (j : ℝ) ^ (-((1 / 2 : ℝ) + 1)) := by
        rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_one_add' hj0.le (by norm_num),
          ← Real.rpow_neg hj0.le]
        congr 1; ring

private theorem summable_sqrtStepDefect : Summable sqrtStepDefect := by
  refine Summable.of_nonneg_of_le sqrtStepDefect_nonneg (fun j => ?_)
    (Real.summable_nat_rpow.mpr (by norm_num : -((1 / 2 : ℝ) + 1) < -1))
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [show sqrtStepDefect 0 = 0 by simp [sqrtStepDefect], Nat.cast_zero,
      Real.zero_rpow (by norm_num : -((1 / 2 : ℝ) + 1) ≠ 0)]
  · exact sqrtStepDefect_le_rpow hj

/-- Positive Euler–Maclaurin constant `c₀ = ∑_{j ≥ 1} (2(√j − √(j − 1)) − 1/√j) ∈ [1, 3]`. -/
noncomputable def sqrtEulerConst : ℝ := ∑' j : ℕ, sqrtStepDefect j

private theorem one_le_sqrtEulerConst : 1 ≤ sqrtEulerConst := by
  have h1 : sqrtStepDefect 1 = 1 := by simp [sqrtStepDefect]; norm_num
  rw [← h1]
  exact summable_sqrtStepDefect.le_tsum 1 fun j _ => sqrtStepDefect_nonneg j

private theorem sqrtEulerConst_sub_sum_le {M : ℕ} (hM : 1 ≤ M) :
    sqrtEulerConst - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j ≤ 2 / Real.sqrt M := by
  have hrange : ∑ j ∈ Finset.range (M + 1), sqrtStepDefect j =
      ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j := by
    have : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [this, Finset.sum_insert (by simp), show sqrtStepDefect 0 = 0 by simp [sqrtStepDefect],
      zero_add]
  have hsplit := summable_sqrtStepDefect.sum_add_tsum_nat_add (M + 1)
  have htail : (∑' k : ℕ, sqrtStepDefect (k + (M + 1))) ≤ 2 / Real.sqrt M := by
    refine (summable_sqrtStepDefect.comp_injective
      (add_left_injective (M + 1))).tsum_le_of_sum_range_le fun N => ?_
    have himg : ∑ k ∈ Finset.range N, sqrtStepDefect (k + (M + 1)) =
        ∑ j ∈ Finset.Ioc M (M + N), sqrtStepDefect j := by
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih, show M + (N + 1) = (M + N) + 1 by omega,
          show N + (M + 1) = (M + N) + 1 by omega,
          Finset.sum_Ioc_succ_top (by omega : M ≤ M + N)]
    dsimp only [Function.comp_apply]
    rw [himg]
    calc ∑ j ∈ Finset.Ioc M (M + N), sqrtStepDefect j
        ≤ ∑ j ∈ Finset.Ioc M (M + N), (j : ℝ) ^ (-((1 / 2 : ℝ) + 1)) :=
          Finset.sum_le_sum fun j hj => sqrtStepDefect_le_rpow (by have := Finset.mem_Ioc.mp hj; omega)
      _ ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2 : ℝ) :=
          DiscretePacket.sum_Ioc_rpow_neg_le (by norm_num) hM (M + N)
      _ = 2 / Real.sqrt M := by
          rw [Real.rpow_neg (Nat.cast_nonneg M), ← Real.sqrt_eq_rpow]; ring
  have htot : sqrtEulerConst = (∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j) +
      ∑' k : ℕ, sqrtStepDefect (k + (M + 1)) := by
    rw [sqrtEulerConst, ← hsplit, hrange]
  linarith

private theorem sqrtEulerConst_le_three : sqrtEulerConst ≤ 3 := by
  have h := sqrtEulerConst_sub_sum_le (M := 1) le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.sqrt_one, div_one] at h
  have h1 : sqrtStepDefect 1 = 1 := by simp [sqrtStepDefect]; norm_num
  linarith

private theorem sum_Icc_one_div_sqrt_add_defect (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (1 / Real.sqrt j + sqrtStepDefect j)) = 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
    unfold sqrtStepDefect
    rw [if_neg (Nat.succ_ne_zero M), Nat.add_sub_cancel]
    ring

/-- Uniform approximation `|(∑_{j=1}^{⌊X/m⌋} 1/√j) − (2√(X/m) − c₀)| ≤ 5√(m/X)` for all `m, X ≥ 1`. -/
private theorem abs_sum_inv_sqrt_div_sub_le {m X : ℕ} (hm : 1 ≤ m) (hX : 1 ≤ X) :
    |(∑ j ∈ Finset.Icc 1 (X / m), 1 / Real.sqrt j) -
        (2 * Real.sqrt ((X : ℝ) / m) - sqrtEulerConst)| ≤
      5 * Real.sqrt ((m : ℝ) / X) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  rcases lt_or_ge X m with hlt | hge
  · have hdiv0 : X / m = 0 := Nat.div_eq_of_lt hlt
    rw [hdiv0]; simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, zero_sub,
      abs_neg]
    have hXm1 : (X : ℝ) / m ≤ 1 := (div_le_one hm0).mpr (by exact_mod_cast hlt.le)
    have hsXm : Real.sqrt ((X : ℝ) / m) ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hXm1
    have hmX1 : 1 ≤ (m : ℝ) / X := (one_le_div hX0).mpr (by exact_mod_cast hlt.le)
    have hsmX : 1 ≤ Real.sqrt ((m : ℝ) / X) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hmX1
    have hc0 := one_le_sqrtEulerConst
    have hc3 := sqrtEulerConst_le_three
    have hs0 : 0 ≤ Real.sqrt ((X : ℝ) / m) := Real.sqrt_nonneg _
    rw [abs_le]
    constructor <;> linarith
  · set M := X / m
    have hM1 : 1 ≤ M := Nat.div_pos hge hm
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have hident : ∑ j ∈ Finset.Icc 1 M, 1 / Real.sqrt j =
        2 * Real.sqrt M - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j := by
      have := sum_Icc_one_div_sqrt_add_defect M
      rw [Finset.sum_add_distrib] at this
      linarith
    have htail_nn : 0 ≤ sqrtEulerConst - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j := by
      have hsub : (Finset.Icc 1 M).sum sqrtStepDefect ≤ sqrtEulerConst :=
        summable_sqrtStepDefect.sum_le_tsum _ fun j _ => sqrtStepDefect_nonneg j
      linarith
    have htail_le := sqrtEulerConst_sub_sum_le hM1
    have hM_le : (M : ℝ) ≤ (X : ℝ) / m :=
      (le_div_iff₀ hm0).mpr (by exact_mod_cast Nat.div_mul_le_self X m)
    have hXm_lt : (X : ℝ) / m < (M : ℝ) + 1 := by
      rw [div_lt_iff₀ hm0]
      have : X < (X / m + 1) * m := by
        rw [add_mul, one_mul, Nat.mul_comm (X / m) m]
        exact Nat.lt_mul_div_succ X hm
      exact_mod_cast this
    have h2M_ge : (X : ℝ) / m ≤ 2 * (M : ℝ) := by linarith [show (1 : ℝ) ≤ M by exact_mod_cast hM1]
    have hinv_M : 1 / Real.sqrt M ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) / X) := by
      have h1 : (M : ℝ)⁻¹ ≤ 2 * ((m : ℝ) / X) := by
        rw [inv_le_iff_one_le_mul₀ hM0]
        have := (div_le_iff₀ hm0).mp h2M_ge
        field_simp; linarith
      have hs := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_inv, Real.sqrt_mul (by norm_num)] at hs
      simpa [one_div] using hs
    have hsqrt2_le : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hinv_M' : 1 / Real.sqrt M ≤ (3 / 2 : ℝ) * Real.sqrt ((m : ℝ) / X) :=
      hinv_M.trans (mul_le_mul_of_nonneg_right hsqrt2_le (Real.sqrt_nonneg _))
    have hgap_nn : 0 ≤ 2 * Real.sqrt ((X : ℝ) / m) - 2 * Real.sqrt M := by
      linarith [Real.sqrt_le_sqrt hM_le]
    have hgap_le : 2 * Real.sqrt ((X : ℝ) / m) - 2 * Real.sqrt M ≤ 1 / Real.sqrt M := by
      have hs1 : Real.sqrt ((X : ℝ) / m) ^ 2 = (X : ℝ) / m := Real.sq_sqrt (by positivity)
      have hs2 : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) := Real.sq_sqrt hM0.le
      have hprod : (Real.sqrt ((X : ℝ) / m) - Real.sqrt M) *
          (Real.sqrt ((X : ℝ) / m) + Real.sqrt M) < 1 := by nlinarith
      have hsum_ge : 2 * Real.sqrt M ≤ Real.sqrt ((X : ℝ) / m) + Real.sqrt M := by
        linarith [Real.sqrt_le_sqrt hM_le]
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hM0)]
      nlinarith [Real.sqrt_le_sqrt hM_le]
    rw [hident]
    have hrew : 2 * Real.sqrt M - (∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j) -
        (2 * Real.sqrt ((X : ℝ) / m) - sqrtEulerConst) =
        (sqrtEulerConst - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j) -
          (2 * Real.sqrt ((X : ℝ) / m) - 2 * Real.sqrt M) := by ring
    rw [hrew]
    calc |(sqrtEulerConst - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j) -
            (2 * Real.sqrt ((X : ℝ) / m) - 2 * Real.sqrt M)|
        ≤ |sqrtEulerConst - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j| +
            |2 * Real.sqrt ((X : ℝ) / m) - 2 * Real.sqrt M| := abs_sub _ _
      _ = (sqrtEulerConst - ∑ j ∈ Finset.Icc 1 M, sqrtStepDefect j) +
            (2 * Real.sqrt ((X : ℝ) / m) - 2 * Real.sqrt M) := by
          rw [abs_of_nonneg htail_nn, abs_of_nonneg hgap_nn]
      _ ≤ 2 / Real.sqrt M + 1 / Real.sqrt M := add_le_add htail_le hgap_le
      _ = 3 * (1 / Real.sqrt M) := by ring
      _ ≤ 3 * ((3 / 2 : ℝ) * Real.sqrt ((m : ℝ) / X)) :=
          mul_le_mul_of_nonneg_left hinv_M' (by norm_num)
      _ ≤ 5 * Real.sqrt ((m : ℝ) / X) := by nlinarith [Real.sqrt_nonneg ((m : ℝ) / X)]

/-- Exact finite summation by parts of `⌊n / m⌋ (1/√n − 1/√(n + 1))`. -/
private theorem sum_Icc_floor_div_mul_sqrt_diff {m : ℕ} (_hm : 1 ≤ m) (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X,
        ((n / m : ℕ) : ℝ) * (1 / Real.sqrt n - 1 / Real.sqrt ((n : ℝ) + 1)) =
      (1 / Real.sqrt m) * (∑ j ∈ Finset.Icc 1 (X / m), 1 / Real.sqrt j) -
        ((X / m : ℕ) : ℝ) / Real.sqrt ((X : ℝ) + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1), ih]
    by_cases hdvd : m ∣ X + 1
    · have hsucc : (X + 1) / m = X / m + 1 := Nat.succ_div_of_dvd hdvd
      have hmul : m * (X / m + 1) = X + 1 := by rw [← hsucc]; exact Nat.mul_div_cancel' hdvd
      have hmR : Real.sqrt m * Real.sqrt ((X / m + 1 : ℕ) : ℝ) = Real.sqrt ((X + 1 : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg m), ← Nat.cast_mul, hmul]
      rw [hsucc, Finset.sum_Icc_succ_top (Nat.succ_pos (X / m))]
      have hprod : (1 / Real.sqrt m) * (1 / Real.sqrt ((X / m + 1 : ℕ) : ℝ)) =
          1 / Real.sqrt ((X + 1 : ℕ) : ℝ) := by rw [← hmR]; ring
      rw [mul_add, hprod]
      push_cast; ring
    · have hsucc : (X + 1) / m = X / m := Nat.succ_div_of_not_dvd hdvd
      rw [hsucc]
      push_cast; ring

/-- Strictly positive leading constant `I_r = c₀ ∑_{a b = r} √a μ(b) = c₀ √r ∏_{p ∣ r} (1 − p^{−1/2})`. -/
noncomputable def twinHalfSlope (r : ℕ) : ℝ :=
  sqrtEulerConst * ∑ x ∈ r.divisorsAntidiagonal, Real.sqrt (x.1 : ℝ) * moebiusReal x.2

private noncomputable def invSqrtArith : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else (Real.sqrt (d : ℝ))⁻¹, by simp⟩

private theorem isMultiplicative_invSqrtArith : invSqrtArith.IsMultiplicative := by
  refine ⟨by simp [invSqrtArith], fun {m n} _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [invSqrtArith]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [invSqrtArith]
  simp only [invSqrtArith, ArithmeticFunction.coe_mk, hm.ne', hn.ne', Nat.mul_ne_zero hm.ne' hn.ne',
    ↓reduceIte, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), mul_inv]

theorem twinHalfSlope_pos {r : ℕ} (hr : 1 < r) : 0 < twinHalfSlope r := by
  unfold twinHalfSlope
  refine mul_pos (by linarith [one_le_sqrtEulerConst]) ?_
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => Real.sqrt (a : ℝ) * moebiusReal b)]
  have hfactor : ∑ b ∈ r.divisors, Real.sqrt ((r / b : ℕ) : ℝ) * moebiusReal b =
      Real.sqrt r * ∑ b ∈ r.divisors, moebiusReal b * invSqrtArith b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
    have hsb0 : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by exact_mod_cast hb0)
    have hmul : (r / b) * b = r := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hb)
    have hsq : Real.sqrt ((r / b : ℕ) : ℝ) * Real.sqrt b = Real.sqrt r := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, hmul]
    have hdiv : Real.sqrt ((r / b : ℕ) : ℝ) = Real.sqrt r * (Real.sqrt b)⁻¹ := by
      rw [← hsq, mul_assoc, mul_inv_cancel₀ hsb0.ne', mul_one]
    simp only [invSqrtArith, ArithmeticFunction.coe_mk, hb0.ne', ↓reduceIte, hdiv]
    ring
  rw [hfactor]
  refine mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < r))) ?_
  set R := ∏ p ∈ r.primeFactors, p
  have hprimes : ∀ p ∈ r.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hsq : Squarefree R := squarefree_prod_primes hprimes
  have hR_dvd_r : R ∣ r :=
    Finset.prod_primes_dvd r (fun p hp => (hprimes p hp).prime)
      (fun _ hp => Nat.dvd_of_mem_primeFactors hp)
  have hsub : R.divisors ⊆ r.divisors :=
    Nat.divisors_subset_of_dvd (by omega) hR_dvd_r
  have hred : ∑ b ∈ r.divisors, moebiusReal b * invSqrtArith b =
      ∑ b ∈ R.divisors, (μ b : ℝ) * invSqrtArith b := by
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp [moebiusReal]
    · intro b hbr hbR
      have hnsq : ¬ Squarefree b := by
        intro hsqb
        apply hbR
        rw [Nat.mem_divisors]
        refine ⟨?_, Finset.prod_ne_zero_iff.mpr fun p hp => (hprimes p hp).ne_zero⟩
        have hbp : b = ∏ p ∈ b.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsqb).symm
        rw [hbp]
        refine Finset.prod_primes_dvd R
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) fun p hp => ?_
        exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hp,
            (Nat.dvd_of_mem_primeFactors hp).trans (Nat.dvd_of_mem_divisors hbr), by omega⟩)
      simp [moebiusReal, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
  rw [hred, ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    invSqrtArith isMultiplicative_invSqrtArith hsq, Nat.primeFactors_prod hprimes]
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprimes p hp).two_le
  have hsp : (1 : ℝ) < Real.sqrt p := by
    rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  simp only [invSqrtArith, ArithmeticFunction.coe_mk, (hprimes p hp).ne_zero, ↓reduceIte]
  linarith [inv_lt_one_of_one_lt₀ hsp]

private theorem sum_antidiagonal_moebiusReal_eq_zero {r : ℕ} (hr : 1 < r) :
    ∑ x ∈ r.divisorsAntidiagonal, moebiusReal x.2 = 0 := by
  have h1 : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) r = (1 : ArithmeticFunction ℝ) r := by
    rw [mul_comm, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, if_neg hr.ne'] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : x.1 ≠ 0 :=
    (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne'
  simp [moebiusReal, hx1]

/-- **Unified lower bound for any positive-weight dilation Dirichlet form at half damping.**
For every modulus `r > 1`, finite set `S` of positive integers, and `X ≥ 1`, let
`H_X(S) = ∑_{d ∈ S, d ≤ X} 1 / d` and `E_r = 2 B_r + 10 ∑_{a ∣ r} a`. Whenever
`E_r ≤ I_r H_X(S)`,
`signedDilationDirichletForm 1 (1/2) S r hr ≥ 4 (I_r H_X(S) − E_r)² / (1 + log X)`. -/
theorem signedDilationDirichletForm_unit_half_ge {r : ℕ} (hr : 1 < r) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d) {X : ℕ} (hX : 1 ≤ X)
    (hpos : 2 * pmRamanujanPrimitiveBound r + 10 * (∑ a ∈ r.divisors, (a : ℝ)) ≤
      twinHalfSlope r * ∑ d ∈ S.filter (· ≤ X), (1 : ℝ) / d) :
    4 * (twinHalfSlope r * (∑ d ∈ S.filter (· ≤ X), (1 : ℝ) / d) -
        (2 * pmRamanujanPrimitiveBound r + 10 * ∑ a ∈ r.divisors, (a : ℝ))) ^ 2 /
      (1 + Real.log X) ≤
      signedDilationDirichletForm (fun _ => 1) (1 / 2) S r hr := by
  set S_X := S.filter (· ≤ X)
  set δ : ℕ → ℝ := fun n => 1 / Real.sqrt n - 1 / Real.sqrt ((n : ℝ) + 1)
  set Ψ : ℕ → ℝ := signedDilationPrimitive (fun _ => 1) (1 / 2) S r
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
    (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
  have hSX_sub : S_X ⊆ Finset.Icc 1 X := by
    intro d hd
    obtain ⟨hdS, hdX⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨hS d hdS, hdX⟩
  have hsum_sqrt_SX : ∑ d ∈ S_X, 1 / Real.sqrt d ≤ 2 * Real.sqrt X :=
    (Finset.sum_le_sum_of_subset_of_nonneg hSX_sub fun _ _ _ => by positivity).trans
      (RHTower.sum_one_div_sqrt_le X)
  have hΨ_trunc : ∀ n ∈ Finset.Icc 1 X,
      Ψ n = ∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (n / d)).re := by
    intro n hn
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    dsimp [Ψ, signedDilationPrimitive]
    rw [← Finset.sum_subset (Finset.filter_subset (· ≤ X) S)]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [one_mul, Real.rpow_neg (Nat.cast_nonneg d), ← Real.sqrt_eq_rpow, one_div]
    · intro d hdS hdSX
      have hgt : X < d := not_le.mp fun hle => hdSX (Finset.mem_filter.mpr ⟨hdS, hle⟩)
      have hdiv0 : n / d = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt hnX hgt)
      simp [hdiv0, pmRamanujanPrimitive]
  have hpair : ∑ n ∈ Finset.Icc 1 X, Ψ n * δ n =
      (∑ d ∈ S_X, (1 / Real.sqrt d) *
        ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
          ((1 / Real.sqrt (d * x.1 : ℕ)) * ∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j)) -
      (1 / Real.sqrt ((X : ℝ) + 1)) *
        ∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (X / d)).re := by
    calc ∑ n ∈ Finset.Icc 1 X, Ψ n * δ n
        = ∑ n ∈ Finset.Icc 1 X,
            (∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (n / d)).re) * δ n :=
          Finset.sum_congr rfl fun n hn => by rw [hΨ_trunc n hn]
      _ = ∑ d ∈ S_X, (1 / Real.sqrt d) *
            ∑ n ∈ Finset.Icc 1 X, (pmRamanujanPrimitive r (n / d)).re * δ n := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hd1 : 1 ≤ d := hS d (Finset.mem_filter.mp hd).1
          have hexp : ∑ n ∈ Finset.Icc 1 X, (pmRamanujanPrimitive r (n / d)).re * δ n =
              ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
                ∑ n ∈ Finset.Icc 1 X, ((n / (d * x.1) : ℕ) : ℝ) * δ n := by
            simp_rw [pmRamanujanPrimitive_re_eq_floor, Finset.sum_mul, Nat.div_div_eq_div_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
          rw [hexp]
          have hstep : ∀ x ∈ r.divisorsAntidiagonal,
              ∑ n ∈ Finset.Icc 1 X, ((n / (d * x.1) : ℕ) : ℝ) * δ n =
                (1 / Real.sqrt (d * x.1 : ℕ)) *
                  (∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j) -
                ((X / (d * x.1) : ℕ) : ℝ) / Real.sqrt ((X : ℝ) + 1) := by
            intro x hx
            have hx1 : 1 ≤ x.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
            exact sum_Icc_floor_div_mul_sqrt_diff (Nat.mul_pos hd1 hx1) X
          rw [Finset.sum_congr rfl fun x hx => by rw [hstep x hx],
            pmRamanujanPrimitive_re_eq_floor r (X / d)]
          simp_rw [mul_sub, Finset.sum_sub_distrib, Nat.div_div_eq_div_mul, Finset.mul_sum]
          rw [mul_sub]
          simp_rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun x _ => by ring
  have hmain_cancel : ∀ d ∈ S_X,
      ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
        ((1 / Real.sqrt (d * x.1 : ℕ)) *
          (2 * Real.sqrt ((X : ℝ) / (d * x.1 : ℕ)) - sqrtEulerConst)) =
        -(1 / Real.sqrt d) * twinHalfSlope r := by
    intro d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hS d (Finset.mem_filter.mp hd).1
    have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    have hterm : ∀ x ∈ r.divisorsAntidiagonal,
        (x.1 : ℝ) * moebiusReal x.2 *
          ((1 / Real.sqrt (d * x.1 : ℕ)) *
            (2 * Real.sqrt ((X : ℝ) / (d * x.1 : ℕ)) - sqrtEulerConst)) =
          (2 * Real.sqrt X / (d : ℝ)) * moebiusReal x.2 -
            (1 / Real.sqrt d) * (sqrtEulerConst * (Real.sqrt (x.1 : ℝ) * moebiusReal x.2)) := by
      intro x hx
      have hx0 : (0 : ℝ) < (x.1 : ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
      have hsx0 : 0 < Real.sqrt (x.1 : ℝ) := Real.sqrt_pos.mpr hx0
      rw [Nat.cast_mul, Real.sqrt_mul hd0.le, Real.sqrt_div hX0.le, Real.sqrt_mul hd0.le]
      field_simp
      rw [Real.sq_sqrt hx0.le]
      ring_nf
      rw [Real.sq_sqrt hd0.le]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_antidiagonal_moebiusReal_eq_zero hr, mul_zero, zero_sub, ← Finset.mul_sum,
      ← Finset.mul_sum, twinHalfSlope, neg_mul]
  have habs_pairing : twinHalfSlope r * (∑ d ∈ S_X, (1 : ℝ) / d) -
      (2 * pmRamanujanPrimitiveBound r + 10 * ∑ a ∈ r.divisors, (a : ℝ)) ≤
      |∑ n ∈ Finset.Icc 1 X, Ψ n * δ n| := by
    set mainTerm := -twinHalfSlope r * ∑ d ∈ S_X, (1 : ℝ) / d
    have hmain_id : ∑ d ∈ S_X, (1 / Real.sqrt d) * (-(1 / Real.sqrt d) * twinHalfSlope r) =
        mainTerm := by
      dsimp [mainTerm]
      rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hS d (Finset.mem_filter.mp hd).1
      have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
      field_simp
      rw [Real.sq_sqrt hd0.le]
      ring
    have herr1 : |(∑ d ∈ S_X, (1 / Real.sqrt d) *
          ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
            ((1 / Real.sqrt (d * x.1 : ℕ)) *
              ∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j)) - mainTerm| ≤
        10 * ∑ a ∈ r.divisors, (a : ℝ) := by
      rw [← hmain_id, ← Finset.sum_sub_distrib]
      calc |∑ d ∈ S_X, ((1 / Real.sqrt d) *
              (∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
                ((1 / Real.sqrt (d * x.1 : ℕ)) *
                  ∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j)) -
              (1 / Real.sqrt d) * (-(1 / Real.sqrt d) * twinHalfSlope r))|
          ≤ ∑ d ∈ S_X, (1 / Real.sqrt d) *
              ((∑ a ∈ r.divisors, (a : ℝ)) * (5 / Real.sqrt X)) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
            rw [← mul_sub, ← hmain_cancel d hd, ← Finset.sum_sub_distrib, abs_mul,
              abs_of_nonneg (by positivity)]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hd1 : 1 ≤ d := hS d (Finset.mem_filter.mp hd).1
            calc |∑ x ∈ r.divisorsAntidiagonal,
                    ((x.1 : ℝ) * moebiusReal x.2 *
                      ((1 / Real.sqrt (d * x.1 : ℕ)) *
                        ∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j) -
                    (x.1 : ℝ) * moebiusReal x.2 *
                      ((1 / Real.sqrt (d * x.1 : ℕ)) *
                        (2 * Real.sqrt ((X : ℝ) / (d * x.1 : ℕ)) - sqrtEulerConst)))|
                ≤ ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * (5 / Real.sqrt X) := by
                  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
                  have hx1 : 1 ≤ x.1 :=
                    Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
                  have hm0 : (0 : ℝ) < ((d * x.1 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd1 hx1
                  have hsm0 : 0 < Real.sqrt (d * x.1 : ℕ) := Real.sqrt_pos.mpr hm0
                  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul,
                    abs_mul (1 / Real.sqrt (d * x.1 : ℕ)),
                    abs_of_nonneg (Nat.cast_nonneg x.1),
                    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt (d * x.1 : ℕ))]
                  have hμ : |moebiusReal x.2| ≤ 1 := by
                    unfold moebiusReal
                    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := x.2)
                  have hrem := abs_sum_inv_sqrt_div_sub_le (Nat.mul_pos hd1 hx1) hX
                  have hcancel_m : (1 / Real.sqrt (d * x.1 : ℕ)) *
                      (5 * Real.sqrt (((d * x.1 : ℕ) : ℝ) / X)) = 5 / Real.sqrt X := by
                    rw [Real.sqrt_div hm0.le]; field_simp
                  calc (x.1 : ℝ) * |moebiusReal x.2| *
                        ((1 / Real.sqrt (d * x.1 : ℕ)) *
                          |(∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j) -
                            (2 * Real.sqrt ((X : ℝ) / (d * x.1 : ℕ)) - sqrtEulerConst)|)
                      ≤ (x.1 : ℝ) * 1 * ((1 / Real.sqrt (d * x.1 : ℕ)) *
                          (5 * Real.sqrt (((d * x.1 : ℕ) : ℝ) / X))) := by
                        refine mul_le_mul (mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg x.1))
                          (mul_le_mul_of_nonneg_left hrem (by positivity))
                          (by positivity) (by positivity)
                    _ = (x.1 : ℝ) * (5 / Real.sqrt X) := by rw [mul_one, hcancel_m]
              _ = (∑ a ∈ r.divisors, (a : ℝ)) * (5 / Real.sqrt X) := by
                  rw [← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => (a : ℝ))]
        _ = (∑ d ∈ S_X, 1 / Real.sqrt d) * ((5 / Real.sqrt X) * ∑ a ∈ r.divisors, (a : ℝ)) := by
            rw [← Finset.sum_mul]; ring
        _ ≤ (2 * Real.sqrt X) * ((5 / Real.sqrt X) * ∑ a ∈ r.divisors, (a : ℝ)) :=
            mul_le_mul_of_nonneg_right hsum_sqrt_SX (by positivity)
        _ = 10 * ∑ a ∈ r.divisors, (a : ℝ) := by
            have hsX0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX0).ne'
            field_simp; ring
    have herr2 : |(1 / Real.sqrt ((X : ℝ) + 1)) *
          ∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (X / d)).re| ≤
        2 * pmRamanujanPrimitiveBound r := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have h1 : |∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (X / d)).re| ≤
          pmRamanujanPrimitiveBound r * (2 * Real.sqrt X) := by
        calc |∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (X / d)).re|
            ≤ ∑ d ∈ S_X, (1 / Real.sqrt d) * pmRamanujanPrimitiveBound r := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
              rw [abs_mul, abs_of_nonneg (by positivity)]
              exact mul_le_mul_of_nonneg_left
                ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
                (by positivity)
          _ = pmRamanujanPrimitiveBound r * ∑ d ∈ S_X, 1 / Real.sqrt d := by
              rw [← Finset.sum_mul, mul_comm]
          _ ≤ pmRamanujanPrimitiveBound r * (2 * Real.sqrt X) :=
              mul_le_mul_of_nonneg_left hsum_sqrt_SX hB0
      have hs_le : Real.sqrt X ≤ Real.sqrt ((X : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      calc 1 / Real.sqrt ((X : ℝ) + 1) *
            |∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (X / d)).re|
          ≤ 1 / Real.sqrt ((X : ℝ) + 1) * (pmRamanujanPrimitiveBound r * (2 * Real.sqrt X)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / Real.sqrt X * (pmRamanujanPrimitiveBound r * (2 * Real.sqrt X)) :=
            mul_le_mul_of_nonneg_right
              (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hX0) hs_le) (by positivity)
        _ = 2 * pmRamanujanPrimitiveBound r := by
            have hsX0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX0).ne'
            field_simp
    rw [hpair]
    set A := ∑ d ∈ S_X, (1 / Real.sqrt d) *
      ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
        ((1 / Real.sqrt (d * x.1 : ℕ)) * ∑ j ∈ Finset.Icc 1 (X / (d * x.1)), 1 / Real.sqrt j)
    set B := (1 / Real.sqrt ((X : ℝ) + 1)) *
      ∑ d ∈ S_X, (1 / Real.sqrt d) * (pmRamanujanPrimitive r (X / d)).re
    have he1 := (abs_le.mp herr1).2
    have he2 := (abs_le.mp herr2).1
    have hneg : -(A - B) ≥ twinHalfSlope r * (∑ d ∈ S_X, (1 : ℝ) / d) -
        (2 * pmRamanujanPrimitiveBound r + 10 * ∑ a ∈ r.divisors, (a : ℝ)) := by
      dsimp [mainTerm] at he1
      linarith
    exact hneg.trans (neg_le_abs _)
  have hcs : (∑ n ∈ Finset.Icc 1 X, Ψ n * δ n) ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 X, Ψ n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) *
        ((1 + Real.log X) / 4) := by
    have hsplit : ∑ n ∈ Finset.Icc 1 X, Ψ n * δ n =
        ∑ n ∈ Finset.Icc 1 X,
          (Ψ n / Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) *
            (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) * δ n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hs0 : Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) ≠ 0 :=
        (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp
    have hsq1 : ∑ n ∈ Finset.Icc 1 X, (Ψ n / Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 =
        ∑ n ∈ Finset.Icc 1 X, Ψ n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_pow, Real.sq_sqrt (by positivity)]
    have hsq2 : ∑ n ∈ Finset.Icc 1 X, (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) * δ n) ^ 2 ≤
        (1 + Real.log X) / 4 := by
      calc ∑ n ∈ Finset.Icc 1 X, (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) * δ n) ^ 2
          ≤ ∑ n ∈ Finset.Icc 1 X, (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
            have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
            have hsn1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
            have hid : Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) * δ n =
                Real.sqrt ((n : ℝ) + 1) - Real.sqrt n := by
              dsimp [δ]; rw [Real.sqrt_mul hn0.le]; field_simp
            have hstep : Real.sqrt ((n : ℝ) + 1) - Real.sqrt n ≤ 1 / (2 * Real.sqrt n) := by
              have hprod : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) *
                  (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n) = 1 := by
                nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1),
                  Real.sq_sqrt hn0.le]
              have hle : Real.sqrt n ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
              rw [le_div_iff₀ (by positivity)]
              nlinarith
            have hnn : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n := by
              linarith [Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)]
            rw [hid]
            calc (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2
                ≤ (1 / (2 * Real.sqrt n)) ^ 2 := pow_le_pow_left₀ hnn hstep 2
              _ = (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
                  rw [div_pow, mul_pow, Real.sq_sqrt hn0.le]; ring
        _ = (1 / 4 : ℝ) * ∑ n ∈ Finset.Icc 1 X, 1 / (n : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (1 / 4 : ℝ) * (1 + Real.log X) :=
            mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_Icc_one_div_le_one_add_log X) (by norm_num)
        _ = (1 + Real.log X) / 4 := by ring
    rw [hsplit]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    rw [hsq1]
    exact mul_le_mul_of_nonneg_left hsq2 (Finset.sum_nonneg fun _ _ => by positivity)
  have hwin : ∑ n ∈ Finset.Icc 1 X, Ψ n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      signedDilationDirichletForm (fun _ => 1) (1 / 2) S r hr := by
    have hIcc : Finset.Icc 1 X = Finset.Ico 1 (X + 1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc]
    exact sum_Ico_signedDilationPrimitive_sq_le (fun _ => 1) (1 / 2) hS hr le_rfl
  have hlog_pos : 0 < 1 + Real.log X := by
    have : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
    linarith
  have hsq_low : (twinHalfSlope r * (∑ d ∈ S_X, (1 : ℝ) / d) -
      (2 * pmRamanujanPrimitiveBound r + 10 * ∑ a ∈ r.divisors, (a : ℝ))) ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 X, Ψ n * δ n) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith) habs_pairing 2
    rwa [sq_abs] at h
  rw [div_le_iff₀ hlog_pos]
  have htot := hsq_low.trans (hcs.trans (mul_le_mul_of_nonneg_right hwin (by positivity)))
  linarith

private theorem log_succ_le_sum_Icc_one_div (N : ℕ) :
    Real.log ((N : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 2) / ((N : ℝ) + 1) by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at hlog
      have hrw : ((N : ℝ) + 2) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by field_simp; ring
      rwa [hrw] at hlog
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    linarith

private theorem tendsto_quad_div_log_atTop {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E) (u : ℕ → ℝ)
    (hu : ∀ X : ℕ, c * Real.log ((X : ℝ) + 1) ≤ u X) :
    Tendsto (fun X : ℕ => 4 * (u X - E) ^ 2 / (1 + Real.log X)) atTop atTop := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop.mpr fun B => ?_
  filter_upwards [hlog.eventually_gt_atTop (max 1 (2 * E / c + 2 * |B| / c ^ 2)),
    eventually_ge_atTop 2] with X hlg hX2
  have hlog1 : 1 < Real.log X := lt_of_le_of_lt (le_max_left _ _) hlg
  have hlog2 : 2 * E / c + 2 * |B| / c ^ 2 < Real.log X :=
    lt_of_le_of_lt (le_max_right _ _) hlg
  have hsucc : Real.log X ≤ Real.log ((X : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hE_lt : E < (c / 2) * Real.log X := by
    have hnn : 0 ≤ 2 * |B| / c ^ 2 := by positivity
    have : 2 * E / c < Real.log X := by linarith
    have := (div_lt_iff₀ hc).mp this
    linarith
  have hnum : (c / 2) * Real.log X ≤ u X - E := by
    have := hu X
    nlinarith
  have hden : 1 + Real.log X ≤ 2 * Real.log X := by linarith
  have h1 : (c ^ 2 / 2) * Real.log X ≤ 4 * (u X - E) ^ 2 / (1 + Real.log X) := by
    have hsq := pow_le_pow_left₀ (by positivity) hnum 2
    have hdiv : 4 * ((c / 2) * Real.log X) ^ 2 / (2 * Real.log X) ≤
        4 * (u X - E) ^ 2 / (1 + Real.log X) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hden
    have hid : 4 * ((c / 2) * Real.log X) ^ 2 / (2 * Real.log X) = (c ^ 2 / 2) * Real.log X := by
      field_simp; ring
    rwa [hid] at hdiv
  have h2 : B ≤ (c ^ 2 / 2) * Real.log X := by
    have hnn : 0 ≤ 2 * E / c := by positivity
    have : 2 * |B| / c ^ 2 < Real.log X := by linarith
    have := (div_lt_iff₀ (sq_pos_of_pos hc)).mp this
    linarith [le_abs_self B]
  exact h2.trans h1

/-- **Size-truncated parity-twin divergence at half damping.**
For every modulus `r > 1`, `sizeTwinHypercubeForm hr (1 / 2) D → +∞` as `D → ∞`. -/
theorem tendsto_sizeTwinHypercubeForm_half_atTop {r : ℕ} (hr : 1 < r) :
    Tendsto (fun D : ℕ => sizeTwinHypercubeForm hr (1 / 2) D) atTop atTop := by
  have hI0 : 0 < twinHalfSlope r := twinHalfSlope_pos hr
  set E := 2 * pmRamanujanPrimitiveBound r + 10 * ∑ a ∈ r.divisors, (a : ℝ)
  have hE0 : 0 ≤ E := by
    have : 0 ≤ pmRamanujanPrimitiveBound r :=
      (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
    positivity
  set u : ℕ → ℝ := fun D =>
    twinHalfSlope r * ∑ d ∈ (Finset.Icc 1 D).filter (· ≤ D), (1 : ℝ) / d
  have hu : ∀ D : ℕ, twinHalfSlope r * Real.log ((D : ℝ) + 1) ≤ u D := fun D => by
    dsimp [u]
    have hfil : (Finset.Icc 1 D).filter (· ≤ D) = Finset.Icc 1 D :=
      Finset.filter_true_of_mem fun _ hd => (Finset.mem_Icc.mp hd).2
    rw [hfil]
    exact mul_le_mul_of_nonneg_left (log_succ_le_sum_Icc_one_div D) hI0.le
  have hlog : Tendsto (fun D : ℕ => Real.log ((D : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_quad_div_log_atTop hI0 hE0 u hu)
  filter_upwards [hlog.eventually_gt_atTop (E / twinHalfSlope r), eventually_ge_atTop 1] with D hlg hD1
  have hpos : E ≤ u D := by
    have := (div_lt_iff₀ hI0).mp hlg
    linarith [hu D]
  exact signedDilationDirichletForm_unit_half_ge hr (fun _ hd => (Finset.mem_Icc.mp hd).1) hD1 hpos

/-! ## §3. Prime-divisor parity-twin divergence along `roughPrimeProd` -/

theorem squarefree_roughPrimeProd (r X : ℕ) : Squarefree (roughPrimeProd r X) :=
  squarefree_prod_primes fun _ hp => (Finset.mem_filter.mp hp).2

theorem coprime_roughPrimeProd {r : ℕ} (hr : 1 < r) (X : ℕ) :
    Nat.Coprime (roughPrimeProd r X) r := by
  refine Nat.Coprime.prod_left fun p hp => ?_
  obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
  have hpr : r < p := (Finset.mem_Ioc.mp hpI).1
  exact (Nat.coprime_or_dvd_of_prime hpp r).resolve_right
    fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

private theorem sum_inv_divisors_roughPrimeProd_ge {r : ℕ} (_hr : 1 < r) (X : ℕ) :
    let R_r := ∏ p ∈ (Finset.Icc 1 r).filter Nat.Prime, p
    Real.log ((X : ℝ) + 1) / (2 * ∑ g ∈ R_r.divisors, (1 : ℝ) / g) ≤
      ∑ d ∈ (roughPrimeProd r X).divisors.filter (· ≤ X), (1 : ℝ) / d := by
  classical
  intro R_r
  have hR_primes : ∀ p ∈ (Finset.Icc 1 r).filter Nat.Prime, p.Prime :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hR_ne : R_r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hR_primes p hp).ne_zero
  have hP_primes : ∀ p ∈ (Finset.Ioc r X).filter Nat.Prime, p.Prime :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hP_ne : roughPrimeProd r X ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hP_primes p hp).ne_zero
  set G := R_r.divisors
  set D_X := (roughPrimeProd r X).divisors.filter (· ≤ X)
  set Sq := (Finset.Icc 1 X).filter Squarefree
  have hG_pos : 0 < ∑ g ∈ G, (1 : ℝ) / g := by
    have h1 : (1 : ℕ) ∈ G := Nat.one_mem_divisors.mpr hR_ne
    refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ) / (1 : ℕ))
      (Finset.single_le_sum (f := fun g : ℕ => (1 : ℝ) / g) (fun _ _ => by positivity) h1)
  set split : ℕ → ℕ × ℕ := fun l => (Nat.gcd l R_r, l / Nat.gcd l R_r)
  have hmaps : ∀ l ∈ Sq, split l ∈ G ×ˢ D_X := by
    intro l hl
    obtain ⟨hlI, hsq_l⟩ := Finset.mem_filter.mp hl
    obtain ⟨hl1, hlX⟩ := Finset.mem_Icc.mp hlI
    set g := Nat.gcd l R_r
    set d := l / g
    have hg_dvd_l : g ∣ l := Nat.gcd_dvd_left l R_r
    have hg_dvd_R : g ∣ R_r := Nat.gcd_dvd_right l R_r
    have hgd : g * d = l := Nat.mul_div_cancel' hg_dvd_l
    have hsq_d : Squarefree d := hsq_l.squarefree_of_dvd ⟨g, by rw [mul_comm, hgd]⟩
    have hd_le_X : d ≤ X := (Nat.div_le_self l g).trans hlX
    have hd_dvd_P : d ∣ roughPrimeProd r X := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq_d]
      refine Finset.prod_primes_dvd (roughPrimeProd r X)
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hpl : p ∣ l := hpd.trans ⟨g, by rw [mul_comm, hgd]⟩
      have hpX : p ≤ X := (Nat.le_of_dvd hl1 hpl).trans hlX
      have hpr : r < p := by
        by_contra hle
        have hpR : p ∣ R_r := Finset.dvd_prod_of_mem _
          (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.pos, not_lt.mp hle⟩, hpp⟩)
        have hpg : p ∣ g := Nat.dvd_gcd hpl hpR
        have hp2 : p * p ∣ l := by
          rw [← hgd]; exact mul_dvd_mul hpg hpd
        have hu := Nat.isUnit_iff.mp (hsq_l p hp2)
        have := hpp.two_le
        omega
      exact Finset.dvd_prod_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpr, hpX⟩, hpp⟩)
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hg_dvd_R, hR_ne⟩,
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd_dvd_P, hP_ne⟩, hd_le_X⟩⟩
  have hinj : Set.InjOn split Sq := by
    intro l₁ _ l₂ _ heq
    have h1 := congr_arg Prod.fst heq
    have h2 := congr_arg Prod.snd heq
    dsimp [split] at h1 h2
    calc l₁ = Nat.gcd l₁ R_r * (l₁ / Nat.gcd l₁ R_r) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      _ = Nat.gcd l₂ R_r * (l₂ / Nat.gcd l₂ R_r) := by rw [h2, h1]
      _ = l₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hsq_le : ∑ l ∈ Sq, (1 : ℝ) / l ≤
      (∑ g ∈ G, (1 : ℝ) / g) * ∑ d ∈ D_X, (1 : ℝ) / d := by
    have hterm : ∑ l ∈ Sq, (1 : ℝ) / l =
        ∑ l ∈ Sq, (fun p : ℕ × ℕ => ((1 : ℝ) / p.1) * ((1 : ℝ) / p.2)) (split l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp [split]
      have hmul : Nat.gcd l R_r * (l / Nat.gcd l R_r) = l :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      conv_lhs => rw [← hmul]
      push_cast; ring
    rw [hterm, ← Finset.sum_image
      (f := fun p : ℕ × ℕ => ((1 : ℝ) / p.1) * ((1 : ℝ) / p.2)) hinj]
    calc ∑ p ∈ Sq.image split, ((1 : ℝ) / p.1) * ((1 : ℝ) / p.2)
        ≤ ∑ p ∈ G ×ˢ D_X, ((1 : ℝ) / p.1) * ((1 : ℝ) / p.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => by obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx; exact hmaps l hl)
            (fun _ _ _ => by positivity)
      _ = (∑ g ∈ G, (1 : ℝ) / g) * ∑ d ∈ D_X, (1 : ℝ) / d := by
          rw [Finset.sum_product]
          dsimp only
          rw [← Finset.sum_mul_sum]
  have hharm := (log_succ_le_sum_Icc_one_div X).trans
    (RHTower.Sieve.sum_inv_le_two_mul_sum_inv_squarefree X)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Prime-divisor parity-twin divergence at half damping (`ε = 1/2`) along `roughPrimeProd`.**
For every modulus `r > 1`, `hypercubeTwinDilationDirichletForm (1 / 2) (roughPrimeProd r X) r hr → +∞`
as `X → ∞`. -/
theorem tendsto_hypercubeTwinDilationDirichletForm_half_roughPrimeProd {r : ℕ} (hr : 1 < r) :
    Tendsto (fun X : ℕ => hypercubeTwinDilationDirichletForm (1 / 2) (roughPrimeProd r X) r hr)
      atTop atTop := by
  set R_r := ∏ p ∈ (Finset.Icc 1 r).filter Nat.Prime, p
  have hR_ne : R_r ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ hp => (Finset.mem_filter.mp hp).2.ne_zero
  have hG_pos : 0 < ∑ g ∈ R_r.divisors, (1 : ℝ) / g :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ) / (1 : ℕ))
      (Finset.single_le_sum (f := fun g : ℕ => (1 : ℝ) / g) (fun _ _ => by positivity)
        (Nat.one_mem_divisors.mpr hR_ne))
  have hI0 : 0 < twinHalfSlope r := twinHalfSlope_pos hr
  set c := twinHalfSlope r / (2 * ∑ g ∈ R_r.divisors, (1 : ℝ) / g)
  have hc0 : 0 < c := by positivity
  set E := 2 * pmRamanujanPrimitiveBound r + 10 * ∑ a ∈ r.divisors, (a : ℝ)
  have hE0 : 0 ≤ E := by
    have : 0 ≤ pmRamanujanPrimitiveBound r :=
      (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
    positivity
  set u : ℕ → ℝ := fun X =>
    twinHalfSlope r * ∑ d ∈ (roughPrimeProd r X).divisors.filter (· ≤ X), (1 : ℝ) / d
  have hu : ∀ X : ℕ, c * Real.log ((X : ℝ) + 1) ≤ u X := fun X => by
    dsimp [u, c]
    have hge := sum_inv_divisors_roughPrimeProd_ge hr X
    have hmul := mul_le_mul_of_nonneg_left hge hI0.le
    calc twinHalfSlope r / (2 * ∑ g ∈ R_r.divisors, (1 : ℝ) / g) * Real.log ((X : ℝ) + 1)
        = twinHalfSlope r *
            (Real.log ((X : ℝ) + 1) / (2 * ∑ g ∈ R_r.divisors, (1 : ℝ) / g)) := by ring
      _ ≤ u X := hmul
  have hlog : Tendsto (fun X : ℕ => Real.log ((X : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_quad_div_log_atTop hc0 hE0 u hu)
  filter_upwards [hlog.eventually_gt_atTop (E / c), eventually_ge_atTop 1] with X hlg hX1
  have hpos : E ≤ u X := by
    have := (div_lt_iff₀ hc0).mp hlg
    linarith [hu X]
  exact signedDilationDirichletForm_unit_half_ge hr
    (fun _ hd => Nat.pos_of_mem_divisors hd) hX1 hpos

/-- **Unboundedness of the parity-twin hypercube form at half damping (`ε = 1/2`).**
For every modulus `r > 1`, `hypercubeTwinDilationDirichletForm (1 / 2) P r hr` is unbounded over
squarefree `P` coprime to `r`. -/
theorem not_bddAbove_hypercubeTwinDilationDirichletForm_half {r : ℕ} (hr : 1 < r) :
    ¬ BddAbove ((fun P => hypercubeTwinDilationDirichletForm (1 / 2) P r hr) ''
      {P : ℕ | Squarefree P ∧ Nat.Coprime P r}) := by
  rintro ⟨C, hC⟩
  obtain ⟨X, hXC⟩ :=
    (tendsto_hypercubeTwinDilationDirichletForm_half_roughPrimeProd hr).eventually_gt_atTop C
      |>.exists
  exact absurd (hC ⟨roughPrimeProd r X,
    ⟨squarefree_roughPrimeProd r X, coprime_roughPrimeProd hr X⟩, rfl⟩) (not_le.mpr hXC)

/-- **Half-damping sign-separation theorem (`ε = 1/2`, `σ = 1`).**
For every modulus `r > 1`, the size-truncated Möbius hypercube form is uniformly bounded in `D`,
whereas both the size-truncated `+1` parity twin and the prime-divisor `+1` parity twin diverge to
`+∞`. -/
theorem half_damping_sign_split {r : ℕ} (hr : 1 < r) :
    (∃ B : ℝ, ∀ D : ℕ, sizeHypercubeForm hr (1 / 2) D ≤ B) ∧
      Tendsto (fun D : ℕ => sizeTwinHypercubeForm hr (1 / 2) D) atTop atTop ∧
      Tendsto (fun X : ℕ => hypercubeTwinDilationDirichletForm (1 / 2) (roughPrimeProd r X) r hr)
        atTop atTop :=
  ⟨sizeHypercubeForm_half_bounded hr, tendsto_sizeTwinHypercubeForm_half_atTop hr,
    tendsto_hypercubeTwinDilationDirichletForm_half_roughPrimeProd hr⟩

end GaloisForLFunctions.SignedSuccessorArithmetic

