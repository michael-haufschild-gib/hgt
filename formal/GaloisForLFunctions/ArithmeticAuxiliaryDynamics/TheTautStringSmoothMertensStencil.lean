import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheLogarithmicPlancherelVariationOfMertens

/-!
# The taut-string smooth Mertens stencil

Combining the logarithmic Mellin–Plancherel `L²` increment bound and greedy dyadic Haar chaining
with a dyadic Bertrand smooth-product jump placement produces, right of any zero-free abscissa
`Θ ∈ [1/2, 1)`, an integer coefficient sequence `b : ℕ → ℤ` supported in `[1, 2 T]` such that:

* `b 1 = 1`, `b 2 = -1`, and every active letter `k ≥ 2` satisfies `¬ 4 ∣ k` with all odd
  prime-power divisors `Q = q^e ∣ k` bounded by `C_d y`;
* the `ℓ¹` mass `∑_{k ≤ 2 T} |b k|` is controlled by
  `(1 + log T)^3 y^{1 + 2 ε} T^{2 Θ - 1 + 2 ε} + (1 + log T) T / y + T^{Θ + ε}`;
* the partial sums `B(x) = ∑_{1 ≤ k ≤ x} b k` approximate `M(x)` within
  `O_d(1 / y + T^{-(1 - Θ - ε)}) x` uniformly for all `x ≥ 1`.
-/

open Complex MeasureTheory Filter Finset Topology
open scoped Classical
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-! ### Part 1: Dyadic Bertrand smooth jump placement -/

/-- Lower threshold multiplier `4 (d + 4)^d` for `d`-factor smooth jump placement. -/
def smoothJumpBase (d : ℕ) : ℕ := 4 * (d + 4) ^ d

/-- Uniform prime-power factor bound multiplier `max (4 (d + 4)^d) 2^(d + 3)`. -/
def smoothJumpPrimeBound (d : ℕ) : ℕ := max (smoothJumpBase d) (2 ^ (d + 3))

/-- Relative shift width multiplier `(4 d + 5) 2^(d² + d)`. -/
def smoothJumpWidth (d : ℕ) : ℝ :=
  ((4 * d + 5 : ℕ) : ℝ) * ((2 ^ (d * d + d) : ℕ) : ℝ)

theorem smoothJumpBase_ge_sixteen {d : ℕ} (hd : 1 ≤ d) : 16 ≤ smoothJumpBase d := by
  unfold smoothJumpBase
  have h1 : 5 ^ 1 ≤ (d + 4) ^ d :=
    le_trans (Nat.pow_le_pow_left (by omega) 1) (Nat.pow_le_pow_right (by omega) hd)
  omega

theorem smoothJumpWidth_pos (d : ℕ) : 0 < smoothJumpWidth d := by
  unfold smoothJumpWidth
  positivity

/-- For `z ∈ [4 (d + 4)^d y, y^(d + 1)]`, there is an integer `k > z` within relative distance
`O_d(1 / y)` of `z` such that `¬ 4 ∣ k` and every prime power dividing `k` is at most `C_d y`. -/
theorem exists_bertrand_smooth_jump {d y z : ℕ} (hd : 1 ≤ d) (hy : 4 * d + 5 ≤ y)
    (hz_lo : smoothJumpBase d * y ≤ z) (hz_hi : z ≤ y ^ (d + 1)) :
    ∃ k : ℕ, z < k ∧
      (k : ℝ) ≤ (z : ℝ) * (1 + smoothJumpWidth d / (y : ℝ)) ∧
      3 ≤ k ∧ ¬ 4 ∣ k ∧
      ∀ q e : ℕ, q.Prime → 1 ≤ e → q ^ e ∣ k → q ^ e ≤ smoothJumpPrimeBound d * y := by
  classical
  have hy_pos : 0 < y := by omega
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  set U : ℕ := z / (4 * y)
  have hU_lo : (d + 4) ^ d ≤ U := by
    refine (Nat.le_div_iff_mul_le (by omega : 0 < 4 * y)).mpr ?_
    simpa [smoothJumpBase, mul_assoc, mul_comm, mul_left_comm] using hz_lo
  have hU_hi : U ≤ y ^ d := by
    refine Nat.div_le_of_le_mul ?_
    calc z ≤ y ^ (d + 1) := hz_hi
      _ = y * y ^ d := by rw [pow_succ']
      _ ≤ (4 * y) * y ^ d := Nat.mul_le_mul_right _ (by omega)
  set S_root := (range (y + 1)).filter fun u => u ^ d ≤ U
  have hd4_mem : d + 4 ∈ S_root :=
    mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hU_lo⟩
  set u₀ : ℕ := S_root.max' ⟨d + 4, hd4_mem⟩
  have hu₀_mem : u₀ ∈ S_root := max'_mem S_root ⟨d + 4, hd4_mem⟩
  have hu₀_le_y : u₀ ≤ y := by
    have := (mem_filter.mp hu₀_mem).1
    rw [Finset.mem_range] at this
    omega
  have hu₀_pow : u₀ ^ d ≤ U := (mem_filter.mp hu₀_mem).2
  have hu₀_ge : d + 4 ≤ u₀ := le_max' S_root (d + 4) hd4_mem
  have hU_lt_succ : U < (u₀ + 1) ^ d := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hu₀_le_y with heq | hlt
    · rw [heq] at hle
      have hgt : y ^ d < (y + 1) ^ d := Nat.pow_lt_pow_left (by omega) (by omega)
      omega
    · have hmem : u₀ + 1 ∈ S_root :=
        mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hle⟩
      have := le_max' S_root (u₀ + 1) hmem
      omega
  have hex_p : ∀ i : ℕ, ∃ p : ℕ, p.Prime ∧ 2 ^ (i + 1) * u₀ < p ∧ p ≤ 2 ^ (i + 2) * u₀ := by
    intro i
    have hne : 2 ^ (i + 1) * u₀ ≠ 0 :=
      Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega)
    obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ (i + 1) * u₀) hne
    refine ⟨p, hp, h1, ?_⟩
    calc p ≤ 2 * (2 ^ (i + 1) * u₀) := h2
      _ = 2 ^ (i + 2) * u₀ := by rw [pow_succ']; ring
  choose p hp_prime hp_gt hp_le using hex_p
  have hp_strictMono : StrictMono p := by
    intro i j hij
    have hpow : 2 ^ (i + 2) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc p i ≤ 2 ^ (i + 2) * u₀ := hp_le i
      _ ≤ 2 ^ (j + 1) * u₀ := Nat.mul_le_mul_right u₀ hpow
      _ < p j := hp_gt j
  set M : ℕ := ∏ i ∈ range d, p i
  have hM_gt_U : U < M := by
    refine lt_of_lt_of_le hU_lt_succ ?_
    have hlow : ∀ i ∈ range d, u₀ + 1 ≤ p i := by
      intro i _
      have h2 : 2 ≤ 2 ^ (i + 1) := Nat.le_self_pow (by omega) 2
      have h2u : 2 * u₀ ≤ 2 ^ (i + 1) * u₀ := Nat.mul_le_mul_right u₀ h2
      have := hp_gt i
      omega
    simpa using Finset.pow_card_le_prod (range d) p (u₀ + 1) hlow
  have hM_pos : 0 < M := lt_of_le_of_lt (Nat.zero_le U) hM_gt_U
  have hz_lt_4yM : z < 4 * y * M := by
    have h1 : z < 4 * y * (U + 1) := Nat.lt_mul_div_succ z (by omega)
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left (4 * y) hM_gt_U)
  have hz_div_M : z / M < 4 * y := Nat.div_lt_of_lt_mul (by linarith)
  have hM_upper : M ≤ 2 ^ (d * d + d) * U := by
    have hup : ∀ i ∈ range d, p i ≤ 2 ^ (d + 1) * u₀ := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine (hp_le i).trans (Nat.mul_le_mul_right u₀ ?_)
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    calc M ≤ (2 ^ (d + 1) * u₀) ^ (range d).card := Finset.prod_le_pow_card (range d) p _ hup
      _ = 2 ^ ((d + 1) * d) * u₀ ^ d := by rw [card_range, mul_pow, ← pow_mul]
      _ = 2 ^ (d * d + d) * u₀ ^ d := by congr 2; ring
      _ ≤ 2 ^ (d * d + d) * U := Nat.mul_le_mul_left _ hu₀_pow
  let t : ℕ → ℕ := fun j => 4 * (z / (4 * M)) + 4 * j + 5
  have hex_j : ∃ j ∈ range (d + 1), ∀ i ∈ range d, ¬ p i ∣ t j := by
    by_contra hall
    push Not at hall
    have hmap : ∀ j, ∃ i, j ∈ range (d + 1) → i ∈ range d ∧ p i ∣ t j := by
      intro j
      by_cases hj : j ∈ range (d + 1)
      · obtain ⟨i, hi, hdvd⟩ := hall j hj
        exact ⟨i, fun _ => ⟨hi, hdvd⟩⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose f hf using hmap
    have hmaps : Set.MapsTo f (range (d + 1) : Set ℕ) (range d : Set ℕ) :=
      fun j hj => (hf j hj).1
    have hcard : (range d).card < (range (d + 1)).card := by simp
    obtain ⟨j₁, hj₁, j₂, hj₂, hne, hfeq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    wlog hlt : j₁ < j₂ generalizing j₁ j₂
    · exact this j₂ hj₂ j₁ hj₁ hne.symm hfeq.symm (by omega)
    set i := f j₁
    have hdvd₁ : p i ∣ t j₁ := (hf j₁ hj₁).2
    have hdvd₂ : p i ∣ t j₂ := hfeq ▸ (hf j₂ hj₂).2
    have hdiff : t j₂ - t j₁ = 4 * (j₂ - j₁) := by dsimp [t]; omega
    have hdvd_sub : p i ∣ 4 * (j₂ - j₁) := hdiff ▸ Nat.dvd_sub hdvd₂ hdvd₁
    have hp_gt_d : 2 * (d + 4) < p i := by
      have h2 : 2 ≤ 2 ^ (i + 1) := Nat.le_self_pow (by omega) 2
      have h2u : 2 * u₀ ≤ 2 ^ (i + 1) * u₀ := Nat.mul_le_mul_right u₀ h2
      have := hp_gt i
      omega
    have hp_odd : ¬ p i ∣ 2 := fun h2 => by
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hcop4 : Nat.Coprime (p i) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd (hp_prime i)).mpr hp_odd)
    have hdvd_j : p i ∣ j₂ - j₁ := hcop4.dvd_of_dvd_mul_left hdvd_sub
    have hj_le : j₂ - j₁ ≤ d := by
      rw [Finset.mem_range] at hj₁ hj₂
      omega
    have hp_le_j : p i ≤ j₂ - j₁ := Nat.le_of_dvd (by omega) hdvd_j
    omega
  obtain ⟨j, hj, hnodvd⟩ := hex_j
  rw [Finset.mem_range] at hj
  refine ⟨M * t j, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : z < (4 * M) * (z / (4 * M) + 1) := Nat.lt_mul_div_succ z (by positivity)
    have h2 : (4 * M) * (z / (4 * M) + 1) < M * t j := by
      dsimp [t]
      nlinarith
    exact lt_trans h1 h2
  · have h1 : (4 * M) * (z / (4 * M)) ≤ z := Nat.mul_div_le z (4 * M)
    have h2 : M * t j ≤ z + (4 * d + 5) * M := by
      have heq : M * t j = (4 * M) * (z / (4 * M)) + (4 * j + 5) * M := by
        dsimp [t]; ring
      rw [heq]
      have hj_le : (4 * j + 5) * M ≤ (4 * d + 5) * M := Nat.mul_le_mul_right M (by omega)
      omega
    have hUR : (U : ℝ) ≤ (z : ℝ) / (4 * (y : ℝ)) := by
      dsimp [U]
      simpa [Nat.cast_mul] using Nat.cast_div_le (m := z) (n := 4 * y)
    have hMR : (M : ℝ) ≤ ((2 ^ (d * d + d) : ℕ) : ℝ) * ((z : ℝ) / (4 * (y : ℝ))) := by
      have hcast : (M : ℝ) ≤ ((2 ^ (d * d + d) : ℕ) : ℝ) * (U : ℝ) := by exact_mod_cast hM_upper
      exact hcast.trans (mul_le_mul_of_nonneg_left hUR (by positivity))
    have h2R : ((M * t j : ℕ) : ℝ) ≤ (z : ℝ) + ((4 * d + 5 : ℕ) : ℝ) * (M : ℝ) := by
      exact_mod_cast h2
    have hdiv4 : (z : ℝ) / (4 * (y : ℝ)) ≤ (z : ℝ) / (y : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg z) hyR (by linarith)
    calc ((M * t j : ℕ) : ℝ)
        ≤ (z : ℝ) + ((4 * d + 5 : ℕ) : ℝ) *
            (((2 ^ (d * d + d) : ℕ) : ℝ) * ((z : ℝ) / (4 * (y : ℝ)))) :=
          h2R.trans (add_le_add_right (mul_le_mul_of_nonneg_left hMR (by positivity)) _)
      _ ≤ (z : ℝ) + ((4 * d + 5 : ℕ) : ℝ) *
            (((2 ^ (d * d + d) : ℕ) : ℝ) * ((z : ℝ) / (y : ℝ))) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hdiv4 (by positivity)) (by positivity)) _
      _ = (z : ℝ) * (1 + smoothJumpWidth d / (y : ℝ)) := by
          unfold smoothJumpWidth; ring
  · have : 5 ≤ t j := by dsimp [t]; omega
    nlinarith
  · have hcop_M2 : Nat.Coprime M 2 :=
      Nat.coprime_prod_left_iff.mpr fun i _ =>
        (Nat.Prime.coprime_iff_not_dvd (hp_prime i)).mpr fun h => by
          have := Nat.le_of_dvd (by norm_num) h
          have hgt := hp_gt i
          have h2p : 2 ≤ 2 ^ (i + 1) := Nat.le_self_pow (by omega) 2
          have h2u : 2 * u₀ ≤ 2 ^ (i + 1) * u₀ := Nat.mul_le_mul_right u₀ h2p
          omega
    have hcop_M4 : Nat.Coprime 4 M := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.Coprime.pow_right 2 hcop_M2).symm
    intro hdvd4
    have ht4 : 4 ∣ t j := hcop_M4.dvd_of_dvd_mul_left hdvd4
    dsimp [t] at ht4
    omega
  · intro q e hq _ hqe_dvd
    have hcop_Mt : Nat.Coprime M (t j) :=
      Nat.coprime_prod_left_iff.mpr fun i hi =>
        (Nat.Prime.coprime_iff_not_dvd (hp_prime i)).mpr (hnodvd i hi)
    have ht_le : t j ≤ 2 ^ (d + 3) * y := by
      have hdiv4 : 4 * (z / (4 * M)) ≤ z / M := by
        rw [mul_comm 4 M, ← Nat.div_div_eq_div_mul]
        exact Nat.mul_div_le (z / M) 4
      have ht1 : t j ≤ 4 * y + 4 * d + 5 := by dsimp [t]; omega
      have h8 : 8 ≤ 2 ^ (d + 3) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc t j ≤ 8 * y := by omega
        _ ≤ 2 ^ (d + 3) * y := Nat.mul_le_mul_right y h8
    by_cases hqM : q ∣ M
    · have hqt : ¬ q ∣ t j := fun h =>
        hq.not_dvd_one (hcop_Mt ▸ Nat.dvd_gcd hqM h)
      have hcop_qt : Nat.Coprime (q ^ e) (t j) :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqt)
      have hqe_M : q ^ e ∣ M := hcop_qt.dvd_of_dvd_mul_right hqe_dvd
      obtain ⟨i₀, hi₀, hqi₀⟩ := (hq.prime.dvd_finsetProd_iff p).mp hqM
      have hpeq : q = p i₀ := (Nat.prime_dvd_prime_iff_eq hq (hp_prime i₀)).mp hqi₀
      subst hpeq
      have hM_split : M = p i₀ * ∏ i ∈ (range d).erase i₀, p i :=
        (Finset.mul_prod_erase (range d) p hi₀).symm
      have hcop_rest : Nat.Coprime (p i₀) (∏ i ∈ (range d).erase i₀, p i) := by
        refine Nat.coprime_prod_right_iff.mpr fun i hi => ?_
        have hne_i : i ≠ i₀ := (mem_erase.mp hi).1
        refine (Nat.Prime.coprime_iff_not_dvd (hp_prime i₀)).mpr fun hdvd => ?_
        have heq := (Nat.prime_dvd_prime_iff_eq (hp_prime i₀) (hp_prime i)).mp hdvd
        exact hne_i (hp_strictMono.injective heq).symm
      have hpe_p : p i₀ ^ e ∣ p i₀ := by
        rw [hM_split] at hqe_M
        exact (Nat.Coprime.pow_left e hcop_rest).dvd_of_dvd_mul_right hqe_M
      have hpe_le_p : p i₀ ^ e ≤ p i₀ := Nat.le_of_dvd (hp_prime i₀).pos hpe_p
      have hp_le_bd : p i₀ ≤ 2 ^ (d + 3) * y := by
        rw [Finset.mem_range] at hi₀
        calc p i₀ ≤ 2 ^ (i₀ + 2) * u₀ := hp_le i₀
          _ ≤ 2 ^ (d + 3) * y := Nat.mul_le_mul
            (Nat.pow_le_pow_right (by norm_num) (by omega)) hu₀_le_y
      exact (hpe_le_p.trans hp_le_bd).trans
        (Nat.mul_le_mul_right y (le_max_right _ _))
    · have hcop_qM : Nat.Coprime (q ^ e) M :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM)
      have hqe_t : q ^ e ∣ t j := hcop_qM.dvd_of_dvd_mul_left (mul_comm M (t j) ▸ hqe_dvd)
      have ht_pos : 0 < t j := by dsimp [t]; omega
      exact ((Nat.le_of_dvd ht_pos hqe_t).trans ht_le).trans
        (Nat.mul_le_mul_right y (le_max_right _ _))

/-! ### Part 2: Single-octave greedy jump family -/

/-- Integer-valued Mertens partial sum. -/
def mertensInt (n : ℕ) : ℤ :=
  ∑ b ∈ Ioc 0 n, ArithmeticFunction.moebius b

theorem cast_mertensInt (n : ℕ) : (mertensInt n : ℝ) = mertens n := by
  simp [mertensInt, mertens]

private lemma abs_mertens_sub_mertens_le {a b : ℕ} (hab : a ≤ b) :
    |mertens b - mertens a| ≤ (b : ℝ) - (a : ℝ) := by
  rw [mertens, mertens, ← sum_Ioc_consecutive _ (Nat.zero_le a) hab, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ k ∈ Ioc a b, |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := fun k _ => by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  refine (sum_le_sum h1).trans ?_
  simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.cast_sub hab]
  exact le_rfl

private lemma abs_smoothMertens_sub_mertens_nat_le {θ X : ℝ} {n : ℕ}
    (hθ : 0 < θ) (hX : 0 < X) (hXn : X ≤ (n : ℝ)) :
    |smoothMertens θ X - mertens n| ≤ θ * X + ((n : ℝ) - X) + 2 := by
  have h1 := abs_smoothMertens_sub_mertens_le hθ hX
  have hfl_le : ⌊X⌋₊ ≤ n := Nat.floor_le_of_le hXn
  have h2 := abs_mertens_sub_mertens_le hfl_le
  have hfl_gt : X - 1 < (⌊X⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one X]
  have htri : |smoothMertens θ X - mertens n| ≤
      |smoothMertens θ X - mertens ⌊X⌋₊| + |mertens n - mertens ⌊X⌋₊| := by
    have : smoothMertens θ X - mertens n =
        (smoothMertens θ X - mertens ⌊X⌋₊) - (mertens n - mertens ⌊X⌋₊) := by ring
    rw [this]
    exact abs_sub _ _
  linarith

private lemma abs_smoothMertens_step_le {θ X₁ X₂ : ℝ}
    (hθ : 0 < θ) (hX₁ : 0 < X₁) (h12 : X₁ ≤ X₂) :
    |smoothMertens θ X₂ - smoothMertens θ X₁| ≤ (X₂ - X₁) + θ * X₁ + θ * X₂ + 3 := by
  have hX₂ : 0 < X₂ := lt_of_lt_of_le hX₁ h12
  have h1 := abs_smoothMertens_sub_mertens_le hθ hX₁
  have h2 := abs_smoothMertens_sub_mertens_le hθ hX₂
  have hfl : ⌊X₁⌋₊ ≤ ⌊X₂⌋₊ := Nat.floor_mono h12
  have h3 := abs_mertens_sub_mertens_le hfl
  have hfl2 : (⌊X₂⌋₊ : ℝ) ≤ X₂ := Nat.floor_le hX₂.le
  have hfl1 : X₁ - 1 < (⌊X₁⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one X₁]
  have htri : |smoothMertens θ X₂ - smoothMertens θ X₁| ≤
      |smoothMertens θ X₂ - mertens ⌊X₂⌋₊| + |mertens ⌊X₂⌋₊ - mertens ⌊X₁⌋₊| +
        |smoothMertens θ X₁ - mertens ⌊X₁⌋₊| := by
    have : smoothMertens θ X₂ - smoothMertens θ X₁ =
        (smoothMertens θ X₂ - mertens ⌊X₂⌋₊) + (mertens ⌊X₂⌋₊ - mertens ⌊X₁⌋₊) -
          (smoothMertens θ X₁ - mertens ⌊X₁⌋₊) := by ring
    rw [this]
    exact (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
  linarith

/-- Logarithmic grid point `(log Y - 1 + k λ₀) + τ` for octave shift `τ ∈ [0, 1]`. -/
private def octaveGrid (Y : ℕ) (lam₀ τ : ℝ) (k : ℕ) : ℝ :=
  (Real.log (Y : ℝ) - 1 + (k : ℝ) * lam₀) + τ

/-- Clamped smooth Mertens grid sample at `k ≤ 2^N`. -/
private def octaveSample (θ : ℝ) (Y N : ℕ) (lam₀ τ : ℝ) (k : ℕ) : ℝ :=
  smoothMertens θ (Real.exp (octaveGrid Y lam₀ τ (min k (2 ^ N))))

private lemma continuousOn_smoothMertens_shift {θ : ℝ} (hθ : 0 < θ) (u₀ : ℝ) :
    ContinuousOn (fun τ : ℝ => smoothMertens θ (Real.exp (u₀ + τ))) (Set.Icc (0 : ℝ) 1) :=
  (continuousOn_smoothMertens (A := Real.exp u₀) (B := Real.exp (u₀ + 1))
    hθ (Real.exp_pos u₀)).comp
    (Real.continuous_exp.continuousOn.comp (by fun_prop) (Set.mapsTo_univ _ _))
    fun _ hτ => ⟨Real.exp_le_exp.mpr (by linarith [hτ.1]),
      Real.exp_le_exp.mpr (by linarith [hτ.2])⟩

private lemma continuousOn_octaveSample_diff_sq {θ : ℝ} (hθ : 0 < θ)
    (Y N k₁ k₂ : ℕ) (lam₀ : ℝ) :
    ContinuousOn
      (fun τ : ℝ => (octaveSample θ Y N lam₀ τ k₁ - octaveSample θ Y N lam₀ τ k₂) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
  ContinuousOn.pow
    (ContinuousOn.sub (continuousOn_smoothMertens_shift hθ _)
      (continuousOn_smoothMertens_shift hθ _)) 2

/-- Averaging over `τ ∈ [0, 1]` selects a shift `τ₀` whose dyadic Haar energy on `[0, 2^{M+1}]`
satisfies the Mellin–Plancherel bound. -/
private lemma exists_octave_min_shift {Θ ε C_pl : ℝ} {y Y : ℕ}
    (hΘ : 1 / 2 ≤ Θ) (hε0 : 0 < ε) (hC_pl : 0 < C_pl)
    (hpl : ∀ θ lam : ℝ, 0 < θ → θ ≤ 1 → 0 < lam → lam ≤ 1 →
      Integrable (fun u : ℝ => Real.exp (-(2 * (Θ + ε)) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) ∧
      (∫ u : ℝ, Real.exp (-(2 * (Θ + ε)) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) ≤
        C_pl * lam ^ (1 - 2 * ε))
    (hy : 16 ≤ y) (hY_pos : 0 < (Y : ℝ)) :
    let θ := 1 / (16 * (y : ℝ))
    let M_grid := Nat.log 2 (16 * y) + 1
    let N := M_grid + 1
    let lam₀ := 1 / ((2 ^ M_grid : ℕ) : ℝ)
    ∃ τ₀ ∈ Set.Icc (0 : ℝ) 1,
      dyadicEnergy N (octaveSample θ Y N lam₀ τ₀) ≤
        6 * Real.exp (4 * (Θ + ε)) * C_pl * ((M_grid : ℝ) + 1) *
          (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * (Θ + ε)) := by
  classical
  intro θ M_grid N lam₀
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by dsimp [θ]; rw [div_le_one (by positivity)]; linarith
  have h2M_le : 2 ^ M_grid ≤ 32 * y := by
    dsimp [M_grid]; rw [pow_succ]
    have := Nat.pow_log_le_self 2 (by omega : 16 * y ≠ 0)
    omega
  have hlam₀_pos : 0 < lam₀ := by dsimp [lam₀]; positivity
  have h2N_lam₀ : ((2 ^ N : ℕ) : ℝ) * lam₀ = 2 := by
    dsimp [N, lam₀]; rw [pow_succ]; push_cast; field_simp
  have hE_cont : ContinuousOn (fun τ => dyadicEnergy N (octaveSample θ Y N lam₀ τ))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_finsetSum _ fun p _ =>
      continuousOn_octaveSample_diff_sq hθ0 Y N ((p.2 + 1) * 2 ^ p.1) (p.2 * 2 ^ p.1) lam₀
  obtain ⟨τ₀, hτ₀, hτ₀_min⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hE_cont
  refine ⟨τ₀, hτ₀, ?_⟩
  obtain ⟨σ, hσ_def⟩ : ∃ σ : ℝ, σ = Θ + ε := ⟨_, rfl⟩
  rw [← hσ_def] at hpl ⊢
  have hσ_pos : 0 < σ := by rw [hσ_def]; linarith
  obtain ⟨lowSet, hlow_def⟩ : ∃ lowSet : Finset (ℕ × ℕ),
      lowSet = (dyadicSet N).filter fun p => p.1 ≤ M_grid := ⟨_, rfl⟩
  have htop_le : ∀ τ : ℝ, dyadicEnergy N (octaveSample θ Y N lam₀ τ) ≤
      3 * ∑ p ∈ lowSet, (octaveSample θ Y N lam₀ τ ((p.2 + 1) * 2 ^ p.1) -
        octaveSample θ Y N lam₀ τ (p.2 * 2 ^ p.1)) ^ 2 := by
    intro τ
    have hpart : dyadicSet N = insert (N, 0) lowSet := by
      ext ⟨m, q⟩
      simp only [hlow_def, Finset.mem_filter, Finset.mem_insert, Prod.mk.injEq, mem_dyadicSet]
      constructor
      · rintro ⟨hm, hq⟩
        rcases eq_or_lt_of_le hm with rfl | hlt
        · left
          rw [Nat.sub_self N, pow_zero] at hq
          exact ⟨rfl, by omega⟩
        · right; exact ⟨⟨hm, hq⟩, by dsimp [N] at hlt; omega⟩
      · rintro (⟨rfl, rfl⟩ | ⟨h, _⟩)
        · exact ⟨le_rfl, by simp⟩
        · exact h
    have hnot : (N, 0) ∉ lowSet := by simp [hlow_def, N]
    rw [dyadicEnergy, hpart, sum_insert hnot]
    have hm0 : (M_grid, 0) ∈ lowSet := by
      simp only [hlow_def, Finset.mem_filter, mem_dyadicSet]
      exact ⟨⟨by dsimp [N]; omega, by dsimp [N]; norm_num⟩, le_rfl⟩
    have hm1 : (M_grid, 1) ∈ lowSet := by
      simp only [hlow_def, Finset.mem_filter, mem_dyadicSet]
      exact ⟨⟨by dsimp [N]; omega, by dsimp [N]; norm_num⟩, le_rfl⟩
    have hne01 : (M_grid, (0 : ℕ)) ≠ (M_grid, 1) := by simp
    have hpair_le : (octaveSample θ Y N lam₀ τ ((0 + 1) * 2 ^ N) -
          octaveSample θ Y N lam₀ τ (0 * 2 ^ N)) ^ 2 ≤
        2 * ((octaveSample θ Y N lam₀ τ ((0 + 1) * 2 ^ M_grid) -
            octaveSample θ Y N lam₀ τ (0 * 2 ^ M_grid)) ^ 2 +
          (octaveSample θ Y N lam₀ τ ((1 + 1) * 2 ^ M_grid) -
            octaveSample θ Y N lam₀ τ (1 * 2 ^ M_grid)) ^ 2) := by
      have h2N : (0 + 1) * 2 ^ N = (1 + 1) * 2 ^ M_grid := by dsimp [N]; rw [pow_succ]; ring
      have h0N : 0 * 2 ^ N = 0 * 2 ^ M_grid := by simp
      have h1M : (0 + 1) * 2 ^ M_grid = 1 * 2 ^ M_grid := by ring
      rw [h2N, h0N, h1M]
      set a := octaveSample θ Y N lam₀ τ (1 * 2 ^ M_grid) -
        octaveSample θ Y N lam₀ τ (0 * 2 ^ M_grid)
      set b := octaveSample θ Y N lam₀ τ ((1 + 1) * 2 ^ M_grid) -
        octaveSample θ Y N lam₀ τ (1 * 2 ^ M_grid)
      have : octaveSample θ Y N lam₀ τ ((1 + 1) * 2 ^ M_grid) -
          octaveSample θ Y N lam₀ τ (0 * 2 ^ M_grid) = a + b := by dsimp [a, b]; ring
      rw [this]
      nlinarith [sq_nonneg (a - b)]
    have hsub2 : ({(M_grid, 0), (M_grid, 1)} : Finset (ℕ × ℕ)) ⊆ lowSet := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx'
      · exact hm0
      · rw [mem_singleton.mp hx']; exact hm1
    have htwo_sum := sum_le_sum_of_subset_of_nonneg hsub2 fun p _ _ =>
      sq_nonneg (octaveSample θ Y N lam₀ τ ((p.2 + 1) * 2 ^ p.1) -
        octaveSample θ Y N lam₀ τ (p.2 * 2 ^ p.1))
    rw [sum_pair hne01] at htwo_sum
    linarith
  have hterm_int : ∀ p ∈ lowSet,
      ∫ τ in Set.Icc (0 : ℝ) 1,
        (octaveSample θ Y N lam₀ τ ((p.2 + 1) * 2 ^ p.1) -
          octaveSample θ Y N lam₀ τ (p.2 * 2 ^ p.1)) ^ 2 ≤
      Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * C_pl *
        (((2 ^ p.1 : ℕ) : ℝ) * lam₀) ^ (1 - 2 * ε) := by
    intro ⟨m, q⟩ hp
    rw [hlow_def] at hp
    have hm_le : m ≤ M_grid := (mem_filter.mp hp).2
    obtain ⟨hmN, hq⟩ := mem_dyadicSet.mp (mem_filter.mp hp).1
    have h_end_le : (q + 1) * 2 ^ m ≤ 2 ^ N := by
      calc (q + 1) * 2 ^ m ≤ 2 ^ (N - m) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ N := by rw [← pow_add, Nat.sub_add_cancel hmN]
    have h_start_le : q * 2 ^ m ≤ 2 ^ N :=
      le_trans (Nat.mul_le_mul_right _ (Nat.le_succ q)) h_end_le
    set lam_m : ℝ := ((2 ^ m : ℕ) : ℝ) * lam₀
    have hlam_m0 : 0 < lam_m := by dsimp [lam_m]; positivity
    have hlam_m1 : lam_m ≤ 1 := by
      dsimp [lam_m, lam₀]
      rw [mul_one_div, div_le_one (by positivity)]
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hm_le
    obtain ⟨hint_pl, hbd_pl⟩ := hpl θ lam_m hθ0 hθ1 hlam_m0 hlam_m1
    set u₀ : ℝ := Real.log (Y : ℝ) - 1 + ((q * 2 ^ m : ℕ) : ℝ) * lam₀
    let dom : ℝ → ℝ := fun τ =>
      Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) *
        (Real.exp (-(2 * σ) * (u₀ + τ)) *
          (smoothMertens θ (Real.exp (u₀ + τ + lam_m)) -
            smoothMertens θ (Real.exp (u₀ + τ))) ^ 2)
    have hdom_int : Integrable dom :=
      (hint_pl.comp_add_left u₀).const_mul (Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ))
    have hpt_le : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        (octaveSample θ Y N lam₀ τ ((q + 1) * 2 ^ m) -
          octaveSample θ Y N lam₀ τ (q * 2 ^ m)) ^ 2 ≤ dom τ := by
      intro τ hτ
      have hw1 : octaveGrid Y lam₀ τ (min ((q + 1) * 2 ^ m) (2 ^ N)) = u₀ + τ + lam_m := by
        rw [min_eq_left h_end_le]
        dsimp [octaveGrid, u₀, lam_m]; push_cast; ring
      have hw0 : octaveGrid Y lam₀ τ (min (q * 2 ^ m) (2 ^ N)) = u₀ + τ := by
        rw [min_eq_left h_start_le]
        dsimp [octaveGrid, u₀]
      have hge1 : 1 ≤ Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) *
          Real.exp (-(2 * σ) * (u₀ + τ)) := by
        rw [Real.rpow_def_of_pos hY_pos, mul_comm (Real.log (Y : ℝ)) (2 * σ),
          ← Real.exp_add, ← Real.exp_add]
        refine Real.one_le_exp ?_
        have hq_le : ((q * 2 ^ m : ℕ) : ℝ) * lam₀ ≤ 2 := by
          calc _ ≤ ((2 ^ N : ℕ) : ℝ) * lam₀ :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast h_start_le) hlam₀_pos.le
            _ = 2 := h2N_lam₀
        dsimp [u₀]; nlinarith [hτ.2, hσ_pos]
      dsimp only [octaveSample, dom]
      rw [hw1, hw0]
      set sq_val := (smoothMertens θ (Real.exp (u₀ + τ + lam_m)) -
        smoothMertens θ (Real.exp (u₀ + τ))) ^ 2
      calc sq_val = 1 * sq_val := (one_mul _).symm
        _ ≤ (Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * Real.exp (-(2 * σ) * (u₀ + τ))) * sq_val :=
            mul_le_mul_of_nonneg_right hge1 (sq_nonneg _)
        _ = _ := by ring
    have hcont_term := continuousOn_octaveSample_diff_sq hθ0 Y N ((q + 1) * 2 ^ m) (q * 2 ^ m) lam₀
    have hset_le : ∫ τ in Set.Icc (0 : ℝ) 1,
        (octaveSample θ Y N lam₀ τ ((q + 1) * 2 ^ m) -
          octaveSample θ Y N lam₀ τ (q * 2 ^ m)) ^ 2 ≤ ∫ τ : ℝ, dom τ :=
      (setIntegral_mono_on hcont_term.integrableOn_Icc hdom_int.integrableOn
        measurableSet_Icc hpt_le).trans
        (setIntegral_le_integral hdom_int (Eventually.of_forall fun _ => by dsimp [dom]; positivity))
    have hshift_all : ∫ τ : ℝ, dom τ =
        Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) *
          ∫ u : ℝ, Real.exp (-(2 * σ) * u) *
            (smoothMertens θ (Real.exp (u + lam_m)) - smoothMertens θ (Real.exp u)) ^ 2 := by
      dsimp [dom]
      rw [integral_const_mul,
        integral_add_left_eq_self
          (fun u : ℝ => Real.exp (-(2 * σ) * u) *
            (smoothMertens θ (Real.exp (u + lam_m)) - smoothMertens θ (Real.exp u)) ^ 2) u₀]
    calc ∫ τ in Set.Icc (0 : ℝ) 1,
          (octaveSample θ Y N lam₀ τ ((q + 1) * 2 ^ m) -
            octaveSample θ Y N lam₀ τ (q * 2 ^ m)) ^ 2
        ≤ Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) *
            ∫ u : ℝ, Real.exp (-(2 * σ) * u) *
              (smoothMertens θ (Real.exp (u + lam_m)) - smoothMertens θ (Real.exp u)) ^ 2 :=
          hset_le.trans_eq hshift_all
      _ ≤ Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * (C_pl * lam_m ^ (1 - 2 * ε)) :=
          mul_le_mul_of_nonneg_left hbd_pl (by positivity)
      _ = _ := by ring
  have hmin_int : dyadicEnergy N (octaveSample θ Y N lam₀ τ₀) ≤
      ∫ τ in Set.Icc (0 : ℝ) 1, dyadicEnergy N (octaveSample θ Y N lam₀ τ) := by
    have hconst : ∫ _τ in Set.Icc (0 : ℝ) 1, dyadicEnergy N (octaveSample θ Y N lam₀ τ₀) =
        dyadicEnergy N (octaveSample θ Y N lam₀ τ₀) := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - 0)]
      simp
    rw [← hconst]
    exact setIntegral_mono_on continuousOn_const.integrableOn_Icc hE_cont.integrableOn_Icc
      measurableSet_Icc fun _ hτ => hτ₀_min hτ
  have hint_each : ∀ p ∈ lowSet, IntegrableOn
      (fun τ => (octaveSample θ Y N lam₀ τ ((p.2 + 1) * 2 ^ p.1) -
        octaveSample θ Y N lam₀ τ (p.2 * 2 ^ p.1)) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    fun p _ => (continuousOn_octaveSample_diff_sq hθ0 Y N
      ((p.2 + 1) * 2 ^ p.1) (p.2 * 2 ^ p.1) lam₀).integrableOn_Icc
  have hlow_sum : ∫ τ in Set.Icc (0 : ℝ) 1, dyadicEnergy N (octaveSample θ Y N lam₀ τ) ≤
      3 * ∑ p ∈ lowSet, Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * C_pl *
        (((2 ^ p.1 : ℕ) : ℝ) * lam₀) ^ (1 - 2 * ε) := by
    have h1 : ∫ τ in Set.Icc (0 : ℝ) 1, dyadicEnergy N (octaveSample θ Y N lam₀ τ) ≤
        ∫ τ in Set.Icc (0 : ℝ) 1, 3 * ∑ p ∈ lowSet,
          (octaveSample θ Y N lam₀ τ ((p.2 + 1) * 2 ^ p.1) -
            octaveSample θ Y N lam₀ τ (p.2 * 2 ^ p.1)) ^ 2 :=
      setIntegral_mono_on hE_cont.integrableOn_Icc
        ((integrable_finsetSum lowSet hint_each).const_mul 3) measurableSet_Icc
        fun τ _ => htop_le τ
    rw [integral_const_mul, integral_finsetSum lowSet hint_each] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (sum_le_sum hterm_int) (by norm_num))
  have hlow_eq : lowSet = (range (M_grid + 1)).biUnion fun m =>
      (range (2 ^ (N - m))).map ⟨fun q => (m, q), fun _ _ h => (Prod.mk.inj h).2⟩ := by
    ext ⟨m, q⟩
    simp only [hlow_def, Finset.mem_filter, mem_dyadicSet, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨⟨_, hq⟩, hm⟩ => ⟨m, by omega, q, hq, rfl, rfl⟩,
      fun ⟨_, hm', _, hq', rfl, rfl⟩ => ⟨⟨by dsimp [N]; omega, hq'⟩, by omega⟩⟩
  have hdisj_m : (range (M_grid + 1) : Set ℕ).PairwiseDisjoint fun m =>
      (range (2 ^ (N - m))).map ⟨fun q => (m, q), fun _ _ h => (Prod.mk.inj h).2⟩ := by
    intro m₁ _ m₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    rcases mem_map.mp hp₁ with ⟨_, _, rfl⟩
    rcases mem_map.mp hp₂ with ⟨_, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm
  have hsum_levels : ∑ p ∈ lowSet,
      Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * C_pl *
        (((2 ^ p.1 : ℕ) : ℝ) * lam₀) ^ (1 - 2 * ε) ≤
      2 * Real.exp (4 * σ) * C_pl * ((M_grid : ℝ) + 1) *
        (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * σ) := by
    rw [hlow_eq, sum_biUnion hdisj_m]
    have hlevel : ∀ m ∈ range (M_grid + 1),
        (∑ p ∈ (range (2 ^ (N - m))).map ⟨fun q => (m, q), fun _ _ h => (Prod.mk.inj h).2⟩,
          Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * C_pl *
            (((2 ^ p.1 : ℕ) : ℝ) * lam₀) ^ (1 - 2 * ε)) ≤
        2 * Real.exp (4 * σ) * C_pl * (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * σ) := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [sum_map]
      simp only [Function.Embedding.coeFn_mk, sum_const, card_range, nsmul_eq_mul]
      have hsub : N - m = (M_grid - m) + 1 := by dsimp [N]; omega
      have hlam_eq : ((2 ^ m : ℕ) : ℝ) * lam₀ = (((2 ^ (M_grid - m) : ℕ) : ℝ))⁻¹ := by
        dsimp [lam₀]
        have hpow : (2 ^ M_grid : ℕ) = 2 ^ m * 2 ^ (M_grid - m) := by
          rw [← pow_add, Nat.add_sub_of_le (by omega)]
        rw [hpow, Nat.cast_mul]; field_simp
      set K_m : ℝ := ((2 ^ (M_grid - m) : ℕ) : ℝ)
      have hKm_pos : 0 < K_m := by dsimp [K_m]; positivity
      have hKm_le : K_m ≤ 32 * (y : ℝ) := by
        dsimp [K_m]
        have : 2 ^ (M_grid - m) ≤ 2 ^ M_grid := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast this.trans h2M_le
      have h2Nm : ((2 ^ (N - m) : ℕ) : ℝ) = 2 * K_m := by
        rw [hsub, pow_succ]; dsimp [K_m]; push_cast; ring
      have hcancel : K_m * (K_m⁻¹) ^ (1 - 2 * ε) = K_m ^ (2 * ε) := by
        rw [← Real.rpow_neg_one K_m, ← Real.rpow_mul hKm_pos.le]
        nth_rw 1 [← Real.rpow_one K_m]
        rw [← Real.rpow_add hKm_pos]
        congr 1; ring
      have hKm_pow : K_m ^ (2 * ε) ≤ (32 * (y : ℝ)) ^ (2 * ε) :=
        Real.rpow_le_rpow hKm_pos.le hKm_le (by positivity)
      rw [h2Nm, hlam_eq]
      calc (2 * K_m) * (Real.exp (4 * σ) * (Y : ℝ) ^ (2 * σ) * C_pl * (K_m⁻¹) ^ (1 - 2 * ε))
          = 2 * Real.exp (4 * σ) * C_pl * (Y : ℝ) ^ (2 * σ) * (K_m * (K_m⁻¹) ^ (1 - 2 * ε)) := by
            ring
        _ = 2 * Real.exp (4 * σ) * C_pl * (Y : ℝ) ^ (2 * σ) * K_m ^ (2 * ε) := by rw [hcancel]
        _ ≤ 2 * Real.exp (4 * σ) * C_pl * (Y : ℝ) ^ (2 * σ) * (32 * (y : ℝ)) ^ (2 * ε) :=
            mul_le_mul_of_nonneg_left hKm_pow (by positivity)
        _ = 2 * Real.exp (4 * σ) * C_pl * (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * σ) := by ring
    exact (sum_le_sum hlevel).trans_eq (by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring)
  linarith [hmin_int.trans hlow_sum, hsum_levels]

private lemma sup_id_mem {S : Finset ℕ} (hne : S.Nonempty) : S.sup id ∈ S := by
  have h1 : S.sup id ≤ S.max' hne := Finset.sup_le fun k hk => le_max' S k hk
  have h2 : S.max' hne ≤ S.sup id := Finset.le_sup (f := id) (max'_mem S hne)
  rw [le_antisymm h1 h2]
  exact max'_mem S hne

/-- Largest grid index `k ≤ 2^N` with `exp(octaveGrid Y lam₀ τ k) ≤ X`. -/
private def octaveIdx (Y N : ℕ) (lam₀ τ X : ℝ) : ℕ :=
  ((range (2 ^ N + 1)).filter fun k => Real.exp (octaveGrid Y lam₀ τ k) ≤ X).sup id

private lemma octaveIdx_mono {Y N : ℕ} {lam₀ τ X₁ X₂ : ℝ} (h12 : X₁ ≤ X₂) :
    octaveIdx Y N lam₀ τ X₁ ≤ octaveIdx Y N lam₀ τ X₂ := by
  unfold octaveIdx
  exact Finset.sup_mono fun k hk =>
    mem_filter.mpr ⟨(mem_filter.mp hk).1, (mem_filter.mp hk).2.trans h12⟩

private lemma octaveIdx_spec {Y N : ℕ} {lam₀ τ X : ℝ}
    (hY_pos : 0 < (Y : ℝ)) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hYX : (Y : ℝ) ≤ X) :
    octaveIdx Y N lam₀ τ X ≤ 2 ^ N ∧
    Real.exp (octaveGrid Y lam₀ τ (octaveIdx Y N lam₀ τ X)) ≤ X := by
  unfold octaveIdx
  have hw0 : Real.exp (octaveGrid Y lam₀ τ 0) ≤ (Y : ℝ) := by
    rw [← Real.exp_log hY_pos]
    refine Real.exp_le_exp.mpr ?_
    dsimp [octaveGrid]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    linarith [hτ.2]
  have h0_mem : 0 ∈ (range (2 ^ N + 1)).filter fun k => Real.exp (octaveGrid Y lam₀ τ k) ≤ X :=
    mem_filter.mpr ⟨Finset.mem_range.mpr (by positivity), hw0.trans hYX⟩
  have hsup := sup_id_mem ⟨0, h0_mem⟩
  obtain ⟨hr, hle⟩ := mem_filter.mp hsup
  rw [Finset.mem_range] at hr
  exact ⟨by omega, hle⟩

private lemma octaveIdx_lt_2N {Y N : ℕ} {lam₀ τ X : ℝ}
    (hY_pos : 0 < (Y : ℝ)) (h2N : ((2 ^ N : ℕ) : ℝ) * lam₀ = 2)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hYX : (Y : ℝ) ≤ X) (hX2Y : X ≤ 2 * (Y : ℝ)) :
    octaveIdx Y N lam₀ τ X < 2 ^ N ∧
    X < Real.exp (octaveGrid Y lam₀ τ (octaveIdx Y N lam₀ τ X + 1)) := by
  classical
  obtain ⟨hle, hbd⟩ := octaveIdx_spec hY_pos hτ hYX
  have htop : 2 * (Y : ℝ) < Real.exp (octaveGrid Y lam₀ τ (2 ^ N)) := by
    have hexp1 : 2 * (Y : ℝ) < Real.exp (Real.log (Y : ℝ) + 1) := by
      rw [Real.exp_add, Real.exp_log hY_pos]
      have : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      nlinarith
    have hwN : Real.log (Y : ℝ) + 1 ≤ octaveGrid Y lam₀ τ (2 ^ N) := by
      dsimp [octaveGrid]; rw [h2N]; linarith [hτ.1]
    exact lt_of_lt_of_le hexp1 (Real.exp_le_exp.mpr hwN)
  have hlt : octaveIdx Y N lam₀ τ X < 2 ^ N := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso; rw [heq] at hbd; linarith
    · exact hlt
  refine ⟨hlt, ?_⟩
  by_contra hge
  push Not at hge
  have hmem : octaveIdx Y N lam₀ τ X + 1 ∈
      (range (2 ^ N + 1)).filter fun k => Real.exp (octaveGrid Y lam₀ τ k) ≤ X :=
    mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hge⟩
  have hsup_ge : octaveIdx Y N lam₀ τ X + 1 ≤ octaveIdx Y N lam₀ τ X := by
    unfold octaveIdx
    exact Finset.le_sup (f := id) hmem
  omega

private def octaveZ (Y Z k_lo : ℕ) (lam₀ τ : ℝ) (i : ℕ) : ℕ :=
  if i = 0 then Y + 1
  else if i = 1 then Z
  else ⌈Real.exp (octaveGrid Y lam₀ τ (k_lo + (i - 2) + 1))⌉₊

private def octaveJ (Y Z k_lo k_hi : ℕ) (g : ℕ → ℝ) (Δ : ℝ) (i : ℕ) : ℤ :=
  if i = 0 then greedyApprox g Δ k_lo - mertensInt Y
  else if i = 1 then mertensInt Z - greedyApprox g Δ k_hi
  else greedyJump g Δ (k_lo + (i - 2))

private lemma card_octave_hit_le {d y Y k_lo L : ℕ} {lam₀ τ A B : ℝ}
    (hy1 : (1 : ℝ) ≤ (y : ℝ)) (hΔ_ge16 : 16 ≤ (Y : ℝ) / (y : ℝ))
    (hlam₀_pos : 0 < lam₀) (hlam₀_ge : 1 / (32 * (y : ℝ)) ≤ lam₀)
    (hAY : (Y : ℝ) / 2 ≤ A) (hBA : B ≤ A * (1 + smoothJumpWidth d / (y : ℝ))) :
    (((range L).filter fun j =>
      A ≤ (octaveZ Y 0 k_lo lam₀ τ (j + 2) : ℝ) ∧
        (octaveZ Y 0 k_lo lam₀ τ (j + 2) : ℝ) ≤ B).card : ℝ) ≤
      64 * smoothJumpWidth d + 65 := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by linarith
  set S_hit := (range L).filter fun j =>
    A ≤ (octaveZ Y 0 k_lo lam₀ τ (j + 2) : ℝ) ∧ (octaveZ Y 0 k_lo lam₀ τ (j + 2) : ℝ) ≤ B
  have hY_ge16 : 16 * (y : ℝ) ≤ (Y : ℝ) := (le_div_iff₀ hy_pos).mp hΔ_ge16
  have hA_ge8 : 8 ≤ A := by linarith
  have hA_pos : 0 < A := by linarith
  by_cases hne : S_hit.Nonempty
  · set j₀ := S_hit.min' hne
    set j₁ := S_hit.max' hne
    have hj₀_mem := min'_mem S_hit hne
    have hj₁_mem := max'_mem S_hit hne
    have hsub_Icc : S_hit ⊆ Icc j₀ j₁ :=
      fun j hj => Finset.mem_Icc.mpr ⟨min'_le S_hit j hj, le_max' S_hit j hj⟩
    have hj₀_le_j₁ : j₀ ≤ j₁ := min'_le S_hit j₁ hj₁_mem
    have hcard_le : S_hit.card ≤ j₁ - j₀ + 1 := by
      have := card_le_card hsub_Icc
      rw [Nat.card_Icc] at this
      omega
    obtain ⟨_, hA_z₀, _⟩ := mem_filter.mp hj₀_mem
    obtain ⟨_, _, hz₁_B⟩ := mem_filter.mp hj₁_mem
    have hz₀_eq : octaveZ Y 0 k_lo lam₀ τ (j₀ + 2) =
        ⌈Real.exp (octaveGrid Y lam₀ τ (k_lo + j₀ + 1))⌉₊ := by
      simp [octaveZ]
    have hz₁_eq : octaveZ Y 0 k_lo lam₀ τ (j₁ + 2) =
        ⌈Real.exp (octaveGrid Y lam₀ τ (k_lo + j₁ + 1))⌉₊ := by
      simp [octaveZ]
    rw [hz₀_eq] at hA_z₀
    rw [hz₁_eq] at hz₁_B
    set X₀ := Real.exp (octaveGrid Y lam₀ τ (k_lo + j₀ + 1))
    set X₁ := Real.exp (octaveGrid Y lam₀ τ (k_lo + j₁ + 1))
    have hX₀_pos : 0 < X₀ := Real.exp_pos _
    have hX₁_le_B : X₁ ≤ B := (Nat.le_ceil X₁).trans hz₁_B
    have hA_lt_X₀ : A - 1 ≤ X₀ := by
      have hceil_X₀ := Nat.ceil_lt_add_one hX₀_pos.le
      linarith only [hceil_X₀, hA_z₀]
    have h1_le_A : 1 ≤ A / (2 * (y : ℝ)) := by
      rw [one_le_div (by positivity)]
      linarith
    have hX₀_ge_half : A / 2 ≤ X₀ := by linarith
    have hratio_exp : X₀ * (1 + ((j₁ - j₀ : ℕ) : ℝ) * lam₀) ≤ X₁ := by
      have heq : X₁ = X₀ * Real.exp (((j₁ - j₀ : ℕ) : ℝ) * lam₀) := by
        dsimp [X₀, X₁, octaveGrid]
        rw [← Real.exp_add]
        congr 1
        rw [Nat.cast_sub hj₀_le_j₁]
        push_cast; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left
        ((add_comm (1 : ℝ) _).trans_le (Real.add_one_le_exp _)) hX₀_pos.le
    have hineq : A - A / (2 * (y : ℝ)) + (A / 2) * (((j₁ - j₀ : ℕ) : ℝ) * lam₀) ≤
        A * (1 + smoothJumpWidth d / (y : ℝ)) := by
      have hstep1 : X₀ + (A / 2) * (((j₁ - j₀ : ℕ) : ℝ) * lam₀) ≤
          X₀ * (1 + ((j₁ - j₀ : ℕ) : ℝ) * lam₀) := by
        have hnn : 0 ≤ ((j₁ - j₀ : ℕ) : ℝ) * lam₀ := by positivity
        nlinarith
      linarith [hratio_exp.trans (hX₁_le_B.trans hBA), hA_lt_X₀, h1_le_A]
    have hdivA : ((j₁ - j₀ : ℕ) : ℝ) * lam₀ ≤ 2 * (smoothJumpWidth d + 1) / (y : ℝ) := by
      have hmulA : A * (((j₁ - j₀ : ℕ) : ℝ) * lam₀) ≤
          A * (2 * (smoothJumpWidth d + 1) / (y : ℝ)) := by
        have h12 : 1 / (2 * (y : ℝ)) ≤ 1 / (y : ℝ) :=
          one_div_le_one_div_of_le hy_pos (by linarith)
        have hmul12 : A * (1 / (2 * (y : ℝ))) ≤ A * (1 / (y : ℝ)) :=
          mul_le_mul_of_nonneg_left h12 hA_pos.le
        have e1 : A / (2 * (y : ℝ)) = A * (1 / (2 * (y : ℝ))) := by ring
        have e3 : A * (2 * (smoothJumpWidth d + 1) / (y : ℝ)) =
            2 * (A * (smoothJumpWidth d / (y : ℝ)) + A * (1 / (y : ℝ))) := by ring
        linarith only [hineq, hmul12, e1, e3]
      exact le_of_mul_le_mul_left hmulA hA_pos
    have hj_diff : ((j₁ - j₀ : ℕ) : ℝ) ≤ 64 * (smoothJumpWidth d + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hlam₀_ge (Nat.cast_nonneg (j₁ - j₀))
      have h2 := h1.trans hdivA
      rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 32 * (y : ℝ))] at h2
      have e : 2 * (smoothJumpWidth d + 1) / (y : ℝ) * (32 * (y : ℝ)) =
          64 * (smoothJumpWidth d + 1) := by field_simp [hy_pos.ne']; ring
      linarith
    have hcast : (S_hit.card : ℝ) ≤ ((j₁ - j₀ : ℕ) : ℝ) + 1 := by exact_mod_cast hcard_le
    linarith
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp only [card_empty, Nat.cast_zero]
    linarith [smoothJumpWidth_pos d]

private lemma exp_lam₀_sub_one_le {lam₀ : ℝ} (hpos : 0 < lam₀) (hle1 : lam₀ ≤ 1) :
    Real.exp lam₀ - 1 ≤ 2 * lam₀ := by
  have hb := Real.exp_bound (x := lam₀) (by rw [abs_of_pos hpos]; exact hle1) (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
    Nat.succ_eq_add_one, Nat.factorial_two, Nat.cast_ofNat] at hb
  rw [abs_of_pos hpos, abs_le] at hb
  nlinarith [hb.2]

private lemma exp_octaveGrid_le_eight_mul {Y N : ℕ} {lam₀ τ : ℝ}
    (hY_pos : 0 < (Y : ℝ)) (hlam₀_pos : 0 < lam₀) (h2N : ((2 ^ N : ℕ) : ℝ) * lam₀ = 2)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {k : ℕ} (hk : k ≤ 2 ^ N) :
    Real.exp (octaveGrid Y lam₀ τ k) ≤ 8 * (Y : ℝ) := by
  have hw_le : octaveGrid Y lam₀ τ k ≤ Real.log (Y : ℝ) + 2 := by
    dsimp [octaveGrid]
    have : (k : ℝ) * lam₀ ≤ 2 := by
      calc (k : ℝ) * lam₀ ≤ ((2 ^ N : ℕ) : ℝ) * lam₀ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hlam₀_pos.le
        _ = 2 := h2N
    linarith [hτ.2]
  have he2 : (Real.exp 1) ^ 2 ≤ 8 := by
    have h1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  calc Real.exp (octaveGrid Y lam₀ τ k)
      ≤ Real.exp (Real.log (Y : ℝ) + 2) := Real.exp_le_exp.mpr hw_le
    _ = (Y : ℝ) * (Real.exp 1) ^ 2 := by
        rw [Real.exp_add, Real.exp_log hY_pos, ← Real.exp_nat_mul]; norm_num
    _ ≤ 8 * (Y : ℝ) := by
        calc (Y : ℝ) * (Real.exp 1) ^ 2 ≤ (Y : ℝ) * 8 :=
              mul_le_mul_of_nonneg_left he2 hY_pos.le
          _ = 8 * (Y : ℝ) := by ring

private theorem exists_octave_jump_family {Θ ε C_pl : ℝ} {d y Y Z : ℕ}
    (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1) (hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4) (hC_pl : 0 < C_pl)
    (hpl : ∀ θ lam : ℝ, 0 < θ → θ ≤ 1 → 0 < lam → lam ≤ 1 →
      Integrable (fun u : ℝ => Real.exp (-(2 * (Θ + ε)) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) ∧
      (∫ u : ℝ, Real.exp (-(2 * (Θ + ε)) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) ≤
        C_pl * lam ^ (1 - 2 * ε))
    (hd : 1 ≤ d) (hy : 16 ≤ y)
    (hY_lo : smoothJumpBase d * y ≤ Y) (hYZ : Y < Z) (hZ2Y : Z ≤ 2 * Y) :
    ∃ (m : ℕ) (z : ℕ → ℕ) (J : ℕ → ℤ),
      (∀ i < m, Y < z i ∧ z i ≤ Z) ∧
      (∑ i ∈ range m, (J i : ℝ)) = mertens Z - mertens Y ∧
      (∀ x : ℕ, Y ≤ x → x ≤ Z →
        |(mertens Y + ∑ i ∈ range m, if z i ≤ x then (J i : ℝ) else 0) - mertens x| ≤
          32 * (Y : ℝ) / (y : ℝ)) ∧
      (∀ A B : ℝ, (Y : ℝ) / 2 ≤ A → B ≤ A * (1 + smoothJumpWidth d / (y : ℝ)) →
        (∑ i ∈ range m, if A ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ B then |(J i : ℝ)| else 0) ≤
          (2000 * smoothJumpWidth d + 2000) * ((Y : ℝ) / (y : ℝ))) ∧
      (∑ i ∈ range m, |(J i : ℝ)|) ≤
        60 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
          (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) * (Y : ℝ) ^ (2 * (Θ + ε) - 1) +
          8 * (Y : ℝ) / (y : ℝ) := by
  classical
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hY_ge16y : 16 * y ≤ Y :=
    le_trans (Nat.mul_le_mul_right y (smoothJumpBase_ge_sixteen hd)) hY_lo
  have hY_pos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hΔ_ge16 : (16 : ℝ) ≤ (Y : ℝ) / (y : ℝ) := by
    rw [le_div_iff₀ hy_pos]; exact_mod_cast hY_ge16y
  obtain ⟨Δ, hΔ_def⟩ : ∃ Δ : ℝ, Δ = (Y : ℝ) / (y : ℝ) := ⟨_, rfl⟩
  have hΔ_pos : 0 < Δ := by rw [hΔ_def]; positivity
  obtain ⟨τ₀, hτ₀, hE_le⟩ := exists_octave_min_shift hΘ hε0 hC_pl hpl hy hY_pos
  obtain ⟨θ, hθ_def⟩ : ∃ θ : ℝ, θ = 1 / (16 * (y : ℝ)) := ⟨_, rfl⟩
  obtain ⟨M_grid, hM_def⟩ : ∃ M_grid : ℕ, M_grid = Nat.log 2 (16 * y) + 1 := ⟨_, rfl⟩
  obtain ⟨N, hN_def⟩ : ∃ N : ℕ, N = M_grid + 1 := ⟨_, rfl⟩
  obtain ⟨lam₀, hlam_def⟩ : ∃ lam₀ : ℝ, lam₀ = 1 / ((2 ^ M_grid : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hθ_def, ← hM_def, ← hN_def, ← hlam_def] at hE_le
  have hθ0 : 0 < θ := by rw [hθ_def]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ_def, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
    linarith
  have h2M_gt : 16 * y < 2 ^ M_grid := by
    rw [hM_def]; exact Nat.lt_pow_succ_log_self (by norm_num) (16 * y)
  have h2M_le : 2 ^ M_grid ≤ 32 * y := by
    rw [hM_def, pow_succ]
    have := Nat.pow_log_le_self 2 (by omega : 16 * y ≠ 0)
    omega
  have hlam₀_pos : 0 < lam₀ := by rw [hlam_def]; positivity
  have hlam₀_le : lam₀ ≤ 1 / (16 * (y : ℝ)) := by
    rw [hlam_def]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h2M_gt.le)
  have hlam₀_ge : 1 / (32 * (y : ℝ)) ≤ lam₀ := by
    rw [hlam_def]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h2M_le)
  have h2N_lam₀ : ((2 ^ N : ℕ) : ℝ) * lam₀ = 2 := by
    rw [hN_def, hlam_def, pow_succ]; push_cast; field_simp
  have hexp_lam₀_sub : Real.exp lam₀ - 1 ≤ 2 * lam₀ :=
    exp_lam₀_sub_one_le hlam₀_pos (hlam₀_le.trans (hθ_def ▸ hθ1))
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ℝ, g = octaveSample θ Y N lam₀ τ₀ := ⟨_, rfl⟩
  rw [← hg_def] at hE_le
  have hg_step : ∀ k : ℕ, |g (k + 1) - g k| ≤ 3 * Δ := by
    intro k
    rw [hg_def]
    rcases le_or_gt (2 ^ N) k with hge | hlt
    · simp only [octaveSample, min_eq_right (by omega : 2 ^ N ≤ k + 1),
        min_eq_right hge, sub_self, abs_zero]
      positivity
    · simp only [octaveSample, min_eq_left (by omega : k + 1 ≤ 2 ^ N), min_eq_left hlt.le]
      set X₁ := Real.exp (octaveGrid Y lam₀ τ₀ k)
      set X₂ := Real.exp (octaveGrid Y lam₀ τ₀ (k + 1))
      have hX₂_eq : X₂ = X₁ * Real.exp lam₀ := by
        dsimp [X₁, X₂, octaveGrid]; rw [← Real.exp_add]; congr 1; push_cast; ring
      have h12 : X₁ ≤ X₂ := by
        rw [hX₂_eq]
        exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp hlam₀_pos.le)
      have hst := abs_smoothMertens_step_le hθ0 (Real.exp_pos _) h12
      have hX₂_bd : X₂ ≤ 8 * (Y : ℝ) :=
        exp_octaveGrid_le_eight_mul hY_pos hlam₀_pos h2N_lam₀ hτ₀ (by omega)
      have hX₁_bd : X₁ ≤ 8 * (Y : ℝ) := h12.trans hX₂_bd
      have hdiff_X : X₂ - X₁ ≤ Δ := by
        have : X₂ - X₁ = X₁ * (Real.exp lam₀ - 1) := by rw [hX₂_eq]; ring
        rw [this, hΔ_def]
        calc X₁ * (Real.exp lam₀ - 1) ≤ (8 * (Y : ℝ)) * (2 * lam₀) :=
              mul_le_mul hX₁_bd hexp_lam₀_sub
                (by linarith [Real.one_le_exp hlam₀_pos.le]) (by positivity)
          _ ≤ (8 * (Y : ℝ)) * (2 * (1 / (16 * (y : ℝ)))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlam₀_le (by norm_num)) (by positivity)
          _ = (Y : ℝ) / (y : ℝ) := by ring
      have hθX : θ * X₁ + θ * X₂ ≤ Δ := by
        rw [hθ_def, hΔ_def]
        calc (1 / (16 * (y : ℝ))) * X₁ + (1 / (16 * (y : ℝ))) * X₂
            = (1 / (16 * (y : ℝ))) * (X₁ + X₂) := by ring
          _ ≤ (1 / (16 * (y : ℝ))) * (16 * (Y : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = (Y : ℝ) / (y : ℝ) := by ring
      linarith
  have happrox_pt : ∀ x : ℕ, Y ≤ x → x ≤ Z →
      |(greedyApprox g Δ (octaveIdx Y N lam₀ τ₀ (x : ℝ)) : ℝ) - mertens x| ≤ 4 * Δ := by
    intro x hxY hxZ
    have hxY_R : (Y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxY
    have hx2Y_R : (x : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast (hxZ.trans hZ2Y)
    obtain ⟨_, hkx_le⟩ := octaveIdx_spec hY_pos hτ₀ hxY_R
    obtain ⟨hkx_lt, hkx_gt⟩ := octaveIdx_lt_2N hY_pos h2N_lam₀ hτ₀ hxY_R hx2Y_R
    set kx := octaveIdx Y N lam₀ τ₀ (x : ℝ)
    have hx_sub : (x : ℝ) - Real.exp (octaveGrid Y lam₀ τ₀ kx) ≤ Δ := by
      have heq : Real.exp (octaveGrid Y lam₀ τ₀ (kx + 1)) =
          Real.exp (octaveGrid Y lam₀ τ₀ kx) * Real.exp lam₀ := by
        dsimp [octaveGrid]; rw [← Real.exp_add]; congr 1; push_cast; ring
      have h1 : (x : ℝ) - Real.exp (octaveGrid Y lam₀ τ₀ kx) ≤
          Real.exp (octaveGrid Y lam₀ τ₀ kx) * (Real.exp lam₀ - 1) := by linarith
      have hX_le_2Y : Real.exp (octaveGrid Y lam₀ τ₀ kx) ≤ 2 * (Y : ℝ) := hkx_le.trans hx2Y_R
      rw [hΔ_def]
      calc (x : ℝ) - Real.exp (octaveGrid Y lam₀ τ₀ kx)
          ≤ (2 * (Y : ℝ)) * (2 * (1 / (16 * (y : ℝ)))) :=
            h1.trans (mul_le_mul hX_le_2Y
              (hexp_lam₀_sub.trans (mul_le_mul_of_nonneg_left hlam₀_le (by norm_num)))
              (by linarith [Real.one_le_exp hlam₀_pos.le]) (by positivity))
        _ ≤ (Y : ℝ) / (y : ℝ) := by
            have : (2 * (Y : ℝ)) * (2 * (1 / (16 * (y : ℝ)))) = (1 / 4) * ((Y : ℝ) / (y : ℝ)) := by
              ring
            rw [this]; linarith [div_pos hY_pos hy_pos]
    have hg_kx : g kx = smoothMertens θ (Real.exp (octaveGrid Y lam₀ τ₀ kx)) := by
      rw [hg_def]; simp [octaveSample, min_eq_left hkx_lt.le]
    have h1 := abs_greedyApprox_sub_le g hΔ_pos kx
    rw [hg_kx] at h1
    have h2 := abs_smoothMertens_sub_mertens_nat_le hθ0 (Real.exp_pos _) hkx_le
    have hθ_bd : θ * Real.exp (octaveGrid Y lam₀ τ₀ kx) ≤ Δ := by
      rw [hθ_def, hΔ_def]
      calc (1 / (16 * (y : ℝ))) * Real.exp (octaveGrid Y lam₀ τ₀ kx)
          ≤ (1 / (16 * (y : ℝ))) * (2 * (Y : ℝ)) :=
            mul_le_mul_of_nonneg_left (hkx_le.trans hx2Y_R) (by positivity)
        _ ≤ (Y : ℝ) / (y : ℝ) := by
            have : (1 / (16 * (y : ℝ))) * (2 * (Y : ℝ)) = (1 / 8) * ((Y : ℝ) / (y : ℝ)) := by ring
            rw [this]; linarith [div_pos hY_pos hy_pos]
    have htri : |(greedyApprox g Δ kx : ℝ) - mertens x| ≤
        |(greedyApprox g Δ kx : ℝ) - smoothMertens θ (Real.exp (octaveGrid Y lam₀ τ₀ kx))| +
          |smoothMertens θ (Real.exp (octaveGrid Y lam₀ τ₀ kx)) - mertens x| := by
      have : (greedyApprox g Δ kx : ℝ) - mertens x =
          ((greedyApprox g Δ kx : ℝ) - smoothMertens θ (Real.exp (octaveGrid Y lam₀ τ₀ kx))) +
            (smoothMertens θ (Real.exp (octaveGrid Y lam₀ τ₀ kx)) - mertens x) := by ring
      rw [this]; exact abs_add_le _ _
    have h1_le_Δ : 2 ≤ Δ := by linarith [hΔ_def ▸ hΔ_ge16]
    linarith
  obtain ⟨k_lo, hklo_def⟩ : ∃ k_lo : ℕ, k_lo = octaveIdx Y N lam₀ τ₀ (Y : ℝ) := ⟨_, rfl⟩
  obtain ⟨k_hi, hkhi_def⟩ : ∃ k_hi : ℕ, k_hi = octaveIdx Y N lam₀ τ₀ (Z : ℝ) := ⟨_, rfl⟩
  have hk_lo_hi : k_lo ≤ k_hi := by
    rw [hklo_def, hkhi_def]; exact octaveIdx_mono (by exact_mod_cast hYZ.le)
  have hk_hi_lt : k_hi < 2 ^ N := by
    rw [hkhi_def]
    exact (octaveIdx_lt_2N hY_pos h2N_lam₀ hτ₀
      (by exact_mod_cast hYZ.le) (by exact_mod_cast hZ2Y)).1
  obtain ⟨L, hL_def⟩ : ∃ L : ℕ, L = k_hi - k_lo := ⟨_, rfl⟩
  obtain ⟨m_tot, hm_def⟩ : ∃ m_tot : ℕ, m_tot = L + 2 := ⟨_, rfl⟩
  obtain ⟨z_fn, hz_def⟩ : ∃ z_fn, z_fn = octaveZ Y Z k_lo lam₀ τ₀ := ⟨_, rfl⟩
  obtain ⟨J_fn, hJ_def⟩ : ∃ J_fn, J_fn = octaveJ Y Z k_lo k_hi g Δ := ⟨_, rfl⟩
  have hz_range : ∀ i < m_tot, Y < z_fn i ∧ z_fn i ≤ Z := by
    intro i hi
    rw [hz_def]
    by_cases h0 : i = 0
    · subst h0; simp [octaveZ]; omega
    by_cases h1 : i = 1
    · subst h1; simp only [octaveZ, one_ne_zero, ↓reduceIte]; exact ⟨hYZ, le_rfl⟩
    simp only [octaveZ, h0, h1, ↓reduceIte]
    have hjL : i - 2 < L := by rw [hm_def] at hi; omega
    have hk_gt : (Y : ℝ) < Real.exp (octaveGrid Y lam₀ τ₀ (k_lo + (i - 2) + 1)) := by
      have hsucc := (octaveIdx_lt_2N hY_pos h2N_lam₀ hτ₀ le_rfl (by linarith)).2
      rw [← hklo_def] at hsucc
      refine lt_of_lt_of_le hsucc (Real.exp_le_exp.mpr ?_)
      dsimp [octaveGrid]
      have hle : ((k_lo + 1 : ℕ) : ℝ) ≤ ((k_lo + (i - 2) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : k_lo + 1 ≤ k_lo + (i - 2) + 1)
      have hm := mul_le_mul_of_nonneg_right hle hlam₀_pos.le
      linarith only [hm]
    have hk_le : Real.exp (octaveGrid Y lam₀ τ₀ (k_lo + (i - 2) + 1)) ≤ (Z : ℝ) := by
      have hspec := (octaveIdx_spec (N := N) (lam₀ := lam₀) hY_pos hτ₀
        (by exact_mod_cast hYZ.le : (Y : ℝ) ≤ (Z : ℝ))).2
      rw [← hkhi_def] at hspec
      refine le_trans (Real.exp_le_exp.mpr ?_) hspec
      dsimp [octaveGrid]
      have hle : ((k_lo + (i - 2) + 1 : ℕ) : ℝ) ≤ (k_hi : ℝ) := by
        exact_mod_cast (by omega : k_lo + (i - 2) + 1 ≤ k_hi)
      have hm := mul_le_mul_of_nonneg_right hle hlam₀_pos.le
      linarith only [hm]
    exact ⟨by exact_mod_cast (lt_of_lt_of_le hk_gt (Nat.le_ceil _)), Nat.ceil_le.mpr hk_le⟩
  have hsum_split : ∀ φ : ℕ → ℝ,
      ∑ i ∈ range m_tot, φ i = φ 0 + φ 1 + ∑ j ∈ range L, φ (j + 2) := by
    intro φ
    have h1 : m_tot = 2 + L := by rw [hm_def]; omega
    rw [h1, sum_range_add, Finset.sum_range_succ, sum_range_one]
    congr 1
    exact sum_congr rfl fun j _ => by congr 1; omega
  have hJ0_abs : |(J_fn 0 : ℝ)| ≤ 4 * Δ := by
    rw [hJ_def]; simp only [octaveJ, ↓reduceIte, Int.cast_sub, cast_mertensInt, hklo_def]
    exact happrox_pt Y le_rfl hYZ.le
  have hJ1_abs : |(J_fn 1 : ℝ)| ≤ 4 * Δ := by
    rw [hJ_def]
    simp only [octaveJ, one_ne_zero, ↓reduceIte, Int.cast_sub, cast_mertensInt, hkhi_def]
    rw [abs_sub_comm]
    exact happrox_pt Z hYZ.le le_rfl
  have hz_j2 : ∀ j : ℕ, z_fn (j + 2) = ⌈Real.exp (octaveGrid Y lam₀ τ₀ (k_lo + j + 1))⌉₊ := by
    intro j; rw [hz_def]; simp [octaveZ]
  have hJ_j2 : ∀ j : ℕ, J_fn (j + 2) = greedyJump g Δ (k_lo + j) := by
    intro j; rw [hJ_def]; simp [octaveJ]
  have hJmid_abs : ∀ k : ℕ, |(greedyJump g Δ k : ℝ)| ≤ 5 * Δ := fun k => by
    have hj := abs_greedyJump_le g hΔ_pos hg_step k
    have hΔ16 : 16 ≤ Δ := by rwa [hΔ_def]
    linarith only [hj, hΔ16]
  have hmid_sum : ∑ j ∈ range L, (J_fn (j + 2) : ℝ) =
      (greedyApprox g Δ k_hi : ℝ) - (greedyApprox g Δ k_lo : ℝ) := by
    have heq : ∑ j ∈ range L, (J_fn (j + 2) : ℝ) =
        ((∑ k ∈ Ico k_lo k_hi, greedyJump g Δ k : ℤ) : ℝ) := by
      rw [Int.cast_sum, sum_Ico_eq_sum_range, ← hL_def]
      exact sum_congr rfl fun j _ => by rw [hJ_j2]
    rw [heq, sum_Ico_greedyJump g Δ hk_lo_hi, Int.cast_sub]
  refine ⟨m_tot, z_fn, J_fn, hz_range, ?_, ?_, ?_, ?_⟩
  · rw [hsum_split fun i => (J_fn i : ℝ), hmid_sum, hJ_def]
    simp only [octaveJ, ↓reduceIte, one_ne_zero, Int.cast_sub, cast_mertensInt]
    ring
  · intro x hxY hxZ
    rcases eq_or_lt_of_le hxY with rfl | hx_gt_Y
    · rw [sum_congr rfl fun i hi => if_neg (by
        have := (hz_range i (Finset.mem_range.mp hi)).1; omega)]
      simp only [sum_const_zero, add_zero, sub_self, abs_zero]; positivity
    rcases eq_or_lt_of_le hxZ with rfl | hx_lt_Z
    · rw [sum_congr rfl fun i hi => if_pos (hz_range i (Finset.mem_range.mp hi)).2,
        hsum_split fun i => (J_fn i : ℝ), hmid_sum, hJ_def]
      simp only [octaveJ, ↓reduceIte, one_ne_zero, Int.cast_sub, cast_mertensInt]
      have hzero : mertens Y + ((greedyApprox g Δ k_lo - mertens Y) +
          (mertens x - greedyApprox g Δ k_hi) +
          (greedyApprox g Δ k_hi - greedyApprox g Δ k_lo)) - mertens x = 0 := by ring
      rw [hzero, abs_zero]; positivity
    · obtain ⟨kx, hkx_def⟩ : ∃ kx : ℕ, kx = octaveIdx Y N lam₀ τ₀ (x : ℝ) := ⟨_, rfl⟩
      have hkx_lo : k_lo ≤ kx := by
        rw [hklo_def, hkx_def]; exact octaveIdx_mono (by exact_mod_cast hxY)
      have hkx_hi : kx ≤ k_hi := by
        rw [hkx_def, hkhi_def]; exact octaveIdx_mono (by exact_mod_cast hxZ)
      rw [hsum_split fun i => if z_fn i ≤ x then (J_fn i : ℝ) else 0]
      have hz0 : z_fn 0 ≤ x := by rw [hz_def]; simp [octaveZ]; omega
      have hz1 : ¬ z_fn 1 ≤ x := by rw [hz_def]; simp [octaveZ]; omega
      rw [if_pos hz0, if_neg hz1, add_zero]
      have hcond : ∀ j < L, (z_fn (j + 2) ≤ x ↔ j < kx - k_lo) := by
        intro j _
        rw [hz_j2 j, Nat.ceil_le]
        constructor
        · intro hle
          by_contra hge
          push Not at hge
          have hlt_exp := (octaveIdx_lt_2N hY_pos h2N_lam₀ hτ₀
            (by exact_mod_cast hxY : (Y : ℝ) ≤ (x : ℝ))
            (by exact_mod_cast (hxZ.trans hZ2Y))).2
          rw [← hkx_def] at hlt_exp
          have hmon_w : octaveGrid Y lam₀ τ₀ (kx + 1) ≤ octaveGrid Y lam₀ τ₀ (k_lo + j + 1) := by
            dsimp [octaveGrid]
            have hnat : ((kx + 1 : ℕ) : ℝ) ≤ ((k_lo + j + 1 : ℕ) : ℝ) := by
              exact_mod_cast (by omega : kx + 1 ≤ k_lo + j + 1)
            have hm := mul_le_mul_of_nonneg_right hnat hlam₀_pos.le
            linarith only [hm]
          have hexp_mon := Real.exp_le_exp.mpr hmon_w
          linarith only [hle, hlt_exp, hexp_mon]
        · intro hlt_j
          have hspec := (octaveIdx_spec (N := N) (lam₀ := lam₀) hY_pos hτ₀
            (by exact_mod_cast hxY : (Y : ℝ) ≤ (x : ℝ))).2
          rw [← hkx_def] at hspec
          refine le_trans (Real.exp_le_exp.mpr ?_) hspec
          dsimp [octaveGrid]
          have hnat : ((k_lo + j + 1 : ℕ) : ℝ) ≤ (kx : ℝ) := by
            exact_mod_cast (by omega : k_lo + j + 1 ≤ kx)
          have hm := mul_le_mul_of_nonneg_right hnat hlam₀_pos.le
          linarith only [hm]
      have hmid_x : ∑ j ∈ range L, (if z_fn (j + 2) ≤ x then (J_fn (j + 2) : ℝ) else 0) =
          (greedyApprox g Δ kx : ℝ) - (greedyApprox g Δ k_lo : ℝ) := by
        have hsplit_r : range L = range (kx - k_lo) ∪ Ico (kx - k_lo) L := by
          ext j; simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        have hdisj_r : Disjoint (range (kx - k_lo)) (Ico (kx - k_lo) L) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
        rw [hsplit_r, sum_union hdisj_r]
        have hright : ∑ j ∈ Ico (kx - k_lo) L,
            (if z_fn (j + 2) ≤ x then (J_fn (j + 2) : ℝ) else 0) = 0 :=
          sum_eq_zero fun j hj => by
            obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
            rw [if_neg]; rw [hcond j hj2]; omega
        have hleft : ∑ j ∈ range (kx - k_lo),
            (if z_fn (j + 2) ≤ x then (J_fn (j + 2) : ℝ) else 0) =
            ((∑ k ∈ Ico k_lo kx, greedyJump g Δ k : ℤ) : ℝ) := by
          rw [Int.cast_sum, sum_Ico_eq_sum_range]
          refine sum_congr rfl fun j hj => ?_
          rw [Finset.mem_range] at hj
          rw [if_pos ((hcond j (by omega)).mpr hj), hJ_j2]
        rw [hright, add_zero, hleft, sum_Ico_greedyJump g Δ hkx_lo, Int.cast_sub]
      rw [hmid_x]
      have hid : mertens Y + ((J_fn 0 : ℝ) +
          ((greedyApprox g Δ kx : ℝ) - (greedyApprox g Δ k_lo : ℝ))) - mertens x =
          (greedyApprox g Δ kx : ℝ) - mertens x := by
        rw [hJ_def]; simp only [octaveJ, ↓reduceIte, Int.cast_sub, cast_mertensInt]; ring
      rw [hid, hkx_def]
      refine (happrox_pt x hxY hxZ).trans ?_
      rw [hΔ_def, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hY_pos.le hy_pos.le)
  · intro A B hAY hBA
    rw [hsum_split fun i => if A ≤ (z_fn i : ℝ) ∧ (z_fn i : ℝ) ≤ B then |(J_fn i : ℝ)| else 0]
    have h01 : (if A ≤ (z_fn 0 : ℝ) ∧ (z_fn 0 : ℝ) ≤ B then |(J_fn 0 : ℝ)| else 0) +
        (if A ≤ (z_fn 1 : ℝ) ∧ (z_fn 1 : ℝ) ≤ B then |(J_fn 1 : ℝ)| else 0) ≤ 8 * Δ := by
      have b0 : (if A ≤ (z_fn 0 : ℝ) ∧ (z_fn 0 : ℝ) ≤ B then |(J_fn 0 : ℝ)| else 0) ≤ 4 * Δ := by
        split_ifs; exact hJ0_abs; positivity
      have b1 : (if A ≤ (z_fn 1 : ℝ) ∧ (z_fn 1 : ℝ) ≤ B then |(J_fn 1 : ℝ)| else 0) ≤ 4 * Δ := by
        split_ifs; exact hJ1_abs; positivity
      linarith only [b0, b1]
    have hy1_R : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
    have hcard_hit := card_octave_hit_le (k_lo := k_lo) (L := L) (τ := τ₀)
      hy1_R hΔ_ge16 hlam₀_pos hlam₀_ge hAY hBA
    have hz_eq_0 : ∀ j : ℕ, z_fn (j + 2) = octaveZ Y 0 k_lo lam₀ τ₀ (j + 2) := by
      intro j; rw [hz_def]; simp [octaveZ]
    have hmid_hit : ∑ j ∈ range L,
        (if A ≤ (z_fn (j + 2) : ℝ) ∧ (z_fn (j + 2) : ℝ) ≤ B then |(J_fn (j + 2) : ℝ)| else 0) ≤
        (64 * smoothJumpWidth d + 65) * (5 * Δ) := by
      simp only [hz_eq_0]
      rw [← sum_filter]
      refine (sum_le_sum fun j _ => show |(J_fn (j + 2) : ℝ)| ≤ 5 * Δ from ?_).trans ?_
      · rw [hJ_j2]; exact hJmid_abs _
      · rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard_hit (by positivity)
    rw [← hΔ_def]
    have hcomb : 8 * Δ + (64 * smoothJumpWidth d + 65) * (5 * Δ) ≤
        (2000 * smoothJumpWidth d + 2000) * Δ := by
      have hw0 := smoothJumpWidth_pos d
      have hcoef : 8 + (64 * smoothJumpWidth d + 65) * 5 ≤ 2000 * smoothJumpWidth d + 2000 := by
        linarith only [hw0]
      calc 8 * Δ + (64 * smoothJumpWidth d + 65) * (5 * Δ)
          = (8 + (64 * smoothJumpWidth d + 65) * 5) * Δ := by ring
        _ ≤ (2000 * smoothJumpWidth d + 2000) * Δ :=
            mul_le_mul_of_nonneg_right hcoef hΔ_pos.le
    linarith only [h01, hmid_hit, hcomb]
  · rw [hsum_split fun i => |(J_fn i : ℝ)|]
    have hmid_tot : ∑ j ∈ range L, |(J_fn (j + 2) : ℝ)| ≤
        ((greedyExits N g Δ).card : ℝ) * (5 * Δ) := by
      have hterm_le : ∀ j ∈ range L, |(J_fn (j + 2) : ℝ)| ≤
          if k_lo + j ∈ greedyExits N g Δ then 5 * Δ else 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hJ_j2]
        split_ifs with hmem
        · exact hJmid_abs _
        · rw [greedyJump_eq_zero_of_notMem (by omega : k_lo + j < 2 ^ N) hmem]; simp
      refine (sum_le_sum hterm_le).trans ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hinj : Set.InjOn (fun j => k_lo + j)
          (((range L).filter fun j => k_lo + j ∈ greedyExits N g Δ) : Set ℕ) :=
        fun _ _ _ _ h => Nat.add_left_cancel h
      have hmaps : ∀ j ∈ (range L).filter (fun j => k_lo + j ∈ greedyExits N g Δ),
          k_lo + j ∈ greedyExits N g Δ := fun _ hj => (mem_filter.mp hj).2
      exact_mod_cast card_le_card_of_injOn _ hmaps hinj
    have hexp8 : Real.exp (4 * (Θ + ε)) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
    have hcs := card_greedyExits_mul_sq_le N g hΔ_pos
    have hN_le : (N : ℝ) + 1 ≤ (Nat.log 2 (16 * y) : ℝ) + 4 := by
      rw [hN_def, hM_def]; push_cast; linarith
    have hM_le : (M_grid : ℝ) + 1 ≤ (Nat.log 2 (16 * y) : ℝ) + 4 := by
      rw [hM_def]; push_cast; linarith
    have hcs2 : ((greedyExits N g Δ).card : ℝ) * Δ ^ 2 ≤
        12 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
          (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * (Θ + ε)) := by
      calc ((greedyExits N g Δ).card : ℝ) * Δ ^ 2
          ≤ 2 * ((N : ℝ) + 1) * dyadicEnergy N g := hcs
        _ ≤ 2 * ((Nat.log 2 (16 * y) : ℝ) + 4) *
            (6 * Real.exp (4 * (Θ + ε)) * C_pl * ((M_grid : ℝ) + 1) *
              (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * (Θ + ε))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hN_le (by norm_num : (0 : ℝ) ≤ 2))
              hE_le (dyadicEnergy_nonneg N g) (by positivity)
        _ ≤ 2 * ((Nat.log 2 (16 * y) : ℝ) + 4) *
            (6 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) *
              (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * (Θ + ε))) := by gcongr
        _ = 12 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
            (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * (Θ + ε)) := by ring
    have hdivΔ : ((greedyExits N g Δ).card : ℝ) * (5 * Δ) =
        (5 / Δ) * (((greedyExits N g Δ).card : ℝ) * Δ ^ 2) := by
      field_simp [hΔ_pos.ne']
    have hY_pow : (5 / Δ) * (Y : ℝ) ^ (2 * (Θ + ε)) =
        5 * (y : ℝ) * (Y : ℝ) ^ (2 * (Θ + ε) - 1) := by
      rw [hΔ_def]
      have : (Y : ℝ) ^ (2 * (Θ + ε)) = (Y : ℝ) * (Y : ℝ) ^ (2 * (Θ + ε) - 1) := by
        nth_rw 2 [← Real.rpow_one (Y : ℝ)]
        rw [← Real.rpow_add hY_pos]
        congr 1; ring
      rw [this]; field_simp [hY_pos.ne', hy_pos.ne']
    have hexits_bd : ((greedyExits N g Δ).card : ℝ) * (5 * Δ) ≤
        60 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
          (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) * (Y : ℝ) ^ (2 * (Θ + ε) - 1) := by
      rw [hdivΔ]
      calc (5 / Δ) * (((greedyExits N g Δ).card : ℝ) * Δ ^ 2)
          ≤ (5 / Δ) * (12 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
              (32 * (y : ℝ)) ^ (2 * ε) * (Y : ℝ) ^ (2 * (Θ + ε))) :=
            mul_le_mul_of_nonneg_left hcs2 (by positivity)
        _ = 12 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
              (32 * (y : ℝ)) ^ (2 * ε) * ((5 / Δ) * (Y : ℝ) ^ (2 * (Θ + ε))) := by ring
        _ = 60 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
              (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) * (Y : ℝ) ^ (2 * (Θ + ε) - 1) := by
            rw [hY_pow]; ring
    have h8 : 8 * Δ = 8 * (Y : ℝ) / (y : ℝ) := by rw [hΔ_def]; ring
    linarith [hJ0_abs, hJ1_abs, hmid_tot.trans hexits_bd, h8]

/-! ### Part 3: Global taut-string smooth Mertens stencil -/

/-- Minimum scale threshold for `y` at degree `d`. -/
def tautStencilMinY (d : ℕ) : ℕ :=
  max (4 * d + 5) (⌈2 * smoothJumpWidth d⌉₊ + 16)

private def octaveCut (T y₀ j : ℕ) : ℕ := min T (2 ^ j * y₀)

private lemma octaveCut_mono (T y₀ : ℕ) : Monotone (octaveCut T y₀) :=
  monotone_nat_of_le_succ fun j =>
    min_le_min_left T (Nat.mul_le_mul_right y₀ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)))

private lemma octaveCut_succ_le_two_mul (T y₀ j : ℕ) :
    octaveCut T y₀ (j + 1) ≤ 2 * octaveCut T y₀ j := by
  unfold octaveCut
  rw [pow_succ']
  rcases le_total T (2 ^ j * y₀) with h | h
  · have hle : T ≤ (2 * 2 ^ j) * y₀ :=
      h.trans (Nat.mul_le_mul_right y₀ (by omega : 2 ^ j ≤ 2 * 2 ^ j))
    rw [min_eq_left h, min_eq_left hle]; omega
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans_eq (by ring)

private def tautEvents (J : ℕ) (m_oct : ℕ → ℕ) : Finset (Option (ℕ × ℕ)) :=
  insert none (((range J).biUnion fun j =>
    (range (m_oct j)).map ⟨fun i => (j, i), fun _ _ h => (Prod.mk.inj h).2⟩).map
      Function.Embedding.some)

private def tautZ (T : ℕ) (z_oct : ℕ → ℕ → ℕ) : Option (ℕ × ℕ) → ℕ
  | none => T
  | some p => z_oct p.1 p.2

private def tautJ (T : ℕ) (J_oct : ℕ → ℕ → ℤ) : Option (ℕ × ℕ) → ℤ
  | none => -mertensInt T
  | some p => J_oct p.1 p.2

private def tautCoeff (y₀ : ℕ) (E : Finset (Option (ℕ × ℕ)))
    (k_ev : Option (ℕ × ℕ) → ℕ) (J_ev : Option (ℕ × ℕ) → ℤ) (k : ℕ) : ℤ :=
  if 1 ≤ k ∧ k ≤ y₀ then ArithmeticFunction.moebius k
  else ∑ e ∈ E, if k_ev e = k then J_ev e else 0

private lemma sum_tautEvents (J : ℕ) (m_oct : ℕ → ℕ) (φ : Option (ℕ × ℕ) → ℝ) :
    ∑ e ∈ tautEvents J m_oct, φ e =
      φ none + ∑ j ∈ range J, ∑ i ∈ range (m_oct j), φ (some (j, i)) := by
  unfold tautEvents
  rw [sum_insert (by simp), sum_map]
  congr 1
  have hdisj : (range J : Set ℕ).PairwiseDisjoint fun j =>
      (range (m_oct j)).map ⟨fun i => (j, i), fun _ _ h => (Prod.mk.inj h).2⟩ := by
    intro j₁ _ j₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    rcases mem_map.mp hp₁ with ⟨_, _, rfl⟩
    rcases mem_map.mp hp₂ with ⟨_, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm
  rw [sum_biUnion hdisj]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_map]; rfl

@[simp] private lemma tautZ_none (T : ℕ) (z_oct : ℕ → ℕ → ℕ) :
    tautZ T z_oct none = T := rfl

@[simp] private lemma tautZ_some (T : ℕ) (z_oct : ℕ → ℕ → ℕ) (j i : ℕ) :
    tautZ T z_oct (some (j, i)) = z_oct j i := rfl

@[simp] private lemma tautJ_none (T : ℕ) (J_oct : ℕ → ℕ → ℤ) :
    tautJ T J_oct none = -mertensInt T := rfl

@[simp] private lemma tautJ_some (T : ℕ) (J_oct : ℕ → ℕ → ℤ) (j i : ℕ) :
    tautJ T J_oct (some (j, i)) = J_oct j i := rfl

private lemma some_mem_tautEvents {J : ℕ} {m_oct : ℕ → ℕ} {j i : ℕ}
    (hj : j ∈ range J) (hi : i ∈ range (m_oct j)) :
    some (j, i) ∈ tautEvents J m_oct := by
  unfold tautEvents
  refine mem_insert_of_mem (mem_map.mpr ⟨(j, i), ?_, rfl⟩)
  exact mem_biUnion.mpr ⟨j, hj, mem_map.mpr ⟨i, hi, rfl⟩⟩

private lemma tautMass_combine {sHead sTail base C_var C_M J A B C lT : ℝ}
    (hbase0 : 0 ≤ base) (hCvar0 : 0 ≤ C_var) (hCM0 : 0 ≤ C_M)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hlT : 0 ≤ lT)
    (hhead : sHead ≤ base * A)
    (htail : sTail ≤ C_M * C + J * ((C_var / 2) * (1 + lT) ^ 2 * A + 8 * B))
    (hJ : J ≤ 2 * (1 + lT)) :
    sHead + sTail ≤
      (C_var + base + 500 + C_M) * ((1 + lT) ^ 3 * A + (1 + lT) * B + C) := by
  have h1 : 1 ≤ (1 + lT) ^ 3 := one_le_pow₀ (by linarith)
  have hbase_A : base * A ≤ base * ((1 + lT) ^ 3 * A) := by
    calc base * A = base * (1 * A) := by ring
      _ ≤ base * ((1 + lT) ^ 3 * A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hA0) hbase0
  have hJ_mul : J * ((C_var / 2) * (1 + lT) ^ 2 * A + 8 * B) ≤
      C_var * ((1 + lT) ^ 3 * A) + 16 * ((1 + lT) * B) := by
    calc J * ((C_var / 2) * (1 + lT) ^ 2 * A + 8 * B)
        ≤ (2 * (1 + lT)) * ((C_var / 2) * (1 + lT) ^ 2 * A + 8 * B) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = C_var * ((1 + lT) ^ 3 * A) + 16 * ((1 + lT) * B) := by ring
  set TA := (1 + lT) ^ 3 * A
  set TB := (1 + lT) * B
  have hTA0 : 0 ≤ TA := by positivity
  have hTB0 : 0 ≤ TB := by positivity
  have hsum : sHead + sTail ≤ (C_var + base) * TA + 16 * TB + C_M * C := by
    linarith [hhead.trans hbase_A, htail, hJ_mul]
  refine hsum.trans ?_
  have hexp : (C_var + base + 500 + C_M) * (TA + TB + C) =
      (C_var + base) * TA + (500 + C_M) * TA + (C_var + base + 484 + C_M) * TB + 16 * TB +
        (C_var + base + 500) * C + C_M * C := by ring
  rw [hexp]
  have p1 : 0 ≤ (500 + C_M) * TA := by positivity
  have p2 : 0 ≤ (C_var + base + 484 + C_M) * TB := by positivity
  have p3 : 0 ≤ (C_var + base + 500) * C := by positivity
  linarith

private lemma octave_var_scale {Θ ε C_pl : ℝ} {y T Yj : ℕ}
    (hΘ : 1 / 2 ≤ Θ) (hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4) (hC_pl : 0 < C_pl)
    (hy_pos : 0 < (y : ℝ)) (hYj_pos : 0 < (Yj : ℝ)) (hYj_T : Yj ≤ T)
    (hlog16y : (Nat.log 2 (16 * y) : ℝ) + 4 ≤ 16 * (1 + Real.log (T : ℝ))) :
    60 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
      (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) * (Yj : ℝ) ^ (2 * (Θ + ε) - 1) ≤
    ((60 * Real.exp 8 * C_pl * 1000 * 32) / 2) * (1 + Real.log (T : ℝ)) ^ 2 *
      ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) := by
  have hYj_le_T : (Yj : ℝ) ≤ (T : ℝ) := by exact_mod_cast hYj_T
  have hpow_T : (Yj : ℝ) ^ (2 * (Θ + ε) - 1) ≤ (T : ℝ) ^ (2 * (Θ + ε) - 1) :=
    Real.rpow_le_rpow hYj_pos.le hYj_le_T (by linarith)
  have h32y : (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) ≤ 32 * (y : ℝ) ^ (1 + 2 * ε) := by
    rw [Real.mul_rpow (by norm_num) hy_pos.le]
    have h32 : (32 : ℝ) ^ (2 * ε) ≤ 32 := by
      calc (32 : ℝ) ^ (2 * ε) ≤ (32 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 32 := Real.rpow_one _
    have hy_add : (y : ℝ) ^ (2 * ε) * (y : ℝ) = (y : ℝ) ^ (1 + 2 * ε) := by
      nth_rw 2 [← Real.rpow_one (y : ℝ)]
      rw [← Real.rpow_add hy_pos]
      congr 1; ring
    calc (32 : ℝ) ^ (2 * ε) * (y : ℝ) ^ (2 * ε) * (y : ℝ)
        = (32 : ℝ) ^ (2 * ε) * ((y : ℝ) ^ (2 * ε) * (y : ℝ)) := by ring
      _ = (32 : ℝ) ^ (2 * ε) * (y : ℝ) ^ (1 + 2 * ε) := by rw [hy_add]
      _ ≤ 32 * (y : ℝ) ^ (1 + 2 * ε) := mul_le_mul_of_nonneg_right h32 (by positivity)
  have hsq_log : ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 ≤ 256 * (1 + Real.log (T : ℝ)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hlog16y 2
    linarith
  have hprod1 : ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
      ((32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ)) * (Yj : ℝ) ^ (2 * (Θ + ε) - 1) ≤
      (256 * (1 + Real.log (T : ℝ)) ^ 2) *
        (32 * (y : ℝ) ^ (1 + 2 * ε)) * (T : ℝ) ^ (2 * (Θ + ε) - 1) :=
    mul_le_mul (mul_le_mul hsq_log h32y (by positivity) (by positivity))
      hpow_T (by positivity) (by positivity)
  calc 60 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
        (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) * (Yj : ℝ) ^ (2 * (Θ + ε) - 1)
      = (60 * Real.exp 8 * C_pl) * (((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
          ((32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ)) * (Yj : ℝ) ^ (2 * (Θ + ε) - 1)) := by ring
    _ ≤ (60 * Real.exp 8 * C_pl) * ((256 * (1 + Real.log (T : ℝ)) ^ 2) *
          (32 * (y : ℝ) ^ (1 + 2 * ε)) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) :=
        mul_le_mul_of_nonneg_left hprod1 (by positivity)
    _ ≤ ((60 * Real.exp 8 * C_pl * 1000 * 32) / 2) * (1 + Real.log (T : ℝ)) ^ 2 *
          ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) := by
        set K_core := Real.exp 8 * C_pl * (1 + Real.log (T : ℝ)) ^ 2 *
          ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1))
        have hK_nn : 0 ≤ K_core := by positivity
        have e1 : (60 * Real.exp 8 * C_pl) * ((256 * (1 + Real.log (T : ℝ)) ^ 2) *
            (32 * (y : ℝ) ^ (1 + 2 * ε)) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) =
            (60 * 256 * 32) * K_core := by dsimp [K_core]; ring
        have e2 : ((60 * Real.exp 8 * C_pl * 1000 * 32) / 2) * (1 + Real.log (T : ℝ)) ^ 2 *
            ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) =
            (60 * 500 * 32) * K_core := by dsimp [K_core]; ring
        rw [e1, e2]; linarith

private lemma card_hitOct_le_two (T y₀ J x : ℕ) :
    ((range J).filter fun j =>
      octaveCut T y₀ j < octaveCut T y₀ (j + 1) ∧
        (octaveCut T y₀ j : ℝ) < (x : ℝ) ∧ (x : ℝ) / 3 ≤ (octaveCut T y₀ j : ℝ)).card ≤ 2 := by
  set hitOct := (range J).filter fun j =>
    octaveCut T y₀ j < octaveCut T y₀ (j + 1) ∧
      (octaveCut T y₀ j : ℝ) < (x : ℝ) ∧ (x : ℝ) / 3 ≤ (octaveCut T y₀ j : ℝ)
  by_cases hne : hitOct.Nonempty
  · obtain ⟨j₀, hj₀_def⟩ : ∃ j₀, j₀ = hitOct.min' hne := ⟨_, rfl⟩
    obtain ⟨j₁, hj₁_def⟩ : ∃ j₁, j₁ = hitOct.max' hne := ⟨_, rfl⟩
    have hj₀ : j₀ ∈ hitOct := hj₀_def ▸ min'_mem hitOct hne
    have hj₁ : j₁ ∈ hitOct := hj₁_def ▸ max'_mem hitOct hne
    have hsub : hitOct ⊆ Icc j₀ j₁ := fun j hj =>
      Finset.mem_Icc.mpr ⟨hj₀_def ▸ min'_le hitOct j hj, hj₁_def ▸ le_max' hitOct j hj⟩
    have hj₀_le_j₁ : j₀ ≤ j₁ := hj₀_def ▸ min'_le hitOct j₁ hj₁
    have hcard_le : hitOct.card ≤ j₁ - j₀ + 1 := by
      have := card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    suffices j₁ - j₀ ≤ 1 by omega
    by_contra hgt1
    have hj1_ge : j₀ + 2 ≤ j₁ := by omega
    obtain ⟨_, hlt₁, hYj₁_x, _⟩ := mem_filter.mp hj₁
    obtain ⟨_, _, _, hx3_Yj₀⟩ := mem_filter.mp hj₀
    have hYj₁_eq : octaveCut T y₀ j₁ = 2 ^ j₁ * y₀ := by
      unfold octaveCut
      refine min_eq_right ?_
      by_contra hT_lt
      push Not at hT_lt
      have h1 : octaveCut T y₀ j₁ = T := min_eq_left hT_lt.le
      have h2 : octaveCut T y₀ (j₁ + 1) = T := min_eq_left (hT_lt.le.trans
        (Nat.mul_le_mul_right y₀ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j₁))))
      omega
    have hYj₀_le : octaveCut T y₀ j₀ ≤ 2 ^ j₀ * y₀ := min_le_right _ _
    have h4mul : 4 * octaveCut T y₀ j₀ ≤ octaveCut T y₀ j₁ := by
      rw [hYj₁_eq]
      calc 4 * octaveCut T y₀ j₀ ≤ 4 * (2 ^ j₀ * y₀) := Nat.mul_le_mul_left 4 hYj₀_le
        _ = 2 ^ (j₀ + 2) * y₀ := by rw [pow_add]; norm_num; ring
        _ ≤ 2 ^ j₁ * y₀ := Nat.mul_le_mul_right y₀ (Nat.pow_le_pow_right (by norm_num) hj1_ge)
    have h4R : 4 * (octaveCut T y₀ j₀ : ℝ) ≤ (octaveCut T y₀ j₁ : ℝ) := by exact_mod_cast h4mul
    linarith only [hYj₁_x, hx3_Yj₀, h4R]
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp

private lemma tautCoeff_prefix_sum {y₀ x : ℕ} {E : Finset (Option (ℕ × ℕ))}
    {k_ev : Option (ℕ × ℕ) → ℕ} {J_ev : Option (ℕ × ℕ) → ℤ}
    (hxy₀ : y₀ < x) (hk_lo : ∀ e ∈ E, y₀ < k_ev e) :
    ∑ k ∈ Icc 1 x, (tautCoeff y₀ E k_ev J_ev k : ℝ) =
      mertens y₀ + ∑ e ∈ E, if k_ev e ≤ x then (J_ev e : ℝ) else 0 := by
  have hsplit : Icc 1 x = Icc 1 y₀ ∪ Ioc y₀ x := by
    ext k; simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 y₀) (Ioc y₀ x) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    rw [Finset.mem_Icc] at hk1; rw [Finset.mem_Ioc] at hk2; omega
  rw [hsplit, sum_union hdisj]
  have h1 : ∑ k ∈ Icc 1 y₀, (tautCoeff y₀ E k_ev J_ev k : ℝ) = mertens y₀ := by
    rw [mertens]
    have hset : Icc 1 y₀ = Ioc 0 y₀ := by ext k; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hset]
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ioc] at hk
    rw [tautCoeff, if_pos ⟨by omega, hk.2⟩]
  have h2 : ∑ k ∈ Ioc y₀ x, (tautCoeff y₀ E k_ev J_ev k : ℝ) =
      ∑ e ∈ E, if k_ev e ≤ x then (J_ev e : ℝ) else 0 := by
    have hterm : ∀ k ∈ Ioc y₀ x, (tautCoeff y₀ E k_ev J_ev k : ℝ) =
        ∑ e ∈ E, if k_ev e = k then (J_ev e : ℝ) else 0 := by
      intro k hk; rw [Finset.mem_Ioc] at hk
      rw [tautCoeff, if_neg (by omega)]; simp
    rw [sum_congr rfl hterm, sum_comm]
    refine sum_congr rfl fun e he => ?_
    have hgt := hk_lo e he
    by_cases hkx : k_ev e ≤ x
    · rw [if_pos hkx, sum_eq_single (k_ev e)]
      · simp
      · intro k _ hne; exact if_neg hne.symm
      · intro hmem; exact absurd (Finset.mem_Ioc.mpr ⟨hgt, hkx⟩) hmem
    · rw [if_neg hkx]
      exact sum_eq_zero fun k hk => if_neg (by rw [Finset.mem_Ioc] at hk; omega)
  rw [h1, h2]

private lemma tautShift_diff_le {Θ ε C_M : ℝ} {d y y₀ T J x : ℕ}
    {m_oct : ℕ → ℕ} {z_oct : ℕ → ℕ → ℕ} {J_oct : ℕ → ℕ → ℤ}
    {k_ev : Option (ℕ × ℕ) → ℕ}
    (hC_M : 0 < C_M) (hy_pos : 0 < (y : ℝ)) (hx1 : 1 ≤ x)
    (h1E_le : 1 + smoothJumpWidth d / (y : ℝ) ≤ 3 / 2)
    (hM_T : |mertens T| ≤ C_M * (T : ℝ) ^ (Θ + ε))
    (hoct_empty : ∀ j : ℕ, ¬ octaveCut T y₀ j < octaveCut T y₀ (j + 1) → m_oct j = 0)
    (hoct_z : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      ∀ i < m_oct j, octaveCut T y₀ j < z_oct j i ∧ z_oct j i ≤ octaveCut T y₀ (j + 1))
    (hoct_cl : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      ∀ A B : ℝ, (octaveCut T y₀ j : ℝ) / 2 ≤ A →
        B ≤ A * (1 + smoothJumpWidth d / (y : ℝ)) →
        (∑ i ∈ range (m_oct j), if A ≤ (z_oct j i : ℝ) ∧ (z_oct j i : ℝ) ≤ B then
          |(J_oct j i : ℝ)| else 0) ≤
          (2000 * smoothJumpWidth d + 2000) * ((octaveCut T y₀ j : ℝ) / (y : ℝ)))
    (hk_zk : ∀ e ∈ tautEvents J m_oct,
      tautZ T z_oct e < k_ev e ∧
        (k_ev e : ℝ) ≤ (tautZ T z_oct e : ℝ) * (1 + smoothJumpWidth d / (y : ℝ)))
    (hk_2T : k_ev none ≤ 2 * T) :
    |((mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if tautZ T z_oct e ≤ x then (tautJ T J_oct e : ℝ) else 0) -
      (mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if k_ev e ≤ x then (tautJ T J_oct e : ℝ) else 0))| ≤
      (if T ≤ x ∧ x ≤ 2 * T then C_M * (T : ℝ) ^ (Θ + ε) else 0) +
        2 * (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) := by
  have hxR_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hsub_eq : (mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if tautZ T z_oct e ≤ x then (tautJ T J_oct e : ℝ) else 0) -
      (mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if k_ev e ≤ x then (tautJ T J_oct e : ℝ) else 0) =
      ∑ e ∈ tautEvents J m_oct,
        if tautZ T z_oct e ≤ x ∧ x < k_ev e then (tautJ T J_oct e : ℝ) else 0 := by
    rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
    refine sum_congr rfl fun e he => ?_
    have hlt_zk := (hk_zk e he).1
    by_cases hkx : k_ev e ≤ x
    · rw [if_pos (by omega), if_pos hkx, if_neg (by omega), sub_self]
    · by_cases hzx : tautZ T z_oct e ≤ x
      · rw [if_pos hzx, if_neg hkx, if_pos ⟨hzx, by omega⟩, sub_zero]
      · rw [if_neg hzx, if_neg hkx, if_neg (fun h => hzx h.1), sub_zero]
  rw [hsub_eq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have habs_ite : ∑ e ∈ tautEvents J m_oct,
      |if tautZ T z_oct e ≤ x ∧ x < k_ev e then (tautJ T J_oct e : ℝ) else 0| =
      ∑ e ∈ tautEvents J m_oct,
        if tautZ T z_oct e ≤ x ∧ x < k_ev e then |(tautJ T J_oct e : ℝ)| else 0 :=
    sum_congr rfl fun _ _ => by split_ifs <;> simp
  rw [habs_ite, sum_tautEvents]
  simp only [tautZ_none, tautJ_none, tautZ_some, tautJ_some]
  refine add_le_add ?_ ?_
  · split_ifs with h1 h2
    · rw [Int.cast_neg, abs_neg, cast_mertensInt]; exact hM_T
    · exfalso; exact h2 ⟨h1.1, by omega⟩
    · positivity
    · exact le_rfl
  · obtain ⟨hitOct, hhit_def⟩ : ∃ hitOct : Finset ℕ, hitOct = (range J).filter fun j =>
        octaveCut T y₀ j < octaveCut T y₀ (j + 1) ∧
          (octaveCut T y₀ j : ℝ) < (x : ℝ) ∧ (x : ℝ) / 3 ≤ (octaveCut T y₀ j : ℝ) := ⟨_, rfl⟩
    have hoct_zero : ∀ j ∈ range J, j ∉ hitOct →
        ∑ i ∈ range (m_oct j),
          (if z_oct j i ≤ x ∧ x < k_ev (some (j, i)) then |(J_oct j i : ℝ)| else 0) = 0 := by
      intro j hj hnot_hit
      refine sum_eq_zero fun i hi => if_neg ?_
      rintro ⟨hzx, hxk⟩
      apply hnot_hit
      have hlt_j : octaveCut T y₀ j < octaveCut T y₀ (j + 1) := by
        rw [Finset.mem_range] at hi
        by_contra hno; rw [hoct_empty j hno] at hi; omega
      obtain ⟨hz_gt, hz_le⟩ := hoct_z j hlt_j i (Finset.mem_range.mp hi)
      have hk_le := (hk_zk (some (j, i)) (some_mem_tautEvents hj hi)).2
      rw [tautZ_some] at hk_le
      have hYj_lt_x : (octaveCut T y₀ j : ℝ) < (x : ℝ) :=
        by exact_mod_cast (lt_of_lt_of_le hz_gt hzx)
      have hx_lt_z : (x : ℝ) < (z_oct j i : ℝ) * (3 / 2) := by
        calc (x : ℝ) < (k_ev (some (j, i)) : ℝ) := by exact_mod_cast hxk
          _ ≤ (z_oct j i : ℝ) * (1 + smoothJumpWidth d / (y : ℝ)) := hk_le
          _ ≤ (z_oct j i : ℝ) * (3 / 2) :=
              mul_le_mul_of_nonneg_left h1E_le (Nat.cast_nonneg _)
      have hz_le_2Y : (z_oct j i : ℝ) ≤ 2 * (octaveCut T y₀ j : ℝ) :=
        by exact_mod_cast (hz_le.trans (octaveCut_succ_le_two_mul T y₀ j))
      rw [hhit_def]; exact mem_filter.mpr ⟨hj, hlt_j, hYj_lt_x, by linarith only [hx_lt_z, hz_le_2Y]⟩
    have hoct_hit_bd : ∀ j ∈ hitOct,
        ∑ i ∈ range (m_oct j),
          (if z_oct j i ≤ x ∧ x < k_ev (some (j, i)) then |(J_oct j i : ℝ)| else 0) ≤
        (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) := by
      intro j hj
      rw [hhit_def] at hj
      obtain ⟨hj_range, hlt_j, hYj_lt_x, _⟩ := mem_filter.mp hj
      obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = (x : ℝ) / (1 + smoothJumpWidth d / (y : ℝ)) := ⟨_, rfl⟩
      have hden : 0 < 1 + smoothJumpWidth d / (y : ℝ) := by
        have := smoothJumpWidth_pos d; positivity
      have hA_ge_half : (octaveCut T y₀ j : ℝ) / 2 ≤ A := by
        have h23 : (2 / 3 : ℝ) * (x : ℝ) ≤ A := by
          rw [hA_def, le_div_iff₀ hden]
          calc (2 / 3 : ℝ) * (x : ℝ) * (1 + smoothJumpWidth d / (y : ℝ))
              ≤ (2 / 3 : ℝ) * (x : ℝ) * (3 / 2) :=
                mul_le_mul_of_nonneg_left h1E_le (by positivity)
            _ = (x : ℝ) := by ring
        linarith only [hYj_lt_x, hxR_pos, h23]
      have hBA : (x : ℝ) ≤ A * (1 + smoothJumpWidth d / (y : ℝ)) := by
        rw [hA_def, div_mul_cancel₀ _ hden.ne']
      have hcl := hoct_cl j hlt_j A (x : ℝ) hA_ge_half hBA
      have hsub_sum : ∑ i ∈ range (m_oct j),
          (if z_oct j i ≤ x ∧ x < k_ev (some (j, i)) then |(J_oct j i : ℝ)| else 0) ≤
          ∑ i ∈ range (m_oct j),
            (if A ≤ (z_oct j i : ℝ) ∧ (z_oct j i : ℝ) ≤ (x : ℝ) then
              |(J_oct j i : ℝ)| else 0) := by
        refine sum_le_sum fun i hi => ?_
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          have hk_le := (hk_zk (some (j, i)) (some_mem_tautEvents hj_range hi)).2
          rw [tautZ_some] at hk_le
          refine ⟨?_, by exact_mod_cast h1.1⟩
          rw [hA_def, div_le_iff₀ hden]
          exact (by exact_mod_cast h1.2.le : (x : ℝ) ≤ (k_ev (some (j, i)) : ℝ)).trans hk_le
        · positivity
        · exact le_rfl
      refine hsub_sum.trans (hcl.trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [smoothJumpWidth_pos d])
      exact div_le_div_of_nonneg_right hYj_lt_x.le hy_pos.le
    have hsplit_oct : ∑ j ∈ range J, ∑ i ∈ range (m_oct j),
        (if z_oct j i ≤ x ∧ x < k_ev (some (j, i)) then |(J_oct j i : ℝ)| else 0) =
        ∑ j ∈ hitOct, ∑ i ∈ range (m_oct j),
          (if z_oct j i ≤ x ∧ x < k_ev (some (j, i)) then |(J_oct j i : ℝ)| else 0) :=
      (sum_subset (hhit_def ▸ filter_subset _ _) fun j hj hnot => hoct_zero j hj hnot).symm
    rw [hsplit_oct]
    have hcard_hit : (hitOct.card : ℝ) ≤ 2 := by
      rw [hhit_def]; exact_mod_cast card_hitOct_le_two T y₀ J x
    calc _ ≤ ∑ _j ∈ hitOct, (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) :=
          sum_le_sum hoct_hit_bd
      _ = (hitOct.card : ℝ) * ((2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) := by
          have hpos_r : 0 ≤ (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) := by
            have := smoothJumpWidth_pos d; positivity
          calc (hitOct.card : ℝ) * ((2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)))
              ≤ 2 * ((2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ))) :=
                mul_le_mul_of_nonneg_right hcard_hit hpos_r
            _ = _ := by ring

private lemma tautTel_prefix {T y₀ : ℕ} {m_oct : ℕ → ℕ} {J_oct : ℕ → ℕ → ℤ}
    (hY0 : octaveCut T y₀ 0 = y₀)
    (hoct_empty : ∀ j : ℕ, ¬ octaveCut T y₀ j < octaveCut T y₀ (j + 1) → m_oct j = 0)
    (hoct_tel : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      (∑ i ∈ range (m_oct j), (J_oct j i : ℝ)) =
        mertens (octaveCut T y₀ (j + 1)) - mertens (octaveCut T y₀ j))
    (r : ℕ) :
    mertens y₀ + (∑ j ∈ range r, ∑ i ∈ range (m_oct j), (J_oct j i : ℝ)) =
      mertens (octaveCut T y₀ r) := by
  induction r with
  | zero => simp [hY0]
  | succ r ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    by_cases hlt_r : octaveCut T y₀ r < octaveCut T y₀ (r + 1)
    · rw [hoct_tel r hlt_r]; ring
    · have heq_r : octaveCut T y₀ r = octaveCut T y₀ (r + 1) :=
        le_antisymm (octaveCut_mono T y₀ (Nat.le_succ r)) (not_lt.mp hlt_r)
      rw [hoct_empty r hlt_r, heq_r]; simp

private lemma tautUnshifted_lt_err {y y₀ T J x : ℕ}
    {m_oct : ℕ → ℕ} {z_oct : ℕ → ℕ → ℕ} {J_oct : ℕ → ℕ → ℤ}
    (hy_pos : 0 < (y : ℝ)) (hJ_pos : 0 < J)
    (hY0 : octaveCut T y₀ 0 = y₀) (hYJ : octaveCut T y₀ J = T)
    (hxy₀ : y₀ < x) (hx_lt_T : x < T)
    (hoct_empty : ∀ j : ℕ, ¬ octaveCut T y₀ j < octaveCut T y₀ (j + 1) → m_oct j = 0)
    (hoct_z : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      ∀ i < m_oct j, octaveCut T y₀ j < z_oct j i ∧ z_oct j i ≤ octaveCut T y₀ (j + 1))
    (hoct_tel : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      (∑ i ∈ range (m_oct j), (J_oct j i : ℝ)) =
        mertens (octaveCut T y₀ (j + 1)) - mertens (octaveCut T y₀ j))
    (hoct_pt : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      ∀ u : ℕ, octaveCut T y₀ j ≤ u → u ≤ octaveCut T y₀ (j + 1) →
        |(mertens (octaveCut T y₀ j) +
          ∑ i ∈ range (m_oct j), if z_oct j i ≤ u then (J_oct j i : ℝ) else 0) -
          mertens u| ≤ 32 * (octaveCut T y₀ j : ℝ) / (y : ℝ)) :
    |((mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if tautZ T z_oct e ≤ x then (tautJ T J_oct e : ℝ) else 0) - mertens x)| ≤
      32 * ((x : ℝ) / (y : ℝ)) := by
  have hex_j : ∃ j ∈ range J, octaveCut T y₀ j < x ∧ x ≤ octaveCut T y₀ (j + 1) := by
    set S_up := (range J).filter fun j => x ≤ octaveCut T y₀ (j + 1)
    have hne_up : S_up.Nonempty := by
      refine ⟨J - 1, mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [Nat.sub_add_cancel hJ_pos, hYJ]; exact hx_lt_T.le
    obtain ⟨jx, hjx_def⟩ : ∃ jx, jx = S_up.min' hne_up := ⟨_, rfl⟩
    have hjx_mem : jx ∈ S_up := hjx_def ▸ min'_mem S_up hne_up
    obtain ⟨hjx_range, hx_le_succ⟩ := mem_filter.mp hjx_mem
    refine ⟨jx, hjx_range, ?_, hx_le_succ⟩
    rcases Nat.eq_zero_or_pos jx with rfl | hjx_pos
    · rwa [hY0]
    · by_contra hle; push Not at hle
      have hprev : jx - 1 ∈ S_up := mem_filter.mpr
        ⟨Finset.mem_range.mpr (by rw [Finset.mem_range] at hjx_range; omega),
          by rwa [Nat.sub_add_cancel hjx_pos]⟩
      have hmin_le : jx ≤ jx - 1 := hjx_def ▸ min'_le S_up (jx - 1) hprev
      omega
  obtain ⟨jx, hjx_range, hYjx_lt, hx_Yjx1⟩ := hex_j
  rw [Finset.mem_range] at hjx_range
  have hlt_jx : octaveCut T y₀ jx < octaveCut T y₀ (jx + 1) := lt_of_lt_of_le hYjx_lt hx_Yjx1
  rw [sum_tautEvents]
  simp only [tautZ_none, tautZ_some, tautJ_some]
  rw [if_neg (by omega : ¬ T ≤ x), zero_add]
  have hsplit_J : range J = insert jx (range jx ∪ Ico (jx + 1) J) := by
    ext j; simp [Finset.mem_range, Finset.mem_insert, Finset.mem_union, Finset.mem_Ico]; omega
  have hnot_jx : jx ∉ range jx ∪ Ico (jx + 1) J := by
    simp [Finset.mem_range, Finset.mem_Ico]
  have hdisj_J : Disjoint (range jx) (Ico (jx + 1) J) := by
    rw [Finset.disjoint_left]; intro j hj1 hj2
    rw [Finset.mem_range] at hj1; rw [Finset.mem_Ico] at hj2; omega
  rw [hsplit_J, sum_insert hnot_jx, sum_union hdisj_J]
  have hleft_all : ∑ j ∈ range jx, ∑ i ∈ range (m_oct j),
      (if z_oct j i ≤ x then (J_oct j i : ℝ) else 0) =
      ∑ j ∈ range jx, ∑ i ∈ range (m_oct j), (J_oct j i : ℝ) := by
    refine sum_congr rfl fun j hj => sum_congr rfl fun i hi => if_pos ?_
    rw [Finset.mem_range] at hj hi
    have hlt_j : octaveCut T y₀ j < octaveCut T y₀ (j + 1) := by
      by_contra hno; rw [hoct_empty j hno] at hi; omega
    have hz_le := (hoct_z j hlt_j i hi).2
    have hmon : octaveCut T y₀ (j + 1) ≤ octaveCut T y₀ jx := octaveCut_mono T y₀ (by omega)
    omega
  have hright_zero : ∑ j ∈ Ico (jx + 1) J, ∑ i ∈ range (m_oct j),
      (if z_oct j i ≤ x then (J_oct j i : ℝ) else 0) = 0 := by
    refine sum_eq_zero fun j hj => sum_eq_zero fun i hi => if_neg ?_
    obtain ⟨hj1, _⟩ := Finset.mem_Ico.mp hj
    rw [Finset.mem_range] at hi
    have hlt_j : octaveCut T y₀ j < octaveCut T y₀ (j + 1) := by
      by_contra hno; rw [hoct_empty j hno] at hi; omega
    have hz_gt := (hoct_z j hlt_j i hi).1
    have hmon : octaveCut T y₀ (jx + 1) ≤ octaveCut T y₀ j := octaveCut_mono T y₀ hj1
    omega
  rw [hleft_all, hright_zero, add_zero]
  have htel := tautTel_prefix hY0 hoct_empty hoct_tel jx
  have hrearr : mertens y₀ + ((∑ i ∈ range (m_oct jx),
        if z_oct jx i ≤ x then (J_oct jx i : ℝ) else 0) +
      ∑ j ∈ range jx, ∑ i ∈ range (m_oct j), (J_oct j i : ℝ)) =
      mertens (octaveCut T y₀ jx) + ∑ i ∈ range (m_oct jx),
        if z_oct jx i ≤ x then (J_oct jx i : ℝ) else 0 := by
    linarith only [htel]
  rw [hrearr]
  refine (hoct_pt jx hlt_jx x hYjx_lt.le hx_Yjx1).trans ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (by exact_mod_cast hYjx_lt.le) hy_pos.le) (by norm_num)

private lemma tautUnshifted_ge_eq_zero {y₀ T J x : ℕ}
    {m_oct : ℕ → ℕ} {z_oct : ℕ → ℕ → ℕ} {J_oct : ℕ → ℕ → ℤ}
    (hY0 : octaveCut T y₀ 0 = y₀) (hYJ : octaveCut T y₀ J = T) (hx_ge_T : T ≤ x)
    (hz_hi : ∀ e ∈ tautEvents J m_oct, tautZ T z_oct e ≤ T)
    (hoct_empty : ∀ j : ℕ, ¬ octaveCut T y₀ j < octaveCut T y₀ (j + 1) → m_oct j = 0)
    (hoct_tel : ∀ j : ℕ, octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
      (∑ i ∈ range (m_oct j), (J_oct j i : ℝ)) =
        mertens (octaveCut T y₀ (j + 1)) - mertens (octaveCut T y₀ j)) :
    mertens y₀ + (∑ e ∈ tautEvents J m_oct,
      if tautZ T z_oct e ≤ x then (tautJ T J_oct e : ℝ) else 0) = 0 := by
  rw [sum_tautEvents]
  have hall_oct : ∑ j ∈ range J, ∑ i ∈ range (m_oct j),
      (if tautZ T z_oct (some (j, i)) ≤ x then (tautJ T J_oct (some (j, i)) : ℝ) else 0) =
      ∑ j ∈ range J, ∑ i ∈ range (m_oct j), (J_oct j i : ℝ) := by
    refine sum_congr rfl fun j hj => sum_congr rfl fun i hi => ?_
    have hle : tautZ T z_oct (some (j, i)) ≤ x :=
      (hz_hi _ (some_mem_tautEvents hj hi)).trans hx_ge_T
    rw [if_pos hle, tautJ_some]
  rw [hall_oct, if_pos (by simp [hx_ge_T] : tautZ T z_oct none ≤ x),
    tautJ_none, Int.cast_neg, cast_mertensInt]
  have htel := tautTel_prefix hY0 hoct_empty hoct_tel J
  rw [hYJ] at htel
  linarith only [htel]

/-- Right of a zero-free abscissa `Θ ∈ [1/2, 1)`, for every `d ≥ 1` and `T ∈ [C_d y, y^(d + 1)]`,
there is an integer stencil `b : ℕ → ℤ` supported in `[1, 2 T]` with `b 1 = 1`, `b 2 = -1`,
`¬ 4 ∣ k` on active letters `k ≥ 2`, all prime-power divisors of active letters bounded by
`smoothJumpPrimeBound d * y`, sublinear `ℓ¹` mass, and global Mertens tracking error
`O_{Θ,ε,d}(1 / y + T^{-(1 - Θ - ε)}) x`. -/
theorem exists_taut_mertens_stencil {Θ ε : ℝ} {d : ℕ}
    (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    (hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4) (hΘε : Θ + ε < 1)
    (hd : 1 ≤ d) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y T : ℕ, tautStencilMinY d ≤ y → smoothJumpBase d * y ≤ T → T ≤ y ^ (d + 1) →
        ∃ b : ℕ → ℤ,
          b 0 = 0 ∧ b 1 = 1 ∧ b 2 = -1 ∧
          (∀ k : ℕ, 2 * T < k → b k = 0) ∧
          (∀ k : ℕ, 2 ≤ k → b k ≠ 0 → ¬ 4 ∣ k ∧
            ∀ q e : ℕ, q.Prime → 1 ≤ e → q ^ e ∣ k → q ^ e ≤ smoothJumpPrimeBound d * y) ∧
          (∑ k ∈ Icc 1 (2 * T), |(b k : ℝ)|) ≤
            C₁ * ((1 + Real.log (T : ℝ)) ^ 3 * (y : ℝ) ^ (1 + 2 * ε) *
              (T : ℝ) ^ (2 * (Θ + ε) - 1) +
              (1 + Real.log (T : ℝ)) * ((T : ℝ) / (y : ℝ)) + (T : ℝ) ^ (Θ + ε)) ∧
          (∀ x : ℕ, 1 ≤ x →
            |(∑ k ∈ Icc 1 x, (b k : ℝ)) - mertens x| ≤
              C₂ * (1 / (y : ℝ) + (T : ℝ) ^ (-(1 - Θ - ε))) * (x : ℝ)) := by
  classical
  obtain ⟨C_pl, hC_pl, hpl⟩ :=
    exists_integral_smoothMertens_log_diff_sq_le hΘ hΘ1 hzf hε0 hε4
  obtain ⟨C_M0, hC_M0, hM_pow0⟩ :=
    exists_mertens_power_of_zeroFree hΘ hΘ1 hzf (σ := 1 - Θ - ε) (by linarith) (by linarith)
  obtain ⟨C_M, hCM_def⟩ : ∃ C_M : ℝ, C_M = C_M0 + 1 := ⟨_, rfl⟩
  have hC_M : 0 < C_M := by rw [hCM_def]; positivity
  have hM_pow : ∀ n : ℕ, 1 ≤ n → |mertens n| ≤ C_M * (n : ℝ) ^ (Θ + ε) := by
    intro n hn
    rw [mertens_eq_mertensM]
    have h1 := hM_pow0 n hn
    have hexp : 1 - (1 - Θ - ε) = Θ + ε := by ring
    rw [hexp] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (by rw [hCM_def]; linarith) (by positivity))
  obtain ⟨C_var, hCvar_def⟩ : ∃ C_var : ℝ, C_var = 60 * Real.exp 8 * C_pl * 1000 * 32 := ⟨_, rfl⟩
  have hCvar_pos : 0 < C_var := by rw [hCvar_def]; positivity
  obtain ⟨C₁, hC₁_def⟩ : ∃ C₁ : ℝ, C₁ = C_var + (smoothJumpBase d : ℝ) + 500 + C_M := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂_def⟩ : ∃ C₂ : ℝ, C₂ = 4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M :=
    ⟨_, rfl⟩
  have hC₁_pos : 0 < C₁ := by rw [hC₁_def]; positivity
  have hC₂_pos : 0 < C₂ := by
    rw [hC₂_def]; have := smoothJumpWidth_pos d; positivity
  refine ⟨C₁, C₂, hC₁_pos, hC₂_pos, fun y T hy_min hT_lo hT_hi => ?_⟩
  have hy_4d5 : 4 * d + 5 ≤ y := (le_max_left _ _).trans hy_min
  have hy_width : ⌈2 * smoothJumpWidth d⌉₊ + 16 ≤ y := (le_max_right _ _).trans hy_min
  have hy_16 : 16 ≤ y := by omega
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have h1E_le : 1 + smoothJumpWidth d / (y : ℝ) ≤ 3 / 2 := by
    have h1 : 2 * smoothJumpWidth d ≤ (⌈2 * smoothJumpWidth d⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * smoothJumpWidth d⌉₊ : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast (by omega : ⌈2 * smoothJumpWidth d⌉₊ ≤ y)
    have : smoothJumpWidth d / (y : ℝ) ≤ 1 / 2 := by rw [div_le_iff₀ hy_pos]; linarith
    linarith
  obtain ⟨y₀, hy₀_def⟩ : ∃ y₀ : ℕ, y₀ = smoothJumpBase d * y := ⟨_, rfl⟩
  rw [← hy₀_def] at hT_lo
  have hy₀_ge16 : 16 ≤ y₀ := by
    have := smoothJumpBase_ge_sixteen hd; rw [hy₀_def]; nlinarith
  have hT_pos : 0 < T := lt_of_lt_of_le (by omega) hT_lo
  have hTR_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT_pos
  obtain ⟨J, hJ_def⟩ : ∃ J : ℕ, J = Nat.log 2 (T / y₀) + 1 := ⟨_, rfl⟩
  have hY0 : octaveCut T y₀ 0 = y₀ := by simp [octaveCut, hT_lo]
  have hYJ : octaveCut T y₀ J = T := by
    unfold octaveCut; rw [hJ_def]
    refine min_eq_left ?_
    have h1 : T / y₀ < 2 ^ (Nat.log 2 (T / y₀) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (T / y₀)
    have h2 : T < y₀ * (T / y₀ + 1) := Nat.lt_mul_div_succ T (by omega)
    nlinarith
  have hex_oct : ∀ j : ℕ, ∃ (m : ℕ) (z : ℕ → ℕ) (Jf : ℕ → ℤ),
      (octaveCut T y₀ j < octaveCut T y₀ (j + 1) →
        (∀ i < m, octaveCut T y₀ j < z i ∧ z i ≤ octaveCut T y₀ (j + 1)) ∧
        (∑ i ∈ range m, (Jf i : ℝ)) =
          mertens (octaveCut T y₀ (j + 1)) - mertens (octaveCut T y₀ j) ∧
        (∀ x : ℕ, octaveCut T y₀ j ≤ x → x ≤ octaveCut T y₀ (j + 1) →
          |(mertens (octaveCut T y₀ j) + ∑ i ∈ range m, if z i ≤ x then (Jf i : ℝ) else 0) -
              mertens x| ≤
            32 * (octaveCut T y₀ j : ℝ) / (y : ℝ)) ∧
        (∀ A B : ℝ, (octaveCut T y₀ j : ℝ) / 2 ≤ A → B ≤ A * (1 + smoothJumpWidth d / (y : ℝ)) →
          (∑ i ∈ range m, if A ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ B then |(Jf i : ℝ)| else 0) ≤
            (2000 * smoothJumpWidth d + 2000) * ((octaveCut T y₀ j : ℝ) / (y : ℝ))) ∧
        (∑ i ∈ range m, |(Jf i : ℝ)|) ≤
          60 * Real.exp 8 * C_pl * ((Nat.log 2 (16 * y) : ℝ) + 4) ^ 2 *
            (32 * (y : ℝ)) ^ (2 * ε) * (y : ℝ) * (octaveCut T y₀ j : ℝ) ^ (2 * (Θ + ε) - 1) +
            8 * (octaveCut T y₀ j : ℝ) / (y : ℝ)) ∧
      (¬ octaveCut T y₀ j < octaveCut T y₀ (j + 1) → m = 0) := by
    intro j
    by_cases hlt : octaveCut T y₀ j < octaveCut T y₀ (j + 1)
    · have hYj_lo : smoothJumpBase d * y ≤ octaveCut T y₀ j := by
        rw [← hy₀_def]
        exact hY0.symm.trans_le (octaveCut_mono T y₀ (Nat.zero_le j))
      obtain ⟨m, z, Jf, h1, h2, h3, h4, h5⟩ := exists_octave_jump_family
        hΘ hΘ1 hε0 hε4 hC_pl hpl hd hy_16 hYj_lo hlt (octaveCut_succ_le_two_mul T y₀ j)
      exact ⟨m, z, Jf, fun _ => ⟨h1, h2, h3, h4, h5⟩, fun h => absurd hlt h⟩
    · exact ⟨0, fun _ => T, fun _ => 0, fun h => absurd h hlt, fun _ => rfl⟩
  choose m_oct z_oct J_oct hoct hoct_empty using hex_oct
  obtain ⟨E_all, hE_def⟩ : ∃ E_all, E_all = tautEvents J m_oct := ⟨_, rfl⟩
  have hz_ev_bounds : ∀ e ∈ E_all, y₀ ≤ tautZ T z_oct e ∧ tautZ T z_oct e ≤ T := by
    intro e he
    rw [hE_def, tautEvents] at he
    rcases mem_insert.mp he with rfl | he'
    · exact ⟨hT_lo, le_rfl⟩
    · rcases mem_map.mp he' with ⟨⟨j, i⟩, hji, rfl⟩
      rcases mem_biUnion.mp hji with ⟨j', _, himap⟩
      rcases mem_map.mp himap with ⟨i', hi', heq⟩
      simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      rw [Finset.mem_range] at hi'
      have hlt_j : octaveCut T y₀ j' < octaveCut T y₀ (j' + 1) := by
        by_contra hnot; rw [hoct_empty j' hnot] at hi'; omega
      obtain ⟨hgt, hle⟩ := (hoct j' hlt_j).1 i' hi'
      have hYj_lo : y₀ ≤ octaveCut T y₀ j' :=
        hY0.symm.trans_le (octaveCut_mono T y₀ (Nat.zero_le j'))
      have hYj1_hi : octaveCut T y₀ (j' + 1) ≤ T := min_le_left _ _
      simp only [Function.Embedding.some_apply, tautZ]
      exact ⟨hYj_lo.trans hgt.le, hle.trans hYj1_hi⟩
  have hex_k : ∀ e : Option (ℕ × ℕ), ∃ k : ℕ, e ∈ E_all →
      tautZ T z_oct e < k ∧
      (k : ℝ) ≤ (tautZ T z_oct e : ℝ) * (1 + smoothJumpWidth d / (y : ℝ)) ∧
      3 ≤ k ∧ ¬ 4 ∣ k ∧
      ∀ q ex : ℕ, q.Prime → 1 ≤ ex → q ^ ex ∣ k → q ^ ex ≤ smoothJumpPrimeBound d * y := by
    intro e
    by_cases he : e ∈ E_all
    · obtain ⟨hlo, hhi⟩ := hz_ev_bounds e he
      rw [hy₀_def] at hlo
      obtain ⟨k, h1, h2, h3, h4, h5⟩ := exists_bertrand_smooth_jump hd hy_4d5 hlo (hhi.trans hT_hi)
      exact ⟨k, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose k_ev hk_ev using hex_k
  have hk_ev_bounds : ∀ e ∈ E_all, y₀ < k_ev e ∧ k_ev e ≤ 2 * T := by
    intro e he
    obtain ⟨hlo, hhi⟩ := hz_ev_bounds e he
    obtain ⟨hzk, hk_le, _, _, _⟩ := hk_ev e he
    refine ⟨lt_of_le_of_lt hlo hzk, ?_⟩
    have h2T : (k_ev e : ℝ) ≤ 2 * (T : ℝ) := by
      calc (k_ev e : ℝ) ≤ (tautZ T z_oct e : ℝ) * (1 + smoothJumpWidth d / (y : ℝ)) := hk_le
        _ ≤ (T : ℝ) * (3 / 2) := mul_le_mul (by exact_mod_cast hhi) h1E_le
            (by linarith [smoothJumpWidth_pos d, div_nonneg (smoothJumpWidth_pos d).le hy_pos.le])
            (Nat.cast_nonneg T)
        _ ≤ 2 * (T : ℝ) := by linarith
    exact_mod_cast h2T
  obtain ⟨b, hb_def⟩ : ∃ b, b = tautCoeff y₀ E_all k_ev (tautJ T J_oct) := ⟨_, rfl⟩
  have hb0 : b 0 = 0 := by
    rw [hb_def, tautCoeff, if_neg (by omega)]
    exact sum_eq_zero fun e he => if_neg (by have := (hk_ev_bounds e he).1; omega)
  have hb1 : b 1 = 1 := by rw [hb_def, tautCoeff, if_pos ⟨le_rfl, by omega⟩]; simp
  have hb2 : b 2 = -1 := by
    rw [hb_def, tautCoeff, if_pos ⟨by omega, by omega⟩]
    exact ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hb_supp : ∀ k : ℕ, 2 * T < k → b k = 0 := by
    intro k hk
    rw [hb_def, tautCoeff, if_neg (by omega)]
    exact sum_eq_zero fun e he => if_neg (by have := (hk_ev_bounds e he).2; omega)
  have hb_smooth : ∀ k : ℕ, 2 ≤ k → b k ≠ 0 → ¬ 4 ∣ k ∧
      ∀ q ex : ℕ, q.Prime → 1 ≤ ex → q ^ ex ∣ k → q ^ ex ≤ smoothJumpPrimeBound d * y := by
    intro k hk2 hbk
    rw [hb_def, tautCoeff] at hbk
    by_cases hky₀ : k ≤ y₀
    · rw [if_pos ⟨by omega, hky₀⟩] at hbk
      have hsq : Squarefree k := by
        by_contra hnsq; exact hbk (ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq)
      refine ⟨fun h4 => ?_, fun q ex _ _ hqe => ?_⟩
      · exact absurd (hsq 2 (by simpa using h4)) (by norm_num)
      · exact (Nat.le_of_dvd (by omega) hqe).trans
          (hky₀.trans (hy₀_def ▸ Nat.mul_le_mul_right y (le_max_left _ _)))
    · rw [if_neg (by omega)] at hbk
      obtain ⟨e, he, hne_e⟩ := exists_ne_zero_of_sum_ne_zero hbk
      have hkeq : k_ev e = k := by
        by_contra hne_k; rw [if_neg hne_k] at hne_e; exact hne_e rfl
      subst hkeq
      obtain ⟨_, _, _, h4, hpp⟩ := hk_ev e he
      exact ⟨h4, hpp⟩
  -- Bound `ℓ¹` mass.
  have hmass_bd : (∑ k ∈ Icc 1 (2 * T), |(b k : ℝ)|) ≤
      C₁ * ((1 + Real.log (T : ℝ)) ^ 3 * (y : ℝ) ^ (1 + 2 * ε) *
        (T : ℝ) ^ (2 * (Θ + ε) - 1) +
        (1 + Real.log (T : ℝ)) * ((T : ℝ) / (y : ℝ)) + (T : ℝ) ^ (Θ + ε)) := by
    have hsplit_Icc : Icc 1 (2 * T) = Icc 1 y₀ ∪ Ioc y₀ (2 * T) := by
      ext k; simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdisj_Icc : Disjoint (Icc 1 y₀) (Ioc y₀ (2 * T)) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      rw [Finset.mem_Icc] at hk1; rw [Finset.mem_Ioc] at hk2; omega
    rw [hsplit_Icc, sum_union hdisj_Icc]
    have hhead_y₀ : ∑ k ∈ Icc 1 y₀, |(b k : ℝ)| ≤ (y₀ : ℝ) := by
      calc ∑ k ∈ Icc 1 y₀, |(b k : ℝ)|
          ≤ ∑ _k ∈ Icc 1 y₀, (1 : ℝ) := by
            refine sum_le_sum fun k hk => ?_
            rw [hb_def, tautCoeff, if_pos (Finset.mem_Icc.mp hk)]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        _ = (y₀ : ℝ) := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            exact_mod_cast (by omega : y₀ + 1 - 1 = y₀)
    have hy₀_A : (y₀ : ℝ) ≤
        (smoothJumpBase d : ℝ) * ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) := by
      have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
      have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
      have hp1 : (y : ℝ) ≤ (y : ℝ) ^ (1 + 2 * ε) := by
        nth_rw 1 [← Real.rpow_one (y : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      have hp2 : (1 : ℝ) ≤ (T : ℝ) ^ (2 * (Θ + ε) - 1) :=
        Real.one_le_rpow hT1 (by linarith)
      rw [hy₀_def]; push_cast
      calc (smoothJumpBase d : ℝ) * (y : ℝ)
          = (smoothJumpBase d : ℝ) * ((y : ℝ) * 1) := by ring
        _ ≤ (smoothJumpBase d : ℝ) * ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hp1 hp2 zero_le_one (by positivity)) (by positivity)
    have htail_ev : ∑ k ∈ Ioc y₀ (2 * T), |(b k : ℝ)| ≤
        ∑ e ∈ E_all, |(tautJ T J_oct e : ℝ)| := by
      have hterm : ∀ k ∈ Ioc y₀ (2 * T), |(b k : ℝ)| ≤
          ∑ e ∈ E_all, if k_ev e = k then |(tautJ T J_oct e : ℝ)| else 0 := by
        intro k hk
        rw [Finset.mem_Ioc] at hk
        rw [hb_def, tautCoeff, if_neg (by omega)]
        simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero]
        exact (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun _ _ => by split_ifs <;> simp)
      refine (sum_le_sum hterm).trans ?_
      rw [sum_comm]
      refine sum_le_sum fun e he => ?_
      obtain ⟨hgt, hle⟩ := hk_ev_bounds e he
      rw [sum_eq_single (k_ev e)]
      · simp
      · intro k _ hne; exact if_neg hne.symm
      · intro h; exact absurd (Finset.mem_Ioc.mpr ⟨hgt, hle⟩) h
    rw [hE_def, sum_tautEvents] at htail_ev
    have hnone_bd : |(tautJ T J_oct none : ℝ)| ≤ C_M * (T : ℝ) ^ (Θ + ε) := by
      dsimp [tautJ]; rw [Int.cast_neg, abs_neg, cast_mertensInt]; exact hM_pow T (by omega)
    have hlogT_nn : 0 ≤ Real.log (T : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
    have hJ_le_log : (J : ℝ) ≤ 2 * (1 + Real.log (T : ℝ)) := by
      rw [hJ_def]
      have h1 : 2 ^ Nat.log 2 (T / y₀) ≤ T := by
        by_cases h0 : T / y₀ = 0
        · simp [h0]; omega
        · exact (Nat.pow_log_le_self 2 h0).trans (Nat.div_le_self T y₀)
      have h2 : ((2 : ℝ)) ^ Nat.log 2 (T / y₀) ≤ (T : ℝ) := by exact_mod_cast h1
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h3
      have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hl0 : (0 : ℝ) ≤ (Nat.log 2 (T / y₀) : ℝ) := Nat.cast_nonneg _
      push_cast; nlinarith
    have hlog16y : (Nat.log 2 (16 * y) : ℝ) + 4 ≤ 16 * (1 + Real.log (T : ℝ)) := by
      have h16y_le : 16 * y ≤ T :=
        le_trans (hy₀_def ▸ Nat.mul_le_mul_right y (smoothJumpBase_ge_sixteen hd)) hT_lo
      have h1 : 2 ^ Nat.log 2 (16 * y) ≤ T := (Nat.pow_log_le_self 2 (by omega)).trans h16y_le
      have h2 : ((2 : ℝ)) ^ Nat.log 2 (16 * y) ≤ (T : ℝ) := by exact_mod_cast h1
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h3
      have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hl0 : (0 : ℝ) ≤ (Nat.log 2 (16 * y) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hoct_bd : ∀ j ∈ range J, ∑ i ∈ range (m_oct j), |(tautJ T J_oct (some (j, i)) : ℝ)| ≤
        (C_var / 2) * (1 + Real.log (T : ℝ)) ^ 2 *
          ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) +
          8 * ((T : ℝ) / (y : ℝ)) := by
      intro j _
      dsimp only [tautJ]
      by_cases hlt_j : octaveCut T y₀ j < octaveCut T y₀ (j + 1)
      · obtain ⟨_, _, _, _, hvar⟩ := hoct j hlt_j
        have hYj_T : octaveCut T y₀ j ≤ T := min_le_left T _
        have hYj_pos : (0 : ℝ) < (octaveCut T y₀ j : ℝ) := by
          have hlo : y₀ ≤ octaveCut T y₀ j :=
            hY0.symm.trans_le (octaveCut_mono T y₀ (Nat.zero_le j))
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < y₀) hlo)
        refine hvar.trans (add_le_add ?_ ?_)
        · rw [hCvar_def]
          exact octave_var_scale hΘ hε0 hε4 hC_pl hy_pos hYj_pos hYj_T hlog16y
        · rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (by exact_mod_cast hYj_T) hy_pos.le) (by norm_num)
      · rw [hoct_empty j hlt_j]; simp; positivity
    have hsum_oct : ∑ j ∈ range J, ∑ i ∈ range (m_oct j),
        |(tautJ T J_oct (some (j, i)) : ℝ)| ≤
        (J : ℝ) * ((C_var / 2) * (1 + Real.log (T : ℝ)) ^ 2 *
          ((y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1)) +
          8 * ((T : ℝ) / (y : ℝ))) :=
      (sum_le_sum hoct_bd).trans_eq (by rw [sum_const, card_range, nsmul_eq_mul])
    rw [hC₁_def]
    have hcomb := tautMass_combine
      (base := (smoothJumpBase d : ℝ)) (C_var := C_var) (C_M := C_M) (J := (J : ℝ))
      (A := (y : ℝ) ^ (1 + 2 * ε) * (T : ℝ) ^ (2 * (Θ + ε) - 1))
      (B := (T : ℝ) / (y : ℝ)) (C := (T : ℝ) ^ (Θ + ε)) (lT := Real.log (T : ℝ))
      (Nat.cast_nonneg _) hCvar_pos.le hC_M.le (by positivity) (by positivity)
      (by positivity) hlogT_nn (hhead_y₀.trans hy₀_A)
      (htail_ev.trans (add_le_add hnone_bd hsum_oct)) hJ_le_log
    simpa [mul_assoc] using hcomb
  -- Uniform Mertens tracking bound for all `x ≥ 1`.
  refine ⟨b, hb0, hb1, hb2, hb_supp, hb_smooth, hmass_bd, fun x hx1 => ?_⟩
  have hxR_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  by_cases hxy₀ : x ≤ y₀
  · have heq : ∑ k ∈ Icc 1 x, (b k : ℝ) = mertens x := by
      rw [mertens]
      have hset : Icc 1 x = Ioc 0 x := by ext k; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [hset]
      refine sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ioc] at hk
      rw [hb_def, tautCoeff, if_pos ⟨by omega, hk.2.trans hxy₀⟩]
    rw [heq, sub_self, abs_zero]; positivity
  push Not at hxy₀
  have hBx_eq : ∑ k ∈ Icc 1 x, (b k : ℝ) =
      mertens y₀ + ∑ e ∈ tautEvents J m_oct, if k_ev e ≤ x then (tautJ T J_oct e : ℝ) else 0 := by
    rw [hb_def, ← hE_def]
    exact tautCoeff_prefix_sum hxy₀ fun e he => (hk_ev_bounds e he).1
  rw [hBx_eq]
  obtain ⟨A_x, hAx_def⟩ : ∃ A_x : ℝ,
      A_x = mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if tautZ T z_oct e ≤ x then (tautJ T J_oct e : ℝ) else 0 := ⟨_, rfl⟩
  obtain ⟨B_x, hBx_def⟩ : ∃ B_x : ℝ,
      B_x = mertens y₀ + ∑ e ∈ tautEvents J m_oct,
        if k_ev e ≤ x then (tautJ T J_oct e : ℝ) else 0 := ⟨_, rfl⟩
  rw [← hBx_def]
  have hshift_diff : |A_x - B_x| ≤
      (if T ≤ x ∧ x ≤ 2 * T then C_M * (T : ℝ) ^ (Θ + ε) else 0) +
        2 * (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) := by
    rw [hAx_def, hBx_def]
    exact tautShift_diff_le hC_M hy_pos hx1 h1E_le (hM_pow T (by omega)) hoct_empty
      (fun j hlt => (hoct j hlt).1) (fun j hlt => (hoct j hlt).2.2.2.1)
      (fun e he => ⟨(hk_ev e (hE_def ▸ he)).1, (hk_ev e (hE_def ▸ he)).2.1⟩)
      (hk_ev_bounds none (hE_def ▸ mem_insert_self _ _)).2
  rcases lt_or_ge x T with hx_lt_T | hx_ge_T
  · have hJ_pos : 0 < J := by rw [hJ_def]; omega
    have hAx_err : |A_x - mertens x| ≤ 32 * ((x : ℝ) / (y : ℝ)) := by
      rw [hAx_def]
      exact tautUnshifted_lt_err hy_pos hJ_pos hY0 hYJ hxy₀ hx_lt_T hoct_empty
        (fun j hlt => (hoct j hlt).1) (fun j hlt => (hoct j hlt).2.1)
        (fun j hlt => (hoct j hlt).2.2.1)
    rw [if_neg (by omega : ¬(T ≤ x ∧ x ≤ 2 * T)), zero_add] at hshift_diff
    have htri : |B_x - mertens x| ≤ |A_x - B_x| + |A_x - mertens x| := by
      have : B_x - mertens x = (A_x - mertens x) - (A_x - B_x) := by ring
      rw [this]; exact (abs_sub _ _).trans_eq (add_comm _ _)
    refine (htri.trans (add_le_add hshift_diff hAx_err)).trans ?_
    rw [hC₂_def, show (x : ℝ) / (y : ℝ) = (1 / (y : ℝ)) * (x : ℝ) by ring]
    have hcoef : (2 * (2000 * smoothJumpWidth d + 2000) + 32) * (1 / (y : ℝ)) ≤
        (4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M) *
          (1 / (y : ℝ) + (T : ℝ) ^ (-(1 - Θ - ε))) := by
      have hw0 := smoothJumpWidth_pos d
      have hy_inv0 : 0 ≤ 1 / (y : ℝ) := by positivity
      have h1 : (2 * (2000 * smoothJumpWidth d + 2000) + 32) * (1 / (y : ℝ)) ≤
          (4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M) * (1 / (y : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hw0, hC_M]) hy_inv0
      have h2 : 0 ≤ (4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M) *
          (T : ℝ) ^ (-(1 - Θ - ε)) := by positivity
      rw [mul_add]
      linarith only [h1, h2]
    calc _ = ((2 * (2000 * smoothJumpWidth d + 2000) + 32) * (1 / (y : ℝ))) * (x : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hxR_pos.le
  · have hAx_zero : A_x = 0 := by
      rw [hAx_def]
      exact tautUnshifted_ge_eq_zero hY0 hYJ hx_ge_T
        (fun e he => (hz_ev_bounds e (hE_def ▸ he)).2) hoct_empty
        (fun j hlt => (hoct j hlt).2.1)
    have hTR_le_x : (T : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_ge_T
    have hxx_pow : (x : ℝ) ^ (Θ + ε) = (x : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ) := by
      nth_rw 3 [← Real.rpow_one (x : ℝ)]
      rw [← Real.rpow_add hxR_pos]; congr 1; ring
    have hmono_neg : (x : ℝ) ^ (-(1 - Θ - ε)) ≤ (T : ℝ) ^ (-(1 - Θ - ε)) :=
      Real.rpow_le_rpow_of_nonpos hTR_pos hTR_le_x (by linarith only [hΘε])
    have hTx_pow : (T : ℝ) ^ (Θ + ε) ≤ (T : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ) := by
      calc (T : ℝ) ^ (Θ + ε) ≤ (x : ℝ) ^ (Θ + ε) :=
            Real.rpow_le_rpow hTR_pos.le hTR_le_x (by linarith only [hΘ, hε0])
        _ = (x : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ) := hxx_pow
        _ ≤ (T : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ) :=
            mul_le_mul_of_nonneg_right hmono_neg hxR_pos.le
    have hMx_bd : |mertens x| ≤ C_M * (T : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ) := by
      calc |mertens x| ≤ C_M * (x : ℝ) ^ (Θ + ε) := hM_pow x hx1
        _ = C_M * ((x : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ)) := by rw [hxx_pow]
        _ ≤ C_M * ((T : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hmono_neg hxR_pos.le) hC_M.le
        _ = _ := by ring
    have hBx_bd : |B_x| ≤ C_M * (T : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ) +
        2 * (2000 * smoothJumpWidth d + 2000) * ((x : ℝ) / (y : ℝ)) := by
      have h0 : |B_x| = |A_x - B_x| := by rw [hAx_zero, zero_sub, abs_neg]
      rw [h0]
      refine hshift_diff.trans (add_le_add ?_ le_rfl)
      split_ifs
      · calc C_M * (T : ℝ) ^ (Θ + ε)
            ≤ C_M * ((T : ℝ) ^ (-(1 - Θ - ε)) * (x : ℝ)) :=
              mul_le_mul_of_nonneg_left hTx_pow hC_M.le
          _ = _ := by ring
      · positivity
    have htri : |B_x - mertens x| ≤ |B_x| + |mertens x| := abs_sub _ _
    refine (htri.trans (add_le_add hBx_bd hMx_bd)).trans ?_
    rw [hC₂_def, show (x : ℝ) / (y : ℝ) = (1 / (y : ℝ)) * (x : ℝ) by ring]
    have hcoef : 2 * C_M * (T : ℝ) ^ (-(1 - Θ - ε)) +
        2 * (2000 * smoothJumpWidth d + 2000) * (1 / (y : ℝ)) ≤
        (4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M) *
          (1 / (y : ℝ) + (T : ℝ) ^ (-(1 - Θ - ε))) := by
      have hw0 := smoothJumpWidth_pos d
      have hy_inv0 : 0 ≤ 1 / (y : ℝ) := by positivity
      have hT_inv0 : 0 ≤ (T : ℝ) ^ (-(1 - Θ - ε)) := by positivity
      have h1 : 2 * (2000 * smoothJumpWidth d + 2000) * (1 / (y : ℝ)) ≤
          (4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M) * (1 / (y : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hw0, hC_M]) hy_inv0
      have h2 : 2 * C_M * (T : ℝ) ^ (-(1 - Θ - ε)) ≤
          (4 * (2000 * smoothJumpWidth d + 2000) + 64 + 2 * C_M) * (T : ℝ) ^ (-(1 - Θ - ε)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hw0, hC_M]) hT_inv0
      rw [mul_add]
      linarith only [h1, h2]
    calc _ = (2 * C_M * (T : ℝ) ^ (-(1 - Θ - ε)) +
            2 * (2000 * smoothJumpWidth d + 2000) * (1 / (y : ℝ))) * (x : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hxR_pos.le

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
