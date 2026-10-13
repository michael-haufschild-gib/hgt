import GaloisForLFunctions.RHTower.WeilLagSingleBaseResonantChain
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Countably many lag progressions cannot see a non-attained top

The resonant chain `Σ_n e^{−40(n+1)} e^{m(1−2^{−(n+1)})} cos(mφ_n)` is negative for every real
`m ≥ 80` (`chainSum_neg`). Its proof uses only the size of the dominant exponential on the window
`[80·2ⁿ, 160·2ⁿ]` and the signs of the dominant term and its two neighbours. So it survives phase
errors of size `1/10` on those three terms, and arbitrary phases on all other terms.

**Theorem** (`exists_chain_configuration_countable_bddAbove`). For every sequence of spacings
`ℓ_k > 0` there are points `s_n` with real parts strictly increasing to `¼` (never attained),
ordinates tending to infinity, and summable weights `c_n > 0`, such that for every `k`

`sup_{j ∈ ℕ} Σ_n c_n Re e^{jℓ_k s_n} < ∞`.

**Theorem** (`exists_chain_configuration_countable_bddBelow`). The same holds with the samples
bounded below instead.

So, for zero configurations with positive weights, boundedness above (or below) along any countable
family of progressions does not force the top real part to be attained. RH holds iff the spacings
with progressions bounded above form a non-meagre set
(`riemannHypothesis_iff_not_isMeagre_bddAbove_progression`). Countable sets are meagre, and these
configurations show that zero-side data alone cannot lower that threshold to countable families, even
with base-dependent bounds.

**Construction.** Put `s_n = (1 − 2^{−(n+1)})/4 + i(θ_n/4 + 2πq_n/ℓ₀)`, with `θ_n = φ_n` (upper) or
`θ_n = 0` (lower). The integer `q_n ≥ n + 1` comes from simultaneous Dirichlet approximation of
`ℓ_k/ℓ₀`, `k ≤ n`. At lag `u = jℓ_k` with `k ≤ n` the extra phase `jℓ_k · 2πq_n/ℓ₀` is within
`2πj/Q_n` of `2πℤ`, and `Q_n` is large enough that this is at most `1/10` wherever ring `n` is dominant
or a neighbour of the dominant ring. For `u` beyond the window of ring `k + 1`, every dominant ring and
its neighbours are controlled, and the window bounds apply. The finitely many earlier samples are
bounded trivially.
-/

open Real Finset Filter Topology

noncomputable section

namespace RHTower

/-! ## Exponent comparisons on a window -/

theorem exp_neg_five_lt_hundredth : Real.exp (-5) < 1 / 100 := by
  have h1 := Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h100 : (100 : ℝ) < Real.exp 5 := by
    rw [h5]
    have : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h100

/-- A ring at distance at least two from the dominant one is exponentially smaller. -/
theorem chainExponent_sub_le_of_far {m : ℝ} {j n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hd : 2 ≤ Nat.dist j n) :
    resonantChainExponent m j - resonantChainExponent m n ≤ -5 - ((Nat.dist j n : ℝ) - 1) := by
  rw [chainExponent_sub]
  rcases (show (∃ i, n = j + 2 + i) ∨ (∃ i, j = n + 2 + i) by
    rcases le_total j n with h | h
    · left; rw [Nat.dist_eq_sub_of_le h] at hd; exact ⟨n - (j + 2), by omega⟩
    · right; rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h] at hd; exact ⟨j - (n + 2), by omega⟩)
    with ⟨i, h⟩ | ⟨i, h⟩
  · subst h
    have hdist : Nat.dist j (j + 2 + i) = i + 2 := by
      rw [Nat.dist_eq_sub_of_le (by omega)]; omega
    rw [hdist]
    set X : ℝ := 2 ^ (j + 1) with hX
    set Y : ℝ := 2 ^ (i + 2) with hY
    have hX0 : 0 < X := by positivity
    have hY0 : (0 : ℝ) < Y := by positivity
    have hYge : 2 * ((i : ℝ) + 2) ≤ Y := by
      have := two_mul_le_two_pow (i + 2); rw [hY]; exact_mod_cast this
    have e1 : (2 : ℝ) ^ (j + 2 + i + 1) = X * Y := by rw [hX, hY, ← pow_add]; ring_nf
    have e0 : (2 : ℝ) ^ (j + 2 + i) * 2 = X * Y := by rw [← pow_succ, e1]
    have hm : 40 * (X * Y) ≤ m := by rw [← e0]; linarith
    rw [e1]
    have e : m * (1 / (X * Y) - 1 / X) = -(m / (X * Y) * (Y - 1)) := by field_simp; ring
    rw [e]
    have h40 : (40 : ℝ) ≤ m / (X * Y) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hY1 : (0 : ℝ) ≤ Y - 1 := by linarith
    push_cast
    nlinarith
  · subst h
    have hdist : Nat.dist (n + 2 + i) n = i + 2 := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
    rw [hdist]
    set X : ℝ := 2 ^ (n + 1) with hX
    set Y : ℝ := 2 ^ (i + 2) with hY
    have hX0 : 0 < X := by positivity
    have hY0 : (0 : ℝ) < Y := by positivity
    have hY4 : (4 : ℝ) ≤ Y := by
      rw [hY]
      have : (2 : ℝ) ^ 2 ≤ 2 ^ (i + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this ⊢; linarith
    have e1 : (2 : ℝ) ^ (n + 2 + i + 1) = X * Y := by rw [hX, hY, ← pow_add]; ring_nf
    have e0 : (2 : ℝ) ^ n * 2 = X := by rw [hX, pow_succ]
    have hm : m ≤ 80 * X := by rw [← e0]; linarith
    rw [e1]
    have e : m * (1 / X - 1 / (X * Y)) = m / X * (1 - 1 / Y) := by field_simp
    rw [e]
    have hmX : m / X ≤ 80 := by rw [div_le_iff₀ hX0]; linarith
    have hmX0 : 0 ≤ m / X :=
      div_nonneg (by linarith [mul_pos (by norm_num : (0:ℝ) < 80) (pow_pos (by norm_num : (0:ℝ) < 2) n)]) hX0.le
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hY : Y = 4 := by rw [hY]; norm_num
      rw [hY]
      push_cast
      nlinarith
    · have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hipos
      have h1Y : 0 ≤ 1 - 1 / Y := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have h1Y' : 1 - 1 / Y ≤ 1 := by
        have : 0 ≤ 1 / Y := by positivity
        linarith
      have : m / X * (1 - 1 / Y) ≤ 80 := by nlinarith
      push_cast
      nlinarith

/-- The two neighbours of the dominant ring are never larger than it on its window. -/
theorem chainExponent_le_of_neighbour {m : ℝ} {j n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hd : Nat.dist j n = 1) : resonantChainExponent m j ≤ resonantChainExponent m n := by
  have key := chainExponent_sub m j n
  rcases (show n = j + 1 ∨ j = n + 1 by
    rcases le_total j n with h | h
    · left; rw [Nat.dist_eq_sub_of_le h] at hd; omega
    · right; rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h] at hd; omega) with h | h
  · subst h
    have e : (1 : ℝ) / 2 ^ (j + 1 + 1) - 1 / 2 ^ (j + 1) = -(1 / 2 ^ (j + 2)) := by
      rw [show (2 : ℝ) ^ (j + 1 + 1) = 2 ^ (j + 2) by ring_nf, pow_succ (2 : ℝ) (j + 1)]
      field_simp; ring
    rw [e] at key
    have hpos : (0 : ℝ) < 2 ^ (j + 2) := by positivity
    have hm : (40 : ℝ) ≤ m * (1 / 2 ^ (j + 2)) := by
      rw [mul_one_div, le_div_iff₀ hpos]
      have : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      rw [this]; linarith
    push_cast at key
    linarith
  · subst h
    have e : (1 : ℝ) / 2 ^ (n + 1) - 1 / 2 ^ (n + 1 + 1) = 1 / 2 ^ (n + 2) := by
      rw [show (2 : ℝ) ^ (n + 1 + 1) = 2 ^ (n + 2) by ring_nf, show (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) by ring]
      field_simp; ring
    rw [e] at key
    have hpos : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have hm : m * (1 / 2 ^ (n + 2)) ≤ 40 := by
      rw [mul_one_div, div_le_iff₀ hpos]
      have : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
      rw [this]; linarith
    push_cast at key
    linarith

/-- A neighbour either has nonpositive exact cosine or is smaller by `e^{−5}`. -/
theorem chain_neighbour_alt {m : ℝ} {j n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hd : Nat.dist j n = 1) :
    Real.cos (m * resonantChainPhase j) ≤ 0 ∨
      resonantChainExponent m j - resonantChainExponent m n ≤ -5 := by
  have hπ := Real.pi_pos
  rw [chainExponent_sub]
  rcases (show n = j + 1 ∨ j = n + 1 by
    rcases le_total j n with h | h
    · left; rw [Nat.dist_eq_sub_of_le h] at hd; omega
    · right; rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h] at hd; omega) with h | h
  · subst h
    set X : ℝ := 2 ^ j with hX
    have hX0 : 0 < X := by positivity
    have e1 : (2 : ℝ) ^ (j + 1) = 2 * X := by rw [pow_succ, hX]; ring
    have e2 : (2 : ℝ) ^ (j + 1 + 1) = 4 * X := by rw [pow_succ, pow_succ, hX]; ring
    rw [e1] at h1 h2
    by_cases hx : m * resonantChainPhase j ≤ 3 * Real.pi / 2
    · left
      apply Real.cos_nonpos_of_pi_div_two_le_of_le _ (by linarith)
      rw [phase_mul_eq]
      have : (1 : ℝ) / 2 ≤ m / (120 * X) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · right
      push Not at hx
      rw [phase_mul_eq] at hx
      have hm : 180 * X < m := by
        have : (3 : ℝ) / 2 < m / (120 * X) := by
          by_contra hc; push Not at hc; nlinarith
        rw [lt_div_iff₀ (by positivity)] at this; linarith
      rw [e2, e1]
      have e : m * (1 / (4 * X) - 1 / (2 * X)) = -(m / (4 * X)) := by field_simp; ring
      rw [e]
      have : (45 : ℝ) < m / (4 * X) := by rw [lt_div_iff₀ (by positivity)]; linarith
      push_cast
      linarith
  · subst h
    set X : ℝ := 2 ^ n with hX
    have hX0 : 0 < X := by positivity
    have e1 : (2 : ℝ) ^ (n + 1) = 2 * X := by rw [pow_succ, hX]; ring
    have e2 : (2 : ℝ) ^ (n + 1 + 1) = 4 * X := by rw [pow_succ, pow_succ, hX]; ring
    by_cases hx : Real.pi / 2 ≤ m * resonantChainPhase (n + 1)
    · left
      apply Real.cos_nonpos_of_pi_div_two_le_of_le hx
      rw [phase_mul_eq, e1]
      have : m / (120 * (2 * X)) ≤ (2 : ℝ) / 3 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      nlinarith
    · right
      push Not at hx
      rw [phase_mul_eq, e1] at hx
      have hm : m < 120 * X := by
        have : m / (120 * (2 * X)) < (1 : ℝ) / 2 := by
          by_contra hc; push Not at hc; nlinarith
        rw [div_lt_iff₀ (by positivity)] at this; linarith
      rw [e2, e1]
      have e : m * (1 / (2 * X) - 1 / (4 * X)) = m / (4 * X) := by field_simp; ring
      rw [e]
      have : m / (4 * X) < 30 := by rw [div_lt_iff₀ (by positivity)]; linarith
      push_cast
      linarith

/-! ## Chains with perturbed phases -/

/-- The chain term with an arbitrary phase `ψ j`. -/
def genChainTerm (m : ℝ) (ψ : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.exp (resonantChainExponent m j) * Real.cos (ψ j)

theorem abs_genChainTerm_le (m : ℝ) (ψ : ℕ → ℝ) (j : ℕ) :
    |genChainTerm m ψ j| ≤ Real.exp (resonantChainExponent m j) := by
  unfold genChainTerm
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have := Real.abs_cos_le_one (ψ j)
  have := Real.exp_pos (resonantChainExponent m j)
  nlinarith

theorem summable_genChainTerm {m : ℝ} (hm : 0 ≤ m) (ψ : ℕ → ℝ) : Summable (genChainTerm m ψ) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (Real.exp_pos (-40)).le
      ((Real.exp_lt_exp.mpr (by norm_num : (-40 : ℝ) < 0)).trans_eq Real.exp_zero)).mul_left
      (Real.exp (m - 40))) fun j => ?_
  rw [Real.norm_eq_abs]
  refine (abs_genChainTerm_le m ψ j).trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold resonantChainExponent
  have : (0 : ℝ) ≤ m * (1 / 2 ^ (j + 1)) := by positivity
  nlinarith

/-- Far rings: `|term_j| ≤ 2e^{−5}(½)^{|j−n|} e^{E_n}`. -/
theorem abs_genChainTerm_le_far {m : ℝ} {j n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hd : 2 ≤ Nat.dist j n) (ψ : ℕ → ℝ) :
    |genChainTerm m ψ j| ≤
      2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * Real.exp (resonantChainExponent m n) := by
  refine (abs_genChainTerm_le m ψ j).trans ?_
  have hgap := chainExponent_sub_le_of_far h1 h2 hd
  have h2' : Real.exp (resonantChainExponent m j) ≤
      Real.exp (-5 - ((Nat.dist j n : ℝ) - 1)) * Real.exp (resonantChainExponent m n) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  refine h2'.trans ?_
  obtain ⟨k, hk⟩ : ∃ k, Nat.dist j n = k + 1 := ⟨Nat.dist j n - 1, by omega⟩
  rw [hk]
  have h3 : Real.exp (-5 - (((k + 1 : ℕ) : ℝ) - 1)) = Real.exp (-5) * Real.exp (-(k : ℝ)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [h3]
  have h4 := exp_neg_le_half_pow k
  have h5 : (2 : ℝ) * (1 / 2) ^ (k + 1) = (1 / 2) ^ k := by rw [pow_succ]; ring
  have hE := Real.exp_pos (resonantChainExponent m n)
  have h5' := Real.exp_pos (-5)
  calc Real.exp (-5) * Real.exp (-(k : ℝ)) * Real.exp (resonantChainExponent m n)
      ≤ Real.exp (-5) * (1 / 2) ^ k * Real.exp (resonantChainExponent m n) := by gcongr
    _ = 2 * Real.exp (-5) * (1 / 2) ^ (k + 1) * Real.exp (resonantChainExponent m n) := by
        rw [← h5]; ring

/-- A neighbour whose phase is within `η` of the exact phase contributes at most
`(η + e^{−5}) e^{E_n}`. -/
theorem genChainTerm_le_neighbour {m η : ℝ} {j n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hd : Nat.dist j n = 1) (hη : 0 ≤ η) {ψ : ℕ → ℝ} (hψ : |ψ j - m * resonantChainPhase j| ≤ η) :
    genChainTerm m ψ j ≤ (η + Real.exp (-5)) * Real.exp (resonantChainExponent m n) := by
  have hle := chainExponent_le_of_neighbour h1 h2 hd
  have hEj := Real.exp_pos (resonantChainExponent m j)
  have hEn := Real.exp_pos (resonantChainExponent m n)
  have he5 := Real.exp_pos (-5)
  unfold genChainTerm
  rcases chain_neighbour_alt h1 h2 hd with hc | hg
  · have hcos : Real.cos (ψ j) ≤ η := by
      have := Real.abs_cos_sub_cos_le (ψ j) (m * resonantChainPhase j)
      rw [abs_le] at this
      linarith [this.2]
    have hEle : Real.exp (resonantChainExponent m j) ≤ Real.exp (resonantChainExponent m n) :=
      Real.exp_le_exp.mpr hle
    rcases le_total (Real.cos (ψ j)) 0 with h0 | h0
    · have : Real.exp (resonantChainExponent m j) * Real.cos (ψ j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hEj.le h0
      nlinarith
    · calc Real.exp (resonantChainExponent m j) * Real.cos (ψ j)
          ≤ Real.exp (resonantChainExponent m n) * η := mul_le_mul hEle hcos h0 hEn.le
        _ ≤ (η + Real.exp (-5)) * Real.exp (resonantChainExponent m n) := by nlinarith
  · have hEle : Real.exp (resonantChainExponent m j) ≤
        Real.exp (-5) * Real.exp (resonantChainExponent m n) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hc1 := Real.cos_le_one (ψ j)
    calc Real.exp (resonantChainExponent m j) * Real.cos (ψ j)
        ≤ Real.exp (resonantChainExponent m j) := by nlinarith
      _ ≤ Real.exp (-5) * Real.exp (resonantChainExponent m n) := hEle
      _ ≤ (η + Real.exp (-5)) * Real.exp (resonantChainExponent m n) := by nlinarith

/-- The dominant ring with a phase error at most `η` contributes at most `(−½ + η) e^{E_n}`. -/
theorem genChainTerm_self_le {m η : ℝ} {n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    {ψ : ℕ → ℝ} (hψ : |ψ n - m * resonantChainPhase n| ≤ η) :
    genChainTerm m ψ n ≤ (-(1 / 2) + η) * Real.exp (resonantChainExponent m n) := by
  have hπ := Real.pi_pos
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hc : Real.cos (m * resonantChainPhase n) ≤ -(1 / 2) := by
    rw [phase_mul_eq]
    apply cos_le_neg_half_of_mem
    · have : (2 : ℝ) / 3 ≤ m / (120 * 2 ^ n) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · have : m / (120 * 2 ^ n) ≤ (4 : ℝ) / 3 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      nlinarith
  have hcos : Real.cos (ψ n) ≤ -(1 / 2) + η := by
    have := Real.abs_cos_sub_cos_le (ψ n) (m * resonantChainPhase n)
    rw [abs_le] at this
    linarith [this.2]
  unfold genChainTerm
  have := Real.exp_pos (resonantChainExponent m n)
  nlinarith

/-- At most two indices are neighbours of `n`. -/
theorem tsum_neighbour_indicator_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∑' j : ℕ, (if Nat.dist j n = 1 then B else 0) ≤ 2 * B := by
  classical
  have hsupp : ∀ j ∉ ({n - 1, n + 1} : Finset ℕ), (if Nat.dist j n = 1 then B else 0) = 0 := by
    intro j hj
    rw [if_neg]
    intro hd
    apply hj
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases le_total j n with h | h
    · rw [Nat.dist_eq_sub_of_le h] at hd; left; omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h] at hd; right; omega
  rw [tsum_eq_sum hsupp]
  calc ∑ j ∈ ({n - 1, n + 1} : Finset ℕ), (if Nat.dist j n = 1 then B else 0)
      ≤ ∑ _j ∈ ({n - 1, n + 1} : Finset ℕ), B :=
        Finset.sum_le_sum fun j _ => by split_ifs <;> linarith
    _ = ({n - 1, n + 1} : Finset ℕ).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * B := by
        have : (({n - 1, n + 1} : Finset ℕ).card : ℝ) ≤ 2 := by
          exact_mod_cast Finset.card_le_two
        nlinarith

/-- **Upper window law with perturbed phases.** If the dominant ring and its two neighbours have
phases within `η ≤ 1/10` of the exact chain phases, the chain sum is negative, whatever the other
phases are. -/
theorem genChainSum_neg_of_window {m η : ℝ} {n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10) (ψ : ℕ → ℝ)
    (hψ : ∀ j, Nat.dist j n ≤ 1 → |ψ j - m * resonantChainPhase j| ≤ η) :
    ∑' j, genChainTerm m ψ j < 0 := by
  classical
  have hm0 : 0 ≤ m := le_trans (by positivity) h1
  set A := Real.exp (resonantChainExponent m n) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have he := exp_neg_five_lt_hundredth
  have he0 := Real.exp_pos (-5)
  set u : ℕ → ℝ := fun j => 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A +
    (if Nat.dist j n = 1 then η * A else 0) -
    (if j = n then (1 / 2 - η + 2 * Real.exp (-5)) * A else 0) with hu
  have hle : ∀ j, genChainTerm m ψ j ≤ u j := by
    intro j
    by_cases hj : j = n
    · subst hj
      simp only [hu, if_true, Nat.dist_self, pow_zero, mul_one]
      have := genChainTerm_self_le h1 h2 (hψ j (by simp))
      simp only [show ¬ (0 = 1) from by omega, if_false]
      linarith
    · simp only [hu, if_neg hj, sub_zero]
      have hd1 : 1 ≤ Nat.dist j n := by
        rcases lt_or_gt_of_ne hj with h | h
        · rw [Nat.dist_eq_sub_of_le h.le]; omega
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]; omega
      rcases Nat.eq_or_lt_of_le hd1 with hd | hd
      · rw [← hd]
        simp only [if_true, pow_one]
        have := genChainTerm_le_neighbour h1 h2 hd.symm hη0 (hψ j (by omega))
        nlinarith
      · have hfar := abs_genChainTerm_le_far h1 h2 hd ψ
        have hne : Nat.dist j n ≠ 1 := by omega
        simp only [hne, if_false, add_zero]
        exact (le_abs_self _).trans hfar
  have hs1 : Summable fun j => 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A :=
    ((summable_half_pow_dist n).mul_left (2 * Real.exp (-5))).mul_right A
  have hs2 : Summable fun j : ℕ => (if Nat.dist j n = 1 then η * A else 0) :=
    summable_of_ne_finset_zero (s := {n - 1, n + 1}) fun j hj => by
      rw [if_neg]
      intro hd
      apply hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases le_total j n with h | h
      · rw [Nat.dist_eq_sub_of_le h] at hd; left; omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h] at hd; right; omega
  have hs3 : Summable fun j : ℕ => if j = n then (1 / 2 - η + 2 * Real.exp (-5)) * A else 0 :=
    summable_of_ne_finset_zero (s := {n}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hsu : Summable u := (hs1.add hs2).sub hs3
  have hsum := (summable_genChainTerm hm0 ψ).tsum_le_tsum hle hsu
  have hval : ∑' j, u j = 2 * Real.exp (-5) * A * ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n +
      ∑' j : ℕ, (if Nat.dist j n = 1 then η * A else 0) -
      (1 / 2 - η + 2 * Real.exp (-5)) * A := by
    rw [hu, (hs1.add hs2).tsum_sub hs3, hs1.tsum_add hs2, tsum_ite_eq]
    congr 2
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have hd := tsum_half_pow_dist_le n
  have hnb := tsum_neighbour_indicator_le n (B := η * A) (by positivity)
  have : ∑' j, u j < 0 := by
    rw [hval]
    have h3 : 2 * Real.exp (-5) * A * ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n ≤
        2 * Real.exp (-5) * A * 3 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith
  linarith

/-- **Lower window law with resonant phases.** If the dominant ring and its neighbours have phases
within `η ≤ 1/10` of `2πℤ`, the chain sum is positive, whatever the other phases are. -/
theorem genChainSum_pos_of_window {m η : ℝ} {n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hη : η ≤ 1 / 10) (ψ : ℕ → ℝ)
    (hψ : ∀ j, Nat.dist j n ≤ 1 → ∃ z : ℤ, |ψ j - z * (2 * Real.pi)| ≤ η) :
    0 < ∑' j, genChainTerm m ψ j := by
  classical
  have hm0 : 0 ≤ m := le_trans (by positivity) h1
  set A := Real.exp (resonantChainExponent m n) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have he := exp_neg_five_lt_hundredth
  have he0 := Real.exp_pos (-5)
  have hcos : ∀ j, Nat.dist j n ≤ 1 → 99 / 100 ≤ Real.cos (ψ j) := by
    intro j hj
    obtain ⟨z, hz⟩ := hψ j hj
    have e : Real.cos (ψ j) = Real.cos (ψ j - z * (2 * Real.pi)) := (Real.cos_sub_int_mul_two_pi _ _).symm
    rw [e]
    have hb := @Real.one_sub_sq_div_two_le_cos (ψ j - z * (2 * Real.pi))
    have hsq : (ψ j - z * (2 * Real.pi)) ^ 2 ≤ 1 / 100 := by
      have h0 := abs_nonneg (ψ j - z * (2 * Real.pi))
      rw [← sq_abs]; nlinarith
    linarith
  set v : ℕ → ℝ := fun j => (if j = n then (99 / 100 + 2 * Real.exp (-5)) * A else 0) -
    2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A with hv
  have hle : ∀ j, v j ≤ genChainTerm m ψ j := by
    intro j
    by_cases hj : j = n
    · subst hj
      simp only [hv, if_true, Nat.dist_self, pow_zero, mul_one]
      have hc := hcos j (by simp)
      unfold genChainTerm
      nlinarith
    · simp only [hv, if_neg hj, zero_sub]
      have hd1 : 1 ≤ Nat.dist j n := by
        rcases lt_or_gt_of_ne hj with h | h
        · rw [Nat.dist_eq_sub_of_le h.le]; omega
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]; omega
      rcases Nat.eq_or_lt_of_le hd1 with hd | hd
      · have hc := hcos j (by omega)
        have hEj := Real.exp_pos (resonantChainExponent m j)
        have : 0 ≤ genChainTerm m ψ j := by unfold genChainTerm; nlinarith
        have : 0 ≤ 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A := by positivity
        linarith
      · have hfar := abs_genChainTerm_le_far h1 h2 hd ψ
        have := neg_abs_le (genChainTerm m ψ j)
        linarith
  have hs1 : Summable fun j : ℕ => if j = n then (99 / 100 + 2 * Real.exp (-5)) * A else 0 :=
    summable_of_ne_finset_zero (s := {n}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hs2 : Summable fun j => 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A :=
    ((summable_half_pow_dist n).mul_left (2 * Real.exp (-5))).mul_right A
  have hsv : Summable v := hs1.sub hs2
  have hsum := hsv.tsum_le_tsum hle (summable_genChainTerm hm0 ψ)
  have hval : ∑' j, v j = (99 / 100 + 2 * Real.exp (-5)) * A -
      2 * Real.exp (-5) * A * ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n := by
    rw [hv, hs1.tsum_sub hs2, tsum_ite_eq]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have hd := tsum_half_pow_dist_le n
  have : 0 < ∑' j, v j := by
    rw [hval]
    have h3 : 2 * Real.exp (-5) * A * ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n ≤
        2 * Real.exp (-5) * A * 3 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith
  linarith

/-! ## The construction -/

open GaloisForLFunctions.HTGeometry

/-- A common denominator: `q ≥ n + 1` with `q ℓ_k/ℓ₀` within `1/Q` of `ℤ` for every `k ≤ n`. -/
theorem exists_chain_denominator (ℓ : ℕ → ℝ) (n : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ q : ℕ, n + 1 ≤ q ∧ ∀ k ≤ n, ∃ p : ℤ, |(q : ℝ) * (ℓ k / ℓ 0) - p| ≤ 1 / Q := by
  have hQ' : 0 < (n + 1) * Q := Nat.mul_pos (Nat.succ_pos n) hQ
  obtain ⟨q', hq'1, -, hq'⟩ :=
    exists_simultaneous_dirichlet (fun i : Fin (n + 1) => ℓ i / ℓ 0) hQ'
  refine ⟨(n + 1) * q', by nlinarith, fun k hk => ?_⟩
  obtain ⟨p, hp⟩ := hq' ⟨k, by omega⟩
  refine ⟨(n + 1 : ℤ) * p, ?_⟩
  simp only at hp
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e : ((((n + 1) * q' : ℕ) : ℝ) * (ℓ k / ℓ 0) - (((n + 1 : ℤ) * p : ℤ) : ℝ)) =
      ((n : ℝ) + 1) * ((q' : ℝ) * (ℓ k / ℓ 0) - p) := by push_cast; ring
  rw [e, abs_mul, abs_of_pos hn]
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc ((n : ℝ) + 1) * |(q' : ℝ) * (ℓ k / ℓ 0) - p| ≤ ((n : ℝ) + 1) * (1 / (((n + 1) * Q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hp.le hn.le
    _ = 1 / Q := by push_cast; field_simp

/-- The smallest of the first `n + 1` spacings. -/
def chainMinSpacing (ℓ : ℕ → ℝ) (n : ℕ) : ℝ := (Finset.range (n + 1)).inf' ⟨0, by simp⟩ ℓ

theorem chainMinSpacing_pos {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (n : ℕ) : 0 < chainMinSpacing ℓ n := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1)) ⟨0, by simp⟩ ℓ
  rw [chainMinSpacing, hk]; exact hℓ k

theorem chainMinSpacing_le (ℓ : ℕ → ℝ) {k n : ℕ} (hk : k ≤ n) : chainMinSpacing ℓ n ≤ ℓ k :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

/-- The precision needed at ring `n`. -/
def chainPrecision (ℓ : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈2 * Real.pi * 640 * 2 ^ (n + 1) * 10 / chainMinSpacing ℓ n⌉₊ + 1

theorem chainPrecision_pos (ℓ : ℕ → ℝ) (n : ℕ) : 0 < chainPrecision ℓ n := Nat.succ_pos _

/-- The common denominator of ring `n`. -/
def chainDen (ℓ : ℕ → ℝ) (n : ℕ) : ℕ :=
  Classical.choose (exists_chain_denominator ℓ n (chainPrecision_pos ℓ n))

theorem chainDen_spec (ℓ : ℕ → ℝ) (n : ℕ) :
    n + 1 ≤ chainDen ℓ n ∧ ∀ k ≤ n, ∃ p : ℤ,
      |(chainDen ℓ n : ℝ) * (ℓ k / ℓ 0) - p| ≤ 1 / chainPrecision ℓ n :=
  Classical.choose_spec (exists_chain_denominator ℓ n (chainPrecision_pos ℓ n))

/-- The real part `(1 − 2^{−(n+1)})/4`. -/
def chainRe (n : ℕ) : ℝ := (1 - 1 / 2 ^ (n + 1)) / 4

/-- The point `s_n = (1 − 2^{−(n+1)})/4 + i(θ_n/4 + 2πq_n/ℓ₀)`. -/
def chainPoint (ℓ : ℕ → ℝ) (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  (chainRe n : ℂ) + Complex.I * ((θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0 : ℝ) : ℂ)

/-- The weight `e^{−40(n+1)}`. -/
def chainWeight (n : ℕ) : ℝ := Real.exp (-(40 * ((n : ℝ) + 1)))

theorem re_chainWeight_mul_exp (ℓ : ℕ → ℝ) (θ : ℕ → ℝ) (u : ℝ) (n : ℕ) :
    chainWeight n * (Complex.exp ((u : ℂ) * chainPoint ℓ θ n)).re =
      Real.exp (resonantChainExponent (u / 4) n) *
        Real.cos (u * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0)) := by
  have e : (u : ℂ) * chainPoint ℓ θ n = ((u * chainRe n : ℝ) : ℂ) +
      ((u * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0) : ℝ) : ℂ) * Complex.I := by
    unfold chainPoint; push_cast; ring
  rw [e, Complex.exp_add_mul_I]
  rw [show Complex.exp ((u * chainRe n : ℝ) : ℂ) = ((Real.exp (u * chainRe n) : ℝ) : ℂ) by
    rw [Complex.ofReal_exp]]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one]
  unfold chainWeight resonantChainExponent chainRe
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem abs_re_chainWeight_mul_exp_le (ℓ : ℕ → ℝ) (θ : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |chainWeight n * (Complex.exp ((u : ℂ) * chainPoint ℓ θ n)).re| ≤
      Real.exp (u / 4) * chainWeight n := by
  rw [re_chainWeight_mul_exp, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc := Real.abs_cos_le_one (u * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0))
  have h1 : Real.exp (resonantChainExponent (u / 4) n) ≤ Real.exp (u / 4) * chainWeight n := by
    unfold chainWeight resonantChainExponent
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ u / 4 * (1 / 2 ^ (n + 1)) := by positivity
    nlinarith
  have := Real.exp_pos (resonantChainExponent (u / 4) n)
  nlinarith

theorem summable_chainWeight : Summable chainWeight := by
  have := (summable_geometric_of_lt_one (Real.exp_pos (-40)).le
    ((Real.exp_lt_exp.mpr (by norm_num : (-40 : ℝ) < 0)).trans_eq Real.exp_zero)).mul_left
    (Real.exp (-40))
  refine this.congr fun n => ?_
  unfold chainWeight
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring

theorem summable_chainSample (ℓ : ℕ → ℝ) (θ : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Summable fun n => chainWeight n * (Complex.exp ((u : ℂ) * chainPoint ℓ θ n)).re :=
  Summable.of_norm_bounded (summable_chainWeight.mul_left (Real.exp (u / 4)))
    fun n => by rw [Real.norm_eq_abs]; exact abs_re_chainWeight_mul_exp_le ℓ θ hu n

/-- The phase at the sample `u = jℓ_k`, reduced modulo `2π` on the controlled rings `n ≥ k`. -/
theorem exists_reduced_phase {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (θ : ℕ → ℝ) {k n j : ℕ} (hkn : k ≤ n) :
    ∃ z : ℤ, |(j * ℓ k) * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0) - z * (2 * Real.pi) -
        (j * ℓ k / 4) * θ n| ≤ 2 * Real.pi * j / chainPrecision ℓ n := by
  obtain ⟨p, hp⟩ := (chainDen_spec ℓ n).2 k hkn
  refine ⟨j * p, ?_⟩
  have hℓ0 := hℓ 0
  have e : (j * ℓ k) * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0) - ((j * p : ℤ) : ℝ) * (2 * Real.pi) -
      (j * ℓ k / 4) * θ n = 2 * Real.pi * j * ((chainDen ℓ n : ℝ) * (ℓ k / ℓ 0) - p) := by
    push_cast; field_simp; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hQ : (0 : ℝ) < chainPrecision ℓ n := by exact_mod_cast chainPrecision_pos ℓ n
  calc 2 * Real.pi * j * |(chainDen ℓ n : ℝ) * (ℓ k / ℓ 0) - p|
      ≤ 2 * Real.pi * j * (1 / chainPrecision ℓ n) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2 * Real.pi * j / chainPrecision ℓ n := by ring

/-- On the rings that matter for samples `u ≤ 640·2^{n+1}`, the reduced phase error is at most
`1/10`. -/
theorem reduced_phase_error_le {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) {k n j : ℕ} (hkn : k ≤ n)
    (hj : (j : ℝ) * ℓ k ≤ 640 * 2 ^ (n + 1)) :
    2 * Real.pi * j / chainPrecision ℓ n ≤ 1 / 10 := by
  have hm := chainMinSpacing_pos hℓ n
  have hmk := chainMinSpacing_le ℓ hkn
  have hk := hℓ k
  have hQ : 2 * Real.pi * 640 * 2 ^ (n + 1) * 10 / chainMinSpacing ℓ n ≤ chainPrecision ℓ n := by
    unfold chainPrecision
    push_cast
    have := Nat.le_ceil (2 * Real.pi * 640 * 2 ^ (n + 1) * 10 / chainMinSpacing ℓ n)
    linarith
  have hQ0 : (0 : ℝ) < chainPrecision ℓ n := by exact_mod_cast chainPrecision_pos ℓ n
  have hπ := Real.pi_pos
  rw [div_le_iff₀ hQ0]
  have hj' : (j : ℝ) ≤ 640 * 2 ^ (n + 1) / ℓ k := by rw [le_div_iff₀ hk]; exact hj
  have h2 : 640 * 2 ^ (n + 1) / ℓ k ≤ 640 * 2 ^ (n + 1) / chainMinSpacing ℓ n :=
    div_le_div_of_nonneg_left (by positivity) hm hmk
  have h3 : 2 * Real.pi * (j : ℝ) ≤ 2 * Real.pi * (640 * 2 ^ (n + 1) / chainMinSpacing ℓ n) := by
    have := hj'.trans h2; nlinarith
  have h4 : 2 * Real.pi * (640 * 2 ^ (n + 1) / chainMinSpacing ℓ n) =
      1 / 10 * (2 * Real.pi * 640 * 2 ^ (n + 1) * 10 / chainMinSpacing ℓ n) := by
    field_simp
  nlinarith

/-- The dyadic window containing a large real `m`, beyond the window of a given ring. -/
theorem exists_window_ge {m : ℝ} {k : ℕ} (hm : 160 * 2 ^ (k + 1) ≤ m) :
    ∃ N : ℕ, k + 1 ≤ N ∧ 80 * 2 ^ N ≤ m ∧ m ≤ 160 * 2 ^ N := by
  classical
  have hex : ∃ N : ℕ, m ≤ 160 * 2 ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt m (by norm_num : (1 : ℝ) < 2)
    exact ⟨N, by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]⟩
  set N := Nat.find hex with hN
  have h2 : m ≤ 160 * 2 ^ N := Nat.find_spec hex
  have hNk : k + 1 ≤ N := by
    by_contra hlt
    push Not at hlt
    have : (2 : ℝ) ^ N ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hpos : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith
  obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hmin := Nat.find_min hex (m := N') (by omega)
  push Not at hmin
  refine ⟨N, hNk, ?_, h2⟩
  rw [hN', pow_succ]
  linarith

/-! ## Point data -/

theorem chainRe_strictMono : StrictMono chainRe := by
  intro a b hab
  unfold chainRe
  have : (2 : ℝ) ^ (a + 1) < 2 ^ (b + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have h0 : (0 : ℝ) < 2 ^ (a + 1) := by positivity
  have : 1 / (2 : ℝ) ^ (b + 1) < 1 / 2 ^ (a + 1) := one_div_lt_one_div_of_lt h0 this
  linarith

theorem chainRe_mem (n : ℕ) : 0 < chainRe n ∧ chainRe n < 1 / 4 := by
  unfold chainRe
  have h1 : (1 : ℝ) / 2 ^ (n + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ 2 ^ (n + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h0 : (0 : ℝ) < 1 / 2 ^ (n + 1) := by positivity
  constructor <;> linarith

theorem chainRe_tendsto : Tendsto chainRe atTop (𝓝 (1 / 4)) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have h' : Tendsto (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ (n + 1)) / 4) atTop (𝓝 ((1 - 0) / 4)) :=
    (tendsto_const_nhds.sub h).div_const 4
  rw [sub_zero] at h'
  refine h'.congr fun n => ?_
  unfold chainRe
  rw [one_div_pow]

theorem chainPoint_re (ℓ θ : ℕ → ℝ) (n : ℕ) : (chainPoint ℓ θ n).re = chainRe n := by
  unfold chainPoint; simp

theorem chainPoint_im (ℓ θ : ℕ → ℝ) (n : ℕ) :
    (chainPoint ℓ θ n).im = θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0 := by
  unfold chainPoint; simp

theorem chainPoint_locallyFinite {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) {θ : ℕ → ℝ}
    (hθ : ∀ n, |θ n| ≤ 4) (T : ℝ) : {n | |(chainPoint ℓ θ n).im| ≤ T}.Finite := by
  have hℓ0 := hℓ 0
  have hπ := Real.pi_pos
  refine (Set.finite_Iic ⌈(T + 1) * ℓ 0 / (2 * Real.pi)⌉₊).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn
  rw [chainPoint_im] at hn
  simp only [Set.mem_Iic]
  have hden := (chainDen_spec ℓ n).1
  have hdenR : (n : ℝ) + 1 ≤ chainDen ℓ n := by exact_mod_cast hden
  have hθn := hθ n
  have habs := le_abs_self (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0)
  have hθ4 : -1 ≤ θ n / 4 := by rw [abs_le] at hθn; linarith [hθn.1]
  have h1 : 2 * Real.pi * chainDen ℓ n / ℓ 0 ≤ T + 1 := by linarith
  have h2 : 2 * Real.pi * ((n : ℝ) + 1) / ℓ 0 ≤ T + 1 := by
    have : 2 * Real.pi * ((n : ℝ) + 1) / ℓ 0 ≤ 2 * Real.pi * chainDen ℓ n / ℓ 0 := by
      apply div_le_div_of_nonneg_right _ hℓ0.le; nlinarith
    linarith
  have h3 : (n : ℝ) ≤ (T + 1) * ℓ 0 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hℓ0] at h2
    nlinarith
  exact_mod_cast h3.trans (Nat.le_ceil _)

theorem abs_resonantChainPhase_le (n : ℕ) : |resonantChainPhase n| ≤ 4 := by
  unfold resonantChainPhase
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  rw [abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith

/-! ## Samples as perturbed chains -/

/-- The phase of ring `n` at the sample `u = jℓ_k`, reduced modulo `2π` on the rings `n ≥ k`. -/
def chainPhase {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (θ : ℕ → ℝ) (k j n : ℕ) : ℝ :=
  if h : k ≤ n then
    (j * ℓ k) * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0) -
      ((Classical.choose (exists_reduced_phase hℓ θ (j := j) h) : ℤ) : ℝ) * (2 * Real.pi)
  else (j * ℓ k) * (θ n / 4 + 2 * Real.pi * chainDen ℓ n / ℓ 0)

theorem chainSample_eq {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (θ : ℕ → ℝ) (k j : ℕ) :
    ∑' n, chainWeight n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) * chainPoint ℓ θ n)).re =
      ∑' n, genChainTerm ((j * ℓ k : ℝ) / 4) (chainPhase hℓ θ k j) n := by
  refine tsum_congr fun n => ?_
  rw [re_chainWeight_mul_exp]
  unfold genChainTerm chainPhase
  congr 1
  split_ifs with h
  · exact (Real.cos_sub_int_mul_two_pi _ _).symm
  · rfl

theorem chainPhase_close {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (θ : ℕ → ℝ) {k j n : ℕ} (hkn : k ≤ n)
    (hj : (j : ℝ) * ℓ k ≤ 640 * 2 ^ (n + 1)) :
    |chainPhase hℓ θ k j n - ((j * ℓ k : ℝ) / 4) * θ n| ≤ 1 / 10 := by
  unfold chainPhase
  rw [dif_pos hkn]
  have hspec := Classical.choose_spec (exists_reduced_phase hℓ θ (j := j) hkn)
  have herr := reduced_phase_error_le hℓ hkn hj
  exact hspec.trans herr

theorem abs_chainSample_le {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (θ : ℕ → ℝ) (k j : ℕ) :
    |∑' n, chainWeight n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) * chainPoint ℓ θ n)).re| ≤
      Real.exp (j * ℓ k / 4) * ∑' n, chainWeight n := by
  have hu0 : (0 : ℝ) ≤ j * ℓ k := by have := hℓ k; positivity
  have hs := summable_chainSample ℓ θ hu0
  calc |∑' n, chainWeight n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) * chainPoint ℓ θ n)).re|
      ≤ ∑' n, |chainWeight n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) * chainPoint ℓ θ n)).re| := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq ?_)
        simp only [Real.norm_eq_abs]
    _ ≤ ∑' n, Real.exp ((j * ℓ k : ℝ) / 4) * chainWeight n :=
        hs.abs.tsum_le_tsum (fun n => abs_re_chainWeight_mul_exp_le ℓ θ hu0 n)
          (summable_chainWeight.mul_left _)
    _ = Real.exp (j * ℓ k / 4) * ∑' n, chainWeight n := by rw [tsum_mul_left]

/-- Beyond the window of ring `k + 1`, the sample at `jℓ_k` sits in a window of a controlled ring. -/
theorem exists_controlled_window {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) {k j : ℕ}
    (hj : ⌈4 * 160 * 2 ^ (k + 1) / ℓ k⌉₊ ≤ j) :
    ∃ N : ℕ, k + 1 ≤ N ∧ 80 * 2 ^ N ≤ (j * ℓ k : ℝ) / 4 ∧ (j * ℓ k : ℝ) / 4 ≤ 160 * 2 ^ N := by
  have hk := hℓ k
  have hm : 160 * 2 ^ (k + 1) ≤ (j * ℓ k : ℝ) / 4 := by
    have h1 : 4 * 160 * 2 ^ (k + 1) / ℓ k ≤ (⌈4 * 160 * 2 ^ (k + 1) / ℓ k⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈4 * 160 * 2 ^ (k + 1) / ℓ k⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have := (div_le_iff₀ hk).mp (h1.trans h2)
    linarith
  exact exists_window_ge hm

theorem controlled_of_window {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) (θ : ℕ → ℝ) {k j N : ℕ}
    (hNk : k + 1 ≤ N) (hN2 : (j * ℓ k : ℝ) / 4 ≤ 160 * 2 ^ N) :
    ∀ n, Nat.dist n N ≤ 1 → |chainPhase hℓ θ k j n - ((j * ℓ k : ℝ) / 4) * θ n| ≤ 1 / 10 := by
  intro n hn
  have hnN : N ≤ n + 1 := by
    rcases le_total n N with h | h
    · rw [Nat.dist_eq_sub_of_le h] at hn; omega
    · omega
  have hkn : k ≤ n := by omega
  refine chainPhase_close hℓ θ hkn ?_
  have : (2 : ℝ) ^ N ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hnN
  have h4 : (j : ℝ) * ℓ k ≤ 4 * (160 * 2 ^ N) := by linarith
  nlinarith

/-- **Upper bounds along every spacing of a countable family.** -/
theorem exists_chain_configuration_countable_bddAbove {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) :
    ∃ (s : ℕ → ℂ) (c : ℕ → ℝ), StrictMono (fun n => (s n).re) ∧
      (∀ n, 0 < (s n).re ∧ (s n).re < 1 / 4) ∧ Tendsto (fun n => (s n).re) atTop (𝓝 (1 / 4)) ∧
      (∀ T : ℝ, {n | |(s n).im| ≤ T}.Finite) ∧ (∀ n, 0 < c n) ∧ Summable c ∧
      ∀ k, ∃ M : ℝ, ∀ j : ℕ, ∑' n, c n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) * s n)).re ≤ M := by
  refine ⟨chainPoint ℓ resonantChainPhase, chainWeight, ?_, ?_, ?_, ?_, fun n => Real.exp_pos _,
    summable_chainWeight, ?_⟩
  · intro a b hab; simp only [chainPoint_re]; exact chainRe_strictMono hab
  · intro n; rw [chainPoint_re]; exact chainRe_mem n
  · simp only [chainPoint_re]; exact chainRe_tendsto
  · exact chainPoint_locallyFinite hℓ abs_resonantChainPhase_le
  · intro k
    set J : ℕ := ⌈4 * 160 * 2 ^ (k + 1) / ℓ k⌉₊ with hJ
    refine ⟨max 0 (Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n), fun j => ?_⟩
    by_cases hjJ : J ≤ j
    · obtain ⟨N, hNk, hN1, hN2⟩ := exists_controlled_window hℓ hjJ
      rw [chainSample_eq hℓ]
      have := genChainSum_neg_of_window hN1 hN2 (by norm_num) le_rfl (chainPhase hℓ resonantChainPhase k j)
        (controlled_of_window hℓ resonantChainPhase hNk hN2)
      exact (this.le).trans (le_max_left _ _)
    · push Not at hjJ
      have hb := abs_chainSample_le hℓ resonantChainPhase k j
      have hk := hℓ k
      have hjJ' : (j : ℝ) * ℓ k / 4 ≤ J * ℓ k / 4 := by
        have : (j : ℝ) ≤ J := by exact_mod_cast hjJ.le
        nlinarith
      have hmono : Real.exp (j * ℓ k / 4) * ∑' n, chainWeight n ≤
          Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hjJ')
          (tsum_nonneg fun n => (Real.exp_pos _).le)
      exact ((le_abs_self _).trans (hb.trans hmono)).trans (le_max_right _ _)

/-- **Lower bounds along every spacing of a countable family.** -/
theorem exists_chain_configuration_countable_bddBelow {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k) :
    ∃ (s : ℕ → ℂ) (c : ℕ → ℝ), StrictMono (fun n => (s n).re) ∧
      (∀ n, 0 < (s n).re ∧ (s n).re < 1 / 4) ∧ Tendsto (fun n => (s n).re) atTop (𝓝 (1 / 4)) ∧
      (∀ T : ℝ, {n | |(s n).im| ≤ T}.Finite) ∧ (∀ n, 0 < c n) ∧ Summable c ∧
      ∀ k, ∃ M : ℝ, ∀ j : ℕ, -M ≤ ∑' n, c n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) * s n)).re := by
  refine ⟨chainPoint ℓ (fun _ => 0), chainWeight, ?_, ?_, ?_, ?_, fun n => Real.exp_pos _,
    summable_chainWeight, ?_⟩
  · intro a b hab; simp only [chainPoint_re]; exact chainRe_strictMono hab
  · intro n; rw [chainPoint_re]; exact chainRe_mem n
  · simp only [chainPoint_re]; exact chainRe_tendsto
  · exact chainPoint_locallyFinite hℓ (fun n => by simp)
  · intro k
    set J : ℕ := ⌈4 * 160 * 2 ^ (k + 1) / ℓ k⌉₊ with hJ
    refine ⟨max 0 (Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n), fun j => ?_⟩
    by_cases hjJ : J ≤ j
    · obtain ⟨N, hNk, hN1, hN2⟩ := exists_controlled_window hℓ hjJ
      rw [chainSample_eq hℓ]
      have hctl := controlled_of_window hℓ (fun _ => 0) hNk hN2
      have := genChainSum_pos_of_window hN1 hN2 le_rfl (chainPhase hℓ (fun _ => 0) k j)
        (fun n hn => ⟨0, by simpa using hctl n hn⟩)
      have h0 : -max 0 (Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n) ≤ 0 := by
        have := le_max_left 0 (Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n); linarith
      linarith
    · push Not at hjJ
      have hb := abs_chainSample_le hℓ (fun _ => 0) k j
      have hk := hℓ k
      have hjJ' : (j : ℝ) * ℓ k / 4 ≤ J * ℓ k / 4 := by
        have : (j : ℝ) ≤ J := by exact_mod_cast hjJ.le
        nlinarith
      have hmono : Real.exp (j * ℓ k / 4) * ∑' n, chainWeight n ≤
          Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hjJ')
          (tsum_nonneg fun n => (Real.exp_pos _).le)
      have := neg_abs_le (∑' n, chainWeight n * (Complex.exp (((j * ℓ k : ℝ) : ℂ) *
        chainPoint ℓ (fun _ => 0) n)).re)
      have hM := le_max_right 0 (Real.exp (J * ℓ k / 4) * ∑' n, chainWeight n)
      linarith

end RHTower
