import GaloisForLFunctions.HTGeometry.RelativeScaleDefectKernel
import GaloisForLFunctions.RHTower.ShrinkingWindowPrimeSupply

/-!
# Crowded prime-log pairs

The certified shrinking-window prime supply gives constants `c, K` such that every large window
`[R, R + η_R]`, `η_R = K e^{-c R^{1/10}}`, contains a prime logarithm.  Applying it at `R` and at
`R + 2η_R` (the admissible width only shrinks with the base point) produces primes with
`R ≤ log p ≤ R + η_R` and `R + 2η_R ≤ log q ≤ R + 3η_R` `(FGP.6)`.  Their normalized ordered
defect is uniformly tiny: `sup_t |ab ω_t(a,b)| ≤ (3K/R) e^{-c R^{1/10}}` `(FGP.7)`.  Choosing the
base points `R_j = R₀ + 4j` separates the products `p_j q_j`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- The crowding width `η_R = K e^{-c R^{1/10}}`. -/
def crowdWidth (c K R : ℝ) : ℝ := K * Real.exp (-(c * R ^ ((1 : ℝ) / 10)))

theorem crowdWidth_pos {c K : ℝ} (hK : 0 < K) (R : ℝ) : 0 < crowdWidth c K R := by
  unfold crowdWidth; positivity

theorem crowdWidth_antitone {c K : ℝ} (hc : 0 < c) (hK : 0 < K) {R R' : ℝ} (hR : 0 ≤ R)
    (hRR' : R ≤ R') : crowdWidth c K R' ≤ crowdWidth c K R := by
  unfold crowdWidth
  gcongr

theorem tendsto_crowdWidth {c K : ℝ} (hc : 0 < c) :
    Tendsto (crowdWidth c K) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => c * R ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).const_mul_atTop hc
  have h2 : Tendsto (fun R : ℝ => K * Real.exp (-(c * R ^ ((1 : ℝ) / 10)))) atTop (𝓝 (K * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
  rw [mul_zero] at h2
  exact h2

/-- **`(FGP.6)`: crowded prime pairs.** -/
theorem exists_crowded_prime_pair :
    ∃ c K R₀ : ℝ, 0 < c ∧ 0 < K ∧ 3 ≤ R₀ ∧ (∀ R, R₀ ≤ R → crowdWidth c K R ≤ 1) ∧
      ∀ R, R₀ ≤ R → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        R ≤ Real.log p ∧ Real.log p ≤ R + crowdWidth c K R ∧
        R + 2 * crowdWidth c K R ≤ Real.log q ∧ Real.log q ≤ R + 3 * crowdWidth c K R := by
  obtain ⟨c, K, y₀, hc, hK, hy₀, hsupply⟩ := RHTower.exists_prime_log_in_shrinking_window
  have hev : ∀ᶠ R in atTop, crowdWidth c K R ≤ 1 :=
    (tendsto_crowdWidth hc).eventually (ge_mem_nhds one_pos)
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hev
  refine ⟨c, K, max y₀ R₁, hc, hK, le_trans hy₀ (le_max_left _ _),
    fun R hR => hR₁ R (le_trans (le_max_right _ _) hR), fun R hR => ?_⟩
  have hRy : y₀ ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 ≤ R := by linarith
  have hη : crowdWidth c K R ≤ 1 := hR₁ R (le_trans (le_max_right _ _) hR)
  have hηpos := crowdWidth_pos (c := c) hK R
  obtain ⟨p, hp, hp1, hp2⟩ := hsupply R (crowdWidth c K R) hRy hηpos hη le_rfl
  have hR2 : R ≤ R + 2 * crowdWidth c K R := by linarith
  obtain ⟨q, hq, hq1, hq2⟩ := hsupply (R + 2 * crowdWidth c K R) (crowdWidth c K R)
    (le_trans hRy hR2) hηpos hη (crowdWidth_antitone hc hK hR0 hR2)
  exact ⟨p, q, hp, hq, hp1, hp2, hq1, by linarith⟩

/-- A separated sequence of crowded prime pairs. -/
structure CrowdedPairs where
  c : ℝ
  K : ℝ
  R₀ : ℝ
  hc : 0 < c
  hK : 0 < K
  hR₀ : 3 ≤ R₀
  /-- The base points `R_j = R₀ + 4j`. -/
  base : ℕ → ℝ
  base_eq : ∀ j, base j = R₀ + 4 * j
  width_le : ∀ j, crowdWidth c K (base j) ≤ 1
  p : ℕ → ℕ
  q : ℕ → ℕ
  p_prime : ∀ j, (p j).Prime
  q_prime : ∀ j, (q j).Prime
  log_p_ge : ∀ j, base j ≤ Real.log (p j)
  log_p_le : ∀ j, Real.log (p j) ≤ base j + crowdWidth c K (base j)
  log_q_ge : ∀ j, base j + 2 * crowdWidth c K (base j) ≤ Real.log (q j)
  log_q_le : ∀ j, Real.log (q j) ≤ base j + 3 * crowdWidth c K (base j)

namespace CrowdedPairs

theorem nonempty : Nonempty CrowdedPairs := by
  obtain ⟨c, K, R₀, hc, hK, hR₀, hwidth, hpair⟩ := exists_crowded_prime_pair
  have h : ∀ j : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      R₀ + 4 * j ≤ Real.log p ∧ Real.log p ≤ R₀ + 4 * j + crowdWidth c K (R₀ + 4 * j) ∧
      R₀ + 4 * j + 2 * crowdWidth c K (R₀ + 4 * j) ≤ Real.log q ∧
      Real.log q ≤ R₀ + 4 * j + 3 * crowdWidth c K (R₀ + 4 * j) := fun j =>
    hpair _ (by have : (0 : ℝ) ≤ 4 * j := (by positivity); linarith)
  choose p q hp hq h1 h2 h3 h4 using h
  exact ⟨⟨c, K, R₀, hc, hK, hR₀, fun j => R₀ + 4 * j, fun _ => rfl,
    fun j => hwidth _ (by have : (0 : ℝ) ≤ 4 * j := (by positivity); linarith),
    p, q, hp, hq, h1, h2, h3, h4⟩⟩

variable (P : CrowdedPairs)

/-- `a_j = log p_j`. -/
def a (j : ℕ) : ℝ := Real.log (P.p j)

/-- `b_j = log q_j`. -/
def b (j : ℕ) : ℝ := Real.log (P.q j)

/-- `η_j = η_{R_j}`. -/
def η (j : ℕ) : ℝ := crowdWidth P.c P.K (P.base j)

theorem base_ge (j : ℕ) : 3 ≤ P.base j := by
  rw [P.base_eq]
  have : (0 : ℝ) ≤ 4 * j := by positivity
  linarith [P.hR₀]

theorem η_pos (j : ℕ) : 0 < P.η j := crowdWidth_pos P.hK _

theorem a_pos (j : ℕ) : 0 < P.a j := by
  have := P.log_p_ge j
  have := P.base_ge j
  unfold a; linarith

theorem a_lt_b (j : ℕ) : P.a j < P.b j := by
  have h1 := P.log_p_le j
  have h2 := P.log_q_ge j
  have h3 := P.η_pos j
  unfold a b η at *
  linarith

theorem b_sub_a_le (j : ℕ) : P.b j - P.a j ≤ 3 * P.η j := by
  have h1 := P.log_p_ge j
  have h2 := P.log_q_le j
  unfold a b η
  linarith

theorem b_le_two_a (j : ℕ) : P.b j ≤ 2 * P.a j := by
  have h1 := P.log_p_ge j
  have h2 := P.log_q_le j
  have h3 := P.width_le j
  have h4 := P.base_ge j
  unfold a b
  linarith

theorem a_ge (j : ℕ) : P.base j ≤ P.a j := P.log_p_ge j

theorem b_le (j : ℕ) : P.b j ≤ P.base j + 3 := by
  have h2 := P.log_q_le j
  have h3 := P.width_le j
  unfold b
  linarith

/-- **`(FGP.7)`**: `|a_j b_j ω_t(a_j, b_j)| ≤ (3K/R_j) e^{-c R_j^{1/10}}` for all `t ≥ 0`. -/
theorem abs_defect_le (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |P.a j * P.b j * defectKernel t (P.a j) (P.b j)| ≤ 3 * P.η j / P.base j := by
  have hneg := neg_defect_le (P.a_pos j) (P.a_lt_b j) ht
  have hnn : 0 ≤ -(P.a j * P.b j * defectKernel t (P.a j) (P.b j)) := by
    rcases eq_or_lt_of_le ht with h0 | h0
    · subst h0
      simp [defectKernel, simplexKernel]
    · exact (neg_defect_pos (P.a_pos j) (P.a_lt_b j) h0).le
  rw [abs_of_nonpos (neg_nonneg.mp hnn)]
  calc -(P.a j * P.b j * defectKernel t (P.a j) (P.b j)) ≤ (P.b j - P.a j) / P.a j := hneg
    _ ≤ 3 * P.η j / P.base j := by
        have hR : 0 < P.base j := by linarith [P.base_ge j]
        exact div_le_div₀ (by linarith [P.η_pos j]) (P.b_sub_a_le j) hR (P.a_ge j)

/-- The products `p_j q_j` are pairwise distinct. -/
theorem mul_injective : Function.Injective fun j => P.p j * P.q j := by
  intro i j hij
  have hlog : P.a i + P.b i = P.a j + P.b j := by
    have hpi := (P.p_prime i).pos
    have hqi := (P.q_prime i).pos
    have hpj := (P.p_prime j).pos
    have hqj := (P.q_prime j).pos
    have h := congrArg (fun n : ℕ => Real.log (n : ℝ)) hij
    simp only [Nat.cast_mul] at h
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity)] at h
  have bounds : ∀ k, 2 * P.base k ≤ P.a k + P.b k ∧ P.a k + P.b k ≤ 2 * P.base k + 4 := fun k => by
    have := P.a_ge k
    have := P.b_le k
    have := P.a_lt_b k
    have h1 := P.log_p_le k
    have h2 := P.width_le k
    unfold a at *
    constructor <;> linarith
  have hi := bounds i
  have hj := bounds j
  simp only [P.base_eq] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exfalso
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith [hi.1, hi.2, hj.1, hj.2]
  · exact h
  · exfalso
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    linarith [hi.1, hi.2, hj.1, hj.2]

end CrowdedPairs

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
