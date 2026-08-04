import GaloisForLFunctions.RHTower.Sieve.MRInterface
import GaloisForLFunctions.RHTower.Sieve.CoprimeMoebiusSeries

/-!
# Rescaling the balanced pairs at a shared prime

A balanced pair both of whose entries are divisible by `p` is `(p m₁, p m₂)` with `(m₁, m₂)` a
balanced pair for

    X_p = x/p²,   h_p = h/p,

because `√X_p = √x/p` and `X_p + h_p√X_p = (x + h√x)/p²`.  The correspondence is a bijection, so the
shared-prime sector is literally a balanced pair sum at the rescaled parameters — which is what lets
the bilinear theorem be applied there.

The membership test simplifies first: for `x > 0` the bounding box of `balancedPairs` is implied by
the product constraint, so membership is exactly the four real inequalities.
-/

namespace RHTower.Sieve

open Finset

/-- **Membership in the balanced pair set**, with the bounding box eliminated. -/
theorem mem_balancedPairs {x h : ℝ} (hx : 0 < x) (q : ℕ × ℕ) :
    q ∈ balancedPairs x h ↔
      (x ≤ ((q.1 * q.2 : ℕ) : ℝ) ∧ ((q.1 * q.2 : ℕ) : ℝ) ≤ x + h * Real.sqrt x
        ∧ Real.sqrt x ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * Real.sqrt x) := by
  classical
  constructor
  · intro hq
    rw [balancedPairs, Finset.mem_filter] at hq
    exact hq.2
  · intro hq
    obtain ⟨h1, h2, h3, h4⟩ := hq
    have hprodpos : 0 < q.1 * q.2 := by
      by_contra hc
      have : q.1 * q.2 = 0 := by omega
      rw [this] at h1
      simp at h1
      linarith
    have hq1 : 1 ≤ q.1 := by
      rcases Nat.eq_zero_or_pos q.1 with hz | hz
      · rw [hz] at hprodpos; simp at hprodpos
      · exact hz
    have hq2 : 1 ≤ q.2 := by
      rcases Nat.eq_zero_or_pos q.2 with hz | hz
      · rw [hz] at hprodpos; simp at hprodpos
      · exact hz
    have hle1 : q.1 ≤ q.1 * q.2 := Nat.le_mul_of_pos_right _ (by omega)
    have hle2 : q.2 ≤ q.1 * q.2 := Nat.le_mul_of_pos_left _ (by omega)
    have hfloor : q.1 * q.2 ≤ ⌊x + h * Real.sqrt x⌋₊ := Nat.le_floor h2
    rw [balancedPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hq1, le_trans hle1 hfloor⟩, ⟨hq2, le_trans hle2 hfloor⟩⟩, h1, h2, h3, h4⟩

/-- The rescaled square root. -/
theorem sqrt_div_sq {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 0 < p) :
    Real.sqrt (x / (p : ℝ) ^ 2) = Real.sqrt x / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [Real.sqrt_div hx, Real.sqrt_sq hp0.le]

/-- The rescaled window endpoint. -/
theorem rescaled_endpoint {x h : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 0 < p) :
    x / (p : ℝ) ^ 2 + h / (p : ℝ) * Real.sqrt (x / (p : ℝ) ^ 2)
      = (x + h * Real.sqrt x) / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [sqrt_div_sq hx hp]
  field_simp

/-- **The shared-prime sector is a rescaled balanced pair set.** -/
theorem balancedPairs_shared_eq_image {x h : ℝ} (hx : 0 < x) {p : ℕ} (hp : 0 < p) :
    (balancedPairs x h).filter (fun q => p ∣ q.1 ∧ p ∣ q.2)
      = (balancedPairs (x / (p : ℝ) ^ 2) (h / (p : ℝ))).image
        (fun q => (p * q.1, p * q.2)) := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hXpos : (0 : ℝ) < x / (p : ℝ) ^ 2 := by positivity
  have hsq := sqrt_div_sq hx.le hp
  have hend := rescaled_endpoint (h := h) hx.le hp
  refine Finset.Subset.antisymm ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hmem, hd1, hd2⟩ := hq
    obtain ⟨a, ha⟩ := hd1
    obtain ⟨b, hb⟩ := hd2
    rw [mem_balancedPairs hx, ha, hb] at hmem
    obtain ⟨h1, h2, h3, h4⟩ := hmem
    have hab : ((p * a * (p * b) : ℕ) : ℝ) = (p : ℝ) ^ 2 * ((a * b : ℕ) : ℝ) := by
      push_cast; ring
    have hpa : ((p * a : ℕ) : ℝ) = (p : ℝ) * ((a : ℕ) : ℝ) := by push_cast; ring
    rw [hab] at h1 h2
    rw [hpa] at h3 h4
    rw [Finset.mem_image]
    refine ⟨(a, b), ?_, ?_⟩
    · rw [mem_balancedPairs hXpos, hend, hsq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [div_le_iff₀ (by positivity)]
        linarith
      · rw [le_div_iff₀ (by positivity)]
        linarith
      · rw [div_le_iff₀ hp0]
        have hc := mul_comm ((a : ℕ) : ℝ) ((p : ℕ) : ℝ)
        linarith
      · rw [show (2 : ℝ) * (Real.sqrt x / (p : ℝ)) = (2 * Real.sqrt x) / (p : ℝ) by ring,
          le_div_iff₀ hp0]
        have hc := mul_comm ((a : ℕ) : ℝ) ((p : ℕ) : ℝ)
        linarith
    · rw [Prod.ext_iff]
      exact ⟨ha.symm, hb.symm⟩
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨⟨a, b⟩, hmem, hqe⟩ := hq
    subst hqe
    rw [mem_balancedPairs hXpos, hend, hsq] at hmem
    obtain ⟨h1, h2, h3, h4⟩ := hmem
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)] at h2
    rw [div_le_iff₀ hp0] at h3
    rw [show (2 : ℝ) * (Real.sqrt x / (p : ℝ)) = (2 * Real.sqrt x) / (p : ℝ) by ring,
      le_div_iff₀ hp0] at h4
    rw [Finset.mem_filter]
    refine ⟨?_, ⟨a, rfl⟩, ⟨b, rfl⟩⟩
    rw [mem_balancedPairs hx]
    have hab : ((p * a * (p * b) : ℕ) : ℝ) = (p : ℝ) ^ 2 * ((a * b : ℕ) : ℝ) := by
      push_cast; ring
    have hpa : ((p * a : ℕ) : ℝ) = (p : ℝ) * ((a : ℕ) : ℝ) := by push_cast; ring
    show x ≤ ((p * a * (p * b) : ℕ) : ℝ) ∧ ((p * a * (p * b) : ℕ) : ℝ) ≤ x + h * Real.sqrt x
      ∧ Real.sqrt x ≤ ((p * a : ℕ) : ℝ) ∧ ((p * a : ℕ) : ℝ) ≤ 2 * Real.sqrt x
    rw [hab, hpa]
    have hc := mul_comm ((a : ℕ) : ℝ) ((p : ℕ) : ℝ)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The weight of the card's step 2: squarefree and coprime to `p`. -/
noncomputable def coprimeSquarefreeWeight (p : ℕ) (n : ℕ) : ℝ :=
  if p ∣ n then 0 else ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2

/-- The squarefree weight of a multiple of `p` is the deleted weight. -/
theorem moebius_sq_prime_mul {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((ArithmeticFunction.moebius (p * a) : ℤ) : ℝ) ^ 2 = coprimeSquarefreeWeight p a := by
  rw [coprimeSquarefreeWeight, moebius_prime_mul hp]
  by_cases ha : p ∣ a
  · rw [if_pos ha, if_pos ha]
    norm_num
  · rw [if_neg ha, if_neg ha]
    ring

/-- The shared-prime sector count. -/
noncomputable def sharedSectorCount (x h : ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ (balancedPairs x h).filter (fun q => p ∣ q.1 ∧ p ∣ q.2),
    ((ArithmeticFunction.moebius q.1 : ℤ) : ℝ) ^ 2
      * ((ArithmeticFunction.moebius q.2 : ℤ) : ℝ) ^ 2

/-- **The shared-prime sector is a rescaled pair sum.**  Card equation `(9)`, before the limit. -/
theorem sharedSectorCount_eq_pairSum {x h : ℝ} (hx : 0 < x) {p : ℕ} (hp : p.Prime) :
    sharedSectorCount x h p
      = pairSum (coprimeSquarefreeWeight p) (x / (p : ℝ) ^ 2) (h / (p : ℝ)) := by
  classical
  have hp0 : 0 < p := hp.pos
  rw [sharedSectorCount, balancedPairs_shared_eq_image hx hp0]
  rw [Finset.sum_image]
  · rw [pairSum]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [moebius_sq_prime_mul hp, moebius_sq_prime_mul hp]
  · intro a _ b _ hab
    rw [Prod.ext_iff] at hab ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hp0 hab.1, Nat.eq_of_mul_eq_mul_left hp0 hab.2⟩

end RHTower.Sieve
