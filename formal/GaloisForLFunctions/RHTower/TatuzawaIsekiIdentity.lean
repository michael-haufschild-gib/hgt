import GaloisForLFunctions.RHTower.MoebiusFloorInversion

/-!
# The discrete Tatuzawa–Iseki identity

For any `F : ℕ → ℝ` and `N ≥ 1`, with `S(k) = ∑_{d ≤ k} F(⌊k/d⌋)`,

`∑_{n ≤ N} μ(n)·(log N − log n)·S(⌊N/n⌋)
   = F(N)·log N + ∑_{k ≤ N} Λ(k)·F(⌊N/k⌋)`,

an **exact** identity: the weight `log N − log n` splits into the `log N`
part, collapsed by `moebius_floor_inversion`, and the `log n` part, which
the hyperbola regrouping `hyperbola_weight_regroup` turns into the divisor
sums `∑_{a ∣ k} μ(a) log a = −Λ(k)`.  This is the engine that converts
elementary summatory estimates into Selberg's symmetry formula.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The floor-averaged summatory transform `S(k) = ∑_{d ≤ k} F(⌊k/d⌋)`. -/
def floorSummatory (F : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 k, F (k / d)

/-- **Weighted hyperbola regrouping**: a weighted double sum over the
hyperbola `dm ≤ N` regroups by the product `k = dm` into divisor-sum
weights.  The Möbius specialization is `moebius_floor_inversion`. -/
theorem hyperbola_weight_regroup (g F : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, g d * ∑ m ∈ Finset.Icc 1 (N / d), F (N / d / m)
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ p ∈ k.divisorsAntidiagonal, g p.1) * F (N / k) := by
  have hstep : ∀ d ∈ Finset.Icc 1 N,
      g d * ∑ m ∈ Finset.Icc 1 (N / d), F (N / d / m)
        = ∑ m ∈ Finset.Icc 1 (N / d), g d * F (N / (d * m)) := by
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.div_div_eq_div_mul]
  calc ∑ d ∈ Finset.Icc 1 N, g d
        * ∑ m ∈ Finset.Icc 1 (N / d), F (N / d / m)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          g d * F (N / (d * m)) :=
        Finset.sum_congr rfl hstep
    _ = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
          g x.1 * F (N / (x.1 * x.2)) :=
        Finset.sum_sigma' _ _ _
    _ = ∑ y ∈ (Finset.Icc 1 N).sigma (fun k => k.divisorsAntidiagonal),
          g y.2.1 * F (N / y.1) := by
        apply Finset.sum_nbij'
          (i := fun x => ⟨x.1 * x.2, (x.1, x.2)⟩)
          (j := fun y => ⟨y.2.1, y.2.2⟩)
        · rintro ⟨d, m⟩ hx
          rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hx
          dsimp only at hx
          obtain ⟨hd, hm⟩ := hx
          rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
          dsimp only
          refine ⟨⟨?_, ?_⟩, rfl, ?_⟩
          · exact Nat.one_le_iff_ne_zero.2
              (Nat.mul_ne_zero (by omega) (by omega))
          · calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d hm.2
              _ ≤ N := Nat.mul_div_le N d
          · exact Nat.mul_ne_zero (by omega) (by omega)
        · rintro ⟨k, d, m⟩ hy
          rw [Finset.mem_sigma, Finset.mem_Icc] at hy
          dsimp only at hy
          obtain ⟨hk, hdm⟩ := hy
          rw [Nat.mem_divisorsAntidiagonal] at hdm
          dsimp only at hdm
          obtain ⟨hprod, hk0⟩ := hdm
          rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
          dsimp only
          have hd0 : d ≠ 0 := by
            intro h
            rw [h, zero_mul] at hprod
            omega
          have hm0 : m ≠ 0 := by
            intro h
            rw [h, mul_zero] at hprod
            omega
          refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
          · calc d ≤ d * m := Nat.le_mul_of_pos_right d (by omega)
              _ = k := hprod
              _ ≤ N := hk.2
          · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
            calc m * d = k := by rw [mul_comm]; exact hprod
              _ ≤ N := hk.2
        · rintro ⟨d, m⟩ _
          rfl
        · rintro ⟨k, d, m⟩ hy
          rw [Finset.mem_sigma] at hy
          obtain ⟨-, hdm⟩ := hy
          rw [Nat.mem_divisorsAntidiagonal] at hdm
          obtain ⟨hprod, -⟩ := hdm
          dsimp only at hprod ⊢
          subst hprod
          rfl
        · rintro ⟨d, m⟩ _
          rfl
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ p ∈ k.divisorsAntidiagonal,
          g p.1 * F (N / k) :=
        Finset.sum_sigma _ _ _
    _ = ∑ k ∈ Finset.Icc 1 N,
          (∑ p ∈ k.divisorsAntidiagonal, g p.1) * F (N / k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_mul]

/-- The antidiagonal form of `∑_{d ∣ k} μ(d) log d = −Λ(k)`. -/
theorem sum_divisorsAntidiagonal_moebius_mul_log (k : ℕ) :
    ∑ p ∈ k.divisorsAntidiagonal, ((moebius p.1 : ℤ) : ℝ) * Real.log p.1
      = -vonMangoldt k := by
  rw [Nat.sum_divisorsAntidiagonal
    (fun d _ => ((moebius d : ℤ) : ℝ) * Real.log d) (n := k)]
  exact ArithmeticFunction.sum_moebius_mul_log_eq

/-- **Discrete Tatuzawa–Iseki identity** (exact, no error term):
`∑_{n ≤ N} μ(n)(log N − log n)·S(⌊N/n⌋) = F(N)log N + ∑_{k ≤ N} Λ(k)F(⌊N/k⌋)`. -/
theorem tatuzawa_iseki (F : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ)
        * (Real.log N - Real.log n) * floorSummatory F (N / n)
      = F N * Real.log N
        + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * F (N / k) := by
  have hsplit : ∀ n ∈ Finset.Icc 1 N,
      ((moebius n : ℤ) : ℝ) * (Real.log N - Real.log n)
          * floorSummatory F (N / n)
        = Real.log N * (((moebius n : ℤ) : ℝ) * floorSummatory F (N / n))
          - (((moebius n : ℤ) : ℝ) * Real.log n)
            * floorSummatory F (N / n) := by
    intro n _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ n ∈ Finset.Icc 1 N,
      ((moebius n : ℤ) : ℝ) * floorSummatory F (N / n) = F N := by
    simp only [floorSummatory]
    exact moebius_floor_inversion F N hN
  have h2 : ∑ n ∈ Finset.Icc 1 N,
      (((moebius n : ℤ) : ℝ) * Real.log n) * floorSummatory F (N / n)
        = ∑ k ∈ Finset.Icc 1 N, (-vonMangoldt k) * F (N / k) := by
    simp only [floorSummatory]
    rw [hyperbola_weight_regroup
      (fun n => ((moebius n : ℤ) : ℝ) * Real.log n) F N]
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_divisorsAntidiagonal_moebius_mul_log]
  rw [h1, h2]
  have hneg : ∑ k ∈ Finset.Icc 1 N, (-vonMangoldt k) * F (N / k)
      = -∑ k ∈ Finset.Icc 1 N, vonMangoldt k * F (N / k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hneg]
  ring

end RHTower
