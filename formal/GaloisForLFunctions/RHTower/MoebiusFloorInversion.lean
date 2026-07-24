import GaloisForLFunctions.RHTower.Mollifier

/-!
# Floor-sum Möbius inversion

For any `F : ℕ → ℝ` and `N ≥ 1`,

`∑_{d ≤ N} μ(d) · ∑_{m ≤ ⌊N/d⌋} F(⌊N/(dm)⌋) = F(N)`:

expanding the double sum over the hyperbola `dm ≤ N` and grouping by the
product `n = dm` leaves `F(⌊N/n⌋)` weighted by the Möbius cancellation
`∑_{d ∣ n} μ(d) = [n = 1]`, so only the term `n = 1` survives.  This is
the inversion engine of the Tatuzawa–Iseki identity: it recovers a
summatory function from its floor-averaged transform, generalizing
`moebius_floor_summatory` (the case `F = 1`).
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Floor-sum Möbius inversion**: grouping the Möbius-weighted hyperbola
sum by products collapses it to `F(N)`. -/
theorem moebius_floor_inversion (F : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ)
        * ∑ m ∈ Finset.Icc 1 (N / d), F (N / d / m) = F N := by
  have hstep : ∀ d ∈ Finset.Icc 1 N,
      ((moebius d : ℤ) : ℝ) * ∑ m ∈ Finset.Icc 1 (N / d), F (N / d / m)
        = ∑ m ∈ Finset.Icc 1 (N / d),
            ((moebius d : ℤ) : ℝ) * F (N / (d * m)) := by
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.div_div_eq_div_mul]
  calc ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ)
        * ∑ m ∈ Finset.Icc 1 (N / d), F (N / d / m)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          ((moebius d : ℤ) : ℝ) * F (N / (d * m)) :=
        Finset.sum_congr rfl hstep
    _ = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
          ((moebius x.1 : ℤ) : ℝ) * F (N / (x.1 * x.2)) :=
        Finset.sum_sigma' _ _ _
    _ = ∑ y ∈ (Finset.Icc 1 N).sigma (fun n => n.divisorsAntidiagonal),
          ((moebius y.2.1 : ℤ) : ℝ) * F (N / y.1) := by
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
        · rintro ⟨n, d, m⟩ hy
          rw [Finset.mem_sigma, Finset.mem_Icc] at hy
          dsimp only at hy
          obtain ⟨hn, hdm⟩ := hy
          rw [Nat.mem_divisorsAntidiagonal] at hdm
          dsimp only at hdm
          obtain ⟨hprod, hn0⟩ := hdm
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
              _ = n := hprod
              _ ≤ N := hn.2
          · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
            calc m * d = n := by rw [mul_comm]; exact hprod
              _ ≤ N := hn.2
        · rintro ⟨d, m⟩ _
          rfl
        · rintro ⟨n, d, m⟩ hy
          rw [Finset.mem_sigma] at hy
          obtain ⟨-, hdm⟩ := hy
          rw [Nat.mem_divisorsAntidiagonal] at hdm
          obtain ⟨hprod, -⟩ := hdm
          dsimp only at hprod ⊢
          subst hprod
          rfl
        · rintro ⟨d, m⟩ _
          rfl
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
          ((moebius p.1 : ℤ) : ℝ) * F (N / n) :=
        Finset.sum_sigma _ _ _
    _ = ∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℝ) else 0) * F (N / n) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← Finset.sum_mul]
        congr 1
        rw [Nat.sum_divisorsAntidiagonal
          (fun d _ => ((moebius d : ℤ) : ℝ)) (n := n)]
        have h := sum_moebius_divisors n
        by_cases hn1 : n = 1
        · rw [if_pos hn1]
          rw [if_pos hn1] at h
          exact_mod_cast h
        · rw [if_neg hn1]
          rw [if_neg hn1] at h
          exact_mod_cast h
    _ = F N := by
        rw [Finset.sum_eq_single 1]
        · rw [if_pos rfl, one_mul, Nat.div_one]
        · intro b _ hb1
          rw [if_neg hb1, zero_mul]
        · intro h
          exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hN⟩) h

end RHTower
