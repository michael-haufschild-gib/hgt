import GaloisForLFunctions.RHTower.DirichletLogDerivation

/-!
# Summatory swap for Dirichlet convolutions

The finite hyperbola identity

`∑_{n ≤ N} (f * g)(n) = ∑_{d ≤ N} f(d) · ∑_{m ≤ N/d} g(m)`:

summing a Dirichlet convolution counts the lattice points under the
hyperbola `d·m ≤ N` once for each factorization.  This generalizes the
von Mangoldt count `∑_{m ≤ n} log m = ∑_{d ≤ n} Λ(d)⌊n/d⌋` and the
reciprocal-kernel swap of the mollifier normalization, and drives all
summatory consequences of Selberg's identity.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Summatory swap**: the partial sum of a Dirichlet convolution is the
hyperbola pairing of one factor against the floor-cut partial sums of the
other. -/
theorem sum_Icc_mul_apply {R : Type*} [Semiring R] (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (f * g) n
      = ∑ d ∈ Finset.Icc 1 N, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m := by
  have hexpand : ∑ n ∈ Finset.Icc 1 N, (f * g) n
      = ∑ x ∈ (Finset.Icc 1 N).sigma
          (fun n => n.divisorsAntidiagonal), f x.2.1 * g x.2.2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n _
    rw [ArithmeticFunction.mul_apply]
  have hcollapse : ∑ d ∈ Finset.Icc 1 N, f d * ∑ m ∈ Finset.Icc 1 (N / d), g m
      = ∑ x ∈ (Finset.Icc 1 N).sigma
          (fun d => Finset.Icc 1 (N / d)), f x.1 * g x.2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  rw [hexpand, hcollapse]
  apply Finset.sum_nbij'
    (i := fun x => ⟨x.2.1, x.2.2⟩)
    (j := fun y => ⟨y.1 * y.2, (y.1, y.2)⟩)
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hn, hdm⟩ := hx
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, hn0⟩ := hdm
    dsimp only at hprod hn0 hn ⊢
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
  · rintro ⟨d, m⟩ hy
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hy
    obtain ⟨hd, hm⟩ := hy
    dsimp only at hd hm ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    dsimp only
    have hdm : d * m ≤ N := by
      calc d * m ≤ d * (N / d) :=
            Nat.mul_le_mul_left d hm.2
        _ ≤ N := Nat.mul_div_le N d
    have hne : d * m ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    refine ⟨⟨by omega, hdm⟩, rfl, hne⟩
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, hdm⟩ := hx
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, -⟩ := hdm
    dsimp only at hprod ⊢
    subst hprod
    rfl
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨n, d, m⟩ _
    rfl

end RHTower
