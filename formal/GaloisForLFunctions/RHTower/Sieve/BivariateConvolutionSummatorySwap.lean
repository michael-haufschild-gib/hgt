import GaloisForLFunctions.RHTower.Sieve.BivariateMultiplicative

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private theorem sum_divisor_subtype_eq_sum {M : Type*} [AddCommMonoid M]
    (s : Finset ℕ) (f : ℕ → M) :
    (∑ x : {x // x ∈ s}, f x.1) = ∑ x ∈ s, f x := by
  change (∑ x ∈ s.attach, f x.1) = _
  exact Finset.sum_attach s f

/-- Reindex a positive summatory divisor-antidiagonal by its two factors. -/
theorem sum_Icc_divisorsAntidiagonal_swap
    {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  rw [← Finset.sum_sigma (Finset.Icc 1 N)
      (fun n => n.divisorsAntidiagonal)
      (fun x => F x.2.1 x.2.2),
    ← Finset.sum_sigma (Finset.Icc 1 N)
      (fun a => Finset.Icc 1 (N / a))
      (fun x => F x.1 x.2)]
  apply Finset.sum_nbij'
    (i := fun x => ⟨x.2.1, x.2.2⟩)
    (j := fun y => ⟨y.1 * y.2, (y.1, y.2)⟩)
  · rintro ⟨n, a, b⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hn, hab⟩ := hx
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_divisorsAntidiagonal] at hab
    obtain ⟨hprod, hn0⟩ := hab
    dsimp only at hprod hn0 hn ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, zero_mul] at hprod
      omega
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, mul_zero] at hprod
      omega
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · calc
        a ≤ a * b := Nat.le_mul_of_pos_right a (by omega)
        _ = n := hprod
        _ ≤ N := hn.2
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < a)]
      calc
        b * a = n := by rw [mul_comm]; exact hprod
        _ ≤ N := hn.2
  · rintro ⟨a, b⟩ hy
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hy
    obtain ⟨ha, hb⟩ := hy
    dsimp only at ha hb ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    dsimp only
    have hab : a * b ≤ N := by
      calc
        a * b ≤ a * (N / a) := Nat.mul_le_mul_left a hb.2
        _ ≤ N := Nat.mul_div_le N a
    exact ⟨⟨Nat.mul_pos ha.1 hb.1, hab⟩, rfl,
      Nat.mul_ne_zero (Nat.ne_of_gt (by omega)) (Nat.ne_of_gt (by omega))⟩
  · rintro ⟨n, a, b⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, hab⟩ := hx
    rw [Nat.mem_divisorsAntidiagonal] at hab
    obtain ⟨hprod, -⟩ := hab
    dsimp only at hprod ⊢
    subst hprod
    rfl
  · rintro ⟨a, b⟩ _
    rfl
  · rintro ⟨n, a, b⟩ _
    rfl

theorem bivariateDirichletConvolution_eq_sum_divisorsAntidiagonal
    (f g : ℕ → ℕ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    bivariateDirichletConvolution f g m n =
      ∑ x ∈ m.divisorsAntidiagonal,
        ∑ y ∈ n.divisorsAntidiagonal,
          f x.1 y.1 * g x.2 y.2 := by
  rw [bivariateDirichletConvolution, if_neg (by omega), Fintype.sum_prod_type]
  change (∑ a : {a // a ∈ m.divisors},
      ∑ b : {b // b ∈ n.divisors},
        f a.1 b.1 * g (m / a.1) (n / b.1)) = _
  rw [sum_divisor_subtype_eq_sum m.divisors
    (fun a => ∑ b : {b // b ∈ n.divisors},
      f a b.1 * g (m / a) (n / b.1))]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a r => ∑ y ∈ n.divisorsAntidiagonal, f a y.1 * g r y.2)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_divisor_subtype_eq_sum n.divisors
    (fun b => f a b * g (m / a) (n / b))]
  rw [Nat.sum_divisorsAntidiagonal
    (fun b s => f a b * g (m / a) s)]

/-- Weighted bivariate hyperbola swap for product-divisor convolution. -/
theorem sum_Icc_bivariateDirichletConvolution_mul
    (f g : ℕ → ℕ → ℝ) (W : ℕ → ℕ → ℝ) (X Y : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
        bivariateDirichletConvolution f g m n * W m n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 Y,
        f a b *
          (∑ r ∈ Finset.Icc 1 (X / a), ∑ s ∈ Finset.Icc 1 (Y / b),
            g r s * W (a * r) (b * s)) := by
  have hexpand :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
          bivariateDirichletConvolution f g m n * W m n) =
        ∑ m ∈ Finset.Icc 1 X, ∑ x ∈ m.divisorsAntidiagonal,
          ∑ n ∈ Finset.Icc 1 Y, ∑ y ∈ n.divisorsAntidiagonal,
            f x.1 y.1 * g x.2 y.2 * W m n := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [bivariateDirichletConvolution_eq_sum_divisorsAntidiagonal f g
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_mul]
    
  rw [hexpand]
  have hinner : ∀ m ∈ Finset.Icc 1 X,
      (∑ x ∈ m.divisorsAntidiagonal,
        ∑ n ∈ Finset.Icc 1 Y, ∑ y ∈ n.divisorsAntidiagonal,
          f x.1 y.1 * g x.2 y.2 * W m n) =
      ∑ x ∈ m.divisorsAntidiagonal,
        ∑ b ∈ Finset.Icc 1 Y, ∑ s ∈ Finset.Icc 1 (Y / b),
          f x.1 b * g x.2 s * W m (b * s) := by
    intro m hm
    apply Finset.sum_congr rfl
    intro x hx
    calc
      (∑ n ∈ Finset.Icc 1 Y, ∑ y ∈ n.divisorsAntidiagonal,
          f x.1 y.1 * g x.2 y.2 * W m n) =
          ∑ n ∈ Finset.Icc 1 Y, ∑ y ∈ n.divisorsAntidiagonal,
            f x.1 y.1 * g x.2 y.2 * W m (y.1 * y.2) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro y hy
        rw [(Nat.mem_divisorsAntidiagonal.mp hy).1]
      _ = _ := sum_Icc_divisorsAntidiagonal_swap
        (fun b s => f x.1 b * g x.2 s * W m (b * s)) Y
  rw [Finset.sum_congr rfl hinner]
  calc
    (∑ m ∈ Finset.Icc 1 X, ∑ x ∈ m.divisorsAntidiagonal,
        ∑ b ∈ Finset.Icc 1 Y, ∑ s ∈ Finset.Icc 1 (Y / b),
          f x.1 b * g x.2 s * W m (b * s)) =
        ∑ m ∈ Finset.Icc 1 X, ∑ x ∈ m.divisorsAntidiagonal,
          ∑ b ∈ Finset.Icc 1 Y, ∑ s ∈ Finset.Icc 1 (Y / b),
            f x.1 b * g x.2 s * W (x.1 * x.2) (b * s) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 (X / a),
          ∑ b ∈ Finset.Icc 1 Y, ∑ s ∈ Finset.Icc 1 (Y / b),
            f a b * g r s * W (a * r) (b * s) :=
      sum_Icc_divisorsAntidiagonal_swap
        (fun a r => ∑ b ∈ Finset.Icc 1 Y, ∑ s ∈ Finset.Icc 1 (Y / b),
          f a b * g r s * W (a * r) (b * s)) X
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring

end

end RHTower.Sieve
