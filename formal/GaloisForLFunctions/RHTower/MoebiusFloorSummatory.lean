import GaloisForLFunctions.RHTower.DirichletSummatorySwap

/-!
# Möbius floor summatory and the bounded Möbius harmonic sum

Two classical partial-sum facts for the Möbius function:

* `moebius_floor_summatory`: `∑_{d ≤ N} μ(d)·⌊N/d⌋ = 1` — the summatory
  form of `μ * ζ = 1`, obtained from the hyperbola swap
  `sum_Icc_mul_apply`.
* `abs_sum_moebius_div_le_one`: `|∑_{d ≤ N} μ(d)/d| ≤ 1` — multiplying the
  harmonic Möbius sum by `N` and splitting `N/d` into floor and remainder
  leaves the floor mass `1` plus a remainder sum whose `d`-th term is at
  most `1 − 1/d`; the harmonic term at `d = 1` absorbs the excess.

The rational harmonic-weighted analogue is
`harmonicFloorMoebiusSum_eq_one` (`Mollifier.lean`); the bound here is the
real unweighted form consumed by the μ-weighted hyperbola assembly of
Selberg's symmetry formula.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Möbius floor summatory**: `∑_{d ≤ N} μ(d)·⌊N/d⌋ = 1`. -/
theorem moebius_floor_summatory (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * ((N / d : ℕ) : ℝ) = 1 := by
  have hswap := sum_Icc_mul_apply
    ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
    ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) N
  rw [coe_moebius_mul_coe_zeta] at hswap
  have hone : ∑ n ∈ Finset.Icc 1 N, (1 : ArithmeticFunction ℝ) n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb1
      simp [hb1]
    · intro h
      simp only [Finset.mem_Icc] at h
      omega
  have hzeta : ∀ k : ℕ, ∑ m ∈ Finset.Icc 1 k,
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) m = (k : ℝ) := by
    intro k
    have h1 : ∀ m ∈ Finset.Icc 1 k,
        ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) m = (1 : ℝ) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [natCoe_apply, zeta_apply, if_neg (by omega)]
      norm_num
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Icc]
    simp
  rw [hone] at hswap
  calc ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * ((N / d : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) d
            * ∑ m ∈ Finset.Icc 1 (N / d),
              ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) m := by
        apply Finset.sum_congr rfl
        intro d _
        rw [intCoe_apply, hzeta]
    _ = 1 := hswap.symm

/-- **Bounded Möbius harmonic sum**: `|∑_{d ≤ N} μ(d)/d| ≤ 1`. -/
theorem abs_sum_moebius_div_le_one (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / d| ≤ 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- split `N·(μ(d)/d)` into floor and remainder parts
  have hterm_eq : ∀ d ∈ Finset.Icc 1 N,
      (N : ℝ) * (((moebius d : ℤ) : ℝ) / d)
        = ((moebius d : ℤ) : ℝ) * ((N / d : ℕ) : ℝ)
          + ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hkey : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N d
    have hsplit : (N : ℝ) / d = ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) / d := by
      rw [← hkey, add_div, mul_div_cancel_left₀ _ hd0.ne']
    calc (N : ℝ) * (((moebius d : ℤ) : ℝ) / d)
        = ((moebius d : ℤ) : ℝ) * ((N : ℝ) / d) := by ring
      _ = ((moebius d : ℤ) : ℝ)
          * (((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) / d) := by rw [hsplit]
      _ = ((moebius d : ℤ) : ℝ) * ((N / d : ℕ) : ℝ)
          + ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d := by ring
  -- remainder sum is at most `N − 1`
  have hE : |∑ d ∈ Finset.Icc 1 N,
      ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d| ≤ (N : ℝ) - 1 := by
    have hterm : ∀ d ∈ Finset.Icc 1 N,
        |((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d|
          ≤ 1 - 1 / (d : ℝ) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hmod : ((N % d : ℕ) : ℝ) ≤ (d : ℝ) - 1 := by
        have h1 : N % d + 1 ≤ d := Nat.mod_lt N (by omega)
        have h2 : ((N % d : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast h1
        linarith
      have hμ : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast abs_moebius_le_one
      calc |((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d|
          = |((moebius d : ℤ) : ℝ)| * (((N % d : ℕ) : ℝ) / d) := by
            rw [abs_div, abs_mul,
              abs_of_nonneg (a := ((N % d : ℕ) : ℝ)) (Nat.cast_nonneg _),
              abs_of_pos hd0, mul_div_assoc]
        _ ≤ 1 * (((d : ℝ) - 1) / d) := by
            apply mul_le_mul hμ _ (by positivity) zero_le_one
            gcongr
        _ = 1 - 1 / (d : ℝ) := by
            rw [one_mul, sub_div, div_self hd0.ne']
    have hharm : (1 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
      have hmem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
      have := Finset.single_le_sum
        (f := fun d : ℕ => 1 / (d : ℝ))
        (fun d _ => by positivity) hmem
      simpa using this
    have hcard : (Finset.Icc 1 N).card = N := by
      rw [Nat.card_Icc]
      omega
    calc |∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d|
        ≤ ∑ d ∈ Finset.Icc 1 N,
          |((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (1 - 1 / (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) - ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
          simp
      _ ≤ (N : ℝ) - 1 := by linarith
  -- assemble: `N·S = 1 + E`, so `N·|S| ≤ N`
  have hprod : (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / d
      = 1 + ∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm_eq,
      Finset.sum_add_distrib, moebius_floor_summatory N hN]
  have habs : (N : ℝ) * |∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / d|
      ≤ (N : ℝ) * 1 := by
    rw [mul_one]
    calc (N : ℝ) * |∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / d|
        = |(N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / d| := by
          rw [abs_mul, abs_of_pos hNR]
      _ = |1 + ∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d| := by rw [hprod]
      _ ≤ |(1 : ℝ)| + |∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ) * ((N % d : ℕ) : ℝ) / d| := abs_add_le _ _
      _ ≤ 1 + ((N : ℝ) - 1) := by
          rw [abs_one]
          linarith
      _ = (N : ℝ) := by ring
  exact le_of_mul_le_mul_left habs hNR
end RHTower
