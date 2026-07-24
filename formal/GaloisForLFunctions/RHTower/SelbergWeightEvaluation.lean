import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# Evaluation of the Selberg weight and the bilinear hyperbola regroup

Three pieces for Selberg's second inequality:

* `abs_selberg_weight_summatory`:
  `|∑_{k ≤ N} (Λ(k)log k + (Λ*Λ)(k)) − 2N·log N| ≤ 420·N` — the symmetry
  formula plus the Abel bounds on `∑ Λ·log`.
* `hyperbola_bilinear_regroup`: the two-weight hyperbola regrouping
  `∑_d g(d)·∑_m h(m)·F(⌊N/(dm)⌋) = ∑_k (∑_{ab=k} g(a)h(b))·F(⌊N/k⌋)`,
  which at `g = h = Λ` produces the `(Λ*Λ)`-weighted fiber sum.
* `psiRemainder_sub_ge`: `R(m) − R(n) ≥ −(m − n)` — slow variation of the
  remainder from monotonicity of `ψ`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Selberg weight evaluation**:
`|∑_{k≤N} (Λ(k)log k + (Λ*Λ)(k)) − 2N log N| ≤ 420N`. -/
theorem abs_selberg_weight_summatory (N : ℕ) (hN : 1 ≤ N) :
    |∑ k ∈ Finset.Icc 1 N,
        (vonMangoldt k * Real.log k + (vonMangoldt * vonMangoldt) k)
        - 2 * N * Real.log N| ≤ 420 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Finset.sum_add_distrib, sum_vonMangoldt_conv_eq]
  have hsym := abs_le.1 (selberg_symmetry_formula N hN)
  have habelu := sum_vonMangoldt_mul_log_le N
  have habell := le_sum_vonMangoldt_mul_log N hN
  rw [abs_le]
  constructor
  · nlinarith [hsym.1, habell]
  · nlinarith [hsym.2, habelu]

/-- **Bilinear hyperbola regrouping**: a two-weight double sum over the
hyperbola `dm ≤ N` regroups by the product into antidiagonal weights. -/
theorem hyperbola_bilinear_regroup (g h F : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, g d
        * ∑ m ∈ Finset.Icc 1 (N / d), h m * F (N / d / m)
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ p ∈ k.divisorsAntidiagonal, g p.1 * h p.2) * F (N / k) := by
  have hstep : ∀ d ∈ Finset.Icc 1 N,
      g d * ∑ m ∈ Finset.Icc 1 (N / d), h m * F (N / d / m)
        = ∑ m ∈ Finset.Icc 1 (N / d), g d * h m * F (N / (d * m)) := by
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.div_div_eq_div_mul]
    ring
  calc ∑ d ∈ Finset.Icc 1 N, g d
        * ∑ m ∈ Finset.Icc 1 (N / d), h m * F (N / d / m)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          g d * h m * F (N / (d * m)) :=
        Finset.sum_congr rfl hstep
    _ = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
          g x.1 * h x.2 * F (N / (x.1 * x.2)) :=
        Finset.sum_sigma' _ _ _
    _ = ∑ y ∈ (Finset.Icc 1 N).sigma (fun k => k.divisorsAntidiagonal),
          g y.2.1 * h y.2.2 * F (N / y.1) := by
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
            intro h0
            rw [h0, zero_mul] at hprod
            omega
          have hm0 : m ≠ 0 := by
            intro h0
            rw [h0, mul_zero] at hprod
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
          g p.1 * h p.2 * F (N / k) :=
        Finset.sum_sigma _ _ _
    _ = ∑ k ∈ Finset.Icc 1 N,
          (∑ p ∈ k.divisorsAntidiagonal, g p.1 * h p.2) * F (N / k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_mul]

/-- The antidiagonal weight at `g = h = Λ` is the convolution square. -/
theorem sum_antidiagonal_vonMangoldt_mul (k : ℕ) :
    ∑ p ∈ k.divisorsAntidiagonal, vonMangoldt p.1 * vonMangoldt p.2
      = (vonMangoldt * vonMangoldt) k :=
  (ArithmeticFunction.mul_apply).symm

/-- **Slow variation of the remainder**: `R(m) − R(n) ≥ −(m − n)`. -/
theorem psiRemainder_sub_ge {n m : ℕ} (h : n ≤ m) :
    -((m : ℝ) - n) ≤ psiRemainder m - psiRemainder n := by
  have hmono : chebyshevPsi n ≤ chebyshevPsi m :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl h)
      (fun _ _ _ => vonMangoldt_nonneg)
  simp only [psiRemainder]
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  linarith

end RHTower
