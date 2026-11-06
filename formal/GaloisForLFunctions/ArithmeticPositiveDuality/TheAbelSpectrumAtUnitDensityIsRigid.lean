import GaloisForLFunctions.HTGeometry.HamburgerIntegralMassRigidity

/-!
# The unit Abel spectrum forces the integers

A positive discrete spectrum with unit atom masses and the same Abel cosine limits as its
support is the positive-integer spectrum. The conclusion uses only the radial limits; a
holomorphic defect with vanishing radial residues does not affect it.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry.FreqHamburger

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Saturation of the cosine bound at every atom forces all frequencies onto the integer lattice;
the zero limits at missing frequencies then fill the lattice. -/
theorem integer_spectrum_of_unit_abel_limits {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hunit : ∀ n, a n = 1) (ha : Summable fun n => a n / lam n ^ 2)
    (hC0 : Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))))
    (hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))))
    (hgap : ∀ τ c : ℝ, 0 < τ → 0 < c → (∀ n, c * lam n ≤ |lam n - τ|) →
      Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 0)) :
    ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => by rw [hunit n]; norm_num
  have hπ2 : 0 < 1 / (2 * Real.pi) := by positivity
  -- integral frequencies
  have hint : ∀ m, ∃ K : ℕ, lam m = K := by
    intro m
    set K : ℕ := ⌊lam m⌋₊ with hK
    set f : ℝ := lam m - K with hf
    have hf0 : 0 ≤ f := by rw [hf, hK]; linarith [Nat.floor_le (hpos m).le]
    have hf1 : f < 1 := by rw [hf, hK]; linarith [Nat.lt_floor_add_one (lam m)]
    refine ⟨K, ?_⟩
    by_contra hne
    have hfpos : 0 < f := lt_of_le_of_ne hf0 (fun h => hne (by rw [hf] at h; linarith))
    -- `C_f → 0` since `f ∈ (0, 1)` is no atom
    have hCf : Tendsto (abelCos a lam f) (𝓝[>] 0) (𝓝 0) := by
      refine hgap f (1 - f) hfpos (by linarith) fun n => ?_
      rw [abs_of_pos (by linarith [hlam n])]
      nlinarith [hlam n]
    -- `C_0 - C_f ≤ 2(C_0 - C_{λ_m}) + 2K²(C_0 - C_{λ_0})`
    have hbound : ∀ ε, 0 < ε → abelCos a lam 0 ε - abelCos a lam f ε ≤
        2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε) +
          2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε) := by
      intro ε hε
      rw [abelCos_zero_sub hlam ha0 ha f hε, abelCos_zero_sub hlam ha0 ha (lam m) hε,
        abelCos_zero_sub hlam ha0 ha (lam 0) hε]
      have sm := summable_abelGap hlam ha0 ha (lam m) hε
      have s1 := summable_abelGap hlam ha0 ha (lam 0) hε
      have hsum : 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
          2 * (K : ℝ) ^ 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam 0))) =
          ∑' n, (2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
            2 * (K : ℝ) ^ 2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
              (1 - Real.cos (2 * Real.pi * lam n * lam 0)))) := by
        rw [(sm.mul_left 2).tsum_add (s1.mul_left _), tsum_mul_left, tsum_mul_left]
      have hle : ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * f)) ≤
          2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
          2 * (K : ℝ) ^ 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam 0))) := by
        rw [hsum]
        refine (summable_abelGap hlam ha0 ha f hε).tsum_le_tsum (fun n => ?_)
          ((sm.mul_left 2).add (s1.mul_left _))
        have hw := mul_nonneg (ha0 n) (Real.exp_pos (-(2 * Real.pi * lam n * ε))).le
        have htrig := one_sub_cos_frac_le (2 * Real.pi * lam n) (lam m) K
        rw [hlam0, mul_one]
        have e1 : 2 * Real.pi * lam n * f = 2 * Real.pi * lam n * (lam m - K) := by rw [hf]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left htrig hw]
      nlinarith [hle, hε.le]
    -- limits: the right side tends to `0`, so `C_f → 1/(2π)`
    have hR : Tendsto (fun ε => 2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε) +
        2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε => 2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε)) (𝓝[>] 0)
          (𝓝 0) := by
        have := (hC0.sub (hatom m)).const_mul 2
        rwa [hunit m, sub_self, mul_zero] at this
      have h2 : Tendsto (fun ε => 2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε))
          (𝓝[>] 0) (𝓝 0) := by
        have := (hC0.sub (hatom 0)).const_mul (2 * (K : ℝ) ^ 2)
        rwa [hunit 0, sub_self, mul_zero] at this
      simpa using h1.add h2
    have hlow : Tendsto (fun ε => abelCos a lam 0 ε - (2 * (abelCos a lam 0 ε -
        abelCos a lam (lam m) ε) + 2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε -
          abelCos a lam (lam 0) ε))) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      simpa using hC0.sub hR
    have hge : 1 / (2 * Real.pi) ≤ 0 := by
      refine le_of_tendsto_of_tendsto hlow hCf ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have := hbound ε hε
      linarith
    linarith
  -- every positive integer is a frequency
  have hsurj : ∀ k : ℕ, 1 ≤ k → ∃ n, lam n = k := by
    intro k hk
    by_contra hnone
    push Not at hnone
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    -- all frequencies are integers different from `k`
    have hsep : ∀ n, 1 / (2 * k) * lam n ≤ |lam n - k| := by
      intro n
      obtain ⟨K, hKn⟩ := hint n
      have hne : K ≠ k := fun h => hnone n (by rw [hKn, h])
      have hdist : 1 ≤ |lam n - k| := by
        rw [hKn]
        rcases lt_or_gt_of_ne hne with h | h
        · have : (K : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (k : ℝ) + 1 ≤ K := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rcases le_or_gt (lam n) (2 * k) with h | h
      · calc 1 / (2 * k) * lam n ≤ 1 / (2 * k) * (2 * k) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 1 := by field_simp
          _ ≤ |lam n - k| := hdist
      · rw [abs_of_pos (by linarith)]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have : 1 / (2 * (k : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        nlinarith [hpos n]
    have hCk := hgap k (1 / (2 * k)) hk0 (by positivity) hsep
    have heq : ∀ ε, abelCos a lam k ε = abelCos a lam 0 ε := by
      intro ε
      unfold abelCos
      congr 1
      refine tsum_congr fun n => ?_
      obtain ⟨K, hKn⟩ := hint n
      have : Real.cos (2 * Real.pi * lam n * k) = 1 := by
        rw [hKn, show 2 * Real.pi * (K : ℝ) * k = ((K * k : ℕ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        exact Real.cos_nat_mul_two_pi _
      rw [this]; simp
    have : Tendsto (abelCos a lam k) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      rw [show abelCos a lam k = abelCos a lam 0 from funext heq]; exact hC0
    have := tendsto_nhds_unique this hCk
    linarith
  -- strict monotonicity pins `λ_n = n + 1`
  have hval : ∀ n, lam n = n + 1 := by
    intro n
    induction n with
    | zero => simp [hlam0]
    | succ n ih =>
      obtain ⟨K, hK⟩ := hint (n + 1)
      have hlt : lam n < lam (n + 1) := hmono (Nat.lt_succ_self n)
      have hKge : n + 2 ≤ K := by
        rw [ih, hK] at hlt
        have : (n : ℝ) + 1 < K := by linarith
        exact_mod_cast (show n + 1 < K by exact_mod_cast this)
      obtain ⟨m, hm⟩ := hsurj (n + 2) (by omega)
      have hmn : n + 1 ≤ m := by
        by_contra h
        push Not at h
        have : lam m ≤ lam n := hmono.monotone (by omega)
        rw [hm, ih] at this
        push_cast at this
        linarith
      have hle : lam (n + 1) ≤ lam m := hmono.monotone hmn
      rw [hK, hm] at hle
      have hKle : K ≤ n + 2 := by exact_mod_cast hle
      rw [hK]
      push_cast
      have : K = n + 2 := le_antisymm hKle hKge
      rw [this]; push_cast; ring
  exact fun n => ⟨hval n, hunit n⟩

end GaloisForLFunctions.ArithmeticPositiveDuality
