import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusAllMomentProfiles
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusSourceAlphabet
import Mathlib.LinearAlgebra.Lagrange

/-!
# Literal cofinal Möbius source-value frequencies

The exact finite source alphabet and arithmetic moment profiles determine each
literal value frequency on `(B+2)N`. Cardinal polynomials extract individual
levels, including zero. Their limiting masses form a symmetric probability law.
The quadratic radical decomposition is classical: de la Bretèche–Dress–Tenenbaum,
https://arxiv.org/abs/1902.09956, equations (2.7)–(2.9).
Strict positivity of all alphabet masses requires a separate arithmetic proof.
-/

open Filter Topology Finset Polynomial
open RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The cardinal polynomial for a source level, zero outside the exact alphabet. -/
def cofinalMobiusSourceCardinal (B : ℕ) (a : ℝ) : ℝ[X] := by
  classical
  exact if a ∈ moebiusLinearHorizonAlphabet (B + 1) then
    Lagrange.basis (moebiusLinearHorizonAlphabet (B + 1)) id a else 0

/-- Literal number of occurrences of a source level in the linear horizon. -/
def moebiusSourceLevelCount (B N : ℕ) (a : ℝ) : ℕ := by
  classical
  exact ((Icc 1 ((B + 2) * N)).filter (fun k => sieveSeq N moebiusReal k = a)).card

/-- An explicit finite arithmetic expression for each limiting source probability. -/
def cofinalMobiusSourceDensity (B : ℕ) (a : ℝ) : ℝ :=
  (∑ m ∈ (cofinalMobiusSourceCardinal B a).support,
    (cofinalMobiusSourceCardinal B a).coeff m * cofinalMobiusMomentProfile B m) /
      ((B + 2 : ℕ) : ℝ)

private theorem source_mem {B N k : ℕ} (hN : 1 ≤ N)
    (hk : k ∈ Icc 1 ((B + 2) * N)) :
    sieveSeq N moebiusReal k ∈ moebiusLinearHorizonAlphabet (B + 1) := by
  have hk1 := (mem_Icc.mp hk).1
  have hkM := (mem_Icc.mp hk).2
  have h := moebius_source_mem_linear_horizon_alphabet B ⟨N, by omega⟩
    ⟨k - 1, by simpa using (show k - 1 < (B + 2) * N by omega)⟩
  change sieveSeq N moebiusReal (k - 1 + 1) ∈ _ at h
  simpa only [Nat.sub_add_cancel hk1] using h

private theorem cardinal_eval {B : ℕ} (a x : ℝ)
    (hx : x ∈ moebiusLinearHorizonAlphabet (B + 1)) :
    (cofinalMobiusSourceCardinal B a).eval x = if x = a then 1 else 0 := by
  classical
  by_cases ha : a ∈ moebiusLinearHorizonAlphabet (B + 1)
  · simp only [cofinalMobiusSourceCardinal, if_pos ha]
    by_cases hxa : x = a
    · subst x
      simpa using Lagrange.eval_basis_self (v := (id : ℝ → ℝ))
        (fun _ _ _ _ h => h) ha
    · simpa [hxa] using
        Lagrange.eval_basis_of_ne (v := (id : ℝ → ℝ)) (Ne.symm hxa) hx
  · have hxa : x ≠ a := fun h => ha (h ▸ hx)
    simp [cofinalMobiusSourceCardinal, ha, hxa]

private theorem count_eq_cardinal_sum (B N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    (moebiusSourceLevelCount B N a : ℝ) =
      ∑ k ∈ Icc 1 ((B + 2) * N),
        (cofinalMobiusSourceCardinal B a).eval (sieveSeq N moebiusReal k) := by
  classical
  simp_rw [Finset.sum_congr rfl (fun k hk => cardinal_eval a _ (source_mem hN hk))]
  simp [moebiusSourceLevelCount, Finset.sum_boole]

private theorem polynomial_average (s : Finset ℕ) (f : ℕ → ℝ) (z : ℝ) (p : ℝ[X]) :
    (∑ k ∈ s, p.eval (f k)) / z =
      ∑ m ∈ p.support, p.coeff m *
        ((∑ k ∈ s, (f k) ^ m) / z) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.mul_sum]
  ring

private theorem tendsto_source_polynomial_mean (B : ℕ) (p : ℝ[X]) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((B + 2) * N), p.eval (sieveSeq N moebiusReal k)) / (N : ℝ))
      atTop (𝓝 (∑ m ∈ p.support, p.coeff m * cofinalMobiusMomentProfile B m)) := by
  simp_rw [polynomial_average]
  exact tendsto_finsetSum _ fun m _ =>
    (tendsto_sieveSeq_moment_linear_horizon B m).const_mul (p.coeff m)

/-- Every literal level frequency converges to its finite arithmetic expression. -/
theorem tendsto_moebiusSourceLevelFrequency (B : ℕ) (a : ℝ) :
    Tendsto (fun N : ℕ =>
      (moebiusSourceLevelCount B N a : ℝ) / (((B + 2) * N : ℕ) : ℝ))
      atTop (𝓝 (cofinalMobiusSourceDensity B a)) := by
  have h := (tendsto_source_polynomial_mean B (cofinalMobiusSourceCardinal B a)).div_const
    (((B + 2 : ℕ) : ℝ))
  change Tendsto _ _ (𝓝 (cofinalMobiusSourceDensity B a)) at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [count_eq_cardinal_sum B N a hN, Nat.cast_mul, div_div, mul_comm (N : ℝ)]

/-- The arithmetic source masses are nonnegative without extra analytic premises. -/
theorem cofinalMobiusSourceDensity_nonneg (B : ℕ) (a : ℝ) :
    0 ≤ cofinalMobiusSourceDensity B a := by
  exact ge_of_tendsto' (tendsto_moebiusSourceLevelFrequency B a) (fun _ => by positivity)

/-- All limiting mass is carried by the exact finite source alphabet. -/
theorem cofinalMobiusSourceDensity_support (B : ℕ) (a : ℝ) :
    cofinalMobiusSourceDensity B a = 0 ∨ a ∈ moebiusLinearHorizonAlphabet (B + 1) := by
  classical
  by_cases ha : a ∈ moebiusLinearHorizonAlphabet (B + 1)
  · exact Or.inr ha
  · exact Or.inl (by simp [cofinalMobiusSourceDensity, cofinalMobiusSourceCardinal, ha])

private theorem sum_level_counts (B N : ℕ) (hN : 1 ≤ N) :
    (∑ a ∈ moebiusLinearHorizonAlphabet (B + 1), moebiusSourceLevelCount B N a) =
      (B + 2) * N := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Icc 1 ((B + 2) * N)) (t := moebiusLinearHorizonAlphabet (B + 1))
    (f := fun k => sieveSeq N moebiusReal k) (fun _ hk => source_mem hN hk)
  simpa only [moebiusSourceLevelCount, Nat.card_Icc, Nat.add_sub_cancel] using h.symm

/-- The complete finite source law has total mass one. -/
theorem sum_cofinalMobiusSourceDensity (B : ℕ) :
    (∑ a ∈ moebiusLinearHorizonAlphabet (B + 1), cofinalMobiusSourceDensity B a) = 1 := by
  have h := tendsto_finsetSum (moebiusLinearHorizonAlphabet (B + 1))
    (fun a _ => tendsto_moebiusSourceLevelFrequency B a)
  have he : (fun N : ℕ => ∑ a ∈ moebiusLinearHorizonAlphabet (B + 1),
      (moebiusSourceLevelCount B N a : ℝ) / (((B + 2) * N : ℕ) : ℝ))
      =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_level_counts B N hN]
    have hM : (((B + 2) * N : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.mul_pos (show 0 < B + 2 by omega)
        (show 0 < N by omega)))
    exact div_self hM
  exact tendsto_nhds_unique (h.congr' he) tendsto_const_nhds

private theorem alphabet_neg {B : ℕ} (x : ℝ)
    (hx : x ∈ moebiusLinearHorizonAlphabet B) :
    -x ∈ moebiusLinearHorizonAlphabet B := by
  classical
  simp only [moebiusLinearHorizonAlphabet, mem_union, mem_singleton,
    mem_biUnion, mem_insert] at hx ⊢
  rcases hx with h | ⟨l, hl, d, hd, h | h⟩
  · exact Or.inl (by rw [h, neg_zero])
  · exact Or.inr ⟨l, hl, d, hd, Or.inr (by rw [h])⟩
  · exact Or.inr ⟨l, hl, d, hd, Or.inl (by rw [h, neg_neg])⟩

private theorem count_neg_eq_cardinal_sum (B N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    (moebiusSourceLevelCount B N (-a) : ℝ) =
      ∑ k ∈ Icc 1 ((B + 2) * N),
        (cofinalMobiusSourceCardinal B a).eval (-sieveSeq N moebiusReal k) := by
  classical
  rw [count_eq_cardinal_sum B N (-a) hN]
  apply Finset.sum_congr rfl
  intro k hk
  rw [cardinal_eval (-a) _ (source_mem hN hk),
    cardinal_eval a _ (alphabet_neg _ (source_mem hN hk))]
  by_cases hs : sieveSeq N moebiusReal k = -a
  · simp [hs]
  · have hn : -sieveSeq N moebiusReal k ≠ a := by
      intro h
      apply hs
      linarith
    simp [hs, hn]

private theorem neg_one_mul_moment_profile (B m : ℕ) :
    (-1 : ℝ) ^ m * cofinalMobiusMomentProfile B m = cofinalMobiusMomentProfile B m := by
  by_cases he : m % 2 = 0
  · have hm : m = 2 * (m / 2) := by omega
    have hsign : (-1 : ℝ) ^ m = 1 := by
      rw [hm, pow_mul]
      norm_num
    rw [hsign, one_mul]
  · have hm : m ≠ 0 := by omega
    simp [cofinalMobiusMomentProfile, hm, he]

private theorem tendsto_negative_source_polynomial_mean (B : ℕ) (p : ℝ[X]) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((B + 2) * N), p.eval (-sieveSeq N moebiusReal k)) / (N : ℝ))
      atTop (𝓝 (∑ m ∈ p.support, p.coeff m * cofinalMobiusMomentProfile B m)) := by
  have hneg (m : ℕ) : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((B + 2) * N), (-sieveSeq N moebiusReal k) ^ m) / (N : ℝ))
      atTop (𝓝 (cofinalMobiusMomentProfile B m)) := by
    have h := (tendsto_sieveSeq_moment_linear_horizon B m).const_mul ((-1 : ℝ) ^ m)
    rw [neg_one_mul_moment_profile] at h
    apply h.congr'
    filter_upwards [] with N
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Icc 1 ((B + 2) * N)) =>
      neg_pow (sieveSeq N moebiusReal k) m)]
    rw [← Finset.mul_sum]
    ring
  simp_rw [polynomial_average]
  exact tendsto_finsetSum _ fun m _ => (hneg m).const_mul (p.coeff m)

/-- Odd-moment cancellation gives exact symmetry of the complete source law. -/
theorem cofinalMobiusSourceDensity_neg (B : ℕ) (a : ℝ) :
    cofinalMobiusSourceDensity B (-a) = cofinalMobiusSourceDensity B a := by
  have h := (tendsto_negative_source_polynomial_mean B
    (cofinalMobiusSourceCardinal B a)).div_const (((B + 2 : ℕ) : ℝ))
  change Tendsto _ _ (𝓝 (cofinalMobiusSourceDensity B a)) at h
  have hneg : Tendsto (fun N : ℕ =>
      (moebiusSourceLevelCount B N (-a) : ℝ) / (((B + 2) * N : ℕ) : ℝ))
      atTop (𝓝 (cofinalMobiusSourceDensity B a)) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    rw [count_neg_eq_cardinal_sum B N a hN, Nat.cast_mul, div_div, mul_comm (N : ℝ)]
  exact tendsto_nhds_unique (tendsto_moebiusSourceLevelFrequency B (-a)) hneg

end
end GaloisForLFunctions.BezoutValuationIncidence
