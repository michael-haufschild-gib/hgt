import GaloisForLFunctions.BezoutValuationIncidence.SharpInitialPrefixObservabilityAndExactGramDeterminants

/-!
# Exact common-return windows and their two-moment kernel

The prefix discrepancy reflects about a common return with defect `H - Σ c`.
Consequently its complete window kernel consists of the initial-prefix kernel
and one additional scalar condition. Positive left/right radii impose both the
harmonic and raw tail moments. A centered window of `2N-3` samples detects every
nonconstant weight; the adjacent `2N-4` window has exactly the normalized final
second-difference direction. All statements concern the actual discrepancy.

The sharp horizon at arbitrary phases remains open. The factorial anchor supplies
divisibility and room for the left radius for every natural parameter, including
empty levels. No mean-zero premise or asymptotic cancellation is asserted.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-- The scalar defect in reflection about a common return. -/
def sieveReflectionDefect (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  finiteHarmonicSum N c - ∑ d ∈ Finset.Icc 1 N, c d

/-- An unconditional common return with room for the prescribed left radius. -/
def sieveReturnAnchor (N a k : ℕ) : ℕ := (k + a + 1) * N.factorial

/-- Vanishing on the actual consecutive interval around the common return. -/
def sieveReturnWindowZero (N a b k : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ M ∈ Finset.Icc (sieveReturnAnchor N a k - a) (sieveReturnAnchor N a k + b),
    sievePrefixDiscrepancy N M c = 0

private theorem return_anchor_ge (N a k : ℕ) : a ≤ sieveReturnAnchor N a k := by
  have h := Nat.le_mul_of_pos_right (k + a + 1) (Nat.factorial_pos N)
  unfold sieveReturnAnchor
  omega

private theorem return_anchor_dvd (N a k d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    d ∣ sieveReturnAnchor N a k := by
  exact dvd_mul_of_dvd_right
    (Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2) _

private theorem return_residue (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c =
      -(∑ d ∈ Finset.Icc 1 N, c d * ((M % d : ℕ) : ℝ) / (d : ℝ)) := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievedFractSum_eq_residueCombination, DeletionPeriodCovariance.residueCombination]

private theorem return_translate (N P t : ℕ) (c : ℕ → ℝ)
    (hP : ∀ d ∈ Finset.Icc 1 N, d ∣ P) :
    sievePrefixDiscrepancy N (P + t) c = sievePrefixDiscrepancy N t c := by
  rw [return_residue, return_residue]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hP d hd), zero_add, Nat.mod_mod]

private theorem return_reflect (N P t : ℕ) (c : ℕ → ℝ) (ht : t < P)
    (hP : ∀ d ∈ Finset.Icc 1 N, d ∣ P) :
    sievePrefixDiscrepancy N (P - (t + 1)) c =
      sieveReflectionDefect N c - sievePrefixDiscrepancy N t c := by
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      -(c d * (((P - (t + 1)) % d : ℕ) : ℝ) / (d : ℝ)) =
        c d / (d : ℝ) - c d + c d * ((t % d : ℕ) : ℝ) / (d : ℝ) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hmod : (P - (t + 1)) % d = d - (t % d + 1) := by
      obtain ⟨q, hq⟩ := hP d hd
      rw [hq] at ht ⊢
      exact Nat.mul_sub_mod ht
    rw [hmod, Nat.cast_sub (by have := Nat.mod_lt t hdpos; omega)]
    push_cast
    field_simp
    ring
  calc
    _ = ∑ d ∈ Finset.Icc 1 N,
        -(c d * (((P - (t + 1)) % d : ℕ) : ℝ) / (d : ℝ)) := by
      rw [return_residue, Finset.sum_neg_distrib]
    _ = ∑ d ∈ Finset.Icc 1 N,
        (c d / (d : ℝ) - c d + c d * ((t % d : ℕ) : ℝ) / (d : ℝ)) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        sieveReflectionDefect, finiteHarmonicSum, return_residue]
      ring

/-- Every common-return anchor preserves all subsequent discrepancy values. -/
theorem sievePrefix_return_translation (N a k t : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N (sieveReturnAnchor N a k + t) c =
      sievePrefixDiscrepancy N t c :=
  return_translate N _ t c (return_anchor_dvd N a k)

/-- Complete window classification, including zero radii and empty sieve levels. -/
theorem sieveReturnWindow_zero_iff (N a b k : ℕ) (c : ℕ → ℝ) :
    sieveReturnWindowZero N a b k c ↔
      (∀ t ∈ Finset.Icc 1 (max b (a - 1)), sievePrefixDiscrepancy N t c = 0) ∧
        (a = 0 ∨ sieveReflectionDefect N c = 0) := by
  let P := sieveReturnAnchor N a k
  have hPa : a ≤ P := return_anchor_ge N a k
  have hP : ∀ d ∈ Finset.Icc 1 N, d ∣ P := return_anchor_dvd N a k
  change (∀ M ∈ Finset.Icc (P - a) (P + b), sievePrefixDiscrepancy N M c = 0) ↔ _
  constructor
  · intro hw
    have hD : a = 0 ∨ sieveReflectionDefect N c = 0 := by
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        have h := hw (P - (0 + 1)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [return_reflect N P 0 c (by omega) hP, sievePrefixDiscrepancy_zero,
          sub_zero] at h
        exact h
    refine ⟨?_, hD⟩
    intro t ht
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    by_cases htb : t ≤ b
    · have h := hw (P + t) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rwa [return_translate N P t c hP] at h
    · have ha : a ≠ 0 := by omega
      have hD0 := hD.resolve_left ha
      have h := hw (P - (t + 1)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [return_reflect N P t c (by omega) hP, hD0] at h
      linarith
  · rintro ⟨hi, hD⟩ M hM
    obtain ⟨hMl, hMr⟩ := Finset.mem_Icc.mp hM
    by_cases hPM : P ≤ M
    · have heq : P + (M - P) = M := by omega
      rw [← heq, return_translate N P (M - P) c hP]
      by_cases ht : M - P = 0
      · rw [ht, sievePrefixDiscrepancy_zero]
      · exact hi _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · have ha : a ≠ 0 := by omega
      have hD0 := hD.resolve_left ha
      have heq : P - (P - M - 1 + 1) = M := by omega
      rw [← heq, return_reflect N P (P - M - 1) c (by omega) hP, hD0]
      have hz : sievePrefixDiscrepancy N (P - M - 1) c = 0 := by
        by_cases ht : P - M - 1 = 0
        · rw [ht, sievePrefixDiscrepancy_zero]
        · exact hi _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hz, sub_self]

/-- Coefficient form of the complete all-radii classification. -/
theorem sieveReturnWindow_coefficient_kernel (N a b k : ℕ) (c : ℕ → ℝ) :
    sieveReturnWindowZero N a b k c ↔
      (max b (a - 1) = 0 ∨
        ((∀ d ∈ Finset.Icc 2 (min (max b (a - 1)) N), c d = 0) ∧
          (∑ d ∈ Finset.Icc (min (max b (a - 1)) N + 1) N, c d / (d : ℝ)) = 0)) ∧
        (a = 0 ∨ sieveReflectionDefect N c = 0) := by
  rw [sieveReturnWindow_zero_iff, sievePrefix_initial_kernel_iff]

private theorem return_sum_split (N s : ℕ) (f : ℕ → ℝ)
    (hs1 : 1 ≤ s) (hsN : s ≤ N) (hf : ∀ d ∈ Finset.Icc 2 s, f d = 0) :
    (∑ d ∈ Finset.Icc 1 N, f d) = f 1 + ∑ d ∈ Finset.Icc (s + 1) N, f d := by
  have hh : (∑ d ∈ Finset.Icc 1 s, f d) = f 1 := by
    apply Finset.sum_eq_single
    · intro d hd hd1
      exact hf d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
        (Finset.mem_Icc.mp hd).2⟩)
    · intro h
      exact False.elim (h (Finset.mem_Icc.mpr ⟨by omega, hs1⟩))
  have h := Finset.sum_Ico_consecutive f
    (show 1 ≤ s + 1 by omega) (show s + 1 ≤ N + 1 by omega)
  simp only [Finset.Ico_add_one_right_eq_Icc] at h
  rw [hh] at h
  exact h.symm

private theorem return_two_moments (N T : ℕ) (c : ℕ → ℝ) (hT : 0 < T) :
    ((∀ t ∈ Finset.Icc 1 T, sievePrefixDiscrepancy N t c = 0) ∧
      sieveReflectionDefect N c = 0) ↔
    (∀ d ∈ Finset.Icc 2 (min T N), c d = 0) ∧
      (∑ d ∈ Finset.Icc (min T N + 1) N, c d / (d : ℝ)) = 0 ∧
      (∑ d ∈ Finset.Icc (min T N + 1) N, c d) = 0 := by
  rw [sievePrefix_initial_kernel_iff]
  have hT0 : T ≠ 0 := by omega
  simp only [hT0, false_or]
  cases N with
  | zero => simp [sieveReflectionDefect, finiteHarmonicSum]
  | succ N =>
    have hs1 : 1 ≤ min T (N + 1) := by omega
    have hsN : min T (N + 1) ≤ N + 1 := min_le_right _ _
    have split (hc : ∀ d ∈ Finset.Icc 2 (min T (N + 1)), c d = 0) :
        sieveReflectionDefect (N + 1) c =
          (∑ d ∈ Finset.Icc (min T (N + 1) + 1) (N + 1), c d / (d : ℝ)) -
          ∑ d ∈ Finset.Icc (min T (N + 1) + 1) (N + 1), c d := by
      have hh := return_sum_split (N + 1) _ (fun d => c d / (d : ℝ)) hs1 hsN
        (fun d hd => by rw [hc d hd, zero_div])
      have hs := return_sum_split (N + 1) _ c hs1 hsN hc
      rw [sieveReflectionDefect, finiteHarmonicSum, hh, hs]
      simp
    constructor
    · rintro ⟨⟨hc, hh⟩, hd⟩
      refine ⟨hc, hh, ?_⟩
      rw [split hc, hh] at hd
      linarith
    · rintro ⟨hc, hh, hs⟩
      exact ⟨⟨hc, hh⟩, by rw [split hc, hh, hs, sub_self]⟩

/-- Positive radii leave exactly a zero head and two vanishing tail moments. -/
theorem sieveReturnWindow_two_moment_kernel (N a b k : ℕ) (c : ℕ → ℝ) :
    sieveReturnWindowZero N (a + 1) (b + 1) k c ↔
      (∀ d ∈ Finset.Icc 2 (min (max (b + 1) a) N), c d = 0) ∧
        (∑ d ∈ Finset.Icc (min (max (b + 1) a) N + 1) N, c d / (d : ℝ)) = 0 ∧
        (∑ d ∈ Finset.Icc (min (max (b + 1) a) N + 1) N, c d) = 0 := by
  rw [sieveReturnWindow_zero_iff]
  have ha : a + 1 ≠ 0 := by omega
  simp only [ha, false_or, Nat.add_sub_cancel]
  exact return_two_moments N _ c (by omega)

private theorem return_sum_two (n : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc (n + 2) (n + 3), f d) = f (n + 2) + f (n + 3) := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

/-- `2N-3` centered samples detect precisely the nonconstant variance at every return. -/
theorem sieveReturnWindow_sharp_detection (n k : ℕ) (c : ℕ → ℝ) :
    sieveReturnWindowZero (n + 3) (n + 1) (n + 1) k c ↔
      sieveVariance (n + 3) c = 0 := by
  rw [sieveReturnWindow_two_moment_kernel, sieveVariance_eq_zero_iff_tail_zero]
  have hs : min (max (n + 1) n) (n + 3) = n + 1 := by omega
  rw [hs, return_sum_two, return_sum_two]
  constructor
  · rintro ⟨hc, hh, hr⟩
    have hn2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hn3 : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp at hh
    push_cast at hh
    have h2 : c (n + 2) = 0 := by nlinarith
    have h3 : c (n + 3) = 0 := by linarith
    intro d hd
    obtain ⟨hd2, hdN⟩ := Finset.mem_Icc.mp hd
    by_cases h : d ≤ n + 1
    · exact hc d (Finset.mem_Icc.mpr ⟨hd2, h⟩)
    · have h : d = n + 2 ∨ d = n + 3 := by omega
      rcases h with rfl | rfl <;> assumption
  · intro hc
    have h2 := hc (n + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h3 := hc (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    refine ⟨fun d hd => hc d (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hd).1, by have := (Finset.mem_Icc.mp hd).2; omega⟩), ?_, ?_⟩
    · rw [h2, h3]; simp
    · rw [h2, h3]; simp

private theorem return_sum_three (n : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc (n + 2) (n + 4), f d) =
      f (n + 2) + f (n + 3) + f (n + 4) := by
  rw [Finset.sum_Icc_succ_top (by omega), return_sum_two]

/-- The only surviving direction in the longest two-sided return window. -/
def sieveReturnTripleWeight (n : ℕ) (v : ℝ) (d : ℕ) : ℝ :=
  if d = n + 2 then v * (d : ℝ)
  else if d = n + 3 then -2 * v * (d : ℝ)
  else if d = n + 4 then v * (d : ℝ)
  else 0

private theorem return_triple_values (n : ℕ) (v : ℝ) :
    sieveReturnTripleWeight n v (n + 2) = v * ((n + 2 : ℕ) : ℝ) ∧
      sieveReturnTripleWeight n v (n + 3) = -2 * v * ((n + 3 : ℕ) : ℝ) ∧
      sieveReturnTripleWeight n v (n + 4) = v * ((n + 4 : ℕ) : ℝ) := by
  simp [sieveReturnTripleWeight, show n + 3 ≠ n + 2 by omega,
    show n + 4 ≠ n + 2 by omega, show n + 4 ≠ n + 3 by omega]

private theorem return_triple_head (n : ℕ) (v : ℝ) (d : ℕ) (hd : d ≤ n + 1) :
    sieveReturnTripleWeight n v d = 0 := by
  simp [sieveReturnTripleWeight, show d ≠ n + 2 by omega,
    show d ≠ n + 3 by omega, show d ≠ n + 4 by omega]

/-- Every extremal return-window kernel is exactly one final normalized second difference.
The scalar is unique; the constant coefficient and coefficients above the level stay free. -/
theorem sieveReturnWindow_extremal_iff (n k : ℕ) (c : ℕ → ℝ) :
    sieveReturnWindowZero (n + 4) (n + 2) (n + 1) k c ↔
      ∃! v : ℝ, ∀ d ∈ Finset.Icc 2 (n + 4), c d = sieveReturnTripleWeight n v d := by
  have hk := sieveReturnWindow_two_moment_kernel (n + 4) (n + 1) n k c
  have hs : min (max (n + 1) (n + 1)) (n + 4) = n + 1 := by omega
  rw [hs, return_sum_three, return_sum_three] at hk
  rw [hk]
  have hn2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn3 : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn4 : ((n + 4 : ℕ) : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨hc, hh, hr⟩
    let x := c (n + 2) / ((n + 2 : ℕ) : ℝ)
    let y := c (n + 3) / ((n + 3 : ℕ) : ℝ)
    let z := c (n + 4) / ((n + 4 : ℕ) : ℝ)
    have hx : c (n + 2) = x * ((n + 2 : ℕ) : ℝ) := by dsimp [x]; field_simp
    have hy : c (n + 3) = y * ((n + 3 : ℕ) : ℝ) := by dsimp [y]; field_simp
    have hz : c (n + 4) = z * ((n + 4 : ℕ) : ℝ) := by dsimp [z]; field_simp
    change x + y + z = 0 at hh
    rw [hx, hy, hz] at hr
    push_cast at hr
    have hm : ((n : ℝ) + 2) * (x + y + z) = 0 := by rw [hh, mul_zero]
    have hyz : y = -2 * z := by nlinarith
    have hxz : x = z := by linarith
    have hcz : ∀ d ∈ Finset.Icc 2 (n + 4), c d = sieveReturnTripleWeight n z d := by
      intro d hd
      obtain ⟨hd2, hdN⟩ := Finset.mem_Icc.mp hd
      by_cases hhead : d ≤ n + 1
      · rw [hc d (Finset.mem_Icc.mpr ⟨hd2, hhead⟩), return_triple_head n z d hhead]
      · have hd : d = n + 2 ∨ d = n + 3 ∨ d = n + 4 := by omega
        rcases hd with rfl | rfl | rfl
        · rw [(return_triple_values n z).1, hx, hxz]
        · rw [(return_triple_values n z).2.1, hy, hyz]
        · rw [(return_triple_values n z).2.2, hz]
    refine ⟨z, hcz, ?_⟩
    intro μ hμ
    have hlast := hμ (n + 4) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [(return_triple_values n μ).2.2, hz] at hlast
    have hmz : (μ - z) * ((n + 4 : ℕ) : ℝ) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmz with h | h
    · linarith
    · exact False.elim (hn4 h)
  · rintro ⟨v, hc, _⟩
    have h2 := (hc (n + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).trans
      (return_triple_values n v).1
    have h3 := (hc (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).trans
      (return_triple_values n v).2.1
    have h4 := (hc (n + 4) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).trans
      (return_triple_values n v).2.2
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      rw [hc d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
        by have := (Finset.mem_Icc.mp hd).2; omega⟩)]
      exact return_triple_head n v d (Finset.mem_Icc.mp hd).2
    · rw [h2, h3, h4]
      field_simp
      ring
    · rw [h2, h3, h4]
      push_cast
      ring

/-- Every scalar multiple realizes the entire `2N-4` zero block. -/
theorem sieveReturnTripleWeight_zero_block (n k : ℕ) (v : ℝ) :
    sieveReturnWindowZero (n + 4) (n + 2) (n + 1) k (sieveReturnTripleWeight n v) := by
  rw [sieveReturnWindow_extremal_iff]
  refine ⟨v, fun _ _ => rfl, ?_⟩
  intro μ hμ
  have h := hμ (n + 4) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [(return_triple_values n v).2.2, (return_triple_values n μ).2.2] at h
  have hn : ((n + 4 : ℕ) : ℝ) ≠ 0 := by positivity
  have hm : (μ - v) * ((n + 4 : ℕ) : ℝ) = 0 := by nlinarith
  rcases mul_eq_zero.mp hm with h | h
  · linarith
  · exact False.elim (hn h)

/-- The extremal direction is nonconstant exactly when its scalar is nonzero. -/
theorem sieveReturnTripleWeight_variance_zero_iff (n : ℕ) (v : ℝ) :
    sieveVariance (n + 4) (sieveReturnTripleWeight n v) = 0 ↔ v = 0 := by
  rw [sieveVariance_eq_zero_iff_tail_zero]
  constructor
  · intro h
    have hlast := h (n + 4) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [(return_triple_values n v).2.2] at hlast
    rcases mul_eq_zero.mp hlast with hv | hn
    · exact hv
    · have : (0 : ℝ) < ((n + 4 : ℕ) : ℝ) := by positivity
      linarith
  · rintro rfl d _
    simp [sieveReturnTripleWeight]

private theorem return_triple_first_jump (n : ℕ) (v : ℝ) :
    sievePrefixDiscrepancy (n + 4) (n + 2) (sieveReturnTripleWeight n v) =
      v * ((n + 2 : ℕ) : ℝ) := by
  let f := fun d => sieveReturnTripleWeight n v d * (((n + 2) % d : ℕ) : ℝ) / (d : ℝ)
  have hs := return_sum_split (n + 4) (n + 1) f (by omega) (by omega)
    (fun d hd => by
      dsimp [f]
      rw [return_triple_head n v d (Finset.mem_Icc.mp hd).2, zero_mul, zero_div])
  rw [return_sum_three] at hs
  rw [return_residue]
  change -(∑ d ∈ Finset.Icc 1 (n + 4), f d) = _
  rw [hs]
  dsimp only [f]
  rw [return_triple_head n v 1 (by omega), zero_mul, zero_div, zero_add,
    (return_triple_values n v).1, (return_triple_values n v).2.1,
    (return_triple_values n v).2.2, Nat.mod_self,
    Nat.mod_eq_of_lt (by omega : n + 2 < n + 3),
    Nat.mod_eq_of_lt (by omega : n + 2 < n + 4)]
  have hn3 : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn4 : ((n + 4 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_zero, mul_zero, zero_div, zero_add]
  field_simp
  ring

/-- Both adjacent samples are exact and nonzero for a nonzero extremal scalar. -/
theorem sieveReturnTripleWeight_adjacent_values (n k : ℕ) (v : ℝ) :
    sievePrefixDiscrepancy (n + 4) (sieveReturnAnchor (n + 4) (n + 2) k - (n + 3))
        (sieveReturnTripleWeight n v) = -v * ((n + 2 : ℕ) : ℝ) ∧
      sievePrefixDiscrepancy (n + 4) (sieveReturnAnchor (n + 4) (n + 2) k + (n + 2))
        (sieveReturnTripleWeight n v) = v * ((n + 2 : ℕ) : ℝ) := by
  have hD := ((sieveReturnWindow_zero_iff (n + 4) (n + 2) (n + 1) k
    (sieveReturnTripleWeight n v)).mp (sieveReturnTripleWeight_zero_block n k v)).2
  have hD0 := hD.resolve_left (by omega)
  have hP : n + 2 < sieveReturnAnchor (n + 4) (n + 2) k := by
    have h := Nat.le_mul_of_pos_right (k + (n + 2) + 1) (Nat.factorial_pos (n + 4))
    unfold sieveReturnAnchor
    omega
  constructor
  · rw [show n + 3 = n + 2 + 1 by omega,
      return_reflect (n + 4) _ (n + 2) _ hP (return_anchor_dvd (n + 4) (n + 2) k),
      hD0, return_triple_first_jump]
    ring
  · rw [sievePrefix_return_translation, return_triple_first_jump]

end

end GaloisForLFunctions.BezoutValuationIncidence
