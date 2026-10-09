import GaloisForLFunctions.RHTower.ComplexFugacityLeeYangChain
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# First order of complex-fugacity Lee–Yang chains

Expand the chain partition function `cChainZ α u N` in the wall fugacities.  With no wall flipped,
`A = 1` and `B = ∏_{j ≤ N} u_j`.  With one wall `k < N` flipped, `A` collects
`α_k ∏_{j ≤ k} u_j` and `B` collects `conj α_k ∏_{k < j ≤ N} u_j`.  So

  `Z = 1 + ∏_{j ≤ N} u_j + Σ_{k<N} (α_k ∏_{j ≤ k} u_j + conj α_k ∏_{k<j≤N} u_j) + R`.

For fields in the closed unit disc, `‖R‖ ≤ s² e^s` with `s = Σ_{k<N} ‖α_k‖`
(`norm_cChainZ_sub_firstOrder_le`).  The remainder pair obeys
`ρ_{k+1} ≤ (1 + ‖α_k‖)ρ_k + 2‖α_k‖ s_k`.  For real scalings `α_k = κ c_k`, the first-order term is
the `κ`-derivative at `κ = 0`, for arbitrary fields (`hasDerivAt_cChainZ_smul`).

**Doubled harmonic chain.**  With fields `λ_j = 2 log((j+2)/(j+1))` the field products telescope to
`∏_{j ≤ k} u_j = (k+2)^{−2iz}`, and the total frequency is `L = Σ_{j≤N} λ_j = 2 log(N+2)`.  With
fugacities `κ/(k+2)` the zeroth order is `1 + e^{−izL}`, and the first-order coefficient is
`Σ_{n=2}^{N+1} (n^{−1−2iz} + e^{−izL} n^{−1+2iz})` (`hasDerivAt_doubledHarmonicChainZ`).  For real
`x`,

  `e^{ixL/2} Z = 2 cos(xL/2) + 2κ Re[e^{ixL/2} Σ_{n=2}^{N+1} n^{−1−2ix}] + R`,
  `‖R‖ ≤ κ² H² e^{|κ| H}`, where `H = Σ_{n=2}^{N+1} 1/n`

(`norm_doubledHarmonicChainZ_sub_le`).  This is the shape `2√y Re[ξ(1+2iτ) y^{iτ}]` of the
Eisenstein constant term, with `y = e^{L/2} = N + 2`.
-/

open Complex Finset

namespace RHTower.LeeYangChain

noncomputable section

/-! ## The first-order expansion -/

/-- Product of the fields at sites `0, …, k`. -/
def fieldProd (u : ℕ → ℂ) (k : ℕ) : ℂ := ∏ j ∈ range (k + 1), u j

/-- Product of the fields at sites `k + 1, …, N`. -/
def fieldProdAfter (u : ℕ → ℂ) (k N : ℕ) : ℂ := ∏ j ∈ Ico (k + 1) (N + 1), u j

/-- First-order `A`-weight: exactly one flipped wall `k < N`. -/
def firstOrderA (α u : ℕ → ℂ) (N : ℕ) : ℂ := ∑ k ∈ range N, α k * fieldProd u k

/-- First-order `B`-weight: exactly one flipped wall `k < N`. -/
def firstOrderB (α u : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, (starRingEnd ℂ) (α k) * fieldProdAfter u k N

theorem fieldProd_succ (u : ℕ → ℂ) (k : ℕ) :
    fieldProd u (k + 1) = fieldProd u k * u (k + 1) := by
  simp only [fieldProd]
  rw [prod_range_succ]

theorem fieldProdAfter_self (u : ℕ → ℂ) (N : ℕ) : fieldProdAfter u N N = 1 := by
  simp [fieldProdAfter]

theorem fieldProdAfter_succ (u : ℕ → ℂ) {k N : ℕ} (h : k ≤ N) :
    fieldProdAfter u k (N + 1) = fieldProdAfter u k N * u (N + 1) := by
  simp only [fieldProdAfter]
  exact prod_Ico_succ_top (by omega) u

theorem fieldProd_mul_fieldProdAfter (u : ℕ → ℂ) {k N : ℕ} (h : k ≤ N) :
    fieldProd u k * fieldProdAfter u k N = fieldProd u N := by
  simp only [fieldProd, fieldProdAfter]
  exact prod_range_mul_prod_Ico u (by omega)

theorem firstOrderA_succ (α u : ℕ → ℂ) (N : ℕ) :
    firstOrderA α u (N + 1) = firstOrderA α u N + α N * fieldProd u N := by
  simp only [firstOrderA]
  rw [sum_range_succ]

theorem firstOrderB_succ (α u : ℕ → ℂ) (N : ℕ) :
    firstOrderB α u (N + 1) = u (N + 1) * ((starRingEnd ℂ) (α N) + firstOrderB α u N) := by
  have h1 : ∑ k ∈ range N, (starRingEnd ℂ) (α k) * fieldProdAfter u k (N + 1) =
      u (N + 1) * ∑ k ∈ range N, (starRingEnd ℂ) (α k) * fieldProdAfter u k N := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [fieldProdAfter_succ u (mem_range.mp hk).le]
    ring
  simp only [firstOrderB]
  rw [sum_range_succ, h1, fieldProdAfter_succ u le_rfl, fieldProdAfter_self]
  ring

/-- With every fugacity zero the chain is the product of the fields. -/
theorem cChainPair_zero (u : ℕ → ℂ) (N : ℕ) : cChainPair (fun _ => 0) u N = (1, fieldProd u N) := by
  induction N with
  | zero => simp [cChainPair, fieldProd]
  | succ N ih =>
    simp only [cChainPair, ih, fieldProd_succ, map_zero, zero_mul, add_zero, zero_add]
    rw [mul_comm]

section Bounds

variable {u : ℕ → ℂ}

theorem norm_fieldProd_le_one (hu : ∀ k, ‖u k‖ ≤ 1) (k : ℕ) : ‖fieldProd u k‖ ≤ 1 :=
  (Finset.norm_prod_le _ _).trans (prod_le_one (fun _ _ => norm_nonneg _) fun j _ => hu j)

theorem norm_fieldProdAfter_le_one (hu : ∀ k, ‖u k‖ ≤ 1) (k N : ℕ) :
    ‖fieldProdAfter u k N‖ ≤ 1 :=
  (Finset.norm_prod_le _ _).trans (prod_le_one (fun _ _ => norm_nonneg _) fun j _ => hu j)

theorem norm_firstOrderA_le (α : ℕ → ℂ) (hu : ∀ k, ‖u k‖ ≤ 1) (N : ℕ) :
    ‖firstOrderA α u N‖ ≤ ∑ k ∈ range N, ‖α k‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_fieldProd_le_one hu k)

theorem norm_firstOrderB_le (α : ℕ → ℂ) (hu : ∀ k, ‖u k‖ ≤ 1) (N : ℕ) :
    ‖firstOrderB α u N‖ ≤ ∑ k ∈ range N, ‖α k‖ := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_fieldProdAfter_le_one hu k N)

/-- **Second-order remainder of the chain weights.**  For fields in the closed unit disc, the two
weights differ from their first-order expansions by at most `s² e^s` in total,
`s = Σ_{k<N} ‖α_k‖`. -/
theorem norm_cChainPair_sub_firstOrder_le (α : ℕ → ℂ) (hu : ∀ k, ‖u k‖ ≤ 1) (N : ℕ) :
    ‖(cChainPair α u N).1 - 1 - firstOrderA α u N‖ +
        ‖(cChainPair α u N).2 - fieldProd u N - firstOrderB α u N‖ ≤
      (∑ k ∈ range N, ‖α k‖) ^ 2 * Real.exp (∑ k ∈ range N, ‖α k‖) := by
  induction N with
  | zero => simp [cChainPair, firstOrderA, firstOrderB, fieldProd]
  | succ N ih =>
    set s := ∑ k ∈ range N, ‖α k‖ with hs
    set a := ‖α N‖ with ha
    have hs0 : 0 ≤ s := sum_nonneg fun _ _ => norm_nonneg _
    have ha0 : 0 ≤ a := norm_nonneg _
    set rA := (cChainPair α u N).1 - 1 - firstOrderA α u N with hrA
    set rB := (cChainPair α u N).2 - fieldProd u N - firstOrderB α u N with hrB
    have eA : (cChainPair α u (N + 1)).1 - 1 - firstOrderA α u (N + 1) =
        rA + α N * (rB + firstOrderB α u N) := by
      simp only [cChainPair, firstOrderA_succ, hrA, hrB]
      ring
    have eB : (cChainPair α u (N + 1)).2 - fieldProd u (N + 1) - firstOrderB α u (N + 1) =
        u (N + 1) * ((starRingEnd ℂ) (α N) * (rA + firstOrderA α u N) + rB) := by
      simp only [cChainPair, fieldProd_succ, firstOrderB_succ, hrA, hrB]
      ring
    have hA := norm_firstOrderA_le α hu N
    have hB := norm_firstOrderB_le α hu N
    have bA : ‖rA + α N * (rB + firstOrderB α u N)‖ ≤ ‖rA‖ + a * (‖rB‖ + s) := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl hB)) ha0
    have bB : ‖u (N + 1) * ((starRingEnd ℂ) (α N) * (rA + firstOrderA α u N) + rB)‖ ≤
        a * (‖rA‖ + s) + ‖rB‖ := by
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (hu _)).trans ?_
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl hA)) ha0
    have hsum : ∑ k ∈ range (N + 1), ‖α k‖ = s + a := by rw [sum_range_succ]
    rw [eA, eB, hsum]
    have hρ : ‖rA‖ + ‖rB‖ ≤ s ^ 2 * Real.exp s := ih
    have hexp : Real.exp (s + a) ≥ Real.exp s * (1 + a) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos s).le
    have hes : 1 ≤ Real.exp s := Real.one_le_exp hs0
    calc ‖rA + α N * (rB + firstOrderB α u N)‖ +
          ‖u (N + 1) * ((starRingEnd ℂ) (α N) * (rA + firstOrderA α u N) + rB)‖
        ≤ (1 + a) * (‖rA‖ + ‖rB‖) + 2 * a * s := by linarith
      _ ≤ (1 + a) * (s ^ 2 * Real.exp s) + 2 * a * s :=
          add_le_add (mul_le_mul_of_nonneg_left hρ (by linarith)) le_rfl
      _ ≤ (s + a) ^ 2 * (Real.exp s * (1 + a)) := by
          have hm : 1 ≤ (1 + a) * Real.exp s := by nlinarith [mul_nonneg ha0 (Real.exp_pos s).le]
          have hq : 0 ≤ 2 * a * s := by positivity
          have h2 : 2 * a * s ≤ (2 * a * s + a ^ 2) * ((1 + a) * Real.exp s) := by
            nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ (1 + a) * Real.exp s)]
          have e : (s + a) ^ 2 * (Real.exp s * (1 + a)) =
              (1 + a) * (s ^ 2 * Real.exp s) + (2 * a * s + a ^ 2) * ((1 + a) * Real.exp s) := by
            ring
          rw [e]
          linarith
      _ ≤ (s + a) ^ 2 * Real.exp (s + a) :=
          mul_le_mul_of_nonneg_left hexp (sq_nonneg _)

/-- **First-order expansion of the chain partition function.**  For fields in the closed unit
disc, `‖Z − (1 + ∏_{j≤N} u_j) − Z¹‖ ≤ s² e^s` with `s = Σ_{k<N} ‖α_k‖`. -/
theorem norm_cChainZ_sub_firstOrder_le (α : ℕ → ℂ) (hu : ∀ k, ‖u k‖ ≤ 1) (N : ℕ) :
    ‖cChainZ α u N - (1 + fieldProd u N) - (firstOrderA α u N + firstOrderB α u N)‖ ≤
      (∑ k ∈ range N, ‖α k‖) ^ 2 * Real.exp (∑ k ∈ range N, ‖α k‖) := by
  have e : cChainZ α u N - (1 + fieldProd u N) - (firstOrderA α u N + firstOrderB α u N) =
      ((cChainPair α u N).1 - 1 - firstOrderA α u N) +
        ((cChainPair α u N).2 - fieldProd u N - firstOrderB α u N) := by
    simp only [cChainZ]
    ring
  rw [e]
  exact (norm_add_le _ _).trans (norm_cChainPair_sub_firstOrder_le α hu N)

end Bounds

/-- **The first-order term is the derivative in a real coupling.**  For real wall profiles `c`
and arbitrary fields, `κ ↦ Z(κ c)` has derivative `Σ_{k<N} c_k (∏_{j≤k} u_j + ∏_{k<j≤N} u_j)` at
`κ = 0`. -/
theorem hasDerivAt_cChainPair_smul (c : ℕ → ℝ) (u : ℕ → ℂ) (N : ℕ) :
    HasDerivAt (fun κ : ℝ => (cChainPair (fun k => ((κ * c k : ℝ) : ℂ)) u N).1)
        (firstOrderA (fun k => (c k : ℂ)) u N) 0 ∧
      HasDerivAt (fun κ : ℝ => (cChainPair (fun k => ((κ * c k : ℝ) : ℂ)) u N).2)
        (firstOrderB (fun k => (c k : ℂ)) u N) 0 := by
  have hzero : (fun k => (((0 : ℝ) * c k : ℝ) : ℂ)) = fun _ => 0 := by
    funext k
    simp
  have h0 := cChainPair_zero u
  induction N with
  | zero =>
    simp only [cChainPair, firstOrderA, firstOrderB, range_zero, sum_empty]
    exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩
  | succ N ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hα : HasDerivAt (fun κ : ℝ => ((κ * c N : ℝ) : ℂ)) ((c N : ℝ) : ℂ) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (c N)).ofReal_comp
      simpa using this
    have vA : (cChainPair (fun k => (((0 : ℝ) * c k : ℝ) : ℂ)) u N).1 = 1 := by
      rw [hzero, h0]
    have vB : (cChainPair (fun k => (((0 : ℝ) * c k : ℝ) : ℂ)) u N).2 = fieldProd u N := by
      rw [hzero, h0]
    constructor
    · have h := ihA.add (hα.mul ihB)
      rw [vB] at h
      have e : firstOrderA (fun k => (c k : ℂ)) u N + (((c N : ℝ) : ℂ) * fieldProd u N +
          (((0 : ℝ) * c N : ℝ) : ℂ) * firstOrderB (fun k => (c k : ℂ)) u N) =
          firstOrderA (fun k => (c k : ℂ)) u (N + 1) := by
        rw [firstOrderA_succ]
        push_cast
        ring
      rw [e] at h
      exact h
    · have hc : (fun κ : ℝ => (cChainPair (fun k => ((κ * c k : ℝ) : ℂ)) u (N + 1)).2) =
          fun κ : ℝ => u (N + 1) * (((κ * c N : ℝ) : ℂ) *
            (cChainPair (fun k => ((κ * c k : ℝ) : ℂ)) u N).1 +
              (cChainPair (fun k => ((κ * c k : ℝ) : ℂ)) u N).2) := by
        funext κ
        simp only [cChainPair, Complex.conj_ofReal]
      rw [hc]
      have h := ((hα.mul ihA).add ihB).const_mul (u (N + 1))
      rw [vA] at h
      have e : u (N + 1) * (((c N : ℝ) : ℂ) * 1 +
          (((0 : ℝ) * c N : ℝ) : ℂ) * firstOrderA (fun k => (c k : ℂ)) u N +
            firstOrderB (fun k => (c k : ℂ)) u N) =
          firstOrderB (fun k => (c k : ℂ)) u (N + 1) := by
        rw [firstOrderB_succ, Complex.conj_ofReal]
        push_cast
        ring
      rw [e] at h
      exact h

/-- The `κ`-derivative of the chain partition function at `κ = 0`. -/
theorem hasDerivAt_cChainZ_smul (c : ℕ → ℝ) (u : ℕ → ℂ) (N : ℕ) :
    HasDerivAt (fun κ : ℝ => cChainZ (fun k => ((κ * c k : ℝ) : ℂ)) u N)
      (firstOrderA (fun k => (c k : ℂ)) u N + firstOrderB (fun k => (c k : ℂ)) u N) 0 := by
  obtain ⟨hA, hB⟩ := hasDerivAt_cChainPair_smul c u N
  exact hA.add hB

/-! ## The doubled harmonic chain -/

/-- Doubled harmonic frequencies `λ_j = 2 log((j+2)/(j+1))`. -/
def doubledHarmonicFreq (j : ℕ) : ℝ :=
  2 * (Real.log ((j + 2 : ℕ) : ℝ) - Real.log ((j + 1 : ℕ) : ℝ))

theorem doubledHarmonicFreq_pos (j : ℕ) : 0 < doubledHarmonicFreq j := by
  rw [doubledHarmonicFreq]
  have : Real.log ((j + 1 : ℕ) : ℝ) < Real.log ((j + 2 : ℕ) : ℝ) :=
    Real.log_lt_log (by positivity) (by push_cast; linarith)
  linarith

/-- The frequencies telescope: `Σ_{j ≤ k} λ_j = 2 log(k + 2)`. -/
theorem sum_doubledHarmonicFreq (k : ℕ) :
    ∑ j ∈ range (k + 1), doubledHarmonicFreq j = 2 * Real.log ((k + 2 : ℕ) : ℝ) := by
  have h : ∀ j, doubledHarmonicFreq j =
      2 * (Real.log ((j + 1 + 1 : ℕ) : ℝ) - Real.log ((j + 1 : ℕ) : ℝ)) := fun j => rfl
  simp only [h]
  rw [← mul_sum, sum_range_sub (fun j => Real.log ((j + 1 : ℕ) : ℝ))]
  simp only [Nat.cast_add, Nat.cast_one, zero_add, Real.log_one, sub_zero, Nat.cast_ofNat]
  congr 2
  ring

/-- Field products of the doubled harmonic chain: `∏_{j ≤ k} u_j = e^{−2iz log(k+2)}`. -/
theorem fieldProd_doubledHarmonic (z : ℂ) (k : ℕ) :
    fieldProd (chainExpField doubledHarmonicFreq z) k =
      cexp (-(2 * I * z * Real.log ((k + 2 : ℕ) : ℝ))) := by
  simp only [fieldProd, chainExpField]
  rw [← Complex.exp_sum]
  congr 1
  have hs : (∑ j ∈ range (k + 1), (doubledHarmonicFreq j : ℂ)) =
      ((2 * Real.log ((k + 2 : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← sum_doubledHarmonicFreq k]
    push_cast
    rfl
  rw [sum_neg_distrib]
  congr 1
  rw [← sum_mul, ← mul_sum, hs]
  push_cast
  ring

theorem fieldProdAfter_doubledHarmonic (z : ℂ) {k N : ℕ} (h : k ≤ N) :
    fieldProdAfter (chainExpField doubledHarmonicFreq z) k N =
      cexp (-(2 * I * z * Real.log ((N + 2 : ℕ) : ℝ))) *
        cexp (2 * I * z * Real.log ((k + 2 : ℕ) : ℝ)) := by
  have e := fieldProd_mul_fieldProdAfter (chainExpField doubledHarmonicFreq z) h
  rw [fieldProd_doubledHarmonic, fieldProd_doubledHarmonic] at e
  set w : ℂ := 2 * I * z * Real.log ((k + 2 : ℕ) : ℝ) with hw
  have hX : cexp w * cexp (-w) = 1 := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc fieldProdAfter (chainExpField doubledHarmonicFreq z) k N
      = (cexp w * cexp (-w)) * fieldProdAfter (chainExpField doubledHarmonicFreq z) k N := by
        rw [hX, one_mul]
    _ = cexp w * (cexp (-w) * fieldProdAfter (chainExpField doubledHarmonicFreq z) k N) := by ring
    _ = _ := by rw [e]; ring

/-- `n^s = e^{s log n}` for a positive integer `n`. -/
theorem natCast_cpow_eq_cexp {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ((n : ℂ) ^ s) = cexp (Real.log n * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.natCast_log]

/-- `e^{−log n} · e^{w} = e^{w − log n}` with the reciprocal written out. -/
theorem inv_natCast_mul_cexp {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    ((1 / (n : ℝ) : ℝ) : ℂ) * cexp w = cexp (Real.log n * (-1) + w) := by
  rw [Complex.exp_add]
  congr 1
  rw [mul_neg_one, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  push_cast
  ring

/-- First-order `A`-weight of the doubled harmonic chain with profile `1/(k+2)`. -/
theorem firstOrderA_doubledHarmonic (z : ℂ) (N : ℕ) :
    firstOrderA (fun k => ((1 / ((k + 2 : ℕ) : ℝ) : ℝ) : ℂ))
        (chainExpField doubledHarmonicFreq z) N =
      ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 - 2 * I * z) := by
  refine sum_congr rfl fun k _ => ?_
  rw [fieldProd_doubledHarmonic, inv_natCast_mul_cexp (by omega),
    natCast_cpow_eq_cexp (by omega)]
  congr 1
  ring

/-- First-order `B`-weight of the doubled harmonic chain with profile `1/(k+2)`. -/
theorem firstOrderB_doubledHarmonic (z : ℂ) (N : ℕ) :
    firstOrderB (fun k => ((1 / ((k + 2 : ℕ) : ℝ) : ℝ) : ℂ))
        (chainExpField doubledHarmonicFreq z) N =
      cexp (-(2 * I * z * Real.log ((N + 2 : ℕ) : ℝ))) *
        ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 + 2 * I * z) := by
  rw [firstOrderB, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [Complex.conj_ofReal, fieldProdAfter_doubledHarmonic z (mem_range.mp hk).le,
    mul_left_comm, inv_natCast_mul_cexp (by omega), natCast_cpow_eq_cexp (by omega)]
  congr 2
  ring

/-- **The doubled harmonic chain at first order.**  With fugacities `κ/(k+2)`, the chain is
`1 + e^{−izL}` at `κ = 0` (`L = 2 log(N+2)`), and its `κ`-derivative there is
`Σ_{n=2}^{N+1} (n^{−1−2iz} + e^{−izL} n^{−1+2iz})`. -/
theorem hasDerivAt_doubledHarmonicChainZ (z : ℂ) (N : ℕ) :
    cChainZ (fun k => (((0 : ℝ) * (1 / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ))
        (chainExpField doubledHarmonicFreq z) N =
      1 + cexp (-(2 * I * z * Real.log ((N + 2 : ℕ) : ℝ))) ∧
    HasDerivAt (fun κ : ℝ => cChainZ (fun k => ((κ * (1 / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ))
        (chainExpField doubledHarmonicFreq z) N)
      (∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 - 2 * I * z) +
        cexp (-(2 * I * z * Real.log ((N + 2 : ℕ) : ℝ))) *
          ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 + 2 * I * z)) 0 := by
  constructor
  · have hzero : (fun k => (((0 : ℝ) * (1 / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ)) = fun _ => 0 := by
      funext k
      simp
    rw [hzero, cChainZ, cChainPair_zero, fieldProd_doubledHarmonic]
  · have := hasDerivAt_cChainZ_smul (fun k => 1 / ((k + 2 : ℕ) : ℝ))
      (chainExpField doubledHarmonicFreq z) N
    rwa [firstOrderA_doubledHarmonic, firstOrderB_doubledHarmonic] at this

/-- Conjugation of `n^s` for a positive integer `n`. -/
theorem conj_natCast_cpow {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ s) = (n : ℂ) ^ ((starRingEnd ℂ) s) := by
  rw [natCast_cpow_eq_cexp hn, natCast_cpow_eq_cexp hn, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal]

/-- **The doubled harmonic chain is a first-order Eisenstein constant term.**  For real `x`, with
`ℓ = log(N+2)` (half the total frequency) and `H = Σ_{n=2}^{N+1} 1/n`,
`‖e^{ixℓ} Z − 2cos(xℓ) − 2κ Re[e^{ixℓ} Σ_{n=2}^{N+1} n^{−1−2ix}]‖ ≤ κ² H² e^{|κ| H}`. -/
theorem norm_doubledHarmonicChainZ_sub_le (x κ : ℝ) (N : ℕ) :
    ‖cexp (I * x * Real.log ((N + 2 : ℕ) : ℝ)) *
          cChainZ (fun k => ((κ * (1 / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ))
            (chainExpField doubledHarmonicFreq x) N -
        (((2 * Real.cos (x * Real.log ((N + 2 : ℕ) : ℝ)) : ℝ) : ℂ) +
          ((2 * κ * (cexp (I * x * Real.log ((N + 2 : ℕ) : ℝ)) *
            ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 - 2 * I * x)).re : ℝ) : ℂ))‖ ≤
      κ ^ 2 * (∑ k ∈ range N, 1 / ((k + 2 : ℕ) : ℝ)) ^ 2 *
        Real.exp (|κ| * ∑ k ∈ range N, 1 / ((k + 2 : ℕ) : ℝ)) := by
  set u := chainExpField doubledHarmonicFreq (x : ℂ) with hu_def
  set ℓ := Real.log ((N + 2 : ℕ) : ℝ) with hℓ
  set E := cexp (I * x * ℓ) with hE
  set β : ℕ → ℂ := fun k => ((1 / ((k + 2 : ℕ) : ℝ) : ℝ) : ℂ) with hβ
  set H := ∑ k ∈ range N, 1 / ((k + 2 : ℕ) : ℝ) with hH
  set A := ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 - 2 * I * x) with hA
  have hu : ∀ k, ‖u k‖ ≤ 1 := fun k => by
    rw [hu_def, norm_chainExpField]
    simp
  have hα : (fun k => ((κ * (1 / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ)) = fun k => (κ : ℂ) * β k := by
    funext k
    simp [hβ]
  have hfA : firstOrderA (fun k => (κ : ℂ) * β k) u N = κ * firstOrderA β u N := by
    simp only [firstOrderA, mul_sum, mul_assoc]
  have hfB : firstOrderB (fun k => (κ : ℂ) * β k) u N = κ * firstOrderB β u N := by
    simp only [firstOrderB, mul_sum, map_mul, Complex.conj_ofReal, mul_assoc]
  have hs : ∑ k ∈ range N, ‖(κ : ℂ) * β k‖ = |κ| * H := by
    rw [hH, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hβ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < 1 / ((k + 2 : ℕ) : ℝ) by positivity)]
  have hR := norm_cChainZ_sub_firstOrder_le (fun k => (κ : ℂ) * β k) hu N
  rw [hs, hfA, hfB] at hR
  have hAβ : firstOrderA β u N = A := firstOrderA_doubledHarmonic (x : ℂ) N
  have hBβ : firstOrderB β u N =
      cexp (-(2 * I * x * ℓ)) * ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 + 2 * I * x) :=
    firstOrderB_doubledHarmonic (x : ℂ) N
  have hE1 : ‖E‖ = 1 := by
    rw [hE, show I * (x : ℂ) * (ℓ : ℂ) = ((x * ℓ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h0 : E * (1 + fieldProd u N) = ((2 * Real.cos (x * ℓ) : ℝ) : ℂ) := by
    rw [hu_def, fieldProd_doubledHarmonic, ← hℓ, mul_add, mul_one, hE, ← Complex.exp_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.two_cos,
      Complex.ofReal_mul]
    congr 1 <;> congr 1 <;> ring
  have hconjE : (starRingEnd ℂ) E = cexp (-(I * x * ℓ)) := by
    rw [hE, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofReal]
    congr 1
    ring
  have hconjA : (starRingEnd ℂ) A = ∑ k ∈ range N, ((k + 2 : ℕ) : ℂ) ^ (-1 + 2 * I * x) := by
    rw [hA, map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [conj_natCast_cpow (by omega)]
    congr 1
    simp only [map_sub, map_neg, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have h1 : E * (firstOrderA β u N + firstOrderB β u N) = ((2 * (E * A).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj, map_mul, hconjE, hconjA, hAβ, hBβ, mul_add]
    congr 1
    rw [← mul_assoc, hE, ← Complex.exp_add]
    congr 2
    ring
  have key : E * cChainZ (fun k => ((κ * (1 / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ)) u N -
      (((2 * Real.cos (x * ℓ) : ℝ) : ℂ) + ((2 * κ * (E * A).re : ℝ) : ℂ)) =
      E * (cChainZ (fun k => (κ : ℂ) * β k) u N - (1 + fieldProd u N) -
        (κ * firstOrderA β u N + κ * firstOrderB β u N)) := by
    rw [hα, ← h0]
    have : ((2 * κ * (E * A).re : ℝ) : ℂ) = κ * ((2 * (E * A).re : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← h1]
    ring
  rw [key, norm_mul, hE1, one_mul]
  refine hR.trans (le_of_eq ?_)
  rw [mul_pow, sq_abs]

end

end RHTower.LeeYangChain
