import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Weyl alternative for a half-line Jacobi recurrence

For a real half-line Jacobi recurrence

`a_n u_n + b_{n+1} u_{n+1} + a_{n+1} u_{n+2} = z u_{n+1}`

the *cross-Wronskian* of a solution `f` at `z` and a solution `g` at `ζ`,

`X_n = a_n (f_{n+1} g_n − f_n g_{n+1})`,

obeys the exact increment law `X_{n+1} = X_n + (z − ζ) f_{n+1} g_{n+1}`.  Two consequences are
proved here, both by Cramer's rule plus a discrete Gronwall bound:

* **transfer**: if some spectral parameter admits a square-summable fundamental system, then every
  solution at every spectral parameter is square-summable;
* **rigidity**: at a non-real spectral parameter, a single nonzero square-summable solution whose
  cross-Wronskian with its own conjugate is bounded away from zero already forces every solution to
  be square-summable.

Together they are the limit-point / limit-circle alternative in the form needed to decide
deficiency indices.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- The half-line Jacobi recurrence, without the left boundary equation. -/
def IsJacobiRec (a b : ℕ → ℝ) (z : ℂ) (u : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, (a n : ℂ) * u n + (b (n + 1) : ℂ) * u (n + 1) + (a (n + 1) : ℂ) * u (n + 2)
    = z * u (n + 1)

/-- The cross-Wronskian of two sequences against the Jacobi weight. -/
def crossWronskian (a : ℕ → ℝ) (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  (a n : ℂ) * (f (n + 1) * g n - f n * g (n + 1))

variable {a b : ℕ → ℝ} {z ζ : ℂ} {f g φ ψ u : ℕ → ℂ}

/-- **The cross-Wronskian increment law.** -/
theorem crossWronskian_succ (hf : IsJacobiRec a b z f) (hg : IsJacobiRec a b ζ g) (n : ℕ) :
    crossWronskian a f g (n + 1)
      = crossWronskian a f g n + (z - ζ) * f (n + 1) * g (n + 1) := by
  simp only [crossWronskian]
  linear_combination g (n + 1) * hf n - f (n + 1) * hg n

/-- Two solutions at the *same* spectral parameter have a constant cross-Wronskian. -/
theorem crossWronskian_const (hf : IsJacobiRec a b z f) (hg : IsJacobiRec a b z g) (n : ℕ) :
    crossWronskian a f g (n + 1) = crossWronskian a f g n := by
  rw [crossWronskian_succ hf hg n]
  ring

theorem crossWronskian_eq_zero_of_const (hf : IsJacobiRec a b z f) (hg : IsJacobiRec a b z g)
    {m n : ℕ} : crossWronskian a f g m = crossWronskian a f g n := by
  have key : ∀ k : ℕ, crossWronskian a f g k = crossWronskian a f g 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [crossWronskian_const hf hg k, ih]
  rw [key m, key n]

/-- **Cramer's rule for a Jacobi fundamental system.** -/
theorem crossWronskian_cramer (a : ℕ → ℝ) (φ ψ u : ℕ → ℂ) (n : ℕ) :
    (a n : ℂ) * (φ n * ψ (n + 1) - φ (n + 1) * ψ n) * u n
      = -crossWronskian a u ψ n * φ n + crossWronskian a u φ n * ψ n := by
  simp only [crossWronskian]
  ring

/-! ## A discrete Gronwall product bound -/

theorem gronwall_exp_bound {G M : ℕ → ℝ} {c : ℝ} {N₁ : ℕ} (hc : 0 ≤ c)
    (hG : ∀ n, 0 ≤ G n)
    (hstep : ∀ n, N₁ ≤ n → G (n + 1) ≤ G n * (1 + 2 * c * M (n + 1) ^ (2 : ℕ)))
    {N : ℕ} (hN : N₁ ≤ N) :
    G N ≤ G N₁ * Real.exp (2 * c * ∑ k ∈ Finset.Ico (N₁ + 1) (N + 1), M k ^ (2 : ℕ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hNN ih =>
      have hsum : ∑ k ∈ Finset.Ico (N₁ + 1) (N + 1 + 1), M k ^ (2 : ℕ)
          = (∑ k ∈ Finset.Ico (N₁ + 1) (N + 1), M k ^ (2 : ℕ)) + M (N + 1) ^ (2 : ℕ) :=
        Finset.sum_Ico_succ_top (by omega) _
      have h1 := hstep N hNN
      have h2 : (1 : ℝ) + 2 * c * M (N + 1) ^ (2 : ℕ) ≤ Real.exp (2 * c * M (N + 1) ^ (2 : ℕ)) := by
        have := Real.add_one_le_exp (2 * c * M (N + 1) ^ (2 : ℕ))
        linarith
      calc G (N + 1) ≤ G N * (1 + 2 * c * M (N + 1) ^ (2 : ℕ)) := h1
        _ ≤ (G N₁ * Real.exp (2 * c * ∑ k ∈ Finset.Ico (N₁ + 1) (N + 1), M k ^ (2 : ℕ)))
              * Real.exp (2 * c * M (N + 1) ^ (2 : ℕ)) := by
            have hpos : (0:ℝ) ≤ Real.exp (2 * c * M (N + 1) ^ (2 : ℕ)) := (Real.exp_pos _).le
            have hb : (0:ℝ) ≤ 1 + 2 * c * M (N + 1) ^ (2 : ℕ) := by positivity
            exact mul_le_mul ih h2 hb (mul_nonneg (hG N₁) (Real.exp_pos _).le)
        _ = G N₁ * Real.exp (2 * c * ∑ k ∈ Finset.Ico (N₁ + 1) (N + 1 + 1), M k ^ (2 : ℕ)) := by
            rw [hsum, mul_assoc, ← Real.exp_add]
            ring_nf


/-- **A discrete Gronwall summability criterion.**  If a nonnegative sequence `w` is dominated by
`G · M` with `M` square-summable, and `G` grows by at most `c · w · M` at each step, then `w` is
square-summable. -/
theorem summable_sq_of_gronwall {G M w : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hG : ∀ n, 0 ≤ G n) (hM : ∀ n, 0 ≤ M n) (hw : ∀ n, 0 ≤ w n)
    (hM2 : Summable fun n => M n ^ (2 : ℕ))
    (hwle : ∀ n, w n ≤ G n * M n)
    (hGstep : ∀ n, G (n + 1) ≤ G n + c * (w (n + 1) * M (n + 1))) :
    Summable fun n => w n ^ (2 : ℕ) := by
  classical
  -- the small-tail index
  have htend : Filter.Tendsto (fun n => c * M n ^ (2 : ℕ)) Filter.atTop (nhds 0) := by
    have := hM2.tendsto_atTop_zero
    simpa using this.const_mul c
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (htend.eventually_le_const (by norm_num : (0:ℝ) < 1 / 2))
  have hstep2 : ∀ n, N₁ ≤ n → G (n + 1) ≤ G n * (1 + 2 * c * M (n + 1) ^ (2 : ℕ)) := by
    intro n hn
    have hx : c * M (n + 1) ^ (2 : ℕ) ≤ 1 / 2 := hN₁ (n + 1) (by omega)
    have hx0 : 0 ≤ c * M (n + 1) ^ (2 : ℕ) := by positivity
    have h1 := hGstep n
    have h2 : w (n + 1) ≤ G (n + 1) * M (n + 1) := hwle (n + 1)
    have h3 : c * (w (n + 1) * M (n + 1)) ≤ c * (G (n + 1) * M (n + 1) ^ (2 : ℕ)) := by
      have : w (n + 1) * M (n + 1) ≤ (G (n + 1) * M (n + 1)) * M (n + 1) :=
        mul_le_mul_of_nonneg_right h2 (hM _)
      nlinarith [hM (n + 1)]
    have hkey : G (n + 1) * (1 - c * M (n + 1) ^ (2 : ℕ)) ≤ G n := by nlinarith
    have hpos : (0:ℝ) ≤ 1 + 2 * (c * M (n + 1) ^ (2 : ℕ)) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hkey hpos
    have hprod : (0:ℝ) ≤ G (n + 1) * (c * M (n + 1) ^ (2 : ℕ) * (1 - 2 * (c * M (n + 1) ^ (2 : ℕ)))) :=
      mul_nonneg (hG (n + 1)) (mul_nonneg hx0 (by linarith))
    nlinarith [hmul, hprod]
  -- Gronwall
  set T : ℝ := ∑' k, M k ^ (2 : ℕ) with hTdef
  have hTb : ∀ N, N₁ ≤ N → (∑ k ∈ Finset.Ico (N₁ + 1) (N + 1), M k ^ (2 : ℕ)) ≤ T :=
    fun N _ => hM2.sum_le_tsum _ (fun i _ => by positivity)
  set C : ℝ := G N₁ * Real.exp (2 * c * T) with hCdef
  have hGle : ∀ N, N₁ ≤ N → G N ≤ C := by
    intro N hN
    refine le_trans (gronwall_exp_bound hc hG hstep2 hN) ?_
    rw [hCdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hG N₁)
    exact mul_le_mul_of_nonneg_left (hTb N hN) (by positivity)
  have hC0 : 0 ≤ C := by
    have := hG N₁
    positivity
  have hfinal : ∀ n, N₁ ≤ n → w n ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * M n ^ (2 : ℕ) := by
    intro n hn
    have h1 : w n ≤ C * M n :=
      le_trans (hwle n) (mul_le_mul_of_nonneg_right (hGle n hn) (hM n))
    have h2 : 0 ≤ w n := hw n
    nlinarith [hM n]
  have htailsum : Summable fun n => w (n + N₁) ^ (2 : ℕ) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hM2.comp_injective (add_left_injective N₁)).mul_left (C ^ (2 : ℕ))))
    exact hfinal (n + N₁) (by omega)
  exact (summable_nat_add_iff N₁).mp htailsum

/-! ## Transfer: a square-summable fundamental system at one parameter -/

/-- **Weyl transfer.**  If some spectral parameter admits a square-summable fundamental system,
then every solution at every spectral parameter is square-summable. -/
theorem summable_sq_of_fundamental
    {z₀ : ℂ} {W : ℂ}
    (hφ : IsJacobiRec a b z₀ φ) (hψ : IsJacobiRec a b z₀ ψ)
    (hu : IsJacobiRec a b z u)
    (hW : W ≠ 0)
    (hWn : ∀ n, (a n : ℂ) * (φ n * ψ (n + 1) - φ (n + 1) * ψ n) = W)
    (hφ2 : Summable fun n => ‖φ n‖ ^ (2 : ℕ)) (hψ2 : Summable fun n => ‖ψ n‖ ^ (2 : ℕ)) :
    Summable fun n => ‖u n‖ ^ (2 : ℕ) := by
  classical
  set M : ℕ → ℝ := fun n => ‖φ n‖ + ‖ψ n‖ with hMdef
  have hM0 : ∀ n, 0 ≤ M n := fun n => by positivity
  have hM2 : Summable fun n => M n ^ (2 : ℕ) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hφ2.mul_left 2).add (hψ2.mul_left 2))
    have : (‖φ n‖ - ‖ψ n‖) ^ (2 : ℕ) ≥ 0 := sq_nonneg _
    simp only [hMdef]
    nlinarith
  set c : ℝ := ‖z - z₀‖ / ‖W‖ with hcdef
  have hc0 : 0 ≤ c := by positivity
  set A : ℕ → ℂ := fun n => -crossWronskian a u ψ n / W with hAdef
  set B : ℕ → ℂ := fun n => crossWronskian a u φ n / W with hBdef
  have hrep : ∀ n, u n = A n * φ n + B n * ψ n := by
    intro n
    have hc := crossWronskian_cramer a φ ψ u n
    rw [hWn n] at hc
    have hAB : A n * φ n + B n * ψ n
        = (-crossWronskian a u ψ n * φ n + crossWronskian a u φ n * ψ n) / W := by
      simp only [hAdef, hBdef]; ring
    rw [hAB, ← hc, mul_div_cancel_left₀ _ hW]
  have hAstep : ∀ n, A (n + 1) - A n = -((z - z₀) * u (n + 1) * ψ (n + 1)) / W := by
    intro n
    have h := crossWronskian_succ hu hψ n
    simp only [hAdef]
    rw [h]
    ring
  have hBstep : ∀ n, B (n + 1) - B n = (z - z₀) * u (n + 1) * φ (n + 1) / W := by
    intro n
    have h := crossWronskian_succ hu hφ n
    simp only [hBdef]
    rw [h]
    ring
  set G : ℕ → ℝ := fun n => ‖A n‖ + ‖B n‖ with hGdef
  have hG0 : ∀ n, 0 ≤ G n := fun n => by positivity
  have hule : ∀ n, ‖u n‖ ≤ G n * M n := by
    intro n
    calc ‖u n‖ = ‖A n * φ n + B n * ψ n‖ := by rw [← hrep n]
      _ ≤ ‖A n * φ n‖ + ‖B n * ψ n‖ := norm_add_le _ _
      _ = ‖A n‖ * ‖φ n‖ + ‖B n‖ * ‖ψ n‖ := by rw [norm_mul, norm_mul]
      _ ≤ G n * M n := by
          simp only [hGdef, hMdef]
          have h1 : (0:ℝ) ≤ ‖A n‖ := norm_nonneg _
          have h2 : (0:ℝ) ≤ ‖B n‖ := norm_nonneg _
          have h3 : (0:ℝ) ≤ ‖φ n‖ := norm_nonneg _
          have h4 : (0:ℝ) ≤ ‖ψ n‖ := norm_nonneg _
          nlinarith
  have hGstep : ∀ n, G (n + 1) ≤ G n + c * (‖u (n + 1)‖ * M (n + 1)) := by
    intro n
    have hA : ‖A (n + 1)‖ ≤ ‖A n‖ + c * (‖u (n + 1)‖ * ‖ψ (n + 1)‖) := by
      have h := hAstep n
      have hnorm : ‖A (n + 1) - A n‖ = c * (‖u (n + 1)‖ * ‖ψ (n + 1)‖) := by
        rw [h, norm_div, norm_neg, norm_mul, norm_mul, hcdef]
        ring
      have := norm_sub_norm_le (A (n + 1)) (A n)
      linarith [hnorm ▸ this]
    have hB : ‖B (n + 1)‖ ≤ ‖B n‖ + c * (‖u (n + 1)‖ * ‖φ (n + 1)‖) := by
      have h := hBstep n
      have hnorm : ‖B (n + 1) - B n‖ = c * (‖u (n + 1)‖ * ‖φ (n + 1)‖) := by
        rw [h, norm_div, norm_mul, norm_mul, hcdef]
        ring
      have := norm_sub_norm_le (B (n + 1)) (B n)
      linarith [hnorm ▸ this]
    simp only [hGdef, hMdef]
    have : c * (‖u (n + 1)‖ * (‖φ (n + 1)‖ + ‖ψ (n + 1)‖))
        = c * (‖u (n + 1)‖ * ‖φ (n + 1)‖) + c * (‖u (n + 1)‖ * ‖ψ (n + 1)‖) := by ring
    linarith
  exact summable_sq_of_gronwall hc0 hG0 hM0 (fun n => norm_nonneg _) hM2 hule hGstep

/-! ## Rigidity at a non-real spectral parameter -/

theorem IsJacobiRec.conj (hu : IsJacobiRec a b z u) :
    IsJacobiRec a b ((starRingEnd ℂ) z) (fun n => (starRingEnd ℂ) (u n)) := by
  intro n
  have h := congrArg (starRingEnd ℂ) (hu n)
  simpa [map_add, map_mul, Complex.conj_ofReal] using h

theorem mul_conj_eq_normSq (w : ℂ) : w * (starRingEnd ℂ) w = ((‖w‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq w

/-- **The self-conjugate cross-Wronskian of a boundary solution.**  It accumulates the partial
square sums exactly. -/
theorem crossWronskian_self_conj (hu : IsJacobiRec a b z u)
    (hbase : (b 0 : ℂ) * u 0 + (a 0 : ℂ) * u 1 = z * u 0) (n : ℕ) :
    crossWronskian a u (fun k => (starRingEnd ℂ) (u k)) n
      = (z - (starRingEnd ℂ) z) * ((∑ k ∈ Finset.range (n + 1), ‖u k‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  induction n with
  | zero =>
      have hb := congrArg (starRingEnd ℂ) hbase
      simp only [map_add, map_mul, Complex.conj_ofReal] at hb
      have h1 : (a 0 : ℂ) * u 1 = (z - (b 0 : ℂ)) * u 0 := by linear_combination hbase
      have h2 : (a 0 : ℂ) * (starRingEnd ℂ) (u 1)
          = ((starRingEnd ℂ) z - (b 0 : ℂ)) * (starRingEnd ℂ) (u 0) := by linear_combination hb
      have hmc := mul_conj_eq_normSq (u 0)
      simp only [crossWronskian]
      have hr : ((∑ k ∈ Finset.range (0 + 1), ‖u k‖ ^ (2 : ℕ) : ℝ) : ℂ) = ((‖u 0‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
        norm_num
      calc (a 0 : ℂ) * (u 1 * (starRingEnd ℂ) (u 0) - u 0 * (starRingEnd ℂ) (u 1))
          = ((a 0 : ℂ) * u 1) * (starRingEnd ℂ) (u 0)
            - u 0 * ((a 0 : ℂ) * (starRingEnd ℂ) (u 1)) := by ring
        _ = (z - (starRingEnd ℂ) z) * (u 0 * (starRingEnd ℂ) (u 0)) := by rw [h1, h2]; ring
        _ = (z - (starRingEnd ℂ) z) * ((‖u 0‖ ^ (2 : ℕ) : ℝ) : ℂ) := by rw [hmc]
        _ = _ := by rw [hr]
  | succ n ih =>
      have hmc := mul_conj_eq_normSq (u (n + 1))
      have hs : ((∑ k ∈ Finset.range (n + 1 + 1), ‖u k‖ ^ (2 : ℕ) : ℝ) : ℂ)
          = ((∑ k ∈ Finset.range (n + 1), ‖u k‖ ^ (2 : ℕ) : ℝ) : ℂ) + ((‖u (n + 1)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
        rw [Finset.sum_range_succ, Complex.ofReal_add]
      rw [crossWronskian_succ hu hu.conj n, ih, hs]
      linear_combination (z - (starRingEnd ℂ) z) * hmc

/-- **Weyl rigidity.**  At a non-real spectral parameter, a single nonzero square-summable solution
obeying the left boundary equation forces *every* solution to be square-summable. -/
theorem summable_sq_of_boundary_solution
    (hu : IsJacobiRec a b z u) (hw : IsJacobiRec a b z w)
    (hbase : (b 0 : ℂ) * u 0 + (a 0 : ℂ) * u 1 = z * u 0)
    (hz : (starRingEnd ℂ) z ≠ z) (hu0 : u 0 ≠ 0)
    (hu2 : Summable fun n => ‖u n‖ ^ (2 : ℕ)) :
    Summable fun n => ‖w n‖ ^ (2 : ℕ) := by
  classical
  set uc : ℕ → ℂ := fun k => (starRingEnd ℂ) (u k) with hucdef
  have huc : IsJacobiRec a b ((starRingEnd ℂ) z) uc := hu.conj
  have hucnorm : ∀ n, ‖uc n‖ = ‖u n‖ := fun n => by
    simp only [hucdef, RCLike.norm_conj]
  have hXeq := crossWronskian_self_conj hu hbase
  set d : ℝ := ‖z - (starRingEnd ℂ) z‖ with hddef
  have hd : 0 < d := by
    rw [hddef, norm_pos_iff, sub_ne_zero]
    exact fun h => hz h.symm
  set δ : ℝ := d * ‖u 0‖ ^ (2 : ℕ) with hδdef
  have hδ : 0 < δ := by
    have : 0 < ‖u 0‖ := norm_pos_iff.mpr hu0
    positivity
  have hXlb : ∀ n, δ ≤ ‖crossWronskian a u uc n‖ := by
    intro n
    have hsum : ‖u 0‖ ^ (2 : ℕ) ≤ ∑ k ∈ Finset.range (n + 1), ‖u k‖ ^ (2 : ℕ) := by
      refine Finset.single_le_sum (f := fun k => ‖u k‖ ^ (2 : ℕ)) (fun i _ => by positivity) ?_
      simp
    have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range (n + 1), ‖u k‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    rw [show crossWronskian a u uc n = crossWronskian a u (fun k => (starRingEnd ℂ) (u k)) n from rfl,
      hXeq n, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, ← hddef, hδdef]
    exact mul_le_mul_of_nonneg_left hsum hd.le
  set Wc : ℂ := crossWronskian a w u 0 with hWcdef
  have hWconst : ∀ n, crossWronskian a w u n = Wc := fun n =>
    crossWronskian_eq_zero_of_const hw hu
  set V : ℕ → ℂ := fun n => crossWronskian a w uc n with hVdef
  have hVstep : ∀ n, V (n + 1) = V n + (z - (starRingEnd ℂ) z) * w (n + 1) * uc (n + 1) := fun n =>
    crossWronskian_succ hw huc n
  have hcram : ∀ n, crossWronskian a u uc n * w n = V n * u n - Wc * uc n := by
    intro n
    have h := crossWronskian_cramer a u uc w n
    have hlhs : (a n : ℂ) * (u n * uc (n + 1) - u (n + 1) * uc n)
        = -crossWronskian a u uc n := by
      simp only [crossWronskian]; ring
    rw [hlhs, hWconst n] at h
    simp only [hVdef]
    linear_combination -h
  set G : ℕ → ℝ := fun n => (‖V n‖ + ‖Wc‖) / δ with hGdef
  have hG : ∀ n, 0 ≤ G n := fun n => by
    simp only [hGdef]
    positivity
  have hwle : ∀ n, ‖w n‖ ≤ G n * ‖u n‖ := by
    intro n
    have h1 : δ * ‖w n‖ ≤ ‖crossWronskian a u uc n‖ * ‖w n‖ :=
      mul_le_mul_of_nonneg_right (hXlb n) (norm_nonneg _)
    have h2 : ‖crossWronskian a u uc n‖ * ‖w n‖ ≤ (‖V n‖ + ‖Wc‖) * ‖u n‖ := by
      rw [← norm_mul, hcram n]
      calc ‖V n * u n - Wc * uc n‖ ≤ ‖V n * u n‖ + ‖Wc * uc n‖ := norm_sub_le _ _
        _ = ‖V n‖ * ‖u n‖ + ‖Wc‖ * ‖u n‖ := by
            rw [norm_mul, norm_mul, hucnorm n]
        _ = (‖V n‖ + ‖Wc‖) * ‖u n‖ := by ring
    have h3 : δ * ‖w n‖ ≤ (‖V n‖ + ‖Wc‖) * ‖u n‖ := le_trans h1 h2
    rw [hGdef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
  have hGstep : ∀ n, G (n + 1) ≤ G n + (d / δ) * (‖w (n + 1)‖ * ‖u (n + 1)‖) := by
    intro n
    have h := hVstep n
    have hnorm : ‖V (n + 1) - V n‖ = d * (‖w (n + 1)‖ * ‖u (n + 1)‖) := by
      rw [show V (n + 1) - V n = (z - (starRingEnd ℂ) z) * w (n + 1) * uc (n + 1) by
        rw [h]; ring, norm_mul, norm_mul, hucnorm (n + 1), ← hddef]
      ring
    have hstep := norm_sub_norm_le (V (n + 1)) (V n)
    rw [hnorm] at hstep
    have key : ‖V (n + 1)‖ + ‖Wc‖
        ≤ (‖V n‖ + ‖Wc‖) + d * (‖w (n + 1)‖ * ‖u (n + 1)‖) := by linarith
    simp only [hGdef]
    rw [div_le_iff₀ hδ]
    have hexp : ((‖V n‖ + ‖Wc‖) / δ + d / δ * (‖w (n + 1)‖ * ‖u (n + 1)‖)) * δ
        = (‖V n‖ + ‖Wc‖) + d * (‖w (n + 1)‖ * ‖u (n + 1)‖) := by
      field_simp
    rw [hexp]
    exact key
  refine summable_sq_of_gronwall (by positivity) hG (fun n => norm_nonneg _)
    (fun n => norm_nonneg _) hu2 hwle hGstep

end GaloisForLFunctions.HTGeometry
