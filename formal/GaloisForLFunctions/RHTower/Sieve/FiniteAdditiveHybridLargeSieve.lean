import GaloisForLFunctions.RHTower.ChenGuptaLiHybridCharacterMeanSquare
import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveLargeSieve

/-!
# Continuous hybrid additive large sieve

Exact additive-character Parseval splits a logarithmic Dirichlet polynomial into residue fibres.
Gallagher's mean-square estimate on each sparse fibre then gives the hybrid `(N + qT)` scale used
in the Deshouillers--Iwaniec treatment of Kloosterman quadratic forms.
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

/-- Positive integers in `[1,N]` with a fixed residue modulo `q + 1`. -/
def additiveResidueInterval (q N : ℕ) (r : ZMod (q + 1)) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun n : ℕ => (Nat.cast n : ZMod (q + 1)) = r)

/-- Logarithmic Dirichlet polynomial with one additive frequency modulo `q + 1`. -/
def additiveHybridLogPoly (q N : ℕ) (a : ℕ → ℂ)
    (d : ZMod (q + 1)) (w : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    a n * Complex.exp
      (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) *
      ZMod.stdAddChar (d * (Nat.cast n : ZMod (q + 1)))

theorem continuous_additiveHybridLogPoly (q N : ℕ) (a : ℕ → ℂ)
    (d : ZMod (q + 1)) :
    Continuous (additiveHybridLogPoly q N a d) := by
  unfold additiveHybridLogPoly
  refine continuous_finsetSum _ fun n _ => ?_
  fun_prop

/-- The additive polynomial is the finite Fourier transform of its residue-fibre polynomials. -/
theorem additiveHybridLogPoly_eq_sum_residues
    (q N : ℕ) (a : ℕ → ℂ) (d : ZMod (q + 1)) (w : ℝ) :
    additiveHybridLogPoly q N a d w =
      ∑ r : ZMod (q + 1), logPoly a (additiveResidueInterval q N r) w *
        ZMod.stdAddChar (d * r) := by
  unfold additiveHybridLogPoly
  rw [← Finset.sum_fiberwise (Finset.Icc 1 N)
    (fun n : ℕ => (Nat.cast n : ZMod (q + 1)))
    (fun n => a n * Complex.exp
      (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) *
      ZMod.stdAddChar (d * (Nat.cast n : ZMod (q + 1))))]
  apply Finset.sum_congr rfl
  intro r _
  unfold additiveResidueInterval logPoly
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnr : (Nat.cast n : ZMod (q + 1)) = r := (Finset.mem_filter.1 hn).2
  rw [hnr]

/-- Pointwise hybrid additive Parseval identity. -/
theorem sum_normSq_additiveHybridLogPoly
    (q N : ℕ) (a : ℕ → ℂ) (w : ℝ) :
    ∑ d : ZMod (q + 1), ‖additiveHybridLogPoly q N a d w‖ ^ (2 : ℕ) =
      ((q + 1 : ℕ) : ℝ) *
        ∑ r : ZMod (q + 1), ‖logPoly a (additiveResidueInterval q N r) w‖ ^ (2 : ℕ) := by
  letI : NeZero (q + 1) := ⟨by omega⟩
  simp_rw [additiveHybridLogPoly_eq_sum_residues]
  simpa only [Complex.normSq_eq_norm_sq] using
    sum_normSq_weighted_stdAddChar_mul_of_injective (q + 1)
      (fun r : ZMod (q + 1) => r) Function.injective_id
      (fun r => logPoly a (additiveResidueInterval q N r) w)

/-- Continuous hybrid additive large sieve before choosing the logarithmic localization width. -/
theorem sum_integral_normSq_additiveHybridLogPoly_le
    (q N : ℕ) (a : ℕ → ℂ) {δ W : ℝ}
    (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    ∑ d : ZMod (q + 1),
        (∫ w in Set.Icc (-W) W, ‖additiveHybridLogPoly q N a d w‖ ^ (2 : ℕ))
      ≤ ((q + 1 : ℕ) : ℝ) * (5 / (4 * δ)) *
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
            ‖a n‖ ^ (2 : ℕ) := by
  classical
  let I : Set ℝ := Set.Icc (-W) W
  have hdint : ∀ d : ZMod (q + 1),
      Integrable (fun w => ‖additiveHybridLogPoly q N a d w‖ ^ (2 : ℕ))
        (volume.restrict I) := by
    intro d
    exact (continuous_additiveHybridLogPoly q N a d).norm.pow 2 |>.integrableOn_Icc
  have hrint : ∀ r : ZMod (q + 1),
      Integrable (fun w => ‖logPoly a (additiveResidueInterval q N r) w‖ ^ (2 : ℕ))
        (volume.restrict I) := by
    intro r
    exact (continuous_logPoly a (additiveResidueInterval q N r)).norm.pow 2
      |>.integrableOn_Icc
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun d _ => hdint d)]
  change (∫ w in I, ∑ d : ZMod (q + 1),
      ‖additiveHybridLogPoly q N a d w‖ ^ (2 : ℕ)) ≤ _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun w _ => sum_normSq_additiveHybridLogPoly q N a w)]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun r _ => hrint r)]
  have hrbound : ∀ r : ZMod (q + 1),
      (∫ w in I, ‖logPoly a (additiveResidueInterval q N r) w‖ ^ (2 : ℕ)) ≤
        (5 / (4 * δ)) * ∑ n ∈ additiveResidueInterval q N r,
          ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
            ‖a n‖ ^ (2 : ℕ) := by
    intro r
    have hs0 : (0 : ℕ) ∉ additiveResidueInterval q N r := by
      simp [additiveResidueInterval]
    have hres : ∀ n ∈ additiveResidueInterval q N r,
        n % (q + 1) = r.val := by
      intro n hn
      have hcast := (Finset.mem_filter.1 hn).2
      rw [← ZMod.val_natCast, hcast]
    exact integral_Icc_normSq_logPoly_le_residue a
      (additiveResidueInterval q N r) (by omega : 0 < q + 1)
      r.val hs0 hres hδ hWδ
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hrbound r)
  have hfac0 : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hfac0) ?_
  let g : ℕ → ℝ := fun n =>
    ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) * ‖a n‖ ^ (2 : ℕ)
  have hfib : ∑ r : ZMod (q + 1), ∑ n ∈ additiveResidueInterval q N r, g n =
      ∑ n ∈ Finset.Icc 1 N, g n := by
    simpa only [additiveResidueInterval] using
      (Finset.sum_fiberwise (Finset.Icc 1 N)
        (fun n : ℕ => (Nat.cast n : ZMod (q + 1))) g)
  dsimp only [g] at hfib
  calc
    ((q + 1 : ℕ) : ℝ) *
        ∑ r : ZMod (q + 1), (5 / (4 * δ)) *
          ∑ n ∈ additiveResidueInterval q N r,
            ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) /
                ((q + 1 : ℕ) : ℝ) + 2) * ‖a n‖ ^ (2 : ℕ) =
      ((q + 1 : ℕ) : ℝ) * (5 / (4 * δ)) *
        ∑ r : ZMod (q + 1),
          ∑ n ∈ additiveResidueInterval q N r,
            ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) /
                ((q + 1 : ℕ) : ℝ) + 2) * ‖a n‖ ^ (2 : ℕ) := by
        rw [← Finset.mul_sum]
        ring
    _ = ((q + 1 : ℕ) : ℝ) * (5 / (4 * δ)) *
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) /
              ((q + 1 : ℕ) : ℝ) + 2) * ‖a n‖ ^ (2 : ℕ) := by rw [hfib]
    _ ≤ _ := le_rfl

/-- Affine hybrid additive mean square on the natural height scale. -/
theorem sum_integral_normSq_additiveHybridLogPoly_le_affine
    (q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    ∑ d : ZMod (q + 1),
        (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖additiveHybridLogPoly q N a d w‖ ^ (2 : ℕ))
      ≤ (5 * Real.exp 1 / 2) *
          ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ (2 : ℕ)
        + (5 / 2) * ((q + 1 : ℕ) : ℝ) * T *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  refine le_trans (sum_integral_normSq_additiveHybridLogPoly_le q N a hδ hWδ) ?_
  set E0 : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ) with hE0def
  set E1 : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ (2 : ℕ) with hE1def
  have hE0 : 0 ≤ E0 := by rw [hE0def]; positivity
  have hE1 : 0 ≤ E1 := by rw [hE1def]; positivity
  have hsplit : ∑ n ∈ Finset.Icc 1 N,
      ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) /
          ((q + 1 : ℕ) : ℝ) + 2) * ‖a n‖ ^ (2 : ℕ)
      = (Real.exp (1 / T) - Real.exp (-(1 / T))) /
          ((q + 1 : ℕ) : ℝ) * E1 + 2 * E0 := by
    rw [hE0def, hE1def, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit]
  have hwindow := mul_exp_sub_exp_neg_le hT
  have hcoef : 5 / (4 * (1 / T)) = 5 * T / 4 := by field_simp
  rw [hcoef]
  have hmain : ((q + 1 : ℕ) : ℝ) * (5 * T / 4) *
      ((Real.exp (1 / T) - Real.exp (-(1 / T))) /
        ((q + 1 : ℕ) : ℝ) * E1) ≤ (5 * Real.exp 1 / 2) * E1 := by
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwindow (by norm_num : (0 : ℝ) ≤ 5 / 4)) hE1
    calc
      _ = (5 / 4) * (T * (Real.exp (1 / T) - Real.exp (-(1 / T)))) * E1 := by
        field_simp
      _ ≤ (5 / 4) * (2 * Real.exp 1) * E1 := hscaled
      _ = _ := by ring
  calc
    ((q + 1 : ℕ) : ℝ) * (5 * T / 4) *
        ((Real.exp (1 / T) - Real.exp (-(1 / T))) /
          ((q + 1 : ℕ) : ℝ) * E1 + 2 * E0)
      = ((q + 1 : ℕ) : ℝ) * (5 * T / 4) *
          ((Real.exp (1 / T) - Real.exp (-(1 / T))) /
            ((q + 1 : ℕ) : ℝ) * E1)
        + (5 / 2) * ((q + 1 : ℕ) : ℝ) * T * E0 := by ring
    _ ≤ (5 * Real.exp 1 / 2) * E1 +
        (5 / 2) * ((q + 1 : ℕ) : ℝ) * T * E0 :=
      add_le_add hmain (le_refl _)

/-- Closed `(N + qT)` form of the continuous hybrid additive large sieve. -/
theorem sum_integral_normSq_additiveHybridLogPoly_le_length
    (q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    ∑ d : ZMod (q + 1),
        (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖additiveHybridLogPoly q N a d w‖ ^ (2 : ℕ))
      ≤ ((5 * Real.exp 1 / 2) * (N : ℝ) +
          (5 / 2) * ((q + 1 : ℕ) : ℝ) * T) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ) := by
  refine le_trans (sum_integral_normSq_additiveHybridLogPoly_le_affine q N a hT) ?_
  have hweighted : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ (2 : ℕ)
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.1 hn).2) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hweighted
    (by positivity : (0 : ℝ) ≤ 5 * Real.exp 1 / 2)
  calc
    _ ≤ (5 * Real.exp 1 / 2) *
          ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ))
        + (5 / 2) * ((q + 1 : ℕ) : ℝ) * T *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ) := add_le_add hscaled (le_refl _)
    _ = _ := by ring

end RHTower.Sieve
