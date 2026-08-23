import GaloisForLFunctions.RHTower.Sieve.AdaptiveGallagherBrunTitchmarsh
import GaloisForLFunctions.RHTower.Sieve.LorentzianMeanSquare

/-!
# The adaptive mean square at bounded height, without a lower prime restriction

Lemma B needs its primes to exceed `T²`.  At the bounded height `T = 2` that excludes only `2` and
`3`, whose Dirichlet polynomial is bounded outright, so splitting the support and paying one factor
`2` from `(a+b)² ≤ 2a² + 2b²` removes the restriction entirely.  This is the form the cell
decomposition of the second reciprocal energy uses, after twisting the coefficients by `q^{-ih}`.
-/

namespace RHTower.Sieve

open Real

noncomputable section

theorem logPoly_union {a : ℕ → ℂ} {s t : Finset ℕ} (h : Disjoint s t) (w : ℝ) :
    logPoly a (s ∪ t) w = logPoly a s w + logPoly a t w := by
  rw [logPoly, logPoly, logPoly, Finset.sum_union h]

/-- The Dirichlet polynomial of a two-element prime head is bounded outright. -/
theorem norm_logPoly_small_le {a : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖a n‖ ≤ 1) {s : Finset ℕ}
    (hs : s ⊆ ({2, 3} : Finset ℕ)) (w : ℝ) :
    ‖logPoly (fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) s w‖ ≤ 2 := by
  classical
  rw [logPoly]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ s,
      ‖(a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ))
        * Complex.exp (((2 * Real.pi * (w * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)‖
        ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    have hp23 : p = 2 ∨ p = 3 := by
      have := hs hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact this
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      rcases hp23 with h | h <;> rw [h] <;> norm_num
    have hlogp : (0 : ℝ) ≤ Real.log p := by
      refine Real.log_nonneg ?_
      rcases hp23 with h | h <;> rw [h] <;> norm_num
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogp, Complex.norm_natCast]
    have hexp : ‖Complex.exp (((2 * Real.pi * (w * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)‖
        = 1 := by
      rw [Complex.norm_exp]
      have hre : (((2 * Real.pi * (w * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I).re = 0 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im]
        ring
      rw [hre, Real.exp_zero]
    rw [hexp, mul_one]
    have hf := hbdd p
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hf (mul_nonneg hlogp hp0.le)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsub : ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ ({2, 3} : Finset ℕ), Real.log (p : ℝ) / (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hs fun i hi _ => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h <;> rw [h] <;> positivity
  refine le_trans hsub ?_
  rw [show ({2, 3} : Finset ℕ) = {2, 3} from rfl]
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have h3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith
  norm_num
  linarith [h2, h3]

/-- **Lemma B at bounded height, with no lower restriction on the primes.**  The primes below `4`
are handled by the trivial bound; everything above `4` is the adaptive mean square at `T = 2`. -/
theorem gallagher_bt_mean_square_all {S : Finset ℕ} (hs : ∀ m ∈ S, Nat.Prime m)
    {a : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖a n‖ ≤ 1) :
    (∫ w in Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi)),
        ‖logPoly (fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ 2)
      ≤ 4500 * ∑ p ∈ S, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) + 8 * (2 / Real.pi) := by
  classical
  set b : ℕ → ℂ := fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ) with hb
  set S₄ : Finset ℕ := S.filter (fun p => 4 ≤ p) with hS₄
  set Sm : Finset ℕ := S.filter (fun p => ¬ 4 ≤ p) with hSm
  have hdisj : Disjoint S₄ Sm := Finset.disjoint_filter_filter_not S S _
  have hunion : S₄ ∪ Sm = S := Finset.filter_union_filter_not_eq _ S
  have hSmsub : Sm ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    rw [hSm, Finset.mem_filter] at hp
    have hpp := hs p hp.1
    have hp2 := hpp.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hpt : ∀ w : ℝ, ‖logPoly b S w‖ ^ 2
      ≤ 2 * ‖logPoly b S₄ w‖ ^ 2 + 2 * 4 := by
    intro w
    have hsplit : logPoly b S w = logPoly b S₄ w + logPoly b Sm w := by
      rw [← hunion, logPoly_union hdisj]
    have hsm : ‖logPoly b Sm w‖ ≤ 2 := norm_logPoly_small_le hbdd hSmsub w
    have hnorm : ‖logPoly b S w‖ ≤ ‖logPoly b S₄ w‖ + ‖logPoly b Sm w‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    have hA := norm_nonneg (logPoly b S₄ w)
    have hBn := norm_nonneg (logPoly b Sm w)
    have hC := norm_nonneg (logPoly b S w)
    have hsq : ‖logPoly b S w‖ ^ 2 ≤ (‖logPoly b S₄ w‖ + ‖logPoly b Sm w‖) ^ 2 := by
      nlinarith [hnorm, hC]
    have hexpand : (‖logPoly b S₄ w‖ + ‖logPoly b Sm w‖) ^ 2
        ≤ 2 * ‖logPoly b S₄ w‖ ^ 2 + 2 * ‖logPoly b Sm w‖ ^ 2 := by
      nlinarith [sq_nonneg (‖logPoly b S₄ w‖ - ‖logPoly b Sm w‖)]
    have hsm2 : ‖logPoly b Sm w‖ ^ 2 ≤ 4 := by nlinarith [hsm, hBn]
    linarith
  have hint1 : MeasureTheory.IntegrableOn (fun w : ℝ => ‖logPoly b S w‖ ^ 2)
      (Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi))) :=
    (continuous_normSq_logPoly b S).continuousOn.integrableOn_Icc
  have hint2 : MeasureTheory.IntegrableOn
      (fun w : ℝ => 2 * ‖logPoly b S₄ w‖ ^ 2 + 2 * 4)
      (Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi))) :=
    (((continuous_normSq_logPoly b S₄).const_smul (2 : ℝ)).add continuous_const).continuousOn.integrableOn_Icc
  have hmono : (∫ w in Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi)), ‖logPoly b S w‖ ^ 2)
      ≤ ∫ w in Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi)),
          (2 * ‖logPoly b S₄ w‖ ^ 2 + 2 * 4) :=
    MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun w _ => hpt w)
  refine le_trans hmono ?_
  have hconst : (∫ _w in Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi)), (2 * 4 : ℝ))
      = 8 * (2 / Real.pi) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hnn : (0 : ℝ) ≤ 2 / (2 * Real.pi) - -(2 / (2 * Real.pi)) := by
      have h : (0 : ℝ) < 2 / (2 * Real.pi) := by positivity
      linarith
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal hnn]
    field_simp
    ring
  have hsplitint : (∫ w in Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi)),
      (2 * ‖logPoly b S₄ w‖ ^ 2 + 2 * 4))
      = 2 * (∫ w in Set.Icc (-(2 / (2 * Real.pi))) (2 / (2 * Real.pi)), ‖logPoly b S₄ w‖ ^ 2)
        + 8 * (2 / Real.pi) := by
    rw [MeasureTheory.integral_add
        ((continuous_normSq_logPoly b S₄).continuousOn.integrableOn_Icc.const_mul 2)
        (continuous_const.continuousOn.integrableOn_Icc),
      MeasureTheory.integral_const_mul, hconst]
  rw [hsplitint]
  have hB := gallagher_bt_mean_square_coeff (T := 2) (by norm_num)
    (fun m hm => hs m (Finset.mem_of_mem_filter m hm))
    (fun m hm => by
      have h4 : 4 ≤ m := (Finset.mem_filter.mp hm).2
      have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h4
      norm_num
      linarith) a
  have hsub : ∑ p ∈ S₄, ‖a p‖ ^ 2 * Real.log p / (p : ℝ)
      ≤ ∑ p ∈ S, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i hi _ => ?_
    have hpp := hs i hi
    have hp0 : (0 : ℝ) < (i : ℝ) := by
      have := hpp.two_le
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two this
    have hlogp : (0 : ℝ) ≤ Real.log i := Real.log_nonneg (by
      have := hpp.two_le
      have : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
      linarith)
    positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hB, hsub]

end

end RHTower.Sieve
