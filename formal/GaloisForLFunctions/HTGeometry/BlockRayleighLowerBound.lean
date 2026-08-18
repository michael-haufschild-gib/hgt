import GaloisForLFunctions.HTGeometry.BlockAverageAntiConcentration
import GaloisForLFunctions.HTGeometry.AtomicMomentHankelSection

/-!
# A Rayleigh floor from block masses

The block anti-concentration bound says a polynomial whose weighted block averages are small has
small coefficients.  Cauchy--Schwarz turns each block average into the square root of the block
energy, so a lower bound on the block masses converts the bound into a **Rayleigh floor** for the
total weighted nodal energy — which is exactly the quadratic form of the atomic Hankel section.

Together with `exists_solve_atomicHankel` this solves the interpolation system with an explicit
size bound on the solution, which is the analytic content of Andersson's Lemma 4.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The aggregate fixed-node coefficient constant. -/
def unitCoeffConstSum (J : ℕ) : ℝ := ∑ k : Fin J, unitCoeffConst J (k : ℕ)

theorem unitCoeffConst_le_sum {J : ℕ} (k : Fin J) :
    unitCoeffConst J (k : ℕ) ≤ unitCoeffConstSum J := by
  rw [unitCoeffConstSum]
  exact Finset.single_le_sum (f := fun j : Fin J => unitCoeffConst J (j : ℕ))
    (fun j _ => unitCoeffConst_nonneg J (j : ℕ)) (Finset.mem_univ k)

theorem unitCoeffConstSum_nonneg (J : ℕ) : 0 ≤ unitCoeffConstSum J :=
  Finset.sum_nonneg fun k _ => unitCoeffConst_nonneg J (k : ℕ)

/-- **The Rayleigh floor.**  Block masses at least `m` force the weighted nodal energy to dominate
the squared coefficient vector. -/
theorem rayleigh_lower_of_blocks {N J : ℕ} (hJ : 0 < J) {η m : ℝ} (hη : 0 < η) (hm : 0 < m)
    (a b : Fin J → ℝ)
    (hIcc : ∀ i : Fin J, ∀ t ∈ Set.Icc (a i) (b i), t ∈ Set.Icc (0:ℝ) 1)
    (hsep : ∀ i k : Fin J, i ≠ k → ∀ s ∈ Set.Icc (a i) (b i), ∀ u ∈ Set.Icc (a k) (b k),
      η ≤ |s - u|)
    (x w : Fin N → ℝ) (hw : ∀ r, 0 < w r)
    (B : Fin J → Finset (Fin N)) (hBne : ∀ i, (B i).Nonempty)
    (hBmem : ∀ i : Fin J, ∀ r ∈ B i, x r ∈ Set.Icc (a i) (b i))
    (hBmass : ∀ i, m ≤ ∑ r ∈ B i, w r)
    (c : Fin J → ℝ) :
    (m / ((J : ℝ) * (2 * (((J : ℝ)) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial))))
        * unitCoeffConstSum J) ^ 2)) * (∑ k, c k ^ 2)
      ≤ ∑ r, w r * (Polynomial.eval (x r) (Polynomial.ofFn J c)) ^ 2 := by
  classical
  set P : Polynomial ℝ := Polynomial.ofFn J c with hPdef
  set E : ℝ := ∑ r, w r * (Polynomial.eval (x r) P) ^ 2 with hEdef
  set Kc : ℝ := ((J : ℝ)) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial))) with hKcdef
  set U : ℝ := unitCoeffConstSum J with hUdef
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun r _ => mul_nonneg (hw r).le (sq_nonneg _)
  set ε : ℝ := Real.sqrt (E / m) with hepsdef
  have heps0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hepssq : ε ^ 2 = E / m := Real.sq_sqrt (by positivity)
  -- each block average is at most `ε` times the block mass
  have hblock : ∀ i : Fin J,
      |∑ r ∈ B i, w r * Polynomial.eval (x r) P| ≤ ε * ∑ r ∈ B i, w r := by
    intro i
    have hWi : 0 < ∑ r ∈ B i, w r := lt_of_lt_of_le hm (hBmass i)
    have hCS : (∑ r ∈ B i, Polynomial.eval (x r) P * w r) ^ 2
        ≤ (∑ r ∈ B i, (Polynomial.eval (x r) P) ^ 2 * w r) * ∑ r ∈ B i, w r := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (B i)
        (fun r => Polynomial.eval (x r) P * Real.sqrt (w r)) (fun r => Real.sqrt (w r))
      have hL : ∀ r ∈ B i, (Polynomial.eval (x r) P * Real.sqrt (w r)) * Real.sqrt (w r)
          = Polynomial.eval (x r) P * w r := by
        intro r _
        rw [mul_assoc, Real.mul_self_sqrt (hw r).le]
      have hL2 : ∀ r ∈ B i, (Polynomial.eval (x r) P * Real.sqrt (w r)) ^ 2
          = (Polynomial.eval (x r) P) ^ 2 * w r := by
        intro r _
        rw [mul_pow, Real.sq_sqrt (hw r).le]
      have hR2 : ∀ r ∈ B i, (Real.sqrt (w r)) ^ 2 = w r := by
        intro r _
        rw [Real.sq_sqrt (hw r).le]
      rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hL2, Finset.sum_congr rfl hR2] at h
      exact h
    have hEblock : ∑ r ∈ B i, (Polynomial.eval (x r) P) ^ 2 * w r ≤ E := by
      rw [hEdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_ |>.trans_eq ?_
      · intro r _ _
        exact mul_nonneg (sq_nonneg _) (hw r).le
      · exact Finset.sum_congr rfl fun r _ => by ring
    have hsq : (∑ r ∈ B i, w r * Polynomial.eval (x r) P) ^ 2 ≤ (ε * ∑ r ∈ B i, w r) ^ 2 := by
      have hcomm : ∑ r ∈ B i, w r * Polynomial.eval (x r) P
          = ∑ r ∈ B i, Polynomial.eval (x r) P * w r :=
        Finset.sum_congr rfl fun r _ => mul_comm _ _
      rw [hcomm, mul_pow, hepssq]
      have hstep : (∑ r ∈ B i, Polynomial.eval (x r) P * w r) ^ 2 ≤ E * ∑ r ∈ B i, w r := by
        refine hCS.trans ?_
        exact mul_le_mul_of_nonneg_right hEblock hWi.le
      have hmass : m ≤ ∑ r ∈ B i, w r := hBmass i
      have hfinal : E * ∑ r ∈ B i, w r ≤ E / m * (∑ r ∈ B i, w r) ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm]
        nlinarith [hE0, hWi, hmass]
      exact hstep.trans hfinal
    have hnn : (0:ℝ) ≤ ε * ∑ r ∈ B i, w r := by positivity
    nlinarith [hsq, abs_nonneg (∑ r ∈ B i, w r * Polynomial.eval (x r) P),
      sq_abs (∑ r ∈ B i, w r * Polynomial.eval (x r) P), hnn]
  -- transport to the complex anti-concentration bound
  have hcast : ∀ i : Fin J,
      ‖∑ r ∈ B i, ((w r : ℝ) : ℂ) * ∑ k : Fin J, ((c k : ℝ) : ℂ) * ((x r : ℝ) : ℂ) ^ (k : ℕ)‖
        ≤ ε * ∑ r ∈ B i, w r := by
    intro i
    have hinner : ∀ r : Fin N,
        ((w r : ℝ) : ℂ) * ∑ k : Fin J, ((c k : ℝ) : ℂ) * ((x r : ℝ) : ℂ) ^ (k : ℕ)
          = (((w r * Polynomial.eval (x r) P : ℝ)) : ℂ) := by
      intro r
      have hev : Polynomial.eval (x r) P = ∑ k : Fin J, c k * x r ^ (k : ℕ) := by
        rw [hPdef, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
        exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_monomial]
      rw [hev]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun r _ => hinner r, ← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_eq_abs]
    exact hblock i
  have hcoeff : ∀ k : Fin J, |c k| ≤ 2 * (Kc * U) * ε := by
    intro k
    have hres := norm_le_of_block_averages (ι := Fin N) hJ hη a b hIcc hsep x w B hBne hBmem
      (fun _ r _ => hw r) (fun k => ((c k : ℝ) : ℂ)) hcast k
    rw [Complex.norm_real, Real.norm_eq_abs] at hres
    refine hres.trans ?_
    have hKc0 : 0 ≤ Kc := by
      rw [hKcdef]
      positivity
    have hmono : unitCoeffConst J (k : ℕ) ≤ U := by
      rw [hUdef]
      exact unitCoeffConst_le_sum k
    have : 2 * (Kc * unitCoeffConst J (k : ℕ)) ≤ 2 * (Kc * U) := by
      have := mul_le_mul_of_nonneg_left hmono hKc0
      linarith
    exact mul_le_mul_of_nonneg_right this heps0
  -- assemble
  have hCsum : ∑ k, c k ^ 2 ≤ (J : ℝ) * (2 * Kc * U) ^ 2 * ε ^ 2 := by
    have hterm : ∀ k : Fin J, c k ^ 2 ≤ (2 * Kc * U) ^ 2 * ε ^ 2 := by
      intro k
      have h1 := hcoeff k
      have h2 : |c k| ^ 2 = c k ^ 2 := sq_abs _
      nlinarith [abs_nonneg (c k), h1]
    calc ∑ k, c k ^ 2 ≤ ∑ _k : Fin J, (2 * Kc * U) ^ 2 * ε ^ 2 :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (J : ℝ) * (2 * Kc * U) ^ 2 * ε ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hden : (0:ℝ) < (J : ℝ) * (2 * Kc * U) ^ 2 ∨ (2 * Kc * U) = 0 := by
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (2 * Kc * U) ^ 2) with h | h
    · right
      have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h.symm
      exact this
    · left
      have hJ0 : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
      exact mul_pos hJ0 h
  rcases hden with hpos | hzero
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := hCsum
    rw [hepssq] at this
    have hJ0 : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    calc m * ∑ k, c k ^ 2
        ≤ m * ((J : ℝ) * (2 * Kc * U) ^ 2 * (E / m)) :=
          mul_le_mul_of_nonneg_left this hm.le
      _ = E * ((J : ℝ) * (2 * Kc * U) ^ 2) := by field_simp
  · have hz : ∑ k, c k ^ 2 ≤ 0 := by
      have := hCsum
      rw [hzero] at this
      simpa using this
    have hz0 : ∑ k, c k ^ 2 = 0 :=
      le_antisymm hz (Finset.sum_nonneg fun k _ => sq_nonneg _)
    rw [hz0, mul_zero]
    exact hE0

end GaloisForLFunctions.HTGeometry

end
