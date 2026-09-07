import GaloisForLFunctions.RHTower.Sieve.DirichletDiagonal
import GaloisForLFunctions.HTGeometry.RiemannGaussian.MontgomeryVaughan.Final

/-!
# The sharp Montgomery–Vaughan mean value theorem for Dirichlet polynomials

`|∫_0^T |F(t)|² dt − T ∑_{n<N} |a_n|²| ≤ 104 ∑_{n<N} (n+1) |a_n|²`

for `F(t) = ∑_{n<N} a_n (n+1)^{it}`.  The off-diagonal of the expanded mean square is the
difference of two bilinear Hilbert forms at the frequencies `log(n+1)`, with admissible gaps
`1/(2(n+1))`; the corpus's Montgomery–Vaughan inequality `MVHilbert 26` bounds each by
`52 ∑ (n+1)|a_n|²`.  This replaces the elementary `O(N log N ∑|a_n|²)` of `DirichletMVT.lean`
by the error `O(∑ n |a_n|²)` needed for infinite Dirichlet series.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Complex

/-- The frequencies `log(m+1)` are injective. -/
theorem logSucc_fin_injective (N : ℕ) :
    Function.Injective (fun m : Fin N => Real.log (((m : ℕ) : ℝ) + 1)) := by
  intro m n h
  have h' := Real.log_injOn_pos (by simp; positivity) (by simp; positivity) h
  have : ((m : ℕ) : ℝ) = n := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- `log y ≥ 1 − 1/y` for `y > 0`. -/
theorem one_sub_inv_le_log {y : ℝ} (hy : 0 < y) : 1 - 1 / y ≤ Real.log y := by
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at this
  rw [one_div]; linarith

/-- The admissible gap `1/(2(m+1)) ≤ |log(m+1) − log(n+1)|` for `m ≠ n`. -/
theorem gap_log_succ {m n : ℕ} (h : m ≠ n) :
    1 / (2 * (((m : ℕ) : ℝ) + 1)) ≤ |Real.log (((m : ℕ) : ℝ) + 1) - Real.log (((n : ℕ) : ℝ) + 1)| := by
  rcases lt_or_gt_of_ne h with hmn | hmn
  · -- `m < n`: `log(n+1) − log(m+1) ≥ log((m+2)/(m+1)) ≥ 1/(m+2)`
    have hle : ((m : ℕ) : ℝ) + 2 ≤ ((n : ℕ) : ℝ) + 1 := by
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
      linarith
    have h1 : Real.log (((m : ℕ) : ℝ) + 2) ≤ Real.log (((n : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) hle
    have h2 : 1 - 1 / ((((m : ℕ) : ℝ) + 2) / (((m : ℕ) : ℝ) + 1))
        ≤ Real.log ((((m : ℕ) : ℝ) + 2) / (((m : ℕ) : ℝ) + 1)) :=
      one_sub_inv_le_log (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h2
    have h3 : 1 - 1 / ((((m : ℕ) : ℝ) + 2) / (((m : ℕ) : ℝ) + 1)) = 1 / (((m : ℕ) : ℝ) + 2) := by
      field_simp; ring
    rw [h3] at h2
    have h4 : 1 / (2 * (((m : ℕ) : ℝ) + 1)) ≤ 1 / (((m : ℕ) : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h5 : 0 < 1 / (((m : ℕ) : ℝ) + 2) := by positivity
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · -- `n < m`: `log(m+1) − log(n+1) ≥ log((m+1)/m) ≥ 1/(m+1)`
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have hle : ((n : ℕ) : ℝ) + 1 ≤ ((m : ℕ) : ℝ) := by
      have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hmn
      linarith
    have h1 : Real.log (((n : ℕ) : ℝ) + 1) ≤ Real.log ((m : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hle
    have h2 : 1 - 1 / ((((m : ℕ) : ℝ) + 1) / ((m : ℕ) : ℝ))
        ≤ Real.log ((((m : ℕ) : ℝ) + 1) / ((m : ℕ) : ℝ)) :=
      one_sub_inv_le_log (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h2
    have h3 : 1 - 1 / ((((m : ℕ) : ℝ) + 1) / ((m : ℕ) : ℝ)) = 1 / (((m : ℕ) : ℝ) + 1) := by
      field_simp; ring
    rw [h3] at h2
    have h4 : 1 / (2 * (((m : ℕ) : ℝ) + 1)) ≤ 1 / (((m : ℕ) : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h5 : 0 < 1 / (((m : ℕ) : ℝ) + 1) := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The off-diagonal double sum with `erase` equals the `if r = s then 0` form. -/
theorem sum_erase_eq_sum_ite {N : ℕ} (f : Fin N → Fin N → ℂ) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, f m n
      = ∑ m : Fin N, ∑ n : Fin N, if m = n then 0 else f m n := by
  classical
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_erase (Finset.univ) (a := m) (by simp)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_erase] at hn
  rw [if_neg (Ne.symm hn.1)]

/-- **The sharp mean value theorem.** -/
theorem dirichlet_meanValue_sharp (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2) - T * ∑ m : Fin N, ‖a m‖ ^ 2|
      ≤ 104 * ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2 := by
  classical
  set freq : Fin N → ℝ := fun m => Real.log (((m : ℕ) : ℝ) + 1) with hfreq
  set δ : Fin N → ℝ := fun m => 1 / (2 * (((m : ℕ) : ℝ) + 1)) with hδ
  set x1 : Fin N → ℂ := fun m => a m * Complex.exp (((T * freq m : ℝ) : ℂ) * Complex.I) with hx1
  set E : ℝ := ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2 with hE
  -- the complex form of the left-hand side
  have hcast : (∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ 2 : ℝ) : ℂ))
      - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ 2 : ℝ) : ℂ)
      = ((((∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2) - T * ∑ m : Fin N, ‖a m‖ ^ 2 : ℝ)) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hcast, integral_normSq_dirPoly_sub_diag,
    sum_erase_eq_sum_ite]
  -- the off-diagonal phase integrals
  have hterm : ∀ m n : Fin N, m ≠ n →
      (a m * (starRingEnd ℂ) (a n))
        * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
            - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
      = Complex.I⁻¹ * (x1 m * (starRingEnd ℂ) (x1 n) / ((freq m - freq n : ℝ) : ℂ)
          - a m * (starRingEnd ℂ) (a n) / ((freq m - freq n : ℝ) : ℂ)) := by
    intro m n hmn
    have hL : freq m - freq n ≠ 0 := sub_ne_zero.mpr ((logSucc_fin_injective N).ne hmn)
    have hconj : (starRingEnd ℂ) (x1 n)
        = (starRingEnd ℂ) (a n) * Complex.exp (-(((T * freq n : ℝ) : ℂ) * Complex.I)) := by
      simp only [hx1, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    have hexp : Complex.exp (((T * (freq m - freq n) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((T * freq m : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-(((T * freq n : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hL' : ((freq m - freq n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    rw [integral_exp_phase _ hL T, hconj, hexp]
    simp only [hx1]
    field_simp
  have hite : ∀ m n : Fin N,
      (if m = n then (0 : ℂ) else (a m * (starRingEnd ℂ) (a n))
        * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
            - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)))
      = Complex.I⁻¹ * ((if m = n then 0 else x1 m * (starRingEnd ℂ) (x1 n) / ((freq m - freq n : ℝ) : ℂ))
          - (if m = n then 0 else a m * (starRingEnd ℂ) (a n) / ((freq m - freq n : ℝ) : ℂ))) := by
    intro m n
    split_ifs with h
    · simp
    · exact hterm m n h
  rw [Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => hite m n]
  -- assemble the two bilinear forms
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [norm_mul, norm_inv, Complex.norm_I, inv_one, one_mul]
  have hMV := RiemannGaussian.MontgomeryVaughan.mvHilbert_twentySix
  have hinj : Function.Injective freq := logSucc_fin_injective N
  have hδpos : ∀ r, 0 < δ r := fun r => by simp only [hδ]; positivity
  have hgap : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s| := fun r s hrs =>
    gap_log_succ (fun h => hrs (Fin.ext h))
  have h1 := hMV (Fin N) freq δ x1 x1 hinj hδpos hgap
  have h2 := hMV (Fin N) freq δ a a hinj hδpos hgap
  have hnx1 : ∀ m, ‖x1 m‖ = ‖a m‖ := fun m => by
    simp only [hx1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum : ∀ f : Fin N → ℂ, (∀ m, ‖f m‖ = ‖a m‖) → ∑ r, ‖f r‖ ^ 2 / δ r = 2 * E := by
    intro f hf
    simp only [hE, Finset.mul_sum, hδ, hf]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun m _ => by positivity
  have hs1 := hsum x1 hnx1
  have hs2 := hsum a (fun _ => rfl)
  rw [hs1] at h1
  rw [hs2] at h2
  have hsq : Real.sqrt (2 * E) * Real.sqrt (2 * E) = 2 * E := Real.mul_self_sqrt (by linarith)
  calc ‖(∑ m : Fin N, ∑ n : Fin N, if m = n then (0 : ℂ)
          else x1 m * (starRingEnd ℂ) (x1 n) / ((freq m - freq n : ℝ) : ℂ))
        - ∑ m : Fin N, ∑ n : Fin N, if m = n then (0 : ℂ)
          else a m * (starRingEnd ℂ) (a n) / ((freq m - freq n : ℝ) : ℂ)‖
      ≤ ‖∑ m : Fin N, ∑ n : Fin N, if m = n then (0 : ℂ)
          else x1 m * (starRingEnd ℂ) (x1 n) / ((freq m - freq n : ℝ) : ℂ)‖
        + ‖∑ m : Fin N, ∑ n : Fin N, if m = n then (0 : ℂ)
          else a m * (starRingEnd ℂ) (a n) / ((freq m - freq n : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 26 * Real.sqrt (2 * E) * Real.sqrt (2 * E) + 26 * Real.sqrt (2 * E) * Real.sqrt (2 * E) :=
        add_le_add h1 h2
    _ = 104 * E := by rw [mul_assoc, hsq]; ring

end RHTower.Sieve
