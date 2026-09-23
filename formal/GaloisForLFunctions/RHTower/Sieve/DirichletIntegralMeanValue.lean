import GaloisForLFunctions.RHTower.Sieve.DirichletDiagonal
import GaloisForLFunctions.RHTower.OffDiagonalBound
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The integral mean value theorem for Dirichlet polynomials

The off-diagonal estimate of `RHTower/OffDiagonalBound.lean` is stated for coefficients indexed by a
`Finset ℕ` inside `[1, K]`; the mean square of `RHTower/Sieve/DirichletDiagonal.lean` is indexed by
`Fin N`, with `n` standing for `n + 1`.  They are the same double sum, so bridging the indices gives

    | ∫₀^T |∑_{n ≤ N} a_n n^{it}|² dt - T·∑ |a_n|² |  ≤  4N·(∑_{j ≤ N} 1/j)·∑ |a_n|²,

the classical `T + O(N log N)` mean value theorem, unconditionally.

The elementary `N log N` in place of Montgomery–Vaughan's `N` is exactly what the logarithmic
separation `|log n - log m| ≥ |n - m|/N` costs; no Hilbert inequality enters.

This is the continuous companion of `DirichletMeanValue.lean`, which bounds a discrete mean square
over separated frequencies.
-/

namespace RHTower.Sieve

open Finset

/-- The successor map sends the index set onto `[1, N]`. -/
theorem image_succ_univ (N : ℕ) :
    (Finset.univ : Finset (Fin N)).image (fun m : Fin N => (m : ℕ) + 1) = Finset.Icc 1 N := by
  classical
  ext k
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨by omega, by have := m.isLt; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨k - 1, by omega⟩, by simp; omega⟩

/-- The successor map is injective. -/
theorem succ_injOn (N : ℕ) :
    ∀ a ∈ (Finset.univ : Finset (Fin N)), ∀ b ∈ (Finset.univ : Finset (Fin N)),
      (a : ℕ) + 1 = (b : ℕ) + 1 → a = b := by
  intro a _ b _ hab
  exact Fin.val_injective (by omega)

/-- A sum over `Fin N` is a sum over `[1, N]`. -/
theorem sum_fin_eq_sum_Icc (N : ℕ) (g : ℕ → ℝ) :
    ∑ m : Fin N, g ((m : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 N, g k := by
  classical
  rw [← image_succ_univ N, Finset.sum_image (succ_injOn N)]

/-- The successor map sends a punctured index set onto a punctured `[1, N]`. -/
theorem image_succ_erase (N : ℕ) (m : Fin N) :
    ((Finset.univ : Finset (Fin N)).erase m).image (fun n : Fin N => (n : ℕ) + 1)
      = (Finset.Icc 1 N).erase ((m : ℕ) + 1) := by
  classical
  ext k
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Icc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨?_, by omega, by have := n.isLt; omega⟩
    intro hcon
    exact hn (Fin.val_injective (by omega))
  · rintro ⟨hne, h1, h2⟩
    have hklt : k - 1 < N := by omega
    refine ⟨⟨k - 1, hklt⟩, ?_, by simp; omega⟩
    intro hcon
    apply hne
    have hval : ((⟨k - 1, hklt⟩ : Fin N) : ℕ) = (m : ℕ) := by rw [hcon]
    simp only at hval
    omega

/-- A punctured sum over `Fin N` is a punctured sum over `[1, N]`. -/
theorem sum_fin_erase_eq_sum_Icc_erase (N : ℕ) (m : Fin N) (g : ℕ → ℝ) :
    ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, g ((n : ℕ) + 1)
      = ∑ k ∈ (Finset.Icc 1 N).erase ((m : ℕ) + 1), g k := by
  classical
  rw [← image_succ_erase N m,
    Finset.sum_image (fun a _ b _ hab => Fin.val_injective (by omega : (a : ℕ) = (b : ℕ)))]

/-- The coefficient moduli, extended to `ℕ` and shifted. -/
noncomputable def coeffAbs {N : ℕ} (a : Fin N → ℂ) (k : ℕ) : ℝ :=
  if h : k - 1 < N then ‖a ⟨k - 1, h⟩‖ else 0

theorem coeffAbs_succ {N : ℕ} (a : Fin N → ℂ) (m : Fin N) :
    coeffAbs a ((m : ℕ) + 1) = ‖a m‖ := by
  rw [coeffAbs]
  have hlt : (m : ℕ) + 1 - 1 < N := by have := m.isLt; omega
  rw [dif_pos hlt]
  congr 1

theorem coeffAbs_nonneg {N : ℕ} (a : Fin N → ℂ) (k : ℕ) : 0 ≤ coeffAbs a k := by
  rw [coeffAbs]
  split
  · exact norm_nonneg _
  · exact le_refl 0

/-- **The integral mean value theorem for Dirichlet polynomials.** -/
theorem norm_integral_normSq_dirPoly_sub_diag_le_explicit (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ (2 : ℕ) : ℝ) : ℂ)‖
      ≤ 4 * (N : ℝ) * (∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ)) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  classical
  refine le_trans (norm_integral_normSq_dirPoly_sub_diag_le N a T) ?_
  have hbridge : ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
        ‖a m‖ * ‖a n‖ * (2 / |Real.log (((m : ℕ) : ℝ) + 1) - Real.log (((n : ℕ) : ℝ) + 1)|)
      = ∑ p ∈ Finset.Icc 1 N, ∑ q ∈ (Finset.Icc 1 N).erase p,
          2 * |coeffAbs a p * coeffAbs a q| / |Real.log (q : ℝ) - Real.log (p : ℝ)| := by
    rw [← sum_fin_eq_sum_Icc N (fun p => ∑ q ∈ (Finset.Icc 1 N).erase p,
      2 * |coeffAbs a p * coeffAbs a q| / |Real.log (q : ℝ) - Real.log (p : ℝ)|)]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [← sum_fin_erase_eq_sum_Icc_erase N m (fun q =>
      2 * |coeffAbs a ((m : ℕ) + 1) * coeffAbs a q|
        / |Real.log (q : ℝ) - Real.log ((((m : ℕ) + 1 : ℕ)) : ℝ)|)]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [coeffAbs_succ, coeffAbs_succ]
    have hcastm : ((((m : ℕ) + 1 : ℕ)) : ℝ) = ((m : ℕ) : ℝ) + 1 := by push_cast; ring
    have hcastn : ((((n : ℕ) + 1 : ℕ)) : ℝ) = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcastm, hcastn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a m‖ * ‖a n‖),
      abs_sub_comm (Real.log (((n : ℕ) : ℝ) + 1))]
    ring
  rw [hbridge]
  refine le_trans (RHTower.offDiagonal_le (coeffAbs a) (Finset.Subset.refl _)) ?_
  have hsq : ∑ k ∈ Finset.Icc 1 N, (coeffAbs a k) ^ (2 : ℕ) = ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
    rw [← sum_fin_eq_sum_Icc N (fun k => (coeffAbs a k) ^ (2 : ℕ))]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [coeffAbs_succ]
  rw [hsq]

/-- **The mean value theorem, in the `T + O(N log N)` form.** -/
theorem norm_integral_normSq_dirPoly_sub_diag_le_log (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ (2 : ℕ) : ℝ) : ℂ)‖
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  refine le_trans (norm_integral_normSq_dirPoly_sub_diag_le_explicit N a T) ?_
  have hcoef : (0 : ℝ) ≤ 4 * (N : ℝ) := by positivity
  have hsq : (0 : ℝ) ≤ ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hharm := sum_Icc_one_div_le_one_add_log N
  have hstep : 4 * (N : ℝ) * (∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ))
      ≤ 4 * (N : ℝ) * (1 + Real.log N) := mul_le_mul_of_nonneg_left hharm hcoef
  exact mul_le_mul_of_nonneg_right hstep hsq

end RHTower.Sieve
