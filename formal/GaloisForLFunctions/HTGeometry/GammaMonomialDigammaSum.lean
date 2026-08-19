import GaloisForLFunctions.HTGeometry.GammaShiftLadderCoeffTop
import GaloisForLFunctions.HTGeometry.GammaMonomialLogDeriv

/-!
# The logarithmic derivative of a balanced gamma monomial, to every order

Summing the shifted Stirling ladder over the exponent vector cancels the `log s` term when the
degree vanishes, leaving a pure power series in `1/s` whose coefficients are the signed ladder
moments.  When the first moment also vanishes the series starts at `s^{-2}`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- The signed ladder moment of an exponent vector. -/
def balancedLadderCoeff {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (m : ℕ) : ℂ :=
  ∑ k, (g k : ℂ) * shiftLadderCoeff (lam k) m

/-- A polynomial of degree one is read off from its two coefficients. -/
theorem shiftLadderCoeff_zero_eq (mu : ℂ) :
    shiftLadderCoeff mu 0
      = (shiftLadderCoeffPoly 0).coeff 0 + (shiftLadderCoeffPoly 0).coeff 1 * mu := by
  rw [shiftLadderCoeff_eq_eval, Polynomial.eval_eq_sum_range, natDegree_shiftLadderCoeffPoly 0]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- **A balanced exponent vector kills the first ladder moment.** -/
theorem balancedLadderCoeff_zero {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    balancedLadderCoeff lam g 0 = 0 := by
  have hdegC : ∑ k, ((g k : ℤ) : ℂ) = 0 := by
    have : ((∑ k, g k : ℤ) : ℂ) = 0 := by rw [hdeg]; simp
    rw [← this]
    push_cast
    ring
  rw [balancedLadderCoeff]
  have hterm : ∀ k : Fin r, ((g k : ℤ) : ℂ) * shiftLadderCoeff (lam k) 0
      = (shiftLadderCoeffPoly 0).coeff 0 * ((g k : ℤ) : ℂ)
        + (shiftLadderCoeffPoly 0).coeff 1 * (((g k : ℤ) : ℂ) * lam k) := by
    intro k
    rw [shiftLadderCoeff_zero_eq]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hdegC, hmom]
  ring

/-- **The expansion of `∑ g_k ψ(s + λ_k)` to every order**, for a vector of vanishing degree. -/
theorem exists_norm_logDeriv_gammaMonomial_expansion {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (M : ℕ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖(∑ k, (g k : ℂ) * Complex.digamma (s + lam k))
          + ∑ m ∈ Finset.range M, balancedLadderCoeff lam g m / s ^ (m + 1)‖
        ≤ K / ‖s‖ ^ (M + 1) := by
  classical
  choose K R hK0 hR hb using fun k : Fin r => exists_norm_digamma_shift_ladder_expansion_le (lam k) M
  have hdegC : ∑ k, ((g k : ℤ) : ℂ) = 0 := by
    have hz : ((∑ k, g k : ℤ) : ℂ) = 0 := by rw [hdeg]; simp
    rw [← hz]
    push_cast
    ring
  refine ⟨∑ k, ‖((g k : ℤ) : ℂ)‖ * K k, 2 + ∑ k, |R k|, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hK0 k)
  · have : (0 : ℝ) ≤ ∑ k, |R k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · intro s hs hRs
    have hsn : (0 : ℝ) < ‖s‖ := by
      have h0 : (0 : ℝ) ≤ ∑ k, |R k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    have hRk : ∀ k : Fin r, R k ≤ ‖s‖ := by
      intro k
      have h1 : |R k| ≤ ∑ j, |R j| :=
        Finset.single_le_sum (f := fun j => |R j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
      have h2 : R k ≤ |R k| := le_abs_self _
      linarith
    set S : Fin r → ℂ :=
      fun k => ∑ m ∈ Finset.range M, shiftLadderCoeff (lam k) m / s ^ (m + 1) with hS
    have hmoment : ∑ m ∈ Finset.range M, balancedLadderCoeff lam g m / s ^ (m + 1)
        = ∑ k, ((g k : ℤ) : ℂ) * S k := by
      have h2 : ∀ k : Fin r, ((g k : ℤ) : ℂ) * S k
          = ∑ m ∈ Finset.range M, ((g k : ℤ) : ℂ) * shiftLadderCoeff (lam k) m / s ^ (m + 1) := by
        intro k
        rw [hS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
      have h3 : ∑ k, ((g k : ℤ) : ℂ) * S k
          = ∑ k, ∑ m ∈ Finset.range M,
              ((g k : ℤ) : ℂ) * shiftLadderCoeff (lam k) m / s ^ (m + 1) :=
        Finset.sum_congr rfl fun k _ => h2 k
      rw [h3, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [balancedLadderCoeff, Finset.sum_div]
    have hrepr : (∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (s + lam k))
        + ∑ m ∈ Finset.range M, balancedLadderCoeff lam g m / s ^ (m + 1)
        = ∑ k, ((g k : ℤ) : ℂ)
            * (Complex.digamma (s + lam k) - (Complex.log s - S k)) := by
      have h1 : ∀ k : Fin r, ((g k : ℤ) : ℂ)
            * (Complex.digamma (s + lam k) - (Complex.log s - S k))
          = ((g k : ℤ) : ℂ) * Complex.digamma (s + lam k) + ((g k : ℤ) : ℂ) * S k
            - ((g k : ℤ) : ℂ) * Complex.log s := fun k => by ring
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, hdegC, zero_mul, sub_zero, hmoment]
    rw [hrepr]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul]
    have hbk := hb k s hs (hRk k)
    have hSk : Complex.digamma (s + lam k) - (Complex.log s - S k)
        = Complex.digamma (s + lam k)
          - (Complex.log s - ∑ m ∈ Finset.range M, shiftLadderCoeff (lam k) m / s ^ (m + 1)) := by
      rw [hS]
    rw [hSk]
    have hmul : ‖((g k : ℤ) : ℂ)‖ * K k / ‖s‖ ^ (M + 1)
        = ‖((g k : ℤ) : ℂ)‖ * (K k / ‖s‖ ^ (M + 1)) := by ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hbk (norm_nonneg _)

end

end GaloisForLFunctions.HTGeometry
