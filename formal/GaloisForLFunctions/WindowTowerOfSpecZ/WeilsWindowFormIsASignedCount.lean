import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowFormIsTheDerivativeOfTheJordanCounts
import Mathlib.LinearAlgebra.Lagrange

/-!
# Weil's window form is a signed count

On a window of level `N = ⌊e^A⌋` the Tate function `τ_H(k) = Σ_{n ≤ N} J_k(n) n^{−1/2} ∫H(u)H(u + log n)`
only involves the finitely many frequencies `log d`, `d ≤ N`, so its derivative at dimension zero is a
fixed linear combination of its values at the integers `0, 1, …, N − 1`.

Let `P = Σ_j p_j x^j` be any real polynomial with `P(d) = log d` for `1 ≤ d ≤ N`; one exists of degree
`< N` (Lagrange, `exists_log_interpolant`). Then

* **Von Mangoldt is a signed combination of Jordan counts** (`sum_coeff_mul_jordanTotient`):
  `Λ(n) = Σ_j p_j J_j(n)` for `1 ≤ n ≤ N`, because `Σ_j p_j J_j(n) = Σ_{d∣n} μ(n/d)P(d) = Σ_{d∣n} μ(n/d) log d`.
* **Weil's window form is a signed count** (`weilQuad_eq_signedCount`):
  `Q(H) = Ω(0)‖H‖² + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩² − 2 Σ_j p_j τ_H(j)`,
  where `τ_H(j) = Σ_{m ≤ N} φ(m)#ℙ^{j−1}(ℤ/m) m^{−1/2} ∫H(u)H(u + log m)` for `j ≥ 1` and `τ_H(0) = ‖H‖²`.

The arithmetic of a window is thus an explicit signed linear combination of projective point counts
over the residue rings `ℤ/m`, `m ≤ e^A`, in dimensions `< e^A`, with the coefficients of the polynomial
interpolating `log` at the integers of the window. The signs come from the interpolation, not from the
counts: positivity of Weil's form is a statement about this interpolation against the archimedean
data, which is why no positivity of the counts alone can produce it.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23 Polynomial

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open ArithmeticDegenerationTheory

/-- A polynomial interpolating `log` at the integers `1, …, N` exists (Lagrange). -/
theorem exists_log_interpolant (N : ℕ) :
    ∃ P : ℝ[X], ∀ d, 1 ≤ d → d ≤ N → P.eval (d : ℝ) = Real.log d := by
  classical
  refine ⟨Lagrange.interpolate (Finset.Icc 1 N) (fun d : ℕ => (d : ℝ)) (fun d => Real.log d),
    fun d h1 hN => ?_⟩
  exact Lagrange.eval_interpolate_at_node (fun d : ℕ => Real.log d)
    (fun a _ b _ hab => by exact_mod_cast hab) (Finset.mem_Icc.mpr ⟨h1, hN⟩)

/-- **Von Mangoldt is a signed combination of Jordan counts**: for an interpolant `P` of `log` at
`1, …, N`, `Σ_j p_j J_j(n) = Λ(n)` for `1 ≤ n ≤ N`. -/
theorem sum_coeff_mul_jordanTotient {N : ℕ} {P : ℝ[X]}
    (hP : ∀ d, 1 ≤ d → d ≤ N → P.eval (d : ℝ) = Real.log d) {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * jordanTotient (j : ℕ) n =
      ArithmeticFunction.vonMangoldt n := by
  simp_rw [jordanTotient, Real.rpow_natCast, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← ArithmeticFunction.log_mul_moebius_eq_vonMangoldt, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.log a *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdn : d ≤ n := Nat.divisor_le hd
  rw [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply, ← hP d hd1 (hdn.trans hnN),
    eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The arithmetic pairing as a signed combination of Tate counts:
`⟨ρ_A(Λ)H, H⟩ = Σ_j p_j τ_H(j)`. -/
theorem integral_windowRep_vonMangoldt_eq_signedCount {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {P : ℝ[X]} (hP : ∀ d, 1 ≤ d → d ≤ windowLevel A → P.eval (d : ℝ) = Real.log d) :
    ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * tateFunction A H (j : ℕ) := by
  have hmem := mem_windowSupported_of_isWindowTest hH
  have hint : ∀ n ∈ Finset.Icc 1 (windowLevel A), Integrable fun u =>
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (windowShift (Real.log n) H u * H u) := fun n _ => by
    refine Integrable.const_mul ?_ _
    simp_rw [windowShift_mul_self hmem]
    refine (integrable_mul_shift hH.continuous hH.hasCompactSupport (-Real.log n)).congr
      (Eventually.of_forall fun u => ?_)
    simp only [sub_eq_add_neg]
    ring
  simp_rw [tateFunction_eq hH, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [windowRepFun, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  rw [integral_const_mul, integral_windowShift_mul hmem, ← sum_coeff_mul_jordanTotient hP hn1 hnN,
    Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Weil's window form is a signed count**: for an interpolant `P` of `log` at the integers of the
window, `Q(H) = Ω(0)‖H‖² + J_∞(H) + pole − 2 Σ_j p_j τ_H(j)`, a signed combination of projective point
counts over residue rings. -/
theorem weilQuad_eq_signedCount {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) {P : ℝ[X]}
    (hP : ∀ d, 1 ≤ d → d ≤ windowLevel A → P.eval (d : ℝ) = Real.log d) :
    weilQuad H = EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
      (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) -
        2 * ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * tateFunction A H (j : ℕ) := by
  rw [weilQuad_eq_windowRep hH, integral_windowRep_vonMangoldt_eq_signedCount hH hP]
  ring

end GaloisForLFunctions.WindowTowerOfSpecZ
