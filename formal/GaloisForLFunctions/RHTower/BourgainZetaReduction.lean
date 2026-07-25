/-
Connection from Bourgain's logarithmic exponential sums to the corpus zeta
carrier.

The canonical critical-line point is `linePt t = 1/2 + it`.  Its Dirichlet
polynomial is exactly the critical complex-power sum treated by
`BourgainDyadicDissection`.  The final theorem composes that block estimate
with the corpus's unconditional Euler--Maclaurin zeta transfer.

This is not yet Bourgain's conductor-length symmetric AFE: its explicit
Euler--Maclaurin pole and remainder remain visible.  It nevertheless closes
the exact algebraic, partial-summation, and dyadic interfaces and cannot hide
an exponential-sum estimate as an axiom.
-/
import GaloisForLFunctions.RHTower.BourgainDyadicDissection
import GaloisForLFunctions.RHTower.ZetaAFETransfer
import GaloisForLFunctions.RHTower.HardyCarrier

open Complex

namespace RHTower

/-- The corpus Dirichlet polynomial on the critical line is the exact finite
sum of the monomials `n⁻¹ᐟ²⁻ⁱᵗ` over `(0,N]`. -/
theorem dirichletPoly_line_eq_critical_cpow_sum (N : ℕ) (t : ℝ) :
    dirichletPoly N (linePt t) =
      ∑ n ∈ Finset.Ioc 0 N,
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) := by
  rw [dirichletPoly]
  rw [show Finset.Icc 1 N = Finset.Ioc 0 N by ext n; simp; omega]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  simp [linePt]
  ring

/-- Dyadic unweighted logarithmic phase bounds control the canonical corpus
Dirichlet polynomial on the critical line. -/
theorem norm_dirichletPoly_line_le_dyadic
    {N : ℕ} (hN : 0 < N) (t : ℝ) (B : ℕ → ℝ)
    (hpartial : ∀ k, k < bourgainDyadicDepth N →
      ∀ n ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) (bourgainDyadicCut N k),
        ‖∑ m ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) n,
            (m : ℂ) ^ (-Complex.I * (t : ℂ))‖ ≤ B k) :
    ‖dirichletPoly N (linePt t)‖
      ≤ ∑ k ∈ Finset.range (bourgainDyadicDepth N),
          B k * ((bourgainDyadicCut N (k + 1) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [dirichletPoly_line_eq_critical_cpow_sum]
  exact norm_sum_Ioc_critical_cpow_dyadic_le hN t B hpartial

/-- **Unconditional zeta reduction.** Dyadic phase-sum control bounds
`ζ(1/2+it)` through the existing Euler--Maclaurin AFE.  All correction terms
are explicit in the conclusion. -/
theorem norm_riemannZeta_line_le_dyadic_em
    {N : ℕ} (hN : 0 < N) (t : ℝ) (B : ℕ → ℝ)
    (hpartial : ∀ k, k < bourgainDyadicDepth N →
      ∀ n ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) (bourgainDyadicCut N k),
        ‖∑ m ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) n,
            (m : ℂ) ^ (-Complex.I * (t : ℂ))‖ ≤ B k) :
    ‖riemannZeta (linePt t)‖
      ≤ (∑ k ∈ Finset.range (bourgainDyadicDepth N),
          B k * ((bourgainDyadicCut N (k + 1) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
        + ‖emPole N (linePt t)‖
        + ‖linePt t‖ * (N : ℝ) ^ (-(linePt t).re) / (linePt t).re := by
  have hN1 : 1 ≤ N := hN
  have hre : 0 < (linePt t).re := by rw [linePt_re]; norm_num
  have hne : linePt t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [linePt_re] at this
    norm_num at this
  exact (zeta_norm_le_afe hN1 hre hne).trans <| by
    gcongr
    exact norm_dirichletPoly_line_le_dyadic hN t B hpartial

end RHTower
