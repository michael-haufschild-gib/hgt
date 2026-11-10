import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsIsThePoleMinusWeilsFunctional
import GaloisForLFunctions.SquareRootThreshold.ZetaWindowPrimePolynomialReadsZeroCountRemainder

/-!
# The contacts at a height read the remainder of the zero count

The gluing conditions of the square count the zeros up to the remainder `S`. The remainder is not
a second invariant next to the contacts: it is what the contacts give when they are tested at a
height.

For the bump packet `c_ℓ` of aperture `ℓ`, with autocorrelation `k_ℓ` and spectral window
`ψ_ℓ = |ĉ_ℓ|²`, the contacts of the window at the height `T` are

  `C_ℓ(T) = Re Σ_{2 ≤ n ≤ e^{2ℓ}} (Λ(n)/√n)·(k_ℓ(log n) n^{−iT} + k_ℓ(−log n) n^{iT})`,

the contact weights of the square against the packet modulated to the height `T`
(`windowPrime_eq_contacts`). As `T → ∞`,

  `C_ℓ(T) + Corr_ℓ(T) − ∫_1^{2T} S(t) ψ_ℓ'(t − T) dt → 0`

(`tendsto_contacts_add_offLineCorrection_sub`), where `Corr_ℓ(T)` is the displacement of the
zeros off the line, which vanishes when they are on it (corpus). So the increments of `S` over a
height window, smoothed by the window, are the contacts of the square at that height: in the
count of the zeros of a window the gluing conditions are the archimedean term and the contacts
are the remainder.
-/

open Finset Filter Topology Complex
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- **The prime polynomial of a window is the contact weights of the square at a height.** -/
theorem windowPrime_eq_contacts (ℓ T : ℝ) :
    SquareRootThreshold.windowPrime ℓ T =
      (∑ n ∈ Icc 2 ⌊Real.exp (2 * ℓ)⌋₊, ((contactWeight n : ℝ) : ℂ) *
        (EF.weilTest (SquareRootThreshold.cb ℓ 0) (SquareRootThreshold.cb ℓ 0) (Real.log n) *
            cexp (-(I * T * Real.log n)) +
          EF.weilTest (SquareRootThreshold.cb ℓ 0) (SquareRootThreshold.cb ℓ 0) (-Real.log n) *
            cexp (I * T * Real.log n))).re := by
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have e1 : ∀ x : ℝ, 2 * (Real.pi : ℂ) * I * ((SquareRootThreshold.heightWindowShift T : ℝ) : ℂ) *
      (x : ℂ) = -(I * T * x) := by
    intro x
    unfold SquareRootThreshold.heightWindowShift
    push_cast
    field_simp
  unfold SquareRootThreshold.windowPrime SquareRootThreshold.primePolynomial
    SquareRootThreshold.expSum
  congr 1
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fintype.sum_bool]
  simp only [SquareRootThreshold.primeCoeff, SquareRootThreshold.primeFreq, if_true,
    Bool.false_eq_true, if_false, contactWeight]
  rw [e1 (Real.log n), e1 (-Real.log n)]
  push_cast
  ring_nf

/-- **The contacts at a height read the remainder of the zero count.** As `T → ∞` the contacts of
the window of aperture `ℓ` at the height `T`, plus the correction of the zeros off the line, minus
the remainder `S` integrated against the derivative of the spectral window, tend to `0`. -/
theorem tendsto_contacts_add_offLineCorrection_sub {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun T : ℝ =>
      (∑ n ∈ Icc 2 ⌊Real.exp (2 * ℓ)⌋₊, ((contactWeight n : ℝ) : ℂ) *
        (EF.weilTest (SquareRootThreshold.cb ℓ 0) (SquareRootThreshold.cb ℓ 0) (Real.log n) *
            cexp (-(I * T * Real.log n)) +
          EF.weilTest (SquareRootThreshold.cb ℓ 0) (SquareRootThreshold.cb ℓ 0) (-Real.log n) *
            cexp (I * T * Real.log n))).re +
        SquareRootThreshold.offLineCorrection ℓ T -
        ∫ t in (1 : ℝ)..(2 * T),
          _root_.RHTower.rvmRemainder t * SquareRootThreshold.psiDeriv ℓ (t - T)) atTop
      (𝓝 0) := by
  refine (SquareRootThreshold.tendsto_windowPrime_add_offLineCorrection_sub hℓ).congr fun T => ?_
  rw [windowPrime_eq_contacts]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
