import GaloisForLFunctions.SignedSuccessorArithmetic.TheSizeTruncatedHypercubeForm
import GaloisForLFunctions.BezoutValuationIncidence.TheNaturalCutoffDilationFormIsTheReceiver

/-!
# The size-truncated hypercube form is the receiver

`TheSizeTruncatedHypercubeForm` introduced the spectral square integral of the size-truncated
Möbius–Dirichlet polynomial against the Ramanujan step weight,

    R_ε(D) = ∫ W_r(ξ) |Σ_{d ≤ D} μ(d) d^{−(1/2 + ε)} e^{2πiξ log d}|² dξ,

in contrast to the prime-divisor hypercube form, which diverges below half damping independently of
zeros. On the physical side, `R_ε(D)` is definitionally the natural-cutoff dilation Dirichlet form
`naturalDilationDirichletForm ε D r hr` (`sizeHypercubeForm_eq_naturalDilationDirichletForm`).

Expanding `R_ε(D)` in the pronic basis splits it into the **receiver head** `1 ≤ n ≤ D` and a
nonnegative **trans-cutoff tail** `n > D` (`sizeHypercubeForm_eq_head_add_tail`):

    R_ε(D) = ‖Ψ_D‖_D² + Σ_{m ≥ 0} Ψ_D(D + 1 + m)² / ((D + 1 + m)(D + 2 + m)).

For any prime core `p`:
* Cutoff-uniform boundedness of the head `‖Ψ_D‖_D` is equivalent (`↔`) to admission
  `ε ∈ receiverDampings`;
* Cutoff-uniform boundedness of `R_ε(D)` at `ε > 0` forces `ε ∈ receiverDampings`, on an interval
  `(a, b)` forces the zero-free strip `Re ρ ≤ 1/2 + a`, and along any sequence `ε → 0⁺` implies
  `RiemannHypothesis` (`riemannHypothesis_of_cofinal_bounded_spectral_moebiusPolySq`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Finset Filter Topology
open _root_.RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

/-- **Definitional identity between the spectral size-truncated hypercube form and the natural
dilation Dirichlet form.** -/
theorem sizeHypercubeForm_eq_naturalDilationDirichletForm {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) :
    sizeHypercubeForm hr ε D = naturalDilationDirichletForm ε D r hr := rfl

/-- Physical pronic-series expansion of `sizeHypercubeForm`. -/
theorem hasSum_naturalDilationPrimitive_sq_sizeHypercubeForm {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) :
    HasSum (fun n : ℕ => naturalDilationPrimitive ε D r (n + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (sizeHypercubeForm hr ε D) :=
  hasSum_signedDilationPrimitive_sq moebiusReal ε (fun _ hd => (mem_Icc.mp hd).1) hr

/-- **Exact head-plus-tail decomposition of `sizeHypercubeForm`.**
The spectral integral `R_ε(D)` splits into the receiver head `‖Ψ_D‖_D²` (`1 ≤ n ≤ D`) plus the
nonnegative trans-cutoff pronic tail (`n > D`). -/
theorem sizeHypercubeForm_eq_head_add_tail {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) :
    sizeHypercubeForm hr ε D =
      TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive ε D r) D ^ 2 +
        ∑' m : ℕ, naturalDilationPrimitive ε D r (m + D + 1) ^ 2 /
          ((((m + D : ℕ) : ℝ) + 1) * (((m + D : ℕ) : ℝ) + 2)) := by
  have hsum := hasSum_naturalDilationPrimitive_sq_sizeHypercubeForm hr ε D
  rw [← hsum.tsum_eq,
    ← hsum.summable.sum_add_tsum_nat_add D]
  congr 1
  rw [TransHorizonIncidenceMechanics.pronicNorm,
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => by positivity)]
  have hrange : ∀ (f : ℕ → ℝ) (k : ℕ),
      ∑ n ∈ Finset.range k, f (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        ∑ n ∈ Finset.Icc 1 k, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
      congr 1
      push_cast
      ring
  exact hrange _ D

/-- The receiver head energy is bounded by `sizeHypercubeForm`. -/
theorem pronicNorm_naturalDilationPrimitive_sq_le_sizeHypercubeForm {r : ℕ} (hr : 1 < r)
    (ε : ℝ) (D : ℕ) :
    TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive ε D r) D ^ 2 ≤
      sizeHypercubeForm hr ε D :=
  pnorm_naturalDilationPrimitive_sq_le ε D hr

/-- **A cutoff-uniform bound on `sizeHypercubeForm` at a prime core is receiver admission.** -/
theorem mem_receiverDampings_of_bounded_sizeHypercubeForm {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε0 : 0 < ε)
    (hB : ∃ B : ℝ, ∀ D : ℕ, sizeHypercubeForm hp.one_lt ε D ≤ B) :
    ε ∈ receiverDampings :=
  mem_receiverDampings_of_bounded_naturalDilationDirichletForm hp hε0 hB

/-- **A cutoff-uniform bound on `sizeHypercubeForm` across `(a, b)` forces a zero-free strip.** -/
theorem re_le_of_bounded_sizeHypercubeForm_on_Ioo {p : ℕ} (hp : p.Prime) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hB : ∀ ε ∈ Set.Ioo a b, ∃ B : ℝ, ∀ D : ℕ, sizeHypercubeForm hp.one_lt ε D ≤ B)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hρ1 : ρ.re < 1) :
    ρ.re ≤ 1 / 2 + a :=
  re_le_of_bounded_naturalDilationDirichletForm_on_Ioo hp ha hab hB hzero hρ1

/-- **Cofinal boundedness of `sizeHypercubeForm` as `ε → 0⁺` implies `RiemannHypothesis`.** -/
theorem riemannHypothesis_of_cofinal_bounded_sizeHypercubeForm {p : ℕ} (hp : p.Prime)
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ D : ℕ, sizeHypercubeForm hp.one_lt ε D ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_accPt_zero_receiverDampings (accPt_zero_receiverDampings_iff.mpr ?_)
  intro δ hδ
  obtain ⟨ε, hε0, hεδ, hB⟩ := h δ hδ
  have hadm := mem_receiverDampings_of_bounded_sizeHypercubeForm hp hε0 hB
  exact ⟨ε, hε0, hεδ, hadm.2⟩

/-- **Spectral receiver criterion for `RiemannHypothesis`.**
If for some prime `p` and dampings `ε → 0⁺` the truncated Möbius–Dirichlet polynomials have
`stepSpectralWeight`-weighted `L²` norm bounded uniformly in the size cutoff `D`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofinal_bounded_spectral_moebiusPolySq {p : ℕ} (hp : p.Prime)
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ D : ℕ,
        (∫ ξ, stepSpectralWeight hp.one_lt ξ * moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D) ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_bounded_sizeHypercubeForm hp fun δ hδ => ?_
  obtain ⟨ε, hε0, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε0, hεδ, B, fun D => ?_⟩
  rw [sizeHypercubeForm_eq_integral]
  exact hB D

end GaloisForLFunctions.SignedSuccessorArithmetic
