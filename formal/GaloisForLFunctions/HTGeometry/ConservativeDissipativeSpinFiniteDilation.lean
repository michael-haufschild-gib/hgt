import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinInstrumentPinching
import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay

/-!
# Finite spin-filter dilations and the autonomous-unitary boundary

Application of Schaffer–Exl, arXiv:2609.04530, to the corpus's compact finite-unitary
recurrence theorem. Every individual spin-filter time is realized by an explicit
four-dimensional unitary acting on spin and a two-dimensional environment. Its two
environment outcomes reproduce the exact Kraus operators and the full channel.
Yet no fixed finite-dimensional unitary, with fixed arbitrary initial matrix and
fixed arbitrary linear expectation readout, produces the positive-damping coherence
profile at all integer times. The positive survivor is the exact per-time finite
unitary dilation; the obstruction is to a fixed autonomous finite realization.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Two explicit environment rotations controlled by the physical spin coordinate. -/
def spinFilterEnvBlock (k : ℂ) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = 0 then (spinChartScale k : ℂ) • !![1, k; -conj k, 1]
  else (spinChartScale k : ℂ) • !![conj k, 1; -1, k]

/-- Each constructed environment block is unitary with no restriction on the chart multiplier. -/
theorem spinFilterEnvBlock_unitary (k : ℂ) (i : Fin 2) :
    (spinFilterEnvBlock k i)ᴴ * spinFilterEnvBlock k i = 1 := by
  have hc := spinChartScale_complex_identity k
  fin_cases i <;> ext p q <;> fin_cases p <;> fin_cases q <;>
    simp [spinFilterEnvBlock, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals linear_combination hc

/-- Explicit four-dimensional unitary dilation, with environment coordinate listed first. -/
def spinFilterDilation (k : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal (spinFilterEnvBlock k)

/-- The four-dimensional dilation is an actual finite unitary. -/
theorem spinFilterDilation_unitary (k : ℂ) :
    spinFilterDilation k ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (spinFilterDilation k)ᴴ * spinFilterDilation k = 1
  rw [spinFilterDilation, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  simp only [spinFilterEnvBlock_unitary]
  exact Matrix.blockDiagonal_one

/-- Environment-outcome extraction for an arbitrary joint operator and a fixed initial environment basis state. -/
def spinEnvironmentOperator (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (e : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => U (e, i) (1, j)

/-- Physical Kraus operator obtained by starting the environment in its second basis state. -/
def spinFilterDilationKraus (k : ℂ) (e : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinEnvironmentOperator (spinFilterDilation k) e

/-- The two environment outcomes recover exactly the earlier normalized Kraus operators. -/
theorem spinFilterDilationKraus_eq (k : ℂ) (e : Fin 2) :
    spinFilterDilationKraus k e = (spinFilterChannel k).operator e := by
  ext i j
  fin_cases e <;> fin_cases i <;> fin_cases j <;>
    simp [spinFilterDilationKraus, spinEnvironmentOperator, spinFilterDilation, Matrix.blockDiagonal_apply,
      spinFilterEnvBlock, spinFilterChannel, spinFilterSelected, spinFilterComplement,
      Matrix.smul_apply]

/-- Discarding the finite environment gives exactly the existing complete spin-filter channel. -/
theorem spinFilterDilation_channel (k : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ e : Fin 2, spinFilterDilationKraus k e * ρ * (spinFilterDilationKraus k e)ᴴ =
      (spinFilterChannel k).evolveMatrix ρ := by
  simp only [spinFilterDilationKraus_eq, FiniteRectangularKrausChannel.evolveMatrix]

/-- A complete exact finite unitary realization exists separately at every real spin time. -/
theorem spinFilter_time_has_finite_unitary_dilation (a t : ℝ) :
    ∃ U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ,
      ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
        ∑ e : Fin 2, spinEnvironmentOperator (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) e * ρ *
          (spinEnvironmentOperator (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) e)ᴴ =
            (spinFilterChannel (Complex.exp (spinPlaneRate a * (t : ℂ)))).evolveMatrix ρ := by
  refine ⟨⟨spinFilterDilation (Complex.exp (spinPlaneRate a * (t : ℂ))),
    spinFilterDilation_unitary (Complex.exp (spinPlaneRate a * (t : ℂ)))⟩, ?_⟩
  exact spinFilterDilation_channel (Complex.exp (spinPlaneRate a * (t : ℂ)))

/-- Finite closed unitary recurrence excludes a fixed autonomous realization of the decaying coherence profile,
even with arbitrary initial matrices and arbitrary linear expectation readouts. -/
theorem spinFilter_no_finite_autonomous_unitary (n : ℕ) (s : ℝ) :
    ¬ ∃ (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
      (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      ∀ k : ℕ, (Matrix.trace (B * ((U ^ k : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * A *
        star ((U ^ k : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))).re =
          spinFilterCoherence (Complex.exp (spinPlaneRate (Real.exp s) * ((k : ℝ) : ℂ))) := by
  rintro ⟨U, A, B, h⟩
  let f : Matrix.unitaryGroup (Fin (n + 1)) ℂ → ℝ := fun V =>
    (Matrix.trace (B * (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * A *
      star (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))).re
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hzero : f 1 = 1 := by
    have h0 := h 0
    have h01 : f 1 = (2 : ℝ) * (1 + 1)⁻¹ := by
      simpa [f, spinFilterCoherence, spinChartScale_sq] using h0
    calc
      f 1 = _ := h01
      _ = 1 := by ring
  obtain ⟨u, hu, hU⟩ := (matrixUnitary_pow_recurrent U).tendsto_subseq
  have hreturn : Tendsto (fun k => f (U ^ u k)) atTop (nhds 1) := by
    have ht := hf.continuousAt.tendsto.comp hU
    rw [hzero] at ht
    convert ht using 1
    funext k
    rfl
  have hdecay := ((spinFilterCoherence_flow_tendsto_zero s).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).comp hu.tendsto_atTop
  have hvanish : Tendsto (fun k => f (U ^ u k)) atTop (nhds 0) := by
    convert hdecay using 1
    funext k
    exact h (u k)
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hreturn hvanish
  exact one_ne_zero hbad

end
end GaloisForLFunctions.HTGeometry.SchafferExl
