import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries
import GaloisForLFunctions.HTGeometry.FiniteDeterminantZeros
import GaloisForLFunctions.HTGeometry.GradedTraceDeterminantRigidity

/-!
# Graded regularized-trace determinant rigidity

Order-two regularization does not create a graded zero-moving loophole.  If the signed power
traces of an even block `E` and odd block `O` agree with a source block `C` in every degree from
two onward, then their finite Hilbert--Carleman determinants satisfy

`det₂(I - zE) = det₂(I - zC) det₂(I - zO)`.

Only the first trace is forgotten by `det₂`; all higher traces determine its entire germ.  Thus a
real divisor for the even block still forces every source zero to be real.  In particular, any
graded/Krein construction that genuinely moves source zeros must change at least one signed trace
of degree two or higher.
-/

open Complex Filter Matrix
open scoped Matrix Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Two entire scalar functions agreeing near zero agree globally. -/
private theorem differentiable_eq_of_eventuallyEq_nhds_zero
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ᶠ z in nhds (0 : ℂ), f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hga : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  funext z
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) h (Set.mem_univ z)

/-- Equality of all matrix power traces from degree two determines the complete finite
Hilbert--Carleman determinant. -/
theorem finiteDet2_neg_eq_of_trace_pow_add_two_eq
    {M N : Matrix ι ι ℂ}
    (htrace : ∀ n : ℕ, (M ^ (n + 2)).trace = (N ^ (n + 2)).trace) :
    (fun z => finiteDet2 (-M) z) = fun z => finiteDet2 (-N) z := by
  apply differentiable_eq_of_eventuallyEq_nhds_zero
    (differentiable_finiteDet2 (-M)) (differentiable_finiteDet2 (-N))
  have hM : Tendsto
      (fun z : ℂ => ‖z‖ * Real.sqrt (matHSNormSq M)) (nhds 0) (nhds 0) := by
    simpa using (tendsto_norm_zero.mul_const (Real.sqrt (matHSNormSq M)))
  have hN : Tendsto
      (fun z : ℂ => ‖z‖ * Real.sqrt (matHSNormSq N)) (nhds 0) (nhds 0) := by
    simpa using (tendsto_norm_zero.mul_const (Real.sqrt (matHSNormSq N)))
  filter_upwards [hM.eventually (Iio_mem_nhds zero_lt_one),
    hN.eventually (Iio_mem_nhds zero_lt_one)] with z hzM hzN
  rw [← exp_neg_traceSeries_eq_finiteDet2_neg M hzM,
    ← exp_neg_traceSeries_eq_finiteDet2_neg N hzN]
  congr 2
  apply tsum_congr
  intro n
  rw [htrace n]

/-- Finite Hilbert--Carleman determinants multiply across a graded block diagonal. -/
theorem finiteDet2_neg_gradedBlockDiagonal
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ) (z : ℂ) :
    finiteDet2 (-(gradedBlockDiagonal C O)) z =
      finiteDet2 (-C) z * finiteDet2 (-O) z := by
  rw [finiteDet2, finiteDet2, finiteDet2]
  have hdet :
      ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) +
          z • (-(gradedBlockDiagonal C O))).det =
        ((1 : Matrix ι ι ℂ) + z • (-C)).det *
          ((1 : Matrix κ κ ℂ) + z • (-O)).det := by
    simpa [sub_eq_add_neg] using gradedBlockDiagonal_det_one_sub C O z
  have htrace : (-(gradedBlockDiagonal C O)).trace = (-C).trace + (-O).trace := by
    have hblock : (gradedBlockDiagonal C O).trace = C.trace + O.trace := by
      simpa using gradedBlockDiagonal_trace_pow C O 1
    simp only [Matrix.trace_neg]
    rw [hblock]
    ring
  rw [hdet, htrace,
    show -(z * ((-C).trace + (-O).trace)) =
        -(z * (-C).trace) + -(z * (-O).trace) by ring,
    Complex.exp_add]
  ring

/-- **Order-two signed-trace rigidity.**  Exact supertraces only from degree two onward force the
cross-multiplied regularized superdeterminant identity. -/
theorem graded_signedTrace_add_two_forces_finiteDet2_factor
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (htrace : ∀ n : ℕ,
      (E ^ (n + 2)).trace - (O ^ (n + 2)).trace = (C ^ (n + 2)).trace)
    (z : ℂ) :
    finiteDet2 (-E) z = finiteDet2 (-C) z * finiteDet2 (-O) z := by
  let B := gradedBlockDiagonal C O
  have hEB : ∀ n : ℕ, (E ^ (n + 2)).trace = (B ^ (n + 2)).trace := by
    intro n
    rw [show (B ^ (n + 2)).trace =
        (C ^ (n + 2)).trace + (O ^ (n + 2)).trace by
      exact gradedBlockDiagonal_trace_pow C O (n + 2)]
    exact sub_eq_iff_eq_add.mp (htrace n)
  have hdet := congrFun (finiteDet2_neg_eq_of_trace_pow_add_two_eq hEB) z
  rw [hdet]
  exact finiteDet2_neg_gradedBlockDiagonal C O z

/-- A real even divisor cannot hide a nonreal source zero when signed traces are preserved from
degree two onward. -/
theorem source_realDivisor_of_graded_signedTrace_add_two_realDivisor
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (htrace : ∀ n : ℕ,
      (E ^ (n + 2)).trace - (O ^ (n + 2)).trace = (C ^ (n + 2)).trace)
    (hreal : ∀ z : ℂ,
      ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) - z • E).det = 0 → z.im = 0)
    {z : ℂ} (hz : ((1 : Matrix ι ι ℂ) - z • C).det = 0) :
    z.im = 0 := by
  apply hreal z
  have hdetE : ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) + z • (-E)).det = 0 := by
    apply (finiteDet2_eq_zero_iff_det (-E) z).mp
    rw [graded_signedTrace_add_two_forces_finiteDet2_factor C O E htrace z]
    apply mul_eq_zero.mpr
    left
    apply (finiteDet2_eq_zero_iff_det (-C) z).mpr
    simpa [sub_eq_add_neg] using hz
  simpa [sub_eq_add_neg] using hdetE

/-- Sharp design law: if an even real-divisor block moves a nonreal source zero, then some signed
source trace of degree at least two must change. -/
theorem exists_signedTrace_anomaly_add_two_of_nonreal_source_zero
    (C : Matrix ι ι ℂ) (O : Matrix κ κ ℂ)
    (E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (hreal : ∀ z : ℂ,
      ((1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) - z • E).det = 0 → z.im = 0)
    {z : ℂ} (hz : ((1 : Matrix ι ι ℂ) - z • C).det = 0) (hzim : z.im ≠ 0) :
    ∃ n : ℕ,
      (E ^ (n + 2)).trace - (O ^ (n + 2)).trace ≠ (C ^ (n + 2)).trace := by
  by_contra hnone
  push Not at hnone
  exact hzim
    (source_realDivisor_of_graded_signedTrace_add_two_realDivisor
      C O E hnone hreal hz)

end

end GaloisForLFunctions.HTGeometry
