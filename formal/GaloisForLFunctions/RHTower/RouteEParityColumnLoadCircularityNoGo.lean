import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureRH
import GaloisForLFunctions.RHTower.MobiusReciprocalAllocationJacobian

/-!
# Route E parity-column circularity

For any finite row-stochastic kernel whose supported transitions reverse a sign, signed source
imbalance is exactly half the signed column-load defect.  Applied to the finite Möbius signature,
an all-strict-half bound for total column defect already implies RH by Littlewood's criterion.

Thus constructing an opposite-parity Route E kernel does not turn a strict-half column estimate
into an unsigned anti-concentration problem: that estimate itself contains the missing Möbius
cancellation.  Any surviving producer must control this signed defect before scalar column-load
normalization.
-/

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower

noncomputable section

namespace FiniteRowStochasticKernel

variable {ι : Type*} [Fintype ι]

/-- Incoming load at one column of a finite row-stochastic kernel. -/
def columnLoad (P : FiniteRowStochasticKernel ι ι) (j : ι) : ℝ :=
  ∑ i, P.weight i j

/-- **Exact parity-column law.**  A row-stochastic sign-reversing transport carries the signed
source imbalance into precisely half the signed defect of its column loads. -/
theorem two_mul_signedSum_eq_signedColumnDefect
    (P : FiniteRowStochasticKernel ι ι) (sign : ι → ℝ)
    (hflip : ∀ i j, P.weight i j ≠ 0 → sign i + sign j = 0) :
    2 * ∑ i, sign i = ∑ j, sign j * (1 - P.columnLoad j) := by
  have hterm (i j : ι) :
      sign i * P.weight i j = -sign j * P.weight i j := by
    by_cases hzero : P.weight i j = 0
    · simp [hzero]
    · have hsign : sign i = -sign j := by
        linarith [hflip i j hzero]
      rw [hsign]
  have htransport :
      (∑ i, sign i) = -∑ j, sign j * P.columnLoad j := by
    calc
      (∑ i, sign i) = ∑ i, sign i * ∑ j, P.weight i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [P.row_sum i, mul_one]
      _ = ∑ i, ∑ j, sign i * P.weight i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, sign i * P.weight i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -sign j * P.weight i j := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro i _hi
        exact hterm i j
      _ = -∑ j, sign j * P.columnLoad j := by
        unfold columnLoad
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hright :
      (∑ j, sign j * (1 - P.columnLoad j)) =
        (∑ i, sign i) - ∑ j, sign j * P.columnLoad j := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hright]
  linarith

/-- Total absolute column defect bounds every unit-bounded signed source imbalance. -/
theorem abs_signedSum_le_half_columnDefect
    (P : FiniteRowStochasticKernel ι ι) (sign : ι → ℝ)
    (hsign : ∀ i, |sign i| ≤ 1)
    (hflip : ∀ i j, P.weight i j ≠ 0 → sign i + sign j = 0) :
    |∑ i, sign i| ≤ (1 / 2 : ℝ) * ∑ j, |1 - P.columnLoad j| := by
  have hid := P.two_mul_signedSum_eq_signedColumnDefect sign hflip
  have habs :
      |2 * ∑ i, sign i| ≤ ∑ j, |1 - P.columnLoad j| := by
    rw [hid]
    calc
      |∑ j, sign j * (1 - P.columnLoad j)| ≤
          ∑ j, |sign j * (1 - P.columnLoad j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |1 - P.columnLoad j| := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_right (hsign j) (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
  nlinarith

end FiniteRowStochasticKernel

/-- The Möbius signs on positive coordinates through `N` sum to the finite coprimality
signature. -/
theorem sum_finiteMobiusCoprimeCoordinate_mobius_eq_signature (N : ℕ) :
    (∑ i : finiteMobiusCoprimeCoordinate N, ((μ i.1 : ℤ) : ℝ)) =
      ((finiteMobiusCoprimeSignature N : ℤ) : ℝ) := by
  rw [finiteMobiusCoprimeSignature_eq_sum_Icc]
  push_cast
  simpa [finiteMobiusCoprimeCoordinate] using
    (Finset.sum_attach (Finset.Icc 1 N) (fun n => ((μ n : ℤ) : ℝ)))

/-- Route E's proposed strict-half total column-defect input, after retaining the literal Möbius
signs and requiring every supported edge to reverse them. -/
def RouteEParityColumnDefectAllStrictHalfPowerBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∃ P : FiniteRowStochasticKernel
        (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N),
      (∀ i j, P.weight i j ≠ 0 →
        ((μ i.1 : ℤ) : ℝ) + ((μ j.1 : ℤ) : ℝ) = 0) ∧
      (∑ j, |1 - P.columnLoad j|) ≤
        2 * C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)

/-- A strict-half Route E column-defect estimate is already the strict-half Möbius signature
estimate.  Kernel construction supplies no independent cancellation. -/
theorem routeEParityColumnDefectAllStrictHalfPowerBound_implies_signature
    (h : RouteEParityColumnDefectAllStrictHalfPowerBound) :
    FiniteMobiusCoprimeSignatureAllStrictHalfPowerBound := by
  intro δ hδ
  obtain ⟨C, hC, hload⟩ := h δ hδ
  refine ⟨C + 2, by positivity, fun N => ?_⟩
  by_cases hN : 2 ≤ N
  · obtain ⟨P, hflip, hdefect⟩ := hload N hN
    have hsign : ∀ i : finiteMobiusCoprimeCoordinate N,
        |(((μ i.1 : ℤ) : ℝ))| ≤ 1 := by
      intro i
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := i.1)
    have hbound := P.abs_signedSum_le_half_columnDefect
      (fun i => ((μ i.1 : ℤ) : ℝ)) hsign hflip
    rw [sum_finiteMobiusCoprimeCoordinate_mobius_eq_signature] at hbound
    calc
      |((finiteMobiusCoprimeSignature N : ℤ) : ℝ)|
          ≤ (1 / 2 : ℝ) * ∑ j, |1 - P.columnLoad j| := hbound
      _ ≤ (1 / 2 : ℝ) *
          (2 * C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) := by
        gcongr
      _ ≤ (C + 2) * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
        have hpow : 0 ≤ ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) :=
          Real.rpow_nonneg (by positivity) _
        nlinarith
  · have hNle : N ≤ 1 := by omega
    have htrivial :
        |((finiteMobiusCoprimeSignature N : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [finiteMobiusCoprimeSignature_eq_sum_range]
      push_cast
      calc
        |∑ j ∈ Finset.range N, ((μ (j + 1) : ℤ) : ℝ)| ≤
            ∑ j ∈ Finset.range N, |((μ (j + 1) : ℤ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _hj
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j + 1)
        _ = (N : ℝ) := by simp
    have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have hexp : 0 ≤ (1 / 2 : ℝ) + δ := by linarith
    have hpow : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
      simpa using Real.one_le_rpow hbase hexp
    calc
      |((finiteMobiusCoprimeSignature N : ℤ) : ℝ)| ≤ (N : ℝ) := htrivial
      _ ≤ 1 := by exact_mod_cast hNle
      _ ≤ (C + 2) * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
        nlinarith

/-- **Route kill.**  All-strict-half opposite-parity column-load control already proves RH. -/
theorem routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis
    (h : RouteEParityColumnDefectAllStrictHalfPowerBound) :
    RiemannHypothesis :=
  finiteMobiusCoprimeSignatureAllStrictHalfPowerBound_iff_riemannHypothesis.mp
    (routeEParityColumnDefectAllStrictHalfPowerBound_implies_signature h)

end

end RHTower
