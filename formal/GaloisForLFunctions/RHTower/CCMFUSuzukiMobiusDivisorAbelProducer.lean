import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergOutgoingAbelWeld
import GaloisForLFunctions.RHTower.MoebiusFloorInversion
import GaloisForLFunctions.RHTower.PsiDefectSqrtBound

/-!
# Möbius--divisor producer for the CCM-FU half-order Abel action

The floor-summatory defect is rewritten without von Mangoldt coefficients: it is the difference
between the logarithmic factorial sum and the divisor summatory function, with its Euler constant
main term restored.  Möbius floor inversion then reconstructs the actual Chebyshev defect from
this prime-free `O(sqrt N)` source before scalar Abel readout.

The resulting finite producer preserves every Möbius sign and every floor-dilation coefficient.
Its normalized uniform boundedness is exactly RH.  Consequently separate absolute estimates of
the square-root-bounded divisor source lose the critical cancellation; the open datum is the
joint signed Möbius--divisor action.
-/

open Filter Topology

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Prime-free logarithmic-factorial minus divisor-summatory defect. -/
def primeFreeDivisorDefect (N : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 N, Real.log m) -
    (∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ)) +
    2 * Real.eulerMascheroniConstant * (N : ℝ)

/-- Exact deletion of all von Mangoldt coefficients after floor summation. -/
theorem floorSummatory_psiDefect_eq_primeFreeDivisorDefect (N : ℕ) :
    floorSummatory psiDefect N = primeFreeDivisorDefect N := by
  have hpsi := floorSummatory_chebyshevPsi N
  simp only [floorSummatory, psiDefect] at hpsi ⊢
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Icc, show N + 1 - 1 = N from by omega, nsmul_eq_mul, hpsi]
  unfold primeFreeDivisorDefect
  ring

/-- Unconditional square-root envelope of the prime-free divisor source. -/
theorem abs_primeFreeDivisorDefect_le
    {N : ℕ} (hN : 1 ≤ N) :
    |primeFreeDivisorDefect N| ≤ 24 * Real.sqrt N := by
  rw [← floorSummatory_psiDefect_eq_primeFreeDivisorDefect]
  exact abs_floorSummatory_psiDefect_le N hN

/-- Coefficient-faithful Möbius recovery of the actual Chebyshev defect. -/
theorem psiDefect_eq_mobius_primeFreeDivisorDefect
    {N : ℕ} (hN : 1 ≤ N) :
    psiDefect N =
      ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          primeFreeDivisorDefect (N / d) := by
  have hinv := moebius_floor_inversion psiDefect N hN
  rw [← hinv]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change floorSummatory psiDefect (N / d) = _
  rw [floorSummatory_psiDefect_eq_primeFreeDivisorDefect]

/-- Pre-scalar signed Möbius--divisor action followed by the half-order Abel readout. -/
def mobiusDivisorSquareRootAbelMoment (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (M - 1),
    (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
      (∑ d ∈ Finset.Icc 1 k,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          primeFreeDivisorDefect (k / d))

private theorem sum_sqrt_succ_sub_sqrt_Icc
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1),
      (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)) =
      Real.sqrt M - 1 := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [show M - 1 + 1 = M by omega]
  rw [Finset.sum_Ico_eq_sum_range]
  have htel := Finset.sum_range_sub (fun i : ℕ => Real.sqrt (i + 1 : ℕ)) (M - 1)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.sub_add_cancel hM] using htel

/-- Exact CCM-FU/G-CE weld: Möbius--divisor action equals completed Abel action plus Euler edge. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      coherentSelbergSquareRootAbelMoment M +
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) := by
  rw [mobiusDivisorSquareRootAbelMoment,
    coherentSelbergSquareRootAbelMoment]
  have hpoint : ∀ k ∈ Finset.Icc 1 (M - 1),
      (∑ d ∈ Finset.Icc 1 k,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          primeFreeDivisorDefect (k / d)) =
        psiRemainder k + 2 * Real.eulerMascheroniConstant := by
    intro k hk
    rw [← psiDefect_eq_mobius_primeFreeDivisorDefect
      (Finset.mem_Icc.mp hk).1, psiDefect_eq_psiRemainder_add]
  have hrewrite :
      (∑ k ∈ Finset.Icc 1 (M - 1),
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
          (∑ d ∈ Finset.Icc 1 k,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              primeFreeDivisorDefect (k / d))) =
      ∑ k ∈ Finset.Icc 1 (M - 1),
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
          (psiRemainder k + 2 * Real.eulerMascheroniConstant) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hpoint k hk]
  rw [hrewrite]
  have hsplit :
      (∑ k ∈ Finset.Icc 1 (M - 1),
        ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiRemainder k +
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
            (2 * Real.eulerMascheroniConstant))) =
      (∑ k ∈ Finset.Icc 1 (M - 1),
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiRemainder k) +
        2 * Real.eulerMascheroniConstant *
          (∑ k ∈ Finset.Icc 1 (M - 1),
            (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [mul_add]
  rw [hsplit, sum_sqrt_succ_sub_sqrt_Icc hM]

/-- Uniform normalized bound for the signed Möbius--divisor producer. -/
def MobiusDivisorSquareRootAbelBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 2 ≤ M →
    |mobiusDivisorSquareRootAbelMoment M / M| ≤ B

private theorem abs_gamma_sqrtBoundary_div_le
    {M : ℕ} (hM : 2 ≤ M) :
    |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      |2 * Real.eulerMascheroniConstant| := by
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hsqrtSq : Real.sqrt (M : ℝ) ^ (2 : ℕ) = (M : ℝ) :=
    Real.sq_sqrt hMR.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by
    nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by
    nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hratio : |Real.sqrt M - 1| / (M : ℝ) ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    exact (div_le_one hMR).2 (by linarith)
  rw [abs_div, abs_mul, abs_of_pos hMR]
  calc
    |2 * Real.eulerMascheroniConstant| * |Real.sqrt ↑M - 1| / ↑M =
        |2 * Real.eulerMascheroniConstant| *
          (|Real.sqrt ↑M - 1| / ↑M) := by ring
    _ ≤ |2 * Real.eulerMascheroniConstant| * 1 :=
      mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
    _ = _ := mul_one _

/-- Euler boundary is bounded and creates no gap between coherent and Möbius--divisor criteria. -/
theorem coherentSelbergSquareRootAbelBounded_iff_mobiusDivisor :
    CoherentSelbergSquareRootAbelBounded ↔
      MobiusDivisorSquareRootAbelBounded := by
  constructor
  · rintro ⟨B, hB, hcoherent⟩
    refine ⟨B + |2 * Real.eulerMascheroniConstant|, by positivity, ?_⟩
    intro M hM
    rw [mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary
      (by omega : 1 ≤ M), add_div]
    exact (abs_add_le _ _).trans
      (add_le_add (hcoherent M hM) (abs_gamma_sqrtBoundary_div_le hM))
  · rintro ⟨B, hB, hmobius⟩
    refine ⟨B + |2 * Real.eulerMascheroniConstant|, by positivity, ?_⟩
    intro M hM
    have hrel := mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary
      (by omega : 1 ≤ M)
    have hsolve :
        coherentSelbergSquareRootAbelMoment M / M =
          mobiusDivisorSquareRootAbelMoment M / M -
            (2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M := by
      rw [hrel]
      ring
    rw [hsolve]
    exact (abs_sub _ _).trans
      (add_le_add (hmobius M hM) (abs_gamma_sqrtBoundary_div_le hM))

/-- RH is exactly uniform boundedness of the prime-free signed Möbius--divisor Abel action. -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded :
    RiemannHypothesis ↔ MobiusDivisorSquareRootAbelBounded :=
  riemannHypothesis_iff_coherentSelbergSquareRootAbelBounded.trans
    coherentSelbergSquareRootAbelBounded_iff_mobiusDivisor

end RHTower
