import GaloisForLFunctions.RHTower.SuzukiEulerianSelbergAbelWeld

/-!
# Exact outgoing-charge classification of the literal SP-E discrepancy

The literal Eulerian SP-E current differs from terminal normalized Chebyshev error by the
completed outgoing charge plus a source-free polar--lattice residual.  This file gives that
residual a uniform explicit bound.  Hence uniform boundedness of this actual signed SP-E
discrepancy is equivalent to RH, and does not define a second independent cancellation problem
beyond the completed outgoing source.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Literal SP-E mass-error discrepancy from its terminal normalized Chebyshev error. -/
def suzukiEulerianCompletedOutgoingDiscrepancy (N : ℕ) : ℝ :=
  suzukiChebyshevMassErrorCesaroDefect N -
    criticalMellinNormalizedChebyshevError (Real.log ((N + 1 : ℕ) : ℝ))

/-- Source-free polar--lattice residual left after extracting the completed outgoing charge. -/
def suzukiEulerianCompletedOutgoingResidual (N : ℕ) : ℝ :=
  (coherentSquareRootPolarLatticeDefect (N + 1) -
    suzukiEulerianSelbergLatticePrefix N -
    suzukiEulerianCoherentBoundaryAnchor) / (N + 1 : ℕ)

/-- Exact actual-source decomposition: no prime or polar absolute value is taken. -/
theorem suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_charge_add_residual
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiEulerianCompletedOutgoingDiscrepancy N =
      -unitRieszCoherentCompletedOutgoingCharge (N + 1) +
        suzukiEulerianCompletedOutgoingResidual N := by
  rw [suzukiEulerianCompletedOutgoingDiscrepancy,
    suzukiEulerianCompletedOutgoingResidual,
    suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_completedOutgoing hN]
  ring

/-- The source-free residual is uniformly bounded, with a fully explicit bound. -/
theorem abs_suzukiEulerianCompletedOutgoingResidual_le (N : ℕ) :
    |suzukiEulerianCompletedOutgoingResidual N| ≤
      5 + |suzukiEulerianCoherentBoundaryAnchor| := by
  have hMpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hMone : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ N + 1)
  have hsqrtSq : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ 2 = ((N + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hMpos.le
  have hsqrtLe : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  have hdef :
      |coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hMpos]
    calc
      |coherentSquareRootPolarLatticeDefect (N + 1)| / ((N + 1 : ℕ) : ℝ) ≤
          Real.sqrt ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right
          (abs_coherentSquareRootPolarLatticeDefect_le (by omega : 1 ≤ N + 1)) hMpos.le
      _ ≤ 1 := (div_le_one hMpos).2 hsqrtLe
  have hshift : Real.sqrt ((N + 2 : ℕ) : ℝ) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    have hnat : ((N + 2 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N + 2 ≤ 4 * (N + 1))
    calc
      Real.sqrt ((N + 2 : ℕ) : ℝ) ≤
          Real.sqrt (4 * ((N + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hnat
      _ = 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have hlattice :
      |suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ)| ≤ 4 := by
    rw [abs_div,
      abs_of_nonneg (suzukiEulerianSelbergLatticePrefix_nonneg_le N).1,
      abs_of_pos hMpos]
    apply (div_le_iff₀ hMpos).2
    calc
      suzukiEulerianSelbergLatticePrefix N ≤ 2 * Real.sqrt ((N + 2 : ℕ) : ℝ) :=
        (suzukiEulerianSelbergLatticePrefix_nonneg_le N).2
      _ ≤ 4 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by linarith
      _ ≤ 4 * ((N + 1 : ℕ) : ℝ) := by linarith
  have hanchor :
      |suzukiEulerianCoherentBoundaryAnchor / (N + 1 : ℕ)| ≤
        |suzukiEulerianCoherentBoundaryAnchor| := by
    rw [abs_div, abs_of_pos hMpos]
    apply (div_le_iff₀ hMpos).2
    exact le_mul_of_one_le_right (abs_nonneg _) hMone
  rw [suzukiEulerianCompletedOutgoingResidual]
  have hrearrange :
      (coherentSquareRootPolarLatticeDefect (N + 1) -
        suzukiEulerianSelbergLatticePrefix N -
        suzukiEulerianCoherentBoundaryAnchor) / (N + 1 : ℕ) =
      coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ) -
        suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ) -
        suzukiEulerianCoherentBoundaryAnchor / (N + 1 : ℕ) := by
    ring
  rw [hrearrange]
  calc
    |coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ) -
        suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ) -
        suzukiEulerianCoherentBoundaryAnchor / (N + 1 : ℕ)| ≤
        |coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ)| +
          |suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ)| +
          |suzukiEulerianCoherentBoundaryAnchor / (N + 1 : ℕ)| := by
      calc
        _ ≤ |coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ) -
            suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ)| +
            |suzukiEulerianCoherentBoundaryAnchor / (N + 1 : ℕ)| := abs_sub _ _
        _ ≤ _ := by
          gcongr
          exact abs_sub _ _
    _ ≤ 5 + |suzukiEulerianCoherentBoundaryAnchor| := by linarith

/-- Uniform boundedness of the literal completed SP-E discrepancy. -/
def SuzukiEulerianCompletedOutgoingDiscrepancyBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 2 ≤ N →
    |suzukiEulerianCompletedOutgoingDiscrepancy N| ≤ B

/-- **SP-E reduction.** Boundedness of the actual signed SP-E discrepancy is equivalent to RH.
The only nontrivial unbounded term is the pre-existing completed outgoing charge. -/
theorem riemannHypothesis_iff_suzukiEulerianCompletedOutgoingDiscrepancyBounded :
    RiemannHypothesis ↔ SuzukiEulerianCompletedOutgoingDiscrepancyBounded := by
  constructor
  · intro hRH
    obtain ⟨B, hB, hres⟩ :=
      riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mp hRH
    refine ⟨B / 2 + 5 + |suzukiEulerianCoherentBoundaryAnchor|, by positivity, ?_⟩
    intro N hN
    have hcharge : |unitRieszCoherentCompletedOutgoingCharge (N + 1)| ≤ B / 2 := by
      rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half (by omega : 2 ≤ N + 1),
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (hres (N + 1) (by omega)) (by norm_num)
    rw [suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_charge_add_residual hN]
    calc
      |-unitRieszCoherentCompletedOutgoingCharge (N + 1) +
          suzukiEulerianCompletedOutgoingResidual N| ≤
          |unitRieszCoherentCompletedOutgoingCharge (N + 1)| +
            |suzukiEulerianCompletedOutgoingResidual N| := by
        simpa only [abs_neg] using abs_add_le
          (-unitRieszCoherentCompletedOutgoingCharge (N + 1))
          (suzukiEulerianCompletedOutgoingResidual N)
      _ ≤ B / 2 + 5 + |suzukiEulerianCoherentBoundaryAnchor| := by
        linarith [abs_suzukiEulerianCompletedOutgoingResidual_le N]
  · rintro ⟨B, hB, hdisc⟩
    apply riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mpr
    refine ⟨2 * (B + 5 + |suzukiEulerianCoherentBoundaryAnchor| +
      |unitRieszCoherentCompletedOutgoingCharge 2|), by positivity, ?_⟩
    intro M hM
    by_cases hMthree : 3 ≤ M
    · have hN : 2 ≤ M - 1 := by omega
      have hsource :=
        suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_charge_add_residual hN
      have hNadd : M - 1 + 1 = M := Nat.sub_add_cancel (by omega : 1 ≤ M)
      rw [hNadd] at hsource
      have hcharge : |unitRieszCoherentCompletedOutgoingCharge M| ≤
          B + 5 + |suzukiEulerianCoherentBoundaryAnchor| := by
        have hrewrite : unitRieszCoherentCompletedOutgoingCharge M =
            suzukiEulerianCompletedOutgoingResidual (M - 1) -
              suzukiEulerianCompletedOutgoingDiscrepancy (M - 1) := by
          linarith
        rw [hrewrite]
        calc
          |suzukiEulerianCompletedOutgoingResidual (M - 1) -
              suzukiEulerianCompletedOutgoingDiscrepancy (M - 1)| ≤
              |suzukiEulerianCompletedOutgoingResidual (M - 1)| +
                |suzukiEulerianCompletedOutgoingDiscrepancy (M - 1)| := abs_sub _ _
          _ ≤ B + 5 + |suzukiEulerianCoherentBoundaryAnchor| := by
            linarith [abs_suzukiEulerianCompletedOutgoingResidual_le (M - 1),
              hdisc (M - 1) hN]
      have hresEq : criticalMellinChebyshevResolventSource (Real.log M) =
          2 * unitRieszCoherentCompletedOutgoingCharge M := by
        rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM]
        ring
      rw [hresEq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [abs_nonneg (unitRieszCoherentCompletedOutgoingCharge 2)]
    · have hMtwo : M = 2 := by omega
      subst M
      have hresEq : criticalMellinChebyshevResolventSource (Real.log 2) =
          2 * unitRieszCoherentCompletedOutgoingCharge 2 := by
        rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half (by omega)]
        ring
      norm_num at hresEq ⊢
      rw [hresEq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hB, abs_nonneg suzukiEulerianCoherentBoundaryAnchor,
        abs_nonneg (unitRieszCoherentCompletedOutgoingCharge 2)]

end

end GaloisForLFunctions.RHTower
