import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCofinalLinearFiniteHankelDimension
import GaloisForLFunctions.RHTower.XiShiftedTerminalFrontierZeroPhaseLaw

/-!
# The least defective hard-edge block

For a shift `y`, let

`D(y) = min { N : the leading N-by-N shifted reciprocal Hankel block is not positive semidefinite }`

with the convention `D(y) = 0` when no such block exists.  Two independent estimates trap `D` on the
square-root shift scale as soon as it is nonzero.

* The parabolic degree horizon forbids a negative block of dimension `N` unless
  `y < horizon·N²`, so `√y < √horizon·D(y)`.  A first defect cannot hide below the hard-edge scale.
* Failure of the Riemann hypothesis produces one explicit Chebyshev packet family whose reciprocal
  pullback is negative at every large integral mass and has dimension at most linear in the mass, so
  `D(y) ≤ C√y`.  A negative witness never needs superlinear degree.

Together these are the two-sided hard-edge defect law.  It is the statement that Route-U degree
escape, after the unique scaling `N/√y`, is a compact phenomenon.
-/

open Filter

noncomputable section

namespace RHTower

/-- Dimensions at which the shifted reciprocal Hankel form takes a negative value. -/
def xiShiftedDefectiveSizes (y : ℝ) : Set ℕ :=
  {N : ℕ | ∃ c : Fin N → ℝ, xiShiftedReciprocalHankelQuadratic y c < 0}

/-- The least dimension at which the shifted reciprocal Hankel block fails to be positive
semidefinite; zero if every block is positive semidefinite. -/
def xiShiftedLeastDefectiveSize (y : ℝ) : ℕ := sInf (xiShiftedDefectiveSizes y)

/-- The empty coefficient vector has vanishing Hankel form, so dimension zero is never defective. -/
theorem xiShiftedReciprocalHankelQuadratic_of_isEmpty (y : ℝ) (c : Fin 0 → ℝ) :
    xiShiftedReciprocalHankelQuadratic y c = 0 := by
  simp [xiShiftedReciprocalHankelQuadratic]

theorem pos_of_mem_xiShiftedDefectiveSizes {y : ℝ} {N : ℕ}
    (hN : N ∈ xiShiftedDefectiveSizes y) : 0 < N := by
  obtain ⟨c, hc⟩ := hN
  rcases Nat.eq_zero_or_pos N with rfl | h
  · rw [xiShiftedReciprocalHankelQuadratic_of_isEmpty y c] at hc
    exact absurd hc (lt_irrefl 0)
  · exact h

/-- A negative Hankel value at dimension `N` bounds the least defective dimension by `N`. -/
theorem xiShiftedLeastDefectiveSize_le {y : ℝ} {N : ℕ} (c : Fin N → ℝ)
    (hneg : xiShiftedReciprocalHankelQuadratic y c < 0) :
    xiShiftedLeastDefectiveSize y ≤ N :=
  Nat.sInf_le ⟨c, hneg⟩

/-- Any defective dimension is strictly above the parabolic horizon scale. -/
theorem lt_horizon_mul_sq_of_mem_xiShiftedDefectiveSizes {y : ℝ} {N : ℕ}
    (hN : N ∈ xiShiftedDefectiveSizes y) :
    y < routeUParabolicDegreeHorizon * (N : ℝ) ^ 2 := by
  obtain ⟨c, hc⟩ := hN
  have hpos : 0 < N := pos_of_mem_xiShiftedDefectiveSizes ⟨c, hc⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, N = d + 1 := ⟨N - 1, by omega⟩
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    have hzero : xiShiftedReciprocalHankelQuadratic y (0 : Fin (d + 1) → ℝ) = 0 := by
      simp [xiShiftedReciprocalHankelQuadratic]
    rw [hzero] at hc
    exact absurd hc (lt_irrefl 0)
  by_contra hcon
  have hy : routeUParabolicDegreeHorizon * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ y := by
    push_cast at hcon ⊢
    linarith [le_of_not_gt hcon]
  exact absurd (xiShiftedReciprocalHankelQuadratic_pos_of_parabolic d c hcne hy) (not_lt.2 hc.le)

/-- A defective dimension exists exactly when the least defective dimension is positive. -/
theorem pos_xiShiftedLeastDefectiveSize_of_neg {y : ℝ} {N : ℕ} (c : Fin N → ℝ)
    (hneg : xiShiftedReciprocalHankelQuadratic y c < 0) :
    0 < xiShiftedLeastDefectiveSize y := by
  have hne : (xiShiftedDefectiveSizes y).Nonempty := ⟨N, ⟨c, hneg⟩⟩
  exact pos_of_mem_xiShiftedDefectiveSizes (Nat.sInf_mem hne)

/-- **The parabolic lower half of the hard-edge defect law.**  A first defect cannot occur below the
square-root shift scale. -/
theorem sqrt_lt_sqrt_horizon_mul_leastDefectiveSize {y : ℝ} (hy : 0 ≤ y) {N : ℕ}
    (c : Fin N → ℝ) (hneg : xiShiftedReciprocalHankelQuadratic y c < 0) :
    Real.sqrt y
      < Real.sqrt routeUParabolicDegreeHorizon * (xiShiftedLeastDefectiveSize y : ℝ) := by
  have hne : (xiShiftedDefectiveSizes y).Nonempty := ⟨N, ⟨c, hneg⟩⟩
  have hmem := Nat.sInf_mem hne
  have hlt := lt_horizon_mul_sq_of_mem_xiShiftedDefectiveSizes hmem
  have hD : (0 : ℝ) ≤ (xiShiftedLeastDefectiveSize y : ℝ) := Nat.cast_nonneg _
  have hHorizon : (0 : ℝ) ≤ routeUParabolicDegreeHorizon := routeUParabolicDegreeHorizon_pos.le
  have hsqrt : Real.sqrt y
      < Real.sqrt (routeUParabolicDegreeHorizon * (xiShiftedLeastDefectiveSize y : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt hy hlt
  rwa [Real.sqrt_mul hHorizon, Real.sqrt_sq hD] at hsqrt

/-- **(HEPW.1) The two-sided hard-edge defect law.**  If the Riemann hypothesis fails, then at every
sufficiently large integral hard-edge mass the least defective shifted-Hankel dimension is trapped
between two positive multiples of `√y`. -/
theorem exists_twoSided_xiShiftedLeastDefectiveSize_law_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ k : ℕ, K ≤ k →
      Real.sqrt (routeUHardEdgeMass (k : ℝ) ^ 2)
          < Real.sqrt routeUParabolicDegreeHorizon
              * (xiShiftedLeastDefectiveSize (routeUHardEdgeMass (k : ℝ) ^ 2) : ℝ)
        ∧ (xiShiftedLeastDefectiveSize (routeUHardEdgeMass (k : ℝ) ^ 2) : ℝ)
            ≤ C * Real.sqrt (routeUHardEdgeMass (k : ℝ) ^ 2) := by
  obtain ⟨P, t, n, K, hphase⟩ := xiShiftedHardEdgeCofinalLinearNegativePhase_of_not_rh hRH
  refine ⟨((n : ℝ) + 3), K, by positivity, fun k hk => ?_⟩
  obtain ⟨hneg, _, hsize⟩ := hphase k hk
  have hmass : routeUHardEdgeMass (k : ℝ) = (k : ℝ) + 1 := by
    rw [routeUHardEdgeMass, abs_of_nonneg (Nat.cast_nonneg k)]
    ring
  have hmasspos : 0 < routeUHardEdgeMass (k : ℝ) := routeUHardEdgeMass_pos (k : ℝ)
  have hsqrt : Real.sqrt (routeUHardEdgeMass (k : ℝ) ^ 2) = routeUHardEdgeMass (k : ℝ) :=
    Real.sqrt_sq hmasspos.le
  have hquad : xiShiftedReciprocalHankelQuadratic (routeUHardEdgeMass (k : ℝ) ^ 2)
      (xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ))
        (routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t))) < 0 := by
    simpa only [routeUExplicitPolynomialGaussianFiniteHankelQuadratic,
      routeUPolynomialGaussianFiniteHankelQuadratic, routeUExplicitFiniteChebyshevPacket]
      using hneg
  refine ⟨sqrt_lt_sqrt_horizon_mul_leastDefectiveSize (by positivity) _ hquad, ?_⟩
  have hle : xiShiftedLeastDefectiveSize (routeUHardEdgeMass (k : ℝ) ^ 2)
      ≤ routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) :=
    xiShiftedLeastDefectiveSize_le _ hquad
  have hchain : (xiShiftedLeastDefectiveSize (routeUHardEdgeMass (k : ℝ) ^ 2) : ℝ)
      ≤ (((n + 1) * (k + 1) + 2 : ℕ) : ℝ) := by
    exact_mod_cast le_trans hle hsize
  have hlinear : (((n + 1) * (k + 1) + 2 : ℕ) : ℝ)
      ≤ ((n : ℝ) + 3) * routeUHardEdgeMass (k : ℝ) := by
    rw [hmass]
    push_cast
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hn0, hk0]
  rw [hsqrt]
  linarith [hchain, hlinear]

/-- Under the Riemann hypothesis every shifted reciprocal Hankel block is positive definite, so no
dimension is defective. -/
theorem xiShiftedDefectiveSizes_eq_empty_of_rh (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y) :
    xiShiftedDefectiveSizes y = ∅ := by
  ext N
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, hc⟩
  rcases eq_or_ne c 0 with rfl | hcne
  · rw [show xiShiftedReciprocalHankelQuadratic y (0 : Fin N → ℝ) = 0 by
      simp [xiShiftedReciprocalHankelQuadratic]] at hc
    exact absurd hc (lt_irrefl 0)
  · exact absurd (xiShiftedReciprocalHankelQuadratic_pos_of_riemannHypothesis hRH hy c hcne)
      (not_lt.2 hc.le)

theorem xiShiftedLeastDefectiveSize_eq_zero_of_rh (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y) :
    xiShiftedLeastDefectiveSize y = 0 := by
  rw [xiShiftedLeastDefectiveSize, xiShiftedDefectiveSizes_eq_empty_of_rh hRH hy]
  exact Nat.sInf_empty

/-- **(HEPW.19) The exact cofinal hard-edge criterion.**  The Riemann hypothesis fails exactly when
some nonnegative shift has a defective block at all. -/
theorem not_riemannHypothesis_iff_exists_defective_hardEdge_block :
    ¬ RiemannHypothesis ↔ ∃ y : ℝ, 0 ≤ y ∧ xiShiftedLeastDefectiveSize y ≠ 0 := by
  constructor
  · intro hRH
    obtain ⟨C, K, hC, h⟩ := exists_twoSided_xiShiftedLeastDefectiveSize_law_of_not_rh hRH
    refine ⟨routeUHardEdgeMass (K : ℝ) ^ 2, by positivity, ?_⟩
    obtain ⟨hlow, -⟩ := h K le_rfl
    intro h0
    have hpos : 0 < Real.sqrt (routeUHardEdgeMass (K : ℝ) ^ 2) := by
      rw [Real.sqrt_sq (routeUHardEdgeMass_pos (K : ℝ)).le]
      exact routeUHardEdgeMass_pos (K : ℝ)
    rw [h0, Nat.cast_zero, mul_zero] at hlow
    linarith
  · rintro ⟨y, hy, hne⟩ hRH
    exact hne (xiShiftedLeastDefectiveSize_eq_zero_of_rh hRH hy)

end RHTower

end
