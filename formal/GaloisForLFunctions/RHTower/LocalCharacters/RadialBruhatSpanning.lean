import GaloisForLFunctions.RHTower.FieldOnePadicRadialBruhatClassification

/-!
# Finite ball and shell expansion of radial Bruhat tests

A radial Bruhat test is constant on a sufficiently small ball and zero
outside a sufficiently large ball. The intervening valuation shells give
an exact finite expansion, including tests nonzero at the origin.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

open Set
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- The value of a radial test on the shell of valuation `k`. -/
def radialValue (f : compactlySupportedLocallyConstant ℚ_[p]) (k : ℤ) : ℂ :=
  f.1 ((fieldOnePadicValuationUnitForward p (Multiplicative.ofAdd k, 1) : ℚ_[p]ˣ) : ℚ_[p])

/-- Every radial Bruhat test is a small-ball constant plus finitely many shells. -/
theorem exists_ball_shell_decomposition (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p], f.1 ((u : ℤ_[p]) * x) = f.1 x) :
    ∃ N L : ℕ, f = f.1 0 • fieldOnePadicSoninBall p (-(L : ℤ)) +
      ∑ k ∈ Finset.Ico (-(N : ℤ)) (L : ℤ),
        radialValue p f k • fieldOnePadicSoninShell p (-k) := by
  obtain ⟨N, L, hsupport, hperiod⟩ := fieldOnePadicBruhat_exists_finiteLevel p f
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hconst (x : ℚ_[p]) (hx : x ∈ fieldOnePadicSoninBallSet p (-(L : ℤ))) :
      f.1 x = f.1 0 := by
    obtain ⟨z, hz⟩ := hx
    have hz' : (z : ℚ_[p]) = (p : ℚ_[p]) ^ (-(L : ℤ)) * x := by
      simpa only [Units.val_zpow_eq_zpow_val, fieldOnePadicPrimeUnit] using hz
    have hxz : x = (p : ℚ_[p]) ^ L * (z : ℚ_[p]) := by
      rw [hz', ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hp]
      simp
    rw [hxz]
    simpa only [zero_add] using hperiod 0 z
  have heval (x : ℚ_[p]) :
      (f.1 0 • fieldOnePadicSoninBall p (-(L : ℤ)) +
        ∑ k ∈ Finset.Ico (-(N : ℤ)) (L : ℤ),
          radialValue p f k • fieldOnePadicSoninShell p (-k)).1 x =
      f.1 0 * (fieldOnePadicSoninBall p (-(L : ℤ))).1 x +
        ∑ k ∈ Finset.Ico (-(N : ℤ)) (L : ℤ),
          radialValue p f k * (fieldOnePadicSoninShell p (-k)).1 x := by
    change fieldOnePadicBruhatEvalLinear p x _ = _
    simp only [map_add, map_sum, map_smul, fieldOnePadicBruhatEvalLinear_apply,
      smul_eq_mul]
  have hcoord (k : ℤ) (u : ℤ_[p]ˣ) :
      f.1 ((fieldOnePadicValuationUnitForward p (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) :
        ℚ_[p]) =
      (f.1 0 • fieldOnePadicSoninBall p (-(L : ℤ)) +
        ∑ j ∈ Finset.Ico (-(N : ℤ)) (L : ℤ),
          radialValue p f j • fieldOnePadicSoninShell p (-j)).1
        ((fieldOnePadicValuationUnitForward p (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) :
          ℚ_[p]) := by
    have hrad : f.1 ((fieldOnePadicValuationUnitForward p
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) = radialValue p f k := by
      unfold radialValue
      have hmul : ((u : ℤ_[p]) : ℚ_[p]) *
          ((fieldOnePadicValuationUnitForward p (Multiplicative.ofAdd k, 1) : ℚ_[p]ˣ) :
            ℚ_[p]) =
          ((fieldOnePadicValuationUnitForward p (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) :
            ℚ_[p]) := by
        dsimp [fieldOnePadicValuationUnitForward]
        simp only [mul_one]
        ring
      rw [← hmul]
      exact hunit u _
    rw [heval, fieldOnePadicSoninBall_apply_eq_indicator,
      fieldOnePadicSoninBallSet_mem_forward_iff]
    by_cases hhigh : (L : ℤ) ≤ k
    · rw [if_pos (by omega), mul_one]
      rw [hconst _ ((fieldOnePadicSoninBallSet_mem_forward_iff p _ _ _).mpr (by omega))]
      have hsum : (∑ j ∈ Finset.Ico (-(N : ℤ)) (L : ℤ), radialValue p f j *
          (fieldOnePadicSoninShell p (-j)).1
            ((fieldOnePadicValuationUnitForward p (Multiplicative.ofAdd k, u) :
              ℚ_[p]ˣ) : ℚ_[p])) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjL := (Finset.mem_Ico.mp hj).2
        rw [fieldOnePadicSoninShell_apply_forward, if_neg (by omega), mul_zero]
      rw [hsum, add_zero]
    · rw [if_neg (by omega), mul_zero, zero_add, hrad]
      by_cases hlow : k < -(N : ℤ)
      · have hzero : radialValue p f k = 0 := by
          apply Classical.byContradiction
          intro hne
          have hx := hsupport (subset_tsupport f.1 hne)
          have hv := (fieldOnePadicDenominatorStage_coordinates_iff p N k 1).mp hx
          omega
        rw [hzero]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        have hjN := (Finset.mem_Ico.mp hj).1
        rw [fieldOnePadicSoninShell_apply_forward, if_neg (by omega), mul_zero]
      · have hk : k ∈ Finset.Ico (-(N : ℤ)) (L : ℤ) := Finset.mem_Ico.mpr (by omega)
        rw [Finset.sum_eq_single_of_mem k hk]
        · rw [fieldOnePadicSoninShell_apply_forward]
          simp
        · intro j _ hj
          rw [fieldOnePadicSoninShell_apply_forward, if_neg (by omega), mul_zero]
  refine ⟨N, L, ?_⟩
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [heval]
    simp [fieldOnePadicSoninBall_apply]
  · let a : ℚ_[p]ˣ := Units.mk0 x hx
    let z := (fieldOnePadicValuationUnitMulEquiv p).symm a
    have hz : fieldOnePadicValuationUnitForward p
        (Multiplicative.ofAdd z.1.toAdd, z.2) = a := by
      change fieldOnePadicValuationUnitMulEquiv p z = a
      exact (fieldOnePadicValuationUnitMulEquiv p).apply_symm_apply a
    have hxcoord := congrArg Units.val hz
    change ((fieldOnePadicValuationUnitForward p
      (Multiplicative.ofAdd z.1.toAdd, z.2) : ℚ_[p]ˣ) : ℚ_[p]) = x at hxcoord
    rw [← hxcoord]
    exact hcoord z.1.toAdd z.2

#print axioms exists_ball_shell_decomposition

end GaloisForLFunctions.RHTower.LocalCharacters
