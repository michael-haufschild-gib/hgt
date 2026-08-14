import GaloisForLFunctions.RHTower.FieldOnePadicSoninApproximation

/-!
# Classification of radial p-adic Bruhat functions with a Sonin gap

A compactly supported locally constant function which is invariant under
`ℤ_pˣ` and vanishes on `pℤ_p` is a finite sum of the source shells
`ε₀, …, ε_N`.  This is the exact finite radial algebra used in the proof of
Connes--Consani--Moscovici Proposition 4.4.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

def fieldOnePadicRadialShellCoefficient
    (f : compactlySupportedLocallyConstant ℚ_[p]) (n : ℕ) : ℂ :=
  f.1 (((fieldOnePadicValuationUnitForward p
    (Multiplicative.ofAdd (-(n : ℤ)), 1) : ℚ_[p]ˣ) : ℚ_[p]))

theorem fieldOnePadicBruhatEval_radialShellSum
    (f : compactlySupportedLocallyConstant ℚ_[p]) (N : ℕ) (x : ℚ_[p]) :
    (∑ n ∈ Finset.range (N + 1),
      (fieldOnePadicRadialShellCoefficient p f n) •
        fieldOnePadicSoninShell p (n : ℤ)).1 x =
      ∑ n ∈ Finset.range (N + 1),
        fieldOnePadicRadialShellCoefficient p f n *
          (fieldOnePadicSoninShell p (n : ℤ)).1 x := by
  change fieldOnePadicBruhatEvalLinear p x
      (∑ n ∈ Finset.range (N + 1),
        (fieldOnePadicRadialShellCoefficient p f n) •
          fieldOnePadicSoninShell p (n : ℤ)) = _
  simp only [map_sum, map_smul, fieldOnePadicBruhatEvalLinear_apply,
    smul_eq_mul]

theorem fieldOnePadicRadialBruhat_apply_forward_eq_shellSum
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0) :
    ∃ N : ℕ, ∀ k : ℤ, ∀ u : ℤ_[p]ˣ,
      f.1 (((fieldOnePadicValuationUnitForward p
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) =
        ∑ n ∈ Finset.range (N + 1),
          fieldOnePadicRadialShellCoefficient p f n *
            (fieldOnePadicSoninShell p (n : ℤ)).1
              (((fieldOnePadicValuationUnitForward p
                (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) := by
  obtain ⟨N, L, hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  refine ⟨N, fun k u => ?_⟩
  let x : ℚ_[p] :=
    ((fieldOnePadicValuationUnitForward p
      (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])
  let xone : ℚ_[p] :=
    ((fieldOnePadicValuationUnitForward p
      (Multiplicative.ofAdd k, 1) : ℚ_[p]ˣ) : ℚ_[p])
  have hrad : f.1 x = f.1 xone := by
    have hmul' : (((u : ℤ_[p]) : ℚ_[p])) * xone = x := by
      dsimp [x, xone, fieldOnePadicValuationUnitForward]
      simp only [mul_one]
      ring
    rw [← hmul']
    exact hunit u xone
  rw [hrad]
  by_cases hkpos : 1 ≤ k
  · have hxinner : xone ∈ fieldOnePadicSoninInnerBall p := by
      change xone ∈ fieldOnePadicSoninBallSet p (-1)
      rw [fieldOnePadicSoninBallSet_mem_forward_iff]
      omega
    rw [hgap xone hxinner]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_range] at hn
    rw [fieldOnePadicSoninShell_apply_forward]
    rw [if_neg]
    ring
    omega
  · by_cases hklow : k < -(N : ℤ)
    · have hxoutside : xone ∉ fieldOnePadicDenominatorStage p N := by
        have hcoord := fieldOnePadicDenominatorStage_coordinates_iff p N k 1
        change xone ∈ fieldOnePadicDenominatorStage p N ↔
          -(N : ℤ) ≤ k at hcoord
        exact hcoord.not.mpr (by omega)
      have hfx : f.1 xone = 0 := by
        by_contra hne
        exact hxoutside (hsupport (subset_tsupport f.1 hne))
      rw [hfx]
      symm
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_range] at hn
      rw [fieldOnePadicSoninShell_apply_forward]
      rw [if_neg]
      ring
      omega
    · let n : ℕ := (-k).toNat
      have hk0 : k ≤ 0 := by omega
      have hnval : (n : ℤ) = -k := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ -k)]
      have hnmem : n ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        omega
      rw [Finset.sum_eq_single_of_mem n hnmem]
      · rw [fieldOnePadicSoninShell_apply_forward]
        unfold fieldOnePadicRadialShellCoefficient
        have hkn : k = -(n : ℤ) := by omega
        dsimp [xone]
        rw [hkn]
        simp
      · intro m hm hmne
        rw [fieldOnePadicSoninShell_apply_forward]
        rw [if_neg]
        ring
        omega

theorem fieldOnePadicRadialBruhat_eq_shellSum
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0) :
    ∃ N : ℕ,
      f = ∑ n ∈ Finset.range (N + 1),
        (fieldOnePadicRadialShellCoefficient p f n) •
          fieldOnePadicSoninShell p (n : ℤ) := by
  obtain ⟨N, hN⟩ :=
    fieldOnePadicRadialBruhat_apply_forward_eq_shellSum p f hunit hgap
  refine ⟨N, ?_⟩
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hgap 0]
    · rw [fieldOnePadicBruhatEval_radialShellSum]
      simp
    · change 0 ∈ fieldOnePadicSoninBallSet p (-1)
      refine ⟨(0 : ℤ_[p]), ?_⟩
      simp
  · let a : ℚ_[p]ˣ := Units.mk0 x hx
    let z := (fieldOnePadicValuationUnitContinuousMulEquiv p).symm a
    let k : ℤ := z.1.toAdd
    let u : ℤ_[p]ˣ := z.2
    have hz : z = (Multiplicative.ofAdd k, u) := by
      apply Prod.ext
      · exact Multiplicative.toAdd.injective (by rfl)
      · rfl
    have ha : fieldOnePadicValuationUnitForward p
        (Multiplicative.ofAdd k, u) = a := by
      change (fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) = a
      rw [← hz]
      exact (fieldOnePadicValuationUnitContinuousMulEquiv p).apply_symm_apply a
    have hxcoord :
        ((fieldOnePadicValuationUnitForward p
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) = x :=
      congrArg Units.val ha
    rw [← hxcoord]
    rw [fieldOnePadicBruhatEval_radialShellSum]
    exact hN k u

end

end GaloisForLFunctions.RHTower
