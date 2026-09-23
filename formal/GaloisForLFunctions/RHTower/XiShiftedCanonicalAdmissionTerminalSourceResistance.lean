import GaloisForLFunctions.HTGeometry.GaussTerminalSourceResistance
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionVacuumFreeHardEdgeSourceCapacity

/-!
# Canonical shifted-Xi terminal-source resistance

The literal current/adjacent vacuum-free completed `P^sharp` producer carries an endogenous
capacity at each nonzero current Gauss root.  Multiplying its terminal source product by the
canonical Gauss resistance share removes both Christoffel weight and root derivative:

`share * (Padé residue * source capacity) = y * x^(4 : ℕ) * preceding norm`.

Across all current roots the shares form a probability law.  Thus terminal-source loss is exactly
loss of tightness of an admission-dependent probability, not failure of source formation and not a
fixed linear report from the Gamma corona.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Current Gauss-root resistance share selected by a degree-`n` shifted-Xi admission. -/
def xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  HTGeometry.gaussTerminalSourceResistance
    (xiShiftedRealMomentSequence w) (n - 1) x

/-- Generic source-terminal resistance law before shifted-Xi specialization. -/
theorem gaussTerminalSourceResistance_mul_hardEdgeTerminalMass_eq
    {s : ℕ → ℝ} {N m : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hmN : m + 1 < N) (y : ℝ) {x : ℝ}
    (hroot : (HTGeometry.monicOrtho s (m + 1)).eval x = 0) :
    HTGeometry.gaussTerminalSourceResistance s m x *
        xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
          (HTGeometry.monicOrtho s (m + 1)) x =
      y * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m := by
  have hcd := HTGeometry.christoffel_mul_derivative_mul_prev_eq_normSq_below
    h hmN hroot
  have hnorm : HTGeometry.monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below h (show m < N by omega))
  simp only [HTGeometry.gaussTerminalSourceResistance,
    xiShiftedHardEdgeGaussTerminalMass, Nat.add_sub_cancel]
  calc
    (HTGeometry.christoffel s m x * (HTGeometry.monicOrtho s m).eval x ^ (2 : ℕ) /
          HTGeometry.monicOrthoNormSq s m) *
        (y * x ^ (4 : ℕ) * HTGeometry.christoffel s m x *
          (HTGeometry.monicOrtho s (m + 1)).derivative.eval x ^ (2 : ℕ)) =
      y * x ^ (4 : ℕ) *
        (HTGeometry.christoffel s m x *
          (HTGeometry.monicOrtho s (m + 1)).derivative.eval x *
          (HTGeometry.monicOrtho s m).eval x) ^ (2 : ℕ) /
        HTGeometry.monicOrthoNormSq s m := by ring
    _ = y * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m ^ (2 : ℕ) /
        HTGeometry.monicOrthoNormSq s m := by rw [hcd]
    _ = y * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m := by
      field_simp

/-- **Reciprocal terminal-source conservation.** If the mass parameter and every current Gauss
node are nonzero, the source products themselves recover the full admission probability by one
nonlinear all-root identity. -/
theorem sum_normalized_hardEdgeTerminalMass_eq_one
    {s : ℕ → ℝ} {N m : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hmN : m + 1 < N) {y : ℝ} (hy : y ≠ 0)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes s m, x ≠ 0) :
    ∑ x ∈ HTGeometry.gaussNodes s m,
        (y * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m) /
          xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
            (HTGeometry.monicOrtho s (m + 1)) x = 1 := by
  calc
    _ = ∑ x ∈ HTGeometry.gaussNodes s m,
        HTGeometry.gaussTerminalSourceResistance s m x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hroot : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 :=
        (HTGeometry.mem_gaussNodes_iff m x).mp hx
      have hproduct := gaussTerminalSourceResistance_mul_hardEdgeTerminalMass_eq
        h hmN y hroot
      have hnorm : HTGeometry.monicOrthoNormSq s m ≠ 0 :=
        ne_of_gt (HTGeometry.monicOrthoNorm_pos_below h (by omega))
      have hrhs : y * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m ≠ 0 :=
        mul_ne_zero (mul_ne_zero hy (pow_ne_zero 4 (hnodes x hx))) hnorm
      have hmass :
          xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
            (HTGeometry.monicOrtho s (m + 1)) x ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hproduct
        exact hrhs hproduct.symm
      exact (div_eq_iff hmass).2 hproduct.symm
    _ = 1 := HTGeometry.sum_gaussTerminalSourceResistance_eq_one h hmN

/-- Current shifted-Xi Gauss-root resistance shares sum to one. -/
theorem sum_xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance_eq_one
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  simpa only [xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance,
    Nat.succ_sub_one] using
    HTGeometry.sum_gaussTerminalSourceResistance_eq_one hbelow (m := m) (by omega)

/-- Every current shifted-Xi Gauss-root resistance share is positive. -/
theorem xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance_pos
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ}
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0) :
    0 < xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hroot' : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 := by
    rw [← hP]
    exact hroot
  simpa only [xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance,
    Nat.succ_sub_one, s] using
    HTGeometry.gaussTerminalSourceResistance_pos hbelow (by omega) hroot'

/-- **Literal current/adjacent completed-source resistance law.** At every nonzero current root,
the admission share times Padé residue times endogenous capacity of the already-formed vacuum-free
mixed/completed `P^sharp` source is exactly preceding norm times the fourth hard-root monomial. -/
theorem xiShiftedCanonicalAdmissionTerminalSourceResistance_mul_residue_mul_vacuumFreeCapacity_eq
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ} (hx : x ≠ 0)
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x *
        (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
          xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
            w n x) =
      w ^ (2 : ℕ) * x ^ (4 : ℕ) *
        HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hroot' : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 := by
    rw [← hP]
    exact hroot
  have hsource :=
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
      (w := w) (n := m + 1) hx hroot
  rw [hsource]
  change HTGeometry.gaussTerminalSourceResistance s m x *
      xiShiftedHardEdgeGaussTerminalMass (w ^ (2 : ℕ)) s (m + 1)
        (HTGeometry.monicMomentAdmissionPolynomial s (m + 1)) x =
    w ^ (2 : ℕ) * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m
  rw [hP]
  exact gaussTerminalSourceResistance_mul_hardEdgeTerminalMass_eq
    hbelow (by omega) (w ^ (2 : ℕ)) hroot'

/-- **Literal nonlinear arithmetic source aggregate.** Away from the zero hard node, reciprocal
normalization of actual Padé-residue/completed-capacity products is exactly one.  The denominator
is formed by the current/adjacent vacuum-free `P^sharp` source before this all-root aggregation. -/
theorem sum_xiShiftedCanonicalAdmission_normalizedResidueMulVacuumFreeCapacity_eq_one
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) :
    ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        (w ^ (2 : ℕ) * x ^ (4 : ℕ) *
          HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1)) /
          (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
            xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
              w n x) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodes ⊢
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  calc
    _ = ∑ x ∈ HTGeometry.gaussNodes s m,
        (w ^ (2 : ℕ) * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m) /
          xiShiftedHardEdgeGaussTerminalMass (w ^ (2 : ℕ)) s (m + 1)
            (HTGeometry.monicOrtho s (m + 1)) x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x ≠ 0 := hnodes x hx
      have hrootOrtho : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 :=
        (HTGeometry.mem_gaussNodes_iff m x).mp hx
      have hrootAdmission :
          (HTGeometry.monicMomentAdmissionPolynomial s (m + 1)).eval x = 0 := by
        rw [hP]
        exact hrootOrtho
      rw [xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
        hx0 hrootAdmission]
      simp only [xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass, s]
      rw [hP]
    _ = 1 := sum_normalized_hardEdgeTerminalMass_eq_one hbelow (by omega)
      (pow_ne_zero 2 hw) hnodes

/-- Ratio form using current and adjacent canonical admissions. -/
theorem xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance_eq_currentAdjacentRatio
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ}
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x =
      -(HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) (n + 1)).eval x /
        (HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n).derivative.eval x) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hPnext : HTGeometry.monicMomentAdmissionPolynomial s (m + 2) =
      HTGeometry.monicOrtho s (m + 2) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  have hroot' : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 := by
    rw [← hP]
    exact hroot
  simpa only [xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance,
    Nat.succ_sub_one, hP, hPnext, s] using
    HTGeometry.gaussTerminalSourceResistance_eq_neg_next_div_beta_mul_derivative
      hbelow (by omega) hroot'

/-- Closed capstone: literal source products are normalized by one positive, admission-dependent
all-root probability. -/
theorem xiShiftedCanonicalAdmission_vacuumFreeTerminalSourceResistanceLaw
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    (∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x = 1) ∧
      (∀ x : ℝ,
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n).eval x = 0 →
        0 < xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x) ∧
      (∀ x : ℝ, x ≠ 0 →
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n).eval x = 0 →
        xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x *
            (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
              xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
                w n x) =
          w ^ (2 : ℕ) * x ^ (4 : ℕ) *
            HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1)) := by
  refine ⟨sum_xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance_eq_one hn hH,
    ?_, ?_⟩
  · intro x hroot
    exact xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance_pos hn hH hroot
  · intro x hx hroot
    exact
      xiShiftedCanonicalAdmissionTerminalSourceResistance_mul_residue_mul_vacuumFreeCapacity_eq
        hn hH hx hroot

end

end RHTower
