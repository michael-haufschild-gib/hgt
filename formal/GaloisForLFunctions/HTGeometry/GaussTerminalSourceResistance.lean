import GaloisForLFunctions.HTGeometry.FiniteConfluentDarboux

/-!
# Gauss terminal-source resistance

At the roots of the current monic orthogonal admission, the preceding polynomial defines a
canonical positive terminal share. Gaussian exactness makes the shares sum to one, confluent
Christoffel--Darboux identifies each share with a preceding/current derivative ratio, and the
three-term recurrence expresses the same share using the adjacent admission.

These are finite positive-block theorems. No representing measure, computation, or infinite
moment extension is used.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Terminal share of a current Gauss root, normalized by the preceding monic norm. -/
noncomputable def gaussTerminalSourceResistance
    (s : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  christoffel s m x * (monicOrtho s m).eval x ^ 2 / monicOrthoNormSq s m

/-- **Terminal-share conservation.** All root shares of one finite positive admission sum to one. -/
theorem sum_gaussTerminalSourceResistance_eq_one {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) :
    ∑ x ∈ gaussNodes s m, gaussTerminalSourceResistance s m x = 1 := by
  have hpdeg : ((monicOrtho s m) ^ 2).degree < ((2 * m + 2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_pow, monicOrtho_degree]
    norm_num
    exact_mod_cast (show 2 * m < 2 * m + 2 by omega)
  have hquad := momentFunctional_eq_gaussSum_below h m hmN
    ((monicOrtho s m) ^ 2) hpdeg
  have hnorm : monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (show m < N by omega))
  have hsum :
      monicOrthoNormSq s m =
        ∑ x ∈ gaussNodes s m,
          christoffel s m x * (monicOrtho s m).eval x ^ 2 := by
    rw [pow_two] at hquad
    simpa only [monicOrthoNormSq, momentInner_def, Polynomial.eval_mul, pow_two] using hquad
  simp_rw [gaussTerminalSourceResistance]
  rw [← Finset.sum_div, ← hsum]
  exact div_self hnorm

/-- A terminal share is the preceding admission divided by the current root derivative. -/
theorem gaussTerminalSourceResistance_eq_prev_div_derivative {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    gaussTerminalSourceResistance s m x =
      (monicOrtho s m).eval x / (monicOrtho s (m + 1)).derivative.eval x := by
  have hcd := christoffel_mul_derivative_mul_prev_eq_normSq_below h hmN hroot
  have hnorm : monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (show m < N by omega))
  have hderiv : (monicOrtho s (m + 1)).derivative.eval x ≠ 0 := by
    intro hz
    rw [hz] at hcd
    norm_num at hcd
    exact hnorm hcd.symm
  apply (div_eq_div_iff hnorm hderiv).2
  calc
    christoffel s m x * (monicOrtho s m).eval x ^ 2 *
          (monicOrtho s (m + 1)).derivative.eval x =
        (monicOrtho s m).eval x *
          (christoffel s m x * (monicOrtho s (m + 1)).derivative.eval x *
            (monicOrtho s m).eval x) := by ring
    _ = (monicOrtho s m).eval x * monicOrthoNormSq s m := by rw [hcd]

/-- Every terminal share at a current Gauss root is strictly positive. -/
theorem gaussTerminalSourceResistance_pos {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    0 < gaussTerminalSourceResistance s m x := by
  have hcd := christoffel_mul_derivative_mul_prev_eq_normSq_below h hmN hroot
  have hnormpos : 0 < monicOrthoNormSq s m :=
    monicOrthoNorm_pos_below h (show m < N by omega)
  have hprev : (monicOrtho s m).eval x ≠ 0 := by
    intro hz
    rw [hz] at hcd
    linarith
  simp only [gaussTerminalSourceResistance]
  exact div_pos (mul_pos (christoffel_pos_below h m (by omega) x) (sq_pos_of_ne_zero hprev))
    hnormpos

/-- Adjacent-admission form of the same terminal share. -/
noncomputable def gaussAdjacentTerminalSourceResistance
    (s : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  christoffel s m x * (monicOrtho s (m + 2)).eval x ^ 2 /
    (monicOrthoBeta s (m + 1) * monicOrthoNormSq s (m + 1))

/-- At a current root, the adjacent admission is minus the current edge times the predecessor. -/
theorem monicOrtho_next_eval_root_eq_neg_beta_mul_prev {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 ≤ N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    (monicOrtho s (m + 2)).eval x =
      -monicOrthoBeta s (m + 1) * (monicOrtho s m).eval x := by
  have hrec := congrArg (Polynomial.eval x)
    (X_mul_monicOrtho_below h (n := m + 1) hmN)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul, hroot, mul_zero, add_zero] at hrec
  rw [show m + 1 + 1 = m + 2 by omega, Nat.add_sub_cancel] at hrec
  linarith

/-- The adjacent and preceding constructions give exactly the same share. -/
theorem gaussAdjacentTerminalSourceResistance_eq_terminal {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    gaussAdjacentTerminalSourceResistance s m x =
      gaussTerminalSourceResistance s m x := by
  have hnext := monicOrtho_next_eval_root_eq_neg_beta_mul_prev h (by omega) hroot
  have hbeta : monicOrthoBeta s (m + 1) ≠ 0 :=
    ne_of_gt (monicOrthoBeta_pos_below h (by omega) (by omega))
  have hnorm : monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (show m < N by omega))
  have hnormnext := monicOrthoNormSq_mul_nextBeta h (n := m) (by omega)
  simp only [gaussAdjacentTerminalSourceResistance, gaussTerminalSourceResistance]
  rw [hnext, ← hnormnext]
  field_simp [hbeta, hnorm]

/-- Adjacent-admission terminal shares also sum to one. -/
theorem sum_gaussAdjacentTerminalSourceResistance_eq_one {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) :
    ∑ x ∈ gaussNodes s m, gaussAdjacentTerminalSourceResistance s m x = 1 := by
  calc
    _ = ∑ x ∈ gaussNodes s m, gaussTerminalSourceResistance s m x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact gaussAdjacentTerminalSourceResistance_eq_terminal h hmN
        ((mem_gaussNodes_iff m x).mp hx)
    _ = 1 := sum_gaussTerminalSourceResistance_eq_one h (by omega)

/-- Current/adjacent ratio form of a terminal share. -/
theorem gaussTerminalSourceResistance_eq_neg_next_div_beta_mul_derivative {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    gaussTerminalSourceResistance s m x =
      -(monicOrtho s (m + 2)).eval x /
        (monicOrthoBeta s (m + 1) *
          (monicOrtho s (m + 1)).derivative.eval x) := by
  have hshare := gaussTerminalSourceResistance_eq_prev_div_derivative h (by omega) hroot
  have hnext := monicOrtho_next_eval_root_eq_neg_beta_mul_prev h (by omega) hroot
  have hbeta : monicOrthoBeta s (m + 1) ≠ 0 :=
    ne_of_gt (monicOrthoBeta_pos_below h (by omega) (by omega))
  rw [hshare, hnext]
  field_simp

/-! ## Sharp two-node nonuniformity boundary -/

/-- Left terminal share of a monic quadratic with an interlacing monic linear predecessor. -/
noncomputable def quadraticLeftTerminalSourceResistance
    (a b alpha : ℝ) : ℝ :=
  (X - C alpha).eval a / (((X - C a) * (X - C b)).derivative.eval a)

/-- Exact barycentric formula for the left quadratic terminal share. -/
theorem quadraticLeftTerminalSourceResistance_eq (a b alpha : ℝ) (hab : a ≠ b) :
    quadraticLeftTerminalSourceResistance a b alpha = (alpha - a) / (b - a) := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [quadraticLeftTerminalSourceResistance, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, one_mul, sub_zero]
  field_simp [hab', hba]
  ring

/-- **No uniform selected-share floor from interlacing.** Every open probability share occurs in
an ordered two-root interlacing configuration. -/
theorem quadraticLeftTerminalSourceResistance_affine_eq
    (a b theta : ℝ) (hab : a ≠ b) :
    quadraticLeftTerminalSourceResistance a b (a + theta * (b - a)) = theta := by
  rw [quadraticLeftTerminalSourceResistance_eq a b _ hab]
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

end HTGeometry
