import GaloisForLFunctions.RHTower.DeningerArithmeticPowerBar
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finsupp.Order
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Positive Gamma-rank regular coefficient for Deninger arithmetic cohomology

The Frobenius colimit replaces the one-sided power monoid by a group of rational powers.  On the
finite-support group algebra, domain translation is therefore invertible.  Its quaternionic double
has an explicit alternating cup form and a positive odd Hodge operator, both preserved by every
translation.

This is source-side algebra.  It uses no Xi zero, zero location, Weil positivity, or RH premise.
It does not identify the regular representation with arithmetic cohomology; that identification
still requires the Milnor--Witt incidence differential, harmonic reduction, and comparison with
the determinant/Lefschetz carrier.
-/

namespace RHTower

noncomputable section

/-- Algebraic finite-support core of the doubled Gamma-rank coefficient. -/
abbrev DeningerGammaRankCore (G : Type*) :=
  (G →₀ ℂ) × (G →₀ ℂ)

/-- Coefficientwise complex conjugation on a finite group-algebra packet. -/
def deningerGammaRankConjugation {G : Type*} :
    (G →₀ ℂ) ≃ₛₗ[starRingEnd ℂ] (G →₀ ℂ) :=
  Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ)

@[simp]
theorem deningerGammaRankConjugation_apply
    {G : Type*} (a : G →₀ ℂ) (q : G) :
    deningerGammaRankConjugation a q =
      (starRingEnd ℂ) (a q) :=
  rfl

/-- Reindex both summands by a bijection of the Frobenius-colimit group. -/
def deningerGammaRankShift {G : Type*}
    (e : G ≃ G) (x : DeningerGammaRankCore G) :
    DeningerGammaRankCore G :=
  (Finsupp.equivMapDomain e x.1,
    Finsupp.equivMapDomain e x.2)

/-- Left regular action of a group element on the algebraic Gamma-rank core. -/
def deningerGammaRankPowerShift {G : Type*} [Group G]
    (a : G) (x : DeningerGammaRankCore G) :
    DeningerGammaRankCore G :=
  deningerGammaRankShift (Equiv.mulLeft a) x

/-- Positive odd Hodge operator on the quaternionic double. -/
def deningerGammaRankHodge {G : Type*}
    (x : DeningerGammaRankCore G) :
    DeningerGammaRankCore G :=
  (-deningerGammaRankConjugation x.2,
    deningerGammaRankConjugation x.1)

/-- Coordinate contraction on finite group-algebra packets. -/
def deningerGammaRankDot {G : Type*}
    (a b : G →₀ ℂ) : ℂ :=
  a.sum fun q z => z * b q

/-- A coordinate packet contracts by coordinate evaluation. -/
@[simp]
private theorem deningerGammaRankDot_single_left
    {G : Type*} (q : G) (z : ℂ) (a : G →₀ ℂ) :
    deningerGammaRankDot (Finsupp.single q z) a = z * a q := by
  simp [deningerGammaRankDot]

/-- Coordinate contraction is additive in its left packet. -/
private theorem deningerGammaRankDot_add_left
    {G : Type*} (a b c : G →₀ ℂ) :
    deningerGammaRankDot (a + b) c =
      deningerGammaRankDot a c + deningerGammaRankDot b c := by
  unfold deningerGammaRankDot
  rw [Finsupp.sum_add_index'
    (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)]

/-- Coordinate contraction is additive in its right packet. -/
private theorem deningerGammaRankDot_add_right
    {G : Type*} (a b c : G →₀ ℂ) :
    deningerGammaRankDot a (b + c) =
      deningerGammaRankDot a b + deningerGammaRankDot a c := by
  unfold deningerGammaRankDot
  calc
    a.sum (fun q z => z * (b + c) q) =
        a.sum (fun q z => z * b q + z * c q) := by
      apply Finsupp.sum_congr
      intro q _hq
      simp [mul_add]
    _ = a.sum (fun q z => z * b q) +
        a.sum (fun q z => z * c q) := by
      simp [Finsupp.sum, Finset.sum_add_distrib]

/-- Contraction against a coordinate packet evaluates that coordinate. -/
private theorem deningerGammaRankDot_single_right
    {G : Type*} (q : G) (z : ℂ) (a : G →₀ ℂ) :
    deningerGammaRankDot a (Finsupp.single q z) = a q * z := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      simp [deningerGammaRankDot]
  | single_add p c a hp _hc ih =>
      by_cases hpq : p = q
      · subst p
        simp [deningerGammaRankDot_add_left,
          deningerGammaRankDot_single_left, ih, mul_comm]
        ring
      · simp [deningerGammaRankDot_add_left,
          deningerGammaRankDot_single_left, ih, hpq]

/-- Coordinate contraction is symmetric. -/
theorem deningerGammaRankDot_comm
    {G : Type*} (a b : G →₀ ℂ) :
    deningerGammaRankDot a b =
      deningerGammaRankDot b a := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      simp [deningerGammaRankDot]
  | single_add q z a hq _hz ih =>
      rw [deningerGammaRankDot_add_left,
        deningerGammaRankDot_add_right,
        deningerGammaRankDot_single_left,
        deningerGammaRankDot_single_right, ih, mul_comm]

/-- Complex-bilinear alternating cup form on the doubled algebraic core. -/
def deningerGammaRankCup {G : Type*}
    (x y : DeningerGammaRankCore G) : ℂ :=
  deningerGammaRankDot x.1 y.2 -
    deningerGammaRankDot x.2 y.1

/-- Positive coefficient energy on the doubled algebraic core. -/
def deningerGammaRankEnergy {G : Type*}
    (x : DeningerGammaRankCore G) : ℝ :=
  x.1.sum (fun _ z => Complex.normSq z) +
    x.2.sum (fun _ z => Complex.normSq z)

/-- The Gamma-rank Hodge operator is conjugate-linear. -/
theorem deningerGammaRankHodge_smul
    {G : Type*} (c : ℂ) (x : DeningerGammaRankCore G) :
    deningerGammaRankHodge (c • x) =
      (starRingEnd ℂ) c • deningerGammaRankHodge x := by
  ext q <;>
    simp [deningerGammaRankHodge,
      deningerGammaRankConjugation_apply, map_mul]

/-- The Gamma-rank Hodge operator is additive. -/
@[simp]
theorem deningerGammaRankHodge_add
    {G : Type*} (x y : DeningerGammaRankCore G) :
    deningerGammaRankHodge (x + y) =
      deningerGammaRankHodge x +
        deningerGammaRankHodge y := by
  ext q
  · simp [deningerGammaRankHodge,
      deningerGammaRankConjugation_apply]
    ring
  · simp [deningerGammaRankHodge,
      deningerGammaRankConjugation_apply]

/-- The Gamma-rank Hodge operator fixes the additive zero. -/
@[simp]
theorem deningerGammaRankHodge_zero
    {G : Type*} :
    deningerGammaRankHodge
        (0 : DeningerGammaRankCore G) = 0 := by
  ext q <;>
    simp [deningerGammaRankHodge]

/-- The Gamma-rank Hodge operator commutes with additive negation. -/
@[simp]
theorem deningerGammaRankHodge_neg
    {G : Type*} (x : DeningerGammaRankCore G) :
    deningerGammaRankHodge (-x) =
      -deningerGammaRankHodge x := by
  ext q <;>
    simp [deningerGammaRankHodge,
      deningerGammaRankConjugation_apply]

/-- The Gamma-rank Hodge operator commutes with subtraction. -/
@[simp]
theorem deningerGammaRankHodge_sub
    {G : Type*} (x y : DeningerGammaRankCore G) :
    deningerGammaRankHodge (x - y) =
      deningerGammaRankHodge x -
        deningerGammaRankHodge y := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    deningerGammaRankHodge_add,
    deningerGammaRankHodge_neg]

/-- The Gamma-rank Hodge operator is genuinely odd: `J² = -1`. -/
@[simp]
theorem deningerGammaRankHodge_sq
    {G : Type*} (x : DeningerGammaRankCore G) :
    deningerGammaRankHodge (deningerGammaRankHodge x) = -x := by
  ext q <;>
    simp [deningerGammaRankHodge,
      deningerGammaRankConjugation_apply]

/-- The doubled cup form vanishes on the diagonal. -/
@[simp]
theorem deningerGammaRankCup_self
    {G : Type*} (x : DeningerGammaRankCore G) :
    deningerGammaRankCup x x = 0 := by
  rw [deningerGammaRankCup,
    deningerGammaRankDot_comm x.2 x.1, sub_self]

/-- Contracting a packet with its conjugate gives its norm-square sum. -/
theorem deningerGammaRankDot_conjugation
    {G : Type*} (a : G →₀ ℂ) :
    deningerGammaRankDot a (deningerGammaRankConjugation a) =
      (a.sum (fun _ z => Complex.normSq z) : ℂ) := by
  unfold deningerGammaRankDot
  apply Finsupp.sum_congr
  intro q _hq
  rw [deningerGammaRankConjugation_apply, Complex.mul_conj]

/-- Cup followed by the odd Hodge operator is exactly the positive energy. -/
theorem deningerGammaRankCup_hodge
    {G : Type*} (x : DeningerGammaRankCore G) :
    deningerGammaRankCup x (deningerGammaRankHodge x) =
      (deningerGammaRankEnergy x : ℂ) := by
  have hnegative :
      deningerGammaRankDot x.2
          (-deningerGammaRankConjugation x.2) =
        -(x.2.sum (fun _ z => Complex.normSq z) : ℂ) := by
    unfold deningerGammaRankDot
    calc
      x.2.sum (fun q z =>
          z * (-deningerGammaRankConjugation x.2) q) =
          x.2.sum (fun _ z => -(Complex.normSq z : ℂ)) := by
        apply Finsupp.sum_congr
        intro q _hq
        rw [Finsupp.neg_apply,
          deningerGammaRankConjugation_apply,
          mul_neg, Complex.mul_conj]
      _ = -(x.2.sum
          (fun _ z => Complex.normSq z) : ℂ) := by
        simp [Finsupp.sum]
  have hcast (a : G →₀ ℂ) :
      a.sum (fun _ z =>
          Complex.ofReal (Complex.normSq z)) =
        Complex.ofReal
          (a.sum (fun _ z => Complex.normSq z)) := by
    unfold Finsupp.sum
    exact (Complex.ofReal_sum a.support
      (fun q => Complex.normSq (a q))).symm
  rw [deningerGammaRankCup, deningerGammaRankHodge]
  change
    deningerGammaRankDot x.1 (deningerGammaRankConjugation x.1) -
        deningerGammaRankDot x.2
          (-deningerGammaRankConjugation x.2) =
      (deningerGammaRankEnergy x : ℂ)
  rw [deningerGammaRankDot_conjugation, hnegative]
  rw [deningerGammaRankEnergy, Complex.ofReal_add,
    sub_neg_eq_add]
  exact congrArg₂ (· + ·)
    (hcast x.1) (hcast x.2)

/-- A nonzero finite packet has strictly positive coefficient energy. -/
private theorem deningerGammaRankPacketEnergy_pos
    {G : Type*} {a : G →₀ ℂ} (ha : a ≠ 0) :
    0 < a.sum (fun _ z => Complex.normSq z) := by
  apply Finsupp.sum_pos
  · intro q hq
    exact Complex.normSq_pos.mpr (Finsupp.mem_support_iff.mp hq)
  · exact ha

/-- Every finite packet has nonnegative coefficient energy. -/
private theorem deningerGammaRankPacketEnergy_nonneg
    {G : Type*} (a : G →₀ ℂ) :
    0 ≤ a.sum (fun _ z => Complex.normSq z) :=
  Finsupp.sum_nonneg' fun _ => Complex.normSq_nonneg _

/-- The cup--Hodge metric is positive definite on the algebraic core. -/
theorem deningerGammaRankEnergy_pos
    {G : Type*} {x : DeningerGammaRankCore G} (hx : x ≠ 0) :
    0 < deningerGammaRankEnergy x := by
  by_cases hfirst : x.1 = 0
  · have hsecond : x.2 ≠ 0 := by
      intro h
      apply hx
      exact Prod.ext hfirst h
    exact add_pos_of_nonneg_of_pos
      (deningerGammaRankPacketEnergy_nonneg x.1)
      (deningerGammaRankPacketEnergy_pos hsecond)
  · exact add_pos_of_pos_of_nonneg
      (deningerGammaRankPacketEnergy_pos hfirst)
      (deningerGammaRankPacketEnergy_nonneg x.2)

/-- Real diagonal of the positive cup--Hodge metric. -/
theorem deningerGammaRankCup_hodge_re
    {G : Type*} (x : DeningerGammaRankCore G) :
    (deningerGammaRankCup x (deningerGammaRankHodge x)).re =
      deningerGammaRankEnergy x := by
  rw [deningerGammaRankCup_hodge]
  simp

/-- The source cup--Hodge form is strictly positive away from zero. -/
theorem deningerGammaRankCup_hodge_pos
    {G : Type*} {x : DeningerGammaRankCore G} (hx : x ≠ 0) :
    0 < (deningerGammaRankCup x
      (deningerGammaRankHodge x)).re := by
  rw [deningerGammaRankCup_hodge_re]
  exact deningerGammaRankEnergy_pos hx

/-- Simultaneous reindexing preserves coordinate contraction. -/
theorem deningerGammaRankDot_shift
    {G : Type*} (e : G ≃ G) (a b : G →₀ ℂ) :
    deningerGammaRankDot (Finsupp.equivMapDomain e a)
        (Finsupp.equivMapDomain e b) =
      deningerGammaRankDot a b := by
  unfold deningerGammaRankDot
  rw [Finsupp.sum_equivMapDomain]
  simp [Finsupp.equivMapDomain_apply]

/-- Every regular translation preserves the alternating cup form. -/
theorem deningerGammaRankCup_shift
    {G : Type*} (e : G ≃ G)
    (x y : DeningerGammaRankCore G) :
    deningerGammaRankCup
        (deningerGammaRankShift e x)
        (deningerGammaRankShift e y) =
      deningerGammaRankCup x y := by
  simp [deningerGammaRankCup, deningerGammaRankShift,
    deningerGammaRankDot_shift]

/-- Every regular translation preserves positive coefficient energy. -/
theorem deningerGammaRankEnergy_shift
    {G : Type*} (e : G ≃ G) (x : DeningerGammaRankCore G) :
    deningerGammaRankEnergy (deningerGammaRankShift e x) =
      deningerGammaRankEnergy x := by
  unfold deningerGammaRankEnergy deningerGammaRankShift
  rw [Finsupp.sum_equivMapDomain,
    Finsupp.sum_equivMapDomain]

/-- Every regular translation commutes with the positive odd Hodge operator. -/
theorem deningerGammaRankShift_hodge
    {G : Type*} (e : G ≃ G) (x : DeningerGammaRankCore G) :
    deningerGammaRankShift e (deningerGammaRankHodge x) =
      deningerGammaRankHodge (deningerGammaRankShift e x) := by
  ext q <;>
    simp [deningerGammaRankShift, deningerGammaRankHodge,
      Finsupp.equivMapDomain_apply,
      deningerGammaRankConjugation_apply]

/-- Reindexing by the inverse equivalence is a two-sided inverse translation. -/
@[simp]
theorem deningerGammaRankShift_symm
    {G : Type*} (e : G ≃ G) (x : DeningerGammaRankCore G) :
    deningerGammaRankShift e.symm
        (deningerGammaRankShift e x) = x := by
  ext q <;>
    simp [deningerGammaRankShift,
      Finsupp.equivMapDomain_apply]

/-- Regular translation preserves the additive zero. -/
@[simp]
theorem deningerGammaRankPowerShift_zero
    {G : Type*} [Group G] (a : G) :
    deningerGammaRankPowerShift a
        (0 : DeningerGammaRankCore G) = 0 := by
  ext q <;>
    simp [deningerGammaRankPowerShift,
      deningerGammaRankShift]

/-- Regular translation is additive. -/
@[simp]
theorem deningerGammaRankPowerShift_add
    {G : Type*} [Group G] (a : G)
    (x y : DeningerGammaRankCore G) :
    deningerGammaRankPowerShift a (x + y) =
      deningerGammaRankPowerShift a x +
        deningerGammaRankPowerShift a y := by
  ext q <;>
    simp [deningerGammaRankPowerShift,
      deningerGammaRankShift,
      Finsupp.equivMapDomain_apply]

/-- The left regular shifts satisfy the group law. -/
theorem deningerGammaRankPowerShift_mul
    {G : Type*} [Group G] (a b : G)
    (x : DeningerGammaRankCore G) :
    deningerGammaRankPowerShift a
        (deningerGammaRankPowerShift b x) =
      deningerGammaRankPowerShift (a * b : G) x := by
  have hequiv :
      (Equiv.mulLeft b).trans (Equiv.mulLeft a) =
        Equiv.mulLeft (a * b : G) := by
    ext q
    simp
  apply Prod.ext
  · change
      Finsupp.equivMapDomain (Equiv.mulLeft a)
          (Finsupp.equivMapDomain (Equiv.mulLeft b) x.1) =
        Finsupp.equivMapDomain (Equiv.mulLeft (a * b)) x.1
    rw [← Finsupp.equivMapDomain_trans, hequiv]
  · change
      Finsupp.equivMapDomain (Equiv.mulLeft a)
          (Finsupp.equivMapDomain (Equiv.mulLeft b) x.2) =
        Finsupp.equivMapDomain (Equiv.mulLeft (a * b)) x.2
    rw [← Finsupp.equivMapDomain_trans, hequiv]

/-- The identity rational power acts trivially. -/
@[simp]
theorem deningerGammaRankPowerShift_one
    {G : Type*} [Group G]
    (x : DeningerGammaRankCore G) :
    deningerGammaRankPowerShift (1 : G) x = x := by
  have hequiv :
      Equiv.mulLeft (1 : G) = Equiv.refl G := by
    ext q
    simp
  rw [deningerGammaRankPowerShift, hequiv]
  ext q <;>
    simp [deningerGammaRankShift]

/-- Centered rational-power translations commute with the positive odd Hodge operator. -/
@[simp]
theorem deningerGammaRankHodge_powerShift
    {G : Type*} [Group G] (a : G)
    (x : DeningerGammaRankCore G) :
    deningerGammaRankHodge
        (deningerGammaRankPowerShift a x) =
      deningerGammaRankPowerShift a
        (deningerGammaRankHodge x) :=
  (deningerGammaRankShift_hodge
    (Equiv.mulLeft a) x).symm

/-- The left regular representation supplies the coefficient action for the power-bar complex. -/
instance deningerGammaRankDistribMulAction
    {G : Type*} [Group G] :
    DistribMulAction G (DeningerGammaRankCore G) where
  smul := deningerGammaRankPowerShift
  one_smul := deningerGammaRankPowerShift_one
  mul_smul a b x :=
    (deningerGammaRankPowerShift_mul a b x).symm
  smul_zero := deningerGammaRankPowerShift_zero
  smul_add := deningerGammaRankPowerShift_add

@[simp]
theorem deningerGammaRank_smul_def
    {G : Type*} [Group G] (a : G)
    (x : DeningerGammaRankCore G) :
    a • x = deningerGammaRankPowerShift a x :=
  rfl

/-- Pointwise odd Hodge operator on degree-one bar cochains. -/
def deningerGammaRankBarHodge1
    {G : Type*} (φ : G → DeningerGammaRankCore G) :
    G → DeningerGammaRankCore G :=
  fun n => deningerGammaRankHodge (φ n)

/-- Pointwise odd Hodge operator on degree-two bar cochains. -/
def deningerGammaRankBarHodge2
    {G : Type*}
    (ψ : G → G → DeningerGammaRankCore G) :
    G → G → DeningerGammaRankCore G :=
  fun m n => deningerGammaRankHodge (ψ m n)

/-- Pointwise odd Hodge operator on degree-three bar cochains. -/
def deningerGammaRankBarHodge3
    {G : Type*}
    (χ : G → G → G → DeningerGammaRankCore G) :
    G → G → G → DeningerGammaRankCore G :=
  fun l m n => deningerGammaRankHodge (χ l m n)

/-- Hodge commutes with the first arithmetic incidence coboundary. -/
theorem deningerGammaRankBarHodge_D0
    {G : Type*} [Group G]
    (v : DeningerGammaRankCore G) :
    deningerGammaRankBarHodge1
        (deningerPowerBarD0 (M := G) v) =
      deningerPowerBarD0 (M := G)
        (deningerGammaRankHodge v) := by
  funext n
  simp [deningerGammaRankBarHodge1,
    deningerPowerBarD0, deningerGammaRank_smul_def,
    deningerGammaRankHodge_sub,
    deningerGammaRankHodge_powerShift]

/-- Hodge commutes with the second arithmetic incidence coboundary. -/
theorem deningerGammaRankBarHodge_D1
    {G : Type*} [Group G]
    (φ : G → DeningerGammaRankCore G) :
    deningerGammaRankBarHodge2
        (deningerPowerBarD1 (M := G) φ) =
      deningerPowerBarD1 (M := G)
        (deningerGammaRankBarHodge1 φ) := by
  funext m n
  simp [deningerGammaRankBarHodge1,
    deningerGammaRankBarHodge2,
    deningerPowerBarD1,
    deningerGammaRank_smul_def,
    deningerGammaRankHodge_sub,
    deningerGammaRankHodge_add,
    deningerGammaRankHodge_powerShift]

/-- Hodge commutes with the third arithmetic incidence coboundary. -/
theorem deningerGammaRankBarHodge_D2
    {G : Type*} [Group G]
    (ψ : G → G → DeningerGammaRankCore G) :
    deningerGammaRankBarHodge3
        (deningerPowerBarD2 (M := G) ψ) =
      deningerPowerBarD2 (M := G)
        (deningerGammaRankBarHodge2 ψ) := by
  funext l m n
  simp [deningerGammaRankBarHodge2,
    deningerGammaRankBarHodge3,
    deningerPowerBarD2,
    deningerGammaRank_smul_def,
    deningerGammaRankHodge_sub,
    deningerGammaRankHodge_add,
    deningerGammaRankHodge_powerShift]

/-- The good degree-two cocycle kernel is stable under source Hodge. -/
def deningerGammaRankBarHodgeCocycle2
    {G : Type*} [Group G]
    (ψ : DeningerPowerBarCocycle2
      (M := G) (V := DeningerGammaRankCore G)) :
    DeningerPowerBarCocycle2
      (M := G) (V := DeningerGammaRankCore G) where
  val := deningerGammaRankBarHodge2 ψ.1
  property := by
    rw [← deningerGammaRankBarHodge_D2]
    funext l m n
    have hzero :
        deningerPowerBarD2 (M := G) ψ.1 l m n = 0 := by
      rw [ψ.2]
      rfl
    simp [deningerGammaRankBarHodge3, hzero]

/-! ## Hilbert completion -/

/-- Hilbert completion of the doubled Gamma-rank coefficient. -/
abbrev DeningerGammaRankHilbert (G : Type*) :=
  lp (fun _ : G ⊕ G => ℂ) 2

/-- Canonical linear inclusion of the algebraic Gamma-rank core into its Hilbert completion. -/
def deningerGammaRankCoreToHilbert
    {G : Type*} :
    DeningerGammaRankCore G →ₗ[ℂ]
      DeningerGammaRankHilbert G where
  toFun x :=
    let f : G ⊕ G →₀ ℂ := x.1.sumElim x.2
    ⟨(f : G ⊕ G → ℂ), HilbertSchmidt.memℓp_of_sq
      (summable_of_hasFiniteSupport
        ((Finsupp.hasFiniteSupport f).subset
          (by
            intro s hs hzero
            apply hs
            simp [hzero])))⟩
  map_add' x y := by
    ext s
    cases s with
    | inl q =>
        change x.1 q + y.1 q = x.1 q + y.1 q
        rfl
    | inr q =>
        change x.2 q + y.2 q = x.2 q + y.2 q
        rfl
  map_smul' c x := by
    ext s
    cases s with
    | inl q =>
        change c * x.1 q = c * x.1 q
        rfl
    | inr q =>
        change c * x.2 q = c * x.2 q
        rfl

@[simp]
theorem deningerGammaRankCoreToHilbert_inl
    {G : Type*} (x : DeningerGammaRankCore G) (q : G) :
    deningerGammaRankCoreToHilbert x (Sum.inl q) = x.1 q :=
  by
    simp [deningerGammaRankCoreToHilbert]

@[simp]
theorem deningerGammaRankCoreToHilbert_inr
    {G : Type*} (x : DeningerGammaRankCore G) (q : G) :
    deningerGammaRankCoreToHilbert x (Sum.inr q) = x.2 q :=
  by
    simp [deningerGammaRankCoreToHilbert]

/-- The algebraic core embeds faithfully into the Hilbert completion. -/
theorem deningerGammaRankCoreToHilbert_injective
    {G : Type*} :
    Function.Injective
      (deningerGammaRankCoreToHilbert
        (G := G)) := by
  intro x y hxy
  apply Prod.ext
  · ext q
    have h := congrArg
      (fun z : DeningerGammaRankHilbert G =>
        z (Sum.inl q)) hxy
    simpa using h
  · ext q
    have h := congrArg
      (fun z : DeningerGammaRankHilbert G =>
        z (Sum.inr q)) hxy
    simpa using h

/-- The quaternionic odd Hodge operator on the completed coefficient. -/
def deningerGammaRankHilbertHodge
    {G : Type*} (x : DeningerGammaRankHilbert G) :
    DeningerGammaRankHilbert G :=
  ⟨fun s =>
      match s with
      | Sum.inl q => -(starRingEnd ℂ) (x (Sum.inr q))
      | Sum.inr q => (starRingEnd ℂ) (x (Sum.inl q)),
    HilbertSchmidt.memℓp_of_sq
      (((Equiv.sumComm G G).summable_iff.mpr
        (HilbertSchmidt.summable_coe_sq x)).congr fun s => by
          cases s <;> simp)⟩

@[simp]
theorem deningerGammaRankHilbertHodge_inl
    {G : Type*} (x : DeningerGammaRankHilbert G) (q : G) :
    deningerGammaRankHilbertHodge x (Sum.inl q) =
      -(starRingEnd ℂ) (x (Sum.inr q)) :=
  rfl

@[simp]
theorem deningerGammaRankHilbertHodge_inr
    {G : Type*} (x : DeningerGammaRankHilbert G) (q : G) :
    deningerGammaRankHilbertHodge x (Sum.inr q) =
      (starRingEnd ℂ) (x (Sum.inl q)) :=
  rfl

/-- Completed Gamma-rank Hodge as a conjugate-linear map. -/
def deningerGammaRankHilbertHodgeSigma
    {G : Type*} :
    DeningerGammaRankHilbert G →ₛₗ[starRingEnd ℂ]
      DeningerGammaRankHilbert G where
  toFun := deningerGammaRankHilbertHodge
  map_add' x y := by
    ext s
    cases s with
    | inl q =>
        change
          -(starRingEnd ℂ) (x (Sum.inr q) + y (Sum.inr q)) =
            -(starRingEnd ℂ) (x (Sum.inr q)) +
              -(starRingEnd ℂ) (y (Sum.inr q))
        rw [map_add]
        ring
    | inr q =>
        change
          (starRingEnd ℂ) (x (Sum.inl q) + y (Sum.inl q)) =
            (starRingEnd ℂ) (x (Sum.inl q)) +
              (starRingEnd ℂ) (y (Sum.inl q))
        rw [map_add]
  map_smul' c x := by
    ext s
    cases s <;>
      simp [deningerGammaRankHilbertHodge, map_mul]

/-- The completed Gamma-rank Hodge operator squares to `-1`. -/
@[simp]
theorem deningerGammaRankHilbertHodge_sq
    {G : Type*} (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertHodge
        (deningerGammaRankHilbertHodge x) = -x := by
  ext s
  cases s with
  | inl q =>
      change
        -(starRingEnd ℂ)
            ((starRingEnd ℂ) (x (Sum.inl q))) =
          -x (Sum.inl q)
      simp
  | inr q =>
      change
        (starRingEnd ℂ)
            (-(starRingEnd ℂ) (x (Sum.inr q))) =
          -x (Sum.inr q)
      simp

/-- Algebraic and completed odd Hodge operators agree on the finite-support core. -/
theorem deningerGammaRankCoreToHilbert_hodge
    {G : Type*} (x : DeningerGammaRankCore G) :
    deningerGammaRankCoreToHilbert
        (deningerGammaRankHodge x) =
      deningerGammaRankHilbertHodge
        (deningerGammaRankCoreToHilbert x) := by
  ext s
  cases s <;>
    simp [deningerGammaRankHodge]

/-- The completed Gamma-rank Hodge operator is antiunitary. -/
theorem inner_deningerGammaRankHilbertHodge
    {G : Type*} (x y : DeningerGammaRankHilbert G) :
    inner ℂ (deningerGammaRankHilbertHodge x)
        (deningerGammaRankHilbertHodge y) =
      inner ℂ y x := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    (∑' s : G ⊕ G,
        inner ℂ (deningerGammaRankHilbertHodge x s)
          (deningerGammaRankHilbertHodge y s)) =
        ∑' s : G ⊕ G,
          inner ℂ (y ((Equiv.sumComm G G) s))
            (x ((Equiv.sumComm G G) s)) := by
      apply tsum_congr
      intro s
      cases s <;>
        simp [RCLike.inner_apply, map_neg] <;>
        ring
    _ = ∑' s : G ⊕ G, inner ℂ (y s) (x s) :=
      (Equiv.sumComm G G).tsum_eq
        (fun s => inner ℂ (y s) (x s))

/-- The completed odd Hodge operator preserves the Hilbert norm. -/
theorem norm_deningerGammaRankHilbertHodge
    {G : Type*} (x : DeningerGammaRankHilbert G) :
    ‖deningerGammaRankHilbertHodge x‖ = ‖x‖ := by
  have hsq :
      ‖deningerGammaRankHilbertHodge x‖ ^ 2 =
        ‖x‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq,
      HilbertSchmidt.lp_norm_sq_eq]
    calc
      (∑' s : G ⊕ G,
          ‖deningerGammaRankHilbertHodge x s‖ ^ 2) =
          ∑' s : G ⊕ G,
            ‖x ((Equiv.sumComm G G) s)‖ ^ 2 := by
        apply tsum_congr
        intro s
        cases s <;> simp
      _ = ∑' s : G ⊕ G, ‖x s‖ ^ 2 :=
        (Equiv.sumComm G G).tsum_eq
          (fun s => ‖x s‖ ^ 2)
  nlinarith [norm_nonneg
    (deningerGammaRankHilbertHodge x), norm_nonneg x]

/-- Completed alternating cup form, defined from source Hodge and Hilbert metric. -/
def deningerGammaRankHilbertCup
    {G : Type*} :
    LinearMap.BilinForm ℂ (DeningerGammaRankHilbert G) :=
  LinearMap.mk₂ ℂ
    (fun x y =>
      inner ℂ (deningerGammaRankHilbertHodge x) y)
    (by
      intro x x' y
      change
        inner ℂ (deningerGammaRankHilbertHodge (x + x')) y =
          inner ℂ (deningerGammaRankHilbertHodge x) y +
            inner ℂ (deningerGammaRankHilbertHodge x') y
      have hJ :=
        deningerGammaRankHilbertHodgeSigma.map_add x x'
      change
        deningerGammaRankHilbertHodge (x + x') =
          deningerGammaRankHilbertHodge x +
            deningerGammaRankHilbertHodge x' at hJ
      rw [hJ, inner_add_left])
    (by
      intro c x y
      change
        inner ℂ (deningerGammaRankHilbertHodge (c • x)) y =
          c • inner ℂ (deningerGammaRankHilbertHodge x) y
      have hJ :=
        map_smulₛₗ deningerGammaRankHilbertHodgeSigma c x
      change
        deningerGammaRankHilbertHodge (c • x) =
          (starRingEnd ℂ) c •
            deningerGammaRankHilbertHodge x at hJ
      rw [hJ, inner_smul_left]
      simp)
    (by
      intro x y y'
      change
        inner ℂ (deningerGammaRankHilbertHodge x) (y + y') =
          inner ℂ (deningerGammaRankHilbertHodge x) y +
            inner ℂ (deningerGammaRankHilbertHodge x) y'
      rw [inner_add_right])
    (by
      intro c x y
      change
        inner ℂ (deningerGammaRankHilbertHodge x) (c • y) =
          c • inner ℂ (deningerGammaRankHilbertHodge x) y
      rw [inner_smul_right]
      simp [smul_eq_mul])

@[simp]
theorem deningerGammaRankHilbertCup_apply
    {G : Type*} (x y : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertCup x y =
      inner ℂ (deningerGammaRankHilbertHodge x) y :=
  rfl

/-- Cup followed by completed Hodge is the Hilbert norm-square form. -/
theorem deningerGammaRankHilbertCup_hodge
    {G : Type*} (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertCup x
        (deningerGammaRankHilbertHodge x) =
      inner ℂ (deningerGammaRankHilbertHodge x)
        (deningerGammaRankHilbertHodge x) :=
  rfl

/-- The completed Gamma-rank cup form is alternating. -/
theorem deningerGammaRankHilbertCup_isAlt
    {G : Type*} :
    (deningerGammaRankHilbertCup
      (G := G)).IsAlt := by
  intro x
  have hanti :=
    inner_deningerGammaRankHilbertHodge x
      (deningerGammaRankHilbertHodge x)
  rw [deningerGammaRankHilbertHodge_sq,
    inner_neg_right] at hanti
  rw [deningerGammaRankHilbertCup_apply]
  linear_combination (-1 / 2 : ℂ) * hanti

/-- The completed source cup--Hodge metric is strictly positive away from zero. -/
theorem deningerGammaRankHilbertHodge_positive
    {G : Type*} {x : DeningerGammaRankHilbert G}
    (hx : x ≠ 0) :
    0 < (deningerGammaRankHilbertCup x
      (deningerGammaRankHilbertHodge x)).re := by
  rw [deningerGammaRankHilbertCup_hodge]
  have hnorm :
      (inner ℂ (deningerGammaRankHilbertHodge x)
        (deningerGammaRankHilbertHodge x)).re =
        ‖deningerGammaRankHilbertHodge x‖ ^ 2 := by
    simpa using
      (InnerProductSpace.norm_sq_eq_re_inner
        (𝕜 := ℂ)
        (deningerGammaRankHilbertHodge x)).symm
  rw [hnorm, norm_deningerGammaRankHilbertHodge]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)

/-- Block-diagonal reindexing of the Hilbert coefficient by an index equivalence. -/
def deningerGammaRankHilbertShift
    {G : Type*} (e : (G ⊕ G) ≃ (G ⊕ G))
    (x : DeningerGammaRankHilbert G) :
    DeningerGammaRankHilbert G :=
  ⟨fun s => x (e.symm s),
    HilbertSchmidt.memℓp_of_sq
      ((e.symm.summable_iff.mpr
        (HilbertSchmidt.summable_coe_sq x)).congr
          fun _ => rfl)⟩

/-- Simultaneous left multiplication on both copies of the Gamma-rank index. -/
def deningerGammaRankHilbertPowerEquiv
    {G : Type*} [Group G] (a : G) :
    (G ⊕ G) ≃ (G ⊕ G) :=
  Equiv.sumCongr (Equiv.mulLeft a) (Equiv.mulLeft a)

/-- Centered rational-power action on the completed Gamma-rank coefficient. -/
def deningerGammaRankHilbertPowerShift
    {G : Type*} [Group G] (a : G)
    (x : DeningerGammaRankHilbert G) :
    DeningerGammaRankHilbert G :=
  deningerGammaRankHilbertShift
    (deningerGammaRankHilbertPowerEquiv a) x

/-- Every completed regular translation preserves the Hilbert inner product. -/
theorem inner_deningerGammaRankHilbertShift
    {G : Type*} (e : (G ⊕ G) ≃ (G ⊕ G))
    (x y : DeningerGammaRankHilbert G) :
    inner ℂ (deningerGammaRankHilbertShift e x)
        (deningerGammaRankHilbertShift e y) =
      inner ℂ x y := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact e.symm.tsum_eq
    (fun s => inner ℂ (x s) (y s))

/-- Every completed regular translation is norm preserving. -/
theorem norm_deningerGammaRankHilbertShift
    {G : Type*} (e : (G ⊕ G) ≃ (G ⊕ G))
    (x : DeningerGammaRankHilbert G) :
    ‖deningerGammaRankHilbertShift e x‖ = ‖x‖ := by
  have hsq :
      ‖deningerGammaRankHilbertShift e x‖ ^ 2 =
        ‖x‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq,
      HilbertSchmidt.lp_norm_sq_eq]
    exact e.symm.tsum_eq (fun s => ‖x s‖ ^ 2)
  nlinarith [norm_nonneg
    (deningerGammaRankHilbertShift e x), norm_nonneg x]

/-- Completed rational-power action commutes with source Hodge. -/
theorem deningerGammaRankHilbertPowerShift_hodge
    {G : Type*} [Group G] (a : G)
    (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertPowerShift a
        (deningerGammaRankHilbertHodge x) =
      deningerGammaRankHilbertHodge
        (deningerGammaRankHilbertPowerShift a x) := by
  ext s
  cases s <;>
    simp [deningerGammaRankHilbertPowerShift,
      deningerGammaRankHilbertShift,
      deningerGammaRankHilbertPowerEquiv]

/-- Algebraic and completed rational-power actions agree on the dense core. -/
theorem deningerGammaRankCoreToHilbert_powerShift
    {G : Type*} [Group G] (a : G)
    (x : DeningerGammaRankCore G) :
    deningerGammaRankCoreToHilbert
        (deningerGammaRankPowerShift a x) =
      deningerGammaRankHilbertPowerShift a
        (deningerGammaRankCoreToHilbert x) := by
  ext s
  cases s <;>
    simp [deningerGammaRankPowerShift,
      deningerGammaRankShift,
      deningerGammaRankHilbertPowerShift,
      deningerGammaRankHilbertShift,
      deningerGammaRankHilbertPowerEquiv,
      Finsupp.equivMapDomain_apply]

/-- The algebraic Gamma-rank core has dense image in the completed coefficient Hilbert space. -/
theorem deningerGammaRankCoreToHilbert_denseRange
    {G : Type*} :
    DenseRange
      (deningerGammaRankCoreToHilbert
        (G := G)) := by
  classical
  rw [denseRange_iff_closure_range,
    ← LinearMap.coe_range,
    ← Submodule.topologicalClosure_coe]
  apply Set.eq_univ_of_forall
  intro x
  change x ∈
    (LinearMap.range
      (deningerGammaRankCoreToHilbert
        (G := G))).topologicalClosure
  have hsum :
      HasSum
        (fun s : G ⊕ G =>
          lp.single 2 s (x s))
        x :=
    lp.hasSum_single ENNReal.ofNat_ne_top x
  rw [← hsum.tsum_eq]
  apply tsum_mem
    (Submodule.isClosed_topologicalClosure
      (LinearMap.range
        (deningerGammaRankCoreToHilbert
          (G := G))))
  intro s
  apply Submodule.le_topologicalClosure
  cases s with
  | inl q =>
      refine ⟨(Finsupp.single q (x (Sum.inl q)), 0), ?_⟩
      ext t
      cases t with
      | inl r =>
          by_cases h : r = q
          · subst r
            simp [deningerGammaRankCoreToHilbert]
          · simp [deningerGammaRankCoreToHilbert, h]
      | inr r =>
          simp [deningerGammaRankCoreToHilbert]
  | inr q =>
      refine ⟨(0, Finsupp.single q (x (Sum.inr q))), ?_⟩
      ext t
      cases t with
      | inl r =>
          simp [deningerGammaRankCoreToHilbert]
      | inr r =>
          by_cases h : r = q
          · subst r
            simp [deningerGammaRankCoreToHilbert]
          · simp [deningerGammaRankCoreToHilbert, h]

/-- Centered rational-power action preserves completed cup. -/
theorem deningerGammaRankHilbertCup_powerShift
    {G : Type*} [Group G] (a : G)
    (x y : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertCup
        (deningerGammaRankHilbertPowerShift a x)
        (deningerGammaRankHilbertPowerShift a y) =
      deningerGammaRankHilbertCup x y := by
  change
    inner ℂ
        (deningerGammaRankHilbertHodge
          (deningerGammaRankHilbertPowerShift a x))
        (deningerGammaRankHilbertPowerShift a y) =
      inner ℂ (deningerGammaRankHilbertHodge x) y
  rw [← deningerGammaRankHilbertPowerShift_hodge]
  exact inner_deningerGammaRankHilbertShift
    (deningerGammaRankHilbertPowerEquiv a)
    (deningerGammaRankHilbertHodge x) y

/-- The inverse rational-power shift is the inverse regular translation. -/
@[simp]
theorem deningerGammaRankPowerShift_inv
    {G : Type*} [Group G] (a : G)
    (x : DeningerGammaRankCore G) :
    deningerGammaRankPowerShift a⁻¹
        (deningerGammaRankPowerShift a x) = x := by
  rw [deningerGammaRankPowerShift_mul,
    inv_mul_cancel, deningerGammaRankPowerShift_one]

end

end RHTower
