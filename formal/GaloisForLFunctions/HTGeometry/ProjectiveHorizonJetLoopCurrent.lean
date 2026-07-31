import GaloisForLFunctions.HTGeometry.ProjectiveHorizonObserverLieAlgebra
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAffineChartField

/-!
# The loop currents of the observer group on the jet field

An observer whose parameter is allowed to depend polynomially on the source parameter acts on jets
by a shift of jet order weighted by a falling factorial: the depth-`k` current attached to a matrix
of constants sends the jet of order `l` to the jet of order `l-k`, with the coefficient
`l(l-1)...(l-k+1)`.

Depth zero is the infinitesimal observer itself.  The total-derivative jet shift lowers the depth:
its bracket with the depth-`k` current is `-k` times the depth-`(k-1)` current, so the currents form
a graded family which the shift descends.  This is the representation of the polynomial current
algebra on the jet field that a higher-depth horizon needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-! ## A falling-factorial identity -/

theorem succ_descFactorial_succ_eq (l j : ℕ) :
    (l + 1).descFactorial (j + 1) = l.descFactorial (j + 1) + (j + 1) * l.descFactorial j := by
  rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
  rcases le_or_gt j l with h | h
  · rw [← Nat.add_mul]
    congr 1
    omega
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]
    simp

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The loop currents -/

/-- The depth-`k` polynomial loop current attached to a matrix of constants. -/
def jetLoopDerivationPoly (k : ℕ) (M : Matrix n n K) :
    Derivation K (MvPolynomial (n × ℕ) K) (MvPolynomial (n × ℕ) K) :=
  MvPolynomial.mkDerivation K fun p : n × ℕ =>
    ∑ m, MvPolynomial.C ((p.2.descFactorial k : K) * M p.1 m) *
      MvPolynomial.X ((m, p.2 - k) : n × ℕ)

omit [DecidableEq n] in
@[simp]
theorem jetLoopDerivationPoly_X (k : ℕ) (M : Matrix n n K) (a : n) (l : ℕ) :
    jetLoopDerivationPoly k M (MvPolynomial.X ((a, l) : n × ℕ)) =
      ∑ m, MvPolynomial.C ((l.descFactorial k : K) * M a m) *
        MvPolynomial.X ((m, l - k) : n × ℕ) :=
  MvPolynomial.mkDerivation_X _ _ _

omit [DecidableEq n] in
/-- Depth zero is the infinitesimal observer. -/
theorem jetLoopDerivationPoly_zero (M : Matrix n n K) :
    jetLoopDerivationPoly 0 M = jetDerivationPoly M := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, l⟩
  rw [jetLoopDerivationPoly_X, jetDerivationPoly_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero]

/-- The depth-`k` loop current on the jet field. -/
def jetLoopDerivation (k : ℕ) (M : Matrix n n K) :
    Derivation K (HomogeneousJetField n K) (HomogeneousJetField n K) :=
  extendFreeCoordinatePolynomialDerivation (jetLoopDerivationPoly k M)

omit [DecidableEq n] in
@[simp]
theorem jetLoopDerivation_algebraMap (k : ℕ) (M : Matrix n n K) (p : MvPolynomial (n × ℕ) K) :
    jetLoopDerivation k M (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
        (jetLoopDerivationPoly k M p) :=
  extendFreeCoordinatePolynomialDerivation_algebraMap _ _

omit [DecidableEq n] in
theorem jetLoopDerivation_zero (M : Matrix n n K) :
    jetLoopDerivation 0 M = jetDerivation M := by
  rw [jetLoopDerivation, jetLoopDerivationPoly_zero]
  rfl

omit [DecidableEq n] in
theorem jetLoopDerivation_freeCoordinate (k : ℕ) (M : Matrix n n K) (a : n) (l : ℕ) :
    jetLoopDerivation k M (freeCoordinate K (n × ℕ) (a, l)) =
      ∑ m, algebraMap K (HomogeneousJetField n K) ((l.descFactorial k : K) * M a m) *
        freeCoordinate K (n × ℕ) (m, l - k) := by
  simp only [freeCoordinate]
  rw [jetLoopDerivation_algebraMap, jetLoopDerivationPoly_X, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-! ## The jet shift lowers the depth -/

omit [Fintype n] [DecidableEq n] in
/-- The single-term identity behind the bracket of the jet shift with a loop current. -/
theorem jetLoopShiftTerm (k l : ℕ) (m : n) (c : K) :
    MvPolynomial.C ((l.descFactorial k : K) * c) *
        MvPolynomial.X ((m, l - k + 1) : n × ℕ) -
      MvPolynomial.C ((((l + 1).descFactorial k : ℕ) : K) * c) *
        MvPolynomial.X ((m, l + 1 - k) : n × ℕ) =
    MvPolynomial.C ((-(k : K) * (l.descFactorial (k - 1) : K)) * c) *
      MvPolynomial.X ((m, l - (k - 1)) : n × ℕ) := by
  match k with
  | 0 =>
      simp
  | (j + 1) =>
      rcases le_or_gt (j + 1) l with h | h
      · have hi1 : l - (j + 1) + 1 = l - j := by omega
        have hi2 : l + 1 - (j + 1) = l - j := by omega
        have hi3 : l - (j + 1 - 1) = l - j := by omega
        rw [hi1, hi2, hi3, ← sub_mul, ← map_sub, succ_descFactorial_succ_eq]
        congr 2
        push_cast
        ring
      · rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 h) with heq | hlt
        · subst heq
          have hz : l.descFactorial (l + 1) = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.2 (Nat.lt_succ_self l)
          have hi2 : l + 1 - (l + 1) = 0 := by omega
          have hi3 : l - (l + 1 - 1) = 0 := by omega
          have hs : (l + 1).descFactorial (l + 1) = (l + 1) * l.descFactorial l :=
            Nat.succ_descFactorial_succ l l
          rw [hz, hi2, hi3, hs, Nat.cast_zero, zero_mul, map_zero, zero_mul, zero_sub,
            ← neg_mul, ← map_neg]
          congr 2
          push_cast
          ring
        · have hz1 : l.descFactorial (j + 1) = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
          have hz2 : (l + 1).descFactorial (j + 1) = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
          have hz3 : l.descFactorial j = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
          rw [hz1, hz2, show j + 1 - 1 = j from rfl, hz3]
          simp

omit [DecidableEq n] in
/-- **The jet shift lowers the depth of a loop current.**  Its bracket with the depth-`k` current is
`-k` times the depth-`(k-1)` current; in particular the infinitesimal observers of depth zero
commute with the shift. -/
theorem jetLoopDerivationPoly_lie_shift (k : ℕ) (M : Matrix n n K) :
    ⁅differentialPolynomialDerivation n K, jetLoopDerivationPoly k M⁆ =
      (-(k : K)) • jetLoopDerivationPoly (k - 1) M := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, l⟩
  rw [Derivation.commutator_apply, jetLoopDerivationPoly_X, differentialPolynomialDerivation_X,
    jetLoopDerivationPoly_X, Derivation.smul_apply, jetLoopDerivationPoly_X, map_sum,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hD : differentialPolynomialDerivation n K
      (MvPolynomial.C ((l.descFactorial k : K) * M a m) *
        MvPolynomial.X ((m, l - k) : n × ℕ)) =
      MvPolynomial.C ((l.descFactorial k : K) * M a m) *
        MvPolynomial.X ((m, l - k + 1) : n × ℕ) := by
    rw [Derivation.leibniz, differentialPolynomialDerivation_X, smul_eq_mul]
    have hC : differentialPolynomialDerivation n K
        (MvPolynomial.C ((l.descFactorial k : K) * M a m)) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]
      exact Derivation.map_algebraMap _ _
    rw [hC, smul_zero, add_zero]
  rw [hD]
  have hsmul : ((-(k : K)) • (MvPolynomial.C ((l.descFactorial (k - 1) : K) * M a m) *
      MvPolynomial.X ((m, l - (k - 1)) : n × ℕ))) =
      MvPolynomial.C ((-(k : K) * (l.descFactorial (k - 1) : K)) * M a m) *
        MvPolynomial.X ((m, l - (k - 1)) : n × ℕ) := by
    rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_assoc]
  rw [hsmul]
  exact jetLoopShiftTerm k l m (M a m)

omit [DecidableEq n] in
/-- The same, on the jet field. -/
theorem jetLoopDerivation_lie_shift (k : ℕ) (M : Matrix n n K) :
    ⁅homogeneousJetShift n K, jetLoopDerivation k M⁆ =
      (-(k : K)) • jetLoopDerivation (k - 1) M := by
  rw [homogeneousJetShift, jetLoopDerivation, extendFreeCoordinatePolynomialDerivation_lie,
    jetLoopDerivationPoly_lie_shift, extendFreeCoordinatePolynomialDerivation_smul]
  rfl

omit [DecidableEq n] in
/-- The infinitesimal observers commute with the jet shift. -/
theorem jetDerivation_lie_shift (M : Matrix n n K) :
    ⁅homogeneousJetShift n K, jetDerivation M⁆ = 0 := by
  have h := jetLoopDerivation_lie_shift (K := K) 0 M
  rw [jetLoopDerivation_zero] at h
  rw [h]
  simp

end

end GaloisForLFunctions.HTGeometry
