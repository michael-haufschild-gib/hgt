import GaloisForLFunctions.HTGeometry.NormalCrossingMinimalizationDescent

/-!
# No faithful scalar totalization of a genuine bifiltration

The normal-crossing critical-descent object has two independent nonnegative degrees: internal
critical degree and source-face degree.  This file records the exact algebraic obstruction to
collapsing them to one additive filtration.  Every such scalarization identifies nonzero pure
degrees on the two axes.  The positive successor is joint conservativity: two transverse scalar
views already recover the complete bidegree.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Collapse a bidegree to one nonnegative integral filtration degree. -/
def scalarTotalDegree (a b : ℕ) (d : ℕ × ℕ) : ℕ :=
  a * d.1 + b * d.2

/-- Every positive integral scalarization identifies a nonzero pure degree on one axis with a
nonzero pure degree on the other axis. -/
theorem scalarTotalDegree_pureAxis_collision
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      scalarTotalDegree a b (p, 0) = scalarTotalDegree a b (0, q) := by
  exact ⟨b, a, hb, ha, by simp [scalarTotalDegree, Nat.mul_comm]⟩

/-- No nonnegative integral weighted total degree faithfully remembers a genuine bidegree. -/
theorem scalarTotalDegree_not_injective (a b : ℕ) :
    ¬ Function.Injective (scalarTotalDegree a b) := by
  intro hinj
  by_cases ha : a = 0
  · have hpair := hinj (show scalarTotalDegree a b (0, 0) =
        scalarTotalDegree a b (1, 0) by simp [scalarTotalDegree, ha])
    have hfirst := congrArg Prod.fst hpair
    simp at hfirst
  by_cases hb : b = 0
  · have hpair := hinj (show scalarTotalDegree a b (0, 0) =
        scalarTotalDegree a b (0, 1) by simp [scalarTotalDegree, hb])
    have hsecond := congrArg Prod.snd hpair
    simp at hsecond
  have hpair := hinj (show scalarTotalDegree a b (b, 0) =
      scalarTotalDegree a b (0, a) by simp [scalarTotalDegree, Nat.mul_comm])
  have hfirst := congrArg Prod.fst hpair
  simp [hb] at hfirst

/-- **Rank-two grading no-go.**  There is no faithful additive collapse from the free rank-two
nonnegative grading monoid to the rank-one nonnegative grading monoid.  Thus the obstruction is
not an artifact of choosing a particular weighted-total-degree formula. -/
theorem natProd_addMonoidHom_not_injective (w : (ℕ × ℕ) →+ ℕ) :
    ¬ Function.Injective w := by
  intro hinj
  let a := w (1, 0)
  let b := w (0, 1)
  have hleft (n : ℕ) : w (n, 0) = n * a := by
    simpa [a] using w.map_nsmul n (1, 0)
  have hright (n : ℕ) : w (0, n) = n * b := by
    simpa [b] using w.map_nsmul n (0, 1)
  by_cases ha : a = 0
  · have hpair : w (0, 0) = w (1, 0) := by
      calc
        w (0, 0) = 0 := w.map_zero
        _ = 1 * a := by simp [ha]
        _ = w (1, 0) := (hleft 1).symm
    have := congrArg Prod.fst (hinj hpair)
    simp at this
  by_cases hb : b = 0
  · have hpair : w (0, 0) = w (0, 1) := by
      calc
        w (0, 0) = 0 := w.map_zero
        _ = 1 * b := by simp [hb]
        _ = w (0, 1) := (hright 1).symm
    have := congrArg Prod.snd (hinj hpair)
    simp at this
  have hpair : w (b, 0) = w (0, a) := by
    rw [hleft, hright]
    exact Nat.mul_comm b a
  have := congrArg Prod.fst (hinj hpair)
  simp [hb] at this

/-- Two nonparallel scalar views of one bidegree.  The first is ordinary total degree and the
second gives the source degree twice the weight of the internal degree. -/
def transverseScalarDegrees (d : ℕ × ℕ) : ℕ × ℕ :=
  (scalarTotalDegree 1 1 d, scalarTotalDegree 1 2 d)

/-- **Transverse-realization positive theorem.**  Although no one additive scalar totalization is
faithful, the pair with weights `(1,1)` and `(1,2)` is jointly faithful.  Thus two nonparallel
one-parameter realization chains recover the entire rank-two grading. -/
theorem transverseScalarDegrees_injective :
    Function.Injective transverseScalarDegrees := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  simp only [transverseScalarDegrees, scalarTotalDegree, one_mul, Prod.mk.injEq] at h
  apply Prod.ext <;> omega

/-- **Unpaired-realization no-go.**  The two scalar spectra do not recover the bidegrees if their
classes are observed only as separate marginals.  The packets `{(1,1),(2,1)}` and
`{(0,2),(3,0)}` have the same ordinary-total-degree values and the same `(1,2)`-weighted values,
but with the second matching swapped.  A jointly conservative realization therefore needs
comparison data pairing the two scalar observations of the same class. -/
theorem transverseScalarMarginal_pairing_ambiguity :
    scalarTotalDegree 1 1 (1, 1) = scalarTotalDegree 1 1 (0, 2) ∧
    scalarTotalDegree 1 1 (2, 1) = scalarTotalDegree 1 1 (3, 0) ∧
    scalarTotalDegree 1 2 (1, 1) = scalarTotalDegree 1 2 (3, 0) ∧
    scalarTotalDegree 1 2 (2, 1) = scalarTotalDegree 1 2 (0, 2) ∧
    ((1, 1) : ℕ × ℕ) ≠ (0, 2) ∧ ((2, 1) : ℕ × ℕ) ≠ (3, 0) := by
  norm_num [scalarTotalDegree]

end GaloisForLFunctions.HTGeometry
