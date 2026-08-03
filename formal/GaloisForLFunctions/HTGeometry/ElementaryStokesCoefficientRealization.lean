import GaloisForLFunctions.HTGeometry.ElementaryStokesGraphRecognition

/-!
# Global complex coefficients for elementary Stokes dendrograms

For every decorated graph satisfying the acute-isosceles contact law, strict contact thresholds are
equivalence relations.  This module turns each finite threshold quotient into explicit nonzero
complex coefficients and proves that two labels receive the same coefficient exactly when their
prescribed contact lies strictly below the threshold.  Positive powers remain separated, supplying
the coefficient-level source required by ramified Galois-orbit separation.
-/

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

namespace ElementaryDecoratedGraph

def strictThresholdSetoid {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) : Setoid (Fin n) where
  r i j := i = j ∨ g.rescaledEdge i j < t
  iseqv := {
    refl := fun i => Or.inl rfl
    symm := by
      intro i j h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by simpa [g.rescaledEdge_symm] using h)
    trans := by
      intro i j k hij hjk
      rcases hij with rfl | hij
      · exact hjk
      rcases hjk with rfl | hjk
      · exact Or.inr hij
      right
      exact (hacute i j k).2.1.trans_lt (max_lt hij hjk) }

def thresholdClass {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i : Fin n) :
    Quotient (g.strictThresholdSetoid hacute t) :=
  Quotient.mk (g.strictThresholdSetoid hacute t) i

def thresholdClassCode {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i : Fin n) : ℕ :=
  letI : Fintype (Quotient (g.strictThresholdSetoid hacute t)) :=
    Fintype.ofFinite _
  (Fintype.equivFin (Quotient (g.strictThresholdSetoid hacute t))
    (g.thresholdClass hacute t i)).val

def thresholdCoefficient {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i : Fin n) : ℂ :=
  (g.thresholdClassCode hacute t i + 1 : ℕ)

theorem thresholdClass_eq_iff {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i j : Fin n) :
    g.thresholdClass hacute t i = g.thresholdClass hacute t j ↔
      (g.strictThresholdSetoid hacute t).r i j := by
  exact Quotient.eq

theorem thresholdClassCode_eq_iff {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i j : Fin n) :
    g.thresholdClassCode hacute t i = g.thresholdClassCode hacute t j ↔
      (g.strictThresholdSetoid hacute t).r i j := by
  letI : Fintype (Quotient (g.strictThresholdSetoid hacute t)) :=
    Fintype.ofFinite _
  rw [← g.thresholdClass_eq_iff hacute t i j]
  constructor
  · intro h
    unfold thresholdClassCode at h
    apply (Fintype.equivFin (Quotient (g.strictThresholdSetoid hacute t))).injective
    exact Fin.ext h
  · intro h
    unfold thresholdClassCode
    rw [h]

theorem thresholdCoefficient_eq_iff {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i j : Fin n) :
    g.thresholdCoefficient hacute t i = g.thresholdCoefficient hacute t j ↔
      i = j ∨ g.rescaledEdge i j < t := by
  change (((g.thresholdClassCode hacute t i + 1 : ℕ) : ℂ) =
      ((g.thresholdClassCode hacute t j + 1 : ℕ) : ℂ)) ↔ _
  constructor
  · intro h
    have hnat : g.thresholdClassCode hacute t i + 1 =
        g.thresholdClassCode hacute t j + 1 := by exact_mod_cast h
    exact (g.thresholdClassCode_eq_iff hacute t i j).mp (Nat.add_right_cancel hnat)
  · intro h
    have hcode := (g.thresholdClassCode_eq_iff hacute t i j).mpr h
    exact_mod_cast congrArg (· + 1) hcode

theorem thresholdCoefficient_ne_zero {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ) (i : Fin n) :
    g.thresholdCoefficient hacute t i ≠ 0 := by
  change ((g.thresholdClassCode hacute t i + 1 : ℕ) : ℂ) ≠ 0
  exact_mod_cast Nat.succ_ne_zero (g.thresholdClassCode hacute t i)

theorem thresholdCoefficient_pow_ne_of_not_rel {n a : ℕ}
    (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (t : ℚ)
    (ha : 0 < a) {i j : Fin n}
    (hrel : ¬(i = j ∨ g.rescaledEdge i j < t)) :
    g.thresholdCoefficient hacute t i ^ a ≠
      g.thresholdCoefficient hacute t j ^ a := by
  intro hpow
  change (((g.thresholdClassCode hacute t i + 1 : ℕ) : ℂ) ^ a) =
    (((g.thresholdClassCode hacute t j + 1 : ℕ) : ℂ) ^ a) at hpow
  have hnat : (g.thresholdClassCode hacute t i + 1) ^ a =
      (g.thresholdClassCode hacute t j + 1) ^ a := by
    exact_mod_cast hpow
  have hbase := Nat.pow_left_injective (Nat.ne_of_gt ha) hnat
  apply hrel
  apply (g.thresholdCoefficient_eq_iff hacute t i j).mp
  change (((g.thresholdClassCode hacute t i + 1 : ℕ) : ℂ) =
    ((g.thresholdClassCode hacute t j + 1 : ℕ) : ℂ))
  exact_mod_cast hbase

end ElementaryDecoratedGraph
end
end GaloisForLFunctions.IrregularStokes
