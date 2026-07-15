import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IntermediateField

/-- Degree of a rational self-map of the projective line.  Mathlib identifies this maximum
with the degree of the function-field extension `K(X) / K(f)`. -/
def ratFuncDegree {K : Type*} [Field K] (f : RatFunc K) : ℕ :=
  max f.num.natDegree f.denom.natDegree

/-- Substitution `a(X) ↦ a(P)` by a nonconstant rational function `P`. -/
def ratFuncSubstitutionAlgHom
    {K : Type*} [Field K] (P : RatFunc K)
    (hP : ¬ ∃ c : K, P = RatFunc.C c) : RatFunc K →ₐ[K] RatFunc K :=
  (K⟮P⟯.val).comp
    (RatFunc.algEquivOfTranscendental P (P.transcendental_of_ne_C hP)).toAlgHom

@[simp]
theorem ratFuncSubstitutionAlgHom_X
    {K : Type*} [Field K] (P : RatFunc K)
    (hP : ¬ ∃ c : K, P = RatFunc.C c) :
    ratFuncSubstitutionAlgHom P hP RatFunc.X = P := by
  simp [ratFuncSubstitutionAlgHom, RatFunc.algEquivOfTranscendental_X]

@[simp]
theorem ratFuncSubstitutionAlgHom_C
    {K : Type*} [Field K] (P : RatFunc K)
    (hP : ¬ ∃ c : K, P = RatFunc.C c) (c : K) :
    ratFuncSubstitutionAlgHom P hP (RatFunc.C c) = RatFunc.C c := by
  change ratFuncSubstitutionAlgHom P hP (algebraMap K (RatFunc K) c) =
    algebraMap K (RatFunc K) c
  exact (ratFuncSubstitutionAlgHom P hP).commutes c

theorem ratFuncSubstitutionAlgHom_fieldRange
    {K : Type*} [Field K] (P : RatFunc K)
    (hP : ¬ ∃ c : K, P = RatFunc.C c) :
    (ratFuncSubstitutionAlgHom P hP).fieldRange = K⟮P⟯ := by
  change ((K⟮P⟯.val).comp
    (RatFunc.algEquivOfTranscendental P (P.transcendental_of_ne_C hP)).toAlgHom).fieldRange = _
  rw [← AlgHom.map_fieldRange,
    AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]

theorem adjoin_map_ratFuncSubstitutionAlgHom
    {K : Type*} [Field K] (P a : RatFunc K)
    (hP : ¬ ∃ c : K, P = RatFunc.C c) :
    K⟮a⟯.map (ratFuncSubstitutionAlgHom P hP) =
      K⟮ratFuncSubstitutionAlgHom P hP a⟯ := by
  rw [show K⟮a⟯ = IntermediateField.adjoin K {a} from rfl,
    IntermediateField.adjoin_map]
  simp only [Set.image_singleton]

/-- **Degree multiplicativity for genuine rational substitution.**  This proof uses the tower
`K(a(P)) ⊆ K(P) ⊆ K(X)`, so it includes every possible numerator-denominator cancellation. -/
theorem ratFuncDegree_substitution
    {K : Type*} [Field K] (P a : RatFunc K)
    (hP : ¬ ∃ c : K, P = RatFunc.C c) :
    ratFuncDegree (ratFuncSubstitutionAlgHom P hP a) =
      ratFuncDegree a * ratFuncDegree P := by
  let φ := ratFuncSubstitutionAlgHom P hP
  have hmap := IntermediateField.relfinrank_map_map K⟮a⟯
    (⊤ : IntermediateField K (RatFunc K)) φ
  have hrel :
      K⟮φ a⟯.relfinrank K⟮P⟯ =
        Module.finrank K⟮a⟯ (RatFunc K) := by
    rw [← adjoin_map_ratFuncSubstitutionAlgHom P a hP,
      ← ratFuncSubstitutionAlgHom_fieldRange P hP,
      AlgHom.fieldRange_eq_map,
      hmap,
      IntermediateField.relfinrank_top_right]
  have hle : K⟮φ a⟯ ≤ K⟮P⟯ := by
    rw [← adjoin_map_ratFuncSubstitutionAlgHom P a hP,
      ← ratFuncSubstitutionAlgHom_fieldRange P hP,
      AlgHom.fieldRange_eq_map]
    exact IntermediateField.map_mono φ le_top
  calc
    ratFuncDegree (φ a) = Module.finrank K⟮φ a⟯ (RatFunc K) :=
      (RatFunc.finrank_eq_max_natDegree (φ a)).symm
    _ = K⟮φ a⟯.relfinrank K⟮P⟯ * Module.finrank K⟮P⟯ (RatFunc K) :=
      (IntermediateField.relfinrank_mul_finrank_top hle).symm
    _ = Module.finrank K⟮a⟯ (RatFunc K) * Module.finrank K⟮P⟯ (RatFunc K) := by
      rw [hrel]
    _ = ratFuncDegree a * ratFuncDegree P := by
      rw [RatFunc.finrank_eq_max_natDegree, RatFunc.finrank_eq_max_natDegree]
      rfl

theorem ratFuncDegree_pos_of_not_constant
    {K : Type*} [Field K] {a : RatFunc K}
    (ha : ¬ ∃ c : K, a = RatFunc.C c) : 0 < ratFuncDegree a := by
  apply Nat.pos_of_ne_zero
  intro hzero
  apply ha
  rw [RatFunc.eq_C_iff]
  exact Nat.max_eq_zero_iff.mp hzero

theorem succ_le_two_pow : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- **No nonconstant order-zero tail.**  A fixed rational function cannot factor through
rational protocol prefixes whose degrees grow at least as `2^n`. -/
theorem compatibleRatFuncChain_zeroPhase_constant
    {K : Type*} [Field K]
    (P a : ℕ → RatFunc K)
    (hP : ∀ n, ¬ ∃ c : K, P n = RatFunc.C c)
    (hdegree : ∀ n, 2 ^ n ≤ ratFuncDegree (P n))
    (hcompat : ∀ n, ratFuncSubstitutionAlgHom (P n) (hP n) (a n) = a 0) :
    ∃ c : K, a 0 = RatFunc.C c := by
  by_contra ha0
  push Not at ha0
  let N := ratFuncDegree (a 0)
  have haN : ¬ ∃ c : K, a N = RatFunc.C c := by
    rintro ⟨c, hc⟩
    apply ha0 c
    rw [← hcompat N, hc, ratFuncSubstitutionAlgHom_C]
  have hdegEq : ratFuncDegree (a 0) = ratFuncDegree (a N) * ratFuncDegree (P N) := by
    rw [← hcompat N]
    exact ratFuncDegree_substitution (P N) (a N) (hP N)
  have hP_le : ratFuncDegree (P N) ≤ ratFuncDegree (a 0) := by
    rw [hdegEq]
    exact Nat.le_mul_of_pos_left _ (ratFuncDegree_pos_of_not_constant haN)
  have hlt : ratFuncDegree (a 0) < 2 ^ N := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (succ_le_two_pow N)
  exact (not_lt_of_ge ((hdegree N).trans hP_le)) hlt

end

end GaloisForLFunctions.HTGeometry
