import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPrincipalDivisorRigidity
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Contact orders of the complete Hermitian plane linear system

Affine functions with infinity pole bounded by Q+1 are exactly the
affine-linear functions in the two coordinates. At any point their
normalized local basis consists of one, a uniformizer and the tangent.
Its three distinct orders determine the entire vanishing sequence.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "φ" => algebraMap E H
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "T" => hermitianGeometricTangentFunction p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "V" => hermitianGeometricPointValuation p s
local notation "W" => hermitianGeometricInfinityValuation p s

/-- The first plane linear system on the normalization has explicit global coordinates. -/
theorem hermitianPlaneSections_affine (f : H) (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hi : W f ≤ WithZero.exp ((Q+1:ℕ):ℤ)) :
    ∃ a b c : E, f = φ a + φ b*z + φ c*u := by
  classical
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  obtain ⟨t,ht,hdeg⟩ := hermitianGeometric_exists_lowDegree_polynomial_expansion p s f 1 hQ hf
    (by simpa only [one_mul] using hi)
  let i₀ : Fin (Q+1) := ⟨0,Nat.succ_pos _⟩
  let i₁ : Fin (Q+1) := ⟨1,by omega⟩
  have hne : i₀ ≠ i₁ := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hb (i : Fin (Q+1)) : i.val + (t i).natDegree ≤ 1 ∨ t i = 0 :=
    (em (t i = 0)).elim Or.inr (fun h => Or.inl (hdeg i h))
  have h₀ : (t i₀).natDegree ≤ 1 := by
    rcases hb i₀ with h | h
    · change 0 + (t i₀).natDegree ≤ 1 at h
      simpa only [Nat.zero_add] using h
    · simp [h]
  have h₁ : (t i₁).natDegree ≤ 0 := by
    rcases hb i₁ with h | h
    · change 1 + _ ≤ 1 at h; omega
    · simp [h]
  obtain ⟨c,a,hca⟩ := exists_eq_X_add_C_of_natDegree_le_one h₀
  let b := (t i₁).coeff 0
  let η := (hermitianExtensionTraceConstant p s E : E)
  let g := fun i : Fin (Q+1) => algebraMap E[X] H (t i) * z^i.val
  have hsum : ∑ i, g i = g i₀ + g i₁ := by
    calc
      _ = ∑ i ∈ ({i₀,i₁} : Finset _), g i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hg : t i = 0 := by
          rcases hb i with h | h
          · have hle : i.val ≤ 1 := by omega
            have hor : i.val = 0 ∨ i.val = 1 := by omega
            apply (hi ?_).elim
            rcases hor with he | he
            · exact Finset.mem_insert.mpr (Or.inl (Fin.ext he : i = i₀))
            · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Fin.ext he : i = i₁))
          · exact h
        simp only [g,hg,map_zero,zero_mul]
      _ = _ := by simp [hne]
  have hc (e : E) : algebraMap E[X] H (C e) = φ e :=
    (IsScalarTower.algebraMap_apply E E[X] H e).symm
  refine ⟨a,b,c*η,?_⟩
  rw [ht]
  change (∑ i, g i) = _
  rw [hsum]
  change algebraMap E[X] H (t i₀) * z^0 + algebraMap E[X] H (t i₁) * z^1 = _
  rw [hca,eq_C_of_natDegree_le_zero h₁, pow_zero,pow_one,mul_one,map_add,map_mul,hc,hc,hc,
    ← hermitianExtensionAdditiveCoordinate_recover, map_mul]
  dsimp only [b,η]
  ring

/-- Changing to the flag of a point and its tangent gives adapted local coordinates. -/
theorem hermitianPlaneSections_adapted (P : Pts) (f : H)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hi : W f ≤ WithZero.exp ((Q+1:ℕ):ℤ)) :
    ∃ a b c : E, f = φ a + (φ b*(z-φ P.val.1) + φ c*T P) := by
  obtain ⟨a,b,c,h⟩ := hermitianPlaneSections_affine p s f hf hi
  refine ⟨a+b*P.val.1+c*P.val.2,b+c*P.val.1^Q,c,?_⟩
  rw [h,hermitianGeometricTangentFunction_eq]
  simp only [map_add,map_mul]
  ring

private theorem geometric_scalar_le (P : Pts) (a : E) : V P (φ a) ≤ 1 := by
  by_cases h : a=0
  · rw [h,map_zero,map_zero]; exact zero_le_one
  · exact (hermitianGeometricPointValuation_constant p s P a h).le

private theorem scalar_factor_le (P : Pts) (a : E) (f : H) :
    V P (φ a*f) ≤ V P f := by
  rw [map_mul]
  exact mul_le_of_le_one_left' (geometric_scalar_le p s P a)

/-- At every affine point the tangent term is strictly smaller than the uniformizer. -/
theorem hermitianGeometricTangent_contact_gt_one (P : Pts) :
    V P (T P) < WithZero.exp (-1:ℤ) := by
  have hQ : 1<Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  rw [hermitianGeometricPointValuation_tangent, WithZero.exp_lt_exp]
  split_ifs <;> omega

/-- The local leading term of any plane section is determined exactly by its first nonzero coefficient. -/
theorem hermitianPlaneSection_value (P : Pts) (a b c : E) :
    V P (φ a + (φ b*(z-φ P.val.1) + φ c*T P)) =
      if a ≠ 0 then 1 else if b ≠ 0 then WithZero.exp (-1:ℤ) else V P (φ c*T P) := by
  classical
  have ht := (scalar_factor_le p s P c (T P)).trans_lt (hermitianGeometricTangent_contact_gt_one p s P)
  have hz := (scalar_factor_le p s P b (z-φ P.val.1)).trans_eq
    (hermitianGeometricPointValuation_radical_sub p s P)
  have he : WithZero.exp (-1:ℤ) < 1 := by rw [← WithZero.exp_zero,WithZero.exp_lt_exp]; omega
  by_cases ha : a≠0
  · rw [if_pos ha,(V P).map_add_eq_of_lt_left,hermitianGeometricPointValuation_constant p s P a ha]
    rw [hermitianGeometricPointValuation_constant p s P a ha]
    exact (V P).map_add_lt (hz.trans_lt he) (ht.trans he)
  · rw [if_neg ha,not_not.mp ha,map_zero,zero_add]
    by_cases hb : b≠0
    · have heq : V P (φ b*(z-φ P.val.1)) = WithZero.exp (-1:ℤ) := by
        rw [map_mul,hermitianGeometricPointValuation_constant p s P b hb,one_mul,
          hermitianGeometricPointValuation_radical_sub]
      rw [if_pos hb,(V P).map_add_eq_of_lt_left (ht.trans_eq heq.symm),heq]
    · rw [if_neg hb,not_not.mp hb,map_zero,zero_mul,zero_add]

/-- Vanishing beyond order one picks out precisely the tangent line in the full plane linear system. -/
theorem hermitianPlaneSection_highContact_iff (P : Pts) (f : H)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hi : W f ≤ WithZero.exp ((Q+1:ℕ):ℤ)) :
    V P f < WithZero.exp (-1:ℤ) ↔ ∃ c : E, f = φ c*T P := by
  constructor
  · intro h
    obtain ⟨a,b,c,hc⟩ := hermitianPlaneSections_adapted p s P f hf hi
    rw [hc,hermitianPlaneSection_value] at h
    by_cases ha : a≠0
    · rw [if_pos ha,← WithZero.exp_zero,WithZero.exp_lt_exp] at h; omega
    · rw [if_neg ha] at h
      by_cases hb : b≠0
      · rw [if_pos hb] at h; exact (lt_irrefl _ h).elim
      · exact ⟨c,by simpa only [not_not.mp ha,not_not.mp hb,map_zero,zero_mul,zero_add] using hc⟩
  · rintro ⟨c,rfl⟩
    exact (scalar_factor_le p s P c (T P)).trans_lt (hermitianGeometricTangent_contact_gt_one p s P)

#print axioms hermitianPlaneSections_affine
#print axioms hermitianPlaneSections_adapted
#print axioms hermitianGeometricTangent_contact_gt_one
#print axioms hermitianPlaneSection_value
#print axioms hermitianPlaneSection_highContact_iff

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
