import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The local mass of unit-fraction sieve conditioning

In the paragraph following Lemma 5.3 of arXiv:2611.14167, primitive
residue pairs exclude only (0,0). Both entries must be units for Kacd=1.
Counting that smaller locus gives the exact rough density. On a fixed
primitive ray the missing mass has a second parametrization.
-/

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning

variable (F : Type*) [Field F]

abbrev Pair := {b : F × F // b ≠ (0,0)}
abbrev Sample := Pair F × F

def product (K : F) (s : Sample F) : F := K*s.1.val.1*s.1.val.2*s.2

abbrev Hit (K : F) := {s : Sample F // product F K s = 1}
abbrev RayHit (K r : F) := {s : Hit F K // s.val.1.val.1+r*s.val.1.val.2=0}

variable {F}

private theorem unit_pair (a c : Fˣ) : ((a : F),(c : F)) ≠ (0,0) :=
  fun h => a.ne_zero (congrArg Prod.fst h)

/-- Nonzero low digits a,c determine the unique forbidden low digit d. -/
def hitEquiv (K : Fˣ) : Hit F (K : F) ≃ Fˣ × Fˣ where
  toFun s := by
    have h := s.property
    have ha : s.val.1.val.1 ≠ 0 := by intro hz; simp [product,hz] at h
    have hc : s.val.1.val.2 ≠ 0 := by intro hz; simp [product,hz] at h
    exact (Units.mk0 _ ha,Units.mk0 _ hc)
  invFun u := ⟨(⟨((u.1 : F),(u.2 : F)),unit_pair _ _⟩,((K : F)*u.1*u.2)⁻¹),by
    exact mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero K.ne_zero u.1.ne_zero) u.2.ne_zero)⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := s.property
      change (K : F)*s.val.1.val.1*s.val.1.val.2*s.val.2=1 at h
      exact inv_eq_of_mul_eq_one_right h
  right_inv u := by ext <;> rfl

/-- The numerator congruence a+rc=0 cuts the forbidden set to one
punctured line parametrized by c. -/
def rayEquiv (K r : Fˣ) : RayHit F (K : F) (r : F) ≃ Fˣ where
  toFun s := ((hitEquiv K) s.val).2
  invFun c := ⟨(hitEquiv K).symm (-(r*c),c),by change -(↑r*↑c)+(r : F)*↑c=0; ring⟩
  left_inv s := by
    apply Subtype.ext
    apply (hitEquiv K).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · apply Units.ext
      change -((r : F)*s.val.val.1.val.2)=s.val.val.1.val.1
      have hs := s.property
      linear_combination -hs
    · rfl
  right_inv c := by
    change ((hitEquiv K) ((hitEquiv K).symm _)).2 = c
    rw [Equiv.apply_symm_apply]

variable [Fintype F] [DecidableEq F]

theorem count_sample : Fintype.card (Sample F) = ((Fintype.card F)^2-1)*Fintype.card F := by
  rw [Fintype.card_prod,Fintype.card_subtype_compl (fun b : F × F => b=(0,0))]
  simp only [Fintype.card_prod,Fintype.card_subtype_eq,pow_two]

/-- A prime dividing the numerator never divides the witness modulus. -/
theorem count_rough_at_zero :
    Fintype.card {s : Sample F // product F 0 s ≠ 1} = Fintype.card (Sample F) := by
  let e : {s : Sample F // product F 0 s ≠ 1} ≃ Sample F :=
    { toFun := Subtype.val, invFun := fun s => ⟨s,by simp [product]⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  exact Fintype.card_congr e

theorem count_hit (K : Fˣ) : Fintype.card (Hit F (K : F)) = (Fintype.card F-1)^2 := by
  rw [Fintype.card_congr (hitEquiv K),Fintype.card_prod,Fintype.card_units,pow_two]

theorem count_ray (K r : Fˣ) : Fintype.card (RayHit F (K : F) (r : F)) = Fintype.card F-1 := by
  rw [Fintype.card_congr (rayEquiv K r),Fintype.card_units]

/-- Exact number of primitive triples for which the witness modulus Kacd−1
is a unit. Pairs on a coordinate axis contribute with every d. -/
theorem count_rough (K : Fˣ) :
    Fintype.card {s : Sample F // product F (K : F) s ≠ 1} =
      ((Fintype.card F)^2-1)*Fintype.card F - (Fintype.card F-1)^2 := by
  rw [Fintype.card_subtype_compl (fun s : Sample F => product F (K : F) s=1),
    count_sample,count_hit]

/-- Relative to all primitive pairs, the exact rough fraction exceeds
the both-coordinates-nonzero fraction by 2/(q(q+1)). -/
theorem rough_density (K : Fˣ) :
    (Fintype.card {s : Sample F // product F (K : F) s ≠ 1} : ℚ) /
      Fintype.card (Sample F) =
      1-1/(Fintype.card F : ℚ)+2/((Fintype.card F : ℚ)*(Fintype.card F+1)) := by
  let q := Fintype.card F
  have hq : 1 < q := Fintype.one_lt_card
  have hq' : (1 : ℚ) < q := by exact_mod_cast hq
  have hpos : 0<q^2 := pow_pos (by omega) _
  have hcard : (q-1)^2 ≤ (q^2-1)*q := by
    have h₁ : q-1 ≤ q^2-1 := Nat.sub_le_sub_right (by nlinarith only [hq] : q ≤ q^2) 1
    simpa only [sq] using Nat.mul_le_mul h₁ (Nat.sub_le q 1)
  rw [count_rough,count_sample]
  change (((q^2-1)*q-(q-1)^2 : ℕ) : ℚ)/(((q^2-1)*q : ℕ) : ℚ) = _
  push_cast [Nat.cast_sub hcard,Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_sub (by omega : 1 ≤ q^2)]
  change (((q : ℚ)^2-1)*q-(q-1)^2)/(((q : ℚ)^2-1)*q)=1-1/q+2/((q : ℚ)*(q+1))
  have hn : (q : ℚ)^2-1 ≠ 0 := by nlinarith only [hq',sq_nonneg ((q : ℚ)-1)]
  have hp : (q : ℚ) ≠ 0 := (zero_lt_one.trans hq').ne'
  field_simp
  ring

end GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning

#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_sample
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_hit
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_ray
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_rough
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.rough_density

#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.hitEquiv
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.rayEquiv
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_rough_at_zero
