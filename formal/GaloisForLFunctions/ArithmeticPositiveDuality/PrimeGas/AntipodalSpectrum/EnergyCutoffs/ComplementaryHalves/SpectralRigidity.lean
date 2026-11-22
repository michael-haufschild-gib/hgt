import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.DigitTiling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rigidity of the paired half-integer spectrum

A complete simple spectrum fixes both the relative scale and the common
translation. Collisions exclude smaller scales and the first missing
digit excludes every larger scale.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

def scaled (C : Radix) (q : ℕ) (p : Half C × Half C) := p.1.val+q*p.2.val

theorem integral_scale_iff (C : Radix) (q : ℕ) : Function.Bijective (scaled C q) ↔ q = C.val := by
  constructor
  · intro h
    let o := origin C
    let i := single C ⟨1,C.property⟩
    have hi : i.val = 1 := single_val C _
    rcases lt_trichotomy q C.val with hq|he|hq
    · let x := single C ⟨q,hq⟩
      have hx : x.val = q := single_val C _
      have he : scaled C q (x,o) = scaled C q (o,i) := by
        change x.val+q*0 = 0+q*i.val
        rw [hx,hi]; simp
      have hi₀ : (0:ℕ) = i.val := congrArg (fun p : Half C × Half C => p.2.val) (h.1 he)
      omega
    · exact he
    · obtain ⟨p,hp⟩ := h.2 C.val
      change p.1.val+q*p.2.val = C.val at hp
      rcases Nat.eq_zero_or_pos p.2.val with hz|hy
      · exact ((excludes_radix C p.1) (by simpa only [hz,mul_zero,add_zero] using hp)).elim
      · have hb := Nat.le_mul_of_pos_right q hy
        omega
  · rintro rfl
    exact (interleave C).bijective

def midpoint (C : Radix) : ℝ := 1/(2*((C.val:ℝ)+1))

theorem midpoint_eq (C : Radix) : ((C.val:ℝ)+1)*midpoint C = 1/2 := by
  unfold midpoint
  field_simp [show (C.val:ℝ)+1 ≠ 0 by positivity]

/-- Joint additive level before taking its energy logarithm. -/
def affineLevel {C : Radix} (r a : ℝ) (p : Half C × Half C) : ℝ :=
  ((p.1.val:ℝ)+a)+r*((p.2.val:ℝ)+a)

theorem level_formula (C : Radix) (a : ℝ) (p : Half C × Half C) :
    affineLevel (C.val:ℝ) a p = (interleave C p:ℝ)+((C.val:ℝ)+1)*a := by
  rw [interleave_apply,Nat.cast_add,Nat.cast_mul,affineLevel]
  ring

theorem centered_level (C : Radix) (p : Half C × Half C) :
    affineLevel (C.val:ℝ) (midpoint C) p = (interleave C p:ℝ)+1/2 := by
  rw [level_formula,midpoint_eq]

/-- Multiplicity-one enumeration of all positive half-integers. -/
def HalfIntegerSpectrum (C : Radix) (r a : ℝ) : Prop :=
  ∃ e : Half C × Half C ≃ ℕ, ∀ p, affineLevel r a p = (e p:ℝ)+1/2

/-- Even among real scales and translations, the half-integer spectrum uniquely fixes both. -/
theorem half_integer_rigidity (C : Radix) (r a : ℝ) :
    HalfIntegerSpectrum C r a ↔ r = (C.val:ℝ) ∧ a = midpoint C := by
  constructor
  · rintro ⟨e,h⟩
    let o := origin C
    let i := single C ⟨1,C.property⟩
    let n := e (o,o)
    let m := e (o,i)
    have ho : (o.val:ℝ) = 0 := Nat.cast_zero
    have h₀ : a+r*a = (n:ℝ)+1/2 := by simpa only [affineLevel,ho,zero_add] using h (o,o)
    have hall (p : Half C × Half C) : (p.1.val:ℝ)+r*p.2.val+n = (e p:ℝ) := by
      have hp := h p
      unfold affineLevel at hp
      linear_combination hp-h₀
    have hi : i.val = 1 := single_val C _
    have hr : r+(n:ℝ) = m := by
      have hh := hall (o,i)
      change (o.val:ℝ)+r*(i.val:ℝ)+n = m at hh
      simpa only [ho,hi,Nat.cast_one,zero_add,mul_one] using hh
    have hnm : n ≤ m := by
      by_contra! hm
      have hmn : (m:ℝ)+1 ≤ n := by exact_mod_cast (show m+1 ≤ n from hm)
      obtain ⟨x,hx⟩ := exists_large C n
      have hx' : (n:ℝ) < x.val := by exact_mod_cast hx
      have hh := hall (o,x)
      change (o.val:ℝ)+r*x.val+n = (e (o,x):ℝ) at hh
      rw [ho,zero_add] at hh
      have hneg : r ≤ -1 := by linarith only [hr,hmn]
      linarith only [hh,hx',mul_le_mul_of_nonneg_right hneg (Nat.cast_nonneg (α := ℝ) x.val),
        Nat.cast_nonneg (α := ℝ) (e (o,x))]
    let q := m-n
    have hq : r = (q:ℝ) := by
      change r = ((m-n:ℕ):ℝ)
      rw [Nat.cast_sub hnm]
      linarith only [hr]
    have he (p : Half C × Half C) : scaled C q p+n = e p := by
      have ht := hall p
      rw [hq] at ht
      change p.1.val+q*p.2.val+n = e p
      exact_mod_cast ht
    obtain ⟨z,hz⟩ := e.surjective 0
    have hn : n = 0 := by have H := he z; rw [hz] at H; omega
    have heq : scaled C q = e := funext fun p => by simpa only [hn,add_zero] using he p
    have hqC := (integral_scale_iff C q).mp (heq ▸ e.bijective)
    have hrC : r = (C.val:ℝ) := hq.trans (congrArg (fun k : ℕ => (k:ℝ)) hqC)
    refine ⟨hrC,?_⟩
    simp only [hn,Nat.cast_zero,zero_add,hrC] at h₀
    apply mul_left_cancel₀ (show (C.val:ℝ)+1 ≠ 0 by positivity)
    rw [midpoint_eq]
    linarith only [h₀]
  · rintro ⟨rfl,rfl⟩
    exact ⟨interleave C,centered_level C⟩

#print axioms integral_scale_iff
#print axioms half_integer_rigidity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
