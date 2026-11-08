import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeCorePersistence
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockWindows
import Mathlib.Data.ZMod.Basic

/-!
# Binary intervals in actual prime-weighted homology

For each large-prime core of product `m`, characteristic two joins the lower
windows into `[m,3m)` and the upper windows into `[2m,6m)`. The comparisons
use the original core homology ranges, preserve every height map and vanish
outside these intervals. Coefficients persist unchanged across internal births.
-/

noncomputable section
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- In characteristic two the bottom relation first appears at the three-tag birth. -/
theorem twoPrimeBinaryLowerIdeal (m N : ℕ) (h3 : N < 3*m) :
    twoPrimeLowerIdeal (ZMod 2) m N = ⊥ := by
  rw [twoPrimeLowerIdeal,if_neg (not_le.mpr h3)]
  split_ifs
  · have hz : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    simp only [hz,zero_smul,LinearMap.range_zero]
  · rfl

/-- No binary bottom relation exists before three times the core height. -/
theorem twoPrimeBinaryLowerRelations (m N : ℕ) (h3 : N < 3*m) :
    twoPrimeLowerRelations (ZMod 2) m N = ⊥ := by
  ext c
  change c.val ∈ twoPrimeLowerIdeal (ZMod 2) m N ↔ c=0
  rw [twoPrimeBinaryLowerIdeal m N h3]
  change c.val = 0 ↔ c=0
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

/-- Every binary coefficient is an upper cycle once the two-tag is born. -/
def twoPrimeBinaryUpperCoefficientsEquiv (m N : ℕ) (h2 : 2*m ≤ N) :
    twoPrimeUpperCoefficients (ZMod 2) m N ≃ₗ[ZMod 2] ZMod 2 where
  toFun c := c.val
  invFun c := ⟨c,⟨fun hn => False.elim (by omega),fun _ => by
    have hz : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [hz,zero_mul]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The binary lower branch is one coefficient throughout the interval `[m,3m)`. -/
def twoPrimeBinaryLowerEquiv (m N : ℕ) (hm : m ≤ N) (h3 : N < 3*m) :
    TwoPrimeLowerHomology (ZMod 2) m N ≃ₗ[ZMod 2] ZMod 2 :=
  ((twoPrimeLowerRelations (ZMod 2) m N).quotEquivOfEqBot
    (twoPrimeBinaryLowerRelations m N h3)).trans
      (twoPrimeBlockScalarEquiv (ZMod 2) m N hm)

/-- The binary upper branch is one coefficient throughout the interval `[2m,6m)`. -/
def twoPrimeBinaryUpperEquiv (m N : ℕ) (h2 : 2*m ≤ N) (h6 : N < 6*m) :
    TwoPrimeUpperHomology (ZMod 2) m N ≃ₗ[ZMod 2] ZMod 2 :=
  ((twoPrimeUpperRelations (ZMod 2) m N).quotEquivOfEqBot
    (twoPrimeUpperRelations_before (ZMod 2) m N h6)).trans
      (twoPrimeBinaryUpperCoefficientsEquiv m N h2)

/-- The lower binary coefficient persists unchanged, including across the two-tag birth. -/
theorem twoPrimeBinaryLowerEquiv_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (hm : m ≤ N) (h3 : M < 3*m) (x : TwoPrimeLowerHomology (ZMod 2) m N) :
    twoPrimeBinaryLowerEquiv m M (hm.trans h) h3 (twoPrimeLowerHomologyMap (ZMod 2) m h x) =
      twoPrimeBinaryLowerEquiv m N hm (h.trans_lt h3) x := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations (ZMod 2) m N) x
  rfl

/-- The upper binary coefficient persists unchanged, including across the three-tag birth. -/
theorem twoPrimeBinaryUpperEquiv_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (h2 : 2*m ≤ N) (h6 : M < 6*m) (x : TwoPrimeUpperHomology (ZMod 2) m N) :
    twoPrimeBinaryUpperEquiv m M (h2.trans h) h6 (twoPrimeUpperHomologyMap (ZMod 2) m h x) =
      twoPrimeBinaryUpperEquiv m N h2 (h.trans_lt h6) x := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations (ZMod 2) m N) x
  rfl

/-- Actual binary bottom core homology has the interval coefficient `[m,3m)`. -/
def twoPrimeBinaryLowerCoreEquiv (c : TwoPrimeCoreFace) (N : ℕ)
    (hm : twoPrimeCoreHeight c ≤ N) (h3 : N < 3*twoPrimeCoreHeight c) :
    TwoPrimeHomologyCore (ZMod 2) c.val.card N c ≃ₗ[ZMod 2] ZMod 2 :=
  (twoPrimeLowerCoreCoefficientEquiv (ZMod 2) c N).trans
    (twoPrimeBinaryLowerEquiv (twoPrimeCoreHeight c) N hm h3)

/-- Actual binary middle core homology has the interval coefficient `[2m,6m)`. -/
def twoPrimeBinaryUpperCoreEquiv (c : TwoPrimeCoreFace) (N : ℕ)
    (h2 : 2*twoPrimeCoreHeight c ≤ N) (h6 : N < 6*twoPrimeCoreHeight c) :
    TwoPrimeHomologyCore (ZMod 2) (c.val.card+1) N c ≃ₗ[ZMod 2] ZMod 2 :=
  (twoPrimeUpperCoreCoefficientEquiv (ZMod 2) c N).trans
    (twoPrimeBinaryUpperEquiv (twoPrimeCoreHeight c) N h2 h6)

/-- Actual binary lower core homology vanishes outside its exact interval. -/
theorem twoPrimeBinaryLowerCore_outside (c : TwoPrimeCoreFace) (N : ℕ)
    (h : N < twoPrimeCoreHeight c ∨ 3*twoPrimeCoreHeight c ≤ N)
    (x : TwoPrimeHomologyCore (ZMod 2) c.val.card N c) : x=0 := by
  apply (twoPrimeLowerCoreCoefficientEquiv (ZMod 2) c N).injective
  have hz : twoPrimeLowerCoreCoefficientEquiv (ZMod 2) c N x=0 := by
    rcases h with hb | hd
    · exact twoPrimeLowerHomology_before (ZMod 2) (twoPrimeCoreHeight c) N hb _
    · exact twoPrimeLowerHomology_after (ZMod 2) (twoPrimeCoreHeight c) N hd _
  exact hz.trans (map_zero _).symm

#print axioms twoPrimeBinaryLowerCore_outside
/-- Actual binary upper core homology vanishes outside its exact interval. -/
theorem twoPrimeBinaryUpperCore_outside (c : TwoPrimeCoreFace) (N : ℕ)
    (h : N < 2*twoPrimeCoreHeight c ∨ 6*twoPrimeCoreHeight c ≤ N)
    (x : TwoPrimeHomologyCore (ZMod 2) (c.val.card+1) N c) : x=0 := by
  apply (twoPrimeUpperCoreCoefficientEquiv (ZMod 2) c N).injective
  have hz : twoPrimeUpperCoreCoefficientEquiv (ZMod 2) c N x=0 := by
    rcases h with hb | hd
    · exact twoPrimeUpperHomology_before (ZMod 2) (twoPrimeCoreHeight c) N hb _
    · exact twoPrimeUpperHomology_after (ZMod 2) (twoPrimeCoreHeight c) N hd _
  exact hz.trans (map_zero _).symm

#print axioms twoPrimeBinaryUpperCore_outside
/-- Actual binary lower classes retain their interval coefficient under height inclusion. -/
theorem twoPrimeBinaryLowerCoreEquiv_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M)
    (hb : twoPrimeCoreHeight c ≤ N) (hd : M < 3*twoPrimeCoreHeight c)
    (x : TwoPrimeHomologyCore (ZMod 2) c.val.card N c) :
    twoPrimeBinaryLowerCoreEquiv c M (hb.trans h) hd
      (twoPrimeHomologyCoreMap (ZMod 2) c.val.card c h x) =
      twoPrimeBinaryLowerCoreEquiv c N hb (h.trans_lt hd) x := by
  change twoPrimeBinaryLowerEquiv (twoPrimeCoreHeight c) M (hb.trans h) hd
    (twoPrimeLowerCoreCoefficientEquiv (ZMod 2) c M
      (twoPrimeHomologyCoreMap (ZMod 2) c.val.card c h x)) =
    twoPrimeBinaryLowerEquiv (twoPrimeCoreHeight c) N hb (h.trans_lt hd)
      (twoPrimeLowerCoreCoefficientEquiv (ZMod 2) c N x)
  rw [twoPrimeLowerCoreCoefficientEquiv_natural,twoPrimeBinaryLowerEquiv_natural]

#print axioms twoPrimeBinaryLowerCoreEquiv_natural
/-- Actual binary upper classes retain their interval coefficient under height inclusion. -/
theorem twoPrimeBinaryUpperCoreEquiv_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M)
    (hb : 2*twoPrimeCoreHeight c ≤ N) (hd : M < 6*twoPrimeCoreHeight c)
    (x : TwoPrimeHomologyCore (ZMod 2) (c.val.card+1) N c) :
    twoPrimeBinaryUpperCoreEquiv c M (hb.trans h) hd
      (twoPrimeHomologyCoreMap (ZMod 2) (c.val.card+1) c h x) =
      twoPrimeBinaryUpperCoreEquiv c N hb (h.trans_lt hd) x := by
  change twoPrimeBinaryUpperEquiv (twoPrimeCoreHeight c) M (hb.trans h) hd
    (twoPrimeUpperCoreCoefficientEquiv (ZMod 2) c M
      (twoPrimeHomologyCoreMap (ZMod 2) (c.val.card+1) c h x)) =
    twoPrimeBinaryUpperEquiv (twoPrimeCoreHeight c) N hb (h.trans_lt hd)
      (twoPrimeUpperCoreCoefficientEquiv (ZMod 2) c N x)
  rw [twoPrimeUpperCoreCoefficientEquiv_natural,twoPrimeBinaryUpperEquiv_natural]

#print axioms twoPrimeBinaryUpperCoreEquiv_natural
#print axioms twoPrimeBinaryLowerEquiv_natural
#print axioms twoPrimeBinaryUpperEquiv_natural
#print axioms twoPrimeBinaryLowerCoreEquiv
#print axioms twoPrimeBinaryUpperCoreEquiv
end GaloisForLFunctions.EffectiveScalingGeometry
