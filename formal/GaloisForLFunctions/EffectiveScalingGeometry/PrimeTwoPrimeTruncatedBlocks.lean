import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockAlgebra
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyClasses

/-!
# Truncated two-prime block complexes

A squarefree core of height `m` has four tagged faces born at `m`, `2m`,
`3m` and `6m`. Scalar and middle coefficient submodules record these exact
births. The row `(2,3)` and column `(-3,2)` restrict to adjacent short
complexes, with literal inclusions supplying their height persistence.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- A scalar generator is absent before its birth height. -/
def twoPrimeBlockScalar (m N : ℕ) : Submodule R R where
  carrier := {x | N < m → x = 0}
  zero_mem' _ := rfl
  add_mem' hx hy h := by rw [hx h,hy h,add_zero]
  smul_mem' c x hx h := by rw [hx h,smul_zero]

/-- The middle block coordinates are born at twice and three times the core height. -/
def twoPrimeBlockMiddle (m N : ℕ) : Submodule R (R × R) where
  carrier := {x | (N < 2*m → x.1 = 0) ∧ (N < 3*m → x.2 = 0)}
  zero_mem' := ⟨fun _ => rfl,fun _ => rfl⟩
  add_mem' hx hy := ⟨fun h => by change _+_=0; rw [hx.1 h,hy.1 h,add_zero],
    fun h => by change _+_=0; rw [hx.2 h,hy.2 h,add_zero]⟩
  smul_mem' c x hx := ⟨fun h => by change c • _=0; rw [hx.1 h,smul_zero],
    fun h => by change c • _=0; rw [hx.2 h,smul_zero]⟩

theorem twoPrimeBlockScalar_mono (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    twoPrimeBlockScalar R m N ≤ twoPrimeBlockScalar R m M := by
  intro x hx hm
  exact hx (h.trans_lt hm)

theorem twoPrimeBlockMiddle_mono (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    twoPrimeBlockMiddle R m N ≤ twoPrimeBlockMiddle R m M := by
  intro x hx
  exact ⟨fun hm => hx.1 (h.trans_lt hm),fun hm => hx.2 (h.trans_lt hm)⟩

/-- Restrict the row differential to the exact arithmetic births. -/
def twoPrimeBlockCutoffRow (m N : ℕ) :
    twoPrimeBlockMiddle R m N →ₗ[R] twoPrimeBlockScalar R m N :=
  (twoPrimeBlockRow R).restrict (fun x hx h => by
    change 2*x.1+3*x.2=0
    rw [hx.1 (by omega),hx.2 (by omega),mul_zero,mul_zero,add_zero])

/-- Restrict the top differential, whose generator appears at six times the core height. -/
def twoPrimeBlockCutoffTop (m N : ℕ) :
    twoPrimeBlockScalar R (6*m) N →ₗ[R] twoPrimeBlockMiddle R m N :=
  (twoPrimeBlockTop R).restrict (fun x hx => by
    constructor
    · intro h
      change -3*x=0
      rw [hx (by omega),mul_zero]
    · intro h
      change 2*x=0
      rw [hx (by omega),mul_zero])

/-- The upper adjacent complex of one truncated arithmetic block. -/
def twoPrimeUpperBlock (m N : ℕ) : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (twoPrimeBlockScalar R (6*m) N)
  X₂ := ModuleCat.of R (twoPrimeBlockMiddle R m N)
  X₃ := ModuleCat.of R (twoPrimeBlockScalar R m N)
  f := ModuleCat.ofHom (twoPrimeBlockCutoffTop R m N)
  g := ModuleCat.ofHom (twoPrimeBlockCutoffRow R m N)
  zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change 2*(-3*x.val)+3*(2*x.val)=0
    ring

/-- The lower adjacent complex retains the bottom homology quotient. -/
def twoPrimeLowerBlock (m N : ℕ) : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (twoPrimeBlockMiddle R m N)
  X₂ := ModuleCat.of R (twoPrimeBlockScalar R m N)
  X₃ := ModuleCat.of R (twoPrimeBlockScalar R m N)
  f := ModuleCat.ofHom (twoPrimeBlockCutoffRow R m N)
  g := 0
  zero := by simp only [CategoryTheory.Limits.comp_zero]

/-- Raising height includes the same upper-block coefficients. -/
def twoPrimeUpperBlockInclusion (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    twoPrimeUpperBlock R m N ⟶ twoPrimeUpperBlock R m M where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (twoPrimeBlockScalar_mono R (6*m) h))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (twoPrimeBlockMiddle_mono R m h))
  τ₃ := ModuleCat.ofHom (Submodule.inclusion (twoPrimeBlockScalar_mono R m h))
  comm₁₂ := rfl
  comm₂₃ := rfl

/-- Raising height includes the same lower-block coefficients. -/
def twoPrimeLowerBlockInclusion (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    twoPrimeLowerBlock R m N ⟶ twoPrimeLowerBlock R m M where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (twoPrimeBlockMiddle_mono R m h))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (twoPrimeBlockScalar_mono R m h))
  τ₃ := ModuleCat.ofHom (Submodule.inclusion (twoPrimeBlockScalar_mono R m h))
  comm₁₂ := rfl
  comm₂₃ := rfl

/-- The upper adjacent block varies functorially with the arithmetic height. -/
def twoPrimeUpperBlockPersistence (m : ℕ) : ℕ ⥤ ShortComplex (ModuleCat R) where
  obj N := twoPrimeUpperBlock R m N
  map h := twoPrimeUpperBlockInclusion R m h.le
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

/-- The lower adjacent block varies functorially with the arithmetic height. -/
def twoPrimeLowerBlockPersistence (m : ℕ) : ℕ ⥤ ShortComplex (ModuleCat R) where
  obj N := twoPrimeLowerBlock R m N
  map h := twoPrimeLowerBlockInclusion R m h.le
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

#print axioms twoPrimeUpperBlockPersistence
#print axioms twoPrimeLowerBlockPersistence
end GaloisForLFunctions.EffectiveScalingGeometry
