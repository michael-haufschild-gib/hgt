import GaloisForLFunctions.HTGeometry.ReflectionTateAnomaly
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Faithful reflection-Tate localization of conormal charges

Signed reflection-Tate cohomology of a finitely supported integral permutation lattice is
supported on the fixed locus: every free reflection pair is a boundary.  This module isolates the
corresponding support theorem and its Riemann-hypothesis reduction.

The load-bearing hypothesis is not positivity.  It is a source-first conservative reporter from an
integral principal-conormal charge lattice to reflection-Tate cohomology.  If the reporter has a
left inverse through the canonical fixed-locus support map, every charge in its source lattice is
supported at a reflection fixed point.  If every Xi principal conormal lands in that source
lattice, every Xi zero lies on the critical line.

No such source reporter is constructed here.  Defining it from the Xi divisor or assuming the
reconstruction identity only on already fixed zeros would be circular.
-/

open GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

universe u

variable {ι : Type u}

/-- Extend a finitely supported charge on the reflection fixed locus by zero to the ambient
label set. -/
noncomputable def reflectionFixedExtension (r : ι ≃ ι) :
    (ReflectionFixedPoint r →₀ ZMod 2) →+ (ι →₀ ZMod 2) := by
  classical
  exact
    { toFun := Finsupp.extendDomain
      map_zero' := by
        ext i
        simp only [Finsupp.extendDomain_apply]
        split <;> rfl
      map_add' := by
        intro a b
        ext i
        simp only [Finsupp.add_apply, Finsupp.extendDomain_apply]
        split <;> rfl }

theorem reflectionFixedExtension_apply_of_not_fixed
    (r : ι ≃ ι) (a : ReflectionFixedPoint r →₀ ZMod 2)
    {i : ι} (hi : r i ≠ i) :
    reflectionFixedExtension r a i = 0 := by
  simp [reflectionFixedExtension, hi]

/-- Canonical support realization of a signed reflection-Tate class.  The previously formalized
Tate calculation identifies the class with a finite mod-two charge on the fixed locus; this map
then extends that charge by zero. -/
noncomputable def reflectionTateFixedSupport
    (r : ι ≃ ι) (hr : Function.Involutive r) :
    ReflectionTateCohomology r hr →+ (ι →₀ ZMod 2) :=
  (reflectionFixedExtension r).comp
    (reflectionTateCohomologyEquivFixedParity r hr).toAddMonoidHom

theorem reflectionTateFixedSupport_apply_of_not_fixed
    (r : ι ≃ ι) (hr : Function.Involutive r)
    (a : ReflectionTateCohomology r hr) {i : ι} (hi : r i ≠ i) :
    reflectionTateFixedSupport r hr a i = 0 :=
  reflectionFixedExtension_apply_of_not_fixed r _ hi

/-- A source charge lattice is conservatively reported by reflection-Tate cohomology when one
Tate reporter reconstructs every source charge through the canonical fixed-locus support map. -/
def IsReflectionTateConservative
    (r : ι ≃ ι) (hr : Function.Involutive r)
    (B : AddSubgroup (ι →₀ ZMod 2)) : Prop :=
  ∃ report : B →+ ReflectionTateCohomology r hr,
    ∀ q : B, reflectionTateFixedSupport r hr (report q) = q.1

/-- **Faithful anomaly localization.** Every charge reconstructed from reflection-Tate
cohomology is supported on the reflection fixed locus. -/
theorem support_fixed_of_reflectionTateConservative
    (r : ι ≃ ι) (hr : Function.Involutive r)
    (B : AddSubgroup (ι →₀ ZMod 2))
    (hB : IsReflectionTateConservative r hr B)
    (q : B) {i : ι} (hi : i ∈ q.1.support) :
    r i = i := by
  obtain ⟨report, hreconstruct⟩ := hB
  by_contra hfix
  have hzero :=
    reflectionTateFixedSupport_apply_of_not_fixed r hr (report q) hfix
  rw [hreconstruct q] at hzero
  exact (Finsupp.mem_support_iff.mp hi) hzero

/-- A nonzero point charge can belong to a conservatively reflection-Tate-reported source lattice
only at a reflection fixed point. -/
theorem fixed_of_single_mem_reflectionTateConservative
    (r : ι ≃ ι) (hr : Function.Involutive r)
    (B : AddSubgroup (ι →₀ ZMod 2))
    (hB : IsReflectionTateConservative r hr B)
    {i : ι} {c : ZMod 2} (hc : c ≠ 0)
    (hiB : Finsupp.single i c ∈ B) :
    r i = i := by
  let q : B := ⟨Finsupp.single i c, hiB⟩
  apply support_fixed_of_reflectionTateConservative r hr B hB q
  simp [q, hc]

end

end GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Functional-equation--Schwarz reflection as an involutive equivalence of the spectral plane. -/
def xiFEReflection : ℂ ≃ ℂ where
  toFun ρ := 1 - starRingEnd ℂ ρ
  invFun ρ := 1 - starRingEnd ℂ ρ
  left_inv ρ := by
    apply Complex.ext <;> simp
  right_inv ρ := by
    apply Complex.ext <;> simp

theorem xiFEReflection_involutive : Function.Involutive xiFEReflection := by
  intro ρ
  apply Complex.ext <;> simp [xiFEReflection]

/-- Every Xi principal conormal point-charge lands in a source-constructed mod-two charge lattice.
The intended source is the integral jet grading of an Euler--Gamma Bockstein object; no such
landing theorem is assumed globally by the project. -/
def XiPrincipalConormalLandsIn
    (B : AddSubgroup (ℂ →₀ ZMod 2)) : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → Finsupp.single ρ 1 ∈ B

/-- **Reflection-Tate RH reduction.**  RH follows from two source theorems:

1. every Xi principal conormal point-charge lands in one source-defined integral charge lattice;
2. a reflection-Tate reporter reconstructs that whole lattice through its canonical fixed-locus
   support realization.

The second clause is a left-invertibility/conservativity theorem, not a sign or positivity
condition. -/
theorem riemannHypothesis_of_reflectionTate_conormal_localization
    (B : AddSubgroup (ℂ →₀ ZMod 2))
    (hlanding : XiPrincipalConormalLandsIn B)
    (hconservative :
      IsReflectionTateConservative xiFEReflection xiFEReflection_involutive B) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xiZero_reflection_fixed]
  intro ρ hρ
  have hfixed :
      xiFEReflection ρ = ρ :=
    fixed_of_single_mem_reflectionTateConservative
      xiFEReflection xiFEReflection_involutive B hconservative
      (by decide : (1 : ZMod 2) ≠ 0) (hlanding ρ hρ)
  simpa [xiFEReflection] using hfixed

end

end RHTower
