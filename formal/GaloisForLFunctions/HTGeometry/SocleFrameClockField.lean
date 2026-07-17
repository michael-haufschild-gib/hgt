import GaloisForLFunctions.HTGeometry.TransverseClockConstraintScheme
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.DualNumber

/-!
# Primitive amplitude frames for clocked constraint schemes

A scalar amplitude does not merely evaluate a constraint algebra: structural multiplication moves
it through a regular orbit in the linear dual.  This file identifies the exact conservativity
criterion.  The structural orbits of a primitive family span the full dual exactly when the joint
regular readout is injective.

The positive no-go is sharp.  If the orbit span is proper, some nonzero structural law is invisible
to every available amplitude orbit even though its complete transverse clock jet is algebraically
independent.  Thus insufficient amplitude width does not destroy hypertranscendence; it destroys
conservative access to a genuinely hypertranscendental survivor.

The final theorem gives the elementary but decisive canonicality obstruction: on the dual-number
constraint algebra, no functional nonzero on the nilpotent boundary can be invariant under every
nonzero scaling of that boundary.  The canonical object is therefore a frame orbit, not a selected
scalar amplitude.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {K : Type u} {A : Type v} [Field K]
variable [CommRing A] [Algebra K A]

/-- The regular structural orbit of a scalar amplitude. -/
def structuralAmplitudeAction (a : A) (ell : Module.Dual K A) : Module.Dual K A :=
  ell.comp (LinearMap.mulLeft K a)

@[simp]
theorem structuralAmplitudeAction_apply
    (a b : A) (ell : Module.Dual K A) :
    structuralAmplitudeAction a ell b = ell (a * b) := rfl

/-- The linear span of all structural translates of primitive amplitudes. -/
def primitiveAmplitudeOrbitSpan {alpha : Type w} (ell : alpha -> Module.Dual K A) :
    Submodule K (Module.Dual K A) :=
  Submodule.span K {psi | Exists fun j : alpha => Exists fun a : A =>
    psi = structuralAmplitudeAction a (ell j)}

/-- Joint regular readout: a law is tested against every primitive amplitude after multiplication
by every structural coefficient. -/
def primitiveStructuralReadout {alpha : Type w} (ell : alpha -> Module.Dual K A) :
    A →ₗ[K] (alpha → A → K) where
  toFun a j b := ell j (a * b)
  map_add' a b := by
    funext j x
    simp [add_mul]
  map_smul' c a := by
    funext j x
    simp [Algebra.smul_mul_assoc]

@[simp]
theorem primitiveStructuralReadout_apply {alpha : Type w}
    (ell : alpha -> Module.Dual K A) (a b : A) (j : alpha) :
    primitiveStructuralReadout ell a j b = ell j (a * b) := rfl

/-- The laws invisible to every structural amplitude orbit are exactly the kernel of the joint
regular readout. -/
theorem primitiveAmplitudeOrbitSpan_dualCoannihilator {alpha : Type w}
    (ell : alpha -> Module.Dual K A) :
    (primitiveAmplitudeOrbitSpan ell).dualCoannihilator =
      LinearMap.ker (primitiveStructuralReadout ell) := by
  ext a
  simp only [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
  constructor
  · intro h
    funext j b
    have horbit : structuralAmplitudeAction b (ell j) ∈ primitiveAmplitudeOrbitSpan ell :=
      Submodule.subset_span ⟨j, b, rfl⟩
    simpa [structuralAmplitudeAction_apply, mul_comm] using h _ horbit
  · intro h psi hpsi
    rw [primitiveAmplitudeOrbitSpan, Submodule.mem_span] at hpsi
    exact hpsi (LinearMap.ker (Module.Dual.eval K A a)) (by
      rintro _ ⟨j, b, rfl⟩
      change ell j (b * a) = 0
      have hab := congr_fun (congr_fun h j) b
      simpa [mul_comm] using hab)

/-- **Exact primitive conservativity criterion.**  In finite dimension, structural translates of
the primitive amplitudes span the complete dual exactly when their joint regular readout is
injective. -/
theorem primitiveAmplitudeOrbitSpan_eq_top_iff {alpha : Type w}
    [FiniteDimensional K A] (ell : alpha -> Module.Dual K A) :
    primitiveAmplitudeOrbitSpan ell = ⊤ ↔
      Function.Injective (primitiveStructuralReadout ell) := by
  rw [← LinearMap.ker_eq_bot, ← primitiveAmplitudeOrbitSpan_dualCoannihilator]
  constructor
  · intro h
    simp [h]
  · intro h
    have hdouble := Subspace.dualCoannihilator_dualAnnihilator_eq
      (W := primitiveAmplitudeOrbitSpan ell)
    rw [h] at hdouble
    simpa using hdouble.symm

/-- A proper primitive orbit span has an explicit nonzero jointly invisible structural law. -/
theorem exists_invisible_law_of_primitiveAmplitudeOrbitSpan_ne_top
    {alpha : Type w} [FiniteDimensional K A]
    (ell : alpha -> Module.Dual K A)
    (h : primitiveAmplitudeOrbitSpan ell ≠ ⊤) :
    ∃ a : A, a ≠ 0 ∧ ∀ j b, ell j (a * b) = 0 := by
  have hnotinj : ¬ Function.Injective (primitiveStructuralReadout ell) := by
    intro hinj
    exact h ((primitiveAmplitudeOrbitSpan_eq_top_iff ell).mpr hinj)
  rw [injective_iff_map_eq_zero (primitiveStructuralReadout ell)] at hnotinj
  push Not at hnotinj
  obtain ⟨a, hzero, ha⟩ := hnotinj
  refine ⟨a, ha, ?_⟩
  intro j b
  exact congr_fun (congr_fun hzero j) b

/-- A conservative primitive amplitude family detects every structural law which survives the
prescribed constraint ideal. -/
theorem conservativePrimitiveAmplitudes_detect_survivingLaw
    {iota : Type v} {alpha : Type w}
    (I : Ideal (MvPolynomial iota K))
    [FiniteDimensional K (TransverseConstraintAlgebra I)]
    (ell : alpha -> Module.Dual K (TransverseConstraintAlgebra I))
    (hell : primitiveAmplitudeOrbitSpan ell = ⊤)
    (p : MvPolynomial iota K) (hp : p ∉ I) :
    ∃ j a, ell j (Ideal.Quotient.mk I p * a) ≠ 0 := by
  have hinj : Function.Injective (primitiveStructuralReadout ell) :=
    (primitiveAmplitudeOrbitSpan_eq_top_iff ell).mp hell
  by_contra h
  push Not at h
  have hzero : primitiveStructuralReadout ell (Ideal.Quotient.mk I p) = 0 := by
    ext j a
    exact h j a
  have hclass : Ideal.Quotient.mk I p = 0 := hinj (by simpa using hzero)
  exact hp (Ideal.Quotient.eq_zero_iff_mem.mp hclass)

/-- **Positive survivor below the conservativity wall.**  If the primitive amplitude orbits do not
span the dual, some law outside the constraint ideal is invisible to every one of those orbits,
while its complete transverse clock jet is nevertheless algebraically independent. -/
theorem insufficientPrimitiveAmplitudes_miss_hypertranscendentalLaw
    {iota : Type v} {alpha : Type w}
    (I : Ideal (MvPolynomial iota K))
    [FiniteDimensional K (TransverseConstraintAlgebra I)]
    (ell : alpha -> Module.Dual K (TransverseConstraintAlgebra I))
    (hell : primitiveAmplitudeOrbitSpan ell ≠ ⊤) :
    ∃ p : MvPolynomial iota K,
      p ∉ I ∧
      AlgebraicIndependent K (transverseLawJet I p) ∧
      ∀ j a, ell j (Ideal.Quotient.mk I p * a) = 0 := by
  obtain ⟨x, hx, hinvisible⟩ :=
    exists_invisible_law_of_primitiveAmplitudeOrbitSpan_ne_top ell hell
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hp : p ∉ I := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨p, hp, (transverseLawJet_algebraicIndependent_iff I p).mpr hp, hinvisible⟩

/-- Pull scalar amplitudes on a quotient algebra back to the finer source algebra. -/
def transportedPrimitiveAmplitude
    {B : Type x} [CommRing B] [Algebra K B] {alpha : Type w}
    (q : B →ₐ[K] A) (ell : alpha → Module.Dual K A) :
    alpha → Module.Dual K B :=
  fun j => q.toLinearMap.dualMap (ell j)

/-- **Exact exceptional-dual transition law.**  Suppose the primitive readout on a quotient
algebra is conservative.  After dual transport along a surjective source transition, its complete
invisible subspace is neither larger nor smaller than the transition kernel.  Thus the full
dualizing interval is transported without loss; precisely the new finer-layer laws are invisible
to amplitudes pulled back from the quotient. -/
theorem transportedPrimitiveReadout_ker_eq_sourceKernel
    {B : Type x} [CommRing B] [Algebra K B] {alpha : Type w}
    (q : B →ₐ[K] A) (hq : Function.Surjective q)
    (ell : alpha → Module.Dual K A)
    (hell : Function.Injective (primitiveStructuralReadout ell)) :
    LinearMap.ker
        (primitiveStructuralReadout (transportedPrimitiveAmplitude q ell)) =
      LinearMap.ker q.toLinearMap := by
  ext b
  simp only [LinearMap.mem_ker]
  constructor
  · intro hb
    apply hell
    have hz : primitiveStructuralReadout ell (q b) = 0 := by
      funext j a
      obtain ⟨x, rfl⟩ := hq a
      have hx := congr_fun (congr_fun hb j) x
      simpa [transportedPrimitiveAmplitude] using hx
    simpa using hz
  · intro hb
    funext j x
    change ell j (q (b * x)) = 0
    change q b = 0 at hb
    rw [map_mul, hb, zero_mul, map_zero]

/-- Dual transport of a conservative quotient readout is conservative on the finer source exactly
when the source transition itself is injective. -/
theorem transportedPrimitiveReadout_injective_iff_sourceTransition_injective
    {B : Type x} [CommRing B] [Algebra K B] {alpha : Type w}
    (q : B →ₐ[K] A) (hq : Function.Surjective q)
    (ell : alpha → Module.Dual K A)
    (hell : Function.Injective (primitiveStructuralReadout ell)) :
    Function.Injective
        (primitiveStructuralReadout (transportedPrimitiveAmplitude q ell)) ↔
      Function.Injective q := by
  change Function.Injective
      (primitiveStructuralReadout (transportedPrimitiveAmplitude q ell)) ↔
    Function.Injective q.toLinearMap
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    transportedPrimitiveReadout_ker_eq_sourceKernel q hq ell hell]

open scoped DualNumber

/-- **Dual-number canonicality obstruction.**  No amplitude which sees the nilpotent boundary of
the dual numbers is invariant under every nonzero scaling of that boundary.  Hence a source-free
natural construction cannot select a faithful scalar frame even on this smallest nonreduced
constraint algebra. -/
theorem no_dualNumber_scalingInvariant_faithfulAmplitude
    [CharZero K] :
    ¬ ∃ ell : Module.Dual K (DualNumber K),
        ell DualNumber.eps ≠ 0 ∧
          ∀ u : Kˣ, ell ((u : K) • DualNumber.eps) = ell DualNumber.eps := by
  rintro ⟨ell, hell, hinv⟩
  have hneg := hinv (-1 : Kˣ)
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, map_neg] at hneg
  exact hell (neg_eq_self.mp hneg)

end

end GaloisForLFunctions.HTGeometry
