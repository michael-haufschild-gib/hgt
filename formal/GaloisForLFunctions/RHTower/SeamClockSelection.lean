import GaloisForLFunctions.HTGeometry.WeldRateLattice
import GaloisForLFunctions.RHTower.SigmaOrbit

/-!
# Clock selection for a seam object without a functional equation

An object of the archimedean–difference seam is fixed by two data: a *rate family* `r : ι → ℝ` (the
frequencies of its generators) and a *selecting constraint* — the relation that pins its clock.  The
rate family alone gives the object a weld: if the rates are `ℤ`-linearly independent then the weld
classes `{weldClass (r i)}` are independent (`weldClass_indep_of_linIndep`), and the clock covector on
the rate lattice is free and unique-given-values (`clock_covector_existsUnique`).  None of that selects
a clock; it only says the covector *can* exist.

Whether a *coherent* clock — a single locus fixed by the constraint — actually emerges is decided by
the constraint, not the lattice.  Modelled as an affine map `s ↦ a·s + b` on the clock parameter, the
constraint fixes exactly one locus iff its linear part `a ≠ 1`, and fixes none when `a = 1` and
`b ≠ 0`.  The Riemann functional equation `s ↦ 1 − s` is the reflection `a = −1`; its unique fixed
locus is `1/2`.  This is *one* case.  The seam's own generators are not reflections:

* a **Mahler** constraint `s ↦ q·s` (`a = q ≠ 1`) selects a clock, but at `0`, not `1/2`;
* a **pure shift** `s ↦ s + h` (`a = 1`, `h ≠ 0`) — the native difference-equation / prime-shift
  constraint — selects **no** clock at all.

So a hypertranscendental object carried by a shift constraint has a full nontrivial weld yet no
coherent clock: time does not localize.  The clock is not a feature of the weld or of the rate
lattice; it is read off the linear part of the constraint, and the functional equation is the special
reflection case that happens to hand you `1/2`.  Nothing is constructed here but constraint data — no
carrier, no solution of the difference equation.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- The selecting constraint on the clock parameter, as an affine map `s ↦ a·s + b`.  Its fixed
locus is the selected clock. -/
def affineSelect (a b s : ℂ) : ℂ := a * s + b

/-- With linear part `a ≠ 1` the constraint fixes exactly the point `b / (1 - a)`. -/
theorem affineSelect_fixed_iff {a b : ℂ} (ha : a ≠ 1) (s : ℂ) :
    affineSelect a b s = s ↔ s = b / (1 - a) := by
  unfold affineSelect
  rw [eq_comm, eq_div_iff (sub_ne_zero.mpr (Ne.symm ha))]
  constructor <;> intro h <;> · ring_nf; ring_nf at h; linear_combination h

/-- **A coherent clock is selected iff the constraint is not a pure translation.**  When the linear
part `a ≠ 1` (a reflection `a = −1`, or a scaling `a = q`), the constraint fixes exactly one clock
locus. -/
theorem affineSelect_existsUnique {a b : ℂ} (ha : a ≠ 1) :
    ∃! s, affineSelect a b s = s := by
  refine ⟨b / (1 - a), (affineSelect_fixed_iff ha _).mpr rfl, fun s hs => ?_⟩
  exact (affineSelect_fixed_iff ha s).mp hs

/-- **A pure shift selects no clock.**  A translation `s ↦ s + b` with `b ≠ 0` has no fixed locus —
the native difference/shift constraint localizes no time. -/
theorem affineSelect_no_fixed {b : ℂ} (hb : b ≠ 0) (s : ℂ) :
    affineSelect 1 b s ≠ s := by
  unfold affineSelect; intro h; apply hb; linear_combination h

/-- **The coherent-clock criterion.**  A constraint selects exactly one clock locus iff its linear
part is not `1`.  When `a = 1` the constraint is a translation: either `b ≠ 0` and no locus is fixed,
or `b = 0` and the identity fixes every locus — in both cases the clock is not a single point. -/
theorem affineSelect_existsUnique_iff (a b : ℂ) :
    (∃! s, affineSelect a b s = s) ↔ a ≠ 1 := by
  constructor
  · rintro ⟨s0, hs0, huniq⟩ ha
    subst ha
    have hb0 : b = 0 := by unfold affineSelect at hs0; linear_combination hs0
    have h1 : affineSelect 1 b (s0 + 1) = s0 + 1 := by unfold affineSelect; rw [hb0]; ring
    have hcontra := huniq (s0 + 1) h1
    have : (1 : ℂ) = 0 := by linear_combination hcontra
    exact one_ne_zero this
  · exact affineSelect_existsUnique

/-- The constraint data of a seam object: a rate family with `ℤ`-independent rates (giving the weld)
and an affine selecting constraint `s ↦ selLin · s + selConst` (pinning, or failing to pin, the
clock).  This is constraint data only — no carrier and no solution of the constraint are built. -/
structure SeamObject (ι : Type*) where
  /-- the rate family: the frequencies of the object's generators -/
  rate : ι → ℝ
  /-- the rates carry no `ℤ`-linear relation, so the weld is nontrivial -/
  rate_indep : LinearIndependent ℤ rate
  /-- the linear part of the selecting constraint -/
  selLin : ℂ
  /-- the constant part of the selecting constraint -/
  selConst : ℂ

/-- The object has a nontrivial weld: its weld classes are `ℤ`-linearly independent, whatever the
selecting constraint.  Consumer of `weldClass_indep_of_linIndep`. -/
theorem SeamObject.weld_nontrivial {ι : Type*} (S : SeamObject ι) (c : ι →₀ ℤ)
    (h : c.sum (fun i z => z • weldClassHom (S.rate i)) = 0) : c = 0 :=
  weldClass_indep_of_linIndep S.rate_indep c h

/-- The object's clock covector is free: for any assignment of a time value to each rate there is
exactly one covector on the rate lattice realizing it.  Consumer of `clock_covector_existsUnique`. -/
theorem SeamObject.clock_covector_free {ι : Type*} (S : SeamObject ι) (t : ι → ℝ) :
    ∃! τ : Submodule.span ℤ (Set.range S.rate) →ₗ[ℤ] ℝ,
      ∀ i, τ ⟨S.rate i, Submodule.subset_span ⟨i, rfl⟩⟩ = t i :=
  clock_covector_existsUnique S.rate_indep t

/-- A coherent clock is selected — one locus fixed by the constraint — exactly when the constraint's
linear part is not `1`. -/
theorem SeamObject.clock_selected {ι : Type*} (S : SeamObject ι) (h : S.selLin ≠ 1) :
    ∃! s, affineSelect S.selLin S.selConst s = s :=
  affineSelect_existsUnique h

/-- **A seam object has a coherent clock iff its constraint is not a pure shift.**  The weld is
present for every object (`weld_nontrivial`); a single selected clock locus exists iff the selecting
constraint's linear part is not `1`.  The functional equation (`selLin = −1`) and a Mahler scaling
(`selLin = q ≠ 1`) qualify; the native difference shift (`selLin = 1`) does not. -/
theorem SeamObject.clock_coherent_iff {ι : Type*} (S : SeamObject ι) :
    (∃! s, affineSelect S.selLin S.selConst s = s) ↔ S.selLin ≠ 1 :=
  affineSelect_existsUnique_iff S.selLin S.selConst

/-- The functional-equation object: the prime-rate lattice with the reflection `s ↦ 1 − s`
(`selLin = −1`). -/
def feObject : SeamObject Nat.Primes :=
  ⟨fun p => Real.log (p : ℕ), primeLog_linearIndependent, -1, 1⟩

/-- A Mahler object: the prime-rate lattice with a scaling constraint `s ↦ q·s` (`selLin = q`,
`selConst = 0`) — no functional equation. -/
def mahlerObject (q : ℂ) : SeamObject Nat.Primes :=
  ⟨fun p => Real.log (p : ℕ), primeLog_linearIndependent, q, 0⟩

/-- A shift object: the prime-rate lattice with a pure difference constraint `s ↦ s + h`
(`selLin = 1`) — the native seam shift, no functional equation. -/
def shiftObject (h : ℂ) : SeamObject Nat.Primes :=
  ⟨fun p => Real.log (p : ℕ), primeLog_linearIndependent, 1, h⟩

/-- The functional-equation object's selecting constraint is exactly the reflection `sigma`. -/
theorem feObject_is_sigma (s : ℂ) :
    affineSelect feObject.selLin feObject.selConst s = sigma s := by
  show affineSelect (-1) 1 s = sigma s
  unfold affineSelect sigma; ring

/-- The functional-equation object selects the clock at `1/2` — the fixed locus of `sigma`. -/
theorem feObject_clock_at_half :
    affineSelect feObject.selLin feObject.selConst (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  rw [feObject_is_sigma]; unfold sigma; ring

/-- The Mahler object selects the clock at `0`, not `1/2`: a non-functional-equation constraint still
localizes time, but elsewhere. -/
theorem mahlerObject_clock_at_zero (q : ℂ) :
    affineSelect (mahlerObject q).selLin (mahlerObject q).selConst (0 : ℂ) = 0 := by
  show affineSelect q 0 (0 : ℂ) = 0
  unfold affineSelect; ring

/-- The shift object selects **no** clock: the native difference constraint fixes no locus. -/
theorem shiftObject_no_clock (h : ℂ) (hne : h ≠ 0) (s : ℂ) :
    affineSelect (shiftObject h).selLin (shiftObject h).selConst s ≠ s :=
  affineSelect_no_fixed hne s

/-- Yet the clock-less shift object still has a nontrivial weld: weld and clock are independent.  The
weld is generic to the rate lattice; the clock is the constraint's alone. -/
theorem shiftObject_weld_nontrivial (h : ℂ) (c : Nat.Primes →₀ ℤ)
    (hc : c.sum (fun p z => z • weldClassHom (Real.log (p : ℕ))) = 0) : c = 0 :=
  (shiftObject h).weld_nontrivial c hc

end RHTower
end GaloisForLFunctions
