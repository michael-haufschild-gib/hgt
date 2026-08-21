import GaloisForLFunctions.HTGeometry.MilnorKTameDedekind

/-!
# The restricted tame-residue map for a Dedekind fraction field

For the fraction field of a Dedekind domain, every class in `K₂^M` has nonzero tame residue at
only finitely many height-one places.  The coordinatewise tame symbols therefore assemble into a
homomorphism to their direct sum.  Its kernel is precisely the tame kernel.

This is the finite-support, restricted-local layer adjacent to the finite-ramification step in
Albert--Brauer--Hasse--Noether.  It concerns Milnor `K₂`; no comparison with Brauer groups or local
class field theory is used here.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsLocalRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finitely supported family of tame residues of a degree-two Milnor class. -/
noncomputable def tameResidueDirectSumFun (x : MilnorKDeg K 2) :
    DirectSum (HeightOneSpectrum R)
      (fun v => Additive (ResidueField (v.valuation K).valuationSubring)ˣ) := by
  classical
  exact DirectSum.mk
    (fun v : HeightOneSpectrum R =>
      Additive (ResidueField (v.valuation K).valuationSubring)ˣ)
    (finite_tameHomAtPlace_ne_zero_all (R := R) K x).toFinset
    fun v => tameHomAtPlace K v.1 x

/-- A coordinate of the restricted tame-residue family is the ordinary tame symbol. -/
theorem tameResidueDirectSumFun_apply (x : MilnorKDeg K 2) (v : HeightOneSpectrum R) :
    tameResidueDirectSumFun K x v = tameHomAtPlace K v x := by
  classical
  unfold tameResidueDirectSumFun
  by_cases hv : v ∈ (finite_tameHomAtPlace_ne_zero_all (R := R) K x).toFinset
  · rw [DirectSum.mk_apply_of_mem hv]
  · rw [DirectSum.mk_apply_of_notMem hv]
    symm
    by_contra hzero
    apply hv
    exact (Set.Finite.mem_toFinset
      (finite_tameHomAtPlace_ne_zero_all (R := R) K x)).mpr hzero

/-- The direct sum of tame residues is additive in the Milnor class. -/
noncomputable def tameResidueDirectSum :
    MilnorKDeg K 2 →+
      DirectSum (HeightOneSpectrum R)
        (fun v => Additive (ResidueField (v.valuation K).valuationSubring)ˣ) where
  toFun := tameResidueDirectSumFun K
  map_zero' := by
    apply DirectSum.ext
    intro v
    change tameResidueDirectSumFun K 0 v = 0
    rw [tameResidueDirectSumFun_apply]
    exact map_zero _
  map_add' x y := by
    apply DirectSum.ext
    intro v
    change tameResidueDirectSumFun K (x + y) v =
      tameResidueDirectSumFun K x v + tameResidueDirectSumFun K y v
    rw [tameResidueDirectSumFun_apply, tameResidueDirectSumFun_apply,
      tameResidueDirectSumFun_apply]
    exact map_add _ _ _

/-- Evaluation of the additive restricted tame-residue map. -/
theorem tameResidueDirectSum_apply (x : MilnorKDeg K 2) (v : HeightOneSpectrum R) :
    tameResidueDirectSum K x v = tameHomAtPlace K v x :=
  tameResidueDirectSumFun_apply K x v

/-- The kernel of the restricted tame-residue map is the tame kernel at the finite places. -/
theorem tameResidueDirectSum_ker :
    (tameResidueDirectSum (R := R) K).ker =
      tameKernel (fun v : HeightOneSpectrum R => tameDataAtPlace K v) := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_tameKernel_iff]
  constructor
  · intro hx v
    have hxv : tameResidueDirectSum (R := R) K x v = 0 := DFunLike.congr_fun hx v
    rw [tameResidueDirectSum_apply (R := R) K x v] at hxv
    change tameHomAtPlace K v x = 0
    exact hxv
  · intro hx
    apply DirectSum.ext
    intro v
    change tameResidueDirectSum (R := R) K x v = 0
    rw [tameResidueDirectSum_apply (R := R) K x v]
    change (tameDataOfValuation (v.valuation K)).tameHom x = 0
    change ∀ v : HeightOneSpectrum R,
      (tameDataOfValuation (v.valuation K)).tameHom x = 0 at hx
    exact hx v

/-- First-isomorphism-theorem form of the restricted tame-residue map. -/
noncomputable def tameResidueDirectSumQuotientTameKernelEquiv :
    MilnorKDeg K 2 ⧸ tameKernel (fun v : HeightOneSpectrum R => tameDataAtPlace K v) ≃+
      (tameResidueDirectSum (R := R) K).range :=
  (QuotientAddGroup.quotientAddEquivOfEq (tameResidueDirectSum_ker (R := R) K)).symm.trans
    (QuotientAddGroup.quotientKerEquivRange (tameResidueDirectSum (R := R) K))

/-- The tame kernel, `K₂^M`, and the restricted tame-residue direct sum form an exact sequence. -/
theorem tameResidueDirectSum_exact :
    Function.Exact
      (tameKernel (fun v : HeightOneSpectrum R => tameDataAtPlace K v)).subtype
      (tameResidueDirectSum (R := R) K) := by
  intro x
  change x ∈ (tameResidueDirectSum (R := R) K).ker ↔ _
  rw [tameResidueDirectSum_ker (R := R) K]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- The finite-place Hasse criterion for tame symbols: two degree-two Milnor classes have the
same restricted residue profile exactly when their difference is everywhere tamely unramified. -/
theorem tameResidueDirectSum_eq_iff_sub_mem_tameKernel (x y : MilnorKDeg K 2) :
    tameResidueDirectSum (R := R) K x = tameResidueDirectSum (R := R) K y ↔
      x - y ∈ tameKernel (fun v : HeightOneSpectrum R => tameDataAtPlace K v) := by
  constructor
  · intro hxy
    rw [← tameResidueDirectSum_ker (R := R) K]
    change tameResidueDirectSum (R := R) K (x - y) = 0
    rw [sub_eq_add_neg, map_add, map_neg, hxy, add_neg_cancel]
  · intro hxy
    have hker : x - y ∈ (tameResidueDirectSum (R := R) K).ker := by
      rw [tameResidueDirectSum_ker (R := R) K]
      exact hxy
    change tameResidueDirectSum (R := R) K (x - y) = 0 at hker
    rw [sub_eq_add_neg, map_add, map_neg] at hker
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hker)

end GaloisForLFunctions.HTGeometry
