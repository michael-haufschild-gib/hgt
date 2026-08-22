import GaloisForLFunctions.HTGeometry.AffineSpectrumRelationEscape

/-!
# Transporting the escape property along a unitary coordinate change

A spectral escape witness is produced in the spectral basis, while the family that has to inherit it
lives on the physical carrier.  The two are related by a rectangular "unitary" `B` with
`Bᴴ B = 1` and `B Bᴴ = 1`, whose source and target index types are different but of equal
cardinality.  Determinants of such a `B` are not available, but the kernel characterization of a
vanishing determinant is, and it transports characteristic roots in both directions.

## Main results

* `card_eq_of_coordinateUnitary` — the two index types have the same cardinality.
* `matrixCharpolyRelation_eq_zero_of_coordinate` — characteristic roots transport.
* `SpectrumEscapesAffineRelations.ofCoordinate` — hence so does the escape property.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem card_eq_of_coordinateUnitary {B : Matrix I J ℂ}
    (hL : Bᴴ * B = 1) (hR : B * Bᴴ = 1) : Fintype.card I = Fintype.card J := by
  have htr : (Bᴴ * B).trace = (B * Bᴴ).trace := Matrix.trace_mul_comm _ _
  rw [hL, hR, Matrix.trace_one, Matrix.trace_one] at htr
  exact_mod_cast htr.symm

/-- A characteristic root of the coordinate matrix is a characteristic root of the original. -/
theorem matrixCharpolyRelation_eq_zero_of_coordinate {B : Matrix I J ℂ}
    (hL : Bᴴ * B = 1) (hR : B * Bᴴ = 1)
    {N : Matrix I I ℂ} {M : Matrix J J ℂ} (hcoord : Bᴴ * N * B = M) {z : ℂ}
    (hM : matrixCharpolyRelation (M, z) = 0) :
    matrixCharpolyRelation (N, z) = 0 := by
  classical
  have hscalJ : (Matrix.scalar J z : Matrix J J ℂ) = z • (1 : Matrix J J ℂ) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.scalar_apply, hab]
  have hscalI : (Matrix.scalar I z : Matrix I I ℂ) = z • (1 : Matrix I I ℂ) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.scalar_apply, hab]
  have hMdet : (Matrix.scalar J z - M).det = 0 := hM
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMdet
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.scalar I z - N)).mp ⟨B.mulVec v, ?_, ?_⟩
  · intro h0
    apply hv
    have hid : Bᴴ.mulVec (B.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at hid
    exact hid.symm
  · have hNB : N * B = B * M := by
      calc N * B = (B * Bᴴ) * N * B := by rw [hR, Matrix.one_mul]
        _ = B * (Bᴴ * N * B) := by simp [Matrix.mul_assoc]
        _ = B * M := by rw [hcoord]
    have hkey : (Matrix.scalar I z - N) * B = B * (Matrix.scalar J z - M) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, hNB, hscalI, hscalJ]
      simp [Matrix.smul_mul, Matrix.mul_smul]
    calc (Matrix.scalar I z - N).mulVec (B.mulVec v)
        = ((Matrix.scalar I z - N) * B).mulVec v := (Matrix.mulVec_mulVec _ _ _)
      _ = (B * (Matrix.scalar J z - M)).mulVec v := by rw [hkey]
      _ = B.mulVec ((Matrix.scalar J z - M).mulVec v) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hvz, Matrix.mulVec_zero]

/-- **Transport of the escape property.**  If every escaping matrix of the source family is the
coordinate image of a member of the target family, the target family escapes too. -/
theorem SpectrumEscapesAffineRelations.ofCoordinate {B : Matrix I J ℂ}
    (hL : Bᴴ * B = 1) (hR : B * Bᴴ = 1)
    {S : Set (Matrix J J ℂ)} {T : Set (Matrix I I ℂ)}
    (hS : SpectrumEscapesAffineRelations S)
    (hmap : ∀ M ∈ S, ∃ N ∈ T, Bᴴ * N * B = M) :
    SpectrumEscapesAffineRelations T := by
  classical
  have hcard : Fintype.card I = Fintype.card J := card_eq_of_coordinateUnitary hL hR
  let σ : I ≃ J := Fintype.equivOfCardEq hcard
  intro c hbalanced hc target
  have hbalanced' : ∑ j, (c (σ.symm j)) = 0 := by
    rw [← hbalanced]
    exact Fintype.sum_equiv σ.symm _ _ fun j => rfl
  have hc' : (fun j => c (σ.symm j)) ≠ 0 := by
    intro h
    refine hc (funext fun i => ?_)
    have := congrFun h (σ i)
    simpa using this
  obtain ⟨M, hMS, E, hEinj, hEroot, hEesc⟩ := hS (fun j => c (σ.symm j)) hbalanced' hc' target
  obtain ⟨N, hNT, hcoord⟩ := hmap M hMS
  refine ⟨N, hNT, fun i => E (σ i), hEinj.comp σ.injective, ?_, ?_⟩
  · intro i
    exact matrixCharpolyRelation_eq_zero_of_coordinate hL hR hcoord (hEroot (σ i))
  · intro π hzero
    refine hEesc ((σ.symm.trans π).trans σ) ?_
    rw [← hzero]
    refine (Fintype.sum_equiv σ _ _ fun i => ?_).symm
    simp
end

end GaloisForLFunctions.HTGeometry
