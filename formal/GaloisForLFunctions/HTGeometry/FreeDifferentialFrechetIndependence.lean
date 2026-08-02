import GaloisForLFunctions.HTGeometry.DerivationPrescription
import GaloisForLFunctions.HTGeometry.FreeDifferentialChainRule

/-!
# Independence of the rows of the Frechet matrix

The rows of the Frechet matrix of a differential embedding of free differential rational fields
are left linearly independent over the ring of differential operators of the target field.

A relation between the rows says exactly that a finite combination of the differentials of the
jets of the images `Φ y_i` vanishes.  Those jets are algebraically independent over the constants,
so a derivation may be prescribed to be `1` on any one of them and `0` on the others; the
coordinate expansion of that derivation then forces the corresponding coefficient to vanish.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace JetField

noncomputable section

universe w

variable {C : Type u} {ι : Type v} {ι' : Type w} [Field C]

/-- The jet coordinates are algebraically independent over the constants. -/
theorem algebraicIndependent_jet :
    AlgebraicIndependent C (fun p : ι × ℕ => (jet p : JetField C ι)) := by
  have hX : AlgebraicIndependent C (MvPolynomial.X : (ι × ℕ) → JetPoly C ι) :=
    MvPolynomial.algebraicIndependent_X (R := C) (σ := ι × ℕ)
  exact hX.map' (f := IsScalarTower.toAlgHom C (JetPoly C ι) (JetField C ι))
    (IsFractionRing.injective (JetPoly C ι) (JetField C ι))

section Embedding

variable [Algebra (JetField C ι') (JetField C ι)]
  [IsScalarTower C (JetField C ι') (JetField C ι)]

/-- The images of the jet coordinates under a differential embedding are algebraically
independent over the constants. -/
theorem algebraicIndependent_algebraMap_jet :
    AlgebraicIndependent C
      (fun p : ι' × ℕ => algebraMap (JetField C ι') (JetField C ι) (jet p)) :=
  (algebraicIndependent_jet (C := C) (ι := ι')).map'
    (f := IsScalarTower.toAlgHom C (JetField C ι') (JetField C ι))
    (algebraMap (JetField C ι') (JetField C ι)).injective

variable (hδ : ∀ u : JetField C ι', algebraMap (JetField C ι') (JetField C ι) (u′)
  = (algebraMap (JetField C ι') (JetField C ι) u)′)

include hδ

/-- **Independence of the Frechet rows.** -/
theorem rowIndep_frechetMatrix [CharZero C] [Fintype ι'] [Fintype ι] :
    DiffOp.RowIndep (frechetMatrix (C := C) (ι' := ι') (ι := ι)) := by
  classical
  intro v hv
  -- a finite set carrying the supports of all the components of `v`
  set T : Finset ℕ := Finset.univ.biUnion fun i : ι' => (DiffOp.toFinsupp (v i)).support with hT
  have hTsupp : ∀ (i : ι') (n : ℕ), n ∉ T → DiffOp.coeff (v i) n = 0 := by
    intro i n hn
    by_contra hc
    exact hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finsupp.mem_support_iff.mpr hc⟩)
  -- the images of the source jets
  set z : ι' × ℕ → JetField C ι :=
    fun p => algebraMap (JetField C ι') (JetField C ι) (jet p) with hz
  have hzindep : AlgebraicIndependent C z := algebraicIndependent_algebraMap_jet
  -- the relation, coefficientwise
  have hrel : ∀ (j : ι) (m : ℕ),
      ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T, DiffOp.coeff (v p.1) p.2 * pd (j, m) (z p) = 0 := by
    intro j m
    have h0 : DiffOp.coeff (DiffOp.vecMul v (frechetMatrix (C := C) (ι' := ι') (ι := ι)) j) m
        = 0 := by
      rw [congrFun hv j, Pi.zero_apply, DiffOp.coeff_zero]
    rw [DiffOp.vecMul, ← DiffOp.coeffAddHom_apply m, map_sum] at h0
    rw [Finset.sum_product]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h0
    rw [DiffOp.coeffAddHom_apply,
      DiffOp.coeff_mul_of_subset (t := T) (fun n hn => hTsupp i n hn)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coeff_dpartial_iterate_frechetMatrix hδ]
  -- a finite set carrying the coordinates occurring in the images
  have hpdfin : ∀ p : ι' × ℕ, ∃ s : Finset (ι × ℕ), ∀ q ∉ s, pd q (z p) = 0 := by
    intro p
    exact exists_finset_pd_eq_zero (z p)
  choose sset hsset using hpdfin
  set S : Finset (ι × ℕ) :=
    ((Finset.univ : Finset ι') ×ˢ T).biUnion fun p => sset p with hS
  have hSvanish : ∀ (p : ι' × ℕ), p ∈ (Finset.univ : Finset ι') ×ˢ T →
      ∀ q ∉ S, pd q (z p) = 0 := by
    intro p hp q hq
    refine hsset p q fun hmem => hq ?_
    exact Finset.mem_biUnion.mpr ⟨p, hp, hmem⟩
  -- every coefficient vanishes
  funext i₀
  ext n₀
  rw [Pi.zero_apply, DiffOp.coeff_zero]
  by_cases hn₀ : n₀ ∈ T
  · -- prescribe a derivation dual to the coordinate `(i₀, n₀)`
    obtain ⟨D, hD⟩ := exists_derivation_prescribed (C := C) (L := JetField C ι) hzindep
      (fun p => if p = (i₀, n₀) then 1 else 0)
    have hDz : ∀ p : ι' × ℕ, D (z p) = if p = (i₀, n₀) then 1 else 0 := by
      intro p
      rw [hD p]
      by_cases hp : p = (i₀, n₀)
      · rw [if_pos hp, if_pos hp, map_one]
      · rw [if_neg hp, if_neg hp, map_zero]
    have hexp : ∀ p ∈ (Finset.univ : Finset ι') ×ˢ T,
        D (z p) = ∑ q ∈ S, (pd q (z p)) • D (jet q) := fun p hp =>
      pd_expansion D (z p) S (hSvanish p hp)
    have hzero : ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T,
        DiffOp.coeff (v p.1) p.2 * D (z p) = 0 := by
      have hstep1 : ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T,
          DiffOp.coeff (v p.1) p.2 * D (z p)
          = ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T, ∑ q ∈ S,
              DiffOp.coeff (v p.1) p.2 * (pd q (z p) * D (jet q)) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [hexp p hp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_eq_mul]
      have hstep3 : ∑ q ∈ S, ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T,
            DiffOp.coeff (v p.1) p.2 * (pd q (z p) * D (jet q))
          = ∑ q ∈ S, (∑ p ∈ (Finset.univ : Finset ι') ×ˢ T,
              DiffOp.coeff (v p.1) p.2 * pd q (z p)) * D (jet q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      rw [hstep1, Finset.sum_comm, hstep3]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hrel q.1 q.2, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => by rw [hDz p])] at hzero
    have hsingle : ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T,
        DiffOp.coeff (v p.1) p.2 * (if p = (i₀, n₀) then (1 : JetField C ι) else 0)
        = DiffOp.coeff (v i₀) n₀ := by
      rw [Finset.sum_eq_single ((i₀, n₀) : ι' × ℕ)]
      · rw [if_pos rfl, mul_one]
      · intro p _ hp
        rw [if_neg hp, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_product.mpr ⟨Finset.mem_univ i₀, hn₀⟩) hmem
    rw [hsingle] at hzero
    exact hzero
  · exact hTsupp i₀ n₀ hn₀

end Embedding

end

end JetField

end GaloisForLFunctions.HTGeometry
