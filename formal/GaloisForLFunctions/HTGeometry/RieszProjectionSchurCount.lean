import GaloisForLFunctions.HTGeometry.FinrankIndependentSup
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteSectionMultiplicity
import GaloisForLFunctions.HTGeometry.RieszProjectionFiniteSection
import GaloisForLFunctions.HTGeometry.RieszProjectionSpectral
import GaloisForLFunctions.HTGeometry.SchurCharpoly

/-!
# Riesz rank of a finite section in Schur coordinates

For a contour avoiding zero, the Riesz projection of a zero-padded finite section has rank equal
to the number of Schur diagonal entries inside the contour, with algebraic multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Matrix Metric

variable {ι : Type*} [DecidableEq ι]

/-- The Riesz projection of a zero-padded finite section has finite-dimensional range whenever
its contour avoids zero. -/
theorem finiteDimensional_range_rieszProjection_toOperator_truncKernel
    {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r)
    (hres : ∀ lam ∈ sphere c r,
      lam ∈ resolventSet ℂ (toOperator (isHS_truncKernel hK s)))
    (hzero : (0 : ℂ) ∉ closedBall c r) :
    FiniteDimensional ℂ (LinearMap.range
      ((rieszProjection (toOperator (isHS_truncKernel hK s)) c r :
        lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
        lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) := by
  have hLfinite : FiniteDimensional ℂ (LinearMap.range (liftBlockFinLinearMap s)) :=
    (LinearEquiv.ofInjective (liftBlockFinLinearMap s)
      (liftBlockFinLinearMap_injective s)).finiteDimensional
  letI : FiniteDimensional ℂ (LinearMap.range (liftBlockFinLinearMap s)) := hLfinite
  have hle : LinearMap.range
      ((rieszProjection (toOperator (isHS_truncKernel hK s)) c r :
        lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
        lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) ≤
      LinearMap.range (liftBlockFinLinearMap s) :=
    le_trans
      (range_rieszProjection_le_range (toOperator (isHS_truncKernel hK s)) hr hres hzero)
      (le_trans (range_toOperator_truncKernel_le_range_liftBlockLinearMap hK s)
        (range_liftBlockLinearMap_le_range_liftBlockFinLinearMap s))
  exact Submodule.finiteDimensional_of_le hle

open scoped Classical in
/-- **Finite-section Riesz rank is the enclosed Schur count.** -/
theorem finrank_range_rieszProjection_toOperator_truncKernel_eq_schurCount
    {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hres : ∀ lam ∈ closedBall c R \ ball c r,
      lam ∈ resolventSet ℂ (toOperator (isHS_truncKernel hK s)))
    (hzero : (0 : ℂ) ∉ closedBall c r)
    (U T : Matrix (Fin (Fintype.card ↥s)) (Fin (Fintype.card ↥s)) ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hT : T.BlockTriangular id)
    (hMT : Uᴴ * blockFin K s * U = T) :
    Module.finrank ℂ (LinearMap.range
        ((rieszProjection (toOperator (isHS_truncKernel hK s)) c r :
          lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
          lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) =
      (Finset.univ.filter fun i => T i i ≠ 0 ∧ T i i ∈ ball c r).card := by
  classical
  let S : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
    toOperator (isHS_truncKernel hK s)
  let p : ℂ → Submodule ℂ (lp (fun _ : ι => ℂ) 2) := fun mu =>
    Module.End.maxGenEigenspace (S :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) mu
  let J : Finset (Fin (Fintype.card ↥s)) :=
    Finset.univ.filter fun i => T i i ≠ 0 ∧ T i i ∈ ball c r
  let D : Finset ℂ := J.image fun i => T i i

  have hsphere : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ S := by
    intro lam hlam
    apply hres lam
    exact ⟨by
      rw [mem_closedBall, mem_sphere.mp hlam]
      linarith, by
      rw [mem_ball, mem_sphere.mp hlam]
      linarith⟩
  have hP : rieszProjection S c r * rieszProjection S c r = rieszProjection S c r :=
    rieszProjection_mul_self S hr hrR hres

  have hLfinite : FiniteDimensional ℂ (LinearMap.range (liftBlockFinLinearMap s)) :=
    (LinearEquiv.ofInjective (liftBlockFinLinearMap s)
      (liftBlockFinLinearMap_injective s)).finiteDimensional
  letI : FiniteDimensional ℂ (LinearMap.range (liftBlockFinLinearMap s)) := hLfinite
  have hPrange : LinearMap.range ((rieszProjection S c r :
      lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) ≤
      LinearMap.range (liftBlockFinLinearMap s) :=
    le_trans (range_rieszProjection_le_range S hr.le hsphere hzero)
      (le_trans (range_toOperator_truncKernel_le_range_liftBlockLinearMap hK s)
        (range_liftBlockLinearMap_le_range_liftBlockFinLinearMap s))
  letI : FiniteDimensional ℂ (LinearMap.range ((rieszProjection S c r :
      lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) :=
    Submodule.finiteDimensional_of_le hPrange
  have hrange : LinearMap.range ((rieszProjection S c r :
      lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) =
      ⨆ mu ∈ ball c r, p mu := by
    exact range_rieszProjection_eq_iSup_maxGenEigenspace hr.le hsphere hP inferInstance

  have hDmem {mu : ℂ} (hmu : mu ∈ D) : mu ≠ 0 ∧ mu ∈ ball c r := by
    obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp hmu
    exact (Finset.mem_filter.mp hiJ).2
  have hp_le_range {mu : ℂ} (hmu0 : mu ≠ 0) :
      p mu ≤ LinearMap.range (liftBlockFinLinearMap s) := by
    exact le_trans (maxGenEigenspace_le_range_of_ne_zero (S :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) hmu0)
      (le_trans (range_toOperator_truncKernel_le_range_liftBlockLinearMap hK s)
        (range_liftBlockLinearMap_le_range_liftBlockFinLinearMap s))

  have hsup : D.sup p = ⨆ mu ∈ ball c r, p mu := by
    apply le_antisymm
    · apply Finset.sup_le
      intro mu hmu
      exact le_iSup₂ (f := fun nu (_ : nu ∈ ball c r) => p nu) mu (hDmem hmu).2
    · refine iSup₂_le fun mu hmu => ?_
      have hmu0 : mu ≠ 0 := by
        intro hz
        apply hzero
        simpa [hz] using ball_subset_closedBall hmu
      by_cases hpbot : p mu = ⊥
      · rw [hpbot]
        exact bot_le
      have hpfinite : FiniteDimensional ℂ (p mu) :=
        Submodule.finiteDimensional_of_le (hp_le_range hmu0)
      letI : FiniteDimensional ℂ (p mu) := hpfinite
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpbot
      have hpos : 0 < Module.finrank ℂ (p mu) :=
        Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
      have hblock := finrank_maxGenEigenspace_toOperator_truncKernel_eq_blockFin hK s hmu0
      have hschur := finrank_maxGenEigenspace_eq_schurCount hU1 hU2 hT hMT mu
      have hcardpos : 0 < (Finset.univ.filter fun i => T i i = mu).card := by
        rw [← hschur, hblock]
        exact hpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcardpos
      have hdiag : T i i = mu := (Finset.mem_filter.mp hi).2
      have hiJ : i ∈ J := by
        change i ∈ Finset.univ.filter fun j => T j j ≠ 0 ∧ T j j ∈ ball c r
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ i, hdiag.symm ▸ ⟨hmu0, hmu⟩⟩
      have hmuD : mu ∈ D := Finset.mem_image.mpr ⟨i, hiJ, hdiag⟩
      exact Finset.le_sup (f := p) hmuD

  let q : ↥D → Submodule ℂ (lp (fun _ : ι => ℂ) 2) := fun mu => p (mu : ℂ)
  letI (mu : ↥D) : FiniteDimensional ℂ (q mu) :=
    Submodule.finiteDimensional_of_le (hp_le_range (hDmem mu.2).1)
  have hqind : iSupIndep q :=
    (Module.End.independent_maxGenEigenspace (S :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)).comp Subtype.coe_injective
  have hqsum := finrank_finset_sup_of_iSupIndep q hqind (Finset.univ : Finset ↥D)
  have hqSup : (Finset.univ : Finset ↥D).sup q = D.sup p := by
    rw [Finset.sup_eq_iSup, Finset.sup_eq_iSup]
    simp only [Finset.mem_univ, iSup_true]
    apply le_antisymm
    · refine iSup_le fun mu => ?_
      exact le_iSup₂ (f := fun a (_ : a ∈ D) => p a) (mu : ℂ) mu.2
    · refine iSup₂_le fun a ha => ?_
      exact le_iSup (fun mu : ↥D => p (mu : ℂ)) ⟨a, ha⟩
  have hsum : Module.finrank ℂ
      (D.sup p : Submodule ℂ (lp (fun _ : ι => ℂ) 2)) =
      ∑ mu ∈ D, Module.finrank ℂ (p mu) := by
    rw [← hqSup]
    calc
      Module.finrank ℂ ((Finset.univ : Finset ↥D).sup q :
          Submodule ℂ (lp (fun _ : ι => ℂ) 2)) =
          ∑ mu ∈ D.attach, Module.finrank ℂ (p (mu : ℂ)) := by
            simpa [q] using hqsum
      _ = ∑ mu ∈ D, Module.finrank ℂ (p mu) :=
        D.sum_attach (fun mu => Module.finrank ℂ (p mu))

  rw [hrange, ← hsup, hsum]
  calc
    (∑ mu ∈ D, Module.finrank ℂ (p mu))
        = ∑ mu ∈ D, (Finset.univ.filter fun i => T i i = mu).card := by
            apply Finset.sum_congr rfl
            intro mu hmu
            have hmu0 := (hDmem hmu).1
            rw [← finrank_maxGenEigenspace_eq_schurCount hU1 hU2 hT hMT mu,
              finrank_maxGenEigenspace_toOperator_truncKernel_eq_blockFin hK s hmu0]
    _ = J.card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
        have hjp := (Finset.mem_filter.mp hj).2
        change i ∈ Finset.univ.filter fun k => T k k ≠ 0 ∧ T k k ∈ ball c r
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ i, by simpa [← hji] using hjp⟩
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    _ = (Finset.univ.filter fun i => T i i ≠ 0 ∧ T i i ∈ ball c r).card := rfl

end GaloisForLFunctions.HTGeometry
