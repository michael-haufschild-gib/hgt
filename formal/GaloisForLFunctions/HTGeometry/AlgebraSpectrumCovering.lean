import GaloisForLFunctions.HTGeometry.AlgebraSpectrumBijection
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumChart

/-!
# The complex-point space is a covering space of the parameter line

Assembling the chart bijection, the continuity of its inverse, and the root-locus chart gives a
partial homeomorphism of the complex-point space at every point, hence a local homeomorphism; with
the Tychonoff properness this makes the projection a covering map.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology

noncomputable section

namespace AlgSpec

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- The chart, as a partial homeomorphism between the preimage of `U` in the complex-point space
and the part of the root locus above `U`. -/
theorem isLocalHomeomorph_proj_of_chart {θ : B} {p : ℂ[X][X]}
    (hp : Polynomial.aeval θ p = 0) (hmonic : p.Monic)
    {U : Set ℂ} (hU : IsOpen U)
    (hgen : ∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
      (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q)
    (hsep : ∀ s ∈ U, (biFibre p s).Separable)
    (hcard : ∀ s ∈ U, {χ : AlgSpec B | proj B χ = s}.ncard = p.natDegree)
    (χ₀ : AlgSpec B) (hχ₀ : proj B χ₀ ∈ U) :
    ∃ φ : OpenPartialHomeomorph (AlgSpec B) ℂ, χ₀ ∈ φ.source ∧ proj B = φ := by
  classical
  -- the target part of the root locus, as an open subset of the locus
  set T : Set (ℂ × ℂ) := {z : ℂ × ℂ | z ∈ BiRootLocus p ∧ z.1 ∈ U} with hT
  have hbij := bijOn_toPlane hp hmonic hgen hsep hcard
  -- the inverse of the chart
  set Ψ : ℂ × ℂ → AlgSpec B := fun z => if h : z ∈ T then (hbij.2.2 h).choose else χ₀ with hΨ
  have hΨmem : ∀ z ∈ T, Ψ z ∈ proj B ⁻¹' U := by
    intro z hz
    simp only [hΨ, dif_pos hz]
    exact (hbij.2.2 hz).choose_spec.1
  have hΨeq : ∀ z ∈ T, toPlane θ (Ψ z) = z := by
    intro z hz
    simp only [hΨ, dif_pos hz]
    exact (hbij.2.2 hz).choose_spec.2
  have hΨcont : ContinuousOn Ψ T :=
    continuousOn_of_toPlane_eq hgen Ψ hΨeq (fun z hz => hΨmem z hz)
  -- the chart of the root locus at the image point
  set Θ : AlgSpec B → BiRootLocus p := fun χ => ⟨toPlane θ χ, toPlane_mem_biRootLocus hp χ⟩ with hΘ
  have hΘcont : Continuous Θ := by
    apply Continuous.subtype_mk
    exact continuous_toPlane θ
  have hprojΘ : ∀ χ : AlgSpec B, biRootProj (Θ χ) = proj B χ := fun χ => rfl
  obtain ⟨ρ, heρ, hρeq⟩ := exists_chart_biRootProj (Θ χ₀) (by
    show (biFibre p (toPlane θ χ₀).1).Separable
    exact hsep _ hχ₀)
  -- membership of the inverse image in the root-locus part above U
  have hsymm_mem : ∀ s ∈ ρ.target ∩ U, ((ρ.symm s : BiRootLocus p) : ℂ × ℂ) ∈ T := by
    rintro s ⟨hs, hsU⟩
    refine ⟨(ρ.symm s).2, ?_⟩
    have h1 : biRootProj (ρ.symm s) = s := by
      rw [hρeq]; exact ρ.right_inv hs
    show ((ρ.symm s : BiRootLocus p) : ℂ × ℂ).1 ∈ U
    rw [show ((ρ.symm s : BiRootLocus p) : ℂ × ℂ).1 = biRootProj (ρ.symm s) from rfl, h1]
    exact hsU
  refine ⟨{ toFun := proj B
            invFun := fun s => Ψ ((ρ.symm s : BiRootLocus p) : ℂ × ℂ)
            source := proj B ⁻¹' U ∩ Θ ⁻¹' ρ.source
            target := ρ.target ∩ U
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            continuousOn_toFun := (continuous_proj B).continuousOn
            continuousOn_invFun := ?_
            open_source := (hU.preimage (continuous_proj B)).inter (ρ.open_source.preimage hΘcont)
            open_target := ρ.open_target.inter hU }, ⟨hχ₀, heρ⟩, rfl⟩
  · rintro χ ⟨hχU, hχρ⟩
    refine ⟨?_, hχU⟩
    rw [← hprojΘ χ, hρeq]
    exact ρ.map_source hχρ
  · rintro s hs
    have hmem := hsymm_mem s hs
    refine ⟨?_, ?_⟩
    · have h := hΨmem _ hmem
      exact h
    · show Θ (Ψ ((ρ.symm s : BiRootLocus p) : ℂ × ℂ)) ∈ ρ.source
      have h : Θ (Ψ ((ρ.symm s : BiRootLocus p) : ℂ × ℂ)) = ρ.symm s := by
        apply Subtype.ext
        exact hΨeq _ hmem
      rw [h]
      exact ρ.map_target hs.1
  · rintro χ ⟨hχU, hχρ⟩
    have h1 : ρ.symm (proj B χ) = Θ χ := by
      rw [← hprojΘ χ, hρeq]
      exact ρ.left_inv hχρ
    rw [h1]
    have h2 : Ψ (toPlane θ χ) = χ := by
      have hbij2 := bijOn_toPlane hp hmonic hgen hsep hcard
      have hmemT : toPlane θ χ ∈ T := ⟨toPlane_mem_biRootLocus hp χ, hχU⟩
      refine hbij2.2.1 (hΨmem _ hmemT) hχU ?_
      exact hΨeq _ hmemT
    exact h2
  · rintro s hs
    have hmem := hsymm_mem s hs
    have h := hΨeq _ hmem
    show proj B (Ψ ((ρ.symm s : BiRootLocus p) : ℂ × ℂ)) = s
    have h2 : (toPlane θ (Ψ ((ρ.symm s : BiRootLocus p) : ℂ × ℂ))).1 =
        ((ρ.symm s : BiRootLocus p) : ℂ × ℂ).1 := by rw [h]
    have h3 : biRootProj (ρ.symm s) = s := by rw [hρeq]; exact ρ.right_inv hs.1
    exact h2.trans h3
  · refine ContinuousOn.comp hΨcont ?_ (fun s hs => hsymm_mem s hs)
    exact (continuous_subtype_val.comp_continuousOn
      (ρ.continuousOn_symm.mono Set.inter_subset_left))

/-- **The projection is a local homeomorphism** as soon as every complex point admits a chart. -/
theorem isLocalHomeomorph_proj
    (hchart : ∀ χ₀ : AlgSpec B, ∃ (θ : B) (p : ℂ[X][X]) (U : Set ℂ),
      Polynomial.aeval θ p = 0 ∧ p.Monic ∧ IsOpen U ∧ proj B χ₀ ∈ U ∧
      (∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
        (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q) ∧
      (∀ s ∈ U, (biFibre p s).Separable) ∧
      (∀ s ∈ U, {χ : AlgSpec B | proj B χ = s}.ncard = p.natDegree)) :
    IsLocalHomeomorph (proj B) := by
  intro χ₀
  obtain ⟨θ, p, U, hp, hmonic, hU, hχ₀, hgen, hsep, hcard⟩ := hchart χ₀
  exact isLocalHomeomorph_proj_of_chart hp hmonic hU hgen hsep hcard χ₀ hχ₀

/-- **The projection is a covering map.** -/
theorem isCoveringMap_proj [Module.Finite ℂ[X] B]
    (hchart : ∀ χ₀ : AlgSpec B, ∃ (θ : B) (p : ℂ[X][X]) (U : Set ℂ),
      Polynomial.aeval θ p = 0 ∧ p.Monic ∧ IsOpen U ∧ proj B χ₀ ∈ U ∧
      (∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
        (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q) ∧
      (∀ s ∈ U, (biFibre p s).Separable) ∧
      (∀ s ∈ U, {χ : AlgSpec B | proj B χ = s}.ncard = p.natDegree)) :
    IsCoveringMap (proj B) :=
  isCoveringMap_of_isProperMap_of_isLocalHomeomorph (isLocalHomeomorph_proj hchart)
    isProperMap_proj

end AlgSpec


end

end GaloisForLFunctions.HTGeometry
