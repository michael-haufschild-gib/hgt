import GaloisForLFunctions.HTGeometry.AlgebraSpectrumTopology

/-!
# The fibre of the complex-point space over a parameter

Where a chosen element generates the algebra and the monic relation it satisfies specialises to a
separable polynomial, the value map carries the fibre of the projection bijectively onto the root
set.  This is the fibrewise half of the even-covering property for the general (non-monogenic)
simple connectedness of the affine line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- A separable monic polynomial over `ℂ` has exactly `natDegree` roots. -/
theorem card_setOf_isRoot (q : ℂ[X]) (hq : q.Monic) (hsep : q.Separable) :
    Nat.card {t : ℂ | q.eval t = 0} = q.natDegree := by
  classical
  have hne : q ≠ 0 := hq.ne_zero
  have hset : {t : ℂ | q.eval t = 0} = (q.roots.toFinset : Set ℂ) := by
    ext t
    simp [Polynomial.mem_roots hne, Polynomial.IsRoot]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
  exact ((IsAlgClosed.splits q).natDegree_eq_card_roots).symm

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- Over a parameter where a chosen generator satisfies a monic relation, the value map sends the
fibre of `proj` into the roots of the specialised relation. -/
theorem mapsTo_eval_fibre {θ : B} {p : ℂ[X][X]} (hp : Polynomial.aeval θ p = 0) (s : ℂ) :
    Set.MapsTo (fun χ : AlgSpec B => χ θ) {χ | AlgSpec.proj B χ = s}
      {t : ℂ | (biFibre p s).eval t = 0} := by
  intro χ hχ
  have h := AlgSpec.toPlane_mem_biRootLocus hp χ
  have h0 : biEval p (AlgSpec.toPlane θ χ) = 0 := h
  rw [biEval_eq_eval_biFibre] at h0
  show (biFibre p s).eval (χ θ) = 0
  have hs : AlgSpec.proj B χ = s := hχ
  simpa [AlgSpec.toPlane, hs] using h0

/-- **The fibre bijection.**  Where the chosen element generates, where the specialised relation is
separable, and where the fibre has the expected cardinality, the value map is a bijection onto the
roots. -/
theorem bijOn_eval_fibre {θ : B} {p : ℂ[X][X]} (hp : Polynomial.aeval θ p = 0)
    (hmonic : p.Monic) {U : Set ℂ}
    (hgen : ∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
      (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q)
    {s : ℂ} (hs : s ∈ U) (hsep : (biFibre p s).Separable)
    (hcard : {χ : AlgSpec B | AlgSpec.proj B χ = s}.ncard = p.natDegree) :
    Set.BijOn (fun χ : AlgSpec B => χ θ) {χ | AlgSpec.proj B χ = s}
      {t : ℂ | (biFibre p s).eval t = 0} := by
  classical
  have hmaps := mapsTo_eval_fibre (B := B) hp s
  have hinj : Set.InjOn (fun χ : AlgSpec B => χ θ) {χ | AlgSpec.proj B χ = s} := by
    intro χ hχ ψ hψ hEq
    refine AlgSpec.toPlane_injOn hgen (x₁ := χ) (x₂ := ψ) ?_ ?_ ?_
    · show AlgSpec.proj B χ ∈ U
      rw [show AlgSpec.proj B χ = s from hχ]; exact hs
    · show AlgSpec.proj B ψ ∈ U
      rw [show AlgSpec.proj B ψ = s from hψ]; exact hs
    · exact Prod.ext ((show AlgSpec.proj B χ = s from hχ).trans
        (show AlgSpec.proj B ψ = s from hψ).symm) hEq
  have hcardT : {t : ℂ | (biFibre p s).eval t = 0}.ncard = p.natDegree := by
    have h := card_setOf_isRoot (biFibre p s) (biFibre_monic hmonic s) hsep
    rw [biFibre_natDegree hmonic] at h
    rwa [← Nat.card_coe_set_eq]
  have hfinT : {t : ℂ | (biFibre p s).eval t = 0}.Finite := by
    have hne : biFibre p s ≠ 0 := (biFibre_monic hmonic s).ne_zero
    have : {t : ℂ | (biFibre p s).eval t = 0} = ((biFibre p s).roots.toFinset : Set ℂ) := by
      ext t
      simp [Polynomial.mem_roots hne, Polynomial.IsRoot]
    rw [this]
    exact (Finset.finite_toSet _)
  refine ⟨hmaps, hinj, ?_⟩
  have hsub : (fun χ : AlgSpec B => χ θ) '' {χ | AlgSpec.proj B χ = s} ⊆
      {t : ℂ | (biFibre p s).eval t = 0} := Set.image_subset_iff.mpr hmaps
  have hcardImg : ((fun χ : AlgSpec B => χ θ) '' {χ | AlgSpec.proj B χ = s}).ncard = p.natDegree := by
    rw [Set.InjOn.ncard_image hinj, hcard]
  have : (fun χ : AlgSpec B => χ θ) '' {χ | AlgSpec.proj B χ = s} =
      {t : ℂ | (biFibre p s).eval t = 0} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcardT, hcardImg]) hfinT
  rw [Set.SurjOn, ← this]

end

end GaloisForLFunctions.HTGeometry
