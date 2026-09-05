import Mathlib

/-!
# Fourier certificates for canonical faces from arXiv:2608.29060

Equally spaced tower phases are controlled by discrete Fourier inversion. This module proves a
coordinate-free exposed-face reduction and the affine independence of the complete nonzero
`ZMod` character table. A linear-coordinate transfer theorem lets concrete real trigonometric
towers reuse the Fourier certificate after their sine/cosine coordinate map is identified.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Generators attaining a linear support level. -/
def bellmanShorelineLinearExposedSlice
    (K : Set W) (l : W →ₗ[ℝ] ℝ) (c : ℝ) : Set W :=
  {x | x ∈ K ∧ l x = c}

/-- Every convex-hull contact at maximal linear level lies in convex hull of maximizing generators. -/
theorem bellmanShoreline_convexHull_contact_mem_faceHull
    {K : Set W} {x : W} {l : W →ₗ[ℝ] ℝ} {c : ℝ}
    (hx : x ∈ convexHull ℝ K) (hsupport : ∀ y ∈ K, l y ≤ c)
    (hcontact : l x = c) :
    x ∈ convexHull ℝ (bellmanShorelineLinearExposedSlice K l c) := by
  obtain ⟨ι, hιfin, z, w, hzrange, hindep, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  classical
  have hsumzero : ∑ i, w i * (l (z i) - c) = 0 := by
    calc
      ∑ i, w i * (l (z i) - c) =
          l (∑ i, w i • z i) - (∑ i, w i) * c := by
            simp_rw [map_sum, map_smul, smul_eq_mul, mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = 0 := by rw [hwz, hwsum, hcontact]; ring
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), w i * (l (z i) - c) ≤ 0 := by
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hwpos i).le
      (sub_nonpos.mpr (hsupport (z i) (hzrange ⟨i, rfl⟩)))
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsumzero
  have hface : ∀ i, z i ∈ bellmanShorelineLinearExposedSlice K l c := by
    intro i
    refine ⟨hzrange ⟨i, rfl⟩, ?_⟩
    have hi := hall i (Finset.mem_univ i)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hwpos i)))
  rw [← hwz]
  exact (convex_convexHull ℝ _).sum_mem
    (fun i _ => (hwpos i).le) hwsum
    (fun i _ => subset_convexHull ℝ _ (hface i))

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- If samples are exactly generator-level maximizers, their hull is full exposed set. -/
theorem bellmanShoreline_toExposed_convexHull_eq_sampleHull
    {I : Type*} [Nonempty I] (p : I → Y) {K : Set Y}
    (l : StrongDual ℝ Y) (c : ℝ)
    (hsupport : ∀ y ∈ K, l y ≤ c)
    (hsample : Set.range p =
      bellmanShorelineLinearExposedSlice K l.toLinearMap c) :
    l.toExposed (convexHull ℝ K) = convexHull ℝ (Set.range p) := by
  have hpface : ∀ i, p i ∈ bellmanShorelineLinearExposedSlice K l.toLinearMap c := by
    intro i
    rw [← hsample]
    exact Set.mem_range_self i
  have hpK : Set.range p ⊆ K := by
    rintro _ ⟨i, rfl⟩
    exact (hpface i).1
  have hsupportHull : convexHull ℝ K ⊆ {y | l y ≤ c} :=
    convexHull_min hsupport (convex_halfSpace_le l.toLinearMap.isLinear _)
  have hsampleLevel : convexHull ℝ (Set.range p) ⊆ {y | l y = c} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact (hpface i).2
    · exact convex_hyperplane l.toLinearMap.isLinear _
  ext x
  constructor
  · rintro ⟨hxK, hxmax⟩
    let i0 : I := Classical.choice ‹Nonempty I›
    have hc_le : c ≤ l x := by
      rw [← (hpface i0).2]
      exact hxmax (p i0) (subset_convexHull ℝ K (hpK (Set.mem_range_self i0)))
    have hxcontact : l x = c := le_antisymm (hsupportHull hxK) hc_le
    have hxface := bellmanShoreline_convexHull_contact_mem_faceHull
      hxK hsupport hxcontact
    rwa [hsample]
  · intro hx
    refine ⟨convexHull_mono hpK hx, ?_⟩
    intro y hy
    rw [hsampleLevel hx]
    exact hsupportHull hy

/-- Exact maximizing samples span an exposed face of ambient generator hull. -/
theorem bellmanShoreline_sampleHull_isExposed
    {I : Type*} [Nonempty I] (p : I → Y) {K : Set Y}
    (l : StrongDual ℝ Y) (c : ℝ)
    (hsupport : ∀ y ∈ K, l y ≤ c)
    (hsample : Set.range p =
      bellmanShorelineLinearExposedSlice K l.toLinearMap c) :
    IsExposed ℝ (convexHull ℝ K) (convexHull ℝ (Set.range p)) := by
  rw [← bellmanShoreline_toExposed_convexHull_eq_sampleHull p l c hsupport hsample]
  exact ContinuousLinearMap.toExposed.isExposed

variable (N : ℕ) [NeZero N]

/-- Vector of all nonzero additive characters at phase `j`. -/
def bellmanShorelineFourierFeature (j : ZMod N) :
    {k : ZMod N // k ≠ 0} → ℂ :=
  fun k => ZMod.stdAddChar (-(j * k.1))

/-- Complete nonzero Fourier character vectors form affine simplex with `N` vertices. -/
theorem bellmanShorelineFourierFeature_affineIndependent :
    AffineIndependent ℂ (bellmanShorelineFourierFeature N) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hweighted i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hweighted
  have hdft : ZMod.dft w = 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simpa [ZMod.dft_apply] using hw
    · have hcoord := congrFun hweighted (⟨k, hk⟩ : {q : ZMod N // q ≠ 0})
      simpa [ZMod.dft_apply, bellmanShorelineFourierFeature, mul_comm] using hcoord
  have hwzero : w = 0 := ZMod.dft.injective (by simpa using hdft)
  exact congrFun hwzero i

/-- Fourier certificate has exact affine dimension `N - 1`: its vector-span dimension plus one
is the number of canonical phase samples. -/
theorem bellmanShorelineFourierFeature_finrank_add_one :
    Module.finrank ℂ
        (vectorSpan ℂ (Set.range (bellmanShorelineFourierFeature N))) + 1 = N := by
  simpa using
    (bellmanShorelineFourierFeature_affineIndependent N).finrank_vectorSpan_add_one

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A concrete family is affinely independent if a linear coordinate map recovers Fourier feature. -/
theorem bellmanShoreline_affineIndependent_of_fourier_coordinates
    (p : ZMod N → V)
    (T : V →ₗ[ℂ] ({k : ZMod N // k ≠ 0} → ℂ))
    (hT : ∀ j, T (p j) = bellmanShorelineFourierFeature N j) :
    AffineIndependent ℂ p := by
  rw [_root_.affineIndependent_iff]
  intro s w hsum hp j hj
  have hfeature :
      ∑ i ∈ s, w i • bellmanShorelineFourierFeature N i = 0 := by
    calc
      ∑ i ∈ s, w i • bellmanShorelineFourierFeature N i =
          ∑ i ∈ s, w i • T (p i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hT]
      _ = T (∑ i ∈ s, w i • p i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
      _ = 0 := by rw [hp, map_zero]
  exact (bellmanShorelineFourierFeature_affineIndependent N).eq_zero_of_sum_eq_zero
    hsum hfeature j hj

end GaloisForLFunctions.HTGeometry

end
