import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

open Module Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

theorem compactPerturbation_one_surjective_of_injective
    (C : X →L[ℂ] X) (hC : IsCompactOperator C)
    (hinj : Function.Injective (1 + C : X →L[ℂ] X)) :
    Function.Surjective (1 + C : X →L[ℂ] X) := by
  have hneg : IsCompactOperator (-C) := hC.neg
  rcases hneg.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℂ)) one_ne_zero with heig | hres
  · obtain ⟨x, hx⟩ := heig.exists_hasUnifEigenvector
    exfalso
    apply hx.2
    apply hinj
    have happ := hx.apply_eq_smul
    have happ' : -C x = x := by simpa using happ
    simp only [map_zero, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
    calc
      x + C x = -C x + C x := by rw [happ']
      _ = 0 := neg_add_cancel (C x)
  · rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
    have hunit : IsUnit (1 + C : X →L[ℂ] X) := by simpa using hres
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2

theorem compactPerturbation_one_adjoint_kernel_le_span
    (C : X →L[ℂ] X) (hC : IsCompactOperator C)
    (x y : X) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxker : LinearMap.ker (1 + C : X →L[ℂ] X).toLinearMap ≤ ℂ ∙ x)
    (hyker : (1 + C : X →L[ℂ] X).adjoint y = 0) :
    LinearMap.ker (1 + C : X →L[ℂ] X).adjoint.toLinearMap ≤ ℂ ∙ y := by
  let R : X →L[ℂ] X := InnerProductSpace.rankOne ℂ y x
  have hR_apply (z : X) : R z = inner ℂ x z • y := rfl
  have hR : IsCompactOperator R := by
    simp only [R, InnerProductSpace.rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ x)).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ y)
  let T : X →L[ℂ] X := (1 + C) + R
  have hTcompact : IsCompactOperator (C + R : X →L[ℂ] X) := hC.add hR
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hpair : inner ℂ x z * inner ℂ y y = 0 := by
      have hzero : inner ℂ y (T z) = 0 := by rw [hz, inner_zero_right]
      have hSzero : inner ℂ y ((1 + C : X →L[ℂ] X) z) = 0 := by
        rw [← (1 + C : X →L[ℂ] X).adjoint_inner_left z y, hyker, inner_zero_left]
      change inner ℂ y ((1 + C : X →L[ℂ] X) z + R z) = 0 at hzero
      rw [inner_add_right, hSzero, zero_add, hR_apply,
        inner_smul_right] at hzero
      exact hzero
    have hinner : inner ℂ x z = 0 :=
      (mul_eq_zero.mp hpair).resolve_right (inner_self_ne_zero.mpr hy0)
    have hSz : (1 + C : X →L[ℂ] X) z = 0 := by
      have hz' := hz
      change (1 + C : X →L[ℂ] X) z + R z = 0 at hz'
      rw [hR_apply, hinner, zero_smul, add_zero] at hz'
      exact hz'
    have hzspan : z ∈ ℂ ∙ x := hxker (by simpa [LinearMap.mem_ker] using hSz)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzspan
    have hc0 : c = 0 := by
      have : c * inner ℂ x x = 0 := by
        rw [← inner_smul_right]
        simpa [hc] using hinner
      exact (mul_eq_zero.mp this).resolve_right (inner_self_ne_zero.mpr hx0)
    rw [← hc, hc0, zero_smul]
  have hTsurj : Function.Surjective T := by
    have hTinj' : Function.Injective (1 + (C + R) : X →L[ℂ] X) := by
      simpa only [T, add_assoc] using hTinj
    have hsurj' := compactPerturbation_one_surjective_of_injective
      (C + R) hTcompact hTinj'
    simpa only [T, add_assoc] using hsurj'
  intro w hw
  have hwker : (1 + C : X →L[ℂ] X).adjoint w = 0 :=
    LinearMap.mem_ker.mp hw
  let c : ℂ := inner ℂ y w / inner ℂ y y
  let w0 : X := w - c • y
  have hw0ker : (1 + C : X →L[ℂ] X).adjoint w0 = 0 := by
    simp only [w0, map_sub, map_smul, hwker, hyker, smul_zero, sub_zero]
  have hw0orth : inner ℂ w0 y = 0 := by
    have hforward : inner ℂ y w0 = 0 := by
      change inner ℂ y (w - c • y) = 0
      rw [inner_sub_right, inner_smul_right]
      dsimp only [c]
      rw [div_mul_cancel₀ _ (inner_self_ne_zero.mpr hy0), sub_self]
    rw [← inner_conj_symm, hforward, map_zero]
  have hw0 : w0 = 0 := by
    obtain ⟨z, hz⟩ := hTsurj w0
    have hinner : inner ℂ w0 (T z) = 0 := by
      change inner ℂ w0 ((1 + C : X →L[ℂ] X) z + R z) = 0
      rw [inner_add_right]
      have hS : inner ℂ w0 ((1 + C : X →L[ℂ] X) z) = 0 := by
        rw [← (1 + C : X →L[ℂ] X).adjoint_inner_left z w0,
          hw0ker, inner_zero_left]
      rw [hS, zero_add, hR_apply, inner_smul_right, hw0orth,
        mul_zero]
    rw [hz] at hinner
    exact (inner_self_eq_zero.mp hinner)
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  exact (sub_eq_zero.mp hw0).symm

theorem compact_hyperplane_perturbation_range_eq_orthogonal
    (K : Submodule ℂ X) (hK : IsClosed (K : Set X))
    (p : X) (_hp0hp0 : p ≠ 0) (hKorth : Kᗮ = ℂ ∙ p)
    (C : K →L[ℂ] X) (hC : IsCompactOperator C)
    (hJinj : Function.Injective (K.subtypeL + C))
    (hJclosed : IsClosed ((K.subtypeL + C).range : Set X))
    (g : X) (hg0 : g ≠ 0)
    (hgorth : g ∈ (LinearMap.range (K.subtypeL + C).toLinearMap)ᗮ) :
    LinearMap.range (K.subtypeL + C).toLinearMap = (ℂ ∙ g)ᗮ := by
  letI : CompleteSpace K := hK.completeSpace_coe
  let J : K →L[ℂ] X := K.subtypeL + C
  let P : X →L[ℂ] K := K.orthogonalProjectionOnto
  let C0 : K →L[ℂ] K := P ∘L C
  let S : K →L[ℂ] K := 1 + C0
  have hC0 : IsCompactOperator C0 := hC.clm_comp P
  have hS_apply (x : K) : S x = P (J x) := by
    apply Subtype.ext
    simp [S, C0, P, J, K.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hK_eq : K = (ℂ ∙ p)ᗮ := by
    calc
      K = Kᗮᗮ := K.orthogonal_orthogonal.symm
      _ = (ℂ ∙ p)ᗮ := by rw [hKorth]
  have horth_le :
      (LinearMap.range J.toLinearMap)ᗮ ≤ ℂ ∙ g := by
    by_cases hSinj : Function.Injective S
    · have hSsurj : Function.Surjective S := by
        have hsurj := compactPerturbation_one_surjective_of_injective C0 hC0
        simpa only [S] using hsurj hSinj
      have centered_orth_eq_zero {y : X} (hyK : y ∈ K)
          (hyorth : y ∈ (LinearMap.range J.toLinearMap)ᗮ) : y = 0 := by
        let yK : K := ⟨y, hyK⟩
        obtain ⟨x, hx⟩ := hSsurj yK
        have hyann : inner ℂ y (J x) = 0 := by
          rw [Submodule.mem_orthogonal'] at hyorth
          exact hyorth (J x) ⟨x, rfl⟩
        have hself : inner ℂ y y = 0 := by
          calc
            inner ℂ y y = inner ℂ yK yK := K.coe_inner yK yK
            _ = inner ℂ yK (S x) := by rw [hx]
            _ = inner ℂ yK (P (J x)) := by rw [hS_apply]
            _ = inner ℂ y (J x) := K.inner_orthogonalProjectionOnto_eq_of_mem_left yK (J x)
            _ = 0 := hyann
        exact inner_self_eq_zero.mp hself
      have hg_not_K : g ∉ K := fun hgK => hg0 (centered_orth_eq_zero hgK hgorth)
      have hpg : inner ℂ p g ≠ 0 := by
        intro hzero
        apply hg_not_K
        rw [hK_eq, Submodule.mem_orthogonal_singleton_iff_inner_left]
        calc
          inner ℂ g p = (starRingEnd ℂ) (inner ℂ p g) := (inner_conj_symm g p).symm
          _ = 0 := by rw [hzero, map_zero]
      intro y hyorth
      let c : ℂ := inner ℂ p y / inner ℂ p g
      let w : X := y - c • g
      have hwK : w ∈ K := by
        rw [hK_eq, Submodule.mem_orthogonal_singleton_iff_inner_left]
        have hforward : inner ℂ p w = 0 := by
          change inner ℂ p (y - c • g) = 0
          rw [inner_sub_right, inner_smul_right]
          dsimp only [c]
          rw [div_mul_cancel₀ _ hpg, sub_self]
        calc
          inner ℂ w p = (starRingEnd ℂ) (inner ℂ p w) := (inner_conj_symm w p).symm
          _ = 0 := by rw [hforward, map_zero]
      have hworth : w ∈ (LinearMap.range J.toLinearMap)ᗮ :=
        Submodule.sub_mem _ hyorth (Submodule.smul_mem _ c hgorth)
      have hw0 : w = 0 := centered_orth_eq_zero hwK hworth
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      exact (sub_eq_zero.mp hw0).symm
    · rw [Function.Injective] at hSinj
      push_neg at hSinj
      obtain ⟨a, b, hab, hSab⟩ := hSinj
      let x0 : K := a - b
      have hx0 : x0 ≠ 0 := sub_ne_zero.mpr hSab
      have hSx0 : S x0 = 0 := by
        change S (a - b) = 0
        rw [map_sub, hab, sub_self]
      have hJx0 : J x0 ∈ Kᗮ := by
        rw [← K.orthogonalProjectionOnto_eq_zero_iff]
        change P (J x0) = 0
        rw [← hS_apply]
        exact hSx0
      have hJx0_ne : J x0 ≠ 0 := by
        intro hzero
        apply hx0
        apply hJinj
        simpa [J] using hzero
      have hspanJx0 : ℂ ∙ J x0 = Kᗮ := by
        rw [hKorth]
        have hmem : J x0 ∈ ℂ ∙ p := by simpa [hKorth] using hJx0
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
        have hc0 : c ≠ 0 := by
          intro hc0
          apply hJx0_ne
          rw [← hc, hc0, zero_smul]
        symm
        rw [Submodule.span_singleton_eq_span_singleton]
        exact ⟨Units.mk0 c hc0, by simpa using hc⟩
      have orth_mem_K {y : X}
          (hyorth : y ∈ (LinearMap.range J.toLinearMap)ᗮ) : y ∈ K := by
        rw [← K.orthogonal_orthogonal]
        rw [Submodule.mem_orthogonal']
        intro n hn
        have hnspan : n ∈ ℂ ∙ J x0 := by simpa [hspanJx0] using hn
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hnspan
        have hyann : inner ℂ y (J x0) = 0 := by
          rw [Submodule.mem_orthogonal'] at hyorth
          exact hyorth (J x0) ⟨x0, rfl⟩
        calc
          inner ℂ y n = inner ℂ y (c • J x0) := by rw [hc]
          _ = c * inner ℂ y (J x0) := inner_smul_right _ _ _
          _ = 0 := by rw [hyann, mul_zero]
      have hgK : g ∈ K := orth_mem_K hgorth
      let gK : K := ⟨g, hgK⟩
      have hgK0 : gK ≠ 0 := fun h => hg0 (congrArg Subtype.val h)
      have hker_le : LinearMap.ker S.toLinearMap ≤ ℂ ∙ x0 := by
        intro z hz
        have hJz : J z ∈ Kᗮ := by
          rw [← K.orthogonalProjectionOnto_eq_zero_iff]
          change P (J z) = 0
          rw [← hS_apply]
          exact LinearMap.mem_ker.mp hz
        have hJzspan : J z ∈ ℂ ∙ J x0 := by simpa [hspanJx0] using hJz
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hJzspan
        rw [Submodule.mem_span_singleton]
        refine ⟨c, ?_⟩
        have hmap : J (c • x0) = J z := by rw [map_smul, hc]
        exact hJinj hmap
      have hAdj_g : S.adjoint gK = 0 := by
        apply ext_inner_left ℂ
        intro z
        calc
          inner ℂ z (S.adjoint gK) = inner ℂ (S z) gK := S.adjoint_inner_right z gK
          _ = inner ℂ (P (J z)) gK := by rw [hS_apply]
          _ = inner ℂ (J z) g := K.inner_orthogonalProjectionOnto_eq_of_mem_right gK (J z)
          _ = 0 := by
            have hann : inner ℂ g (J z) = 0 := by
              rw [Submodule.mem_orthogonal'] at hgorth
              exact hgorth (J z) ⟨z, rfl⟩
            calc
              inner ℂ (J z) g = (starRingEnd ℂ) (inner ℂ g (J z)) :=
                (inner_conj_symm (J z) g).symm
              _ = 0 := by rw [hann, map_zero]
          _ = inner ℂ z 0 := by simp
      have hAdj_le : LinearMap.ker S.adjoint.toLinearMap ≤ ℂ ∙ gK := by
        have hle := compactPerturbation_one_adjoint_kernel_le_span C0 hC0
          x0 gK hx0 hgK0
        simpa only [S] using hle hker_le hAdj_g
      intro y hyorth
      have hyK : y ∈ K := orth_mem_K hyorth
      let yK : K := ⟨y, hyK⟩
      have hAdj_y : S.adjoint yK = 0 := by
        apply ext_inner_left ℂ
        intro z
        calc
          inner ℂ z (S.adjoint yK) = inner ℂ (S z) yK := S.adjoint_inner_right z yK
          _ = inner ℂ (P (J z)) yK := by rw [hS_apply]
          _ = inner ℂ (J z) y := K.inner_orthogonalProjectionOnto_eq_of_mem_right yK (J z)
          _ = 0 := by
            have hann : inner ℂ y (J z) = 0 := by
              rw [Submodule.mem_orthogonal'] at hyorth
              exact hyorth (J z) ⟨z, rfl⟩
            calc
              inner ℂ (J z) y = (starRingEnd ℂ) (inner ℂ y (J z)) :=
                (inner_conj_symm (J z) y).symm
              _ = 0 := by rw [hann, map_zero]
          _ = inner ℂ z 0 := by simp
      have hySpan : yK ∈ ℂ ∙ gK := hAdj_le (by
        exact LinearMap.mem_ker.mpr hAdj_y)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hySpan
      rw [Submodule.mem_span_singleton]
      exact ⟨c, congrArg Subtype.val hc⟩
  have horth_eq : (LinearMap.range J.toLinearMap)ᗮ = ℂ ∙ g := by
    apply le_antisymm horth_le
    rw [Submodule.span_singleton_le_iff_mem]
    exact hgorth
  change LinearMap.range J.toLinearMap = (ℂ ∙ g)ᗮ
  rw [← horth_eq]
  rw [Submodule.orthogonal_orthogonal_eq_closure]
  exact hJclosed.submodule_topologicalClosure_eq.symm

/-- For every densely defined operator on a Hilbert space, the kernel of its Hilbert-space
adjoint is exactly the orthogonal complement of its range. -/
theorem LinearPMap.adjoint_kernel_eq_orthogonal_range
    (T : X →ₗ.[ℂ] X) (hDense : Dense (T.domain : Set X)) :
    T.adjoint.kernel = T.rangeSubmoduleᗮ := by
  ext y
  rw [LinearPMap.mem_kernel_iff]
  constructor
  · rintro ⟨hyDom, hy0⟩
    rw [Submodule.mem_orthogonal']
    intro k hk
    rcases hk with ⟨x, hx⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint hDense
      (⟨y, hyDom⟩ : T.adjoint.domain) x
    rw [hy0, inner_zero_left] at hformal
    calc
      inner ℂ y k = inner ℂ y (T x) := congrArg (inner ℂ y) hx.symm
      _ = 0 := hformal.symm
  · intro hyOrth
    rw [Submodule.mem_orthogonal'] at hyOrth
    have hyDom : y ∈ T.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨0, ?_⟩
      intro x
      rw [inner_zero_left]
      symm
      exact hyOrth (T x) ⟨x, rfl⟩
    refine ⟨hyDom, ?_⟩
    apply LinearPMap.adjoint_apply_eq hDense
    intro x
    rw [inner_zero_left]
    symm
    exact hyOrth (T x) ⟨x, rfl⟩

end

end GaloisForLFunctions.HTGeometry
