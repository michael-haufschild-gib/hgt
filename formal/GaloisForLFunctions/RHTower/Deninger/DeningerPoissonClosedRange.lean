import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonStrict
import GaloisForLFunctions.HTGeometry.SchwartzComplete

/-!
# The Poisson operator has closed range

Meyer's space is a closed subspace of the complete space `𝓢(ℝ, ℂ)`, hence complete.  A sequence in
the image of the Poisson operator whose radial data converge is, by the strictness bounds, a Cauchy
sequence in Meyer's space; its limit lies in Meyer's space and its Poisson sum is the limit of the
radial data.  So the image is sequentially closed, hence closed.

With `deningerPoissonLM_bound`, `deningerPoissonLM_injective` and `deningerPoissonLM_strict` this
completes statement (3): `Z : ℋ_∩ → ℋ_−` is a strict closed embedding.

* `deningerPoissonSchwartz_sub` : the weights are linear in the function.
* `deningerPoisson_range_isClosed` : **the image of the Poisson operator is closed.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff Topology
open Filter Complex GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Linearity of the weights -/

theorem deningerPoissonSchwartz_sub (s : ℤ) {f g : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap)
    (hg : g ∈ DeningerMeyerCap) :
    deningerPoissonSchwartz s (f - g) (Submodule.sub_mem _ hf hg)
      = deningerPoissonSchwartz s f hf - deningerPoissonSchwartz s g hg := by
  refine SchwartzMap.ext fun t => ?_
  show deningerPoissonWeight s (f - g) t
      = deningerPoissonWeight s f t - deningerPoissonWeight s g t
  have hsub : f - g = f + (-1 : ℂ) • g := by
    rw [neg_one_smul]
    abel
  rw [hsub, deningerPoissonWeight_add, deningerPoissonWeight_smul]
  ring

/-! ## Meyer's space is complete -/

instance instCompleteSpaceDeningerMeyerCap : CompleteSpace DeningerMeyerCap := by
  have hcl : IsClosed (DeningerMeyerCap : Set 𝓢(ℝ, ℂ)) := deningerMeyerCap_isClosed
  exact hcl.isComplete.completeSpace_coe

/-! ## The image is closed -/

/-- **The image of the Poisson operator is closed in the radial space.** -/
theorem deningerPoisson_range_isClosed :
    IsClosed (Set.range (deningerPoissonLM : DeningerMeyerCap →ₗ[ℂ] deningerRadialCompat)) := by
  classical
  refine IsSeqClosed.isClosed fun g G hg hG => ?_
  choose f hf using hg
  -- the components of the sequence converge
  have hGcoe : Tendsto (fun i => ((g i : deningerRadialCompat) : ∀ _ : ℤ, 𝓢(ℝ, ℂ))) atTop
      (𝓝 ((G : deningerRadialCompat) : ∀ _ : ℤ, 𝓢(ℝ, ℂ))) :=
    (continuous_subtype_val.tendsto _).comp hG
  have hcomp : ∀ s : ℤ,
      Tendsto (fun i => deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ))) (f i).2) atTop
        (𝓝 (((G : deningerRadialCompat) : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s)) := by
    intro s
    have h := (tendsto_pi_nhds.mp hGcoe) s
    refine h.congr fun i => ?_
    rw [← hf i]
    rfl
  have hcompCauchy : ∀ s : ℤ,
      CauchySeq (fun i => deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ))) (f i).2) :=
    fun s => (hcomp s).cauchySeq
  -- the preimages form a Cauchy sequence
  have hcauchy : CauchySeq (fun i => ((f i : 𝓢(ℝ, ℂ)))) := by
    refine cauchySeq_of_seminorm fun k n ε hε => ?_
    obtain ⟨S, K, C, hC, hb⟩ := exists_bound_seminorm_radial k n
    set δ : ℝ := ε / (C * (S.card : ℝ) + 1) with hδ
    have hden : (0 : ℝ) < C * (S.card : ℝ) + 1 := by positivity
    have hδpos : 0 < δ := by
      rw [hδ]
      positivity
    choose N hN using fun s : ℤ => exists_schwartzSup_lt_of_cauchySeq (hcompCauchy s) K hδpos
    refine ⟨S.sup N, fun m hm l hl => ?_⟩
    have hmemsub : ((f m : 𝓢(ℝ, ℂ)) - (f l : 𝓢(ℝ, ℂ))) ∈ DeningerMeyerCap :=
      Submodule.sub_mem _ (f m).2 (f l).2
    have hdata : deningerRadialData S K ((f m : 𝓢(ℝ, ℂ)) - (f l : 𝓢(ℝ, ℂ))) hmemsub
        ≤ (S.card : ℝ) * δ := by
      rw [deningerRadialData]
      have hterm : ∀ s ∈ S, (K.sup (schwartzSeminormFamily ℂ ℝ ℂ))
          (deningerPoissonSchwartz s ((f m : 𝓢(ℝ, ℂ)) - (f l : 𝓢(ℝ, ℂ))) hmemsub) ≤ δ := by
        intro s hs
        have hle : N s ≤ S.sup N := Finset.le_sup hs
        have hlt := hN s m (le_trans hle hm) l (le_trans hle hl)
        have hsub : deningerPoissonSchwartz s ((f m : 𝓢(ℝ, ℂ)) - (f l : 𝓢(ℝ, ℂ))) hmemsub
            = deningerPoissonSchwartz s ((f m : 𝓢(ℝ, ℂ))) (f m).2
              - deningerPoissonSchwartz s ((f l : 𝓢(ℝ, ℂ))) (f l).2 :=
          deningerPoissonSchwartz_sub s (f m).2 (f l).2
        rw [hsub]
        exact hlt.le
      calc (∑ s ∈ S, (K.sup (schwartzSeminormFamily ℂ ℝ ℂ))
            (deningerPoissonSchwartz s ((f m : 𝓢(ℝ, ℂ)) - (f l : 𝓢(ℝ, ℂ))) hmemsub))
          ≤ ∑ _s ∈ S, δ := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * δ := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hfinal : SchwartzMap.seminorm ℂ k n ((f m : 𝓢(ℝ, ℂ)) - (f l : 𝓢(ℝ, ℂ)))
        ≤ C * ((S.card : ℝ) * δ) := by
      refine le_trans (hb _ hmemsub) (mul_le_mul_of_nonneg_left hdata hC)
    have hlt : C * ((S.card : ℝ) * δ) < ε := by
      rw [hδ]
      rw [div_eq_inv_mul, ← mul_assoc, ← mul_assoc]
      rw [mul_comm (C * (S.card : ℝ)) ((C * (S.card : ℝ) + 1)⁻¹)]
      rw [mul_assoc]
      have hfrac : (C * (S.card : ℝ) + 1)⁻¹ * (C * (S.card : ℝ)) < 1 := by
        rw [inv_mul_lt_one₀ hden]
        linarith
      have hpos : (0 : ℝ) < ε := hε
      nlinarith [hfrac, hpos]
    exact lt_of_le_of_lt hfinal hlt
  -- the limit lies in Meyer's space
  set F : 𝓢(ℝ, ℂ) := schwartzCauchyLimit hcauchy with hF
  have hFtend : Tendsto (fun i => ((f i : 𝓢(ℝ, ℂ)))) atTop (𝓝 F) :=
    tendsto_schwartzCauchyLimit hcauchy
  have hFmem : F ∈ DeningerMeyerCap :=
    deningerMeyerCap_isClosed.mem_of_tendsto hFtend (Filter.Eventually.of_forall fun i => (f i).2)
  -- the Poisson sums converge to the Poisson sum of the limit
  have hZtend : ∀ s : ℤ,
      Tendsto (fun i => deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ))) (f i).2) atTop
        (𝓝 (deningerPoissonSchwartz s F hFmem)) := by
    intro s
    rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds_atTop]
    rintro ⟨k, n⟩ ε hε
    obtain ⟨K₀, C₀, hC₀, hb₀⟩ := exists_bound_seminorm_deningerPoissonSchwartz s k n
    set δ : ℝ := ε / (C₀ + 1) with hδ
    have hden : (0 : ℝ) < C₀ + 1 := by positivity
    have hδpos : 0 < δ := by
      rw [hδ]
      positivity
    have hev := (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds' _ F |>.mp hFtend K₀ δ hδpos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun i hi => ?_⟩
    have hmemsub : ((f i : 𝓢(ℝ, ℂ)) - F) ∈ DeningerMeyerCap :=
      Submodule.sub_mem _ (f i).2 hFmem
    have hsub : deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ)) - F) hmemsub
        = deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ))) (f i).2
          - deningerPoissonSchwartz s F hFmem :=
      deningerPoissonSchwartz_sub s (f i).2 hFmem
    have hfam : (schwartzSeminormFamily ℂ ℝ ℂ (k, n))
        (deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ))) (f i).2
          - deningerPoissonSchwartz s F hFmem)
        = SchwartzMap.seminorm ℂ k n (deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ))) (f i).2
          - deningerPoissonSchwartz s F hFmem) := rfl
    rw [hfam, ← hsub]
    have hbound := hb₀ ((f i : 𝓢(ℝ, ℂ)) - F) hmemsub
    have hsmall := hN i hi
    have hnn : 0 ≤ (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ((f i : 𝓢(ℝ, ℂ)) - F) :=
      apply_nonneg _ _
    have hstep : SchwartzMap.seminorm ℂ k n
        (deningerPoissonSchwartz s ((f i : 𝓢(ℝ, ℂ)) - F) hmemsub) ≤ C₀ * δ := by
      refine le_trans hbound ?_
      exact mul_le_mul_of_nonneg_left hsmall.le hC₀
    have hlt : C₀ * δ < ε := by
      rw [hδ, mul_div_assoc']
      rw [div_lt_iff₀ hden]
      nlinarith
    exact lt_of_le_of_lt hstep hlt
  -- the limit of the radial data is the radial datum of the limit
  have hGval : ((G : deningerRadialCompat) : ∀ _ : ℤ, 𝓢(ℝ, ℂ))
      = deningerPoissonFamily F hFmem := by
    funext s
    exact tendsto_nhds_unique (hcomp s) (hZtend s)
  exact ⟨⟨F, hFmem⟩, Subtype.ext hGval.symm⟩

end RHTower

end
