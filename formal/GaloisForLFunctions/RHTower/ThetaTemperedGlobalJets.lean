import GaloisForLFunctions.RHTower.ThetaTemperedLocalCoefficients
import GaloisForLFunctions.RHTower.ThetaTemperedCompactCore

/-!
# Joint original Schwartz criterion for actual Xi jet families

Raw coefficients use the actual Xi multiplicity at every real point. Their
finite compact-test formula defines a complex linear functional on the actual
compact Schwartz core. Exactly one joint original-seminorm bound characterizes
the unique original tempered Xi-kernel extension and its canonical coefficients.
-/

open scoped BigOperators SchwartzMap

namespace RHTower

noncomputable section

theorem thetaXiFiniteJetCombination_mem_lowerJetSpan (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ) :
    thetaXiFiniteJetCombination t a ∈ thetaXiTemperedLowerJetSpan t := by
  apply (thetaXiTemperedLowerJetSpan_mem_iff_existsUniqueCoefficients _ t).mpr
  exact ⟨a, rfl, fun b hb => thetaXiFiniteJetCombination_injective t hb⟩

theorem thetaXiFiniteJetCombination_mem_kernel (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ) :
    thetaXiTemperedMultiplier (thetaXiFiniteJetCombination t a) = 0 := by
  exact LinearMap.mem_ker.mp
    (thetaXiTemperedLowerJetSpan_le_ker t
      (thetaXiFiniteJetCombination_mem_lowerJetSpan t a))

theorem thetaXiFiniteJetCombination_eq_zero_of_symbol_ne_zero (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ) (ht : thetaXiRealSymbol t ≠ 0) :
    thetaXiFiniteJetCombination t a = 0 := by
  have hm : thetaRealXiMultiplicity t = 0 := by
    by_contra hm
    have hp : 0 < thetaRealXiMultiplicity t := by omega
    exact ht ((thetaRealXiMultiplicity_pos_iff t).mp hp)
  rw [thetaXiFiniteJetCombination]
  apply Finset.sum_eq_zero
  intro r _
  have hr := r.isLt
  omega

theorem thetaXiFiniteJetCombination_apply_zero_of_notMem_tsupport (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ) (φ : 𝓢(ℝ, ℂ))
    (ht : t ∉ tsupport (φ : ℝ → ℂ)) : thetaXiFiniteJetCombination t a φ = 0 := by
  rw [thetaXiFiniteJetCombination_apply]
  apply Finset.sum_eq_zero
  intro r _
  have hg : (φ : ℝ → ℂ) =ᶠ[nhds t] (fun _ => (0 : ℂ)) :=
    notMem_tsupport_iff_eventuallyEq.mp ht
  have hd : iteratedDeriv (r : ℕ) (φ : ℝ → ℂ) t = 0 := by
    simpa only [iteratedDeriv_const, ite_self] using hg.iteratedDeriv_eq (r : ℕ)
  rw [hd, mul_zero, mul_zero]

def thetaXiRawCompactJetValue
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) : ℂ :=
  ∑ t ∈ thetaXiCompactTestZeros φ hφ, thetaXiFiniteJetCombination t (a t) φ

theorem thetaXiRawCompactJetValue_eq_sum_of_cover
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ)
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hcover : ∀ t ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W) :
    thetaXiRawCompactJetValue a φ hφ = ∑ t ∈ W, thetaXiFiniteJetCombination t (a t) φ := by
  classical
  apply Finset.sum_subset
  · intro t ht
    obtain ⟨hs, hz⟩ := (thetaXiCompactTestZeros_mem_iff φ hφ t).mp ht
    exact hcover t hs hz
  · intro t _ ht
    by_cases hs : t ∈ tsupport (φ : ℝ → ℂ)
    · have hz : thetaXiRealSymbol t ≠ 0 := by
        intro hz
        exact ht ((thetaXiCompactTestZeros_mem_iff φ hφ t).mpr ⟨hs, hz⟩)
      rw [thetaXiFiniteJetCombination_eq_zero_of_symbol_ne_zero t (a t) hz, zero_apply]
    · exact thetaXiFiniteJetCombination_apply_zero_of_notMem_tsupport t (a t) φ hs

def thetaXiRawCompactJetFunctional
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) : thetaSchwartzCompactCore →ₗ[ℂ] ℂ where
  toFun φ := thetaXiRawCompactJetValue a φ φ.property
  map_add' φ ψ := by
    classical
    let W := thetaXiCompactTestZeros (φ : 𝓢(ℝ, ℂ)) φ.property ∪
      thetaXiCompactTestZeros (ψ : 𝓢(ℝ, ℂ)) ψ.property
    have hcφ : ∀ t ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W := by
      intro t ht hz
      exact Finset.mem_union.mpr (Or.inl
        ((thetaXiCompactTestZeros_mem_iff _ φ.property t).mpr ⟨ht, hz⟩))
    have hcψ : ∀ t ∈ tsupport (ψ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W := by
      intro t ht hz
      exact Finset.mem_union.mpr (Or.inr
        ((thetaXiCompactTestZeros_mem_iff _ ψ.property t).mpr ⟨ht, hz⟩))
    have hc : ∀ t ∈ tsupport ((φ + ψ : thetaSchwartzCompactCore) : ℝ → ℂ),
        thetaXiRealSymbol t = 0 → t ∈ W := by
      intro t ht hz
      rcases tsupport_add (φ : ℝ → ℂ) (ψ : ℝ → ℂ) ht with ht | ht
      · exact hcφ t ht hz
      · exact hcψ t ht hz
    rw [thetaXiRawCompactJetValue_eq_sum_of_cover a W _ _ hc,
      thetaXiRawCompactJetValue_eq_sum_of_cover a W _ _ hcφ,
      thetaXiRawCompactJetValue_eq_sum_of_cover a W _ _ hcψ]
    simp only [Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    classical
    let W := thetaXiCompactTestZeros (φ : 𝓢(ℝ, ℂ)) φ.property
    have hcφ : ∀ t ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W := by
      intro t ht hz
      exact (thetaXiCompactTestZeros_mem_iff _ φ.property t).mpr ⟨ht, hz⟩
    have hc : ∀ t ∈ tsupport ((c • φ : thetaSchwartzCompactCore) : ℝ → ℂ),
        thetaXiRealSymbol t = 0 → t ∈ W := by
      intro t ht hz
      exact hcφ t (tsupport_smul_subset_right (fun _ : ℝ => c) (φ : ℝ → ℂ) ht) hz
    rw [thetaXiRawCompactJetValue_eq_sum_of_cover a W _ _ hc,
      thetaXiRawCompactJetValue_eq_sum_of_cover a W _ _ hcφ]
    simp only [Submodule.coe_smul, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem thetaXiRawCompactJetFunctional_apply
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ)
    (φ : thetaSchwartzCompactCore) :
    thetaXiRawCompactJetFunctional a φ =
      ∑ t ∈ thetaXiCompactTestZeros (φ : 𝓢(ℝ, ℂ)) φ.property,
        ∑ r : Fin (thetaRealXiMultiplicity t),
          a t r * ((-1 : ℂ) ^ (r : ℕ) * iteratedDeriv (r : ℕ) (φ : ℝ → ℂ) t) := by
  change thetaXiRawCompactJetValue a (φ : 𝓢(ℝ, ℂ)) φ.property = _
  simp only [thetaXiRawCompactJetValue, thetaXiFiniteJetCombination_apply]

theorem thetaXiSchwartzProduct_hasCompactSupport (φ : 𝓢(ℝ, ℂ))
    (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    HasCompactSupport (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol φ : ℝ → ℂ) := by
  have heq : (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol φ : ℝ → ℂ) =
      thetaXiRealSymbol * (φ : ℝ → ℂ) := by
    funext x
    exact SchwartzMap.smulLeftCLM_apply_apply thetaXiRealSymbol_hasTemperateGrowth φ x
  rw [heq]
  exact hφ.mul_left

theorem thetaXiRawCompactJetValue_Xi_product_zero
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    thetaXiRawCompactJetValue a (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol φ)
      (thetaXiSchwartzProduct_hasCompactSupport φ hφ) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  have hz := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
    (thetaXiFiniteJetCombination_mem_kernel t (a t))
  simpa only [thetaXiTemperedMultiplier, TemperedDistribution.smulLeftCLM_apply_apply,
    zero_apply] using hz

theorem thetaXiRawCompactJetFunctional_of_tempered
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0)
    (φ : thetaSchwartzCompactCore) :
    thetaXiRawCompactJetFunctional (fun t => thetaXiTemperedLocalCoefficients Q hQ t) φ =
      Q (φ : 𝓢(ℝ, ℂ)) := by
  rw [thetaXiRawCompactJetFunctional_apply]
  exact (thetaXiTemperedKernel_compact_coefficients Q hQ φ φ.property).symm

def thetaXiRawJetJointBound
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) : Prop :=
  thetaSchwartzCompactCoreJointBound (thetaXiRawCompactJetFunctional a)

theorem thetaXiRawCompactJetFunctional_extension_mem_kernel
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) (Q : 𝓢'(ℝ, ℂ))
    (hL : ∀ φ : thetaSchwartzCompactCore, Q (φ : 𝓢(ℝ, ℂ)) = thetaXiRawCompactJetFunctional a φ) :
    thetaXiTemperedMultiplier Q = 0 := by
  apply (thetaTempered_eq_zero_iff_compact _).mpr
  intro φ hφ
  change Q (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol φ) = 0
  let ψ : thetaSchwartzCompactCore := ⟨SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol φ,
    thetaXiSchwartzProduct_hasCompactSupport φ hφ⟩
  change Q (ψ : 𝓢(ℝ, ℂ)) = 0
  rw [hL ψ]
  exact thetaXiRawCompactJetValue_Xi_product_zero a φ hφ

private theorem thetaXiFiniteJetCombination_apply_eq_of_germ_eq (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ) (φ ψ : 𝓢(ℝ, ℂ))
    (heq : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → φ x = ψ x) :
    thetaXiFiniteJetCombination t a φ = thetaXiFiniteJetCombination t a ψ := by
  obtain ⟨δ, hδ, heq⟩ := heq
  have hp := ((thetaTemperedPointSupport_Xi_kernel_iff_lowerJetSpan _ t).mpr
    (thetaXiFiniteJetCombination_mem_lowerJetSpan t a)).1
  have hz := hp (φ - ψ) ⟨δ, hδ, fun x hx => by simp only [sub_apply, heq x hx, sub_self]⟩
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem thetaXiRawCompactJetFunctional_extension_coefficients
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) (Q : 𝓢'(ℝ, ℂ))
    (hL : ∀ φ : thetaSchwartzCompactCore, Q (φ : 𝓢(ℝ, ℂ)) = thetaXiRawCompactJetFunctional a φ)
    (t : ℝ) :
    thetaXiTemperedLocalCoefficients Q
      (thetaXiRawCompactJetFunctional_extension_mem_kernel a Q hL) t = a t := by
  classical
  let χ := thetaXiIsolatingCutoff t
  have hχ : HasCompactSupport (χ : ℝ → ℂ) := thetaXiIsolatingCutoff_hasCompactSupport t
  have hloc : thetaXiTemperedLocalization t Q = thetaXiFiniteJetCombination t (a t) := by
    apply ContinuousLinearMap.ext
    intro ψ
    let φ := SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ
    have hφ := (thetaSchwartz_cutoffProduct_compact_support χ ψ hχ).1
    have hcover : ∀ s ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol s = 0 → s ∈ ({t} : Finset ℝ) := by
      intro s hs hz
      apply Finset.mem_singleton.mpr
      exact thetaXiIsolatingCutoff_isolates_zero t s
        ((thetaSchwartz_cutoffProduct_compact_support χ ψ hχ).2.1 hs) hz
    change Q φ = thetaXiFiniteJetCombination t (a t) ψ
    rw [hL ⟨φ, hφ⟩]
    change thetaXiRawCompactJetValue a φ hφ = thetaXiFiniteJetCombination t (a t) ψ
    rw [thetaXiRawCompactJetValue_eq_sum_of_cover a {t} φ hφ hcover, Finset.sum_singleton]
    apply thetaXiFiniteJetCombination_apply_eq_of_germ_eq
    obtain ⟨δ, hδ, hone⟩ := thetaXiIsolatingCutoff_eq_one_near t
    refine ⟨δ, hδ, fun x hx => ?_⟩
    change SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ x = ψ x
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, hone x hx, one_smul]
  exact (thetaXiTemperedLocalCoefficients_unique Q
    (thetaXiRawCompactJetFunctional_extension_mem_kernel a Q hL) t (a t) hloc.symm).symm

theorem thetaXiRawJetJointBound_iff_existsUnique_kernel_extension
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) :
    thetaXiRawJetJointBound a ↔ ∃! Q : 𝓢'(ℝ, ℂ),
      thetaXiTemperedMultiplier Q = 0 ∧
        ∀ φ : thetaSchwartzCompactCore, Q (φ : 𝓢(ℝ, ℂ)) = thetaXiRawCompactJetFunctional a φ := by
  constructor
  · intro h
    obtain ⟨Q, hL, hu⟩ :=
      (thetaSchwartzCompactCoreJointBound_iff_existsUnique_tempered_extension _).mp h
    exact ⟨Q, ⟨thetaXiRawCompactJetFunctional_extension_mem_kernel a Q hL, hL⟩,
      fun R hR => hu R hR.2⟩
  · rintro ⟨Q, ⟨_, hL⟩, _⟩
    exact thetaSchwartzCompactCoreJointBound_of_tempered _ Q hL

theorem thetaXiRawJetJointBound_iff_existsUnique_kernel_coefficients
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) :
    thetaXiRawJetJointBound a ↔ ∃! Q : 𝓢'(ℝ, ℂ),
      ∃ hQ : thetaXiTemperedMultiplier Q = 0,
        ∀ t : ℝ, thetaXiTemperedLocalCoefficients Q hQ t = a t := by
  constructor
  · intro h
    obtain ⟨Q, ⟨hQ, hL⟩, hu⟩ :=
      (thetaXiRawJetJointBound_iff_existsUnique_kernel_extension a).mp h
    refine ⟨Q, ⟨hQ, fun t => thetaXiRawCompactJetFunctional_extension_coefficients a Q hL t⟩, ?_⟩
    rintro R ⟨hR, ha⟩
    apply hu R
    refine ⟨hR, fun φ => ?_⟩
    have hfamily : (fun t => thetaXiTemperedLocalCoefficients R hR t) = a := funext ha
    rw [← hfamily]
    exact (thetaXiRawCompactJetFunctional_of_tempered R hR φ).symm
  · rintro ⟨Q, ⟨hQ, ha⟩, _⟩
    apply thetaSchwartzCompactCoreJointBound_of_tempered _ Q
    intro φ
    have hfamily : (fun t => thetaXiTemperedLocalCoefficients Q hQ t) = a := funext ha
    rw [← hfamily]
    exact (thetaXiRawCompactJetFunctional_of_tempered Q hQ φ).symm

end

end RHTower
