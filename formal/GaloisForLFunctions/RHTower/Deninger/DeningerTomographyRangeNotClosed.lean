import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyProduct
import GaloisForLFunctions.HTGeometry.FrechetClosedRange

/-!
# The cofinal prime tomography has non-closed range

Restricted to `K_p = ker Per_p`, the tomography `𝒫_Q` is a continuous injection of Fréchet spaces:
`K_p` is a closed subspace of the complete Meyer source, and the countable product of circle spaces
is complete, Hausdorff and metrizable.  The damped translates `e^{-n}T_n\psi` show that its inverse
on the range is discontinuous — every compact trace carries the damping factor, while the Meyer
seminorm reads the source at the translated point and cancels it.  By the Fréchet open mapping
theorem a closed range would force that inverse to be continuous, so the range is not closed.

* `deningerEscapeSource_circle_tendsto_zero` : the trace of the escape family tends to zero.
* `deningerEscapeSource_tomography_tendsto_zero` : and hence so does its whole tomogram.
* `deningerTomography_not_continuous_symm` : **the inverse on the range is discontinuous.**
* `deningerTomography_not_isClosed_range` : **the range is not closed.**
-/

namespace RHTower

open SchwartzMap Filter Topology GaloisForLFunctions

noncomputable section

/-! ## The tomogram of the escape family tends to zero -/

/-- **Every circle trace of the escape family tends to zero.**  The `C^r` seminorm is a finite sum
of sup-norms of derivatives, each of which carries the damping factor. -/
theorem deningerEscapeSource_circle_tendsto_zero (P : {x : ℝ // 0 < x}) {a : ℝ} (ha : 0 < a)
    (h : DeningerMeyerSource) :
    Tendsto (fun n : ℕ => deningerPeriodizationLM P (deningerEscapeSource a (n : ℝ) h))
      atTop (𝓝 0) := by
  refine DeningerCircle.hasBasis_nhds_zero.tendsto_right_iff.2 ?_
  rintro ⟨r, ε⟩ hε
  have hsum : Tendsto (fun n : ℕ => ∑ m ∈ Finset.range (r + 1),
      deningerPeriodicSup m (deningerPeriodizationMap P.2
        (deningerEscapeFamily a (n : ℝ) (DeningerMeyerSource.toSource h))))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (r + 1))
      (f := fun m (n : ℕ) => deningerPeriodicSup m (deningerPeriodizationMap P.2
        (deningerEscapeFamily a (n : ℝ) (DeningerMeyerSource.toSource h))))
      (a := fun _ => (0 : ℝ))
      fun m _ => deningerEscape_trace_tendsto_zero P.2 ha m (DeningerMeyerSource.toSource h)
    simpa using this
  exact hsum.eventually (gt_mem_nhds hε)

/-- **The whole tomogram of the escape family tends to zero** in the product topology. -/
theorem deningerEscapeSource_tomography_tendsto_zero {ι : Type*} (P : ι → {x : ℝ // 0 < x})
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Tendsto (fun n : ℕ => deningerTomographyLM P (deningerEscapeSource a (n : ℝ) h))
      atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  simpa [deningerTomographyLM_apply] using
    deningerEscapeSource_circle_tendsto_zero (P i) ha h

/-! ## The source seminorm does not follow -/

/-- **The Meyer seminorm of the escape family is bounded below**, uniformly in the escape
parameter, by the value of the cochain at the origin. -/
theorem deningerEscapeSource_meyer_ge (h : DeningerMeyerSource) (n : ℕ) :
    ‖((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) 0‖
      ≤ DeningerMeyerSource.seminorms (1, 0) (deningerEscapeSource 1 (n : ℝ) h) := by
  have hb := deningerEscapeFamily_meyer_ge (a := 1) (s := (n : ℝ)) (u := 0)
    (by positivity) (DeningerMeyerSource.toSource h)
  simpa [DeningerMeyerSource.seminorms_apply, deningerEscapeSource_toSource] using hb

/-- A nonzero cochain can be translated so that it does not vanish at the origin, without leaving
the kernel of a periodization. -/
theorem exists_escapeSource_apply_zero_ne (P0 : {x : ℝ // 0 < x}) {ψ : DeningerMeyerSource}
    (hψK : deningerPeriodizationLM P0 ψ = 0) (hψ : ψ ≠ 0) :
    ∃ φ : DeningerMeyerSource, deningerPeriodizationLM P0 φ = 0
      ∧ ((DeningerMeyerSource.toSource φ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) 0 ≠ 0 := by
  have hne : ((DeningerMeyerSource.toSource ψ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) ≠ 0 := fun h0 =>
    hψ (DeningerMeyerSource.toSource.injective (Subtype.ext h0))
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.1 hne
  refine ⟨deningerEscapeSource 0 (-u) ψ, deningerEscapeSource_mem_ker P0 0 (-u) hψK, ?_⟩
  rw [deningerEscapeSource_toSource, deningerEscapeFamily_apply]
  simpa using hu

/-! ## The inverse on the range is discontinuous, so the range is not closed -/

variable {Q : Set ℕ} (P : Q → {x : ℝ // 0 < x}) (P0 : {x : ℝ // 0 < x})

/-- The tomography restricted to `K_p`. -/
def deningerTomographyRestricted :
    ↥(LinearMap.ker (deningerPeriodizationLM P0)) →ₗ[ℂ] ((i : Q) → DeningerCircle (P i)) :=
  (deningerTomographyLM P).comp (LinearMap.ker (deningerPeriodizationLM P0)).subtype

theorem deningerTomographyRestricted_continuous :
    Continuous (deningerTomographyRestricted P P0) :=
  (deningerTomographyLM_continuous P).comp continuous_subtype_val

theorem deningerTomographyRestricted_injective (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q) (hP : ∀ q : Q, (P q).1 = Real.log (q : ℕ)) :
    Function.Injective (deningerTomographyRestricted P P0) :=
  (deningerTomographyLM_injective hQinf hQp P hP).comp Subtype.val_injective

/-- **The inverse of the restricted tomography on its range is not continuous.**  The escape family
lies in `K_p`, its tomogram tends to zero, and its Meyer seminorm stays above a positive constant. -/
theorem deningerTomography_not_continuous_symm (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q) (hP : ∀ q : Q, (P q).1 = Real.log (q : ℕ))
    {ψ : DeningerMeyerSource} (hψK : deningerPeriodizationLM P0 ψ = 0) (hψ : ψ ≠ 0) :
    ¬ Continuous (frechetRangeEquiv (deningerTomographyRestricted P P0)
      (deningerTomographyRestricted_injective P P0 hQinf hQp hP)).symm := by
  haveI : CompleteSpace ↥(LinearMap.ker (deningerPeriodizationLM P0)) :=
    ((deningerPeriodizationLM_isClosed_ker P0).isComplete).completeSpace_coe
  haveI : FirstCountableTopology ↥(LinearMap.ker (deningerPeriodizationLM P0)) :=
    Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : IsUniformAddGroup ↥(LinearMap.ker (deningerPeriodizationLM P0)) :=
    inferInstanceAs (IsUniformAddGroup
      ↥((LinearMap.ker (deningerPeriodizationLM P0)).toAddSubgroup))
  set f := deningerTomographyRestricted P P0 with hf
  set hinj := deningerTomographyRestricted_injective P P0 hQinf hQp hP with hinjdef
  intro hsymm
  obtain ⟨φ, hφK, hφ0⟩ := exists_escapeSource_apply_zero_ne P0 hψK hψ
  set x : ℕ → DeningerMeyerSource := fun n => deningerEscapeSource 1 (n : ℝ) φ with hx
  have hxK : ∀ n : ℕ, x n ∈ LinearMap.ker (deningerPeriodizationLM P0) := fun n =>
    deningerEscapeSource_mem_ker P0 1 (n : ℝ) hφK
  set X : ℕ → ↥(LinearMap.ker (deningerPeriodizationLM P0)) := fun n => ⟨x n, hxK n⟩ with hX
  -- the tomogram tends to zero
  have heq : (fun n : ℕ => ((frechetRangeEquiv f hinj (X n) :
      ↥(LinearMap.range f)) : (i : Q) → DeningerCircle (P i)))
      = fun n : ℕ => deningerTomographyLM P (deningerEscapeSource 1 (n : ℝ) φ) :=
    funext fun n => frechetRangeEquiv_coe f hinj (X n)
  have himg : Tendsto (fun n : ℕ => ((frechetRangeEquiv f hinj (X n) :
      ↥(LinearMap.range f)) : (i : Q) → DeningerCircle (P i))) atTop (𝓝 0) := by
    rw [heq]
    exact deningerEscapeSource_tomography_tendsto_zero P (a := 1) one_pos φ
  have hrange : Tendsto (fun n : ℕ => frechetRangeEquiv f hinj (X n)) atTop (𝓝 0) := by
    refine IsInducing.subtypeVal.tendsto_nhds_iff.2 ?_
    simpa [Function.comp_def] using himg
  -- continuity of the inverse would drag the source along
  have hker : Tendsto X atTop (𝓝 0) := by
    have hcomp := (hsymm.tendsto (0 : ↥(LinearMap.range f))).comp hrange
    have hfun : ((frechetRangeEquiv f hinj).symm ∘
        fun n : ℕ => frechetRangeEquiv f hinj (X n)) = X :=
      funext fun n => (frechetRangeEquiv f hinj).symm_apply_apply (X n)
    rw [hfun, map_zero] at hcomp
    exact hcomp
  have hsrc : Tendsto x atTop (𝓝 0) := by
    have hcomp := (continuous_subtype_val (X := DeningerMeyerSource)
      (p := fun y => y ∈ LinearMap.ker (deningerPeriodizationLM P0))).continuousAt.tendsto.comp hker
    simpa [Function.comp_def] using hcomp
  -- but the Meyer seminorm stays above a positive constant
  have hsem : Tendsto
      (fun n : ℕ => DeningerMeyerSource.seminorms (1, 0) (x n)) atTop (𝓝 0) := by
    have hcont := DeningerMeyerSource.withSeminorms.continuous_seminorm (1, 0)
    have hcomp := hcont.continuousAt.tendsto.comp hsrc
    rw [map_zero] at hcomp
    exact hcomp
  have hlow : ∀ n : ℕ, ‖((DeningerMeyerSource.toSource φ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) 0‖
      ≤ DeningerMeyerSource.seminorms (1, 0) (x n) := fun n =>
    deningerEscapeSource_meyer_ge φ n
  have hle := ge_of_tendsto hsem (Filter.Eventually.of_forall hlow)
  exact absurd (le_antisymm hle (norm_nonneg _)) (norm_ne_zero_iff.2 hφ0)

/-- **The range of the cofinal prime tomography on `K_p` is not closed.**  A closed range would make
the continuous injection a homeomorphism onto its range by the Fréchet open mapping theorem, and its
inverse is not continuous. -/
theorem deningerTomography_not_isClosed_range (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q) (hP : ∀ q : Q, (P q).1 = Real.log (q : ℕ))
    {ψ : DeningerMeyerSource} (hψK : deningerPeriodizationLM P0 ψ = 0) (hψ : ψ ≠ 0) :
    ¬ IsClosed ((LinearMap.range (deningerTomographyRestricted P P0) :
      Submodule ℂ ((i : Q) → DeningerCircle (P i))) :
      Set ((i : Q) → DeningerCircle (P i))) := by
  haveI : CompleteSpace ↥(LinearMap.ker (deningerPeriodizationLM P0)) :=
    ((deningerPeriodizationLM_isClosed_ker P0).isComplete).completeSpace_coe
  haveI : FirstCountableTopology
      ↥(LinearMap.ker (deningerPeriodizationLM P0)) :=
    Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : IsUniformAddGroup ↥(LinearMap.ker (deningerPeriodizationLM P0)) :=
    inferInstanceAs (IsUniformAddGroup
      ↥((LinearMap.ker (deningerPeriodizationLM P0)).toAddSubgroup))
  exact not_isClosed_range_of_not_continuous_symm _
    (deningerTomographyRestricted_continuous P P0)
    (deningerTomographyRestricted_injective P P0 hQinf hQp hP)
    (deningerTomography_not_continuous_symm P P0 hQinf hQp hP hψK hψ)

end

end RHTower
