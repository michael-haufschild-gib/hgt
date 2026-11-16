import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicMeromorphicResolvent

/-!
# The resolvent of the cubic cover on the real segment

The Laplacian of the cubic cover acts on the energy space through the pencil
`T(z) = 1 − (z + 1) S`, `S = m*m` the mass Gram (`kernelSpectralFormOperator`). MMD splits it at the
residual parameter `8/9`. The splitting works at every real parameter:

* `isUnit_spectralForm_of_neg`: for real `x < 0` the pencil is coercive,
  `Re⟨u, T(x)u⟩ = ‖∇u‖² − x‖mu‖² ≥ min(1, −x)‖u‖²`, hence invertible.
* For real `μ ∈ [0, 1)` the pencil is self-adjoint and Fredholm. Its null space `N(μ)` (the
  `μ`-eigenvectors) is finite dimensional, `S = 1/(μ + 1)` on `N(μ)`, and `T(μ)` is invertible on
  `N(μ)ᗮ`. Hence near `μ` (`inverse_spectralForm_eventually_eq`)
  `T(z)⁻¹ = ((μ + 1)/(μ − z)) P_{N(μ)} + (analytic at μ)`.
* On `L²` the resolvent `m T(z)⁻¹ m*` has the simple pole `((μ + 1)/(μ − z)) Π_μ`,
  `Π_μ = m P_{N(μ)} m*` (`resolvent_eventually_eq`), and `⟨F, Π_μ F⟩ = ‖P_{N(μ)} m* F‖²`
  (`inner_eigenProjection_self`): `Π_μ F = 0` as soon as `⟨F, Π_μ F⟩ = 0`.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.CubicEisenstein

/-! ### Negative parameters -/

/-- **Coercivity below the spectrum.** For real `x < 0`, `T(x)` is invertible. -/
theorem isUnit_spectralForm_of_neg {x : ℝ} (hx : x < 0) :
    IsUnit (kernelSpectralFormOperator (x : ℂ)) := by
  set T := kernelSpectralFormOperator (x : ℂ)
  set c : ℝ := min 1 (-x)
  have hc : 0 < c := lt_min one_pos (neg_pos.mpr hx)
  -- `c ‖u‖² ≤ Re ⟨u, T u⟩`
  have hco : ∀ u : KernelEnergyGraph, c * ‖u‖ ^ 2 ≤ (inner ℂ u (T u)).re := by
    intro u
    have hi := kernelSpectralFormOperator_inner (x : ℂ) u
    have hn := kernelEnergyGraph_norm_sq u
    rw [hi]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    have h1 : c ≤ 1 := min_le_left _ _
    have h2 : c ≤ -x := min_le_right _ _
    nlinarith [sq_nonneg ‖kernelEnergyGradient u‖, sq_nonneg ‖kernelEnergyMass u‖]
  -- lower bound `c ‖u‖ ≤ ‖T u‖`
  have hlow : ∀ u : KernelEnergyGraph, c * ‖u‖ ≤ ‖T u‖ := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have h1 := hco u
    have h2 : (inner ℂ u (T u)).re ≤ ‖u‖ * ‖T u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm u (T u))
    nlinarith
  have hinj : Function.Injective T := by
    intro u v huv
    have h := hlow (u - v)
    rw [map_sub, huv, sub_self, norm_zero] at h
    have : ‖u - v‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (u - v)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T :=
    ContinuousLinearMap.antilipschitz_of_bound T fun u => by
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
      have := hlow u
      rw [inv_mul_eq_div, le_div_iff₀ hc]
      linarith
  have hclosed : IsClosed (Set.range T) := hanti.isClosed_range T.uniformContinuous
  have hrange := selfAdjoint_range_eq_ker_orthogonal T (kernelSpectralFormOperator_selfAdjoint x) hclosed
  have hker : T.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (show Function.Injective (T : KernelEnergyGraph →ₗ[ℂ] KernelEnergyGraph)
      from hinj)
  have hsurj : Function.Surjective T := by
    intro v
    have hv : v ∈ T.range := by
      rw [hrange, hker, Submodule.bot_orthogonal_eq_top]
      trivial
    exact hv
  exact (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mpr ⟨hinj, hsurj⟩

/-! ### The splitting at a real parameter -/

variable (μ : ℝ)

/-- The null space of the pencil at `μ`: the `μ`-eigenvectors in the energy space. -/
def eigenNull : Submodule ℂ KernelEnergyGraph := (kernelSpectralFormOperator (μ : ℂ)).ker

instance eigenNull_complete : CompleteSpace (eigenNull μ) :=
  (kernelSpectralFormOperator (μ : ℂ)).isClosed_ker.completeSpace_coe

/-- The orthogonal projection `P` onto the null space. -/
abbrev eigenProj : KernelEnergyGraph →L[ℂ] KernelEnergyGraph := (eigenNull μ).starProjection

theorem eigenProj_mem (u : KernelEnergyGraph) : eigenProj μ u ∈ eigenNull μ :=
  (eigenNull μ).starProjection_apply_mem u

theorem eigenProj_eq_self {u : KernelEnergyGraph} (hu : u ∈ eigenNull μ) : eigenProj μ u = u :=
  (eigenNull μ).starProjection_eq_self_iff.mpr hu

theorem eigenProj_idem (u : KernelEnergyGraph) : eigenProj μ (eigenProj μ u) = eigenProj μ u :=
  eigenProj_eq_self μ (eigenProj_mem μ u)

theorem sub_eigenProj_mem (u : KernelEnergyGraph) : u - eigenProj μ u ∈ (eigenNull μ)ᗮ :=
  (eigenNull μ).sub_starProjection_mem_orthogonal u

/-- On the null space the mass Gram acts as `1/(μ + 1)`. -/
theorem eigenNull_gram (u : KernelEnergyGraph) (hu : u ∈ eigenNull μ) :
    kernelMassGram u = ((μ : ℂ) + 1)⁻¹ • u := by
  have hh : u - ((μ : ℂ) + 1) • kernelMassGram u = 0 := hu
  have he : u = ((μ : ℂ) + 1) • kernelMassGram u := sub_eq_zero.mp hh
  by_cases hne : (μ : ℂ) + 1 = 0
  · rw [hne, zero_smul] at he
    rw [he, map_zero, smul_zero]
  · calc kernelMassGram u = (((μ : ℂ) + 1)⁻¹ * ((μ : ℂ) + 1)) • kernelMassGram u := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = _ := by rw [mul_smul, ← he]

/-- The Gram preserves the orthogonal complement of the null space (self-adjointness). -/
theorem gram_mem_orthogonal (u : KernelEnergyGraph) (hu : u ∈ (eigenNull μ)ᗮ) :
    kernelMassGram u ∈ (eigenNull μ)ᗮ := by
  apply ((eigenNull μ).mem_orthogonal _).mpr
  intro v hv
  have he : inner ℂ v (kernelMassGram u) = inner ℂ (kernelMassGram v) u := by
    simpa only [ContinuousLinearMap.coe_coe] using (kernelMassGram_selfAdjoint.isSymmetric v u).symm
  rw [he, eigenNull_gram μ v hv, inner_smul_left (𝕜 := ℂ) v u (((μ : ℂ) + 1)⁻¹),
    (eigenNull μ).inner_right_of_mem_orthogonal hv hu, mul_zero]

/-- `P S u = P u/(μ + 1)`. -/
theorem eigenProj_gram (u : KernelEnergyGraph) :
    eigenProj μ (kernelMassGram u) = ((μ : ℂ) + 1)⁻¹ • eigenProj μ u := by
  have hsplit : kernelMassGram u = kernelMassGram (eigenProj μ u) + kernelMassGram (u - eigenProj μ u) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit, map_add, eigenNull_gram μ _ (eigenProj_mem μ u), map_smul, eigenProj_idem,
    (eigenNull μ).starProjection_apply_eq_zero_iff.mpr (gram_mem_orthogonal μ _ (sub_eigenProj_mem μ u)),
    add_zero]

/-- `T(z) P u = ((μ − z)/(μ + 1)) P u` (for `μ ≥ 0`). -/
theorem spectralForm_eigenProj (h0 : 0 ≤ μ) (z : ℂ) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (eigenProj μ u) = (((μ : ℂ) - z) / ((μ : ℂ) + 1)) • eigenProj μ u := by
  have hne : (μ : ℂ) + 1 ≠ 0 := by
    have : (μ + 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  change eigenProj μ u - (z + 1) • kernelMassGram (eigenProj μ u) = _
  rw [eigenNull_gram μ _ (eigenProj_mem μ u), smul_smul]
  calc eigenProj μ u - ((z + 1) * ((μ : ℂ) + 1)⁻¹) • eigenProj μ u
      = (1 - (z + 1) * ((μ : ℂ) + 1)⁻¹) • eigenProj μ u := by rw [sub_smul, one_smul]
    _ = _ := by congr 1; field_simp; ring

/-- `P T(z) u = ((μ − z)/(μ + 1)) P u`. -/
theorem eigenProj_spectralForm (h0 : 0 ≤ μ) (z : ℂ) (u : KernelEnergyGraph) :
    eigenProj μ (kernelSpectralFormOperator z u) = (((μ : ℂ) - z) / ((μ : ℂ) + 1)) • eigenProj μ u := by
  rw [← spectralForm_eigenProj μ h0 z u]
  change eigenProj μ (u - (z + 1) • kernelMassGram u) =
    eigenProj μ u - (z + 1) • kernelMassGram (eigenProj μ u)
  rw [map_sub, map_smul, eigenProj_gram, eigenNull_gram μ _ (eigenProj_mem μ u)]

/-- The shifted pencil `B(z) = T(z) + P`. -/
def shiftedPencil (z : ℂ) : KernelEnergyGraph →L[ℂ] KernelEnergyGraph :=
  kernelSpectralFormOperator z + eigenProj μ

theorem shiftedPencil_apply (z : ℂ) (u : KernelEnergyGraph) :
    shiftedPencil μ z u = kernelSpectralFormOperator z u + eigenProj μ u := rfl

theorem shiftedPencil_analyticAt (z : ℂ) : AnalyticAt ℂ (shiftedPencil μ) z :=
  (kernelSpectralFormOperator_analyticAt z).add analyticAt_const

theorem shiftedPencil_eigenProj (h0 : 0 ≤ μ) (z : ℂ) (u : KernelEnergyGraph) :
    shiftedPencil μ z (eigenProj μ u) = eigenProj μ (shiftedPencil μ z u) := by
  rw [shiftedPencil_apply, shiftedPencil_apply, map_add, spectralForm_eigenProj μ h0,
    eigenProj_spectralForm μ h0, eigenProj_idem]

/-- **Fredholm alternative.** At `μ ∈ [0, 1)` the shifted pencil `T(μ) + P` is invertible: `T(μ)` maps
onto `N(μ)ᗮ` (self-adjoint with closed range) and kills `N(μ)`. -/
theorem shiftedPencil_center_isUnit (h0 : 0 ≤ μ) (h1 : μ < 1) : IsUnit (shiftedPencil μ (μ : ℂ)) := by
  have hF := kernelSpectralFormOperator_isFredholm μ h0 h1
  have hrange : (kernelSpectralFormOperator (μ : ℂ)).range = (eigenNull μ)ᗮ :=
    selfAdjoint_range_eq_ker_orthogonal _ (kernelSpectralFormOperator_selfAdjoint μ) hF.isClosed_range
  have hPTu : ∀ u, eigenProj μ (kernelSpectralFormOperator (μ : ℂ) u) = 0 := fun u => by
    rw [eigenProj_spectralForm μ h0, sub_self, zero_div, zero_smul]
  have hTPu : ∀ u, kernelSpectralFormOperator (μ : ℂ) (eigenProj μ u) = 0 := fun u => by
    rw [spectralForm_eigenProj μ h0, sub_self, zero_div, zero_smul]
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mpr
  constructor
  · intro u v huv
    have h : kernelSpectralFormOperator (μ : ℂ) (u - v) + eigenProj μ (u - v) = 0 := by
      rw [← shiftedPencil_apply, map_sub, huv, sub_self]
    have hPd : eigenProj μ (u - v) = 0 := by
      have := congrArg (eigenProj μ) h
      rwa [map_add, map_zero, hPTu, zero_add, eigenProj_idem] at this
    have hTd : kernelSpectralFormOperator (μ : ℂ) (u - v) = 0 := by rwa [hPd, add_zero] at h
    exact sub_eq_zero.mp ((eigenProj_eq_self μ hTd).symm.trans hPd)
  · intro v
    have hv : v - eigenProj μ v ∈ (kernelSpectralFormOperator (μ : ℂ)).range := by
      rw [hrange]
      exact sub_eigenProj_mem μ v
    obtain ⟨u, hu⟩ := hv
    change kernelSpectralFormOperator (μ : ℂ) u = v - eigenProj μ v at hu
    refine ⟨(u - eigenProj μ u) + eigenProj μ v, ?_⟩
    have e1 : kernelSpectralFormOperator (μ : ℂ) ((u - eigenProj μ u) + eigenProj μ v) =
        v - eigenProj μ v := by
      rw [map_add, map_sub, hTPu, sub_zero, hu, hTPu, add_zero]
    have e2 : eigenProj μ ((u - eigenProj μ u) + eigenProj μ v) = eigenProj μ v := by
      rw [map_add, map_sub, eigenProj_idem, sub_self, eigenProj_idem, zero_add]
    rw [shiftedPencil_apply, e1, e2, sub_add_cancel]

theorem shiftedPencil_eventually_isUnit (h0 : 0 ≤ μ) (h1 : μ < 1) :
    ∀ᶠ z : ℂ in 𝓝 (μ : ℂ), IsUnit (shiftedPencil μ z) :=
  (shiftedPencil_analyticAt μ μ).continuousAt.eventually
    ((Units.isOpen (R := KernelEnergyGraph →L[ℂ] KernelEnergyGraph)).mem_nhds
      (show shiftedPencil μ μ ∈ {x : KernelEnergyGraph →L[ℂ] KernelEnergyGraph | IsUnit x} from
        shiftedPencil_center_isUnit μ h0 h1))

/-- The complementary projection `1 − P`. -/
abbrev coProj : KernelEnergyGraph →L[ℂ] KernelEnergyGraph :=
  ContinuousLinearMap.id ℂ KernelEnergyGraph - eigenProj μ

/-- The regular part of the inverse: `B(z)⁻¹ (1 − P)`. -/
def regularInverse (z : ℂ) : KernelEnergyGraph →L[ℂ] KernelEnergyGraph :=
  (Ring.inverse (shiftedPencil μ z)).comp (coProj μ)

/-- Right composition with a fixed operator preserves analyticity. -/
theorem analyticAt_comp_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E →L[ℂ] E} {z : ℂ} (hf : AnalyticAt ℂ f z) (C : E →L[ℂ] E) :
    AnalyticAt ℂ (fun w => (f w).comp C) z :=
  (((ContinuousLinearMap.compL ℂ E E E).flip C).analyticAt _).comp hf

theorem regularInverse_analyticAt (h0 : 0 ≤ μ) (h1 : μ < 1) :
    AnalyticAt ℂ (regularInverse μ) (μ : ℂ) := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) (A := KernelEnergyGraph →L[ℂ] KernelEnergyGraph))
    (shiftedPencil μ μ) (shiftedPencil_center_isUnit μ h0 h1)
  have hinv : AnalyticAt ℂ (fun z => Ring.inverse (shiftedPencil μ z)) (μ : ℂ) :=
    hi.comp_of_eq (shiftedPencil_analyticAt μ μ) rfl
  exact analyticAt_comp_right hinv (coProj μ)

/-- The local inverse `((μ + 1)/(μ − z)) P + B(z)⁻¹(1 − P)`. -/
def localInverse (z : ℂ) : KernelEnergyGraph →L[ℂ] KernelEnergyGraph :=
  (((μ : ℂ) + 1) / ((μ : ℂ) - z)) • eigenProj μ + regularInverse μ z

theorem localInverse_apply (z : ℂ) (u : KernelEnergyGraph) :
    localInverse μ z u = (((μ : ℂ) + 1) / ((μ : ℂ) - z)) • eigenProj μ u +
      Ring.inverse (shiftedPencil μ z) (u - eigenProj μ u) := rfl

/-- The algebra of the local inverse, on an abstract module: if `B = T + P` is invertible, `P` is an
idempotent commuting with `T` and `B⁻¹`, `T P = P T = d P` and `c d = 1`, then `c P + B⁻¹(1 − P)`
inverts `T` on both sides. -/
theorem local_inverse_identities {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T P B Bi : E →ₗ[ℂ] E) (c d : ℂ) (hcd : c * d = 1)
    (hB : ∀ v, B v = T v + P v) (hBiB : ∀ v, Bi (B v) = v) (hBBi : ∀ v, B (Bi v) = v)
    (hTP : ∀ v, T (P v) = d • P v) (hPT : ∀ v, P (T v) = d • P v) (hPP : ∀ v, P (P v) = P v)
    (hBiP : ∀ v, P (Bi v) = Bi (P v)) :
    (∀ u, T (c • P u + Bi (u - P u)) = u) ∧ (∀ u, c • P (T u) + Bi (T u - P (T u)) = u) := by
  have hT : ∀ v, T v = B v - P v := fun v => by rw [hB]; abel
  constructor
  · intro u
    have hP0 : P (Bi (u - P u)) = 0 := by rw [hBiP, map_sub, hPP, sub_self, map_zero]
    rw [map_add, map_smul, hTP, smul_smul, hcd, one_smul, hT (Bi (u - P u)), hBBi, hP0, sub_zero]
    exact add_sub_cancel _ _
  · intro u
    have hco : T u - P (T u) = B (u - P u) := by
      rw [hPT, hB, map_sub, map_sub, hTP, hPP]
      abel
    rw [hco, hBiB, hPT, smul_smul, hcd, one_smul]
    exact add_sub_cancel _ _

/-- **The local inverse inverts the pencil** off `μ`, wherever `B(z)` is invertible:
`T(z) L(z) = 1 = L(z) T(z)`, `L(z) = ((μ + 1)/(μ − z)) P + B(z)⁻¹(1 − P)`. -/
theorem localInverse_spec (h0 : 0 ≤ μ) (z : ℂ) (hne : z ≠ μ) (hz : IsUnit (shiftedPencil μ z)) :
    (∀ u, kernelSpectralFormOperator z (localInverse μ z u) = u) ∧
      (∀ u, localInverse μ z (kernelSpectralFormOperator z u) = u) := by
  have hμ1 : (μ : ℂ) + 1 ≠ 0 := by
    have : (μ + 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hsub : (μ : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hcd : ((μ : ℂ) + 1) / ((μ : ℂ) - z) * (((μ : ℂ) - z) / ((μ : ℂ) + 1)) = 1 := by
    field_simp
  have hBiB : ∀ v, Ring.inverse (shiftedPencil μ z) (shiftedPencil μ z v) = v := fun v =>
    congrArg (fun A : KernelEnergyGraph →L[ℂ] KernelEnergyGraph => A v)
      (Ring.inverse_mul_cancel (shiftedPencil μ z) hz)
  have hBBi : ∀ v, shiftedPencil μ z (Ring.inverse (shiftedPencil μ z) v) = v := fun v =>
    congrArg (fun A : KernelEnergyGraph →L[ℂ] KernelEnergyGraph => A v)
      (Ring.mul_inverse_cancel (shiftedPencil μ z) hz)
  have hBiP : ∀ v, eigenProj μ (Ring.inverse (shiftedPencil μ z) v) =
      Ring.inverse (shiftedPencil μ z) (eigenProj μ v) := fun v => by
    have h := shiftedPencil_eigenProj μ h0 z (Ring.inverse (shiftedPencil μ z) v)
    rw [hBBi] at h
    have h2 := congrArg (fun w : KernelEnergyGraph =>
      (Ring.inverse (shiftedPencil μ z) : KernelEnergyGraph →L[ℂ] KernelEnergyGraph) w) h
    rw [hBiB] at h2
    exact h2
  obtain ⟨hright', hleft'⟩ := local_inverse_identities
    (kernelSpectralFormOperator z).toLinearMap (eigenProj μ).toLinearMap
    (shiftedPencil μ z).toLinearMap (Ring.inverse (shiftedPencil μ z)).toLinearMap
    (((μ : ℂ) + 1) / ((μ : ℂ) - z)) (((μ : ℂ) - z) / ((μ : ℂ) + 1)) hcd
    (fun v => shiftedPencil_apply μ z v) hBiB hBBi (spectralForm_eigenProj μ h0 z)
    (eigenProj_spectralForm μ h0 z) (eigenProj_idem μ) hBiP
  exact ⟨fun u => by rw [localInverse_apply]; exact hright' u,
    fun u => by rw [localInverse_apply]; exact hleft' u⟩

/-- Off `μ`, wherever `B(z)` is invertible, the pencil `T(z)` is invertible. -/
theorem isUnit_spectralForm_of_ne (h0 : 0 ≤ μ) (z : ℂ) (hne : z ≠ μ) (hz : IsUnit (shiftedPencil μ z)) :
    IsUnit (kernelSpectralFormOperator z) := by
  obtain ⟨hright, hleft⟩ := localInverse_spec μ h0 z hne hz
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mpr
  exact ⟨fun a b hab => by rw [← hleft a, ← hleft b, hab], fun v => ⟨_, hright v⟩⟩

/-- The inverse of the pencil off `μ` is the local inverse. -/
theorem inverse_spectralForm_eq (h0 : 0 ≤ μ) (z : ℂ) (hne : z ≠ μ) (hz : IsUnit (shiftedPencil μ z)) :
    Ring.inverse (kernelSpectralFormOperator z) = localInverse μ z := by
  obtain ⟨hright, -⟩ := localInverse_spec μ h0 z hne hz
  have hU := isUnit_spectralForm_of_ne μ h0 z hne hz
  apply ContinuousLinearMap.ext
  intro v
  apply ((ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mp hU).1
  rw [hright]
  exact congrArg (fun A : KernelEnergyGraph →L[ℂ] KernelEnergyGraph => A v)
    (Ring.mul_inverse_cancel (kernelSpectralFormOperator z) hU)

/-- **The eigenvalues in `[0, 1)` are isolated.** Near `μ`, off `μ`, the pencil is invertible. -/
theorem spectralForm_eventually_isUnit (h0 : 0 ≤ μ) (h1 : μ < 1) :
    ∀ᶠ z in 𝓝[≠] (μ : ℂ), IsUnit (kernelSpectralFormOperator z) := by
  filter_upwards [(shiftedPencil_eventually_isUnit μ h0 h1).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hne
  exact isUnit_spectralForm_of_ne μ h0 z hne hz

/-- **The simple pole at a real parameter.** For `μ ∈ [0, 1)`, near `μ` (off `μ`):
`T(z)⁻¹ = ((μ + 1)/(μ − z)) P_{N(μ)} + B(z)⁻¹(1 − P_{N(μ)})`, the second term analytic at `μ`. -/
theorem inverse_spectralForm_eventually_eq (h0 : 0 ≤ μ) (h1 : μ < 1) :
    ∀ᶠ z in 𝓝[≠] (μ : ℂ), Ring.inverse (kernelSpectralFormOperator z) = localInverse μ z := by
  filter_upwards [(shiftedPencil_eventually_isUnit μ h0 h1).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hne
  exact inverse_spectralForm_eq μ h0 z hne hz

/-! ### The resolvent on `L²` -/

/-- `Π_μ = m P_{N(μ)} m*`: the residue of the `L²` resolvent at `μ`, up to the factor `μ + 1`. -/
def eigenProjection : KernelQuotientL2 →L[ℂ] KernelQuotientL2 := kernelL2SandwichCLM (eigenProj μ)

/-- The regular part of the `L²` resolvent at `μ`. -/
def regularResolvent (z : ℂ) : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  kernelL2SandwichCLM (regularInverse μ z)

theorem regularResolvent_analyticAt (h0 : 0 ≤ μ) (h1 : μ < 1) :
    AnalyticAt ℂ (regularResolvent μ) (μ : ℂ) := by
  change AnalyticAt ℂ (⇑kernelL2SandwichCLM ∘ regularInverse μ) (μ : ℂ)
  exact (kernelL2SandwichCLM.analyticAt _).comp (regularInverse_analyticAt μ h0 h1)

/-- **The `L²` resolvent near a real parameter.** `R(z) = ((μ + 1)/(μ − z)) Π_μ + R_reg(z)`. -/
theorem resolvent_eventually_eq (h0 : 0 ≤ μ) (h1 : μ < 1) :
    ∀ᶠ z in 𝓝[≠] (μ : ℂ), kernelSpectralResolvent z =
      (((μ : ℂ) + 1) / ((μ : ℂ) - z)) • eigenProjection μ + regularResolvent μ z := by
  filter_upwards [inverse_spectralForm_eventually_eq μ h0 h1] with z hz
  change kernelL2SandwichCLM (Ring.inverse (kernelSpectralFormOperator z)) = _
  rw [hz, localInverse, map_add, map_smul]
  rfl

/-- `⟨F, Π_μ F⟩ = ‖P_{N(μ)} m* F‖²`. -/
theorem inner_eigenProjection_self (F : KernelQuotientL2) :
    inner ℂ F (eigenProjection μ F) =
      ((‖eigenProj μ (kernelEnergyMass.adjoint F)‖ ^ 2 : ℝ) : ℂ) := by
  change inner ℂ F (kernelEnergyMass (eigenProj μ (kernelEnergyMass.adjoint F))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  set x := kernelEnergyMass.adjoint F
  have h0 : inner ℂ (x - eigenProj μ x) (eigenProj μ x) = 0 :=
    (eigenNull μ).inner_left_of_mem_orthogonal (eigenProj_mem μ x) (sub_eigenProj_mem μ x)
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [h0, inner_self_eq_norm_sq_to_K]
  simp

/-- **No residue without self-pairing.** If `⟨F, Π_μ F⟩ = 0` then `Π_μ F = 0`. -/
theorem eigenProjection_eq_zero_of_inner (F : KernelQuotientL2)
    (h : inner ℂ F (eigenProjection μ F) = 0) : eigenProjection μ F = 0 := by
  rw [inner_eigenProjection_self] at h
  have h2 : ‖eigenProj μ (kernelEnergyMass.adjoint F)‖ = 0 := by
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.zero_re] at this
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  change kernelEnergyMass (eigenProj μ (kernelEnergyMass.adjoint F)) = 0
  rw [norm_eq_zero.mp h2, map_zero]

end GaloisForLFunctions.OrderSixMetaplecticTheory
