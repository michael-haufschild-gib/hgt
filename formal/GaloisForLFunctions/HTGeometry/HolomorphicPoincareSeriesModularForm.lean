import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# The Poincaré series is a modular form of level one

For `k ≥ 3` the Poincaré series `P_m` of weight `k` is holomorphic on `ℍ`, because it is a locally
uniform limit of finite sums of holomorphic summands, and it is bounded at the cusp, because every
summand is dominated in norm by the corresponding Eisenstein summand.  Together with the weight-`k`
transformation law this packages `P_m` as `ModularForm 𝒮ℒ k`.

The holomorphy of one summand is checked on the explicit extension
`z ↦ (cz+d)^{-k} · exp(2πi m (az+b)/(cz+d))` to the open upper half-plane in `ℂ`, which agrees with
the summand through `ofComplex`.
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularForm Complex Matrix CongruenceSubgroup Set Filter Topology
open scoped MatrixGroups Real Manifold ModularForm

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Holomorphy of the summands -/

/-- The bottom row of a determinant-one matrix is not the zero vector. -/
theorem SL2_bottomRow_real_ne_zero (A : SL(2, ℤ)) :
    (fun i : Fin 2 => ((A 1 i : ℤ) : ℝ)) ≠ 0 := by
  intro h
  have h0' : A 1 0 = 0 := by
    have := congrFun h 0
    simpa using this
  have h1' : A 1 1 = 0 := by
    have := congrFun h 1
    simpa using this
  have := A.det_coe
  rw [Matrix.det_fin_two, h0', h1'] at this
  simp at this

/-- The Möbius image of a point of the upper half-plane, as a rational function of `z`. -/
theorem coe_smul_ofComplex_eq (M : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ((M • ofComplex z : ℍ) : ℂ)
      = (((M 0 0 : ℤ) : ℂ) * z + ((M 0 1 : ℤ) : ℂ)) / (((M 1 0 : ℤ) : ℂ) * z + ((M 1 1 : ℤ) : ℂ)) := by
  rw [coe_specialLinearGroup_apply, ofComplex_apply_of_im_pos hz]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]

/-- The extension of one Poincaré summand to the open upper half-plane in `ℂ` is holomorphic. -/
theorem poincareSummand_extension_differentiableOn (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0) :
    DifferentiableOn ℂ (↑ₕ(poincareSummand k m v)) {z : ℂ | 0 < z.im} := by
  set M := gammaSetMatrix v with hM
  have hden : ∀ z ∈ {z : ℂ | 0 < z.im},
      ((M 1 0 : ℤ) : ℂ) * z + ((M 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro z hz
    have hz' : 0 < z.im := hz
    simpa using UpperHalfPlane.linear_ne_zero (cd := fun i : Fin 2 => ((M 1 i : ℤ) : ℝ))
      ⟨z, hz'⟩ (SL2_bottomRow_real_ne_zero M)
  have hmob : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (2 * π * I * m *
      ((((M 0 0 : ℤ) : ℂ) * z + ((M 0 1 : ℤ) : ℂ)) / (((M 1 0 : ℤ) : ℂ) * z + ((M 1 1 : ℤ) : ℂ)))))
      {z : ℂ | 0 < z.im} := by
    apply DifferentiableOn.cexp
    apply DifferentiableOn.mul (differentiableOn_const _)
    exact DifferentiableOn.div (by fun_prop) (by fun_prop) hden
  refine DifferentiableOn.congr ((div_linear_zpow_differentiableOn k v.1).mul hmob) ?_
  intro z hz
  have hz' : 0 < z.im := hz
  lift z to ℍ using hz'
  rw [comp_ofComplex]
  unfold poincareSummand eisSummand
  rw [← hM, coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
  rfl

/-- Locally uniform convergence of the extended partial sums on the open upper half-plane. -/
theorem poincareSeries_tendstoLocallyUniformlyOn {k : ℤ} (hk : 3 ≤ k) (m : ℕ) :
    TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet 1 1 0)) ↦
      ↑ₕ(fun (z : ℍ) ↦ ∑ x ∈ s, poincareSummand k m x z)) (↑ₕ(poincareSeries k m))
        Filter.atTop {z : ℂ | 0 < z.im} := by
  rw [← upperHalfPlaneSet, ← range_coe, ← image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply poincareSeries_tendstoLocallyUniformly hk
  · simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ, mapsTo_range_iff,
      Set.mem_univ, forall_const]

/-- **Holomorphy** of the Poincaré series. -/
theorem poincareSeries_mdifferentiable {k : ℤ} (hk : 3 ≤ k) (m : ℕ) :
    MDiff (poincareSeries k m) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕ(poincareSeries k m)) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z ↦ (comp_ofComplex (poincareSeries k m) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (poincareSeries_tendstoLocallyUniformlyOn hk m).differentiableOn
    (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun _ _ ↦ poincareSummand_extension_differentiableOn _ _ _) isOpen_upperHalfPlaneSet

/-! ## Slash-invariant forms and boundedness at the cusp -/

/-- The Poincaré series as a slash-invariant form for `Γ(1)`. -/
def poincareSeriesSIFGamma (k : ℤ) (m : ℕ) : SlashInvariantForm (Gamma 1) k where
  toFun := poincareSeries k m
  slash_action_eq' A hA := by
    obtain ⟨A, _, rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, poincareSeries_slash_apply]

theorem poincareSeriesSIFGamma_apply (k : ℤ) (m : ℕ) (z : ℍ) :
    poincareSeriesSIFGamma k m z = poincareSeries k m z := rfl

/-- The Poincaré series as a slash-invariant form for `SL(2,ℤ)`. -/
def poincareSeriesSIF (k : ℤ) (m : ℕ) : SlashInvariantForm 𝒮ℒ k where
  toFun := poincareSeries k m
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact poincareSeries_slash_apply k m γ

theorem poincareSeriesSIF_apply (k : ℤ) (m : ℕ) (z : ℍ) :
    poincareSeriesSIF k m z = poincareSeries k m z := rfl

/-- The Poincaré series is dominated by the full sum of Eisenstein summand norms. -/
theorem norm_poincareSeries_le_tsum_norm {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    ‖poincareSeries k m z‖ ≤ ∑' x : Fin 2 → ℤ, ‖eisSummand k x z‖ := by
  unfold poincareSeries
  refine (norm_tsum_le_tsum_norm (summable_norm_poincareSummand hk m z)).trans ?_
  refine ((summable_norm_poincareSummand hk m z).tsum_le_tsum
    (fun v => norm_poincareSummand_le k m v z) ((summable_norm_eisSummand hk z).subtype _)).trans ?_
  exact Summable.tsum_subtype_le (fun x : Fin 2 → ℤ => ‖eisSummand k x z‖) _
    (fun _ => norm_nonneg _) (summable_norm_eisSummand hk z)

/-- **Boundedness at the cusp.** -/
theorem isBoundedAtImInfty_poincareSeries {k : ℤ} (hk : 3 ≤ k) (m : ℕ) :
    IsBoundedAtImInfty (poincareSeries k m) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑' (x : Fin 2 → ℤ), r ⟨⟨1, 2⟩, two_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip z (Nat.one_pos)
  rw [← poincareSeriesSIFGamma_apply, ← SlashInvariantForm.T_zpow_width_invariant 1 k n (poincareSeriesSIFGamma k m) z,
    poincareSeriesSIFGamma_apply]
  apply le_trans (norm_poincareSeries_le_tsum_norm hk m _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨1, 2⟩, two_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right ((1 : ℕ) : ℝ) hz hn)

/-- **The Poincaré series of weight `k ≥ 3` is a modular form of level one.** -/
def poincareSeriesMF {k : ℤ} (hk : 3 ≤ k) (m : ℕ) : ModularForm 𝒮ℒ k where
  toFun := poincareSeries k m
  slash_action_eq' := (poincareSeriesSIF k m).slash_action_eq'
  holo' := poincareSeries_mdifferentiable hk m
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [poincareSeries_slash_apply k m γ]
    exact isBoundedAtImInfty_poincareSeries hk m

theorem poincareSeriesMF_apply {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    poincareSeriesMF hk m z = poincareSeries k m z := rfl

end

end GaloisForLFunctions.HTGeometry
