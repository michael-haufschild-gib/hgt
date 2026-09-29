import GaloisForLFunctions.RHTower.DeckPointPairApproxIdentity
import GaloisForLFunctions.RHTower.HyperbolicBallMeanValue

/-!
# Selberg's theorem for the finite-deck point-pair operators

For a continuous compactly supported profile `k` and a real-`C²` eigenfunction `G` of the positive
Laplacian with eigenvalue `s(1-s)`, the corpus mean-value theorem at an arbitrary centre gives
`∫_ℍ k(u(z, w)) G(w) dμ(w) = h_k(s) G(z)` with the Selberg transform
`h_k(s) = ∫_ℍ k(u(i, w)) (Im w)^s dμ(w)`.  Applied coordinatewise, every `C²` deck-equivariant
eigenfunction `y²ΔU = -s(1-s)U` satisfies `L_k U = h_k(s) U`.  For nonnegative unit profiles
concentrated near `u = 0`, `h_k(s)` is close to `1` and in particular nonzero.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry HyperbolicPointPairCentre HyperbolicRotationMean
  HyperbolicPowerEigen

noncomputable section

variable {N : ℕ}

/-- The Selberg transform `h_φ(s) = ∫_ℍ φ(u(i, w)) (Im w)^s dμ(w)`. -/
def selbergTransform (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ w, ((φ (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * powerEigen s w

theorem pairU_I_rot (θ : ℝ) (w : ℍ) : pairU UpperHalfPlane.I (rot θ • w) = pairU UpperHalfPlane.I w := by
  conv_lhs => rw [← rot_smul_I θ]
  rw [rot_smul_eq, rot_smul_eq, pairU_smul]

theorem integrable_pairKernel_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R) {G : ℍ → E}
    (hG : Continuous G) (z : ℍ) : Integrable (fun w => k (pairU z w) • G w) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall z (1 + 2 * R))
    ?_).1 (((hkc.comp (continuous_pairU_right z)).smul hG).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _))
  intro w hw
  by_contra hwK
  apply hw
  have : R < pairU z w := by
    by_contra h
    push Not at h
    exact hwK (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
  simp [hkR _ this]

/-- **Selberg's theorem, scalar form.** For a real-`C²` eigenfunction `G` of the positive
Laplacian with eigenvalue `s(1-s)` and a continuous compactly supported profile `k`,
`∫_ℍ k(u(z, w)) G(w) dμ(w) = h_k(s) G(z)`. -/
theorem integral_pairKernel_mul_eigen {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hkR : KernelSupport k R) {G : ℍ → ℂ} {s : ℂ} (hG : IsRealSmoothUpperHalfPlane G)
    (hGe : ∀ z, positiveHyperbolicLaplacian G z = s * (1 - s) * G z) (z : ℍ) :
    ∫ w, ((k (pairU z w) : ℝ) : ℂ) * G w = G z * selbergTransform k s := by
  have hGc := HyperbolicPointPair.continuous_of_smooth hG
  have hEc := HyperbolicPointPair.continuous_of_smooth (powerEigen_smooth s)
  let A : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.toGL (toSL2R z)
  have hA : 0 < A.val.det := by
    show 0 < ((toSL2R z : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [(toSL2R z).2]; norm_num
  have hAI : A • UpperHalfPlane.I = z := toSL2R_smul_I z
  have hker : ∀ w, ((k (pairU UpperHalfPlane.I (A⁻¹ • w)) : ℝ) : ℂ) = ((k (pairU z w) : ℝ) : ℂ) := by
    intro w
    congr 2
    have h := pairU_smul (toSL2R z) UpperHalfPlane.I (A⁻¹ • w)
    rw [← h]
    congr 1
    exact (smul_inv_smul A w)
  have hint : Integrable (fun w => ((k (pairU z w) : ℝ) : ℂ) * G w) := by
    refine (integrable_pairKernel_smul' hkc hkR hGc z).congr (Eventually.of_forall fun w => ?_)
    simp [Complex.real_smul]
  have h := integral_centred_kernel A hA (φ := fun w => ((k (pairU UpperHalfPlane.I w) : ℝ) : ℂ))
    (G := G) (s := s) (fun θ w => by simp only [pairU_I_rot])
    ((Complex.continuous_ofReal.comp (hkc.comp (continuous_pairU_right _))).aestronglyMeasurable)
    hG hGe (by simpa only [hker] using hint)
    ((integrable_pairKernel_smul' hkc hkR hEc UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul]))
  simp only [hker, hAI] at h
  exact h

/-- **Selberg's theorem for deck eigenfunctions**: a `C²` deck-equivariant `U` with
`y²ΔU = -s(1-s) U` satisfies `L_k U = h_k(s) U`. -/
theorem ppApply_eigen {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
    {U : ℍ → DeckSpace N} (hU : ContDiffOn ℝ 2 (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hUe : deckEquivariant N U) {s : ℂ} (hUeig : ∀ z, hypLap U z = (-(s * (1 - s))) • U z)
    (z : ℍ) : ppApply k U z = selbergTransform k s • U z := by
  have hUc : Continuous U := by
    have h := hU.continuousOn.comp_continuous continuous_coe fun w => w.im_pos
    simpa [Function.comp_def, ofComplex_apply] using h
  rw [ppApply_eq_integral hkc hkR hUc hUe]
  ext q
  have hint := integrable_pairKernel_smul hkc hkR hUc z
  have h := (EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).integral_comp_comm hint
  have hG : IsRealSmoothUpperHalfPlane (fun w => U w q) :=
    ((EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hU
  have hGe : ∀ z, positiveHyperbolicLaplacian (fun w => U w q) z = s * (1 - s) * U z q := by
    intro z
    have h1 := hypLap_apply hU z q
    rw [hUeig z, PiLp.smul_apply, smul_eq_mul] at h1
    linear_combination h1
  calc (∫ w, ((k (pairU z w) : ℝ) : ℂ) • U w) q
      = EuclideanSpace.proj q (∫ w, ((k (pairU z w) : ℝ) : ℂ) • U w) := rfl
    _ = ∫ w, EuclideanSpace.proj q (((k (pairU z w) : ℝ) : ℂ) • U w) := h.symm
    _ = ∫ w, ((k (pairU z w) : ℝ) : ℂ) * U w q := integral_congr_ae (Eventually.of_forall
          fun w => by
            change EuclideanSpace.proj q (((k (pairU z w) : ℝ) : ℂ) • U w) = _
            rw [map_smul, smul_eq_mul]; rfl)
    _ = U z q * selbergTransform k s := integral_pairKernel_mul_eigen hkc hkR hG hGe z
    _ = (selbergTransform k s • U z) q := by rw [PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- For a nonnegative profile of unit mass, `h_k(s)` is within the oscillation of `(Im w)^s` on
the support of `u(i, ·)`. -/
theorem norm_selbergTransform_sub_one_le {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hk0 : ∀ u, 0 ≤ k u) (hmass : ppKernelMass k = 1) (hkR : KernelSupport k R) (s : ℂ)
    {η : ℝ} (hη : ∀ w, pairU UpperHalfPlane.I w ≤ R → ‖powerEigen s w - 1‖ ≤ η) :
    ‖selbergTransform k s - 1‖ ≤ η := by
  have hEc := HyperbolicPointPair.continuous_of_smooth (powerEigen_smooth s)
  have h1 : (1 : ℂ) = ∫ w, ((k (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * 1 := by
    simp only [mul_one]
    rw [integral_complex_ofReal, integral_pairKernel_eq_one hkc hk0 hmass, Complex.ofReal_one]
  have hi1 : Integrable (fun w => ((k (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * powerEigen s w) :=
    (integrable_pairKernel_smul' hkc hkR hEc UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul])
  have hi2 : Integrable (fun w => ((k (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * 1) :=
    (integrable_pairKernel_smul' hkc hkR (continuous_const (y := (1 : ℂ))) UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul])
  unfold selbergTransform
  rw [h1, ← integral_sub hi1 hi2]
  refine (norm_integral_le_of_norm_le
    ((integrable_pairKernel_real hkc hkR UpperHalfPlane.I).mul_const η)
    (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk0 _)]
    by_cases hu : pairU UpperHalfPlane.I w ≤ R
    · exact mul_le_mul_of_nonneg_left (hη w hu) (hk0 _)
    · rw [hkR _ (not_le.1 hu), zero_mul, zero_mul]
  · rw [integral_mul_const, integral_pairKernel_eq_one hkc hk0 hmass, one_mul]

/-- **`h_k(s) ≠ 0` for concentrated unit profiles.** -/
theorem exists_radius_selbergTransform_ne_zero (s : ℂ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ {k : ℝ → ℝ} {R : ℝ}, Continuous k → (∀ u, 0 ≤ k u) →
      ppKernelMass k = 1 → KernelSupport k R → R ≤ R₀ → selbergTransform k s ≠ 0 := by
  have hEc := HyperbolicPointPair.continuous_of_smooth (powerEigen_smooth s)
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.1 hEc.continuousAt (1 / 2) (by norm_num)
  refine ⟨r ^ 2 / 16, by positivity, fun {k} {R} hkc hk0 hmass hkR hRle => ?_⟩
  have hRr : 8 * R < r ^ 2 := by nlinarith [sq_nonneg r]
  have hb := norm_selbergTransform_sub_one_le hkc hk0 hmass hkR s (η := 1 / 2) fun w hw => by
    have hd := dist_lt_of_pairU_le hRr hr (by rwa [pairU_comm])
    have := hball hd
    rw [dist_eq_norm, powerEigen_I] at this
    exact this.le
  intro h0
  rw [h0, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

end

end GaloisForLFunctions.RHTower.DeckPointPair
