import GaloisForLFunctions.RHTower.RepPointPairErgodic

/-!
# A test-field criterion for a Laplace eigenvalue in `(0, ¼)`

Let `φ` be a nonnegative `C³` profile with `φ(0) > 0`, kernel mass `m` and `h = h_φ(½)`.  Let `F` be a
continuous `ρ`-equivariant field, square-integrable on the modular cell, pointwise orthogonal to the
`ρ`-invariant vectors, whose Dirichlet form is small:

  `∫_𝒟 ∫_ℍ φ(u(z, w)) ‖F(z) − F(w)‖² < 2 (m − h) ∫_𝒟 ‖F‖²`.

By the Dirichlet identity `re⟪L_φ F, F⟫ > h ‖F‖²`, so `L_φ` has an eigenvalue `> h` with an
eigenvector orthogonal to the invariant constants.  Its joint `L_{Dφ}`-eigenvector is a Laplace
eigenfunction with eigenvalue in `[0, ¼)`, and ergodicity excludes `0`
(`exists_laplaceEigen_of_testField`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology RCLike Module End
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.DeckPointPair (selbergTransform selbergTransform_one_eq_mass)

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-- A field pointwise orthogonal to the invariant vectors is orthogonal to the invariant constants. -/
theorem toRepL2_mem_orthogonal_invConst {F : ℍ → EuclideanSpace ℂ ι} (hF2 : MemLp F 2 cellMeasure)
    (hFV : ∀ z (c : EuclideanSpace ℂ ι), (∀ B, ρ B c = c) → ⟪c, F z⟫_ℂ = 0) :
    toRepL2 F hF2 ∈ (invConst ρ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction (p := fun u _ => ⟪u, toRepL2 F hF2⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨c, hc, rfl⟩
    rw [MeasureTheory.L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [constRep_coeFn (ι := ι) c, MemLp.coeFn_toLp hF2] with z h1 h2
    change ⟪(constRep ι c : ℍ → EuclideanSpace ℂ ι) z, (toRepL2 F hF2 : ℍ → _) z⟫_ℂ = 0
    rw [h1, show (toRepL2 F hF2 : ℍ → EuclideanSpace ℂ ι) z = F z from h2]
    exact hFV z c hc
  · exact inner_zero_left _
  · intro x y _ _ hx hy
    rw [inner_add_left, hx, hy, add_zero]
  · intro a x _ hx
    rw [inner_smul_left, hx, mul_zero]

/-- `‖F‖² = ∫_𝒟 ‖F‖²` for the `L²` class of a field. -/
theorem norm_toRepL2_sq {F : ℍ → EuclideanSpace ℂ ι} (hF2 : MemLp F 2 cellMeasure) :
    ‖toRepL2 F hF2‖ ^ 2 = ∫ z in fd, ‖F z‖ ^ 2 := by
  have h := lintegral_normSq_eq (toRepL2 F hF2)
  have hcongr : ∫⁻ z in fd, ENNReal.ofReal (‖(toRepL2 F hF2 : ℍ → EuclideanSpace ℂ ι) z‖ ^ 2) =
      ∫⁻ z in fd, ENNReal.ofReal (‖F z‖ ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hF2] with z hz
    rw [show (toRepL2 F hF2 : ℍ → EuclideanSpace ℂ ι) z = F z from hz]
  rw [hcongr] at h
  have hint : Integrable (fun z => ‖F z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hF2.1).1 hF2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg _)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (integral_nonneg fun z => sq_nonneg _)).1 h.symm

namespace SmoothProfile

variable (P : SmoothProfile)

/-- **The Dirichlet form computes the numerical range**:
`re⟪L_φ F, F⟫ = m ‖F‖² − ½ ∫_𝒟 ∫_ℍ φ(u(z, w)) ‖F(z) − F(w)‖²` for a nonnegative profile. -/
theorem re_inner_repOp_toRepL2 (hφ0 : ∀ u, 0 ≤ P.toFun u) {F : ℍ → EuclideanSpace ℂ ι}
    (hFc : Continuous F) (hFe : IsEquivariant ρ F) (hF2 : MemLp F 2 cellMeasure) :
    re ⟪P.repOp ρ (toRepL2 F hF2), toRepL2 F hF2⟫_ℂ = kernelMassR P.toFun * ‖toRepL2 F hF2‖ ^ 2 -
      (∫ z in fd, ∫ w, P.toFun (pairU z w) * ‖F z - F w‖ ^ 2) / 2 := by
  have hD := integral_dirichlet P.contDiff.continuous P.abs_le P.radius_nonneg hφ0
    P.kernelSupport' hFc hFe hF2
  have hcoe : ppApply ρ P.toFun (toRepL2 F hF2 : ℍ → EuclideanSpace ℂ ι) = ppApply ρ P.toFun F :=
    ppApply_congr_ae _ (MemLp.coeFn_toLp hF2)
  have hinner : ⟪P.repOp ρ (toRepL2 F hF2), toRepL2 F hF2⟫_ℂ =
      ∫ z in fd, ⟪ppApply ρ P.toFun F z, F z⟫_ℂ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [P.repOp_coeFn (ρ := ρ) (toRepL2 F hF2), MemLp.coeFn_toLp hF2] with z h1 h2
    rw [h1, hcoe, show (toRepL2 F hF2 : ℍ → EuclideanSpace ℂ ι) z = F z from h2]
  have hint : Integrable (fun z => ⟪ppApply ρ P.toFun F z, F z⟫_ℂ) cellMeasure := by
    have hLF := memLp_ppApply (ρ := ρ) P.contDiff.continuous P.abs_le P.radius_nonneg
      P.kernelSupport' hF2
    have h1 : Integrable (fun z => ‖ppApply ρ P.toFun F z‖ ^ 2) cellMeasure :=
      (memLp_two_iff_integrable_sq_norm hLF.1).1 hLF
    have h2 : Integrable (fun z => ‖F z‖ ^ 2) cellMeasure :=
      (memLp_two_iff_integrable_sq_norm hF2.1).1 hF2
    refine ((h1.add h2).div_const 2).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((continuous_ppApply (ρ := ρ) P.contDiff.continuous P.abs_le P.kernelSupport'
        hF2).inner hFc).aestronglyMeasurable
    · show ‖⟪ppApply ρ P.toFun F z, F z⟫_ℂ‖ ≤ (‖ppApply ρ P.toFun F z‖ ^ 2 + ‖F z‖ ^ 2) / 2
      refine (norm_inner_le_norm _ _).trans ?_
      nlinarith [sq_nonneg (‖ppApply ρ P.toFun F z‖ - ‖F z‖)]
  rw [hinner, ← integral_re hint, norm_toRepL2_sq hF2]
  have hre : ∀ z, re ⟪ppApply ρ P.toFun F z, F z⟫_ℂ = re ⟪F z, ppApply ρ P.toFun F z⟫_ℂ := by
    intro z
    rw [← inner_conj_symm, RCLike.conj_re]
  simp_rw [hre]
  linarith

/-- **The test-field criterion.**  If a continuous equivariant square-integrable field `F`, pointwise
orthogonal to the `ρ`-invariant vectors, has Dirichlet form below `2(m − h_φ(½)) ∫_𝒟 ‖F‖²` for a
nonnegative `C³` profile `φ` with `φ(0) > 0`, then there is a Laplace eigenfunction `U ≠ 0` with
eigenvalue `λ ∈ (0, ¼)`, orthogonal to the invariant constants. -/
theorem exists_laplaceEigen_of_testField (hφ0 : ∀ u, 0 ≤ P.toFun u) (hφpos : 0 < P.toFun 0)
    {F : ℍ → EuclideanSpace ℂ ι} (hFc : Continuous F) (hFe : IsEquivariant ρ F)
    (hF2 : MemLp F 2 cellMeasure)
    (hFV : ∀ z (c : EuclideanSpace ℂ ι), (∀ B, ρ B c = c) → ⟪c, F z⟫_ℂ = 0)
    (hD : ∫ z in fd, ∫ w, P.toFun (pairU z w) * ‖F z - F w‖ ^ 2 <
      2 * (kernelMassR P.toFun - halfTransform (fun u => |P.toFun u|)) * ∫ z in fd, ‖F z‖ ^ 2) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 / 4 ∧ ∃ U : ℍ → EuclideanSpace ℂ ι,
      ∃ hL : IsLaplaceEigen ρ lam U, (∃ z, U z ≠ 0) ∧ toRepL2 U hL.memLp ∈ (invConst ρ)ᗮ := by
  have hFV' := toRepL2_mem_orthogonal_invConst hF2 hFV
  have hre := P.re_inner_repOp_toRepL2 hφ0 hFc hFe hF2
  have hnorm := norm_toRepL2_sq hF2
  have hstart : halfTransform (fun u => |P.toFun u|) * ‖toRepL2 F hF2‖ ^ 2 <
      re ⟪P.repOp ρ (toRepL2 F hF2), toRepL2 F hF2⟫_ℂ := by
    rw [hre, hnorm]
    linarith
  obtain ⟨M, hhM, -, x, hxV, hx0, hx⟩ := exists_top_eigenvector P.contDiff.continuous P.abs_le
    P.radius_nonneg P.kernelSupport' hFV' hstart
  have hM0 : 0 < M := (halfTransform_abs_nonneg _).trans_lt hhM
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hfin := finiteDimensional_eigenspace_ppL2 (ρ := ρ) P.contDiff.continuous P.abs_le
    P.radius_nonneg P.kernelSupport' (m := (M : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0])
  obtain ⟨u, hu0, huV, hu, κ, hκ⟩ := P.exists_lap_eigenvector hMC hfin hx0 hxV hx
  have hIco := P.laplaceEigenvalue_mem_Ico hφ0 ⟨0, le_refl _, hφpos.ne'⟩ hhM hu hu0 hκ
  have hL := isLaplaceEigen_eigenRep (ρ := ρ) hMC hu hu0 hκ
  rw [Complex.ofReal_re] at hL
  refine ⟨-(κ / M), lt_of_le_of_ne hIco.1 ?_, hIco.2, P.eigenRep ρ M u, hL,
    P.exists_eigenRep_ne_zero hMC hu hu0, ?_⟩
  · -- `λ = 0` would put the top eigenvalue at the kernel mass
    intro hlam0
    have hs : (1 : ℂ) * (1 - 1) = ((-(κ / M) : ℝ) : ℂ) := by
      rw [← hlam0]
      simp
    have hmass := P.selbergTransform_eq_of_lapEigen hM0.ne' hu hu0 hκ hs
    rw [selbergTransform_one_eq_mass P.contDiff.continuous
      (kernelSupport_deck P.kernelSupport')] at hmass
    have hMm : M = kernelMassR P.toFun := by exact_mod_cast hmass.symm
    have hUeig : ∀ z, ppApply ρ P.toFun (P.eigenRep ρ M u) z =
        ((kernelMassR P.toFun : ℝ) : ℂ) • P.eigenRep ρ M u z := by
      intro z
      rw [ppApply_eigenRep hMC hu, ← hMm]
      rfl
    obtain ⟨c, hc, hUc⟩ := eq_const_of_ppApply_eq_mass P.contDiff.continuous P.abs_le
      P.radius_nonneg hφ0 P.kernelSupport' (P.continuous_eigenRep _ _) (P.equivariant_eigenRep _ _)
      hφpos (P.memLp_eigenRep _ _) hUeig
    have huc : u = constRep ι c := by
      rw [← toRepL2_eigenRep hMC hu]
      exact MemLp.toLp_congr _ (memLp_const c) (Eventually.of_forall hUc)
    have huin : u ∈ invConst ρ := huc ▸ Submodule.subset_span ⟨c, hc, rfl⟩
    exact hu0 (inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 huV u huin))
  · convert huV using 1
    exact toRepL2_eigenRep hMC hu

end SmoothProfile

end

end GaloisForLFunctions.RHTower.RepPointPair
