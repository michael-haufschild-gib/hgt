import GaloisForLFunctions.RHTower.RepPointPairLaplacian
import GaloisForLFunctions.RHTower.DeckPointPairEigenRepresentative

/-!
# Eigenvectors of the twisted point-pair operators

Selberg's theorem in vector form: a `C²` `ρ`-equivariant `U` with `y²ΔU = -s(1-s) U` satisfies
`L_k U = h_k(s) U` (`ppApply_eigen`).

For a `C³` profile `φ` supported in `[-R, R]` both `φ` and `Dφ = u(u+1)φ'' + (2u+1)φ'` give bounded
operators on `L²(𝒟; ℂ^ι)` (`SmoothProfile.repOp`, `SmoothProfile.repLapOp`).  If `u` is an
eigenvector of `L_φ` with eigenvalue `ν ≠ 0`, then `U = ν⁻¹ L_φ u` is a representative of `u` with
`U = L_φ(ν⁻¹U)`; hence `U` is `C²`, `y²ΔU = ν⁻¹ L_{Dφ} U`, and the Green identity gives
`L_φ(y²ΔU) = ν y²ΔU`.  So `L_{Dφ}` maps the `ν`-eigenspace of `L_φ` into itself
(`SmoothProfile.repLapOp_mem`), and an eigenvector of `L_{Dφ}` with eigenvalue `κ` inside it is a
Laplace eigenfunction with `-y²ΔU = -(κ/ν) U` (`SmoothProfile.isLaplaceEigen_eigenRep`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Module End
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.DeckPointPair (hypLap radialLap selbergTransform
  integral_pairKernel_mul_eigen exists_abs_le_of_support deriv_eq_zero_of_abs_support)

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-- **Selberg's theorem for equivariant eigenfunctions**: a `C²` `ρ`-equivariant `U` with
`y²ΔU = -s(1-s) U` satisfies `L_k U = h_k(s) U`. -/
theorem ppApply_eigen {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
    {U : ℍ → EuclideanSpace ℂ ι} (hU : ContDiffOn ℝ 2 (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hUe : IsEquivariant ρ U) {s : ℂ} (hUeig : ∀ z, hypLap U z = (-(s * (1 - s))) • U z)
    (z : ℍ) : ppApply ρ k U z = selbergTransform k s • U z := by
  have hUc : Continuous U := by
    have h := hU.continuousOn.comp_continuous continuous_coe fun w => w.im_pos
    simpa [Function.comp_def, ofComplex_apply] using h
  rw [ppApply_eq_integral hkc hkR hUc hUe]
  ext q
  have hint := integrable_pairKernel_smul hkc hkR hUc z
  have h := (EuclideanSpace.proj q : EuclideanSpace ℂ ι →L[ℂ] ℂ).integral_comp_comm hint
  have hG : IsRealSmoothUpperHalfPlane (fun w => U w q) :=
    ((EuclideanSpace.proj q : EuclideanSpace ℂ ι →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hU
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
    _ = U z q * selbergTransform k s :=
        integral_pairKernel_mul_eigen hkc (kernelSupport_deck hkR) hG hGe z
    _ = (selbergTransform k s • U z) q := by rw [PiLp.smul_apply, smul_eq_mul, mul_comm]

theorem isEquivariant_smul {F : ℍ → EuclideanSpace ℂ ι} (c : ℂ) (hF : IsEquivariant ρ F) :
    IsEquivariant ρ (c • F) := fun A z => by
  simp only [Pi.smul_apply, hF A z, map_smul]

/-- A `C³` point-pair profile vanishing for `|u| > R`. -/
structure SmoothProfile where
  toFun : ℝ → ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  contDiff : ContDiff ℝ 3 toFun
  support : ∀ u, radius < |u| → toFun u = 0

namespace SmoothProfile

variable (P : SmoothProfile)

theorem contDiff_two : ContDiff ℝ 2 P.toFun := P.contDiff.of_le (by norm_num)

theorem kernelSupport' : KernelSupport P.toFun P.radius := fun u hu =>
  P.support u (lt_of_lt_of_le hu (le_abs_self u))

theorem contDiff_deriv : ContDiff ℝ 2 (deriv P.toFun) :=
  (contDiff_succ_iff_deriv.1 (show ContDiff ℝ (2 + 1) P.toFun from P.contDiff)).2.2

theorem contDiff_deriv_deriv : ContDiff ℝ 1 (deriv (deriv P.toFun)) :=
  (contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) (deriv P.toFun) from P.contDiff_deriv)).2.2

theorem contDiff_radialLap : ContDiff ℝ 1 (radialLap P.toFun) := by
  unfold radialLap
  have h1 := P.contDiff_deriv_deriv
  have h2 : ContDiff ℝ 1 (deriv P.toFun) := P.contDiff_deriv.of_le (by norm_num)
  exact ((contDiff_id.mul (contDiff_id.add contDiff_const)).mul h1).add
    (((contDiff_const.mul contDiff_id).add contDiff_const).mul h2)

theorem radialLap_support : ∀ u, P.radius < |u| → radialLap P.toFun u = 0 := by
  intro u hu
  have h1 := deriv_eq_zero_of_abs_support P.support hu
  have h2 := deriv_eq_zero_of_abs_support
    (fun v hv => deriv_eq_zero_of_abs_support P.support hv) hu
  simp [radialLap, h1, h2]

/-- A uniform bound for `|φ|`. -/
def bound : ℝ := Classical.choose (exists_abs_le_of_support P.contDiff.continuous P.support)

theorem abs_le (u : ℝ) : |P.toFun u| ≤ P.bound :=
  Classical.choose_spec (exists_abs_le_of_support P.contDiff.continuous P.support) u

/-- A uniform bound for `|Dφ|`. -/
def lapBound : ℝ := Classical.choose (exists_abs_le_of_support
  P.contDiff_radialLap.continuous P.radialLap_support)

theorem abs_lap_le (u : ℝ) : |radialLap P.toFun u| ≤ P.lapBound :=
  Classical.choose_spec (exists_abs_le_of_support P.contDiff_radialLap.continuous
    P.radialLap_support) u

theorem lap_kernelSupport : KernelSupport (radialLap P.toFun) P.radius := fun u hu =>
  P.radialLap_support u (lt_of_lt_of_le hu (le_abs_self u))

variable (ρ) in
/-- The operator `L_φ` on `L²(𝒟; ℂ^ι)`. -/
def repOp : RepL2 ι →L[ℂ] RepL2 ι :=
  ppL2 ρ P.contDiff.continuous P.abs_le P.radius_nonneg P.kernelSupport'

variable (ρ) in
/-- The operator `L_{Dφ}` on `L²(𝒟; ℂ^ι)`. -/
def repLapOp : RepL2 ι →L[ℂ] RepL2 ι :=
  ppL2 ρ P.contDiff_radialLap.continuous P.abs_lap_le P.radius_nonneg P.lap_kernelSupport

theorem repOp_coeFn (F : RepL2 ι) : (P.repOp ρ F : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure]
    ppApply ρ P.toFun F := ppL2_coeFn (ρ := ρ) _ _ _ _ F

theorem repLapOp_coeFn (F : RepL2 ι) : (P.repLapOp ρ F : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure]
    ppApply ρ (radialLap P.toFun) F := ppL2_coeFn (ρ := ρ) _ _ _ _ F

theorem repOp_isSymmetric : ((P.repOp ρ : RepL2 ι →L[ℂ] RepL2 ι) : RepL2 ι →ₗ[ℂ] RepL2 ι).IsSymmetric :=
  ppL2_isSymmetric (ρ := ρ) _ _ _ _

theorem repLapOp_isSymmetric :
    ((P.repLapOp ρ : RepL2 ι →L[ℂ] RepL2 ι) : RepL2 ι →ₗ[ℂ] RepL2 ι).IsSymmetric :=
  ppL2_isSymmetric (ρ := ρ) _ _ _ _

variable (ρ) in
/-- The representative `ν⁻¹ L_φ u`. -/
def eigenRep (ν : ℂ) (u : RepL2 ι) : ℍ → EuclideanSpace ℂ ι := ν⁻¹ • ppApply ρ P.toFun ⇑u

theorem ppApply_ae_of_eigen {u : RepL2 ι} {ν : ℂ} (hu : P.repOp ρ u = ν • u) :
    ppApply ρ P.toFun ⇑u =ᵐ[cellMeasure] ν • ⇑u := by
  have h1 : ⇑(ν • u) =ᵐ[cellMeasure] ppApply ρ P.toFun ⇑u := by
    rw [← hu]; exact P.repOp_coeFn u
  filter_upwards [h1, Lp.coeFn_smul ν u] with z hz1 hz2
  rw [← hz1, hz2]

section Eigen

variable {P} {u : RepL2 ι} {ν : ℂ} (hν : ν ≠ 0) (hu : P.repOp ρ u = ν • u)
include hν hu

theorem eigenRep_ae : P.eigenRep ρ ν u =ᵐ[cellMeasure] ⇑u := by
  filter_upwards [P.ppApply_ae_of_eigen hu] with z hz
  simp only [eigenRep, Pi.smul_apply]
  rw [hz, Pi.smul_apply, smul_smul, inv_mul_cancel₀ hν, one_smul]

theorem ppApply_eigenRep : ppApply ρ P.toFun (P.eigenRep ρ ν u) = ν • P.eigenRep ρ ν u := by
  rw [ppApply_congr_ae _ (eigenRep_ae hν hu)]
  funext z
  simp [eigenRep, smul_smul, mul_inv_cancel₀ hν]

theorem eigenRep_eq_ppApply : P.eigenRep ρ ν u = ppApply ρ P.toFun (ν⁻¹ • P.eigenRep ρ ν u) := by
  rw [ppApply_smul, ppApply_eigenRep hν hu, smul_smul, inv_mul_cancel₀ hν, one_smul]

omit hν hu in
theorem continuous_eigenRep (ν : ℂ) (u : RepL2 ι) : Continuous (P.eigenRep ρ ν u) :=
  (continuous_ppApply P.contDiff.continuous P.abs_le P.kernelSupport' (Lp.memLp u)).const_smul _

omit hν hu in
theorem equivariant_eigenRep (ν : ℂ) (u : RepL2 ι) : IsEquivariant ρ (P.eigenRep ρ ν u) :=
  isEquivariant_smul _ fun A z => ppApply_smul_point P.kernelSupport' _ A z

omit hν hu in
theorem memLp_eigenRep (ν : ℂ) (u : RepL2 ι) : MemLp (P.eigenRep ρ ν u) 2 cellMeasure :=
  (memLp_ppApply P.contDiff.continuous P.abs_le P.radius_nonneg P.kernelSupport'
    (Lp.memLp u)).const_smul _

theorem toRepL2_eigenRep : toRepL2 (P.eigenRep ρ ν u) (P.memLp_eigenRep ν _) = u := by
  rw [toRepL2, MemLp.toLp_congr _ (Lp.memLp _) (eigenRep_ae hν hu), Lp.toLp_coeFn]

theorem contDiffOn_eigenRep :
    ContDiffOn ℝ 2 (fun ζ => P.eigenRep ρ ν u (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} := by
  rw [show (fun ζ => P.eigenRep ρ ν u (ofComplex ζ)) =
      fun ζ => ppApply ρ P.toFun (ν⁻¹ • P.eigenRep ρ ν u) (ofComplex ζ) by
    rw [← eigenRep_eq_ppApply hν hu]]
  exact contDiffOn_two_ppApply (ρ := ρ) P.contDiff_two P.kernelSupport'
    ((P.continuous_eigenRep ν _).const_smul _) (isEquivariant_smul _ (P.equivariant_eigenRep ν _))

theorem hypLap_eigenRep : hypLap (P.eigenRep ρ ν u) =
    ν⁻¹ • ppApply ρ (radialLap P.toFun) (P.eigenRep ρ ν u) := by
  funext w
  conv_lhs => rw [eigenRep_eq_ppApply hν hu]
  rw [hypLap_ppApply P.contDiff_two P.kernelSupport' ((P.continuous_eigenRep ν _).const_smul _)
    (isEquivariant_smul _ (P.equivariant_eigenRep ν _)) w, ppApply_smul]

theorem ppApply_hypLap_eigenRep : ppApply ρ P.toFun (hypLap (P.eigenRep ρ ν u)) =
    ν • hypLap (P.eigenRep ρ ν u) := by
  funext z
  rw [ppApply_hypLap P.contDiff_two P.radius_nonneg P.kernelSupport' (contDiffOn_eigenRep hν hu)
    (P.equivariant_eigenRep ν _) z, hypLap_eigenRep hν hu]
  simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hν, one_smul]

/-- **`L_{Dφ}` preserves the eigenspaces of `L_φ`.** -/
theorem repLapOp_mem : P.repOp ρ (P.repLapOp ρ u) = ν • P.repLapOp ρ u := by
  have e1 : ppApply ρ (radialLap P.toFun) ⇑u = ν • hypLap (P.eigenRep ρ ν u) := by
    rw [← ppApply_congr_ae _ (eigenRep_ae hν hu), hypLap_eigenRep hν hu, smul_smul,
      mul_inv_cancel₀ hν, one_smul]
  have key : ppApply ρ P.toFun ⇑(P.repLapOp ρ u) = ν • ppApply ρ (radialLap P.toFun) ⇑u := by
    rw [ppApply_congr_ae _ (P.repLapOp_coeFn u), e1, ppApply_smul, ppApply_hypLap_eigenRep hν hu]
  apply Lp.ext
  filter_upwards [P.repOp_coeFn (P.repLapOp ρ u), Lp.coeFn_smul ν (P.repLapOp ρ u),
    P.repLapOp_coeFn u] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  exact congrFun key z

end Eigen

end SmoothProfile

variable (ρ) in
/-- A Laplace eigenfunction: a `C²`, `ρ`-equivariant, square-integrable `U` with `-y²ΔU = λ U`. -/
structure IsLaplaceEigen (lam : ℝ) (U : ℍ → EuclideanSpace ℂ ι) : Prop where
  contDiffOn : ContDiffOn ℝ 2 (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}
  equivariant : IsEquivariant ρ U
  memLp : MemLp U 2 cellMeasure
  eigen : ∀ z, hypLap U z = ((-lam : ℝ) : ℂ) • U z

namespace SmoothProfile

variable {P : SmoothProfile} {u : RepL2 ι} {ν : ℂ}

/-- **Eigenvectors of `L_{Dφ}` inside a nonzero eigenspace of `L_φ` are Laplace eigenfunctions**,
with eigenvalue `-κ/ν` of `-y²Δ`. -/
theorem isLaplaceEigen_eigenRep (hν : ν ≠ 0) (hu : P.repOp ρ u = ν • u) (hne : u ≠ 0)
    {κ : ℝ} (hκ : P.repLapOp ρ u = (κ : ℂ) • u) :
    IsLaplaceEigen ρ (-(κ / ν.re)) (P.eigenRep ρ ν u) := by
  have hνreal : ((ν.re : ℝ) : ℂ) = ν := by
    have hev : HasEigenvalue ((P.repOp ρ : RepL2 ι →L[ℂ] RepL2 ι) : RepL2 ι →ₗ[ℂ] RepL2 ι) ν :=
      hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 hu, hne⟩
    exact Complex.conj_eq_iff_re.1 (P.repOp_isSymmetric.conj_eigenvalue_eq_self hev)
  refine ⟨contDiffOn_eigenRep hν hu, P.equivariant_eigenRep ν _, P.memLp_eigenRep ν _, ?_⟩
  set U := P.eigenRep ρ ν u with hUdef
  have hAB : hypLap U =ᵐ[cellMeasure] ((κ / ν.re : ℝ) : ℂ) • U := by
    have h1 : ⇑((κ : ℂ) • u) =ᵐ[cellMeasure] ppApply ρ (radialLap P.toFun) ⇑u := by
      rw [← hκ]; exact P.repLapOp_coeFn u
    filter_upwards [h1, Lp.coeFn_smul (κ : ℂ) u, eigenRep_ae hν hu] with z hz1 hz2 hz3
    rw [hypLap_eigenRep hν hu, ppApply_congr_ae _ (eigenRep_ae hν hu)]
    simp only [Pi.smul_apply]
    rw [← hz1, hz2, Pi.smul_apply, ← hz3, smul_smul]
    congr 1
    rw [Complex.ofReal_div, hνreal]
    ring
  have hA := ppApply_hypLap_eigenRep hν hu
  have hB : ppApply ρ P.toFun (((κ / ν.re : ℝ) : ℂ) • U) = ν • (((κ / ν.re : ℝ) : ℂ) • U) := by
    rw [ppApply_smul, ppApply_eigenRep hν hu, smul_comm]
  have heq : ν • hypLap U = ν • (((κ / ν.re : ℝ) : ℂ) • U) := by
    rw [← hA, ← hB]
    exact ppApply_congr_ae _ hAB
  have heq' := smul_right_injective _ hν heq
  intro z
  rw [heq', neg_neg]
  rfl

end SmoothProfile

end

end GaloisForLFunctions.RHTower.RepPointPair
