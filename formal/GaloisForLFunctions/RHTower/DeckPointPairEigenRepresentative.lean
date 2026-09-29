import GaloisForLFunctions.RHTower.DeckPointPairSelbergTransform

/-!
# Continuous representatives of the eigenvectors of a point-pair operator

For a `C³` profile `φ` vanishing for `|u| > R` both `φ` and `Dφ = u(u+1)φ'' + (2u+1)φ'` are `C¹`
point-pair profiles.  If `u` is a cuspidal eigenvector of `L_φ` with eigenvalue `ν ≠ 0`, then
`U = ν⁻¹ L_φ u` is a representative of `u` with `U = L_φ(ν⁻¹U)`; hence `U` is `C²`,
`y²ΔU = ν⁻¹ L_{Dφ} U`, and the Green identity gives `L_φ(y²ΔU) = ν y²ΔU`.  Consequently `L_{Dφ}`
maps the `ν`-eigenspace of `L_φ` into itself, and an eigenvector of `L_{Dφ}` with eigenvalue `κ`
inside it is a cuspidal Laplace eigenfunction with `-y²ΔU = -(κ/ν) U`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Module End
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

theorem exists_abs_le_of_support {f : ℝ → ℝ} (hf : Continuous f) {R : ℝ}
    (hs : ∀ u, R < |u| → f u = 0) : ∃ M, ∀ u, |f u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, fun u => ?_⟩
  by_cases hu : R < |u|
  · rw [hs u hu, abs_zero]; exact le_max_right _ _
  · have hmem : u ∈ Icc (-R) R := abs_le.1 (not_lt.1 hu)
    have := hM u hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

theorem deriv_eq_zero_of_abs_support {f : ℝ → ℝ} {R : ℝ} (hs : ∀ u, R < |u| → f u = 0) {u : ℝ}
    (hu : R < |u|) : deriv f u = 0 := by
  have hopen : IsOpen {u : ℝ | R < |u|} := isOpen_lt continuous_const continuous_abs
  have h : f =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hu] with v hv using hs v hv
  rw [h.deriv_eq, deriv_const]

theorem deckEquivariant_smul {F : ℍ → DeckSpace N} (c : ℂ) (hF : deckEquivariant N F) :
    deckEquivariant N (c • F) := fun A z => by
  simp only [Pi.smul_apply, hF A z, map_smul]

/-- A `C¹` profile supported in `[-R, R]` as a point-pair profile. -/
def PairProfile.ofContDiff (f : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (hf : ContDiff ℝ 1 f)
    (hs : ∀ u, R < |u| → f u = 0) : PairProfile where
  toFun := f
  radius := R
  bound := Classical.choose (exists_abs_le_of_support hf.continuous hs)
  derivBound := Classical.choose (exists_abs_le_of_support (contDiff_one_iff_deriv.1 hf).2
    fun _ hu => deriv_eq_zero_of_abs_support hs hu)
  radius_nonneg := hR
  differentiable := hf.differentiable (by norm_num)
  continuous_deriv := (contDiff_one_iff_deriv.1 hf).2
  abs_le := Classical.choose_spec (exists_abs_le_of_support hf.continuous hs)
  abs_deriv_le := Classical.choose_spec (exists_abs_le_of_support
    (contDiff_one_iff_deriv.1 hf).2 fun _ hu => deriv_eq_zero_of_abs_support hs hu)
  support u hu := hs u (lt_of_lt_of_le hu (le_abs_self u))

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

theorem kernelSupport : KernelSupport P.toFun P.radius := fun u hu =>
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

/-- The point-pair profile of `φ`. -/
def pp : PairProfile :=
  PairProfile.ofContDiff P.toFun P.radius P.radius_nonneg (P.contDiff.of_le (by norm_num)) P.support

/-- The point-pair profile of `Dφ`. -/
def lap : PairProfile :=
  PairProfile.ofContDiff (radialLap P.toFun) P.radius P.radius_nonneg P.contDiff_radialLap
    P.radialLap_support

@[simp] theorem pp_toFun : P.pp.toFun = P.toFun := rfl

@[simp] theorem lap_toFun : P.lap.toFun = radialLap P.toFun := rfl

/-! ## The continuous representative of an eigenvector -/

/-- The representative `ν⁻¹ L_φ u`. -/
def eigenRep (ν : ℂ) (u : DeckL2 N) : ℍ → DeckSpace N := ν⁻¹ • ppApply P.toFun ⇑u

theorem ppApply_ae_of_eigen {u : CuspidalL2 N} {ν : ℂ} (hu : P.pp.cuspOp N u = ν • u) :
    ppApply P.toFun ⇑(u : DeckL2 N) =ᵐ[cellMeasure] ν • ⇑(u : DeckL2 N) := by
  have h2 : P.pp.op N (u : DeckL2 N) = ν • (u : DeckL2 N) := by
    have := congrArg (fun x : CuspidalL2 N => (x : DeckL2 N)) hu
    simpa [PairProfile.coe_cuspOp] using this
  have h1 : ⇑(ν • (u : DeckL2 N)) =ᵐ[cellMeasure] ppApply P.toFun ⇑(u : DeckL2 N) := by
    rw [← h2]; exact P.pp.op_coeFn (u : DeckL2 N)
  filter_upwards [h1, Lp.coeFn_smul ν (u : DeckL2 N)] with z hz1 hz2
  rw [← hz1, hz2]

section Eigen

variable {P} {u : CuspidalL2 N} {ν : ℂ} (hν : ν ≠ 0) (hu : P.pp.cuspOp N u = ν • u)
include hν hu

theorem eigenRep_ae : P.eigenRep ν (u : DeckL2 N) =ᵐ[cellMeasure] ⇑(u : DeckL2 N) := by
  filter_upwards [P.ppApply_ae_of_eigen hu] with z hz
  simp only [eigenRep, Pi.smul_apply]
  rw [hz, Pi.smul_apply, smul_smul, inv_mul_cancel₀ hν, one_smul]

theorem ppApply_eigenRep :
    ppApply P.toFun (P.eigenRep ν (u : DeckL2 N)) = ν • P.eigenRep ν (u : DeckL2 N) := by
  rw [ppApply_congr_ae _ (eigenRep_ae hν hu)]
  funext z
  simp [eigenRep, smul_smul, mul_inv_cancel₀ hν]

theorem eigenRep_eq_ppApply :
    P.eigenRep ν (u : DeckL2 N) = ppApply P.toFun (ν⁻¹ • P.eigenRep ν (u : DeckL2 N)) := by
  rw [ppApply_smul, ppApply_eigenRep hν hu, smul_smul, inv_mul_cancel₀ hν, one_smul]

omit hν hu in
theorem continuous_eigenRep (ν : ℂ) (u : DeckL2 N) : Continuous (P.eigenRep ν u) :=
  (continuous_ppApply P.pp.differentiable.continuous P.pp.abs_le P.kernelSupport
    (Lp.memLp u)).const_smul _

omit hν hu in
theorem equivariant_eigenRep (ν : ℂ) (u : DeckL2 N) : deckEquivariant N (P.eigenRep ν u) :=
  deckEquivariant_smul _ fun A z => ppApply_smul_point P.kernelSupport _ A z

omit hν hu in
theorem memLp_eigenRep (ν : ℂ) (u : DeckL2 N) : MemLp (P.eigenRep ν u) 2 cellMeasure :=
  (memLp_ppApply P.pp.differentiable.continuous P.pp.abs_le P.radius_nonneg P.kernelSupport
    (Lp.memLp u)).const_smul _

theorem toDeckL2_eigenRep :
    toDeckL2 (P.eigenRep ν (u : DeckL2 N)) (P.memLp_eigenRep ν _) = (u : DeckL2 N) := by
  rw [toDeckL2, MemLp.toLp_congr _ (Lp.memLp _) (eigenRep_ae hν hu), Lp.toLp_coeFn]

theorem contDiffOn_eigenRep :
    ContDiffOn ℝ 2 (fun ζ => P.eigenRep ν (u : DeckL2 N) (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} := by
  rw [show (fun ζ => P.eigenRep ν (u : DeckL2 N) (ofComplex ζ)) =
      fun ζ => ppApply P.toFun (ν⁻¹ • P.eigenRep ν (u : DeckL2 N)) (ofComplex ζ) by
    rw [← eigenRep_eq_ppApply hν hu]]
  exact contDiffOn_two_ppApply P.contDiff_two P.kernelSupport
    ((P.continuous_eigenRep ν _).const_smul _) (deckEquivariant_smul _ (P.equivariant_eigenRep ν _))

theorem hypLap_eigenRep : hypLap (P.eigenRep ν (u : DeckL2 N)) =
    ν⁻¹ • ppApply (radialLap P.toFun) (P.eigenRep ν (u : DeckL2 N)) := by
  funext w
  conv_lhs => rw [eigenRep_eq_ppApply hν hu]
  rw [hypLap_ppApply P.contDiff_two P.kernelSupport ((P.continuous_eigenRep ν _).const_smul _)
    (deckEquivariant_smul _ (P.equivariant_eigenRep ν _)) w, ppApply_smul]

theorem ppApply_hypLap_eigenRep : ppApply P.toFun (hypLap (P.eigenRep ν (u : DeckL2 N))) =
    ν • hypLap (P.eigenRep ν (u : DeckL2 N)) := by
  funext z
  rw [ppApply_hypLap P.contDiff_two P.radius_nonneg P.kernelSupport (contDiffOn_eigenRep hν hu)
    (P.equivariant_eigenRep ν _) z, hypLap_eigenRep hν hu]
  simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hν, one_smul]

/-- **`L_{Dφ}` preserves the eigenspaces of `L_φ`.** -/
theorem lap_cuspOp_mem :
    P.pp.cuspOp N (P.lap.cuspOp N u) = ν • P.lap.cuspOp N u := by
  apply Subtype.ext
  change P.pp.op N (P.lap.op N (u : DeckL2 N)) = ν • P.lap.op N (u : DeckL2 N)
  have e1 : ppApply (radialLap P.toFun) ⇑(u : DeckL2 N) =
      ν • hypLap (P.eigenRep ν (u : DeckL2 N)) := by
    rw [← ppApply_congr_ae _ (eigenRep_ae hν hu), hypLap_eigenRep hν hu, smul_smul,
      mul_inv_cancel₀ hν, one_smul]
  have key : ppApply P.toFun ⇑(P.lap.op N (u : DeckL2 N)) =
      ν • ppApply (radialLap P.toFun) ⇑(u : DeckL2 N) := by
    rw [ppApply_congr_ae _ (P.lap.op_coeFn _), lap_toFun, e1, ppApply_smul,
      ppApply_hypLap_eigenRep hν hu]
  apply Lp.ext
  filter_upwards [P.pp.op_coeFn (P.lap.op N (u : DeckL2 N)),
    Lp.coeFn_smul ν (P.lap.op N (u : DeckL2 N)), P.lap.op_coeFn (u : DeckL2 N)] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  exact congrFun key z

end Eigen

end SmoothProfile

/-- A cuspidal Laplace eigenfunction: a `C²`, deck-equivariant, square-integrable `U` with
cuspidal class and `-y²ΔU = λ U`. -/
structure IsCuspLaplaceEigen (N : ℕ) (lam : ℝ) (U : ℍ → DeckSpace N) : Prop where
  contDiffOn : ContDiffOn ℝ 2 (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}
  equivariant : deckEquivariant N U
  memLp : MemLp U 2 cellMeasure
  cuspidal : toDeckL2 U memLp ∈ cuspidalL2Closure N
  eigen : ∀ z, hypLap U z = ((-lam : ℝ) : ℂ) • U z

namespace SmoothProfile

variable {P : SmoothProfile} {u : CuspidalL2 N} {ν : ℂ}

/-- **Eigenvectors of `L_{Dφ}` inside a nonzero eigenspace of `L_φ` are Laplace
eigenfunctions**, with eigenvalue `-κ/ν` of `-y²Δ`. -/
theorem isCuspLaplaceEigen_eigenRep (hν : ν ≠ 0) (hu : P.pp.cuspOp N u = ν • u) (hne : u ≠ 0)
    {κ : ℝ} (hκ : P.lap.cuspOp N u = (κ : ℂ) • u) :
    IsCuspLaplaceEigen N (-(κ / ν.re)) (P.eigenRep ν (u : DeckL2 N)) := by
  have hνreal : ((ν.re : ℝ) : ℂ) = ν := by
    have hev : HasEigenvalue ((P.pp.cuspOp N : CuspidalL2 N →L[ℂ] CuspidalL2 N) :
        CuspidalL2 N →ₗ[ℂ] CuspidalL2 N) ν :=
      hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 hu, hne⟩
    exact Complex.conj_eq_iff_re.1 ((P.pp.cuspOp_isSymmetric (N := N)).conj_eigenvalue_eq_self hev)
  refine ⟨contDiffOn_eigenRep hν hu, P.equivariant_eigenRep ν _, P.memLp_eigenRep ν _,
    by rw [toDeckL2_eigenRep hν hu]; exact u.2, ?_⟩
  set U := P.eigenRep ν (u : DeckL2 N) with hUdef
  have hlap : P.lap.op N (u : DeckL2 N) = (κ : ℂ) • (u : DeckL2 N) := by
    rw [← PairProfile.coe_cuspOp, hκ]
    rfl
  have hAB : hypLap U =ᵐ[cellMeasure] ((κ / ν.re : ℝ) : ℂ) • U := by
    have h1 : ⇑((κ : ℂ) • (u : DeckL2 N)) =ᵐ[cellMeasure]
        ppApply (radialLap P.toFun) ⇑(u : DeckL2 N) := by
      rw [← hlap]; exact P.lap.op_coeFn (u : DeckL2 N)
    filter_upwards [h1, Lp.coeFn_smul (κ : ℂ) (u : DeckL2 N), eigenRep_ae hν hu] with z hz1 hz2 hz3
    rw [hypLap_eigenRep hν hu, ppApply_congr_ae _ (eigenRep_ae hν hu)]
    simp only [Pi.smul_apply]
    rw [← hz1, hz2, Pi.smul_apply, ← hz3, smul_smul]
    congr 1
    rw [Complex.ofReal_div, hνreal]
    ring
  have hA := ppApply_hypLap_eigenRep hν hu
  have hB : ppApply P.toFun (((κ / ν.re : ℝ) : ℂ) • U) = ν • (((κ / ν.re : ℝ) : ℂ) • U) := by
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

end GaloisForLFunctions.RHTower.DeckPointPair
