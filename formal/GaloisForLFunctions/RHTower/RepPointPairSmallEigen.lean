import GaloisForLFunctions.RHTower.RepPointPairTopEigen
import GaloisForLFunctions.RHTower.SelbergTransformRealMonotone

/-!
# From the top eigenvalue of `L_φ` to a small Laplace eigenvalue

Let `φ` be a nonnegative `C³` profile and `m > h_φ(½)` an eigenvalue of `L_φ` with an eigenvector
orthogonal to the invariant constants.  The eigenspace is finite-dimensional, and both `L_{Dφ}` and the
orthogonal complement of the invariant constants preserve it, so `L_{Dφ}` has an eigenvector `u` there
(`exists_lap_eigenvector`).  Its continuous representative `U` is a Laplace eigenfunction,
`−y²ΔU = λU`, and Selberg's theorem gives `h_φ(s) = m` whenever `s(1 − s) = λ`
(`selbergTransform_eq_of_lapEigen`).  Locating `s`:

* `λ ≥ ¼`: `s = ½ + ir` and `m = |h_φ(½ + ir)| ≤ h_φ(½) < m`, impossible;
* `λ < 0`: `s > 1` real, and `m = h_φ(s)` exceeds the kernel mass `≥ ‖L_φ‖ ≥ m`, impossible.

Hence `0 ≤ λ < ¼` (`laplaceEigenvalue_mem_Ico`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology RCLike Module End
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.DeckPointPair (hypLap radialLap selbergTransform
  selbergRealTransform selbergTransform_ofReal norm_selbergTransform_half_add_le
  integral_pairKernel_lt_selbergRealTransform)

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

namespace SmoothProfile

variable (P : SmoothProfile)

/-- `L_{Dφ}` preserves the orthogonal complement of the invariant constants. -/
theorem repLapOp_mem_orthogonal {x : RepL2 ι} (hx : x ∈ (invConst ρ)ᗮ) :
    P.repLapOp ρ x ∈ (invConst ρ)ᗮ :=
  map_mem_orthogonal_of_invariant P.repLapOp_isSymmetric
    (fun _ hv => ppL2_mem_invConst _ _ _ _ hv) hx

/-- **A joint eigenvector.**  If the `m`-eigenspace of `L_φ` (`m ≠ 0`) is finite-dimensional and meets
the orthogonal complement of the invariant constants, then it contains a nonzero `u` in that
complement which is also an eigenvector of `L_{Dφ}` with a real eigenvalue. -/
theorem exists_lap_eigenvector {m : ℂ} (hm : m ≠ 0)
    (hfin : FiniteDimensional ℂ (eigenspace ((P.repOp ρ : RepL2 ι →L[ℂ] RepL2 ι) :
      End ℂ (RepL2 ι)) m))
    {x : RepL2 ι} (hx0 : x ≠ 0) (hxV : x ∈ (invConst ρ)ᗮ) (hx : P.repOp ρ x = m • x) :
    ∃ u : RepL2 ι, u ≠ 0 ∧ u ∈ (invConst ρ)ᗮ ∧ P.repOp ρ u = m • u ∧
      ∃ κ : ℝ, P.repLapOp ρ u = (κ : ℂ) • u := by
  set W : Submodule ℂ (RepL2 ι) :=
    eigenspace ((P.repOp ρ : RepL2 ι →L[ℂ] RepL2 ι) : End ℂ (RepL2 ι)) m ⊓ (invConst ρ)ᗮ
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_inf_left _ _
  have hxW : x ∈ W := ⟨mem_eigenspace_iff.2 hx, hxV⟩
  haveI : Nontrivial W := ⟨⟨⟨x, hxW⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  have hmaps : ∀ w ∈ W, ((P.repLapOp ρ : RepL2 ι →L[ℂ] RepL2 ι) : End ℂ (RepL2 ι)) w ∈ W := by
    rintro w ⟨hw1, hw2⟩
    refine ⟨mem_eigenspace_iff.2 (P.repLapOp_mem hm (mem_eigenspace_iff.1 hw1)), ?_⟩
    exact P.repLapOp_mem_orthogonal hw2
  set T : End ℂ W := LinearMap.restrict _ hmaps
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv0 : (v : RepL2 ι) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hTv : P.repLapOp ρ (v : RepL2 ι) = c • (v : RepL2 ι) := by
    have := congrArg Subtype.val (mem_eigenspace_iff.1 hv.1)
    simpa [T] using this
  have hcreal : ((c.re : ℝ) : ℂ) = c := by
    have hev : HasEigenvalue ((P.repLapOp ρ : RepL2 ι →L[ℂ] RepL2 ι) : RepL2 ι →ₗ[ℂ] RepL2 ι) c :=
      hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 hTv, hv0⟩
    exact Complex.conj_eq_iff_re.1 (P.repLapOp_isSymmetric.conj_eigenvalue_eq_self hev)
  refine ⟨v, hv0, v.2.2, mem_eigenspace_iff.1 v.2.1, c.re, ?_⟩
  rw [hcreal, hTv]

/-- The continuous representative of a nonzero `L²` field vanishes nowhere identically. -/
theorem exists_eigenRep_ne_zero {m : ℂ} (hm : m ≠ 0) {u : RepL2 ι} (hu : P.repOp ρ u = m • u)
    (hne : u ≠ 0) : ∃ z, P.eigenRep ρ m u z ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  rw [← toRepL2_eigenRep hm hu]
  have : P.eigenRep ρ m u = fun _ => 0 := funext h
  simp only [toRepL2, this]
  exact MemLp.toLp_zero _

/-- **Selberg's theorem fixes the eigenvalue**: if `L_φ u = m u`, `L_{Dφ} u = κ u`, `m ≠ 0`, `u ≠ 0`,
then `h_φ(s) = m` for every `s` with `s(1 − s) = −κ/m`. -/
theorem selbergTransform_eq_of_lapEigen {m : ℝ} (hm : m ≠ 0) {u : RepL2 ι}
    (hu : P.repOp ρ u = (m : ℂ) • u) (hne : u ≠ 0) {κ : ℝ} (hκ : P.repLapOp ρ u = (κ : ℂ) • u)
    {s : ℂ} (hs : s * (1 - s) = ((-(κ / m) : ℝ) : ℂ)) : selbergTransform P.toFun s = m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hL := isLaplaceEigen_eigenRep (ρ := ρ) hmC hu hne hκ
  rw [Complex.ofReal_re] at hL
  set U := P.eigenRep ρ (m : ℂ) u
  have hUeig : ∀ z, hypLap U z = (-(s * (1 - s))) • U z := by
    intro z
    rw [hL.eigen z, hs]
    push_cast
    ring_nf
  have h1 := fun z => ppApply_eigen P.contDiff.continuous P.kernelSupport' hL.contDiffOn
    hL.equivariant hUeig z
  have h2 := ppApply_eigenRep (P := P) (ρ := ρ) hmC hu
  obtain ⟨z, hz⟩ := P.exists_eigenRep_ne_zero hmC hu hne
  have h3 := congrFun h2 z
  rw [h1 z, Pi.smul_apply] at h3
  exact smul_left_injective ℂ hz h3

end SmoothProfile

/-- For a nonnegative profile, `h_{|φ|}(½)` is the real Selberg transform at `½`. -/
theorem halfTransform_eq_selbergReal {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u) :
    halfTransform (fun u => |φ u|) = selbergRealTransform φ (1 / 2) := by
  unfold halfTransform selbergRealTransform
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [sqrtIm, abs_of_nonneg (hφ0 _), Real.sqrt_eq_rpow]

/-- The norm of `L_φ` is at most the kernel mass. -/
theorem norm_ppL2_le {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    (hR : 0 ≤ R) (hφR : KernelSupport φ R) :
    ‖ppL2 ρ hφc hφM hR hφR‖ ≤ (ppKernelMass φ).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- For a nonnegative profile the kernel mass is `∫_ℍ φ(u(i, w)) dμ(w)`. -/
theorem ppKernelMass_toReal {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφR : KernelSupport φ R) : (ppKernelMass φ).toReal = kernelMassR φ := by
  have hint : Integrable (fun w : ℍ => φ (pairU UpperHalfPlane.I w)) := by
    refine (hφc.comp (continuous_pairU_right _)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_pairU_le UpperHalfPlane.I R) fun w hw => ?_
    simp only [Set.mem_setOf_eq, not_le] at hw
    exact hφR _ hw
  unfold ppKernelMass kernelMassR
  simp_rw [abs_of_nonneg (hφ0 _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => hφ0 _),
    ENNReal.toReal_ofReal (integral_nonneg fun w => hφ0 _)]

namespace SmoothProfile

variable (P : SmoothProfile)

/-- **The Laplace eigenvalue lies in `[0, ¼)`.**  Let `φ ≥ 0` be nontrivial, `L_φ u = m u`,
`L_{Dφ} u = κ u`, `u ≠ 0`, with `m > h_φ(½)`.  Then `λ = −κ/m` satisfies `0 ≤ λ < ¼`. -/
theorem laplaceEigenvalue_mem_Ico (hφ0 : ∀ u, 0 ≤ P.toFun u)
    (hne' : ∃ u₀, 0 ≤ u₀ ∧ P.toFun u₀ ≠ 0) {m : ℝ}
    (hmh : halfTransform (fun u => |P.toFun u|) < m) {u : RepL2 ι}
    (hu : P.repOp ρ u = (m : ℂ) • u) (hne : u ≠ 0) {κ : ℝ}
    (hκ : P.repLapOp ρ u = (κ : ℂ) • u) : 0 ≤ -(κ / m) ∧ -(κ / m) < 1 / 4 := by
  have hh0 := halfTransform_abs_nonneg P.toFun
  have hm0 : 0 < m := hh0.trans_lt hmh
  set lam := -(κ / m) with hlam
  have hdeck : DeckPointPair.KernelSupport P.toFun P.radius := P.kernelSupport'
  constructor
  · -- `λ < 0` would force `s > 1`
    by_contra hneg
    push Not at hneg
    set t := Real.sqrt (1 / 4 - lam)
    have ht2 : t ^ 2 = 1 / 4 - lam := Real.sq_sqrt (by linarith)
    have ht : 1 / 2 < t := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hs : ((1 / 2 + t : ℝ) : ℂ) * (1 - ((1 / 2 + t : ℝ) : ℂ)) = ((lam : ℝ) : ℂ) := by
      push_cast
      have : (t : ℂ) ^ 2 = ((1 / 4 - lam : ℝ) : ℂ) := by exact_mod_cast ht2
      push_cast at this
      linear_combination -this
    have heq := P.selbergTransform_eq_of_lapEigen hm0.ne' hu hne hκ hs
    rw [selbergTransform_ofReal] at heq
    have heqR : selbergRealTransform P.toFun (1 / 2 + t) = m := by exact_mod_cast heq
    have hlt := integral_pairKernel_lt_selbergRealTransform P.contDiff.continuous hφ0 hdeck hne'
      (σ := 1 / 2 + t) (by linarith)
    -- `m ≤ ‖L_φ‖ ≤ mass`
    have hnorm : m * ‖u‖ ≤ kernelMassR P.toFun * ‖u‖ := by
      have h1 : ‖P.repOp ρ u‖ = m * ‖u‖ := by
        rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      rw [← h1, ← ppKernelMass_toReal P.contDiff.continuous hφ0 P.kernelSupport']
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_ppL2_le _ _ _ _) (norm_nonneg _))
    have hmass : m ≤ kernelMassR P.toFun := le_of_mul_le_mul_right hnorm (norm_pos_iff.2 hne)
    unfold kernelMassR at hmass
    linarith
  · -- `λ ≥ ¼` would put `s` on the critical line
    by_contra hbig
    push Not at hbig
    set r := Real.sqrt (lam - 1 / 4)
    have hr2 : r ^ 2 = lam - 1 / 4 := Real.sq_sqrt (by linarith)
    have hs : (1 / 2 + (r : ℂ) * Complex.I) * (1 - (1 / 2 + (r : ℂ) * Complex.I)) =
        ((lam : ℝ) : ℂ) := by
      have : (r : ℂ) ^ 2 = ((lam - 1 / 4 : ℝ) : ℂ) := by exact_mod_cast hr2
      push_cast at this
      linear_combination this - (r : ℂ) ^ 2 * Complex.I_sq
    have heq := P.selbergTransform_eq_of_lapEigen hm0.ne' hu hne hκ hs
    have hle := norm_selbergTransform_half_add_le P.contDiff.continuous hφ0 hdeck r
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, selbergTransform_ofReal,
      Complex.ofReal_re, ← halfTransform_eq_selbergReal hφ0] at hle
    linarith

end SmoothProfile

end

end GaloisForLFunctions.RHTower.RepPointPair
