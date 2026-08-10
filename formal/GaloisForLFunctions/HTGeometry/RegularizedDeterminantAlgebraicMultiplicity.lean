import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceNegation
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNegation
import GaloisForLFunctions.HTGeometry.ReciprocalBallGeometry
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEigenvalueLimit
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantMultiplicityEventually
import GaloisForLFunctions.HTGeometry.RieszProjectionSchurCount
import Mathlib.Analysis.Analytic.Order

/-!
# Algebraic multiplicity of zeros of the Hilbert--Schmidt regularized determinant

Finite block determinants count Schur diagonal entries with multiplicity.  Signed reciprocal
inversion identifies that count with a Riesz spectral cluster of the negated kernel.  Operator-norm
convergence stabilizes the Riesz rank, and isolation of nonzero compact spectrum identifies the
limiting range with the maximal generalized eigenspace.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Matrix Metric Filter Polynomial

variable {ι : Type*} [DecidableEq ι]

/-- Every nonzero Schur diagonal entry of a finite block is outside the resolvent set of the
corresponding zero-padded finite-section operator. -/
theorem schur_diagonal_not_mem_resolventSet_toOperator_truncKernel
    {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι)
    {U T : Matrix (Fin (Fintype.card ↥s)) (Fin (Fintype.card ↥s)) ℂ}
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hT : T.BlockTriangular id)
    (hMT : Uᴴ * blockFin K s * U = T) (i : Fin (Fintype.card ↥s))
    : T i i ∉ resolventSet ℂ (toOperator (isHS_truncKernel hK s)) := by
  have hroot : Polynomial.eval (T i i) (blockFin K s).charpoly = 0 := by
    rw [charpoly_of_schur hU1 hU2 hT hMT, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hscalar : (Matrix.scalar _ (T i i)) *ᵥ v = T i i • v := by
    change (Matrix.diagonal (fun _ : Fin (Fintype.card ↥s) => T i i)) *ᵥ v = T i i • v
    exact Matrix.diagonal_const_mulVec (T i i) v
  have hveig : (blockFin K s) *ᵥ v = T i i • v := by
    rw [Matrix.sub_mulVec, hscalar] at hv
    exact (sub_eq_zero.mp hv).symm
  let w : lp (fun _ : ι => ℂ) 2 := liftBlockFinLinearMap s v
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    apply liftBlockFinLinearMap_injective s
    simpa [w] using hw
  have hlin : Matrix.toLin' (blockFin K s) v = T i i • v := by
    simpa [Matrix.toLin'_apply] using hveig
  have hweig : toOperator (isHS_truncKernel hK s) w = T i i • w := by
    calc
      toOperator (isHS_truncKernel hK s) w =
          liftBlockFinLinearMap s (Matrix.toLin' (blockFin K s) v) :=
        (liftBlockFinLinearMap_intertwines hK s v).symm
      _ = liftBlockFinLinearMap s (T i i • v) := by rw [hlin]
      _ = T i i • w := by simp [w]
  exact not_mem_resolventSet_of_eigenvector hw0 hweig

open scoped Classical in
/-- **At a reciprocal eigenvalue, the zero order of `det₂(I - zK)` equals algebraic
multiplicity.**  No normality or self-adjointness is assumed. -/
theorem analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace_and_finite_of_eigenvector
    {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} (hz₀0 : z₀ ≠ 0)
    {w : lp (fun _ : ι => ℂ) 2} (hw0 : w ≠ 0) (hw : toOperator hK w = z₀⁻¹ • w) :
    (analyticOrderAt (entireDet2 K) z₀ =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹) : ℕ∞)) ∧
      FiniteDimensional ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹) := by
  classical
  have horder_ne_top : analyticOrderAt (entireDet2 K) z₀ ≠ ⊤ := by
    intro htop
    have hAn : AnalyticOnNhd ℂ (entireDet2 K) Set.univ :=
      (differentiable_entireDet2 hK).differentiableOn.analyticOnNhd isOpen_univ
    have hzeroFun : entireDet2 K = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀ fun z =>
        hAn z (Set.mem_univ z)).mp htop
    have hzero0 : entireDet2 K 0 = 0 := congrFun hzeroFun 0
    have hone : entireDet2 K 0 = 1 := (isRegularizedDet_entireDet2 hK).eq_one_at_zero
    exact zero_ne_one (hzero0 ▸ hone)
  let d : ℕ := (analyticOrderAt (entireDet2 K) z₀).toNat
  have hord : analyticOrderAt (entireDet2 K) z₀ = (d : ℕ∞) :=
    (ENat.coe_toNat horder_ne_top).symm

  have hdetEvent := eventually_entireDet2_ne_zero hK z₀
  rw [eventually_nhdsWithin_iff] at hdetEvent
  obtain ⟨epsz, hepsz, hdetBall⟩ := Metric.eventually_nhds_iff.mp hdetEvent
  let Rz : ℝ := epsz / 2
  have hRz : 0 < Rz := by dsimp [Rz]; positivity
  have hdetIso : ∀ z ∈ closedBall z₀ Rz, z ≠ z₀ → entireDet2 K z ≠ 0 := by
    intro z hz hzz
    apply hdetBall
    · have hdist := mem_closedBall.mp hz
      dsimp [Rz] at hdist
      linarith
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff]

  let hKneg : IsHS (-K) := isHS_neg hK
  let S : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := toOperator hKneg
  let mu₀ : ℂ := -z₀⁻¹
  have hSneg : S = -toOperator hK := by
    dsimp [S, hKneg]
    exact toOperator_neg hK
  have hSweig : S w = mu₀ • w := by
    rw [hSneg, _root_.neg_apply, hw]
    simp [mu₀]
  have hmuSpec : mu₀ ∈ spectrum ℂ S := by
    simpa [spectrum] using not_mem_resolventSet_of_eigenvector hw0 hSweig
  have hScompact : IsCompactOperator S :=
    (isHilbertSchmidt_toOperator hKneg).isCompactOperator
  obtain ⟨A, hA, hAmu, hSiso⟩ :=
    exists_isolating_closedBall_nonzero_spectrum_general hScompact hmuSpec
      (by simp [mu₀, hz₀0])

  have hdelta : 0 < min Rz (‖z₀‖ / 2) :=
    lt_min hRz (by exact half_pos (norm_pos_iff.mpr hz₀0))
  obtain ⟨r, a, hr, hrdelta, ha, haA, hzToMu, hmuToZ⟩ :=
    exists_nested_balls_signed_reciprocal hz₀0 (mu₀ := mu₀) rfl hA hdelta
  have hrRz : r < Rz := lt_of_lt_of_le hrdelta (min_le_left _ _)
  have hrNorm : r < ‖z₀‖ := by
    calc
      r < min Rz (‖z₀‖ / 2) := hrdelta
      _ ≤ ‖z₀‖ / 2 := min_le_right _ _
      _ < ‖z₀‖ := half_lt_self (norm_pos_iff.mpr hz₀0)
  have haNorm : a < ‖mu₀‖ := lt_trans haA hAmu
  have hzBallZero : (0 : ℂ) ∉ closedBall z₀ r := by
    intro hzero
    have hd := mem_closedBall.mp hzero
    rw [Complex.dist_eq, zero_sub, norm_neg] at hd
    linarith
  have hmuBallZero : (0 : ℂ) ∉ closedBall mu₀ a := by
    intro hzero
    have hd := mem_closedBall.mp hzero
    rw [Complex.dist_eq, zero_sub, norm_neg] at hd
    linarith

  have hSres : ∀ nu ∈ closedBall mu₀ A \ ball mu₀ a, nu ∈ resolventSet ℂ S := by
    intro nu hnu
    apply hSiso nu hnu.1
    intro hEq
    subst nu
    exact hnu.2 (mem_ball_self ha)
  obtain ⟨epsop, hepsop, hstable⟩ :=
    exists_eps_finrank_range_rieszProjection_eq S ha haA hSres
  have hclose : ∀ᶠ s : Finset ι in atTop,
      ‖toOperator (isHS_truncKernel hKneg s) - S‖ < epsop := by
    exact (tendsto_norm_toOperator_truncKernel_sub hKneg).eventually
      (eventually_lt_nhds hepsop)

  choose U T hSchur using fun s : Finset ι =>
    exists_schur_triangulation (Fintype.card ↥s) (blockFin (-K) s)
  have hU1 (s : Finset ι) : (U s)ᴴ * U s = 1 := (hSchur s).1
  have hU2 (s : Finset ι) : U s * (U s)ᴴ = 1 := (hSchur s).2.1
  have hT (s : Finset ι) : (T s).BlockTriangular id := (hSchur s).2.2.1
  have hMT (s : Finset ι) : (U s)ᴴ * blockFin (-K) s * U s = T s :=
    (hSchur s).2.2.2
  have hMTdet (s : Finset ι) : (U s)ᴴ * (-(blockFin K s)) * U s = T s := by
    simpa [blockFin_neg] using hMT s

  have hdetCount : ∀ᶠ s : Finset ι in atTop,
      (Finset.univ.filter fun i =>
        T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card = d :=
    eventually_schurCount_eq_analyticOrder' hK hr hrRz hord hdetIso U T hU1 hU2 hT hMTdet

  have hRieszCount : ∀ᶠ s : Finset ι in atTop,
      Module.finrank ℂ (LinearMap.range
        ((rieszProjection (toOperator (isHS_truncKernel hKneg s)) mu₀ a :
          lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
          lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) =
        (Finset.univ.filter fun i => T s i i ≠ 0 ∧ T s i i ∈ ball mu₀ a).card := by
    filter_upwards [hclose] with s hs
    have hst := hstable (toOperator (isHS_truncKernel hKneg s)) hs
    exact finrank_range_rieszProjection_toOperator_truncKernel_eq_schurCount
      hKneg s ha haA hst.1 hmuBallZero (U s) (T s)
        (hU1 s) (hU2 s) (hT s) (hMT s)

  have hCountEq : ∀ᶠ s : Finset ι in atTop,
      (Finset.univ.filter fun i => T s i i ≠ 0 ∧ T s i i ∈ ball mu₀ a).card =
      (Finset.univ.filter fun i => T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card := by
    filter_upwards [hclose] with s hs
    have hst := hstable (toOperator (isHS_truncKernel hKneg s)) hs
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi0, hi⟩
      exact ⟨hi0, hmuToZ (T s i i) hi⟩
    · rintro ⟨hi0, hi⟩
      refine ⟨hi0, ?_⟩
      have hiOuter : T s i i ∈ ball mu₀ A := by
        have := hzToMu (-(T s i i)⁻¹) hi
        simpa [hi0] using this
      by_contra hiInner
      have hiAnn : T s i i ∈ closedBall mu₀ A \ ball mu₀ a :=
        ⟨ball_subset_closedBall hiOuter, hiInner⟩
      exact (schur_diagonal_not_mem_resolventSet_toOperator_truncKernel
        hKneg s (hU1 s) (hU2 s) (hT s) (hMT s) i) (hst.1 _ hiAnn)

  have hAll : ∀ᶠ s : Finset ι in atTop,
      ‖toOperator (isHS_truncKernel hKneg s) - S‖ < epsop ∧
      (Finset.univ.filter fun i =>
        T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card = d ∧
      Module.finrank ℂ (LinearMap.range
        ((rieszProjection (toOperator (isHS_truncKernel hKneg s)) mu₀ a :
          lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
          lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) =
        (Finset.univ.filter fun i => T s i i ≠ 0 ∧ T s i i ∈ ball mu₀ a).card ∧
      (Finset.univ.filter fun i => T s i i ≠ 0 ∧ T s i i ∈ ball mu₀ a).card =
        (Finset.univ.filter fun i =>
          T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card := by
    filter_upwards [hclose, hdetCount, hRieszCount, hCountEq] with s hs hd hc he
    exact ⟨hs, hd, hc, he⟩
  obtain ⟨s, hsclose, hsdet, hsRiesz, hsCount⟩ := Filter.Eventually.exists hAll
  have hst := hstable (toOperator (isHS_truncKernel hKneg s)) hsclose
  have hsSphere : ∀ nu ∈ sphere mu₀ a,
      nu ∈ resolventSet ℂ (toOperator (isHS_truncKernel hKneg s)) := by
    intro nu hnu
    apply hst.1 nu
    exact ⟨by rw [mem_closedBall, mem_sphere.mp hnu]; linarith,
      by rw [mem_ball, mem_sphere.mp hnu]; linarith⟩
  have hfinSection : FiniteDimensional ℂ (LinearMap.range
      ((rieszProjection (toOperator (isHS_truncKernel hKneg s)) mu₀ a :
        lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
        lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) :=
    finiteDimensional_range_rieszProjection_toOperator_truncKernel
      hKneg s ha.le hsSphere hmuBallZero
  have hfinLimit : FiniteDimensional ℂ (LinearMap.range
      ((rieszProjection S mu₀ a :
        lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
        lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) :=
    hst.2.2 hfinSection
  letI : FiniteDimensional ℂ (LinearMap.range
      ((rieszProjection S mu₀ a :
        lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
        lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)) := hfinLimit
  have hSSphere : ∀ nu ∈ sphere mu₀ a, nu ∈ resolventSet ℂ S := by
    intro nu hnu
    apply hSres nu
    exact ⟨by rw [mem_closedBall, mem_sphere.mp hnu]; linarith,
      by rw [mem_ball, mem_sphere.mp hnu]; linarith⟩
  have hSP : rieszProjection S mu₀ a * rieszProjection S mu₀ a = rieszProjection S mu₀ a :=
    rieszProjection_mul_self S ha haA hSres
  have hSep : ∀ nu : ℂ, nu ≠ mu₀ →
      (∃ v, v ≠ 0 ∧ S v = nu • v) → nu ∉ closedBall mu₀ a := by
    rintro nu hne ⟨v, hv0, hveig⟩ hnu
    exact (not_mem_resolventSet_of_eigenvector hv0 hveig)
      (hSiso nu (Metric.closedBall_subset_closedBall haA.le hnu) hne)
  have hRange : LinearMap.range ((rieszProjection S mu₀ a :
      lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) =
      Module.End.maxGenEigenspace (S :
        lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) mu₀ :=
    range_rieszProjection_eq_maxGenEigenspace ha.le hSSphere (mem_ball_self ha)
      hSP hSep inferInstance
  have hRankLimit : Module.finrank ℂ (Module.End.maxGenEigenspace (S :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) mu₀) = d := by
    rw [← hRange, hst.2.1, hsRiesz, hsCount, hsdet]
  have hGenNeg : Module.End.maxGenEigenspace (S :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) mu₀ =
      Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹ := by
    rw [hSneg]
    simpa [mu₀] using maxGenEigenspace_neg_neg
      (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹
  constructor
  · rw [hord, ← hRankLimit, hGenNeg]
  · rw [← hGenNeg, ← hRange]
    exact hfinLimit

/-- Equality half of the reciprocal-eigenvalue multiplicity theorem. -/
theorem analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace_of_eigenvector
    {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} (hz₀0 : z₀ ≠ 0)
    {w : lp (fun _ : ι => ℂ) 2} (hw0 : w ≠ 0) (hw : toOperator hK w = z₀⁻¹ • w) :
    analyticOrderAt (entireDet2 K) z₀ =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹) : ℕ∞) :=
  (analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace_and_finite_of_eigenvector
    hK hz₀0 hw0 hw).1

/-- **Every nonzero determinant zero has its exact compact-operator algebraic multiplicity.** -/
theorem analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace
    {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} (hz₀ : entireDet2 K z₀ = 0) :
    analyticOrderAt (entireDet2 K) z₀ =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹) : ℕ∞) := by
  have hz₀0 : z₀ ≠ 0 := by
    intro hzero
    subst z₀
    have hone : entireDet2 K 0 = 1 := (isRegularizedDet_entireDet2 hK).eq_one_at_zero
    rw [hz₀] at hone
    exact zero_ne_one hone
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector_of_entireDet2_eq_zero hK hz₀0 hz₀
  exact analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace_of_eigenvector
    hK hz₀0 hw0 hw

/-- **The Hilbert--Carleman determinant vanishes exactly at reciprocal nonzero eigenvalues.** -/
theorem entireDet2_eq_zero_iff_exists_eigenvector {K : ι × ι → ℂ} (hK : IsHS K)
    {z₀ : ℂ} (hz₀0 : z₀ ≠ 0) :
    entireDet2 K z₀ = 0 ↔
      ∃ w : lp (fun _ : ι => ℂ) 2, w ≠ 0 ∧ toOperator hK w = z₀⁻¹ • w := by
  constructor
  · exact exists_eigenvector_of_entireDet2_eq_zero hK hz₀0
  · rintro ⟨w, hw0, hw⟩
    have hmult :=
      analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace_and_finite_of_eigenvector
        hK hz₀0 hw0 hw
    letI : FiniteDimensional ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹) := hmult.2
    have hwmem : w ∈ Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹ := by
      apply Module.End.eigenspace_le_maxGenEigenspace
      exact Module.End.mem_eigenspace_iff.mpr (by simpa using hw)
    have hpos : 0 < Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z₀⁻¹) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨w, hwmem⟩, fun hzero => hw0 (congrArg Subtype.val hzero)⟩
    have hord_ne : analyticOrderAt (entireDet2 K) z₀ ≠ 0 := by
      rw [hmult.1]
      simp [Nat.ne_of_gt hpos]
    have hAn : AnalyticAt ℂ (entireDet2 K) z₀ :=
      ((differentiable_entireDet2 hK).differentiableOn.analyticOnNhd isOpen_univ)
        z₀ (Set.mem_univ z₀)
    by_contra hne
    exact hord_ne (hAn.analyticOrderAt_eq_zero.mpr hne)

end GaloisForLFunctions.HTGeometry
