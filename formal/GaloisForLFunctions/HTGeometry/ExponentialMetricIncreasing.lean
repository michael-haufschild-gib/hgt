import GaloisForLFunctions.HTGeometry.FlatGeodesicIsometry
import GaloisForLFunctions.HTGeometry.GoldenThompsonNorm

/-!
# The exponential metric increasing property

The distance between two observer metrics dominates the spectrum of the difference of their
directions:

```text
∀ i, (S - T).eigenvalues i ≤ observerDist (exp T) (exp S).
```

So two rays whose directions differ diverge: for traceless directions `T ≠ S` the difference has a
positive eigenvalue, and by homogeneity `observerDist (exp (t T)) (exp (t S)) ≥ t · c` with `c > 0`.
Inside one flat this was the Euclidean computation of the previous module; the general case is
exactly the exponential metric increasing property, and its analytic input is the Golden–Thompson
inequality for the norm.

The chain is: the distance dominates the logarithm of the operator norm of the relative form, the
relative form is `exp (-T/2) exp S exp (-T/2)` whose norm is `‖exp (S/2) exp (-T/2)‖ ^ 2`, and
Golden–Thompson bounds that below by `‖exp ((S - T)/2)‖ ^ 2 = ‖exp (S - T)‖`, whose norm is at
least the exponential of any eigenvalue of `S - T`.
-/

namespace GaloisForLFunctions.HTGeometry

open Module NormedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The operator norm of a diagonal operator -/

omit [FiniteDimensional ℂ E] in
theorem norm_sq_eq_sum_repr_of_frame (b : OrthonormalBasis (Fin n) ℂ E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖b.repr v i‖ ^ 2 := by
  have h := inner_self_of_diagonal b (f := LinearMap.id) (d := fun _ => (1 : ℝ))
    (fun i => by simp) v
  rw [LinearMap.id_apply] at h
  have h2 : RCLike.re (inner ℂ v v : ℂ) = ∑ i, 1 * ‖b.repr v i‖ ^ 2 := by
    rw [h]
    simp [-Complex.ofReal_pow]
  rw [inner_self_eq_norm_sq] at h2
  simpa using h2

theorem diagOp_comp_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (w w' : Fin n → ℝ) :
    diagOp b w ∘ₗ diagOp b w' = diagOp b (fun i => w i * w' i) := by
  refine Basis.ext b.toBasis fun i => ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagOp_apply_basis, map_smul,
    diagOp_apply_basis, diagOp_apply_basis, smul_smul]
  congr 1
  push_cast
  ring

theorem norm_diagOp_apply_le (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ i, |w i| ≤ c) (v : E) : ‖diagOp b w v‖ ≤ c * ‖v‖ := by
  have hsym := isSymmetric_diagOp b w
  have hinner : (inner ℂ (diagOp b w v) (diagOp b w v) : ℂ)
      = ((∑ i, (w i * w i) * ‖b.repr v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsym v (diagOp b w v)]
    have hd : ∀ i, (diagOp b w ∘ₗ diagOp b w) (b i) = ((w i * w i : ℝ) : ℂ) • b i := by
      intro i
      rw [diagOp_comp_diagOp, diagOp_apply_basis]
    have := inner_self_of_diagonal b (f := diagOp b w ∘ₗ diagOp b w)
      (d := fun i => w i * w i) hd v
    rw [LinearMap.comp_apply] at this
    exact this
  have hnormsq : ‖diagOp b w v‖ ^ 2 = ∑ i, (w i * w i) * ‖b.repr v i‖ ^ 2 := by
    have h : RCLike.re (inner ℂ (diagOp b w v) (diagOp b w v) : ℂ)
        = ∑ i, (w i * w i) * ‖b.repr v i‖ ^ 2 := by
      rw [hinner]
      simp [-Complex.ofReal_pow]
    rwa [inner_self_eq_norm_sq] at h
  have hbound : ‖diagOp b w v‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by
    rw [hnormsq, mul_pow, norm_sq_eq_sum_repr_of_frame b v, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := abs_le.1 (hc i)
    nlinarith [abs_nonneg (w i), sq_abs (w i), hc0]
  nlinarith [hbound, norm_nonneg (diagOp b w v), mul_nonneg hc0 (norm_nonneg v)]

theorem norm_toCLM_diagOp_le (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ i, |w i| ≤ c) :
    ‖LinearMap.toContinuousLinearMap (diagOp b w)‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc0 fun v => norm_diagOp_apply_le b w hc0 hc v

theorem eq_diagOp_of_apply (b : OrthonormalBasis (Fin n) ℂ E) {f : E →ₗ[ℂ] E} {w : Fin n → ℝ}
    (hd : ∀ i, f (b i) = ((w i : ℝ) : ℂ) • b i) : f = diagOp b w := by
  refine Basis.ext b.toBasis fun i => ?_
  rw [OrthonormalBasis.coe_toBasis, hd i, diagOp_apply_basis]

/-! ## Passing between linear maps and continuous linear maps -/

theorem toCLM_comp (f g : E →ₗ[ℂ] E) :
    LinearMap.toContinuousLinearMap (f ∘ₗ g)
      = LinearMap.toContinuousLinearMap f * LinearMap.toContinuousLinearMap g := by
  ext v
  rfl

theorem toCLM_metricRay (T : E →ₗ[ℂ] E) (t : ℝ) :
    LinearMap.toContinuousLinearMap ((metricRay T t : E →ₗ[ℂ] E)) = metricRay T t := by
  ext v
  rfl

theorem metricRay_eq_exp_smul (T : E →ₗ[ℂ] E) (t : ℝ) :
    (metricRay T t : E →L[ℂ] E)
      = NormedSpace.exp (t • (LinearMap.toContinuousLinearMap T)) := by
  rw [metricRay]
  congr 1

theorem isSelfAdjoint_toCLM {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) :
    IsSelfAdjoint (LinearMap.toContinuousLinearMap T) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hT

/-! ## The exponential dominates the exponential of each eigenvalue -/

theorem exp_le_norm_metricRay_of_eigenvector {D : E →ₗ[ℂ] E} {μ : ℝ} {v : E} (hv : v ≠ 0)
    (hev : D v = ((μ : ℝ) : ℂ) • v) : Real.exp μ ≤ ‖(metricRay D 1 : E →L[ℂ] E)‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h := (metricRay D 1 : E →L[ℂ] E).le_opNorm v
  rw [show (metricRay D 1 : E →L[ℂ] E) v = ((Real.exp (1 * μ) : ℝ) : ℂ) • v from
      metricRay_apply_of_eigenvector hev 1,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] at h
  exact le_of_mul_le_mul_right (by linarith [h]) hvpos

/-! ## The inverse square root of a ray -/

theorem sqrt_exp_real (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have h : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]
    ring_nf
  rw [← h, Real.sqrt_mul_self (Real.exp_nonneg _)]

theorem invSqrtOp_metricRay {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n) :
    invSqrtOp (isSymmetric_metricRay hT hn 1) hn = ((metricRay T (-(2 : ℝ)⁻¹) : E →ₗ[ℂ] E)) := by
  set u := hT.eigenvectorBasis hn with hu
  set τ := hT.eigenvalues hn with hτ
  have hray : ∀ i, ((metricRay T 1 : E →ₗ[ℂ] E)) (u i)
      = ((Real.exp (1 * τ i) : ℝ) : ℂ) • u i := fun i => metricRay_eigenvectorBasis hT hn i 1
  have hpos : ∀ i, 0 < Real.exp (1 * τ i) := fun i => Real.exp_pos _
  have hsqrt : sqrtOp (isSymmetric_metricRay hT hn 1) hn
      = diagOp u (fun i => Real.sqrt (Real.exp (1 * τ i))) :=
    sqrtOp_eq_diagOp u hn (isSymmetric_metricRay hT hn 1) hray hpos
  have hinv : invSqrtOp (isSymmetric_metricRay hT hn 1) hn
      = diagOp u (fun i => (Real.sqrt (Real.exp (1 * τ i)))⁻¹) := by
    rw [invSqrtOp, invOp_congr (isSymmetric_sqrtOp (isSymmetric_metricRay hT hn 1) hn)
      (isSymmetric_diagOp u fun i => Real.sqrt (Real.exp (1 * τ i))) hn hsqrt]
    exact invOp_eq_diagOp u hn (isSymmetric_diagOp u _) (diagOp_apply_basis u _)
      fun i => Real.sqrt_pos.2 (hpos i)
  have hw : (fun i => (Real.sqrt (Real.exp (1 * τ i)))⁻¹)
      = (fun i => Real.exp ((-(2 : ℝ)⁻¹) * τ i)) := by
    funext i
    rw [one_mul, sqrt_exp_real, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv, metricRay_eq_diagOp u (w := τ) (fun i => hT.apply_eigenvectorBasis hn i)
    (-(2 : ℝ)⁻¹), hw]

/-! ## The exponential metric increasing property -/

/-- **The exponential metric increasing property.**  Every eigenvalue of the difference of two
directions is at most the distance between the corresponding observer metrics.  Its analytic input
is the Golden–Thompson inequality for the norm. -/
theorem eigenvector_le_observerDist {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) {μ : ℝ} {v : E} (hv : v ≠ 0)
    (hev : (S - T) v = ((μ : ℝ) : ℂ) • v) :
    μ ≤ observerDist (isSymmetric_metricRay hT hn 1) hn (isSymmetric_metricRay hS hn 1) := by
  classical
  haveI : Nontrivial E := nontrivial_of_ne v 0 hv
  obtain ⟨i⟩ : Nonempty (Fin n) := by
    rw [← Fin.pos_iff_nonempty, ← hn]
    exact Module.finrank_pos
  set P : E →ₗ[ℂ] E := (metricRay T 1 : E →ₗ[ℂ] E) with hP
  set Q : E →ₗ[ℂ] E := (metricRay S 1 : E →ₗ[ℂ] E) with hQ
  have hPs := isSymmetric_metricRay hT hn 1
  have hQs := isSymmetric_metricRay hS hn 1
  have hrel := isSymmetric_relOp hPs hn hQs
  set lam := hrel.eigenvalues hn with hlam
  have hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re :=
    fun v hv => inner_metricRay_pos hT hn hv 1
  have hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re :=
    fun v hv => inner_metricRay_pos hS hn hv 1
  have hlampos : ∀ j, 0 < lam j :=
    eigenvalues_pos hrel hn fun v hv => inner_relOp_pos hPs hn hPpos hQs hQpos hv
  -- the maximal eigenvalue of the relative form
  obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) lam
    ⟨i, Finset.mem_univ i⟩
  have hnormrel : ‖LinearMap.toContinuousLinearMap (relOp hPs hn Q)‖ ≤ lam j := by
    rw [eq_diagOp_of_apply (hrel.eigenvectorBasis hn) (w := lam)
      (hrel.apply_eigenvectorBasis hn)]
    refine norm_toCLM_diagOp_le _ _ (le_of_lt (hlampos j)) fun k => ?_
    rw [abs_of_pos (hlampos k)]
    exact hjmax k (Finset.mem_univ k)
  -- the relative form as a product of exponentials
  have hR : LinearMap.toContinuousLinearMap (invSqrtOp hPs hn)
      = NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T)) := by
    rw [invSqrtOp_metricRay hT hn, toCLM_metricRay, metricRay_eq_exp_smul]
  have hQC : LinearMap.toContinuousLinearMap Q
      = NormedSpace.exp ((1 : ℝ) • (LinearMap.toContinuousLinearMap S)) := by
    rw [hQ, toCLM_metricRay, metricRay_eq_exp_smul]
  have hrelprod : LinearMap.toContinuousLinearMap (relOp hPs hn Q)
      = NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T))
        * NormedSpace.exp ((1 : ℝ) • (LinearMap.toContinuousLinearMap S))
        * NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T)) := by
    rw [relOp_eq_comp, toCLM_comp, toCLM_comp, hR, hQC, mul_assoc]
  -- the Golden–Thompson bound
  have hXsa : IsSelfAdjoint ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T)) :=
    isSelfAdjoint_smul_real (isSelfAdjoint_toCLM hT)
  have hYsa : IsSelfAdjoint (((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap S)) :=
    isSelfAdjoint_smul_real (isSelfAdjoint_toCLM hS)
  have hgt := norm_exp_add_le hYsa hXsa
  have hsum : ((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap S)
      + (-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T)
      = ((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap (S - T)) := by
    rw [map_sub, smul_sub, neg_smul, sub_eq_add_neg]
  have hnormprod : ‖NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T))
        * NormedSpace.exp ((1 : ℝ) • (LinearMap.toContinuousLinearMap S))
        * NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T))‖
      = ‖NormedSpace.exp (((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap S))
        * NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T))‖
        * ‖NormedSpace.exp (((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap S))
        * NormedSpace.exp ((-(2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap T))‖ := by
    rw [← CStarRing.norm_star_mul_self, star_mul, hXsa.exp.star_eq, hYsa.exp.star_eq, one_smul,
      ← exp_half_smul_mul_self (LinearMap.toContinuousLinearMap S)]
    congr 1
  have hhalfnorm : ‖NormedSpace.exp (((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap (S - T)))‖
      * ‖NormedSpace.exp (((2 : ℝ)⁻¹) • (LinearMap.toContinuousLinearMap (S - T)))‖
      = ‖NormedSpace.exp (LinearMap.toContinuousLinearMap (S - T))‖ := by
    rw [← CStarRing.norm_star_mul_self,
      (isSelfAdjoint_smul_real (isSelfAdjoint_toCLM (hS.sub hT))).exp.star_eq,
      exp_half_smul_mul_self]
  have hchain : ‖NormedSpace.exp (LinearMap.toContinuousLinearMap (S - T))‖
      ≤ ‖LinearMap.toContinuousLinearMap (relOp hPs hn Q)‖ := by
    rw [hrelprod, hnormprod, ← hhalfnorm, ← hsum]
    exact mul_le_mul hgt hgt (norm_nonneg _) (norm_nonneg _)
  -- the eigenvalue bound
  have hexp : Real.exp μ ≤ ‖LinearMap.toContinuousLinearMap (relOp hPs hn Q)‖ := by
    refine le_trans ?_ hchain
    have h := exp_le_norm_metricRay_of_eigenvector hv hev
    rwa [metricRay_eq_exp_smul, one_smul] at h
  have hfinal : Real.exp μ ≤ lam j := le_trans hexp hnormrel
  -- conclude
  rw [observerDist, distId_eq_sqrt, ← hlam]
  have hlog : μ ≤ Real.log (lam j) := by
    rw [← Real.log_exp μ]
    exact Real.log_le_log (Real.exp_pos _) hfinal
  refine le_trans hlog ?_
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun k => Real.log (lam k) ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ j)

/-! ## Distinct traceless directions give diverging rays -/

theorem diagOp_zero (b : OrthonormalBasis (Fin n) ℂ E) : diagOp b (fun _ => (0 : ℝ)) = 0 := by
  refine Basis.ext b.toBasis fun i => ?_
  rw [OrthonormalBasis.coe_toBasis, diagOp_apply_basis]
  simp

/-- **A nonzero traceless Hermitian direction has a positive eigenvalue.** -/
theorem exists_pos_eigenvalue_of_trace_zero {D : E →ₗ[ℂ] E} (hD : D.IsSymmetric)
    (hn : finrank ℂ E = n) (htr : LinearMap.trace ℂ E D = 0) (hne : D ≠ 0) :
    ∃ i, 0 < hD.eigenvalues hn i := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ i, hD.eigenvalues hn i = 0 := by
    have h := trace_eq_sum_eigenvalues hD hn
    rw [htr] at h
    exact_mod_cast h.symm
  have hzero : ∀ i, hD.eigenvalues hn i = 0 := by
    intro i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ -hD.eigenvalues hn j :=
      fun j _ => neg_nonneg.2 (hcon j)
    have hsum' : ∑ j, -hD.eigenvalues hn j = 0 := by
      rw [Finset.sum_neg_distrib, hsum, neg_zero]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum' i (Finset.mem_univ i)
    linarith
  refine hne ?_
  rw [eq_diagOp_of_apply (hD.eigenvectorBasis hn) (w := hD.eigenvalues hn)
      (hD.apply_eigenvectorBasis hn),
    show hD.eigenvalues hn = (fun _ => (0 : ℝ)) from funext hzero]
  exact diagOp_zero _

theorem metricRay_smul_one (T : E →ₗ[ℂ] E) (t : ℝ) :
    ((metricRay ((t : ℂ) • T) 1 : E →ₗ[ℂ] E)) = ((metricRay T t : E →ₗ[ℂ] E)) := by
  congr 1
  rw [metricRay, metricRay]
  congr 1
  ext v
  simp

/-- **Two rays with distinct traceless directions diverge linearly.**  This is the general form of
the flat computation: the distance at parameter `t` is at least `c t` for a positive constant.  So
distinct directions give distinct points of the boundary at infinity, with no assumption that the
directions commute. -/
theorem exists_pos_le_observerDist_metricRay {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank ℂ E = n)
    (htr : LinearMap.trace ℂ E (S - T) = 0) (hne : S ≠ T) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      c * t ≤ observerDist (isSymmetric_metricRay hT hn t) hn
        (isSymmetric_metricRay hS hn t) := by
  have hD : (S - T).IsSymmetric := hS.sub hT
  have hDne : S - T ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨i, hi⟩ := exists_pos_eigenvalue_of_trace_zero hD hn htr hDne
  refine ⟨hD.eigenvalues hn i, hi, fun t _ => ?_⟩
  have hvne : (hD.eigenvectorBasis hn) i ≠ 0 :=
    (hD.eigenvectorBasis hn).orthonormal.ne_zero i
  have hev : ((t : ℂ) • S - (t : ℂ) • T) ((hD.eigenvectorBasis hn) i)
      = (((hD.eigenvalues hn i * t : ℝ)) : ℂ) • (hD.eigenvectorBasis hn) i := by
    rw [← smul_sub]
    show (t : ℂ) • ((S - T) ((hD.eigenvectorBasis hn) i)) = _
    rw [hD.apply_eigenvectorBasis hn i, smul_smul]
    simp [mul_comm]
  have h := eigenvector_le_observerDist (isSymmetric_smul_real hT t)
    (isSymmetric_smul_real hS t) hn hvne hev
  rwa [observerDist_congr (isSymmetric_metricRay (isSymmetric_smul_real hT t) hn 1)
    (isSymmetric_metricRay hT hn t) (isSymmetric_metricRay (isSymmetric_smul_real hS t) hn 1)
    (isSymmetric_metricRay hS hn t) hn (metricRay_smul_one T t) (metricRay_smul_one S t)] at h

end GaloisForLFunctions.HTGeometry
