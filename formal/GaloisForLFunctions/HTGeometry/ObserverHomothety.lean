import GaloisForLFunctions.HTGeometry.CompoundHomothety
import GaloisForLFunctions.HTGeometry.ObserverTriangleInequality

/-!
# The homothety contraction of the observer distance

A ray of observer metrics contracts towards the reference metric:

```text
d (exp (λ T), exp (λ S)) ≤ λ · d (exp T, exp S)        (0 ≤ λ ≤ 1).
```

The log-majorization of the pencil spectra on every compound gives the top-sum inequalities, the
determinant gives the equality of totals, and Karamata for the square converts the two into the
inequality of Euclidean norms, which is the distance.

This is what makes the divergence rate of two rays monotone, hence convergent: the rate is bounded
above by twice the speed, so a monotone bounded quantity has a limit, and that limit is the Tits
distance of the two boundary points.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Matrix

variable {n : ℕ}

/-! ## Scaling a top sum -/

theorem topSum_zero {k : ℕ} (hk : k ≤ n) : topSum k (fun _ : Fin n => (0 : ℝ)) = 0 := by
  obtain ⟨t, -, hsum⟩ := exists_sum_eq_topSum (fun _ : Fin n => (0 : ℝ)) hk
  rw [← hsum]
  simp

theorem topSum_smul_nonneg {k : ℕ} (hk : k ≤ n) {lam : ℝ} (hlam : 0 ≤ lam) (v : Fin n → ℝ) :
    topSum k (fun i => lam * v i) = lam * topSum k v := by
  refine le_antisymm ?_ ?_
  · obtain ⟨t, hcard, hsum⟩ := exists_sum_eq_topSum (fun i => lam * v i) hk
    rw [← hsum, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_le_topSum hk hcard) hlam
  · obtain ⟨t, hcard, hsum⟩ := exists_sum_eq_topSum v hk
    rw [← hsum, Finset.mul_sum]
    exact sum_le_topSum (v := fun i => lam * v i) hk hcard

/-! ## Karamata for a scaled majorization -/

/-- **Karamata for the square, in scaled form.**  A vector dominated by a multiple of another one
in every top sum, with matching totals, has its Euclidean norm dominated by the same multiple. -/
theorem sqrt_sum_sq_le_smul_of_topSum_le {a b : Fin n → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ∀ m ≤ n, topSum m a ≤ lam * topSum m b)
    (htot : ∑ i, a i = lam * ∑ i, b i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ lam * Real.sqrt (∑ i, b i ^ 2) := by
  have htop : ∀ m ≤ n, topSum m a
      ≤ topSum m (fun i => lam * b i) + topSum m (fun _ : Fin n => (0 : ℝ)) := by
    intro m hm
    rw [topSum_smul_nonneg hm hlam, topSum_zero hm, add_zero]
    exact h m hm
  have htotal : ∑ i, a i = (∑ i, lam * b i) + ∑ _i : Fin n, (0 : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_const, smul_zero, add_zero]
    exact htot
  have hkey := sqrt_sum_sq_le_of_topSum_le htop htotal
  have hzero : Real.sqrt (∑ _i : Fin n, (0 : ℝ) ^ 2) = 0 := by
    simp
  have hscale : Real.sqrt (∑ i, (lam * b i) ^ 2) = lam * Real.sqrt (∑ i, b i ^ 2) := by
    have hexp : ∑ i, (lam * b i) ^ 2 = lam ^ 2 * ∑ i, b i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam]
  rw [hzero, add_zero, hscale] at hkey
  exact hkey


/-! ## Rays in a frame -/

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- In any orthonormal frame, the matrix of a point of an exponential ray is the corresponding
exponential ray of matrices. -/
theorem obsMat_metricRay_eq_expRayMat (b u : OrthonormalBasis (Fin n) ℂ E) {T : E →ₗ[ℂ] E}
    {w : Fin n → ℝ} (hd : ∀ i, T (u i) = ((w i : ℝ) : ℂ) • u i) (t : ℝ) :
    obsMat b ((metricRay T t : E →ₗ[ℂ] E)) = expRayMat (u.toBasis.toMatrix ⇑b) w t :=
  obsMat_eq_conj_rdiag b u fun i => metricRay_apply_of_eigenvector (hd i) t

/-! ## The determinant along a ray -/

theorem det_conj_rdiag {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (w : Fin n → ℝ) :
    (Vᴴ * rdiag w * V).det = ((∏ i, w i : ℝ) : ℂ) := by
  have hVV : Vᴴ * V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hV
    exact hV
  have hdet : Vᴴ.det * V.det = 1 := by
    rw [← Matrix.det_mul, hVV, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, rdiag, Matrix.det_diagonal,
    show Vᴴ.det * (∏ i, ((w i : ℝ) : ℂ)) * V.det
      = (∏ i, ((w i : ℝ) : ℂ)) * (Vᴴ.det * V.det) from by ring,
    hdet, mul_one, ← Complex.ofReal_prod]

theorem det_expRayMat {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (w : Fin n → ℝ) (t : ℝ) :
    (expRayMat V w t).det = ((Real.exp (t * ∑ i, w i) : ℝ) : ℂ) := by
  rw [expRayMat, det_conj_rdiag hV, ← Real.exp_sum, ← Finset.mul_sum]

/-! ## The product of the relative spectrum along a ray -/

theorem prod_relOp_eigenvalues_metricRay (b u v : OrthonormalBasis (Fin n) ℂ E)
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℂ E = n)
    {τ σ : Fin n → ℝ} (hdT : ∀ i, T (u i) = ((τ i : ℝ) : ℂ) • u i)
    (hdS : ∀ i, S (v i) = ((σ i : ℝ) : ℂ) • v i) (t : ℝ) :
    ∏ i, (isSymmetric_relOp (isSymmetric_metricRay hT hn t) hn
        (isSymmetric_metricRay hS hn t)).eigenvalues hn i
      = Real.exp (t * ((∑ i, σ i) - ∑ i, τ i)) := by
  classical
  set hP := isSymmetric_metricRay hT hn t with hPdef
  set hQ := isSymmetric_metricRay hS hn t with hQdef
  have hPpos : ∀ x : E, x ≠ 0 →
      0 < (inner ℂ x ((metricRay T t : E →ₗ[ℂ] E) x)).re := fun x hx =>
    inner_metricRay_pos hT hn hx t
  set γ := (isSymmetric_relOp hP hn hQ).eigenvalues hn with hγdef
  -- the determinant of the relative form is the product of its spectrum
  have hrel : (obsMat b (relOp hP hn ((metricRay S t : E →ₗ[ℂ] E)))).det
      = ((∏ i, γ i : ℝ) : ℂ) := by
    rw [obsMat_relOp_eq b hP hn hQ, det_conj_rdiag (changeFrame_unitary b _)]
  -- and it factors through the two matrices of the ray
  have hfac : (obsMat b (relOp hP hn ((metricRay S t : E →ₗ[ℂ] E)))).det
      = (invSqrtMat b hP hn).det * (obsMat b ((metricRay S t : E →ₗ[ℂ] E))).det
        * (invSqrtMat b hP hn).det := by
    rw [← invSqrtMat_mul_relOp b hP hn, Matrix.det_mul, Matrix.det_mul]
  have hunit : (invSqrtMat b hP hn).det * (obsMat b ((metricRay T t : E →ₗ[ℂ] E))).det
      * (invSqrtMat b hP hn).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, invSqrtMat_mul_self b hP hn hPpos, Matrix.det_one]
  -- the two matrices of the ray are exponential rays of matrices
  have hPmat : (obsMat b ((metricRay T t : E →ₗ[ℂ] E))).det
      = ((Real.exp (t * ∑ i, τ i) : ℝ) : ℂ) := by
    rw [obsMat_metricRay_eq_expRayMat b u hdT t, det_expRayMat (changeFrame_unitary b u)]
  have hQmat : (obsMat b ((metricRay S t : E →ₗ[ℂ] E))).det
      = ((Real.exp (t * ∑ i, σ i) : ℝ) : ℂ) := by
    rw [obsMat_metricRay_eq_expRayMat b v hdS t, det_expRayMat (changeFrame_unitary b v)]
  -- combine
  have hkey : ((∏ i, γ i : ℝ) : ℂ) * ((Real.exp (t * ∑ i, τ i) : ℝ) : ℂ)
      = ((Real.exp (t * ∑ i, σ i) : ℝ) : ℂ) := by
    rw [← hrel, hfac, ← hPmat, ← hQmat]
    rw [show (invSqrtMat b hP hn).det * (obsMat b ((metricRay S t : E →ₗ[ℂ] E))).det
          * (invSqrtMat b hP hn).det * (obsMat b ((metricRay T t : E →ₗ[ℂ] E))).det
        = ((invSqrtMat b hP hn).det * (obsMat b ((metricRay T t : E →ₗ[ℂ] E))).det
            * (invSqrtMat b hP hn).det) * (obsMat b ((metricRay S t : E →ₗ[ℂ] E))).det from by
      ring, hunit, one_mul]
  have hreal : (∏ i, γ i) * Real.exp (t * ∑ i, τ i) = Real.exp (t * ∑ i, σ i) := by
    exact_mod_cast hkey
  have hexp : Real.exp (t * ∑ i, τ i) ≠ 0 := Real.exp_ne_zero _
  rw [eq_div_of_mul_eq hexp hreal, ← Real.exp_sub]
  congr 1
  ring


/-! ## The homothety contraction -/

/-- **The distance between two exponential rays contracts linearly towards the reference
metric.**  This is what makes the divergence rate of two rays monotone. -/
theorem observerDist_metricRay_smul_le {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank ℂ E = n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    observerDist (isSymmetric_metricRay hT hn lam) hn (isSymmetric_metricRay hS hn lam)
      ≤ lam * observerDist (isSymmetric_metricRay hT hn 1) hn
          (isSymmetric_metricRay hS hn 1) := by
  classical
  set u := hT.eigenvectorBasis hn with hudef
  set τ := hT.eigenvalues hn with hτdef
  have hdT : ∀ i, T (u i) = ((τ i : ℝ) : ℂ) • u i := hT.apply_eigenvectorBasis hn
  set v := hS.eigenvectorBasis hn with hvdef
  set σ := hS.eigenvalues hn with hσdef
  have hdS : ∀ i, S (v i) = ((σ i : ℝ) : ℂ) • v i := hS.apply_eigenvectorBasis hn
  set b := u with hbdef
  have hPpos : ∀ t : ℝ, ∀ x : E, x ≠ 0 →
      0 < (inner ℂ x ((metricRay T t : E →ₗ[ℂ] E) x)).re := fun t x hx =>
    inner_metricRay_pos hT hn hx t
  have hQpos : ∀ t : ℝ, ∀ x : E, x ≠ 0 →
      0 < (inner ℂ x ((metricRay S t : E →ₗ[ℂ] E) x)).re := fun t x hx =>
    inner_metricRay_pos hS hn hx t
  set γ : ℝ → Fin n → ℝ := fun t =>
    (isSymmetric_relOp (isSymmetric_metricRay hT hn t) hn
      (isSymmetric_metricRay hS hn t)).eigenvalues hn with hγdef
  have hγpos : ∀ t : ℝ, ∀ i, 0 < γ t i := fun t =>
    eigenvalues_pos _ hn fun x hx =>
      inner_relOp_pos (isSymmetric_metricRay hT hn t) hn (hPpos t)
        (isSymmetric_metricRay hS hn t) (hQpos t) hx
  -- the matrices of the two rays, in the frame `b`
  have hPmat : ∀ t : ℝ, obsMat b ((metricRay T t : E →ₗ[ℂ] E))
      = expRayMat (u.toBasis.toMatrix ⇑b) τ t := fun t =>
    obsMat_metricRay_eq_expRayMat b u hdT t
  have hQmat : ∀ t : ℝ, obsMat b ((metricRay S t : E →ₗ[ℂ] E))
      = expRayMat (v.toBasis.toMatrix ⇑b) σ t := fun t =>
    obsMat_metricRay_eq_expRayMat b v hdS t
  -- the totals scale
  have hlog : ∀ t : ℝ, ∑ i, Real.log (γ t i) = t * ((∑ i, σ i) - ∑ i, τ i) := by
    intro t
    have hprod := prod_relOp_eigenvalues_metricRay b u v hT hS hn hdT hdS t
    rw [← Real.log_prod fun i _ => ne_of_gt (hγpos t i), hprod, Real.log_exp]
  have htotal : ∑ i, Real.log (γ lam i) = lam * ∑ i, Real.log (γ 1 i) := by
    rw [hlog lam, hlog 1, one_mul]
  -- the top sums contract
  have htop : ∀ k ≤ n, topSum k (fun i => Real.log (γ lam i))
      ≤ lam * topSum k fun i => Real.log (γ 1 i) := by
    intro k hk
    set c₁ := Real.exp (topSum k fun i => Real.log (γ 1 i)) with hc₁def
    have hc₁pos : 0 < c₁ := Real.exp_pos _
    have hform1 : ∀ x, (matQuadForm (compound k (expRayMat (v.toBasis.toMatrix ⇑b) σ 1)) x).re
        ≤ c₁ * (matQuadForm (compound k (expRayMat (u.toBasis.toMatrix ⇑b) τ 1)) x).re := by
      intro x
      rw [← hPmat 1, ← hQmat 1]
      exact compound_quadForm_le (isHermitian_invSqrtMat b (isSymmetric_metricRay hT hn 1) hn)
        (invSqrtMat_mul_self b (isSymmetric_metricRay hT hn 1) hn (hPpos 1))
        (by rw [invSqrtMat_mul_relOp,
          obsMat_relOp_eq b (isSymmetric_metricRay hT hn 1) hn (isSymmetric_metricRay hS hn 1)])
        (changeFrame_unitary b _)
        (fun s => prod_le_exp_topSum (hγpos 1) hk s) x
    have hformlam := quadForm_compound_expRay_le (changeFrame_unitary b u)
      (changeFrame_unitary b v) τ σ hc₁pos hform1 hlam0 hlam1
    have hprod : ∀ s : Set.powersetCard (Fin n) k,
        ∏ i ∈ (s : Finset (Fin n)), γ lam i ≤ c₁ ^ lam := by
      intro s
      refine prod_le_of_compound_quadForm_le
        (isHermitian_invSqrtMat b (isSymmetric_metricRay hT hn lam) hn)
        (invSqrtMat_mul_self b (isSymmetric_metricRay hT hn lam) hn (hPpos lam))
        (by rw [invSqrtMat_mul_relOp, obsMat_relOp_eq b (isSymmetric_metricRay hT hn lam) hn
          (isSymmetric_metricRay hS hn lam)])
        (changeFrame_unitary b _) (fun x => ?_) s
      rw [hPmat lam, hQmat lam]
      exact hformlam x
    obtain ⟨t, htcard, htsum⟩ := exists_sum_eq_topSum (fun i => Real.log (γ lam i)) hk
    have hs := hprod ⟨t, Set.powersetCard.mem_iff.2 htcard⟩
    rw [show ((⟨t, Set.powersetCard.mem_iff.2 htcard⟩ : Set.powersetCard (Fin n) k) :
        Finset (Fin n)) = t from rfl, prod_eq_exp_sum_log t (hγpos lam), htsum, hc₁def,
      ← Real.exp_mul, Real.exp_le_exp] at hs
    linarith [hs]
  -- assemble
  rw [observerDist, observerDist, distId_eq_sqrt, distId_eq_sqrt]
  exact sqrt_sum_sq_le_smul_of_topSum_le hlam0 htop htotal

end GaloisForLFunctions.HTGeometry
