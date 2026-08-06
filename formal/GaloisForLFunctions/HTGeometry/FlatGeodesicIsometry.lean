import GaloisForLFunctions.HTGeometry.ObserverDistanceSymmetry
import GaloisForLFunctions.HTGeometry.FlatEuclidean

/-!
# Flats are Euclidean and rays are geodesics, for the observer distance

The previous flat module measured a flat in the logarithmic chart, through the tangent norm of the
difference of logarithms.  Now that the distance between observer metrics is a metric, the same
computation can be run for the distance itself: two observer metrics diagonal in one frame are at
the Euclidean distance of the logarithms of their weights.

Two consequences.  A maximal flat is isometrically a Euclidean space, so the real rank statement is
metric and not only linear-algebraic; and the ray `t ↦ exp (t T)` is a geodesic line, since the
distance between two of its points is `|t - s| ‖T‖`.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## Transport along equalities of operators -/

theorem invOp_congr {f g : E →ₗ[ℂ] E} (hf : f.IsSymmetric) (hg : g.IsSymmetric)
    (hn : finrank ℂ E = n) (h : f = g) : invOp hf hn = invOp hg hn := by
  subst h
  rfl

theorem observerDist_congr {P P' Q Q' : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hP' : P'.IsSymmetric)
    (hQ : Q.IsSymmetric) (hQ' : Q'.IsSymmetric) (hn : finrank ℂ E = n)
    (h1 : P = P') (h2 : Q = Q') : observerDist hP hn hQ = observerDist hP' hn hQ' := by
  subst h1
  subst h2
  rfl

/-! ## The square root and the inverse of a diagonal form -/

/-- **The square root of a form diagonal in a frame is diagonal in the same frame**, with the
square roots of its weights.  It is proved through the flag: at a nonnegative threshold the flag of
a square root is the flag of the form at the squared threshold. -/
theorem sqrtOp_eq_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric) {d : Fin n → ℝ}
    (hd : ∀ i, f (b i) = ((d i : ℝ) : ℂ) • b i) (hpos : ∀ i, 0 < d i) :
    sqrtOp hf hn = diagOp b (fun i => Real.sqrt (d i)) := by
  classical
  have hfpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (f v)).re :=
    fun v hv => inner_self_pos_of_diagonal b hd hpos hv
  have hval : ∀ i, 0 < hf.eigenvalues hn i := eigenvalues_pos hf hn hfpos
  refine eq_of_eigenSum_eq (isSymmetric_sqrtOp hf hn) (isSymmetric_diagOp b _) hn fun c => ?_
  rw [eigenSum_eq_span_of_eigenbasis (hf.eigenvectorBasis hn).toBasis
      (w := fun i => Real.sqrt (hf.eigenvalues hn i)) (fun i => by
        rw [OrthonormalBasis.coe_toBasis]
        exact sqrtOp_apply_basis hf hn i) c,
    eigenSum_eq_span_of_eigenbasis b.toBasis (w := fun i => Real.sqrt (d i)) (fun i => by
        rw [OrthonormalBasis.coe_toBasis]
        exact diagOp_apply_basis b _ i) c]
  rcases lt_or_ge c 0 with hc | hc
  · have hleft : {i : Fin n | c < Real.sqrt (hf.eigenvalues hn i)} = Set.univ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hc (Real.sqrt_nonneg _)
    have hright : {i : Fin n | c < Real.sqrt (d i)} = Set.univ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hc (Real.sqrt_nonneg _)
    rw [hleft, hright, Set.image_univ, Set.image_univ,
      Submodule.span_range_eq_iSup, Submodule.span_range_eq_iSup]
    rw [show (⨆ i, Submodule.span ℂ {(hf.eigenvectorBasis hn).toBasis i}) = ⊤ from by
        rw [← Submodule.span_range_eq_iSup, ← Set.image_univ]
        simpa using (hf.eigenvectorBasis hn).toBasis.span_eq,
      show (⨆ i, Submodule.span ℂ {b.toBasis i}) = ⊤ from by
        rw [← Submodule.span_range_eq_iSup, ← Set.image_univ]
        simpa using b.toBasis.span_eq]
  · have hleft : {i : Fin n | c < Real.sqrt (hf.eigenvalues hn i)}
        = {i : Fin n | c ^ 2 < hf.eigenvalues hn i} := by
      ext i
      simp only [Set.mem_setOf_eq]
      rw [show (c < Real.sqrt (hf.eigenvalues hn i)) ↔ (c ^ 2 < hf.eigenvalues hn i) from
        Real.lt_sqrt hc]
    have hright : {i : Fin n | c < Real.sqrt (d i)} = {i : Fin n | c ^ 2 < d i} := by
      ext i
      simp only [Set.mem_setOf_eq]
      rw [show (c < Real.sqrt (d i)) ↔ (c ^ 2 < d i) from Real.lt_sqrt hc]
    rw [hleft, hright,
      ← eigenSum_eq_span_of_eigenbasis (hf.eigenvectorBasis hn).toBasis
        (w := fun i => hf.eigenvalues hn i) (fun i => by
          rw [OrthonormalBasis.coe_toBasis]
          exact hf.apply_eigenvectorBasis hn i) (c ^ 2),
      ← eigenSum_eq_span_of_eigenbasis b.toBasis (w := d) (fun i => by
          rw [OrthonormalBasis.coe_toBasis]
          exact hd i) (c ^ 2)]

/-- **The inverse of a form diagonal in a frame is diagonal in the same frame**, with the inverses
of its weights. -/
theorem invOp_eq_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric) {d : Fin n → ℝ}
    (hd : ∀ i, f (b i) = ((d i : ℝ) : ℂ) • b i) (hpos : ∀ i, 0 < d i) :
    invOp hf hn = diagOp b (fun i => (d i)⁻¹) := by
  have hfpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (f v)).re :=
    fun v hv => inner_self_pos_of_diagonal b hd hpos hv
  have hcomp : ∀ w : E, diagOp b (fun i => (d i)⁻¹) (f w) = w := by
    have hext : (diagOp b fun i => (d i)⁻¹) ∘ₗ f = LinearMap.id := by
      refine Basis.ext b.toBasis fun i => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, hd i, map_smul,
        diagOp_apply_basis, smul_smul, LinearMap.id_apply]
      have hne : d i ≠ 0 := ne_of_gt (hpos i)
      rw [show ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ) = ((d i * (d i)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring, mul_inv_cancel₀ hne]
      simp
    exact fun w => congrArg (fun g : E →ₗ[ℂ] E => g w) hext
  refine LinearMap.ext fun v => ?_
  have h := hcomp (invOp hf hn v)
  rw [comp_invOp hf hn hfpos v] at h
  exact h.symm

/-! ## The relative form of two forms in one frame -/

/-- **The relative form of two forms diagonal in one frame** is diagonal in the same frame. -/
theorem relOp_diagOp_apply (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {p q : Fin n → ℝ} (hp : ∀ i, 0 < p i) (i : Fin n) :
    relOp (isSymmetric_diagOp b p) hn (diagOp b q) (b i)
      = (((Real.sqrt (p i))⁻¹ * q i * (Real.sqrt (p i))⁻¹ : ℝ) : ℂ) • b i := by
  have hsqrt : sqrtOp (isSymmetric_diagOp b p) hn = diagOp b (fun i => Real.sqrt (p i)) :=
    sqrtOp_eq_diagOp b hn (isSymmetric_diagOp b p) (diagOp_apply_basis b p) hp
  have hinv : invOp (isSymmetric_sqrtOp (isSymmetric_diagOp b p) hn) hn
      = diagOp b (fun i => (Real.sqrt (p i))⁻¹) := by
    rw [invOp_congr (isSymmetric_sqrtOp (isSymmetric_diagOp b p) hn)
      (isSymmetric_diagOp b fun i => Real.sqrt (p i)) hn hsqrt]
    exact invOp_eq_diagOp b hn (isSymmetric_diagOp b _) (diagOp_apply_basis b _)
      fun i => Real.sqrt_pos.2 (hp i)
  show invOp (isSymmetric_sqrtOp (isSymmetric_diagOp b p) hn) hn
      (diagOp b q (invOp (isSymmetric_sqrtOp (isSymmetric_diagOp b p) hn) hn (b i))) = _
  rw [hinv]
  simp only [diagOp_apply_basis, map_smul, smul_smul]
  congr 1
  push_cast
  ring

/-! ## A flat is Euclidean for the observer distance -/

/-- **Two observer metrics diagonal in one frame are at the Euclidean distance of the logarithms of
their weights.**  So a maximal flat is isometrically a Euclidean space. -/
theorem observerDist_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {p q : Fin n → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    observerDist (isSymmetric_diagOp b p) hn (isSymmetric_diagOp b q)
      = Real.sqrt (∑ i, (Real.log (q i) - Real.log (p i)) ^ 2) := by
  have hwpos : ∀ i, 0 < (Real.sqrt (p i))⁻¹ * q i * (Real.sqrt (p i))⁻¹ := fun i =>
    mul_pos (mul_pos (inv_pos.2 (Real.sqrt_pos.2 (hp i))) (hq i))
      (inv_pos.2 (Real.sqrt_pos.2 (hp i)))
  rw [observerDist,
    distId_eq_sqrt_of_diagonal b hn (isSymmetric_relOp (isSymmetric_diagOp b p) hn
      (isSymmetric_diagOp b q)) (relOp_diagOp_apply b hn hp) hwpos]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hsp : (0:ℝ) < Real.sqrt (p i) := Real.sqrt_pos.2 (hp i)
  rw [Real.log_mul (ne_of_gt (mul_pos (inv_pos.2 hsp) (hq i))) (ne_of_gt (inv_pos.2 hsp)),
    Real.log_mul (ne_of_gt (inv_pos.2 hsp)) (ne_of_gt (hq i)), Real.log_inv,
    Real.log_sqrt (le_of_lt (hp i))]
  ring

/-! ## Rays are geodesic lines -/

/-- **The exponential of a direction is diagonal in any frame diagonalising it.** -/
theorem metricRay_eq_diagOp (b : OrthonormalBasis (Fin n) ℂ E) {T : E →ₗ[ℂ] E} {w : Fin n → ℝ}
    (hw : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i) (t : ℝ) :
    ((metricRay T t : E →ₗ[ℂ] E)) = diagOp b (fun i => Real.exp (t * w i)) := by
  refine Basis.ext b.toBasis fun i => ?_
  rw [OrthonormalBasis.coe_toBasis]
  show metricRay T t (b i) = diagOp b (fun i => Real.exp (t * w i)) (b i)
  rw [metricRay_apply_of_eigenvector (hw i) t, diagOp_apply_basis]

/-- **A metric ray is a geodesic line.**  The distance between the points at parameters `s` and `t`
is `|t - s|` times the tangent norm of the direction, so the ray is an isometric embedding of the
line, scaled by `‖T‖`. -/
theorem observerDist_metricRay {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (s t : ℝ) :
    observerDist (isSymmetric_metricRay hT hn s) hn (isSymmetric_metricRay hT hn t)
      = |t - s| * ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T) := by
  set u := hT.eigenvectorBasis hn with hudef
  set lam := hT.eigenvalues hn with hlamdef
  have hw : ∀ i, T (u i) = ((lam i : ℝ) : ℂ) • u i := hT.apply_eigenvectorBasis hn
  have hs : ((metricRay T s : E →ₗ[ℂ] E)) = diagOp u (fun i => Real.exp (s * lam i)) :=
    metricRay_eq_diagOp u hw s
  have ht : ((metricRay T t : E →ₗ[ℂ] E)) = diagOp u (fun i => Real.exp (t * lam i)) :=
    metricRay_eq_diagOp u hw t
  rw [observerDist_congr (isSymmetric_metricRay hT hn s)
      (isSymmetric_diagOp u fun i => Real.exp (s * lam i)) (isSymmetric_metricRay hT hn t)
      (isSymmetric_diagOp u fun i => Real.exp (t * lam i)) hn hs ht,
    observerDist_diagOp u hn (fun i => Real.exp_pos _) fun i => Real.exp_pos _,
    hsNorm_toCLM_eq_sqrt hT hn, ← hlamdef]
  rw [show (∑ i, (Real.log (Real.exp (t * lam i)) - Real.log (Real.exp (s * lam i))) ^ 2)
      = (t - s) ^ 2 * ∑ i, lam i ^ 2 from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.log_exp, Real.log_exp]
        ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-! ## Rays of one flat diverge at the Euclidean rate -/

/-- **Two rays of one flat separate at exactly the Euclidean rate of their directions.**  The
distance at parameter `t` is `|t|` times the Euclidean distance of the two weight vectors, so
inside an apartment the asymptotic separation rate is the Euclidean one. -/
theorem observerDist_metricRay_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    (w w' : Fin n → ℝ) (t : ℝ) :
    observerDist (isSymmetric_metricRay (isSymmetric_diagOp b w) hn t) hn
        (isSymmetric_metricRay (isSymmetric_diagOp b w') hn t)
      = |t| * Real.sqrt (∑ i, (w' i - w i) ^ 2) := by
  rw [observerDist_congr (isSymmetric_metricRay (isSymmetric_diagOp b w) hn t)
      (isSymmetric_diagOp b fun i => Real.exp (t * w i))
      (isSymmetric_metricRay (isSymmetric_diagOp b w') hn t)
      (isSymmetric_diagOp b fun i => Real.exp (t * w' i)) hn
      (metricRay_eq_diagOp b (diagOp_apply_basis b w) t)
      (metricRay_eq_diagOp b (diagOp_apply_basis b w') t),
    observerDist_diagOp b hn (fun i => Real.exp_pos _) fun i => Real.exp_pos _,
    show (∑ i, (Real.log (Real.exp (t * w' i)) - Real.log (Real.exp (t * w i))) ^ 2)
      = t ^ 2 * ∑ i, (w' i - w i) ^ 2 from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.log_exp, Real.log_exp]
        ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- **Distinct directions of a flat give rays that diverge linearly**, so they are not asymptotic:
inside an apartment the boundary is parametrised faithfully by the directions. -/
theorem exists_pos_observerDist_metricRay_diagOp (b : OrthonormalBasis (Fin n) ℂ E)
    (hn : finrank ℂ E = n) {w w' : Fin n → ℝ} (h : w ≠ w') :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      observerDist (isSymmetric_metricRay (isSymmetric_diagOp b w) hn t) hn
        (isSymmetric_metricRay (isSymmetric_diagOp b w') hn t) = t * c := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, w' i - w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (funext fun i => by linarith [sub_eq_zero.1 (hcon i)])
  refine ⟨Real.sqrt (∑ i, (w' i - w i) ^ 2), Real.sqrt_pos.2 ?_, fun t ht => ?_⟩
  · refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i₀, Finset.mem_univ i₀, ?_⟩
    exact pow_pos (abs_pos.2 hi₀) 2 |>.trans_le (le_of_eq (sq_abs _))
  · rw [observerDist_metricRay_diagOp b hn w w' t, abs_of_nonneg ht]

end GaloisForLFunctions.HTGeometry
