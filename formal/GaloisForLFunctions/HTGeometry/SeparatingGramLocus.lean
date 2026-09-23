import Mathlib

/-!
# The separating locus of a finite operator family is open and dense

A vector is *separating* for a finite family of bounded operators when the images of the vector are
linearly independent, equivalently when their Gram determinant is nonzero.  The separating locus is
open by continuity of the determinant, and it is dense as soon as it is nonempty: along the line
through a separating vector the Gram determinant is a polynomial whose top coefficient is the Gram
determinant at that vector, so it is not the zero polynomial and has only finitely many roots.

Pairwise orthogonal nonzero images are automatically separating, which is how a separating vector is
produced from disjoint supports.

The complementary seam is closed with empty interior, and separation survives any family of
approximations converging to a separating configuration.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Matrix

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Gram matrix of a finite family of vectors. -/
def gramMatrix {n : ℕ} (v : Fin n → E) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => inner ℂ (v i) (v j)

theorem gramMatrix_mulVec_apply {n : ℕ} (v : Fin n → E) (c : Fin n → ℂ) (i : Fin n) :
    ((gramMatrix v).mulVec c) i = inner ℂ (v i) (∑ j, c j • v j) := by
  simp only [Matrix.mulVec, dotProduct, gramMatrix, Matrix.of_apply, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_conj_mul_gramMatrix_mulVec {n : ℕ} (v : Fin n → E) (c : Fin n → ℂ) :
    ∑ i, (starRingEnd ℂ) (c i) * ((gramMatrix v).mulVec c) i
      = inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) := by
  simp only [gramMatrix_mulVec_apply, sum_inner, inner_smul_left]

/-- **The Gram criterion.**  The Gram determinant of a finite family is nonzero exactly when the
family is linearly independent. -/
theorem det_gramMatrix_ne_zero_iff {n : ℕ} (v : Fin n → E) :
    (gramMatrix v).det ≠ 0 ↔ LinearIndependent ℂ v := by
  classical
  constructor
  · intro hdet
    refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    by_contra hne
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
    refine hdet (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, fun h => hi₀ (by rw [h]; rfl), ?_⟩)
    funext i
    rw [gramMatrix_mulVec_apply, hc]
    simp
  · intro hind hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hkey : inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) = 0 := by
      rw [← sum_conj_mul_gramMatrix_mulVec]
      simp [hc]
    have hzero : (∑ i, c i • v i) = 0 := inner_self_eq_zero.1 hkey
    exact hc0 (funext fun i => Fintype.linearIndependent_iff.1 hind c hzero i)

/-- Pairwise orthogonal nonzero vectors are separating. -/
theorem det_gramMatrix_ne_zero_of_orthogonal {n : ℕ} (v : Fin n → E) (hne : ∀ i, v i ≠ 0)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) : (gramMatrix v).det ≠ 0 := by
  classical
  have hdiag : gramMatrix v = Matrix.diagonal fun i => inner ℂ (v i) (v i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [gramMatrix]
    · simp [gramMatrix, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hdiag, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  exact (inner_self_ne_zero (𝕜 := ℂ) (x := v i)).2 (hne i)

/-! ## The separating locus -/

variable {n : ℕ}

/-- The separating Gram determinant of an operator family at a vector. -/
def separatingGramDet (A : Fin n → (E →L[ℂ] E)) (x : E) : ℂ := (gramMatrix fun i => A i x).det

/-- The separating locus of a finite operator family. -/
def separatingLocus (A : Fin n → (E →L[ℂ] E)) : Set E := {x | separatingGramDet A x ≠ 0}

theorem mem_separatingLocus_iff (A : Fin n → (E →L[ℂ] E)) (x : E) :
    x ∈ separatingLocus A ↔ LinearIndependent ℂ (fun i => A i x) := by
  rw [separatingLocus, Set.mem_setOf_eq, separatingGramDet, det_gramMatrix_ne_zero_iff]

theorem continuous_separatingGramDet (A : Fin n → (E →L[ℂ] E)) :
    Continuous (separatingGramDet A) := by
  unfold separatingGramDet gramMatrix
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact Continuous.inner (𝕜 := ℂ) ((A i).continuous) ((A j).continuous)

/-- **The separating locus is open.** -/
theorem isOpen_separatingLocus (A : Fin n → (E →L[ℂ] E)) : IsOpen (separatingLocus A) :=
  isOpen_ne.preimage (continuous_separatingGramDet A)

/-! ## Density -/

/-- The Gram entries along a real line, as quadratic polynomials. -/
def gramLinePoly (A : Fin n → (E →L[ℂ] E)) (x x₀ : E) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  Matrix.of fun i j =>
    Polynomial.C (inner ℂ (A i x₀) (A j x₀)) * Polynomial.X ^ (2 : ℕ)
      + Polynomial.C (inner ℂ (A i x₀) (A j x) + inner ℂ (A i x) (A j x₀)) * Polynomial.X
      + Polynomial.C (inner ℂ (A i x) (A j x))

theorem gramLinePoly_eval (A : Fin n → (E →L[ℂ] E)) (x x₀ : E) (t : ℝ) (i j : Fin n) :
    Polynomial.eval ((t : ℝ) : ℂ) (gramLinePoly A x x₀ i j)
      = inner ℂ (A i (x + t • x₀)) (A j (x + t • x₀)) := by
  have hsmul : ∀ v : E, ((t : ℝ)) • v = ((t : ℂ)) • v := by
    intro v
    rw [show ((t : ℂ)) = algebraMap ℝ ℂ t from rfl, algebraMap_smul]
  have hAi : A i (x + (t : ℝ) • x₀) = A i x + ((t : ℂ)) • A i x₀ := by
    rw [map_add, hsmul, ContinuousLinearMap.map_smul]
  have hAj : A j (x + (t : ℝ) • x₀) = A j x + ((t : ℂ)) • A j x₀ := by
    rw [map_add, hsmul, ContinuousLinearMap.map_smul]
  simp only [gramLinePoly, Matrix.of_apply, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  rw [hAi, hAj, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
    inner_smul_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem natDegree_gramLinePoly_le (A : Fin n → (E →L[ℂ] E)) (x x₀ : E) (i j : Fin n) :
    (gramLinePoly A x x₀ i j).natDegree ≤ 2 := by
  unfold gramLinePoly
  simp only [Matrix.of_apply]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  refine max_le (le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)) ?_
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  · simp

/-- The top coefficient of the Gram determinant along a line is the Gram determinant of the
direction. -/
theorem coeff_det_gramLinePoly (A : Fin n → (E →L[ℂ] E)) (x x₀ : E) :
    (gramLinePoly A x x₀).det.coeff (n * 2) = separatingGramDet A x₀ := by
  classical
  rw [Matrix.det_apply, separatingGramDet, Matrix.det_apply]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.coeff_smul]
  congr 1
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have := Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin n))
    (fun i => gramLinePoly A x x₀ (σ i) i) 2
    (fun i _ => natDegree_gramLinePoly_le A x x₀ (σ i) i)
  rw [hcard] at this
  rw [this]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [gramLinePoly, Matrix.of_apply, gramMatrix, Polynomial.coeff_add, Polynomial.coeff_C]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  norm_num

/-- The Gram determinant along a line is the evaluation of the polynomial determinant. -/
theorem eval_det_gramLinePoly (A : Fin n → (E →L[ℂ] E)) (x x₀ : E) (t : ℝ) :
    Polynomial.eval ((t : ℝ) : ℂ) (gramLinePoly A x x₀).det
      = separatingGramDet A (x + t • x₀) := by
  have hmap := RingHom.map_det (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (gramLinePoly A x x₀)
  rw [separatingGramDet, show Polynomial.eval ((t : ℝ) : ℂ) (gramLinePoly A x x₀).det
      = (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (gramLinePoly A x x₀).det from rfl, hmap]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom,
    gramLinePoly_eval A x x₀ t i j]
  rfl

/-- **The separating locus is dense once it is nonempty.** -/
theorem dense_separatingLocus (A : Fin n → (E →L[ℂ] E)) {x₀ : E}
    (hx₀ : x₀ ∈ separatingLocus A) : Dense (separatingLocus A) := by
  classical
  refine Metric.dense_iff.2 fun x ε hε => ?_
  have hpolyne : (gramLinePoly A x x₀).det ≠ 0 := by
    intro h
    apply hx₀
    have hc := coeff_det_gramLinePoly A x x₀
    rw [h, Polynomial.coeff_zero] at hc
    exact hc.symm
  have hfinC : {z : ℂ | Polynomial.eval z (gramLinePoly A x x₀).det = 0}.Finite := by
    refine Set.Finite.subset
      ((gramLinePoly A x x₀).det.roots.toFinset : Finset ℂ).finite_toSet ?_
    intro z hz
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hpolyne).2 hz
  have hfin : {t : ℝ | Polynomial.eval ((t : ℝ) : ℂ) (gramLinePoly A x x₀).det = 0}.Finite := by
    refine Set.Finite.of_finite_image ?_ Complex.ofReal_injective.injOn
    refine hfinC.subset ?_
    rintro z ⟨t, ht, rfl⟩
    exact ht
  have hδ : (0 : ℝ) < ε / (‖x₀‖ + 1) := by
    have h1 : (0 : ℝ) < ‖x₀‖ + 1 := by positivity
    positivity
  have hinf : (Set.Ioo (0 : ℝ) (ε / (‖x₀‖ + 1))).Infinite := Set.Ioo_infinite hδ
  obtain ⟨t, ht, htne⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨x + t • x₀, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖x + t • x₀ - x‖ = |t| * ‖x₀‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [hnorm, abs_of_pos ht.1]
    have h2 : (0 : ℝ) < ‖x₀‖ + 1 := by positivity
    have h3 : t * (‖x₀‖ + 1) < ε := by
      rw [← lt_div_iff₀ h2]
      exact ht.2
    nlinarith [norm_nonneg x₀, ht.1]
  · have heval := eval_det_gramLinePoly A x x₀ t
    simp only [separatingLocus, Set.mem_setOf_eq]
    rw [← heval]
    exact htne

/-- **The seam is closed with empty interior.** -/
theorem isClosed_compl_separatingLocus (A : Fin n → (E →L[ℂ] E)) :
    IsClosed (separatingLocus A)ᶜ :=
  (isOpen_separatingLocus A).isClosed_compl

theorem interior_compl_separatingLocus_eq_empty (A : Fin n → (E →L[ℂ] E)) {x₀ : E}
    (hx₀ : x₀ ∈ separatingLocus A) : interior (separatingLocus A)ᶜ = ∅ := by
  rw [interior_compl, (dense_separatingLocus A hx₀).closure_eq, Set.compl_univ]

/-! ## The projection criterion -/

/-- **Equation (11).**  A unit vector separates a family together with the identity exactly when the
projected images are independent. -/
theorem linearIndependent_proj_iff {m : ℕ} (x : E) (hx : ‖x‖ = 1) (w : Fin m → E) :
    (∀ (c₀ : ℂ) (c : Fin m → ℂ), c₀ • x + ∑ j, c j • w j = 0 → c₀ = 0 ∧ ∀ j, c j = 0)
      ↔ LinearIndependent ℂ (fun j => w j - (inner ℂ x (w j)) • x) := by
  classical
  have hxx : inner ℂ x x = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num
  constructor
  · intro hsep
    refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
    have hexp : (-(∑ j, c j * inner ℂ x (w j))) • x + ∑ j, c j • w j = 0 := by
      rw [← hc]
      simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
      module
    exact (hsep _ c hexp).2 j
  · intro hind c₀ c hc
    have hproj : ∑ j, c j • (w j - (inner ℂ x (w j)) • x)
        = (-(∑ j, c j * inner ℂ x (w j))) • x + ∑ j, c j • w j := by
      simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
      module
    have hinner : c₀ + ∑ j, c j * inner ℂ x (w j) = 0 := by
      have := congrArg (fun y => inner ℂ x y) hc
      simp only [inner_add_right, inner_smul_right, inner_sum, hxx, mul_one, inner_zero_right]
        at this
      exact this
    have hzero : ∑ j, c j • (w j - (inner ℂ x (w j)) • x) = 0 := by
      rw [hproj]
      have hsum : (∑ j, c j * inner ℂ x (w j)) = -c₀ := by linear_combination hinner
      rw [hsum]
      rw [← hc]
      module
    have hcj := Fintype.linearIndependent_iff.1 hind c hzero
    refine ⟨?_, hcj⟩
    have hsum0 : (∑ j, c j * inner ℂ x (w j)) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcj j, zero_mul]
    rw [hsum0, add_zero] at hinner
    exact hinner

/-! ## Preservation under approximation -/

/-- **Equations (18b)–(18d).**  Separation survives every family of approximations converging to a
separating configuration. -/
theorem eventually_det_gramMatrix_ne_zero {ι : Type*} {l : Filter ι} {m : ℕ}
    (v : Fin m → E) (vM : ι → Fin m → E)
    (hconv : ∀ i, Tendsto (fun M => vM M i) l (𝓝 (v i)))
    (hdet : (gramMatrix v).det ≠ 0) :
    ∀ᶠ M in l, (gramMatrix (vM M)).det ≠ 0 := by
  have hcont : Tendsto (fun M => (gramMatrix (vM M)).det) l (𝓝 ((gramMatrix v).det)) := by
    have hentries : Tendsto (fun M => gramMatrix (vM M)) l (𝓝 (gramMatrix v)) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact Filter.Tendsto.inner (𝕜 := ℂ) (hconv i) (hconv j)
    exact ((Continuous.matrix_det continuous_id).tendsto (gramMatrix v)).comp hentries
  exact hcont.eventually (eventually_ne_nhds hdet)

/-! ## Disjoint supports give orthogonality -/

/-- Two functions with disjoint supports are orthogonal for any weighted `L²` pairing. -/
theorem integral_conj_mul_eq_zero_of_disjoint {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (w : α → ℂ) (f g : α → ℂ) (h : ∀ a, f a = 0 ∨ g a = 0) :
    ∫ a, w a * ((starRingEnd ℂ) (f a) * g a) ∂μ = 0 := by
  have hzero : (fun a => w a * ((starRingEnd ℂ) (f a) * g a)) = fun _ => 0 := by
    funext a
    rcases h a with ha | ha <;> simp [ha]
  rw [hzero, MeasureTheory.integral_zero]

/-- A finite family of functions with pairwise disjoint supports, none identically zero, is linearly
independent. -/
theorem linearIndependent_of_disjoint_support {α : Type*} {m : ℕ} (f : Fin m → α → ℂ)
    (hne : ∀ i, ∃ a, f i a ≠ 0)
    (hdisj : ∀ i j, i ≠ j → ∀ a, f i a = 0 ∨ f j a = 0) :
    LinearIndependent ℂ f := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
  obtain ⟨a, ha⟩ := hne i
  have hval : (∑ j, c j • f j) a = 0 := by rw [hc]; rfl
  have hsum : (∑ j, c j • f j) a = ∑ j, c j * f j a := by
    simp [Finset.sum_apply]
  rw [hsum] at hval
  have hzero : ∀ j, j ≠ i → c j * f j a = 0 := by
    intro j hj
    rcases hdisj j i hj a with h0 | h0
    · rw [h0, mul_zero]
    · exact absurd h0 ha
  have hone : c i * f i a = 0 := by
    rw [← hval]
    rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun h => absurd (Finset.mem_univ i) h)]
  exact (mul_eq_zero.1 hone).resolve_right ha

end

end GaloisForLFunctions.HTGeometry
