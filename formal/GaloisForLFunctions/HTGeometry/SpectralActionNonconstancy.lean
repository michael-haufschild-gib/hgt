/-
# Nonconstancy of the spectral phase from a single non-degenerate coefficient vector

A spectral phase constant on an open patch of the shell forces, by homogeneity, the *quadratic*
identity `(∑ⱼ kⱼ λⱼ(θ))² = b² ∑ₐ θₐ²` on the open cone over the patch.  Symmetrising that defect
over all labellings of the spectrum turns it into a single polynomial in the shell coordinates,
which then vanishes on a nonempty open set and hence identically.  So one coefficient vector at
which *no* labelling satisfies the quadratic identity refutes constancy on every open patch at
once.

Main results:
* `sortedEnsembleSpectrum_smul`, `sortedSpectralAction_smul` — the action is homogeneous of degree
  one.
* `jointActionDefect`, `jointActionDefectProduct` — the symmetrised quadratic defect.
* `exists_shellPoly_jointActionDefectProduct` — it descends to the shell coordinates.
* `exists_ne_spectralActionPhase_of_witness` — **nonconstancy on every open patch from one
  witness**.
-/
import GaloisForLFunctions.HTGeometry.SpectralActionPhaseAnalytic
import GaloisForLFunctions.HTGeometry.JointDescent
import GaloisForLFunctions.HTGeometry.JointCriticalityEvaluation
import GaloisForLFunctions.HTGeometry.AnalyticFiniteProductDomain

open Filter Topology Set MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

section Homogeneity

variable {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

theorem trace_pow_spectralEnsembleMatrix_smul (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (t : ℝ)
    (θ : Fin N → ℝ) (p : ℕ) :
    (((spectralEnsembleMatrix P (fun a => t * θ a)) ^ p).trace).re
      = t ^ p * (((spectralEnsembleMatrix P θ) ^ p).trace).re := by
  rw [spectralEnsembleMatrix_smul, smul_pow, Matrix.trace_smul, smul_eq_mul]
  rw [show ((((t : ℝ) : ℂ)) ^ p) = (((t ^ p : ℝ) : ℂ)) by push_cast; ring]
  rw [Complex.re_ofReal_mul]

/-- **The canonically labelled spectrum is homogeneous of degree one.** -/
theorem sortedEnsembleSpectrum_smul (hP : ∀ a, (P a).IsHermitian) {t : ℝ} (ht : 0 < t)
    (θ : Fin N → ℝ) :
    sortedEnsembleSpectrum hP (fun a => t * θ a) = fun j => t * sortedEnsembleSpectrum hP θ j := by
  refine eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) ?_ ?_
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (monotone_sortedTuple _ hij) ht.le
  · intro p
    have hL : ∑ j, (sortedEnsembleSpectrum hP (fun a => t * θ a) j) ^ p
        = (((spectralEnsembleMatrix P (fun a => t * θ a)) ^ p).trace).re := by
      rw [sortedEnsembleSpectrum, sum_pow_sortedTuple, sum_pow_eigenvalues_eq_trace_pow_re]
    have hR : ∑ j, (sortedEnsembleSpectrum hP θ j) ^ p
        = (((spectralEnsembleMatrix P θ) ^ p).trace).re := by
      rw [sortedEnsembleSpectrum, sum_pow_sortedTuple, sum_pow_eigenvalues_eq_trace_pow_re]
    have hmul : ∑ j, (t * sortedEnsembleSpectrum hP θ j) ^ p
        = t ^ p * ∑ j, (sortedEnsembleSpectrum hP θ j) ^ p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]
    rw [hL, hmul, hR, trace_pow_spectralEnsembleMatrix_smul]

/-- **The canonically labelled spectral action is homogeneous of degree one.** -/
theorem sortedSpectralAction_smul (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) {t : ℝ}
    (ht : 0 < t) (θ : Fin N → ℝ) :
    sortedSpectralAction hP k (fun a => t * θ a) = t * sortedSpectralAction hP k θ := by
  have hs := sortedEnsembleSpectrum_smul hP ht θ
  rw [sortedSpectralAction, sortedSpectralAction]
  have hcoord : ∀ j, sortedTuple
      (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues j
      = t * sortedTuple (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j := by
    intro j
    exact congrFun hs j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hcoord j]; ring

end Homogeneity

section Defect

/-- The quadratic defect of one labelling of the spectral action, on the joint ring. -/
def jointActionDefect (k : Fin D → ℝ) (b : ℝ) (π : Equiv.Perm (Fin D)) :
    MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  (jointAction k π) ^ 2
    - MvPolynomial.C (b ^ 2) * MvPolynomial.rename Sum.inr (normSqPoly N)

/-- The product of the quadratic defects over all labellings. -/
def jointActionDefectProduct (k : Fin D → ℝ) (b : ℝ) : MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  ∏ π : Equiv.Perm (Fin D), jointActionDefect (N := N) k b π

theorem eval_jointActionDefect (k : Fin D → ℝ) (b : ℝ) (π : Equiv.Perm (Fin D))
    (lam : Fin D → ℝ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (Sum.elim lam θ) (jointActionDefect k b π)
      = (∑ j, k j * lam (π j)) ^ 2 - b ^ 2 * (∑ a, (θ a) ^ 2) := by
  rw [jointActionDefect, MvPolynomial.eval_sub, MvPolynomial.eval_pow, eval_jointAction,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_rename_inr, eval_normSqPoly]

theorem eval_jointActionDefectProduct (k : Fin D → ℝ) (b : ℝ) (lam : Fin D → ℝ)
    (θ : Fin N → ℝ) :
    MvPolynomial.eval (Sum.elim lam θ) (jointActionDefectProduct (N := N) k b)
      = ∏ π : Equiv.Perm (Fin D), ((∑ j, k j * lam (π j)) ^ 2 - b ^ 2 * (∑ a, (θ a) ^ 2)) := by
  classical
  rw [jointActionDefectProduct, map_prod]
  exact Finset.prod_congr rfl fun π _ => eval_jointActionDefect k b π lam θ

theorem rename_sumMap_jointActionDefect (k : Fin D → ℝ) (b : ℝ) (π τ : Equiv.Perm (Fin D)) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (jointActionDefect k b π)
      = jointActionDefect k b (τ * π) := by
  rw [jointActionDefect, jointActionDefect, map_sub, map_pow, rename_sumMap_jointAction,
    map_mul, MvPolynomial.rename_C, rename_sumMap_rename_inr]

/-- **The symmetrised quadratic defect is invariant under relabelling the spectrum.** -/
theorem rename_sumMap_jointActionDefectProduct (k : Fin D → ℝ) (b : ℝ)
    (τ : Equiv.Perm (Fin D)) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (jointActionDefectProduct (N := N) k b)
      = jointActionDefectProduct k b := by
  classical
  simp only [jointActionDefectProduct]
  rw [map_prod, Finset.prod_congr rfl fun π _ => rename_sumMap_jointActionDefect k b π τ]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun π => rfl

theorem isSymmetric_sumAlgEquiv_jointActionDefectProduct (k : Fin D → ℝ) (b : ℝ) :
    ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N))
      (jointActionDefectProduct (N := N) k b)).IsSymmetric := by
  intro τ
  rw [rename_sumAlgEquiv, rename_sumMap_jointActionDefectProduct]

/-- **The symmetrised quadratic defect descends to the shell coordinates.** -/
theorem exists_shellPoly_jointActionDefectProduct {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) (b : ℝ) :
    ∃ G : MvPolynomial (Fin N) ℝ, ∀ θ : Fin N → ℝ,
      MvPolynomial.eval θ G
        = MvPolynomial.eval
            (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
            (jointActionDefectProduct k b) := by
  obtain ⟨G, hG⟩ := exists_shellPoly_of_isSymmetric_over hP
    ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) (jointActionDefectProduct k b))
    (isSymmetric_sumAlgEquiv_jointActionDefectProduct k b)
  refine ⟨G, fun θ => ?_⟩
  rw [← hG θ, eval_sumAlgEquiv]

end Defect

section Nonconstancy

variable {m : ℕ}

/-- **Nonconstancy on every open patch from one witness.**  If there is a coefficient vector at
which no labelling of the spectrum satisfies the quadratic identity, the spectral phase is
nonconstant on every nonempty open set avoiding the origin. -/
theorem exists_ne_spectralActionPhase_of_witness
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (k : Fin D → ℝ)
    (hwit : ∀ b : ℝ, ∃ θ₀ : Fin (m + 1) → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ b ^ 2 * (∑ a, (θ₀ a) ^ 2))
    {V : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hV : IsOpen V) (hVne : V.Nonempty)
    (hV0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∉ V) :
    ∃ p ∈ V, ∃ q ∈ V, spectralActionPhase hP k p ≠ spectralActionPhase hP k q := by
  classical
  by_contra hcon
  have hcon' : ∀ p ∈ V, ∀ q ∈ V,
      spectralActionPhase hP k p = spectralActionPhase hP k q := by
    intro p hp q hq
    by_contra hne
    exact hcon ⟨p, hp, q, hq, hne⟩
  obtain ⟨y₀, hy₀⟩ := hVne
  set b : ℝ := spectralActionPhase hP k y₀ with hb
  have hconst : ∀ y ∈ V, spectralActionPhase hP k y = b := fun y hy => hcon' y hy y₀ hy₀
  -- the unnormalised action on `V` is `b` times the norm
  have haction : ∀ y ∈ V,
      sortedSpectralAction hP k (WithLp.ofLp y) = b * ‖y‖ := by
    intro y hy
    have hyne : y ≠ 0 := fun h => hV0 (h ▸ hy)
    have hnpos : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    have hsplit : (WithLp.ofLp y) = fun a => ‖y‖ * (‖y‖⁻¹ * (WithLp.ofLp y) a) := by
      funext a
      rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
    rw [hsplit, sortedSpectralAction_smul hP k hnpos]
    rw [← spectralActionPhase, hconst y hy, mul_comm]
  -- the quadratic identity on the open image of `V`
  obtain ⟨G, hG⟩ := exists_shellPoly_jointActionDefectProduct hP k b
  have hUopen : IsOpen ((euclCoord (m + 1)).symm '' V) :=
    (euclCoord (m + 1)).symm.toHomeomorph.isOpenMap V hV
  have hUne : ((euclCoord (m + 1)).symm '' V).Nonempty := ⟨_, ⟨y₀, hy₀, rfl⟩⟩
  have hGzero : ∀ θ ∈ (euclCoord (m + 1)).symm '' V, MvPolynomial.eval θ G = 0 := by
    rintro θ ⟨y, hy, rfl⟩
    have hθ : (euclCoord (m + 1)).symm y = WithLp.ofLp y := rfl
    rw [hθ, hG (WithLp.ofLp y), eval_jointActionDefectProduct]
    refine Finset.prod_eq_zero
      (Finset.mem_univ (Tuple.sort (isHermitian_spectralEnsembleMatrix hP (WithLp.ofLp y)).eigenvalues)) ?_
    have hleft : (∑ j, k j *
        (isHermitian_spectralEnsembleMatrix hP (WithLp.ofLp y)).eigenvalues
          (Tuple.sort (isHermitian_spectralEnsembleMatrix hP (WithLp.ofLp y)).eigenvalues j))
        = sortedSpectralAction hP k (WithLp.ofLp y) := rfl
    have hnorm : ∑ a, ((WithLp.ofLp y) a) ^ 2 = ‖y‖ ^ 2 := by
      rw [norm_eq_sqrt_sum_sq y, Real.sq_sqrt
        (Finset.sum_nonneg fun a _ => sq_nonneg _)]
    rw [hleft, hnorm, haction y hy]
    ring
  have hGeq : G = 0 := realMvPolynomial_eq_zero_of_eqOn_zero_isOpen hUopen hUne hGzero
  obtain ⟨θ₀, hθ₀⟩ := hwit b
  have hzero : MvPolynomial.eval θ₀ G = 0 := by rw [hGeq]; simp
  rw [hG θ₀, eval_jointActionDefectProduct] at hzero
  obtain ⟨π, -, hπ⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact hθ₀ π (by linarith [sub_eq_zero.mp hπ])

/-- **Angular dephasing from a single witness.**  With a discriminant that does not vanish
identically and one coefficient vector at which no labelling satisfies the quadratic identity, the
oscillatory shell integral of the spectral action against any bounded measurable amplitude tends to
zero. -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_of_witness
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hDisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ)
    (hwit : ∀ b : ℝ, ∃ θ₀ : Fin (m + 1) → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ b ^ 2 * (∑ a, (θ₀ a) ^ 2))
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (m + 1)))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) := by
  refine tendsto_integral_exp_sortedSpectralAction_zero hP hDisc k
    (analyticOnNhd_spectralActionPhase hP k) ?_ g hg hC0 hC
  intro V hVopen hVne hVsub
  refine exists_ne_spectralActionPhase_of_witness hP k hwit hVopen hVne ?_
  intro h0
  exact (hVsub h0).2.2 rfl

end Nonconstancy

end

end GaloisForLFunctions.HTGeometry
