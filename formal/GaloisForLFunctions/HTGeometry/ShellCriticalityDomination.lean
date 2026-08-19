/-
# The transversality power law for the spectral action

Every labelling block of the criticality product is, on the unit shell, the square of the leading
factor of the defining relation times the squared tangential gradient of the labelled spectral
action.  Splitting off the distinguished block therefore writes the shell polynomial as the
tangential gradient times a cofactor which -- although the spectrum is not a continuous function of
the coefficients -- is uniformly bounded on the shell.  That domination is exactly what the
power-law sublevel bound consumes.

Main results:
* `jointCriticalCofactor` — the criticality product with the distinguished tangential block
  removed.
* `eval_jointCriticalProduct_eq_tangential_mul` — **the factorisation on the unit shell**.
* `exists_toSphere_sublevel_le_shellCriticality` — **the transversality power law**: the shell
  measure of `{‖∇_S φ‖² ≤ g}` is at most `A g^{1/d}`.
-/
import GaloisForLFunctions.HTGeometry.JointCriticalityEvaluation
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound
import GaloisForLFunctions.HTGeometry.ShellActionRelation
import GaloisForLFunctions.HTGeometry.SublevelTransfer

open Set MeasureTheory Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The criticality product with the tangential block of the distinguished labelling removed. -/
def jointCriticalCofactor (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π₀ : Equiv.Perm (Fin D)) : MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  (jointLeading M c k π₀) ^ 2
    * ∏ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin D))).erase π₀,
        jointCriticalitySquareSum M c k π

/-- **The factorisation on the unit shell.**  The criticality product is the squared tangential
gradient of the distinguished labelled action times the cofactor. -/
theorem eval_jointCriticalProduct_eq_tangential_mul
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ) (π₀ : Equiv.Perm (Fin D))
    {θ : Fin N → ℝ} (hθ : ∑ a, (θ a) ^ 2 = 1) (Dg : Fin N → ℝ)
    (hrel : ∀ x : Fin N → ℝ,
      ∑ n ∈ Finset.range (M + 1),
        MvPolynomial.eval x (c n) * (shellSpectralAction hP k π₀ x) ^ n = 0)
    (hD : ∀ i : Fin N,
      HasDerivAt (fun t : ℝ =>
          shellSpectralAction hP k π₀ (fun j => θ j + (if j = i then t else 0))) (Dg i) 0) :
    MvPolynomial.eval
        (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
        (jointCriticalProduct M c k)
      = tangentialGradNormSq (shellSpectralAction hP k π₀ θ) θ Dg
        * MvPolynomial.eval
            (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
            (jointCriticalCofactor M c k π₀) := by
  classical
  set lam : Fin D → ℝ :=
    fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i with hlam
  set x : Fin D ⊕ Fin N → ℝ := Sum.elim lam θ with hx
  have hact : (∑ j, k j * lam (π₀ j)) = shellSpectralAction hP k π₀ θ := rfl
  have hblock : MvPolynomial.eval x (jointCriticalitySquareSum M c k π₀)
      = (MvPolynomial.eval x (jointLeading M c k π₀)) ^ 2
        * tangentialGradNormSq (shellSpectralAction hP k π₀ θ) θ Dg := by
    rw [eval_jointCriticalitySquareSum_eq]
    have hval : ∀ i : Fin N, MvPolynomial.eval x (jointCriticality M c k π₀ i)
        = criticalityValue (M + 1) c θ (shellSpectralAction hP k π₀ θ) i := by
      intro i
      rw [hx, eval_jointCriticality_of_unit M c k π₀ i lam hθ, hact]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => by rw [hval i]]
    rw [criticalitySquareSum_eq_leading_sq_mul Dg hrel hD]
    congr 2
    rw [hx, eval_jointLeading, hact]
  have hprod : MvPolynomial.eval x (jointCriticalProduct M c k)
      = MvPolynomial.eval x (jointCriticalitySquareSum M c k π₀)
        * ∏ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin D))).erase π₀,
            MvPolynomial.eval x (jointCriticalitySquareSum M c k π) := by
    rw [jointCriticalProduct, map_prod]
    exact (Finset.mul_prod_erase (Finset.univ : Finset (Equiv.Perm (Fin D)))
      (fun π => MvPolynomial.eval x (jointCriticalitySquareSum M c k π))
      (Finset.mem_univ π₀)).symm
  have hcof : MvPolynomial.eval x (jointCriticalCofactor M c k π₀)
      = (MvPolynomial.eval x (jointLeading M c k π₀)) ^ 2
        * ∏ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin D))).erase π₀,
            MvPolynomial.eval x (jointCriticalitySquareSum M c k π) := by
    rw [jointCriticalCofactor, MvPolynomial.eval_mul, MvPolynomial.eval_pow, map_prod]
  rw [hprod, hblock, hcof]
  ring

section Sphere

variable {m : ℕ}

theorem sphere_abs_coord_le_one (ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (i : Fin (m + 1)) : |(WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i| ≤ 1 := by
  have hnorm : ‖(ω : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have := PiLp.norm_apply_le (ω : EuclideanSpace ℝ (Fin (m + 1))) i
  rw [hnorm] at this
  simpa [Real.norm_eq_abs] using this

theorem sphere_sum_sq_coord (ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ∑ i, ((WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i) ^ 2 = 1 := by
  have hnorm : ‖(ω : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  rw [EuclideanSpace.norm_eq] at hnorm
  have hsq := Real.sqrt_eq_one.mp hnorm
  have hcongr : ∑ i, ((WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i) ^ 2
      = ∑ i, ‖(WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  exact hcongr.trans hsq

/-- **The transversality power law.**  The shell measure of the sublevel sets of the squared
tangential gradient of a labelled spectral action decays like a fixed power. -/
theorem exists_toSphere_sublevel_le_shellCriticality
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (M : ℕ) (c : ℕ → MvPolynomial (Fin (m + 1)) ℝ) (hc : ∀ n, (c n).IsHomogeneous (M - n))
    (k : Fin D → ℝ) (π₀ : Equiv.Perm (Fin D))
    (hrel : ∀ x : Fin (m + 1) → ℝ,
      ∑ n ∈ Finset.range (M + 1),
        MvPolynomial.eval x (c n) * (shellSpectralAction hP k π₀ x) ^ n = 0)
    (Dg : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → Fin (m + 1) → ℝ)
    (hD : ∀ (ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (i : Fin (m + 1)),
      HasDerivAt (fun t : ℝ => shellSpectralAction hP k π₀
          (fun j => (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) j
            + (if j = i then t else 0))) (Dg ω i) 0)
    (θ₀ : Fin (m + 1) → ℝ)
    (hwitness : ∀ π : Equiv.Perm (Fin D),
      MvPolynomial.eval
          (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) θ₀)
          (jointCriticalitySquareSum M c k π) ≠ 0) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ g : ℝ, 0 ≤ g →
      volume.toSphere
          {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
            tangentialGradNormSq
                (shellSpectralAction hP k π₀
                  (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))))
                (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) (Dg ω) ≤ g}
        ≤ A * ENNReal.ofReal
            (g ^ ((1 : ℝ) / (((Finset.univ : Finset (Equiv.Perm (Fin D))).card
              * ((M + 1) * 2) : ℕ) : ℝ))) := by
  classical
  obtain ⟨G, hG⟩ := exists_shellPoly_jointCriticalProduct hP M c k
  have hG0 : G ≠ 0 :=
    shellPoly_ne_zero_of_eval_ne_zero
      (eval_shellPoly_ne_zero_of_forall hP M c k G hG θ₀ hwitness)
  have hGscale : ∀ (t : ℝ) (y : Fin (m + 1) → ℝ),
      MvPolynomial.eval (fun a => t * y a) G
        = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2))
          * MvPolynomial.eval y G :=
    fun t y => eval_shellPoly_jointCriticalProduct_smul hP M c hc k G hG t y
  have hhom : G.IsHomogeneous
      ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2)) :=
    isHomogeneous_of_eval_smul hGscale
  have hdpos : 0 < (Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2) := by
    refine Nat.mul_pos ?_ (by positivity)
    rw [Finset.card_univ]
    exact Fintype.card_pos
  obtain ⟨C, hC, hCbound⟩ := exists_bound_eval_joint hP (jointCriticalCofactor M c k π₀)
  refine exists_toSphere_sublevel_le_of_dominated hdpos G hhom hG0 hC ?_
  intro ω
  set y : Fin (m + 1) → ℝ := WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1))) with hy
  have hcoord : ∀ a, |y a| ≤ 1 := fun a => sphere_abs_coord_le_one ω a
  have hunit : ∑ a, (y a) ^ 2 = 1 := sphere_sum_sq_coord ω
  have hsplit := eval_jointCriticalProduct_eq_tangential_mul hP M c k π₀ hunit (Dg ω) hrel
    (fun i => hD ω i)
  rw [hG y, hsplit, abs_mul,
    abs_of_nonneg (tangentialGradNormSq_nonneg (shellSpectralAction hP k π₀ y) y (Dg ω)),
    mul_comm]
  exact mul_le_mul_of_nonneg_right (hCbound y hcoord)
    (tangentialGradNormSq_nonneg (shellSpectralAction hP k π₀ y) y (Dg ω))

end Sphere

end

end GaloisForLFunctions.HTGeometry
