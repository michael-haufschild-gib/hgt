import GaloisForLFunctions.RHTower.ProlateEvenEigenspaceDecomposition

/-!
# The prolate quadratic form detects a low separation mode

On the even part of a live band eigenspace the prolate action is a symmetric endomorphism of a
finite-dimensional space, so its quadratic form is bounded above by its largest eigenvalue.  Read in
the contrapositive: a single vector on which the form exceeds `-K` produces a joint band/prolate
eigenfunction whose prolate eigenvalue exceeds `-K`, that is, whose radial separation ratio is
below `K/c²`.

This is the finite-dimensional half of the variational selection of a low separation mode; the
other half is a test vector on which the form is large.
-/

noncomputable section

open Filter MeasureTheory Set

namespace RHTower

/-- **A large quadratic-form value produces a high prolate eigenvalue.**  If the prolate form on the
even band eigenspace exceeds `-K` at one vector, some even joint band/prolate eigenfunction has
prolate eigenvalue above `-K`. -/
theorem exists_joint_even_prolate_eigen_gt
    {c lam K : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {u : evenBandEigenspace c lam}
    (hu : -K * ‖u‖ ^ (2 : ℕ) < (inner ℝ (prolateOnEvenEigenspace hc hlam u) u : ℝ)) :
    ∃ (eta : ℝ) (Phi : ℝ → ℝ), -K < eta ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  set T := prolateOnEvenEigenspace hc hlam with hT
  have hsym : T.IsSymmetric := isSymmetric_prolateOnEvenEigenspace hc hlam
  set m : ℕ := Module.finrank ℝ (evenBandEigenspace c lam) with hm
  have hn : Module.finrank ℝ (evenBandEigenspace c lam) = m := rfl
  set b := hsym.eigenvectorBasis hn with hb
  set ev := hsym.eigenvalues hn with hev
  have hexists : ∃ j : Fin m, -K < ev j := by
    by_contra hall
    push Not at hall
    have hquad : (inner ℝ (T u) u : ℝ) = ∑ j : Fin m, ev j * (inner ℝ (b j) u : ℝ) ^ (2 : ℕ) := by
      have h1 := b.sum_inner_mul_inner (T u) u
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : (inner ℝ (T u) (b i) : ℝ) = ev i * (inner ℝ (b i) u : ℝ) := by
        rw [hsym u (b i), hsym.apply_eigenvectorBasis hn i, real_inner_smul_right,
          real_inner_comm]
        norm_cast
      rw [h2]
      ring
    have hnorm : ‖u‖ ^ (2 : ℕ) = ∑ j : Fin m, (inner ℝ (b j) u : ℝ) ^ (2 : ℕ) := by
      have h := b.sum_sq_norm_inner_right u
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    have hle : ∑ j : Fin m, ev j * (inner ℝ (b j) u : ℝ) ^ (2 : ℕ)
        ≤ ∑ j : Fin m, (-K) * (inner ℝ (b j) u : ℝ) ^ (2 : ℕ) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hall i) (sq_nonneg _)
    rw [← Finset.mul_sum, ← hnorm] at hle
    linarith [hquad, hle]
  obtain ⟨j, hj⟩ := hexists
  set bf : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨(b j).1, (b j).2.1⟩ with hbf
  refine ⟨ev j, GaloisForLFunctions.RHTower.eigenRep c lam bf, hj,
    GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam bf, ?_, (b j).2.2,
    fun x => GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam bf x, ?_⟩
  · intro hzero
    have hclass := GaloisForLFunctions.RHTower.bandClass_eigenRep hlam bf
    have hstep : GaloisForLFunctions.RHTower.bandClass
        (GaloisForLFunctions.RHTower.eigenRep c lam bf)
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam bf)
        = GaloisForLFunctions.RHTower.bandClass (fun _ : ℝ => (0 : ℝ)) continuous_const :=
      GaloisForLFunctions.RHTower.bandClass_congr _ _ hzero
    have hbot : (bf : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) = 0 := by
      rw [← hclass, hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    have hbj : (b j) = 0 := by
      apply Subtype.ext
      exact hbot
    have hnormone : ‖b j‖ = 1 := b.orthonormal.1 j
    rw [hbj, norm_zero] at hnormone
    exact zero_ne_one hnormone
  · intro x
    have hveq : T (b j) = ev j • b j := hsym.apply_eigenvectorBasis hn j
    have hvaleq :
        GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam bf = ev j • bf := by
      apply Subtype.ext
      exact congrArg (fun w : evenBandEigenspace c lam => w.1) hveq
    have hrepeq := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hvaleq
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrepeq
    have hx := congrFun hrepeq x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (ev j • bf) x =
        ev j * GaloisForLFunctions.RHTower.eigenRep c lam bf x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam (ev j) bf x
    rw [hsmul] at hx
    exact hx

end RHTower
