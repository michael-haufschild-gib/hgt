import GaloisForLFunctions.HTGeometry.SchwartzSmoothMultiplierSymmetry

/-!
# Canonical local diagonal functionals for momentum-symmetric Schwartz forms

A canonical compact spectral cutoff removes the arbitrary auxiliary function from compact-packet
diagonal factorization.  The resulting local functionals stabilize as the cutoff radius grows, and
nonnegativity of the original form becomes positivity on every smooth compactly supported modulus
square.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial

noncomputable section

namespace SchwartzMap

@[simp] theorem compactIntervalCutoff_apply_of_abs_le_add_one
    (R : ℝ) {t : ℝ} (ht : |t| ≤ |R| + 1) :
    compactIntervalCutoff R t = 1 := by
  rw [compactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  change (b t : ℂ) = 1
  have hmem : t ∈ Metric.closedBall (0 : ℝ) b.rIn := by
    rw [Metric.mem_closedBall]
    change dist t 0 ≤ |R| + 1
    simpa only [Real.dist_0_eq_abs] using ht
  exact_mod_cast b.one_of_mem_closedBall hmem

/-- Every canonical interval cutoff has compact support. -/
theorem compactIntervalCutoff_hasCompactSupport (R : ℝ) :
    HasCompactSupport (compactIntervalCutoff R) := by
  rw [HasCompactSupport, compactIntervalCutoff_tsupport]
  have heq : {t : ℝ | |t| ≤ |R| + 2} = Metric.closedBall (0 : ℝ) (|R| + 2) := by
    ext t
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, Set.mem_setOf_eq]
  rw [heq]
  exact isCompact_closedBall _ _

/-- If two canonical cutoffs have inner radii beyond a compact packet, their difference is
supported strictly outside that packet. -/
theorem tsupport_sub_compactIntervalCutoff_subset_abs_ge_add_one
    {R S T : ℝ} (hS : R ≤ |S|) (hT : R ≤ |T|) :
    tsupport (compactIntervalCutoff S - compactIntervalCutoff T) ⊆
      {t : ℝ | R + 1 ≤ |t|} := by
  have hclosed : IsClosed {t : ℝ | R + 1 ≤ |t|} :=
    isClosed_le continuous_const continuous_abs
  rw [tsupport]
  apply hclosed.closure_subset_iff.mpr
  intro t ht
  by_contra hnot
  have hlt : |t| < R + 1 := lt_of_not_ge hnot
  have hsone : compactIntervalCutoff S t = 1 :=
    compactIntervalCutoff_apply_of_abs_le_add_one S (by linarith)
  have htone : compactIntervalCutoff T t = 1 :=
    compactIntervalCutoff_apply_of_abs_le_add_one T (by linarith)
  apply ht
  simp [hsone, htone]

/-- The local diagonal functional is independent of every sufficiently large canonical cutoff. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_compactIntervalCutoff_stable
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (h : SchwartzMap ℝ ℂ) {R S T : ℝ}
    (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R})
    (hS : R ≤ |S|) (hT : R ≤ |T|) :
    Q.fourierPullback h (compactIntervalCutoff S) =
      Q.fourierPullback h (compactIntervalCutoff T) := by
  let d : SchwartzMap ℝ ℂ := compactIntervalCutoff S - compactIntervalCutoff T
  have hdcompact : IsCompact (tsupport d) := by
    exact (compactIntervalCutoff_hasCompactSupport S).sub
      (compactIntervalCutoff_hasCompactSupport T)
  have hdis : Disjoint (tsupport h) (tsupport d) := by
    apply Set.disjoint_left.mpr
    intro t hth htd
    have hle : |t| ≤ R := hh hth
    have hge : R + 1 ≤ |t| :=
      tsupport_sub_compactIntervalCutoff_subset_abs_ge_add_one hS hT htd
    linarith
  have hzero := Q.fourierPullback_eq_zero_of_disjoint_compact_tsupport hQ
    h d (show IsCompact (tsupport h) from ?_) hdcompact hdis
  · change Q.fourierPullback h
      (compactIntervalCutoff S - compactIntervalCutoff T) = 0 at hzero
    rw [Q.fourierPullback.apply_sub_right] at hzero
    exact sub_eq_zero.mp hzero
  · exact IsCompact.of_isClosed_subset
      (isCompact_Icc : IsCompact (Set.Icc (-R) R)) (isClosed_tsupport h) (by
        intro t ht
        have habs := hh ht
        exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩)

/-- The local diagonal functional obtained by testing the second slot against the canonical
interval cutoff. -/
def ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional
    (Q : ContinuousSchwartzSesquilinearForm) (R : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ where
  toFun h := Q.fourierPullback h (compactIntervalCutoff R)
  map_add' f g := Q.fourierPullback.apply_add_left f g _
  map_smul' c f := by
    rw [Q.fourierPullback.apply_smul_left]
    rfl
  cont := Q.fourierPullback.continuous.comp
    (continuous_id.prodMk continuous_const)

@[simp] theorem ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_apply
    (Q : ContinuousSchwartzSesquilinearForm) (R : ℝ) (h : SchwartzMap ℝ ℂ) :
    Q.compactIntervalDiagonalFunctional R h =
      Q.fourierPullback h (compactIntervalCutoff R) := rfl

/-- On a compact packet, the local diagonal functional sends the modulus square to the original
quadratic value. -/
theorem ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_pointwiseMulConj_self
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (f : SchwartzMap ℝ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ R}) :
    Q.compactIntervalDiagonalFunctional R (pointwiseMulConj f f) =
      Q.fourierPullback f f := by
  rw [Q.compactIntervalDiagonalFunctional_apply]
  symm
  apply Q.fourierPullback_eq_product_cutoff hQ (T := R + 2) (by linarith)
  · intro t ht
    have hle : |t| ≤ R := hf ht
    change |t| ≤ R + 2
    linarith
  · rw [compactIntervalCutoff_tsupport]
    intro t ht
    change |t| ≤ R + 2
    simpa [abs_of_nonneg hR] using ht
  · intro t ht
    apply compactIntervalCutoff_apply_of_abs_le
    simpa [abs_of_nonneg hR] using hf ht

/-- Positivity of the form becomes positivity of the local diagonal functional on every compactly
supported smooth modulus square. -/
theorem ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_square_nonnegative
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hf : tsupport f ⊆ {t : ℝ | |t| ≤ R}) :
    0 ≤ (Q.compactIntervalDiagonalFunctional R (pointwiseMulConj f f)).re ∧
      (Q.compactIntervalDiagonalFunctional R (pointwiseMulConj f f)).im = 0 := by
  rw [Q.compactIntervalDiagonalFunctional_pointwiseMulConj_self hQ f hR hf]
  exact Q.fourierPullback_isNonnegative hQnonneg f

end SchwartzMap

