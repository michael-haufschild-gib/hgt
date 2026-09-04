import GaloisForLFunctions.HTGeometry.StrelitzMaximumPointSlopeSign

/-!
# Right-half-plane phase of nonnegative Strelitz edges

At maximum-modulus points the observed second Euler jet has nonnegative real part.  For a
nonnegative Newton exponent, absolute root proximity survives division by the Newton scale.
Therefore the matched nonzero edge root lies in the closed right half-plane.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Set
open GaloisForLFunctions

/-- At a nonnegative Newton exponent, absolute proximity between the observed second jet and the
selected algebraic root survives Newton normalization. -/
theorem tendsto_strelitzJetCurveNormalizedSecondJet_of_nonnegativeSlope
    {u v root : ℕ → ℂ} {p : ℝ} {idx : ℕ → ℕ} {c : ℂ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hidx : StrictMono idx) (hp : 0 ≤ p)
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0))
    (hnormalized : Tendsto
      (fun n => strelitzJetCurveNormalizedRoot u root p (idx n)) atTop (nhds c)) :
    Tendsto (fun n => strelitzJetCurveNormalizedRoot u v p (idx n)) atTop (nhds c) := by
  have huSub : Tendsto (fun n => ‖u (idx n)‖) atTop atTop :=
    huTop.comp hidx.tendsto_atTop
  have hcloseSub : Tendsto (fun n => ‖v (idx n) - root (idx n)‖) atTop (nhds 0) := by
    simpa [Function.comp_def] using hclose.comp hidx.tendsto_atTop
  have hdiffNorm : Tendsto (fun n =>
      ‖strelitzJetCurveNormalizedRoot u v p (idx n) -
        strelitzJetCurveNormalizedRoot u root p (idx n)‖) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
      _ hcloseSub
    filter_upwards [huSub.eventually_ge_atTop 1] with n hun
    have hden : 1 ≤ ‖u (idx n)‖ ^ p := Real.one_le_rpow hun hp
    simp only [strelitzJetCurveNormalizedRoot]
    rw [← sub_div, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one hden)]
    exact div_le_self (norm_nonneg _) hden
  have hdiff : Tendsto (fun n =>
      strelitzJetCurveNormalizedRoot u v p (idx n) -
        strelitzJetCurveNormalizedRoot u root p (idx n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hdiffNorm
  simpa only [sub_add_cancel, zero_add] using hdiff.add hnormalized

/-- A nonnegative-real-part second jet can only converge after nonnegative Newton normalization
to a point in the closed right half-plane. -/
theorem re_nonneg_of_tendsto_strelitzJetCurveNormalizedRoot_of_nonnegativeSlope
    {u v root : ℕ → ℂ} {p : ℝ} {idx : ℕ → ℕ} {c : ℂ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hidx : StrictMono idx) (hp : 0 ≤ p)
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0))
    (hvre : ∀ n : ℕ, 0 ≤ (v n).re)
    (hnormalized : Tendsto
      (fun n => strelitzJetCurveNormalizedRoot u root p (idx n)) atTop (nhds c)) :
    0 ≤ c.re := by
  have hnormalizedV := tendsto_strelitzJetCurveNormalizedSecondJet_of_nonnegativeSlope
    huTop hidx hp hclose hnormalized
  have hre : Tendsto
      (fun n => (strelitzJetCurveNormalizedRoot u v p (idx n)).re)
      atTop (nhds c.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hnormalizedV
  have huSub : Tendsto (fun n => ‖u (idx n)‖) atTop atTop :=
    huTop.comp hidx.tendsto_atTop
  apply isClosed_Ici.mem_of_tendsto hre
  filter_upwards [huSub.eventually_gt_atTop 0] with n hun
  have hden : 0 ≤ ‖u (idx n)‖ ^ p := (Real.rpow_pos_of_pos hun p).le
  rw [strelitzJetCurveNormalizedRoot, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  simp
  exact div_nonneg (mul_nonneg (hvre (idx n)) hden) (mul_self_nonneg _)

/-- Complete nonnegative-slope matched edge data, including the right-half-plane phase forced by
maximum-modulus curvature. -/
def HasStrelitzJetCurveRightHalfPlaneMatchedNewtonEdgeLimit
    (S : MvPolynomial (Fin 2) ℂ) (u root : ℕ → ℂ) : Prop :=
  ∃ i ∈ (strelitzJetCurvePolynomial S).support,
    ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
          (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
        (∀ k ∈ (strelitzJetCurvePolynomial S).support,
          strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) k ≤
            strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i) ∧
        (0 ≤ strelitzJetCurveNewtonSlope S i j ∧
          strelitzJetCurveNewtonSlope S i j < 2) ∧
        ∃ c : ℂ, c ≠ 0 ∧ 0 ≤ c.re ∧
          (strelitzJetCurveNewtonEdgePolynomial S
            (strelitzJetCurveNewtonSlope S i j)
            (strelitzJetCurveNewtonWeight S
              (strelitzJetCurveNewtonSlope S i j) i)).IsRoot c ∧
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            Tendsto (fun m => strelitzJetCurveNormalizedRoot u root
              (strelitzJetCurveNewtonSlope S i j) (ns (τ m))) atTop (nhds c)

/-- Maximum-point curvature upgrades every matched nonnegative Strelitz edge to one whose selected
nonzero edge root lies in the closed right half-plane. -/
theorem hasStrelitzJetCurveRightHalfPlaneMatchedNewtonEdgeLimit_of_nonnegative
    {S : MvPolynomial (Fin 2) ℂ} {u v root : ℕ → ℂ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0))
    (hvre : ∀ n : ℕ, 0 ≤ (v n).re)
    (hmatched : HasStrelitzJetCurveMatchedNewtonEdgeLimitWith
      (fun p => 0 ≤ p ∧ p < 2) S u root) :
    HasStrelitzJetCurveRightHalfPlaneMatchedNewtonEdgeLimit S u root := by
  obtain ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, hp,
    c, hc, hcEdge, τ, hτ, hcLim⟩ := hmatched
  have hidx : StrictMono (fun m => ns (τ m)) := hns.comp hτ
  have hcre : 0 ≤ c.re :=
    re_nonneg_of_tendsto_strelitzJetCurveNormalizedRoot_of_nonnegativeSlope
      huTop hidx hp.1 hclose hvre hcLim
  exact ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, hp,
    c, hc, hcre, hcEdge, τ, hτ, hcLim⟩

variable {a : ℕ → ℂ}

/-- Under precisely the order-two entire-heat assumptions, the maximum-point Strelitz alternative
has a right-half-plane edge root in its nonnegative branch.  Negative and exact-zero branches are
retained without weakening. -/
theorem exists_strelitzMaximumPointSlopePhaseTrichotomy_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      1 ≤ (strelitzJetCurvePolynomial S).natDegree ∧
      ∃ (x : ℕ → ℝ) (z root : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => ‖eulerLogDeriv (coeffFun a) (z n)‖) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          (strelitzJetCurveSpecialization S
            (eulerLogDeriv (coeffFun a) (z n))).IsRoot (root n)) ∧
        Tendsto (fun n =>
          ‖eulerLogDerivSecond (coeffFun a) (z n) - root n‖) atTop (nhds 0) ∧
        (HasStrelitzJetCurveRightHalfPlaneMatchedNewtonEdgeLimit S
              (fun n => eulerLogDeriv (coeffFun a) (z n)) root ∨
          (HasStrelitzJetCurveMatchedNewtonEdgeLimitWith (fun p => p < 0) S
                (fun n => eulerLogDeriv (coeffFun a) (z n)) root ∧
            ∃ idx : ℕ → ℕ, StrictMono idx ∧
              Tendsto (fun n => ‖root (idx n)‖) atTop (nhds 0) ∧
              Tendsto (fun n => ‖eulerLogDerivSecond (coeffFun a) (z (idx n))‖)
                atTop (nhds 0)) ∨
          ((Polynomial.X ∣ strelitzJetCurvePolynomial S) ∧
            ∃ ns : ℕ → ℕ, StrictMono ns ∧
              (∀ k, root (ns k) = 0) ∧
              Tendsto (fun k => ‖eulerLogDerivSecond (coeffFun a) (z (ns k))‖)
                atTop (nhds 0))) ∧
        StrelitzMaximumPointJetSigns a z := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, htri, hsigns⟩ :=
    exists_strelitzMaximumPointSlopeSignTrichotomy_of_order_two_entireHeat
      ha hheat htrans hDA
  refine ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, ?_, hsigns⟩
  rcases htri with hnonneg | hrest
  · exact Or.inl
      (hasStrelitzJetCurveRightHalfPlaneMatchedNewtonEdgeLimit_of_nonnegative
        huTop hclose hsigns.secondJet_re_nonneg hnonneg)
  · exact Or.inr hrest

end

end GaloisForLFunctions.HTGeometry
