import GaloisForLFunctions.HTGeometry.StrelitzEntireHeatSubquadraticFactorDichotomy

/-!
# Sign classification of Strelitz Newton branches

The heat-scale reduction has already removed every radial power from the fixed leading jet curve.
Its remaining matched Newton slope therefore splits into two exact regimes.  A nonnegative slope
stays below two.  A negative slope forces both the selected curve root and the observed second
logarithmic jet to zero along the final cofinal subsequence.  The recurrent exact-zero branch keeps
its literal factor by the second-jet variable.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter
open GaloisForLFunctions

/-- Complete matched Newton-edge data with an arbitrary predicate imposed on its slope. -/
def HasStrelitzJetCurveMatchedNewtonEdgeLimitWith
    (slopeCondition : ℝ → Prop) (S : MvPolynomial (Fin 2) ℂ)
    (u root : ℕ → ℂ) : Prop :=
  ∃ i ∈ (strelitzJetCurvePolynomial S).support,
    ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
          (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
        (∀ k ∈ (strelitzJetCurvePolynomial S).support,
          strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) k ≤
            strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i) ∧
        slopeCondition (strelitzJetCurveNewtonSlope S i j) ∧
        ∃ c : ℂ, c ≠ 0 ∧
          (strelitzJetCurveNewtonEdgePolynomial S
            (strelitzJetCurveNewtonSlope S i j)
            (strelitzJetCurveNewtonWeight S
              (strelitzJetCurveNewtonSlope S i j) i)).IsRoot c ∧
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            Tendsto (fun m => strelitzJetCurveNormalizedRoot u root
              (strelitzJetCurveNewtonSlope S i j) (ns (τ m))) atTop (nhds c)

/-- A matched normalization at a negative Newton slope forces the unnormalized roots to zero along
the same cofinal subsequence. -/
theorem tendsto_norm_strelitzJetCurveRoot_zero_of_negative_normalized
    {u root : ℕ → ℂ} {p : ℝ} {idx : ℕ → ℕ} {c : ℂ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) (hidx : StrictMono idx)
    (hp : p < 0)
    (hnormalized : Tendsto
      (fun n => strelitzJetCurveNormalizedRoot u root p (idx n)) atTop (nhds c)) :
    Tendsto (fun n => ‖root (idx n)‖) atTop (nhds 0) := by
  have huSub : Tendsto (fun n => ‖u (idx n)‖) atTop atTop :=
    huTop.comp hidx.tendsto_atTop
  have hpow : Tendsto (fun n => ‖u (idx n)‖ ^ p) atTop (nhds 0) :=
    tendsto_rpow_const_zero_of_tendsto_atTop huSub hp
  have hprod : Tendsto (fun n =>
      ‖strelitzJetCurveNormalizedRoot u root p (idx n)‖ * ‖u (idx n)‖ ^ p)
      atTop (nhds 0) := by
    convert hnormalized.norm.mul hpow using 1
    simp
  refine hprod.congr' ?_
  filter_upwards [huSub.eventually_gt_atTop 0] with n hun
  have hpowPos : 0 < ‖u (idx n)‖ ^ p := Real.rpow_pos_of_pos hun p
  rw [strelitzJetCurveNormalizedRoot, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpowPos]
  exact div_mul_cancel₀ ‖root (idx n)‖ hpowPos.ne'

/-- A negative matched branch also forces the observed second logarithmic jet to zero whenever the
selected exact roots approximate it. -/
theorem tendsto_norm_secondJet_zero_of_negative_normalized
    {u v root : ℕ → ℂ} {p : ℝ} {idx : ℕ → ℕ} {c : ℂ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) (hidx : StrictMono idx)
    (hp : p < 0)
    (hnormalized : Tendsto
      (fun n => strelitzJetCurveNormalizedRoot u root p (idx n)) atTop (nhds c))
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    Tendsto (fun n => ‖v (idx n)‖) atTop (nhds 0) := by
  have hroot := tendsto_norm_strelitzJetCurveRoot_zero_of_negative_normalized
    huTop hidx hp hnormalized
  have hcloseSub : Tendsto (fun n => ‖v (idx n) - root (idx n)‖)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using hclose.comp hidx.tendsto_atTop
  have hupper : ∀ n,
      ‖v (idx n)‖ ≤ ‖v (idx n) - root (idx n)‖ + ‖root (idx n)‖ := by
    intro n
    calc
      ‖v (idx n)‖ = ‖(v (idx n) - root (idx n)) + root (idx n)‖ := by ring_nf
      _ ≤ ‖v (idx n) - root (idx n)‖ + ‖root (idx n)‖ := norm_add_le _ _
  have hsum : Tendsto
      (fun n => ‖v (idx n) - root (idx n)‖ + ‖root (idx n)‖)
      atTop (nhds 0) := by simpa using hcloseSub.add hroot
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
    (Filter.Eventually.of_forall hupper) hsum

/-- Exact sign trichotomy for the strongest local Strelitz alternative.  A negative matched slope
has the additional analytic consequence that both selected roots and observed second jets vanish
on its final cofinal subsequence. -/
theorem strelitzJetCurve_slopeSignTrichotomy_of_subquadraticFactorDichotomy
    {S : MvPolynomial (Fin 2) ℂ} {u v root : ℕ → ℂ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0))
    (hdichotomy :
      HasStrelitzJetCurveSubquadraticMatchedNewtonEdgeLimit S u root ∨
        (Polynomial.X ∣ strelitzJetCurvePolynomial S) ∧
          ∃ ns : ℕ → ℕ, StrictMono ns ∧
            (∀ k, root (ns k) = 0) ∧
            Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0)) :
    HasStrelitzJetCurveMatchedNewtonEdgeLimitWith
        (fun p => 0 ≤ p ∧ p < 2) S u root ∨
      (HasStrelitzJetCurveMatchedNewtonEdgeLimitWith (fun p => p < 0) S u root ∧
        ∃ idx : ℕ → ℕ, StrictMono idx ∧
          Tendsto (fun n => ‖root (idx n)‖) atTop (nhds 0) ∧
          Tendsto (fun n => ‖v (idx n)‖) atTop (nhds 0)) ∨
      ((Polynomial.X ∣ strelitzJetCurvePolynomial S) ∧
        ∃ ns : ℕ → ℕ, StrictMono ns ∧
          (∀ k, root (ns k) = 0) ∧
          Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0)) := by
  rcases hdichotomy with hmatched | hzero
  · obtain ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, hp2,
      c, hc, hcEdge, τ, hτ, hcLim⟩ := hmatched
    by_cases hp0 : 0 ≤ strelitzJetCurveNewtonSlope S i j
    · left
      exact ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, ⟨hp0, hp2⟩,
        c, hc, hcEdge, τ, hτ, hcLim⟩
    · right
      left
      have hpneg : strelitzJetCurveNewtonSlope S i j < 0 := lt_of_not_ge hp0
      let idx : ℕ → ℕ := fun m => ns (τ m)
      have hidx : StrictMono idx := hns.comp hτ
      have hrootZero : Tendsto (fun m => ‖root (idx m)‖) atTop (nhds 0) :=
        tendsto_norm_strelitzJetCurveRoot_zero_of_negative_normalized
          huTop hidx hpneg hcLim
      have hvZero : Tendsto (fun m => ‖v (idx m)‖) atTop (nhds 0) :=
        tendsto_norm_secondJet_zero_of_negative_normalized
          huTop hidx hpneg hcLim hclose
      exact ⟨⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, hpneg,
        c, hc, hcEdge, τ, hτ, hcLim⟩, idx, hidx, hrootZero, hvZero⟩
  · exact Or.inr (Or.inr hzero)

variable {a : ℕ → ℂ}

/-- The slope-sign trichotomy follows under exactly the original order-two entire-heat assumptions,
with every Wiman point, jet bound, exact specialization root, and proximity conclusion retained. -/
theorem exists_strelitzJetCurveSlopeSignTrichotomy_of_order_two_entireHeat_isMaximumOnCircle
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
        (HasStrelitzJetCurveMatchedNewtonEdgeLimitWith (fun p => 0 ≤ p ∧ p < 2) S
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
        (∀ n : ℕ, ∀ w : ℂ, ‖w‖ = ‖z n‖ →
          ‖coeffFun a w‖ ≤ ‖coeffFun a (z n)‖) := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, hdichotomy, hmaxCircle⟩ :=
    exists_strelitzJetCurveSubquadraticFactorDichotomy_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  have htri := strelitzJetCurve_slopeSignTrichotomy_of_subquadraticFactorDichotomy
    huTop hclose hdichotomy
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, htri, hmaxCircle⟩

/-- The slope-sign trichotomy follows under exactly the original order-two entire-heat assumptions,
with every Wiman point, jet bound, exact specialization root, and proximity conclusion retained. -/
theorem exists_strelitzJetCurveSlopeSignTrichotomy_of_order_two_entireHeat
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
        (HasStrelitzJetCurveMatchedNewtonEdgeLimitWith (fun p => 0 ≤ p ∧ p < 2) S
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
                atTop (nhds 0))) := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, htri, _⟩ :=
    exists_strelitzJetCurveSlopeSignTrichotomy_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, htri⟩

end

end GaloisForLFunctions.HTGeometry
