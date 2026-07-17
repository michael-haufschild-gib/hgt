import GaloisForLFunctions.HTGeometry.Hypertranscendence
import GaloisForLFunctions.HTGeometry.TorsionFaceExactification
import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance
import GaloisForLFunctions.HTGeometry.GeometricTorsionLanguageRelationExclusion
import GaloisForLFunctions.HTGeometry.GeometricPeriodicLeastLevel
import GaloisForLFunctions.HTGeometry.GeometricPeriodicEveryLevel

/-!
# Geometric Taylor magnitudes and torsion-language exactification

The geometric TLU theorem is proved by constructing its finite locked face and applying the
project-internal Fourier exactifier.  For exact profiles with eventually periodic phase, the
finite exponential cascade, arithmetic-progression phase lock, ADE active-complement estimate,
least-level identity, singleton obstruction, and algebraic-tie consequence are also constructed
internally.  The compatibility inputs below are retained only for callers that already package
their own level families.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MvPolynomial PowerSeries Topology

noncomputable section

/-- The exact output of Mahler normalization, balanced survival, and geometric face confinement
for a torsion-language-universal Taylor phase.  These named analytic parents are data, not axioms. -/
structure GeometricTLULockedFaceInput
    (f : ℂ → ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  torsionOrder : ℕ
  jetDegree : ℕ
  degree_lt_torsionOrder : jetDegree < torsionOrder
  face : Finset (ι → ℕ)
  weight : (ι → ℕ) → ℂ
  multiplicity_le : ∀ e ∈ face, ∀ i, e i ≤ jetDegree
  nonzeroWeight_of_differentiallyAlgebraic :
    DifferentiallyAlgebraic f → ∃ e ∈ face, weight e ≠ 0
  torsionFaceVanishes_of_differentiallyAlgebraic :
    DifferentiallyAlgebraic f →
      ∀ s : ι → ℂ, (∀ i, s i ^ torsionOrder = 1) →
        ∑ e ∈ face, weight e * ∏ i, s i ^ e i = 0

/-- **Geometric TLU hypertranscendence.**  Once the geometric profile locks every possible ADE to
the finite face supplied by `GeometricTLULockedFaceInput`, torsion Fourier separation forces all
face weights to vanish, contradicting balanced survival. -/
theorem hypertranscendental_of_geometricTLU_lockedFace
    {f : ℂ → ℂ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (input : GeometricTLULockedFaceInput f ι) : Hypertranscendental f := by
  intro hDA
  obtain ⟨e, he, hweight⟩ := input.nonzeroWeight_of_differentiallyAlgebraic hDA
  have hall := GaloisForLFunctions.face_weights_eq_zero
    input.degree_lt_torsionOrder input.face input.multiplicity_le input.weight
    (input.torsionFaceVanishes_of_differentiallyAlgebraic hDA)
  exact hweight (hall e he)

set_option maxHeartbeats 2000000 in
/-- **Unconditional geometric TLU hypertranscendence.**  An exact geometric Taylor
log-magnitude with a convergent additive correction and a torsion-language-universal unit phase
admits no algebraic differential equation.  The balanced survivor, finite locked face,
exponential confinement, and Fourier exactification are all constructed internally. -/
theorem hypertranscendental_of_geometric_torsionLanguageUniversal
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {u : ℕ → ℂ} {A lam c₀ : ℝ}
    (hA : 0 < A) (hlam : 1 < lam)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds c₀))
    (hbpos : ∀ i, 0 < A * lam ^ i + c i)
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS f) =
      ((Real.exp (-(A * lam ^ i + c i)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', Q, hQ, hQint, hrel⟩ := formal_mahler_integer_normalization hP hformal
  have hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ =
      Real.exp (-(A * lam ^ i + c i)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    (taylorPS f) hb Q hQ hQint hrel
  obtain ⟨anchor, ha, haD, _haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n' anchor
  have hD : 0 < D := by simpa [D, haD] using hDpos
  have hDmax : D = magnitudeMaxJetDegree n' Q := by simpa [D] using haD
  obtain ⟨K, M, p, Q₀, hpcount, hp⟩ :=
    exists_eventually_boundedPattern_nonzero_aevalWeight_residue
      ha (by simpa [D] using hD) 0 (by simpa [D] using hD)
  have hpweight : ∀ᶠ q : ℕ in atTop,
      aevalWeight n' (D * q + 0) Q (shiftedAtomPatternKey q K p) ≠ 0 := by
    filter_upwards [eventually_ge_atTop Q₀] with q hq
    simpa [D] using (hp q hq).2
  have hgrowth : UniformGeometricGrowth (fun i => A * lam ^ i + c i) :=
    uniformGeometricGrowth_hierarchical hlam hA
      (isLittleO_constPow_of_tendsto hlam hc)
  exact GaloisForLFunctions.no_integerADE_of_geometric_torsionLanguageUniversal
    (F := taylorPS f) (u := u) (A := A) (lam := lam) (c₀ := c₀) (c := c)
    hA hlam hc hbpos hgrowth hcoeff huNorm hu
    (n := n') (D := D) (K₀ := K) (τ := 0) (M₀ := M)
    Q hrel hD hDmax p hpcount hpweight

set_option maxHeartbeats 1200000 in
/-- Eventual paper form of geometric TLU hypertranscendence.  An arbitrary finite Taylor prefix is
removed by a polynomial correction; the geometric correction and phase are changed only on that
finite prefix, so convergence and torsion-language universality are preserved. -/
theorem hypertranscendental_of_eventually_geometric_torsionLanguageUniversal
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {u : ℕ → ℂ} {A lam c₀ : ℝ}
    (hA : 0 < A) (hlam : 1 < lam)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds c₀))
    (hcoeff : ∀ᶠ i : ℕ in atTop, PowerSeries.coeff i (taylorPS f) =
      ((Real.exp (-(A * lam ^ i + c i)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ᶠ i : ℕ in atTop, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u) :
    Hypertranscendental f := by
  have hcLittle := isLittleO_constPow_of_tendsto hlam hc
  have hbposEv : ∀ᶠ i : ℕ in atTop, 0 < A * lam ^ i + c i :=
    eventually_pos_hierarchical hlam hA hcLittle
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp ((hcoeff.and huNorm).and hbposEv)
  let F := taylorPS f
  let p := finiteTaylorCorrection F T
  let g : ℂ → ℂ := fun z => f z + p.eval z
  let u' : ℕ → ℂ := fun i => if i < T then 1 else u i
  let c' : ℕ → ℝ := fun i => if i < T then 1 - A * lam ^ i else c i
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hg : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hcoeff' : ∀ i, PowerSeries.coeff i (taylorPS g) =
      ((Real.exp (-(A * lam ^ i + c' i)) : ℝ) : ℂ) * u' i := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe, coeff_finiteTaylorCorrection]
    by_cases hi : i < T
    · simp [c', u', hi]
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      simpa [F, c', u', hi] using (hT i hiT).1.1
  have huNorm' : ∀ i, ‖u' i‖ = 1 := by
    intro i
    by_cases hi : i < T
    · simp [u', hi]
    · simpa [u', hi] using (hT i (Nat.le_of_not_gt hi)).1.2
  have hcEq : c' =ᶠ[atTop] c := by
    filter_upwards [eventually_ge_atTop T] with i hi
    simp [c', Nat.not_lt.mpr hi]
  have hc' : Tendsto c' atTop (nhds c₀) := hc.congr' hcEq.symm
  have hbpos' : ∀ i, 0 < A * lam ^ i + c' i := by
    intro i
    by_cases hi : i < T
    · simp [c', hi]
    · simpa [c', hi] using (hT i (Nat.le_of_not_gt hi)).2
  have huEq : u' =ᶠ[atTop] u := by
    filter_upwards [eventually_ge_atTop T] with i hi
    simp [u', Nat.not_lt.mpr hi]
  have hu' : TorsionLanguageUniversal u' := hu.of_eventuallyEq huEq
  have hght : Hypertranscendental g :=
    hypertranscendental_of_geometric_torsionLanguageUniversal
      hg hA hlam hc' hbpos' hcoeff' huNorm' hu'
  exact (hypertranscendental_add_polynomial_iff hf p).mp hght

/-- Exact input for all valuation levels of an eventually periodic phase on the exact geometric
profile.  The exponentially separated ADE cascade supplies the convergent level polynomials. -/
structure GeometricPeriodicLevelInput (κ : Type*) where
  levelPolynomial : κ → Polynomial ℂ
  levelSubsequence : κ → ℕ → ℕ
  levelSubsequence_strictMono : ∀ k, StrictMono (levelSubsequence k)
  levelPolynomial_tendsto_zero : ∀ k,
    Tendsto (fun n => (levelPolynomial k).eval
      (((levelSubsequence k n : ℕ) : ℂ))) atTop (nhds 0)

/-- **Level-exactness law.** Every valuation-level polynomial in an exact geometric profile with
eventually periodic phase vanishes identically. -/
theorem geometricPeriodic_everyLevelPolynomial_eq_zero
    {κ : Type*} (input : GeometricPeriodicLevelInput κ) :
    ∀ k, input.levelPolynomial k = 0 := by
  intro k
  exact GaloisForLFunctions.polynomial_eq_zero_of_tendsto_zero
    (input.levelPolynomial k) (input.levelSubsequence k)
    (input.levelSubsequence_strictMono k) (input.levelPolynomial_tendsto_zero k)

/-- A singleton admissible level carrying a nonzero grouped weight is impossible. -/
theorem geometricPeriodic_no_nonzero_level
    {κ : Type*} (input : GeometricPeriodicLevelInput κ) :
    ¬ ∃ k, input.levelPolynomial k ≠ 0 := by
  rintro ⟨k, hk⟩
  exact hk (geometricPeriodic_everyLevelPolynomial_eq_zero input k)

/-- The already checked magnitude-side corollary used by the geometric column: a DA series with a
finite successive log-magnitude ratio greater than one forces that ratio to be algebraic. -/
theorem geometricProfile_da_forces_algebraic_ratio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hDA : DifferentiallyAlgebraic f) :
    IsAlgebraic ℤ lam :=
  logRatio_isAlgebraic_of_eventually_differentiallyAlgebraic
    hf hb hbpos hlam hlam1 hDA

end

end GaloisForLFunctions.HTGeometry
