import GaloisForLFunctions.HTGeometry.EntireFamilyDifferentialAlgebraicLocus
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets

/-!
# The bounded-complexity jet locus on an arbitrary domain

`EntireFamilyDifferentialAlgebraicLocus` decides an algebraic differential equation for an *entire*
function by the vanishing of every square sample minor at nodes accumulating at the origin.  The
same certificate works verbatim on any open preconnected `Ω ⊆ ℂ` once the sample nodes are placed
inside a disc of `Ω`: the identity theorem still upgrades vanishing along an accumulating sequence
to vanishing on all of `Ω`.

This module supplies that domain form.  It is the shared substrate for the compact-open
interlacing law and for the meromorphic translation-spectrum theorems, where the ambient domain is
a pole-free disc rather than the whole plane.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

/-! ## Sample nodes inside a disc -/

/-- Sample nodes inside `Metric.ball z₀ r`, accumulating at `z₀`. -/
def domainSampleNode (z₀ : ℂ) (r : ℝ) (k : ℕ) : ℂ := z₀ + ((r / (k + 2) : ℝ) : ℂ)

theorem dist_domainSampleNode (z₀ : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    dist (domainSampleNode z₀ r k) z₀ = r / (k + 2) := by
  have hpos : (0:ℝ) < r / ((k:ℝ) + 2) := by positivity
  rw [domainSampleNode, dist_eq_norm]
  simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]

theorem domainSampleNode_mem_ball (z₀ : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    domainSampleNode z₀ r k ∈ Metric.ball z₀ r := by
  rw [Metric.mem_ball, dist_domainSampleNode z₀ hr k]
  have h2 : (1:ℝ) < (k : ℝ) + 2 := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  calc r / ((k:ℝ) + 2) < r / 1 := by
        apply div_lt_div_of_pos_left hr one_pos h2
    _ = r := by ring

theorem domainSampleNode_mem_of_ball_subset {Ω : Set ℂ} (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball z₀ r ⊆ Ω) (k : ℕ) : domainSampleNode z₀ r k ∈ Ω :=
  hball (domainSampleNode_mem_ball z₀ hr k)

theorem domainSampleNode_ne (z₀ : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    domainSampleNode z₀ r k ≠ z₀ := by
  intro h
  have := dist_domainSampleNode z₀ hr k
  rw [h, dist_self] at this
  have hpos : (0:ℝ) < r / (k + 2) := by positivity
  exact absurd this.symm (ne_of_gt hpos)

theorem tendsto_domainSampleNode (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (domainSampleNode z₀ r) atTop (𝓝[≠] z₀) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hbase : Tendsto (fun k : ℕ => r / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have h := tendsto_natCast_atTop_atTop (R := ℝ)
      have h2 : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
        h.atTop_add tendsto_const_nhds
      simpa using h2.const_div_atTop r
    have hC : Tendsto (fun k : ℕ => (((r / ((k : ℝ) + 2)) : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hbase
    have hfin := hC.const_add z₀
    show Tendsto (fun k : ℕ => z₀ + (((r / ((k : ℝ) + 2)) : ℝ) : ℂ)) atTop (𝓝 z₀)
    simpa using hfin
  · filter_upwards with k using domainSampleNode_ne z₀ hr k

/-! ## Analyticity of jet monomials on a domain -/

theorem analyticOnNhd_entireJetVector_component {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (n : ℕ) (i : Fin (n + 2)) :
    AnalyticOnNhd ℂ (fun z => entireJetVector f n z i) Ω := by
  induction i using Fin.cases with
  | zero =>
      have : AnalyticOnNhd ℂ (fun z : ℂ => z) Ω := fun z _ => analyticAt_id
      simpa [entireJetVector] using this
  | succ j => simpa [entireJetVector] using analyticOnNhd_iteratedDeriv hf (j : ℕ)

theorem analyticOnNhd_jetMon {f : ℂ → ℂ} {Ω : Set ℂ} (hf : AnalyticOnNhd ℂ f Ω) (n d : ℕ)
    (m : JetExponent n d) : AnalyticOnNhd ℂ (jetMon f n d m) Ω := by
  have heq : jetMon f n d m
      = (∏ i : Fin (n + 2), fun z : ℂ => (entireJetVector f n z i) ^ (m i : ℕ)) := by
    funext z
    simp [jetMon, Finset.prod_apply]
  rw [heq]
  intro z hz
  exact Finset.analyticAt_prod _ fun i _ =>
    (analyticOnNhd_entireJetVector_component hf n i z hz).pow _

/-! ## Bounded-complexity relations on a domain -/

/-- A bounded-exponent linear relation among the differential monomials of `f`, valid on `Ω`. -/
def JetRelationOn (f : ℂ → ℂ) (Ω : Set ℂ) (n d : ℕ) (c : JetExponent n d → ℂ) : Prop :=
  ∀ z ∈ Ω, ∑ m : JetExponent n d, c m * jetMon f n d m z = 0

theorem differentiallyAlgebraicOn_iff_exists_jetRelationOn (f : ℂ → ℂ) (Ω : Set ℂ) :
    DifferentiallyAlgebraicOn f Ω ↔
      ∃ (n d : ℕ) (c : JetExponent n d → ℂ), c ≠ 0 ∧ JetRelationOn f Ω n d c := by
  classical
  constructor
  · rintro ⟨n, P, hP0, hP⟩
    refine ⟨n, P.totalDegree, fun m => MvPolynomial.coeff (jetExponentToFinsupp m) P, ?_, ?_⟩
    · intro hc
      refine hP0 (MvPolynomial.ext P 0 fun μ => ?_)
      by_cases hμ : μ ∈ P.support
      · have hbd : ∀ i, μ i ≤ P.totalDegree := fun i =>
          le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)
        have hmem : jetExponentToFinsupp (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ :
            Fin (P.totalDegree + 1))) = μ := by
          ext i
          rfl
        have := congrFun hc (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ : Fin (P.totalDegree + 1)))
        rw [hmem] at this
        simpa using this
      · simp [MvPolynomial.notMem_support_iff.1 hμ]
    · intro z hz
      have hbd : ∀ μ ∈ P.support, ∀ i, μ i ≤ P.totalDegree := fun μ hμ i =>
        le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)
      have hsum := sum_jetExponent_eq_sum_support (d := P.totalDegree) P hbd
        (fun μ => MvPolynomial.coeff μ P * ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (μ i))
        (fun μ hμ => by simp [MvPolynomial.notMem_support_iff.1 hμ])
      rw [show (∑ m : JetExponent n P.totalDegree,
          (fun m => MvPolynomial.coeff (jetExponentToFinsupp m) P) m * jetMon f n P.totalDegree m z)
          = ∑ m : JetExponent n P.totalDegree,
            (fun μ => MvPolynomial.coeff μ P * ∏ i : Fin (n + 2),
              (entireJetVector f n z i) ^ (μ i)) (jetExponentToFinsupp m) from rfl, hsum,
        ← eval_entireJetVector_eq_sum]
      exact hP z hz
  · rintro ⟨n, d, c, hc0, hrel⟩
    refine ⟨n, ∑ m : JetExponent n d, MvPolynomial.monomial (jetExponentToFinsupp m) (c m), ?_, ?_⟩
    · intro hP
      apply hc0
      funext m
      have := congrArg (MvPolynomial.coeff (jetExponentToFinsupp m)) hP
      rw [MvPolynomial.coeff_sum] at this
      rw [Finset.sum_eq_single m] at this
      · simpa [MvPolynomial.coeff_monomial] using this
      · intro b _ hb
        rw [MvPolynomial.coeff_monomial, if_neg]
        exact fun h => hb (jetExponentToFinsupp_injective h)
      · intro h
        exact absurd (Finset.mem_univ m) h
    · intro z hz
      rw [MvPolynomial.eval_sum]
      have hterm : ∀ m : JetExponent n d,
          MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
            (MvPolynomial.monomial (jetExponentToFinsupp m) (c m))
            = c m * jetMon f n d m z := by
        intro m
        rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
        rfl
      rw [Finset.sum_congr rfl fun m _ => hterm m]
      exact hrel z hz

/-! ## The sample-minor certificate on a domain -/

/-- The sample row of a differential monomial at nodes inside a disc of the domain. -/
def domainJetSampleRow (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ) (m : JetExponent n d) : ℕ → ℂ :=
  fun k => jetMon f n d m (domainSampleNode z₀ r k)

theorem jetRelationOn_iff_rows {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hconn : IsPreconnected Ω) (hf : AnalyticOnNhd ℂ f Ω) (hz₀ : z₀ ∈ Ω)
    (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (hr : 0 < r) (n d : ℕ)
    (c : JetExponent n d → ℂ) :
    JetRelationOn f Ω n d c ↔
      ∀ k : ℕ, ∑ m : JetExponent n d, c m * domainJetSampleRow f z₀ r n d m k = 0 := by
  classical
  refine ⟨fun h k => h _ (hnodes k), fun h => ?_⟩
  have hga : AnalyticOnNhd ℂ (fun z => ∑ m : JetExponent n d, c m * jetMon f n d m z) Ω := by
    have heq : (fun z => ∑ m : JetExponent n d, c m * jetMon f n d m z)
        = ∑ m : JetExponent n d, fun z : ℂ => c m * jetMon f n d m z := by
      funext z
      simp [Finset.sum_apply]
    rw [heq]
    intro z hz
    exact Finset.analyticAt_sum _ fun m _ =>
      analyticAt_const.mul (analyticOnNhd_jetMon hf n d m z hz)
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, (∑ m : JetExponent n d, c m * jetMon f n d m z) = 0 :=
    (tendsto_domainSampleNode z₀ hr).frequently (Filter.Frequently.of_forall fun k => h k)
  have hzero := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn hz₀ hfreq
  intro z hz
  exact hzero hz

theorem exists_jetRelationOn_iff_not_linearIndependent {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hconn : IsPreconnected Ω) (hf : AnalyticOnNhd ℂ f Ω) (hz₀ : z₀ ∈ Ω)
    (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (hr : 0 < r) (n d : ℕ) :
    (∃ c : JetExponent n d → ℂ, c ≠ 0 ∧ JetRelationOn f Ω n d c)
      ↔ ¬ LinearIndependent ℂ (domainJetSampleRow f z₀ r n d) := by
  classical
  rw [Fintype.linearIndependent_iff]
  push Not
  constructor
  · rintro ⟨c, hc0, hrel⟩
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, c m₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc0 (funext hall)
    refine ⟨c, ?_, m₀, hm₀⟩
    funext k
    have := (jetRelationOn_iff_rows hconn hf hz₀ hnodes hr n d c).1 hrel k
    simpa [Finset.sum_apply] using this
  · rintro ⟨c, hsum, m₀, hm₀⟩
    refine ⟨c, ?_, ?_⟩
    · intro h
      exact hm₀ (by rw [h]; rfl)
    · refine (jetRelationOn_iff_rows hconn hf hz₀ hnodes hr n d c).2 fun k => ?_
      have := congrFun hsum k
      simpa [Finset.sum_apply] using this

theorem not_linearIndependent_iff_forall_domainCoordinateMinor_det_eq_zero
    (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ) :
    ¬ LinearIndependent ℂ (domainJetSampleRow f z₀ r n d)
      ↔ ∀ φ : JetExponent n d → ℕ,
          (coordinateMinor (domainJetSampleRow f z₀ r n d) φ).det = 0 := by
  classical
  constructor
  · intro h φ
    by_contra hdet
    exact h (linearIndependent_of_coordinateMinor_det_ne_zero _ φ hdet)
  · intro h hind
    obtain ⟨φ, hφ⟩ := exists_coordinateMinor_det_ne_zero _ hind
    exact hφ (h φ)

/-- **The determinant certificate for an algebraic differential equation on a domain.**  A function
analytic on an open preconnected `Ω` satisfies an algebraic differential equation there exactly
when, at some jet order and exponent bound, every sample minor at nodes accumulating inside `Ω` is
singular. -/
theorem differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero {f : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ : ℂ} {r : ℝ} (hconn : IsPreconnected Ω) (hf : AnalyticOnNhd ℂ f Ω) (hz₀ : z₀ ∈ Ω)
    (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (hr : 0 < r) :
    DifferentiallyAlgebraicOn f Ω ↔
      ∃ n d : ℕ, ∀ φ : JetExponent n d → ℕ,
        (coordinateMinor (domainJetSampleRow f z₀ r n d) φ).det = 0 := by
  rw [differentiallyAlgebraicOn_iff_exists_jetRelationOn]
  constructor
  · rintro ⟨n, d, c, hc0, hrel⟩
    exact ⟨n, d, (not_linearIndependent_iff_forall_domainCoordinateMinor_det_eq_zero f z₀ r n d).1
      ((exists_jetRelationOn_iff_not_linearIndependent hconn hf hz₀ hnodes hr n d).1
        ⟨c, hc0, hrel⟩)⟩
  · rintro ⟨n, d, h⟩
    obtain ⟨c, hc0, hrel⟩ :=
      (exists_jetRelationOn_iff_not_linearIndependent hconn hf hz₀ hnodes hr n d).2
        ((not_linearIndependent_iff_forall_domainCoordinateMinor_det_eq_zero f z₀ r n d).2 h)
    exact ⟨n, d, c, hc0, hrel⟩

end

end GaloisForLFunctions.HTGeometry
