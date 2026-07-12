import GaloisForLFunctions.HTGeometry.BoundedGaugeContinuity
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Nowhere-dense differential rank defects in bounded prime-log gauge space

A fixed finite actual differential coefficient pattern is not merely escapable.  Its defect set is
closed and has empty interior in the complete uniform space of bounded gauges.  The proof joins the
coefficient-uniform determinant escape to the continuity of actual differential jets.  Thus every
certified full-rank finite pattern defines an open dense gauge condition.
-/

namespace GaloisForLFunctions.HTGeometry

open BoundedContinuousFunction
open scoped BoundedContinuousFunction

/-- **Bounded-gauge nowhere-density law.** If one abstract row-jet packet certifies full rank for a
finite coefficient pattern at fixed distinct upper nodes, then the bounded gauges where the actual
prime-log differential packet loses that rank form a nowhere-dense closed set. -/
theorem actualCoefficientPatternRankDefect_isNowhereDense_of_isUnit
    {row ι : Type*} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (nodes : row × ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ)
    (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ))
    (target : row × (Σ i, Fin (orders i)) → ℂ)
    (hfull : IsUnit (Matrix.of fun a b ↦
      base a ^ degree b * (jetExponent b).prod (fun i e ↦ target (a, i) ^ e) :
      Matrix row row ℂ)) :
    IsNowhereDense
      (actualCoefficientPatternRankDefect nodes orders base degree jetExponent) := by
  let D := actualCoefficientPatternRankDefect nodes orders base degree jetExponent
  have hclosed : IsClosed D :=
    actualCoefficientPatternRankDefect_isClosed nodes hupper orders base degree jetExponent
  rw [hclosed.isNowhereDense_iff]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
  let combinedOrders : row × ι → ℕ := fun x ↦ orders x.2
  let baseJet : row × (Σ i, Fin (orders i)) → ℂ :=
    reshapeCombinedJets row ι orders
      (primeLogCauchyJetPacket (fun p ↦ u p) nodes combinedOrders)
  obtain ⟨a, ε, C', hε, hεtime, hpos, hgauge, hbounded, hmass, hfinite, hnorm⟩ :=
    coefficientPattern_fullRank_escape_in_gaugeBall
      nodes hnodes hupper orders base degree jetExponent target hfull
      (fun p ↦ u p) ‖u‖
      (fun p ↦ by simpa only [Real.norm_eq_abs] using norm_coe_le_norm u p)
      baseJet one_pos (half_pos hη)
  let raw : Nat.Primes → ℝ := primeLogPerturbedGauge (fun p ↦ u p) a ε
  let u' : PrimeLogBoundedGauge := primeLogBoundedGaugeOfBound raw C' hbounded
  have hdist : dist u' u ≤ η / 2 := by
    rw [dist_le_iff_of_nonempty]
    intro p
    rw [Real.dist_eq]
    exact (hgauge p).le
  have hu'ball : u' ∈ Metric.ball u η := by
    rw [Metric.mem_ball]
    exact hdist.trans_lt (half_lt_self hη)
  have hu'D : u' ∈ D := interior_subset (hball hu'ball)
  have hpacket := primeLogCauchyJetPacket_perturbedGauge
    (fun p ↦ u p) ‖u‖
    (fun p ↦ (le_abs_self (u p)).trans (norm_coe_le_norm u p))
    nodes hupper combinedOrders a ε hpos
  let L := (reshapeCombinedJets row ι orders).comp
    (cauchyJetRealLinearCombination nodes combinedOrders primeLogSupport)
  have hcoord : baseJet + ε • L a =
      reshapeCombinedJets row ι orders
        (primeLogCauchyJetPacket raw nodes combinedOrders) := by
    rw [hpacket]
    rfl
  rw [hcoord] at hnorm
  let normalized : row → (Σ i, Fin (orders i)) → ℂ := fun r s ↦
    primeLogCauchyJetPacket raw nodes combinedOrders
      (rowJetIndexEquiv row ι orders (r, s))
  let actual : row → (Σ i, Fin (orders i)) → ℂ := fun r s ↦
    primeLogDifferentialJetPacket raw nodes combinedOrders
      (rowJetIndexEquiv row ι orders (r, s))
  have hraw : ∀ p, raw p ≤ C' := fun p ↦
    (le_abs_self _).trans (hbounded p)
  have hactual : ∀ r s,
      actual r s = (s.2.1.factorial : ℂ) * normalized r s := by
    intro r s
    have h := iteratedDeriv_primeLogHerglotz_eq_factorial_mul_packet
      raw C' hraw nodes hupper combinedOrders
      (rowJetIndexEquiv row ι orders (r, s))
    simpa [actual, normalized, primeLogDifferentialJetPacket,
      rowJetIndexEquiv, combinedOrders] using h
  have hnorm' : IsUnit (Matrix.of fun r b ↦
      base r ^ degree b * (jetExponent b).prod (fun s e ↦ normalized r s ^ e) :
      Matrix row row ℂ) := by
    simpa [normalized, reshapeCombinedJets] using hnorm
  have hactualFull := coefficientPattern_isUnit_actual_of_normalized
    base degree jetExponent normalized actual hactual hnorm'
  have hu'notD : u' ∉ D := by
    intro hdef
    exact hdef hactualFull
  exact hu'notD hu'D

/-- The complement of every certified finite actual differential rank defect is open and dense in
the complete bounded-gauge space. -/
theorem actualCoefficientPatternFullRank_isOpen_dense_of_isUnit
    {row ι : Type*} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (nodes : row × ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ)
    (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ))
    (target : row × (Σ i, Fin (orders i)) → ℂ)
    (hfull : IsUnit (Matrix.of fun a b ↦
      base a ^ degree b * (jetExponent b).prod (fun i e ↦ target (a, i) ^ e) :
      Matrix row row ℂ)) :
    IsOpen (actualCoefficientPatternRankDefect nodes orders base degree jetExponent)ᶜ ∧
      Dense (actualCoefficientPatternRankDefect nodes orders base degree jetExponent)ᶜ := by
  rw [← isClosed_isNowhereDense_iff_compl]
  exact ⟨actualCoefficientPatternRankDefect_isClosed
      nodes hupper orders base degree jetExponent,
    actualCoefficientPatternRankDefect_isNowhereDense_of_isUnit
      nodes hnodes hupper orders base degree jetExponent target hfull⟩

/-- Every finite injective translate packet, finite distinct actual differential-monomial support,
and polynomial coefficient-degree bound admits a noncolliding upper evaluation packet whose gauge
rank-defect set is closed and nowhere dense. -/
theorem exists_primeLog_actualCoefficientPattern_closed_nowhereDense
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (q : ℕ) (shift : ι → ℂ) (hshift : Function.Injective shift)
    (orders : ι → ℕ)
    (jetExponent : κ → ((Σ i, Fin (orders i)) →₀ ℕ))
    (hjet : Function.Injective jetExponent) :
    let pattern := κ × Fin (q + 1)
    let n := Fintype.card pattern
    ∃ base : Fin n → ℂ,
      Function.Injective (fun x : Fin n × ι ↦ base x.1 + shift x.2) ∧
      (∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im) ∧
      IsClosed (actualCoefficientPatternRankDefect
        (fun x : Fin n × ι ↦ base x.1 + shift x.2) orders base
        (fun b ↦ ((Fintype.equivFin pattern).symm b).2.val)
        (fun b ↦ jetExponent ((Fintype.equivFin pattern).symm b).1)) ∧
      IsNowhereDense (actualCoefficientPatternRankDefect
        (fun x : Fin n × ι ↦ base x.1 + shift x.2) orders base
        (fun b ↦ ((Fintype.equivFin pattern).symm b).2.val)
        (fun b ↦ jetExponent ((Fintype.equivFin pattern).symm b).1)) := by
  dsimp only
  let pattern := κ × Fin (q + 1)
  let n := Fintype.card pattern
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound shift
  obtain ⟨base, target, hbase, hnodes, hfull⟩ :=
    exists_noncolliding_fullRank_polynomialCoefficientMonomial_packet
      q jetExponent hjet shift hshift H
  let nodes : Fin n × ι → ℂ := fun x ↦ base x.1 + shift x.2
  let degree : Fin n → ℕ := fun b ↦
    ((Fintype.equivFin pattern).symm b).2.val
  let exponent : Fin n → ((Σ i, Fin (orders i)) →₀ ℕ) := fun b ↦
    jetExponent ((Fintype.equivFin pattern).symm b).1
  have hupper : ∀ x : Fin n × ι, 0 < (nodes x).im := by
    intro x
    simp only [nodes, Complex.add_im]
    linarith [hbase x.1, hH x.2]
  have hfull' : IsUnit (Matrix.of fun a b ↦
      base a ^ degree b * (exponent b).prod (fun i e ↦ target a i ^ e) :
      Matrix (Fin n) (Fin n) ℂ) := by
    simpa [degree, exponent] using hfull
  refine ⟨base, hnodes, ?_, ?_, ?_⟩
  · simpa [nodes] using hupper
  · exact actualCoefficientPatternRankDefect_isClosed
      nodes hupper orders base degree exponent
  · exact actualCoefficientPatternRankDefect_isNowhereDense_of_isUnit
      nodes hnodes hupper orders base degree exponent
        (fun x ↦ target x.1 x.2) hfull'

/-- **Countable simultaneous fullness law.** For any countable family of certified finite actual
differential coefficient patterns, the bounded gauges satisfying every full-rank condition form a
dense residual set.  The complex coefficient vectors do not have to be enumerated: each finite
determinant condition excludes all of them at once. -/
theorem countable_actualCoefficientFullRank_dense_residual
    (D : ℕ → Set PrimeLogBoundedGauge)
    (hclosed : ∀ n, IsClosed (D n))
    (hnowhere : ∀ n, IsNowhereDense (D n)) :
    Dense (⋂ n, (D n)ᶜ) ∧
      (⋂ n, (D n)ᶜ) ∈ residual PrimeLogBoundedGauge := by
  have hopen : ∀ n, IsOpen (D n)ᶜ := fun n ↦ (hclosed n).isOpen_compl
  have hdense : ∀ n, Dense (D n)ᶜ := fun n ↦
    interior_eq_empty_iff_dense_compl.mp
      ((hclosed n).isNowhereDense_iff.mp (hnowhere n))
  exact ⟨dense_iInter_of_isOpen_nat hopen hdense,
    countable_iInter_mem.mpr
      (fun n ↦ residual_of_dense_open (hopen n) (hdense n))⟩

end GaloisForLFunctions.HTGeometry
