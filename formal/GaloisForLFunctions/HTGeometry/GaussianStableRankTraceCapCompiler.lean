import GaloisForLFunctions.HTGeometry.GaussianAffineStableRankLowerTail

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Trace/cap compiler for stable rank.  A positive total-mass floor and a
uniform upper bound on every covariance eigenvalue force stable rank at least
`mass / cap`. -/
theorem weightedStableRatio_ge_mass_div_cap
    {I : Type*} [Fintype I] (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {mass cap : ℝ} (hmasspos : 0 < mass) (hcappos : 0 < cap)
    (hmass : mass ≤ ∑ i, weight i)
    (hcap : ∀ i, weight i ≤ cap) :
    mass / cap ≤
      (∑ i, weight i) ^ 2 / ∑ i, weight i ^ 2 := by
  let S : ℝ := ∑ i, weight i
  let Q : ℝ := ∑ i, weight i ^ 2
  have hSpos : 0 < S := hmasspos.trans_le hmass
  have hSnonneg : 0 ≤ S := hSpos.le
  have hQnonneg : 0 ≤ Q := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (weight i)
  have hsq : S ^ 2 ≤ (Fintype.card I : ℝ) * Q := by
    simpa [S, Q] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := weight))
  have hQpos : 0 < Q := by
    by_contra hnot
    have hQzero : Q = 0 := le_antisymm (not_lt.mp hnot) hQnonneg
    rw [hQzero] at hsq
    have hSsqpos : 0 < S ^ 2 := sq_pos_of_pos hSpos
    nlinarith
  have hQcap : Q ≤ cap * S := by
    dsimp [Q, S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := hweight i
    have hic := hcap i
    nlinarith
  calc
    mass / cap ≤ S / cap :=
      div_le_div_of_nonneg_right hmass hcappos.le
    _ ≤ S ^ 2 / Q := by
      rw [div_le_div_iff₀ hcappos hQpos]
      calc
        S * Q ≤ S * (cap * S) :=
          mul_le_mul_of_nonneg_left hQcap hSnonneg
        _ = S ^ 2 * cap := by ring

/-- Complete affine tube union from a trace floor and a per-mode cap.  This is
the direct interface for Casimir mass plus a local commutator norm bound. -/
theorem stdGaussian_measure_iUnion_linearMap_affine_norm_sq_le_of_trace_cap
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (target : C → F)
    (hn : Module.finrank ℝ E = n) (traceFloor cap : ℝ)
    (htraceFloor : 0 < traceFloor) (hcapPos : 0 < cap)
    (htrace : ∀ c,
      traceFloor ≤ ∑ i : Fin n, (A c).singularValues i ^ 2)
    (hcap : ∀ c (i : Fin n), (A c).singularValues i ^ 2 ≤ cap) :
    (stdGaussian E).real
        (⋃ c, {v | ‖A c v - target c‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2}) ≤
      (Fintype.card C : ℝ) *
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) *
            (traceFloor / cap)) := by
  apply stdGaussian_measure_iUnion_linearMap_affine_norm_sq_le_halfActivation
    A target hn (traceFloor / cap)
  intro c
  have hpow : ∀ i : Fin n,
      ((A c).singularValues i ^ 2) ^ 2 =
        (A c).singularValues i ^ 4 := by
    intro i
    ring
  simpa only [hpow] using weightedStableRatio_ge_mass_div_cap
    (fun i : Fin n => (A c).singularValues i ^ 2)
    (fun i => sq_nonneg _)
    htraceFloor hcapPos (htrace c) (hcap c)

end

end GaloisForLFunctions.HTGeometry
