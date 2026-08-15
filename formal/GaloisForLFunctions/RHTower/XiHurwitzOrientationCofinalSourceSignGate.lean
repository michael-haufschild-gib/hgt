import GaloisForLFunctions.RHTower.XiHurwitzOrientationUniversalityLaw

/-!
# Cofinal finite-source sign gate for Xi--Hurwitz orientation

The existing separated-source reconstruction criterion asks one finite prime--Gamma packet
sequence to be eventually nonnegative.  This is stronger than necessary.  Source energy is the
continuous Xi--Weil quadratic of packet evaluation, so every separated packet sequence converging
to the orientation vector automatically has energy limit `-xiHurwitzOrientationEnergy`.

Consequently false RH traps every such reconstruction a definite distance inside the negative
source chamber.  It is enough to construct nonnegative packets at arbitrarily late indices; no
nonnegative tail or quantitative convergence rate is required.  This replaces Route Q's eventual
sign producer by the strictly weaker cofinal sign-recurrence gate.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- One separated finite-source reconstruction has nonnegative energy at arbitrarily late
indices. -/
def XiHurwitzSeparatedSourceSequenceCofinalNonnegative : Prop :=
  ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
    Tendsto (fun n => (P n).evaluation) atTop
      (nhds xiHurwitzOrientationVector) ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 ≤ (P n).sourceEnergy

/-- Under false RH, every separated reconstruction is eventually trapped a definite distance
inside the negative source chamber. -/
theorem eventually_separatedSourceEnergy_lt_neg_half_orientationEnergy_of_not_rh
    (hnot : ¬RiemannHypothesis)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (nhds xiHurwitzOrientationVector)) :
    ∀ᶠ n in atTop,
      (P n).sourceEnergy < -xiHurwitzOrientationEnergy / 2 := by
  have henergy_ne : xiHurwitzOrientationEnergy ≠ 0 := by
    intro hzero
    exact hnot
      (riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.2 hzero)
  have henergy_pos : 0 < xiHurwitzOrientationEnergy :=
    lt_of_le_of_ne xiHurwitzOrientationEnergy_nonneg (Ne.symm henergy_ne)
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hP
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector] at hQ
  have hsource : Tendsto (fun n => (P n).sourceEnergy) atTop
      (nhds (-xiHurwitzOrientationEnergy)) := by
    apply hQ.congr'
    exact Eventually.of_forall fun n =>
      (P n).sourceEnergy_eq_hilbertQuadratic.symm
  exact hsource.eventually
    (Iio_mem_nhds (by linarith :
      -xiHurwitzOrientationEnergy < -xiHurwitzOrientationEnergy / 2))

/-- **Cofinal finite-source sign gate.**  It is enough that one separated prime--Gamma packet
reconstruction return to the nonnegative source chamber arbitrarily far out; tail
nonnegativity is unnecessary. -/
theorem xiHurwitzSeparatedSourceSequenceCofinalNonnegative_iff_riemannHypothesis :
    XiHurwitzSeparatedSourceSequenceCofinalNonnegative ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨P, hP, hcofinal⟩
    by_contra hnot
    have hneg :=
      eventually_separatedSourceEnergy_lt_neg_half_orientationEnergy_of_not_rh
        hnot P hP
    obtain ⟨N, hN⟩ := eventually_atTop.1 hneg
    obtain ⟨n, hnN, hnnonneg⟩ := hcofinal N
    have hnneg := hN n hnN
    have henergy_nonneg := xiHurwitzOrientationEnergy_nonneg
    linarith
  · intro hRH
    obtain ⟨P, hP, _hE, hiff⟩ :=
      exists_separatedContinuedSource_sequence_eventually_nonnegative_iff_riemannHypothesis
    have hnonneg : ∀ᶠ n in atTop, 0 ≤ (P n).sourceEnergy := hiff.1 hRH
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hnonneg
    refine ⟨P, hP, fun N => ?_⟩
    exact ⟨max N N0, le_max_left _ _, hN0 _ (le_max_right _ _)⟩

end

end RHTower
