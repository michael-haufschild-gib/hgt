import GaloisForLFunctions.RHTower.CountableSpectralOrbitCoverReturnLaw
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewValue

/-!
# Relation-metric entropy law for countable quantum recurrence

For every normalized countable pure-point spectral packet, integer relations among
the energies determine the exact compact orbit closure. The state weights then map
that relation hull continuously into Hilbert space. Every finite metric cover of this
weighted image gives an actual positive survival-return deadline, and compactness
guarantees such a cover at every positive resolution.

This theorem separates the two independent inputs to recurrence:

* the relation lattice determines which phase directions exist;
* the spectral weights determine which of those directions are distinguishable.

The resulting metric entropy of the relation hull, rather than ambient Hilbert-space
dimension, controls the recurrence clock.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower

/-- A torus phase point mapped to the corresponding weighted quantum state. -/
def countableSpectralPhaseState
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (z : ℕ → UnitAddCircle) :
    CountableSpectralPhaseSpace :=
  countableSpectralKetAt p hp hsum z 1

theorem countableSpectralPhaseState_apply
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (z : ℕ → UnitAddCircle) (k : ℕ) :
    countableSpectralPhaseState p hp hsum z k =
      (Real.sqrt (p k) : ℂ) * fourier 1 (z k) := by
  rw [countableSpectralPhaseState, countableSpectralKetAt_apply,
    show countableSpectralHamiltonianEvolutionPhase z (1 : ℝ) k =
      fourier 1 (z k) by
        simpa using
          countableSpectralHamiltonianEvolutionPhase_nat z 1 k]

/--
Exact pullback of Hilbert distance to the weighted phase-defect metric.
-/
theorem norm_countableSpectralPhaseState_sub_sq_eq
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (z w : ℕ → UnitAddCircle) :
    ‖countableSpectralPhaseState p hp hsum z -
        countableSpectralPhaseState p hp hsum w‖ ^ (2 : ℕ) =
      2 * GaloisForLFunctions.HTGeometry.screwValue p (z - w) := by
  rw [HilbertSchmidt.lp_norm_sq_eq,
    GaloisForLFunctions.HTGeometry.screwValue, ← tsum_mul_left]
  change
    (∑' k : ℕ,
      ‖countableSpectralPhaseState p hp hsum z k -
        countableSpectralPhaseState p hp hsum w k‖ ^ (2 : ℕ)) =
      ∑' k : ℕ, 2 * (p k *
        (1 - (GaloisForLFunctions.HTGeometry.screwCoord
          ((z - w) k)).re))
  apply tsum_congr
  intro k
  rw [Pi.sub_apply, countableSpectralPhaseState_apply,
    countableSpectralPhaseState_apply, Complex.sq_norm,
    Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_mul]
  have hnormz : Complex.normSq (fourier 1 (z k)) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp
  have hnormw : Complex.normSq (fourier 1 (w k)) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp
  have hsqrt : Complex.normSq (Real.sqrt (p k) : ℂ) = p k := by
    rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (hp k)]
  rw [hnormz, hnormw, hsqrt]
  simp only [mul_one]
  have hphase :
      (fourier 1 (z k) * starRingEnd ℂ (fourier 1 (w k))).re =
        (GaloisForLFunctions.HTGeometry.screwCoord (z k - w k)).re := by
    rw [GaloisForLFunctions.HTGeometry.screwCoord, fourier_one,
      fourier_one, fourier_one, sub_eq_add_neg,
      AddCircle.toCircle_add, AddCircle.toCircle_neg,
      Circle.coe_mul, Circle.coe_inv_eq_conj]
  have hcross :
      (↑√(p k) * fourier 1 (z k) *
          starRingEnd ℂ (↑√(p k) * fourier 1 (w k))).re =
        p k *
          (fourier 1 (z k) *
            starRingEnd ℂ (fourier 1 (w k))).re := by
    have hcomplex :
        (↑√(p k) * fourier 1 (z k)) *
            starRingEnd ℂ (↑√(p k) * fourier 1 (w k)) =
          (p k : ℂ) *
            (fourier 1 (z k) *
              starRingEnd ℂ (fourier 1 (w k))) := by
      rw [map_mul, Complex.conj_ofReal]
      calc
        (↑√(p k) : ℂ) * fourier 1 (z k) *
            ((↑√(p k) : ℂ) *
              starRingEnd ℂ (fourier 1 (w k))) =
          ((√(p k) * √(p k) : ℝ) : ℂ) *
            (fourier 1 (z k) *
              starRingEnd ℂ (fourier 1 (w k))) := by
                push_cast
                ring
        _ = _ := by rw [Real.mul_self_sqrt (hp k)]
    rw [hcomplex, Complex.mul_re]
    simp
  rw [hcross, hphase]
  ring

/-- The weighted phase-state map is continuous even for infinitely many coordinates. -/
theorem countableSpectralPhaseState_continuous
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) :
    Continuous (countableSpectralPhaseState p hp hsum) := by
  rw [continuous_iff_continuous_dist]
  have hvalue :
      Continuous (fun zw : (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle) =>
        GaloisForLFunctions.HTGeometry.screwValue p (zw.1 - zw.2)) :=
    (GaloisForLFunctions.HTGeometry.screwValue_continuous hp hsum).comp
      (continuous_fst.sub continuous_snd)
  have hsqrt :
      Continuous (fun zw : (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle) =>
        Real.sqrt (2 *
          GaloisForLFunctions.HTGeometry.screwValue p (zw.1 - zw.2))) :=
    (continuous_const.mul hvalue).sqrt
  convert hsqrt using 1
  funext zw
  rw [dist_eq_norm]
  change ‖countableSpectralPhaseState p hp hsum zw.1 -
      countableSpectralPhaseState p hp hsum zw.2‖ =
        Real.sqrt (2 *
          GaloisForLFunctions.HTGeometry.screwValue p
            (zw.1 - zw.2))
  have hsquare :=
    norm_countableSpectralPhaseState_sub_sq_eq p hp hsum zw.1 zw.2
  have hvalue :=
    GaloisForLFunctions.HTGeometry.screwValue_nonneg hp (zw.1 - zw.2)
  have hsqrtSq :
      Real.sqrt (2 *
        GaloisForLFunctions.HTGeometry.screwValue p (zw.1 - zw.2)) ^ (2 : ℕ) =
          2 * GaloisForLFunctions.HTGeometry.screwValue p
            (zw.1 - zw.2) :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hvalue)
  nlinarith [norm_nonneg
      (countableSpectralPhaseState p hp hsum zw.1 -
        countableSpectralPhaseState p hp hsum zw.2),
    Real.sqrt_nonneg (2 *
      GaloisForLFunctions.HTGeometry.screwValue p (zw.1 - zw.2))]

/-- Radius-`r` Hilbert cover of the exact relation-determined orbit hull. -/
def CountableSpectralRelationHullCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ)
    (C : Finset CountableSpectralPhaseSpace) (r : ℝ) : Prop :=
  ∀ z ∈ GaloisForLFunctions.HTGeometry.screwHull omega,
    ∃ c ∈ C,
      ‖countableSpectralPhaseState p hp hsum z - c‖ ≤ r

/--
Every countable relation hull has a finite weighted Hilbert cover at every positive
resolution.
-/
theorem exists_countableSpectralRelationHullCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset CountableSpectralPhaseSpace,
      CountableSpectralRelationHullCover p hp hsum omega C r := by
  classical
  let f := countableSpectralPhaseState p hp hsum
  have hcompact :
      IsCompact
        (f '' GaloisForLFunctions.HTGeometry.screwHull omega) :=
    (GaloisForLFunctions.HTGeometry.isCompact_screwHull omega).image
      (countableSpectralPhaseState_continuous p hp hsum)
  obtain ⟨t, _htSub, htFinite, htCover⟩ :=
    hcompact.finite_cover_balls hr
  refine ⟨htFinite.toFinset, ?_⟩
  intro z hz
  have hfmem :
      f z ∈ f '' GaloisForLFunctions.HTGeometry.screwHull omega :=
    ⟨z, hz, rfl⟩
  have hcovered := htCover hfmem
  simp only [Set.mem_iUnion] at hcovered
  obtain ⟨c, hct, hcball⟩ := hcovered
  refine ⟨c, ?_, ?_⟩
  · exact (Set.Finite.mem_toFinset htFinite).mpr hct
  · rw [Metric.mem_ball, dist_eq_norm] at hcball
    exact hcball.le

/-- Cardinalities of all finite radius-`r` covers of the weighted relation hull. -/
def countableSpectralRelationHullCoverCardinals
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ) (r : ℝ) : Set ℕ :=
  {N | ∃ C : Finset CountableSpectralPhaseSpace,
    CountableSpectralRelationHullCover p hp hsum omega C r ∧
      C.card = N}

/--
Minimal number of radius-`r` Hilbert balls needed to cover the weighted relation
hull. Its logarithm is the finite-resolution relation-metric entropy.
-/
noncomputable def countableSpectralRelationHullCoveringNumber
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ) (r : ℝ) : ℕ :=
  sInf (countableSpectralRelationHullCoverCardinals
    p hp hsum omega r)

/-- The minimal covering number is attained at every positive radius. -/
theorem exists_optimal_countableSpectralRelationHullCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset CountableSpectralPhaseSpace,
      CountableSpectralRelationHullCover p hp hsum omega C r ∧
      C.card =
        countableSpectralRelationHullCoveringNumber
          p hp hsum omega r := by
  have hnonempty :
      (countableSpectralRelationHullCoverCardinals
        p hp hsum omega r).Nonempty := by
    obtain ⟨C, hC⟩ :=
      exists_countableSpectralRelationHullCover p hp hsum omega hr
    exact ⟨C.card, C, hC, rfl⟩
  exact Nat.sInf_mem hnonempty

theorem screwPhase_nat_eq_nsmul
    (omega : ℕ → ℝ) (n : ℕ) :
    GaloisForLFunctions.HTGeometry.screwPhase omega (n : ℝ) =
      n • GaloisForLFunctions.HTGeometry.screwPhase omega 1 := by
  induction n with
  | zero =>
      simp [GaloisForLFunctions.HTGeometry.screwPhase_zero]
  | succ n ih =>
      calc
        GaloisForLFunctions.HTGeometry.screwPhase omega
            (Nat.succ n : ℝ) =
          GaloisForLFunctions.HTGeometry.screwPhase omega
            ((n : ℝ) + 1) := by norm_num
        _ =
          GaloisForLFunctions.HTGeometry.screwPhase omega (n : ℝ) +
            GaloisForLFunctions.HTGeometry.screwPhase omega 1 :=
              GaloisForLFunctions.HTGeometry.screwPhase_add omega _ _
        _ =
          n • GaloisForLFunctions.HTGeometry.screwPhase omega 1 +
            GaloisForLFunctions.HTGeometry.screwPhase omega 1 := by rw [ih]
        _ = Nat.succ n •
            GaloisForLFunctions.HTGeometry.screwPhase omega 1 := by
              rw [succ_nsmul]

theorem countableSpectralKetAt_screwPhase_one_nat
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ) (n : ℕ) :
    countableSpectralKetAt p hp hsum
        (GaloisForLFunctions.HTGeometry.screwPhase omega 1) n =
      countableSpectralPhaseState p hp hsum
        (GaloisForLFunctions.HTGeometry.screwPhase omega n) := by
  apply lp.ext
  funext k
  rw [countableSpectralKetAt_apply,
    countableSpectralHamiltonianEvolutionPhase_nat,
    countableSpectralPhaseState_apply,
    screwPhase_nat_eq_nsmul]
  simp

/--
Finite relation-hull metric entropy bounds the actual first survival-return clock.
-/
theorem countableSpectralFirstCoherenceTime_le_card_of_relationHullCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (omega : ℕ → ℝ)
    (C : Finset CountableSpectralPhaseSpace) {r : ℝ}
    (hr : 0 ≤ r)
    (hcover :
      CountableSpectralRelationHullCover p hp hsum omega C r) :
    countableTorusWeightedFirstCoherenceTime p
        (GaloisForLFunctions.HTGeometry.screwPhase omega 1)
        (2 * r ^ (2 : ℕ)) ≤ C.card := by
  apply countableSpectralFirstCoherenceTime_le_card_of_orbitCover
    p hp hsum htotal
      (GaloisForLFunctions.HTGeometry.screwPhase omega 1) C hr
  intro n
  obtain ⟨c, hcC, hdist⟩ :=
    hcover
      (GaloisForLFunctions.HTGeometry.screwPhase omega n)
      (GaloisForLFunctions.HTGeometry.screwPhase_mem_screwHull omega n)
  refine ⟨c, hcC, ?_⟩
  rwa [countableSpectralKetAt_screwPhase_one_nat]

/--
Unconditional countable relation-metric return law: at every positive resolution,
some finite cover exists and its cardinality bounds the actual first return.
-/
theorem exists_countableSpectralRelationHullFirstReturnBound
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset CountableSpectralPhaseSpace,
      CountableSpectralRelationHullCover p hp hsum omega C r ∧
      countableTorusWeightedFirstCoherenceTime p
          (GaloisForLFunctions.HTGeometry.screwPhase omega 1)
          (2 * r ^ (2 : ℕ)) ≤ C.card := by
  obtain ⟨C, hC⟩ :=
    exists_countableSpectralRelationHullCover p hp hsum omega hr
  exact ⟨C, hC,
    countableSpectralFirstCoherenceTime_le_card_of_relationHullCover
      p hp hsum htotal omega C hr.le hC⟩

/--
Universal relation-metric entropy law: actual first survival recurrence is no later
than the minimal covering number of the exact weighted relation hull.
-/
theorem countableSpectralFirstCoherenceTime_le_relationHullCoveringNumber
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    countableTorusWeightedFirstCoherenceTime p
        (GaloisForLFunctions.HTGeometry.screwPhase omega 1)
        (2 * r ^ (2 : ℕ)) ≤
      countableSpectralRelationHullCoveringNumber
        p hp hsum omega r := by
  obtain ⟨C, hcover, hcard⟩ :=
    exists_optimal_countableSpectralRelationHullCover
      p hp hsum omega hr
  rw [← hcard]
  exact
    countableSpectralFirstCoherenceTime_le_card_of_relationHullCover
      p hp hsum htotal omega C hr.le hcover

/--
Relation-lattice form. The hull is exactly the annihilator of every finite integer
energy relation, so no unproved rational-independence premise is present.
-/
theorem exists_countableSpectralRelationLatticeFirstReturnBound
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset CountableSpectralPhaseSpace,
      (∀ z ∈
          GaloisForLFunctions.HTGeometry.screwAnnihilator omega,
        ∃ c ∈ C,
          ‖countableSpectralPhaseState p hp hsum z - c‖ ≤ r) ∧
      countableTorusWeightedFirstCoherenceTime p
          (GaloisForLFunctions.HTGeometry.screwPhase omega 1)
          (2 * r ^ (2 : ℕ)) ≤ C.card := by
  obtain ⟨C, hcover, htime⟩ :=
    exists_countableSpectralRelationHullFirstReturnBound
      p hp hsum htotal omega hr
  refine ⟨C, ?_, htime⟩
  intro z hz
  apply hcover z
  rw [GaloisForLFunctions.HTGeometry.screwHull_eq_screwAnnihilator]
  exact hz

end RHTower
