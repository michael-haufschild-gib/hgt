import GaloisForLFunctions.RHTower.HelsonEulerExponent
import GaloisForLFunctions.RHTower.SteinhausPrimeRealMoment

/-!
# The Helson continuation stratum is null

The stratum of unimodular phases whose Helson zeta function continues meromorphically to the whole
plane has Haar measure zero.

The mechanism is a clash between two facts about the Euler exponent
`E_ω(s) = ∑_p χ_ω(p) p^{-s} + ∑_p logTail(χ_ω(p) p^{-s})` on the half line:

* continuation forces a *logarithmic envelope*: `Re E_ω(σ) = m log(σ - 1/2) + O(1)` near `1/2`;
* the prime layer is a random Dirichlet series with independent coefficients, whose real part
  exceeds `√(∑_{p<N} p^{-2σ}) / 2` in absolute value with probability at least `1/32` — and by the
  half-turn phase symmetry, with probability at least `1/64` on each side.

The second moment `∑_p p^{-2σ}` is unbounded as `σ` decreases to the half line, so no fixed
envelope can hold on a set of large measure.  What makes the argument work is that the envelope
condition — with its *unknown* integer `m` — is a tail event: it is unchanged by modifying finitely
many prime phases.  Splitting it into "bounded above" and "bounded below" removes `m` from the
statement (`m ≥ 0` gives the first, `m ≤ 0` the second), and each half is a tail event, hence has
measure zero or one.  Either way the anti-concentration bound on the corresponding side of the
prime layer contradicts it.

No classical input is used: not Bohr's theorem, not the three-series theorem, not Itô–Nisio, not
the almost-sure natural boundary.
-/

noncomputable section

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-! ### The cut sequence -/

/-- The sequence of real cuts approaching the half line. -/
def cutSeq (k : ℕ) : ℝ := 1 / 2 + 1 / ((k : ℝ) + 1)

theorem cutSeq_gt (k : ℕ) : 1 / 2 < cutSeq k := by
  have h : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  rw [cutSeq]
  linarith

theorem exists_cutSeq_lt {η : ℝ} (hη : 0 < η) : ∃ k : ℕ, cutSeq k < 1 / 2 + η := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  exact ⟨k, by rw [cutSeq]; linarith⟩

/-! ### The two envelope events -/

/-- The phases whose Euler exponent is bounded above along the cut sequence. -/
def negEvent : Set Omega :=
  primeHolomorphicEvent ∩ {ω | ∃ B : ℕ, ∀ k : ℕ, eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)}

/-- The phases whose Euler exponent is bounded below along the cut sequence. -/
def posEvent : Set Omega :=
  primeHolomorphicEvent ∩ {ω | ∃ B : ℕ, ∀ k : ℕ, -(B : ℝ) ≤ eulerExponentRe (cutSeq k) ω}

theorem measurableSet_negEvent : MeasurableSet negEvent := by
  refine measurableSet_primeHolomorphicEvent.inter ?_
  have heq : {ω : Omega | ∃ B : ℕ, ∀ k : ℕ, eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)}
      = ⋃ B : ℕ, ⋂ k : ℕ, {ω : Omega | eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iUnion fun B => MeasurableSet.iInter fun k =>
    measurableSet_le (measurable_eulerExponentRe (cutSeq_gt k)) measurable_const

theorem measurableSet_posEvent : MeasurableSet posEvent := by
  refine measurableSet_primeHolomorphicEvent.inter ?_
  have heq : {ω : Omega | ∃ B : ℕ, ∀ k : ℕ, -(B : ℝ) ≤ eulerExponentRe (cutSeq k) ω}
      = ⋃ B : ℕ, ⋂ k : ℕ, {ω : Omega | -(B : ℝ) ≤ eulerExponentRe (cutSeq k) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iUnion fun B => MeasurableSet.iInter fun k =>
    measurableSet_le measurable_const (measurable_eulerExponentRe (cutSeq_gt k))

theorem primeHolomorphicEvent_invariant {ω ω' : Omega} (hfin : {n : ℕ | ω n ≠ ω' n}.Finite) :
    ω ∈ primeHolomorphicEvent ↔ ω' ∈ primeHolomorphicEvent := by
  constructor <;> intro h <;>
    exact Set.mem_iInter.mpr fun j =>
      (coordSeriesConverges_invariant _ (by
        first
        | exact hfin
        | exact hfin.subset fun n hn => fun hc => hn hc.symm)).mp (Set.mem_iInter.mp h j)


theorem negEvent_invariant {ω ω' : Omega} (hfin : {n : ℕ | ω n ≠ ω' n}.Finite) :
    ω ∈ negEvent ↔ ω' ∈ negEvent := by
  have key : ∀ x y : Omega, {n : ℕ | x n ≠ y n}.Finite → x ∈ negEvent → y ∈ negEvent := by
    rintro x y hxy ⟨hx0, B, hB⟩
    have hy0 : y ∈ primeHolomorphicEvent := (primeHolomorphicEvent_invariant hxy).mp hx0
    obtain ⟨C, hC0, hC⟩ := exists_bound_eulerExponentRe_sub hxy hx0 hy0
    refine ⟨hy0, ⌈(B : ℝ) + C⌉₊, fun k => ?_⟩
    have h1 := abs_le.mp (hC (cutSeq k) (cutSeq_gt k))
    have h2 := hB k
    have h3 : eulerExponentRe (cutSeq k) y ≤ (B : ℝ) + C := by linarith [h1.1, h1.2]
    exact le_trans h3 (Nat.le_ceil _)
  have hsymm : {n : ℕ | ω' n ≠ ω n}.Finite := hfin.subset fun n hn => fun hc => hn hc.symm
  exact ⟨key ω ω' hfin, key ω' ω hsymm⟩

theorem posEvent_invariant {ω ω' : Omega} (hfin : {n : ℕ | ω n ≠ ω' n}.Finite) :
    ω ∈ posEvent ↔ ω' ∈ posEvent := by
  have key : ∀ x y : Omega, {n : ℕ | x n ≠ y n}.Finite → x ∈ posEvent → y ∈ posEvent := by
    rintro x y hxy ⟨hx0, B, hB⟩
    have hy0 : y ∈ primeHolomorphicEvent := (primeHolomorphicEvent_invariant hxy).mp hx0
    obtain ⟨C, hC0, hC⟩ := exists_bound_eulerExponentRe_sub hxy hx0 hy0
    refine ⟨hy0, ⌈(B : ℝ) + C⌉₊, fun k => ?_⟩
    have h1 := abs_le.mp (hC (cutSeq k) (cutSeq_gt k))
    have h2 := hB k
    have h3 : -((B : ℝ) + C) ≤ eulerExponentRe (cutSeq k) y := by linarith [h1.1, h1.2]
    refine le_trans ?_ h3
    have := Nat.le_ceil ((B : ℝ) + C)
    linarith
  have hsymm : {n : ℕ | ω' n ≠ ω n}.Finite := hfin.subset fun n hn => fun hc => hn hc.symm
  exact ⟨key ω ω' hfin, key ω' ω hsymm⟩

theorem measure_negEvent_eq_zero_or_one :
    steinhausMeasure negEvent = 0 ∨ steinhausMeasure negEvent = 1 :=
  measure_infinitePi_eq_zero_or_one_of_invariant
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => 0)
    measurableSet_negEvent (fun _ _ h => negEvent_invariant h)

theorem measure_posEvent_eq_zero_or_one :
    steinhausMeasure posEvent = 0 ∨ steinhausMeasure posEvent = 1 :=
  measure_infinitePi_eq_zero_or_one_of_invariant
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => 0)
    measurableSet_posEvent (fun _ _ h => posEvent_invariant h)

/-! ### The envelope covers the continuation stratum -/

theorem contEvent_inter_subset : contEvent ∩ primeHolomorphicEvent ⊆ negEvent ∪ posEvent := by
  rintro ω ⟨hcont, hω⟩
  obtain ⟨m, δ, B, hδ, hbound⟩ := exists_boundary_bound hcont hω
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → cutSeq k < 1 / 2 + δ := by
    obtain ⟨k₀, hk₀⟩ := exists_cutSeq_lt hδ
    refine ⟨k₀, fun k hk => ?_⟩
    have hmono : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
      have hkk : ((k₀ : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
        have : (k₀ : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
        linarith
      exact one_div_le_one_div_of_le (by positivity) hkk
    rw [cutSeq] at hk₀ ⊢
    linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k ∈ Finset.range k₀, |eulerExponentRe (cutSeq k) ω| ≤ M := by
    rcases (Finset.range k₀).eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    · refine ⟨(Finset.range k₀).sup' h (fun k => |eulerExponentRe (cutSeq k) ω|),
        fun k hk => ?_⟩
      exact Finset.le_sup' (f := fun k => |eulerExponentRe (cutSeq k) ω|) hk
  have hlog : ∀ k : ℕ, Real.log (cutSeq k - 1 / 2) ≤ 0 := by
    intro k
    have hval : cutSeq k - 1 / 2 = 1 / ((k : ℝ) + 1) := by rw [cutSeq]; ring
    rw [hval]
    refine Real.log_nonpos (by positivity) ?_
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hkey : ∀ k : ℕ, k₀ ≤ k →
      |eulerExponentRe (cutSeq k) ω - (m : ℝ) * Real.log (cutSeq k - 1 / 2)| ≤ B := by
    intro k hk
    rw [eulerExponentRe_eq hω (cutSeq_gt k)]
    exact hbound (cutSeq k) (cutSeq_gt k) (hk₀ k hk)
  rcases le_or_gt 0 (m : ℝ) with hm | hm
  · refine Or.inl ⟨hω, ⌈max B M⌉₊, fun k => ?_⟩
    have hle : eulerExponentRe (cutSeq k) ω ≤ max B M := by
      rcases lt_or_ge k k₀ with hk | hk
      · have := hM k (Finset.mem_range.mpr hk)
        have h1 := abs_le.mp this
        exact le_trans h1.2 (le_max_right _ _)
      · have h1 := abs_le.mp (hkey k hk)
        have h2 : (m : ℝ) * Real.log (cutSeq k - 1 / 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hm (hlog k)
        have : eulerExponentRe (cutSeq k) ω ≤ B := by linarith [h1.2]
        exact le_trans this (le_max_left _ _)
    exact le_trans hle (Nat.le_ceil _)
  · refine Or.inr ⟨hω, ⌈max B M⌉₊, fun k => ?_⟩
    have hge : -(max B M) ≤ eulerExponentRe (cutSeq k) ω := by
      rcases lt_or_ge k k₀ with hk | hk
      · have := hM k (Finset.mem_range.mpr hk)
        have h1 := abs_le.mp this
        have : -M ≤ eulerExponentRe (cutSeq k) ω := h1.1
        have hMle : -(max B M) ≤ -M := by
          have := le_max_right B M
          linarith
        linarith
      · have h1 := abs_le.mp (hkey k hk)
        have h2 : 0 ≤ (m : ℝ) * Real.log (cutSeq k - 1 / 2) :=
          mul_nonneg_of_nonpos_of_nonpos (le_of_lt hm) (hlog k)
        have h3 : -B ≤ eulerExponentRe (cutSeq k) ω := by linarith [h1.1]
        have hBle : -(max B M) ≤ -B := by
          have := le_max_left B M
          linarith
        linarith
    refine le_trans ?_ hge
    have := Nat.le_ceil (max B M)
    linarith


/-! ### The prime layer along the cut sequence -/

/-- The real part of the prime layer, recorded through a `limsup`. -/
def primeRe (σ : ℝ) (ω : Omega) : ℝ :=
  Filter.limsup (fun N => (steinhausPrimePoly σ N ω).re) Filter.atTop

theorem measurable_primeRe (σ : ℝ) : Measurable (primeRe σ) :=
  Measurable.limsup fun N => Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N)

theorem tendsto_steinhausPrimePoly {ω : Omega} (hω : ω ∈ primeHolomorphicEvent) {σ : ℝ}
    (hσ : 1 / 2 < σ) :
    Filter.Tendsto (fun N => steinhausPrimePoly σ N ω) Filter.atTop
      (nhds (dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ))) := by
  have hre : (((σ : ℝ) : ℂ)).re = σ := Complex.ofReal_re σ
  have hconv : DirichletConvergesAt (primePhaseCoeff ω) ((σ : ℝ) : ℂ) :=
    convergesAt_primePhaseCoeff_of_gt hω (by rw [hre]; exact hσ)
  have h := tendsto_dirichletSum hconv
  have hshift : Filter.Tendsto (fun N => steinhausPrimePoly σ (N + 1) ω) Filter.atTop
      (nhds (dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ))) := by
    refine h.congr fun N => ?_
    rw [dirichletPartialSum_primePhaseCoeff, coordPartialSum_primeTerm]
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun N => steinhausPrimePoly σ N ω) 1).mp hshift

theorem primeRe_eq {ω : Omega} (hω : ω ∈ primeHolomorphicEvent) {σ : ℝ} (hσ : 1 / 2 < σ) :
    primeRe σ ω = (dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)).re :=
  ((Complex.continuous_re.tendsto _).comp (tendsto_steinhausPrimePoly hω hσ)).limsup_eq

theorem eulerExponentRe_split {ω : Omega} (hω : ω ∈ primeHolomorphicEvent) {σ : ℝ}
    (hσ : 1 / 2 < σ) :
    eulerExponentRe σ ω
      = primeRe σ ω + (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re := by
  rw [eulerExponentRe_eq hω hσ, primeRe_eq hω hσ, helsonExponent, Complex.add_re]

/-! ### The contradiction -/

set_option maxHeartbeats 1000000 in
/-- The core clash: no fixed one-sided envelope can hold on a set of measure above `1 - 1/256`. -/
theorem contradiction_of_envelope {B : ℕ} {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1)
    (hK : 1 - 1 / 256 < (steinhausMeasure (primeHolomorphicEvent ∩
        {ω | ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)})).toReal) : False := by
  classical
  set K : Set Omega := primeHolomorphicEvent ∩
    {ω | ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} with hKdef
  -- the tail level
  set lam : ℝ := max 1 (Real.sqrt (1024 * tailMomentBound)) with hlamdef
  have hlam1 : (1 : ℝ) ≤ lam := le_max_left _ _
  have hlampos : 0 < lam := by linarith
  have hlamsq : 1024 * tailMomentBound ≤ lam ^ 2 := by
    have h1 : Real.sqrt (1024 * tailMomentBound) ≤ lam := le_max_right _ _
    have h2 : Real.sqrt (1024 * tailMomentBound) ^ 2 = 1024 * tailMomentBound :=
      Real.sq_sqrt (by linarith [tailMomentBound_nonneg])
    nlinarith [Real.sqrt_nonneg (1024 * tailMomentBound)]
  have htailbound : ∀ σ : ℝ, 1 / 2 < σ →
      (steinhausMeasure {ω : Omega |
        lam < |(helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re|}).toReal ≤ 1 / 256 := by
    intro σ hσ
    refine le_trans (measure_re_logTail_gt hσ hlampos) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [tailMomentBound_nonneg]
  -- the target level
  set M : ℝ := 4 * ((B : ℝ) + lam + 1) ^ 2 + 1 with hMdef
  obtain ⟨η, N₀, hη, hN₀⟩ := exists_primeSum_gt_nhds M
  obtain ⟨k, hk⟩ := exists_cutSeq_lt hη
  set σ : ℝ := cutSeq k with hσdef
  have hσ : 1 / 2 < σ := cutSeq_gt k
  have hA₀ : M < ∑ p ∈ primeSet N₀, ((p : ℝ) ^ (-(2 * σ))) := hN₀ σ hσ hk
  -- convergence in measure of the prime partial sums
  have hae : ∀ᵐ ω ∂steinhausMeasure,
      Filter.Tendsto (fun N => (steinhausPrimePoly σ N ω).re) Filter.atTop
        (nhds (primeRe σ ω)) := by
    have hone : steinhausMeasure primeHolomorphicEventᶜ = 0 :=
      (prob_compl_eq_zero_iff measurableSet_primeHolomorphicEvent).mpr
        measure_primeHolomorphicEvent
    have : ∀ᵐ ω ∂steinhausMeasure, ω ∈ primeHolomorphicEvent := by
      rw [ae_iff]
      exact hone
    filter_upwards [this] with ω hω
    rw [primeRe_eq hω hσ]
    exact (Complex.continuous_re.tendsto _).comp (tendsto_steinhausPrimePoly hω hσ)
  have hmeasSN : ∀ N : ℕ, Measurable fun ω : Omega => (steinhausPrimePoly σ N ω).re :=
    fun N => Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N)
  have htim : TendstoInMeasure steinhausMeasure
      (fun N ω => (steinhausPrimePoly σ N ω).re) Filter.atTop (primeRe σ) :=
    tendstoInMeasure_of_tendsto_ae (fun N => (hmeasSN N).aestronglyMeasurable) hae
  have hgap := htim 1 (by norm_num)
  have h0 : (0 : ENNReal) < ENNReal.ofReal (1 / 256) := by
    simp only [ENNReal.ofReal_pos]
    norm_num
  have hsmall : ∀ᶠ N in Filter.atTop,
      steinhausMeasure {ω : Omega | (1 : ENNReal) ≤
        edist ((steinhausPrimePoly σ N ω).re) (primeRe σ ω)}
        < ENNReal.ofReal (1 / 256) := hgap.eventually (gt_mem_nhds h0)
  obtain ⟨N, hNsmall, hNge⟩ := (hsmall.and (Filter.eventually_ge_atTop N₀)).exists
  -- the second moment at the chosen cut
  set A : ℝ := ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) with hAdef
  have hAge : ∑ p ∈ primeSet N₀, ((p : ℝ) ^ (-(2 * σ))) ≤ A := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.rpow_nonneg (by positivity) _
    refine Finset.filter_subset_filter _ ?_
    intro n hn
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hNge)

  have hAM : M < A := lt_of_lt_of_le hA₀ hAge
  have hApos : 0 < A := by
    have : (0:ℝ) ≤ 4 * ((B : ℝ) + lam + 1) ^ 2 := by positivity
    rw [hMdef] at hAM
    linarith
  -- the four events
  set V₂ : Set Omega := {ω | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2
    ∧ 0 < sgn * (steinhausPrimePoly σ N ω).re} with hV₂def
  set V₃ : Set Omega := {ω | |(helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re| ≤ lam}
    with hV₃def
  set V₄ : Set Omega := {ω | edist ((steinhausPrimePoly σ N ω).re) (primeRe σ ω) < 1} with hV₄def
  have hV₂measure : (1 : ℝ) / 64 ≤ (steinhausMeasure V₂).toReal := by
    obtain ⟨hpos', hneg'⟩ := measure_re_steinhausPrimePoly_pos σ N hApos
    rcases hsgn with rfl | rfl
    · have hset : V₂ = {ω : Omega | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2
          ∧ 0 < (steinhausPrimePoly σ N ω).re} := by
        ext ω
        simp only [hV₂def, Set.mem_setOf_eq, one_mul]
      rw [hset]
      exact hpos'
    · have hset : V₂ = {ω : Omega | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2
          ∧ (steinhausPrimePoly σ N ω).re < 0} := by
        ext ω
        simp only [hV₂def, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by linarith⟩
      rw [hset]
      exact hneg'
  have hV₃compl : (steinhausMeasure V₃ᶜ).toReal ≤ 1 / 256 := by
    have hset : V₃ᶜ = {ω : Omega |
        lam < |(helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re|} := by
      ext ω
      simp only [hV₃def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hset]
    exact htailbound σ hσ
  have hV₄compl : (steinhausMeasure V₄ᶜ).toReal ≤ 1 / 256 := by
    have hset : V₄ᶜ = {ω : Omega | (1 : ENNReal)
        ≤ edist ((steinhausPrimePoly σ N ω).re) (primeRe σ ω)} := by
      ext ω
      simp only [hV₄def, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [hset]
    have h1 := le_of_lt hNsmall
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by norm_num)] at h2
    exact h2
  have hKcompl : (steinhausMeasure Kᶜ).toReal ≤ 1 / 256 := by
    have hKmeas : MeasurableSet K := by
      refine measurableSet_primeHolomorphicEvent.inter ?_
      have heq : {ω : Omega | ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)}
          = ⋂ k : ℕ, {ω : Omega | sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [heq]
      exact MeasurableSet.iInter fun k =>
        measurableSet_le ((measurable_eulerExponentRe (cutSeq_gt k)).const_mul sgn)
          measurable_const
    rw [prob_compl_eq_one_sub hKmeas]
    have hfin : steinhausMeasure K ≠ ⊤ := measure_ne_top _ _
    have hle1 : steinhausMeasure K ≤ 1 := prob_le_one
    rw [ENNReal.toReal_sub_of_le hle1 (by simp), ENNReal.toReal_one]
    linarith
  -- the four events meet
  have hcover : V₂ ⊆ (((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) ∪ V₃ᶜ) ∪ V₄ᶜ := by
    intro ω hω
    by_cases h1 : ω ∈ K
    · by_cases h2 : ω ∈ V₃
      · by_cases h3 : ω ∈ V₄
        · exact Or.inl (Or.inl (Or.inl ⟨⟨⟨hω, h1⟩, h2⟩, h3⟩))
        · exact Or.inr h3
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl (Or.inr h1))
  have hchain : steinhausMeasure V₂ ≤ steinhausMeasure (V₂ ∩ K ∩ V₃ ∩ V₄)
      + steinhausMeasure Kᶜ + steinhausMeasure V₃ᶜ + steinhausMeasure V₄ᶜ := by
    have e1 : steinhausMeasure ((((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) ∪ V₃ᶜ) ∪ V₄ᶜ)
        ≤ steinhausMeasure (((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) ∪ V₃ᶜ) + steinhausMeasure V₄ᶜ :=
      measure_union_le _ _
    have e2 : steinhausMeasure (((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) ∪ V₃ᶜ)
        ≤ steinhausMeasure ((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) + steinhausMeasure V₃ᶜ :=
      measure_union_le _ _
    have e3 : steinhausMeasure ((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ)
        ≤ steinhausMeasure (V₂ ∩ K ∩ V₃ ∩ V₄) + steinhausMeasure Kᶜ :=
      measure_union_le _ _
    calc steinhausMeasure V₂
        ≤ steinhausMeasure ((((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) ∪ V₃ᶜ) ∪ V₄ᶜ) := measure_mono hcover
      _ ≤ steinhausMeasure (((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) ∪ V₃ᶜ) + steinhausMeasure V₄ᶜ := e1
      _ ≤ (steinhausMeasure ((V₂ ∩ K ∩ V₃ ∩ V₄) ∪ Kᶜ) + steinhausMeasure V₃ᶜ)
            + steinhausMeasure V₄ᶜ := add_le_add e2 (le_refl _)
      _ ≤ ((steinhausMeasure (V₂ ∩ K ∩ V₃ ∩ V₄) + steinhausMeasure Kᶜ)
            + steinhausMeasure V₃ᶜ) + steinhausMeasure V₄ᶜ :=
          add_le_add (add_le_add e3 (le_refl _)) (le_refl _)
  have htoReal : (steinhausMeasure V₂).toReal ≤ (steinhausMeasure (V₂ ∩ K ∩ V₃ ∩ V₄)).toReal
      + (steinhausMeasure Kᶜ).toReal + (steinhausMeasure V₃ᶜ).toReal
      + (steinhausMeasure V₄ᶜ).toReal := by
    have h := ENNReal.toReal_mono (by finiteness) hchain
    rwa [ENNReal.toReal_add (by finiteness) (measure_ne_top _ _),
      ENNReal.toReal_add (by finiteness) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h
  have hposmeasure : 0 < (steinhausMeasure (V₂ ∩ K ∩ V₃ ∩ V₄)).toReal := by
    linarith [hV₂measure, hKcompl, hV₃compl, hV₄compl, htoReal]
  have hne : (V₂ ∩ K ∩ V₃ ∩ V₄).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    rw [hc] at hposmeasure
    simp at hposmeasure
  obtain ⟨ω, ⟨⟨⟨hω2, hωK⟩, hω3⟩, hω4⟩⟩ := hne
  -- the contradiction
  have hsgnabs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hgapreal : |(steinhausPrimePoly σ N ω).re - primeRe σ ω| < 1 := by
    have h := hω4
    rw [hV₄def] at h
    simp only [Set.mem_setOf_eq, edist_dist] at h
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    rw [h1, ENNReal.ofReal_lt_ofReal_iff (by norm_num)] at h
    rwa [Real.dist_eq] at h
  have hKb := hωK.2 k
  have hsplit := eulerExponentRe_split hωK.1 hσ
  have hHbound : |(helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re| ≤ lam := hω3
  have hupper : sgn * (steinhausPrimePoly σ N ω).re ≤ (B : ℝ) + lam + 1 := by
    have h1 : sgn * primeRe σ ω + sgn * (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re
        ≤ (B : ℝ) := by
      have h := hKb
      rw [hsplit, mul_add] at h
      exact h
    have h2 : |sgn * (steinhausPrimePoly σ N ω).re - sgn * primeRe σ ω| < 1 := by
      rw [← mul_sub, abs_mul, hsgnabs, one_mul]
      exact hgapreal
    have h3 : |sgn * (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re| ≤ lam := by
      rw [abs_mul, hsgnabs, one_mul]
      exact hHbound
    have h4 := abs_le.mp (le_of_lt h2)
    have h5 := abs_le.mp h3
    linarith [h1, h4.2, h5.1]
  have hlower : (B : ℝ) + lam + 1 < sgn * (steinhausPrimePoly σ N ω).re := by
    have hsq : ((B : ℝ) + lam + 1) ^ 2 < (sgn * (steinhausPrimePoly σ N ω).re) ^ 2 := by
      have hs : (sgn * (steinhausPrimePoly σ N ω).re) ^ 2
          = ((steinhausPrimePoly σ N ω).re) ^ 2 := by
        rcases hsgn with rfl | rfl <;> ring
      rw [hs]
      have h1 := hω2.1
      rw [hMdef] at hAM
      linarith [h1, hAM]
    have hnn : (0:ℝ) ≤ (B : ℝ) + lam + 1 := by positivity
    nlinarith [hω2.2, hsq, hnn]
  linarith


/-! ### The main theorem -/

theorem measure_contEvent_eq_zero_or_one :
    steinhausMeasure contEvent = 0 ∨ steinhausMeasure contEvent = 1 :=
  measure_infinitePi_eq_zero_or_one_of_invariant
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => 0)
    measurableSet_contEvent (fun _ _ h => contEvent_invariant h)

/-- From a full-measure envelope event one extracts a level with measure above `1 - 1/256`. -/
theorem exists_level_of_measure_one {sgn : ℝ}
    (hone : steinhausMeasure (primeHolomorphicEvent ∩
      {ω | ∃ B : ℕ, ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)}) = 1) :
    ∃ B : ℕ, 1 - 1 / 256 < (steinhausMeasure (primeHolomorphicEvent ∩
      {ω | ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)})).toReal := by
  classical
  set Kfun : ℕ → Set Omega := fun B => primeHolomorphicEvent ∩
    {ω | ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} with hKfundef
  have hmono : Monotone Kfun := by
    intro B B' hBB' ω hω
    refine ⟨hω.1, fun k => le_trans (hω.2 k) ?_⟩
    exact_mod_cast Nat.cast_le.mpr hBB'
  have hunion : (⋃ B, Kfun B) = primeHolomorphicEvent ∩
      {ω | ∃ B : ℕ, ∀ k : ℕ, sgn * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} := by
    ext ω
    simp only [Set.mem_iUnion, hKfundef, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨B, hB0, hB⟩
      exact ⟨hB0, B, hB⟩
    · rintro ⟨hB0, B, hB⟩
      exact ⟨B, hB0, hB⟩
  have htend := tendsto_measure_iUnion_atTop (μ := steinhausMeasure) hmono
  rw [hunion, hone] at htend
  have hlt : ENNReal.ofReal (1 - 1 / 256) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)
  obtain ⟨B, hB⟩ := (htend.eventually (lt_mem_nhds hlt)).exists
  refine ⟨B, ?_⟩
  have hfin : steinhausMeasure (Kfun B) ≠ ⊤ := measure_ne_top _ _
  have := (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) hfin).mp hB
  exact this

/-- **The Helson continuation stratum is null.** -/
theorem measure_contEvent_eq_zero : steinhausMeasure contEvent = 0 := by
  classical
  rcases measure_contEvent_eq_zero_or_one with h | h
  · exact h
  exfalso
  -- the envelope covers a full-measure set
  have hΩ₀ : steinhausMeasure primeHolomorphicEvent = 1 := measure_primeHolomorphicEvent
  have hinter : steinhausMeasure (contEvent ∩ primeHolomorphicEvent) = 1 := by
    have h1 : steinhausMeasure (contEvent ∩ primeHolomorphicEvent)ᶜ = 0 := by
      have hsub : (contEvent ∩ primeHolomorphicEvent)ᶜ ⊆ contEventᶜ ∪ primeHolomorphicEventᶜ := by
        rw [Set.compl_inter]
      have h2 : steinhausMeasure contEventᶜ = 0 :=
        (prob_compl_eq_zero_iff measurableSet_contEvent).mpr h
      have h3 : steinhausMeasure primeHolomorphicEventᶜ = 0 :=
        (prob_compl_eq_zero_iff measurableSet_primeHolomorphicEvent).mpr hΩ₀
      refine le_antisymm ?_ (by exact zero_le)
      calc steinhausMeasure (contEvent ∩ primeHolomorphicEvent)ᶜ
          ≤ steinhausMeasure (contEventᶜ ∪ primeHolomorphicEventᶜ) := measure_mono hsub
        _ ≤ steinhausMeasure contEventᶜ + steinhausMeasure primeHolomorphicEventᶜ :=
            measure_union_le _ _
        _ = 0 := by rw [h2, h3, add_zero]
    exact (prob_compl_eq_zero_iff (measurableSet_contEvent.inter
      measurableSet_primeHolomorphicEvent)).mp h1
  have hcover : steinhausMeasure (negEvent ∪ posEvent) = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← hinter]
    exact measure_mono contEvent_inter_subset
  -- one of the two halves has full measure
  have hone : steinhausMeasure negEvent = 1 ∨ steinhausMeasure posEvent = 1 := by
    rcases measure_negEvent_eq_zero_or_one with h1 | h1
    · rcases measure_posEvent_eq_zero_or_one with h2 | h2
      · exfalso
        have : steinhausMeasure (negEvent ∪ posEvent) = 0 := by
          refine le_antisymm ?_ (by exact zero_le)
          calc steinhausMeasure (negEvent ∪ posEvent)
              ≤ steinhausMeasure negEvent + steinhausMeasure posEvent := measure_union_le _ _
            _ = 0 := by rw [h1, h2, add_zero]
        rw [hcover] at this
        exact one_ne_zero this
      · exact Or.inr h2
    · exact Or.inl h1
  rcases hone with hneg | hpos
  · have hset : negEvent = primeHolomorphicEvent ∩
        {ω | ∃ B : ℕ, ∀ k : ℕ, (1 : ℝ) * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} := by
      rw [negEvent]
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq, one_mul]
    rw [hset] at hneg
    obtain ⟨B, hB⟩ := exists_level_of_measure_one (sgn := 1) hneg
    exact contradiction_of_envelope (Or.inl rfl) hB
  · have hset : posEvent = primeHolomorphicEvent ∩
        {ω | ∃ B : ℕ, ∀ k : ℕ, (-1 : ℝ) * eulerExponentRe (cutSeq k) ω ≤ (B : ℝ)} := by
      rw [posEvent]
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, fun k => by linarith [hB k]⟩
      · rintro ⟨B, hB⟩
        exact ⟨B, fun k => by linarith [hB k]⟩
    rw [hset] at hpos
    obtain ⟨B, hB⟩ := exists_level_of_measure_one (sgn := -1) hpos
    exact contradiction_of_envelope (Or.inr rfl) hB


/-! ### The statement on the phase torus -/

/-- One Steinhaus phase, as a point of the unit circle. -/
def circlePhase (t : ℝ) : {z : ℂ // ‖z‖ = 1} :=
  ⟨Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ)), norm_exp_phase t⟩

theorem measurable_circlePhase : Measurable circlePhase := by
  refine Measurable.subtype_mk ?_
  exact Complex.measurable_exp.comp (by fun_prop)

/-- The uniform (Haar) measure on the unit circle. -/
def circleUniform : Measure {z : ℂ // ‖z‖ = 1} :=
  Measure.map circlePhase (volume.restrict (Set.Icc (0 : ℝ) 1))

instance : IsProbabilityMeasure circleUniform :=
  Measure.isProbabilityMeasure_map measurable_circlePhase.aemeasurable

/-- The restriction of a phase point to the prime coordinates. -/
def primeRestrict (ω : Omega) : Nat.Primes → ℝ := fun p => ω (p : ℕ)

theorem measurable_primeRestrict : Measurable primeRestrict :=
  measurable_pi_lambda _ fun p => measurable_pi_apply (p : ℕ)

theorem phaseTorusOf_eq_comp :
    phaseTorusOf = (fun (y : ∀ _i : Nat.Primes, ℝ) (i : Nat.Primes) => circlePhase (y i))
      ∘ primeRestrict := by
  funext ω p
  refine Subtype.ext ?_
  show X (p : ℕ) ω = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω (p : ℕ) : ℝ) : ℂ))
  exact X_prime_eq p.2 ω

/-- **The law of the random phase is the product of uniform circle measures.** -/
theorem map_phaseTorusOf :
    Measure.map phaseTorusOf steinhausMeasure
      = Measure.infinitePi (fun _ : Nat.Primes => circleUniform) := by
  have h1 : Measure.map primeRestrict steinhausMeasure
      = Measure.infinitePi (fun _ : Nat.Primes => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact Measure.infinitePi_map_restrict'
      (μ := fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (I := {p : ℕ | p.Prime})
  have h2 : Measure.map
      (fun (y : ∀ _i : Nat.Primes, ℝ) (i : Nat.Primes) => circlePhase (y i))
      (Measure.infinitePi (fun _ : Nat.Primes => volume.restrict (Set.Icc (0 : ℝ) 1)))
      = Measure.infinitePi (fun _ : Nat.Primes =>
          Measure.map circlePhase (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    Measure.infinitePi_map_pi _ fun _ => measurable_circlePhase
  have hmeas1 : Measurable
      (fun (y : ∀ _i : Nat.Primes, ℝ) (i : Nat.Primes) => circlePhase (y i)) := by
    refine measurable_pi_lambda _ fun i => ?_
    exact measurable_circlePhase.comp (measurable_pi_apply i)
  rw [phaseTorusOf_eq_comp, ← Measure.map_map hmeas1 measurable_primeRestrict, h1, h2]
  rfl

/-- **The Helson continuation stratum has measure zero on the phase torus.** -/
theorem measure_continuableStratum_eq_zero :
    Measure.infinitePi (fun _ : Nat.Primes => circleUniform) continuableStratum = 0 := by
  rw [← map_phaseTorusOf, Measure.map_apply measurable_phaseTorusOf measurableSet_continuableStratum]
  exact measure_contEvent_eq_zero

end GaloisForLFunctions.RHTower

end
