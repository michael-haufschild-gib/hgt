import GaloisForLFunctions.RHTower.CoherenceGraphVolumeLaw
import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence
import GaloisForLFunctions.HTGeometry.TorusReturnExponentLaw

/-!
# Discrete recurrence of a weighted coherence graph

Integer clocks act on the phase torus by measure preserving endomorphisms, so the Haar mass of the
set of frequency vectors that reach the chord-energy sublevel set within `N` steps is at most `N`
times the mass of that set.  The forest-coordinate volume law therefore converts directly into a
lower bound for the universal recurrence deadline.
-/

namespace RHTower

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The chord-energy sublevel set at resolution `ε`. -/
def energyTarget (src tgt : E → V) (a : E → ℝ) (ε : ℝ) : Set (V → UnitAddCircle) :=
  {x | graphChordEnergy src tgt a x ≤ ε ^ 2}

omit [Fintype V] in
theorem continuous_graphChordEnergy (src tgt : E → V) (a : E → ℝ) :
    Continuous (graphChordEnergy src tgt a) := by
  unfold graphChordEnergy
  fun_prop

theorem measurableSet_energyTarget (src tgt : E → V) (a : E → ℝ) (ε : ℝ) :
    MeasurableSet (energyTarget src tgt a ε) :=
  measurableSet_le (continuous_graphChordEnergy src tgt a).measurable measurable_const

/-- Every nonzero integer clock preserves the Haar mass of the sublevel set. -/
theorem measure_energyTarget_zsmul_preimage (src tgt : E → V) (a : E → ℝ) (ε : ℝ)
    {n : ℤ} (hn : n ≠ 0) :
    volume ((fun x : V → UnitAddCircle => n • x) ⁻¹' energyTarget src tgt a ε) =
      volume (energyTarget src tgt a ε) := by
  have hmp := Measure.measurePreserving_zsmul (G := V → UnitAddCircle) volume hn
  rw [← Measure.map_apply hmp.measurable (measurableSet_energyTarget src tgt a ε), hmp.map_eq]

/-- The frequency vectors that reach the sublevel set within `N` positive clocks. -/
def energyHitUnion (src tgt : E → V) (a : E → ℝ) (ε : ℝ) (N : ℕ) :
    Set (V → UnitAddCircle) :=
  ⋃ k : Fin N, (fun x : V → UnitAddCircle => ((k.1 + 1 : ℕ) : ℤ) • x) ⁻¹'
    energyTarget src tgt a ε

theorem measurableSet_energyHitUnion (src tgt : E → V) (a : E → ℝ) (ε : ℝ) (N : ℕ) :
    MeasurableSet (energyHitUnion src tgt a ε N) := by
  refine MeasurableSet.iUnion fun k => ?_
  have hmp := Measure.measurePreserving_zsmul (G := V → UnitAddCircle) volume
    (n := ((k.1 + 1 : ℕ) : ℤ)) (by omega)
  exact hmp.measurable (measurableSet_energyTarget src tgt a ε)

/-- **Union bound for the first `N` clocks.** -/
theorem measure_energyHitUnion_le (src tgt : E → V) (a : E → ℝ) (ε : ℝ) (N : ℕ) :
    volume (energyHitUnion src tgt a ε N) ≤ N * volume (energyTarget src tgt a ε) := by
  calc volume (energyHitUnion src tgt a ε N)
      ≤ ∑ k : Fin N, volume ((fun x : V → UnitAddCircle =>
          ((k.1 + 1 : ℕ) : ℤ) • x) ⁻¹' energyTarget src tgt a ε) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _k : Fin N, volume (energyTarget src tgt a ε) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact measure_energyTarget_zsmul_preimage src tgt a ε (by omega)
    _ = N * volume (energyTarget src tgt a ε) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Avoidance.**  If `N` times the mass of the sublevel set is below one, some frequency vector
misses the sublevel set at every one of the first `N` clocks. -/
theorem exists_avoiding_energyTarget (src tgt : E → V) (a : E → ℝ) (ε : ℝ) (N : ℕ)
    (h : (N : ℝ≥0∞) * volume (energyTarget src tgt a ε) < 1) :
    ∃ x : V → UnitAddCircle, ∀ n : ℕ, 0 < n → n ≤ N →
      ε ^ 2 < graphChordEnergy src tgt a ((n : ℤ) • x) := by
  have hlt : volume (energyHitUnion src tgt a ε N) < 1 :=
    lt_of_le_of_lt (measure_energyHitUnion_le src tgt a ε N) h
  have huniv : volume (Set.univ : Set (V → UnitAddCircle)) = 1 := by simp
  have hne : (energyHitUnion src tgt a ε N)ᶜ.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hcon
    rw [hcon, huniv] at hlt
    exact lt_irrefl 1 hlt
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, fun n hn hnN => ?_⟩
  by_contra hcon
  push Not at hcon
  refine hx ?_
  rw [energyHitUnion, Set.mem_iUnion]
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  simp only [Set.mem_preimage, energyTarget, Set.mem_setOf_eq]
  rw [show ((n - 1 : ℕ) + 1 : ℕ) = n from by omega]
  exact hcon

/-! ## The pigeonhole deadline -/

/-- **Quantitative simultaneous recurrence on the phase torus.**  Some clock at most `(Q+1)^d`
brings every coordinate within `1/(Q+1)` of the identity. -/
theorem exists_nsmul_norm_le_quantitative {d Q : ℕ} (ξ : Fin d → UnitAddCircle) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧ ∀ i, ‖(n • ξ) i‖ ≤ 1 / (Q + 1 : ℝ) := by
  choose α hα using fun i : Fin d => QuotientAddGroup.mk_surjective (ξ i)
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_integer_approximation_quantitative (Q := Q) α
  refine ⟨n, hn, hnQ, fun i => ?_⟩
  have hrep : (n • ξ) i = (((n : ℝ) * α i : ℝ) : UnitAddCircle) := by
    rw [Pi.smul_apply, ← hα i, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [hrep, UnitAddCircle.norm_eq]
  exact le_trans (round_le _ (r i)) (hr i)

/-- The nonroot vertices of a rooted forest, as a fintype of cardinality the rank. -/
theorem card_nonroot_eq_rank (T : RootedForest V) :
    Fintype.card {v : V // T.depth v ≠ 0} = T.rank := by
  classical
  rw [RootedForest.rank, Fintype.card_subtype]

/-- **The pigeonhole deadline.**  Every phase vector is brought within chord energy
`K_F (2π/(Q+1))²` by some clock at most `(Q+1)^rank`. -/
theorem exists_clock_graphChordEnergy_le {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (x : V → UnitAddCircle) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ T.rank ∧
      graphChordEnergy src tgt a ((n : ℤ) • x) ≤
        chart.constant a * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 := by
  classical
  have hcard := card_nonroot_eq_rank T
  let e : Fin T.rank ≃ {v : V // T.depth v ≠ 0} :=
    (Fintype.equivFinOfCardEq hcard).symm
  let ξ : Fin T.rank → UnitAddCircle := fun k => T.shear x (e k).1
  obtain ⟨n, hn, hnQ, hnorm⟩ := exists_nsmul_norm_le_quantitative (Q := Q) ξ
  refine ⟨n, hn, hnQ, ?_⟩
  refine graphChordEnergy_le_of_shear_le chart ha _ ?_
  intro v hv
  have hshear : T.shear ((n : ℤ) • x) v = (n : ℤ) • T.shear x v := by
    have hmap : T.shear ((n : ℤ) • x) = (n : ℤ) • T.shear x := by
      have := map_zsmul (T.shearEquiv (A := UnitAddCircle)).toAddMonoidHom (n : ℤ) x
      simpa using this
    rw [hmap]
    rfl
  have hkey : ‖T.shear ((n : ℤ) • x) v‖ ≤ 1 / (Q + 1 : ℝ) := by
    have hidx : e (e.symm ⟨v, hv⟩) = ⟨v, hv⟩ := e.apply_symm_apply _
    have hval := hnorm (e.symm ⟨v, hv⟩)
    simp only [ξ, Pi.smul_apply, hidx] at hval
    rw [hshear]
    have hcast : ((n : ℤ)) • T.shear x v = (n : ℕ) • T.shear x v := by
      rw [natCast_zsmul]
    rw [hcast]
    exact hval
  calc ‖fourier 1 (T.shear ((n : ℤ) • x) v) - 1‖
      ≤ 2 * Real.pi * ‖T.shear ((n : ℤ) • x) v‖ :=
        norm_fourier_one_sub_one_le_two_pi_mul_norm _
    _ ≤ 2 * Real.pi * (1 / (Q + 1 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 2 * Real.pi / (Q + 1 : ℝ) := by ring

/-! ## Universal deadlines -/

/-- `N` is a universal recurrence deadline at resolution `ε`: every phase vector reaches chord
energy at most `ε²` at some positive clock no later than `N`. -/
def IsUniversalDeadline (src tgt : E → V) (a : E → ℝ) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ x : V → UnitAddCircle, ∃ n : ℕ, 0 < n ∧ n ≤ N ∧
    graphChordEnergy src tgt a ((n : ℤ) • x) ≤ ε ^ 2

omit [Fintype V] in
theorem IsUniversalDeadline.mono {src tgt : E → V} {a : E → ℝ} {ε : ℝ} {N M : ℕ}
    (h : IsUniversalDeadline src tgt a ε N) (hNM : N ≤ M) :
    IsUniversalDeadline src tgt a ε M := by
  intro x
  obtain ⟨n, hn, hnN, hval⟩ := h x
  exact ⟨n, hn, le_trans hnN hNM, hval⟩

/-- **The pigeonhole deadline is universal.** -/
theorem isUniversalDeadline_pigeonhole {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) (Q : ℕ) :
    IsUniversalDeadline src tgt a
      (Real.sqrt (chart.constant a) * (2 * Real.pi / (Q + 1 : ℝ))) ((Q + 1) ^ T.rank) := by
  intro x
  obtain ⟨n, hn, hnQ, hval⟩ := exists_clock_graphChordEnergy_le chart ha x Q
  refine ⟨n, hn, hnQ, ?_⟩
  have hsq : (Real.sqrt (chart.constant a) * (2 * Real.pi / (Q + 1 : ℝ))) ^ 2
      = chart.constant a * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (chart.constant_nonneg ha)]
  rw [hsq]
  exact hval

/-- **A small target forbids a deadline.** -/
theorem not_isUniversalDeadline_of_measure_lt (src tgt : E → V) (a : E → ℝ) (ε : ℝ) (N : ℕ)
    (h : (N : ℝ≥0∞) * volume (energyTarget src tgt a ε) < 1) :
    ¬ IsUniversalDeadline src tgt a ε N := by
  obtain ⟨x, hx⟩ := exists_avoiding_energyTarget src tgt a ε N h
  intro hdead
  obtain ⟨n, hn, hnN, hval⟩ := hdead x
  exact absurd hval (not_le.2 (hx n hn hnN))

/-- The least universal deadline at resolution `ε`. -/
def universalDeadline (src tgt : E → V) (a : E → ℝ) (ε : ℝ) : ℕ :=
  sInf {N : ℕ | IsUniversalDeadline src tgt a ε N}

omit [Fintype V] in
theorem universalDeadline_le {src tgt : E → V} {a : E → ℝ} {ε : ℝ} {N : ℕ}
    (h : IsUniversalDeadline src tgt a ε N) : universalDeadline src tgt a ε ≤ N :=
  Nat.sInf_le h

omit [Fintype V] in
theorem lt_universalDeadline_of_not {src tgt : E → V} {a : E → ℝ} {ε : ℝ} {N : ℕ}
    (hne : ∃ M, IsUniversalDeadline src tgt a ε M)
    (h : ¬ IsUniversalDeadline src tgt a ε N) : N < universalDeadline src tgt a ε := by
  by_contra hcon
  push Not at hcon
  have hmem : IsUniversalDeadline src tgt a ε (universalDeadline src tgt a ε) :=
    Nat.sInf_mem hne
  exact h (hmem.mono hcon)

/-! ## Quantitative two-sided deadline bounds -/

omit [Fintype V] in
theorem IsUniversalDeadline.mono_resolution {src tgt : E → V} {a : E → ℝ} {ε ε' : ℝ} {N : ℕ}
    (h : IsUniversalDeadline src tgt a ε' N) (hε' : 0 ≤ ε') (hle : ε' ≤ ε) :
    IsUniversalDeadline src tgt a ε N := by
  intro x
  obtain ⟨n, hn, hnN, hval⟩ := h x
  exact ⟨n, hn, hnN, le_trans hval (by nlinarith)⟩

/-- The forest constant controlling the mass of the sublevel set. -/
def ForestChart.upperConstant {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (a : E → ℝ) : ℝ :=
  ∏ v : V, if T.depth v = 0 then 1 else 1 / (2 * Real.sqrt (a (chart.edgeAt v)))

omit [Fintype E] in
theorem ForestChart.upperConstant_pos {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ}
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) :
    0 < chart.upperConstant a := by
  refine Finset.prod_pos fun v _ => ?_
  by_cases h : T.depth v = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    have := Real.sqrt_pos.2 (hpos v h)
    positivity

omit [Fintype E] in
theorem prod_radius_eq {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (a : E → ℝ) (ε : ℝ) :
    (∏ v : V, if T.depth v = 0 then 1
      else ε / (2 * Real.sqrt (a (chart.edgeAt v)))) =
      ε ^ T.rank * chart.upperConstant a := by
  classical
  have hsplit : ∀ v : V,
      (if T.depth v = 0 then (1 : ℝ) else ε / (2 * Real.sqrt (a (chart.edgeAt v))))
        = (if T.depth v = 0 then (1 : ℝ) else ε) *
          (if T.depth v = 0 then (1 : ℝ) else 1 / (2 * Real.sqrt (a (chart.edgeAt v)))) := by
    intro v
    by_cases h : T.depth v = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [div_eq_mul_one_div]
  rw [Finset.prod_congr rfl (fun v _ => hsplit v), Finset.prod_mul_distrib,
    ForestChart.upperConstant]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, RootedForest.rank]

theorem measure_energyTarget_le {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (energyTarget src tgt a ε) ≤
      ENNReal.ofReal (ε ^ T.rank * chart.upperConstant a) := by
  have h := volume_graphChordEnergy_le chart ha hpos hε
  rwa [prod_radius_eq] at h

/-- **Deadline lower bound.**  A clock budget whose mass share is below one cannot be a universal
deadline, so the least deadline exceeds it. -/
theorem lt_universalDeadline_of_mass_lt_one {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    (hne : ∃ M, IsUniversalDeadline src tgt a ε M)
    (h : (N : ℝ) * (ε ^ T.rank * chart.upperConstant a) < 1) :
    N < universalDeadline src tgt a ε := by
  refine lt_universalDeadline_of_not hne
    (not_isUniversalDeadline_of_measure_lt src tgt a ε N ?_)
  have hcpos : 0 < chart.upperConstant a := chart.upperConstant_pos hpos
  have hnn : 0 ≤ ε ^ T.rank * chart.upperConstant a := by positivity
  calc (N : ℝ≥0∞) * volume (energyTarget src tgt a ε)
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (ε ^ T.rank * chart.upperConstant a) := by
        gcongr
        exact measure_energyTarget_le chart ha hpos hε
    _ = ENNReal.ofReal ((N : ℝ) * (ε ^ T.rank * chart.upperConstant a)) := by
        conv_rhs => rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    _ < 1 := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 h

/-- **Deadline upper bound.**  The pigeonhole budget is a universal deadline. -/
theorem universalDeadline_le_pow {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ε : ℝ} (Q : ℕ)
    (hQ : Real.sqrt (chart.constant a) * (2 * Real.pi / (Q + 1 : ℝ)) ≤ ε) :
    universalDeadline src tgt a ε ≤ (Q + 1) ^ T.rank :=
  universalDeadline_le
    ((isUniversalDeadline_pigeonhole chart ha Q).mono_resolution
      (by positivity) hQ)

/-- Universal deadlines exist at every positive resolution. -/
theorem exists_isUniversalDeadline {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ε : ℝ} (hε : 0 < ε) :
    ∃ M, IsUniversalDeadline src tgt a ε M := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.sqrt (chart.constant a) * (2 * Real.pi) / ε)
  refine ⟨(Q + 1) ^ T.rank, (isUniversalDeadline_pigeonhole chart ha Q).mono_resolution
    (by positivity) ?_⟩
  have hQ1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hlt : Real.sqrt (chart.constant a) * (2 * Real.pi) < (Q : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hQ
    exact hQ
  have hform : Real.sqrt (chart.constant a) * (2 * Real.pi / ((Q : ℝ) + 1))
      = Real.sqrt (chart.constant a) * (2 * Real.pi) / ((Q : ℝ) + 1) := by ring
  rw [hform, div_le_iff₀ hQ1]
  nlinarith [hlt, hε.le]

/-! ## The minimax recurrence exponent -/

theorem one_le_universalDeadline {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ε : ℝ} (hε : 0 < ε)
    (hrank : 0 < T.rank) : 1 ≤ universalDeadline src tgt a ε := by
  have hne : ∃ M, IsUniversalDeadline src tgt a ε M := exists_isUniversalDeadline chart ha hε
  have hmem : IsUniversalDeadline src tgt a ε (universalDeadline src tgt a ε) :=
    Nat.sInf_mem hne
  by_contra hcon
  push Not at hcon
  have hzero : universalDeadline src tgt a ε = 0 := by omega
  rw [hzero] at hmem
  have hV : Nonempty V := by
    rw [RootedForest.rank, Finset.card_pos] at hrank
    obtain ⟨v, -⟩ := hrank
    exact ⟨v⟩
  obtain ⟨v⟩ := hV
  obtain ⟨n, hn, hn0, -⟩ := hmem (fun _ => 0)
  omega

theorem universalDeadline_le_of_lt_one {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (universalDeadline src tgt a ε : ℝ) ≤
      ((Real.sqrt (chart.constant a) * (2 * Real.pi) + 2) / ε) ^ T.rank := by
  set C₀ : ℝ := Real.sqrt (chart.constant a) * (2 * Real.pi) with hC₀
  have hC₀nn : 0 ≤ C₀ := by positivity
  set Q : ℕ := ⌈C₀ / ε⌉₊ with hQdef
  have hceil : C₀ / ε ≤ (Q : ℝ) := Nat.le_ceil _
  have hQ1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hres : Real.sqrt (chart.constant a) * (2 * Real.pi / ((Q : ℝ) + 1)) ≤ ε := by
    have hform : Real.sqrt (chart.constant a) * (2 * Real.pi / ((Q : ℝ) + 1))
        = C₀ / ((Q : ℝ) + 1) := by rw [hC₀]; ring
    rw [hform, div_le_iff₀ hQ1]
    have hle : C₀ ≤ (Q : ℝ) * ε := by
      rw [div_le_iff₀ hε] at hceil
      exact hceil
    nlinarith [hle, hε.le]
  have hdead : universalDeadline src tgt a ε ≤ (Q + 1) ^ T.rank :=
    universalDeadline_le_pow chart ha Q hres
  have hcast : ((universalDeadline src tgt a ε : ℕ) : ℝ) ≤ (((Q + 1) ^ T.rank : ℕ) : ℝ) := by
    exact_mod_cast hdead
  refine le_trans hcast ?_
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [le_div_iff₀ hε]
  have hQlt : (Q : ℝ) < C₀ / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdiv : C₀ / ε * ε = C₀ := div_mul_cancel₀ _ (ne_of_gt hε)
  nlinarith [hQlt, hε.le, hε1, hdiv]

theorem lt_universalDeadline_quantitative {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) {ε : ℝ} (hε : 0 < ε) :
    1 / (2 * chart.upperConstant a * ε ^ T.rank) < (universalDeadline src tgt a ε : ℝ) := by
  set C : ℝ := chart.upperConstant a with hC
  have hCpos : 0 < C := chart.upperConstant_pos hpos
  have hεpow : 0 < ε ^ T.rank := by positivity
  set x : ℝ := 1 / (2 * C * ε ^ T.rank) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  set N : ℕ := ⌊x⌋₊ with hN
  have hNle : (N : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
  have hmass : (N : ℝ) * (ε ^ T.rank * C) < 1 := by
    have hprod : x * (ε ^ T.rank * C) = 1 / 2 := by
      rw [hx]
      field_simp
    nlinarith [hNle, hεpow, hCpos, hprod]
  have hne : ∃ M, IsUniversalDeadline src tgt a ε M := exists_isUniversalDeadline chart ha hε
  have hlt : N < universalDeadline src tgt a ε :=
    lt_universalDeadline_of_mass_lt_one chart ha hpos (le_of_lt hε) N hne hmass
  have hfloor : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcast : ((N : ℕ) : ℝ) + 1 ≤ ((universalDeadline src tgt a ε : ℕ) : ℝ) := by
    exact_mod_cast hlt
  linarith

/-- **The minimax recurrence exponent.**  The least universal deadline has logarithmic exponent
exactly the graph rank. -/
theorem tendsto_log_universalDeadline {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) (hrank : 0 < T.rank) :
    Filter.Tendsto
      (fun ε : ℝ => Real.log (universalDeadline src tgt a ε : ℝ) / Real.log (1 / ε))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (T.rank : ℝ)) := by
  classical
  have hC₀nn : (0 : ℝ) ≤ Real.sqrt (chart.constant a) * (2 * Real.pi) := by positivity
  have hCpos : 0 < chart.upperConstant a := chart.upperConstant_pos hpos
  have hc₁pos : 0 < ((Real.sqrt (chart.constant a) * (2 * Real.pi) + 2)⁻¹) ^ T.rank := by
    positivity
  have hc₂pos : 0 < 2 * chart.upperConstant a := by positivity
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :=
    Ioo_mem_nhdsGT one_pos
  have hmem : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ε ∈ Set.Ioo (0 : ℝ) 1 :=
    Filter.eventually_of_mem hIoo fun _ h => h
  have hDpos : ∀ ε : ℝ, 0 < ε → (0 : ℝ) < (universalDeadline src tgt a ε : ℝ) := by
    intro ε hεpos
    have := one_le_universalDeadline chart ha hεpos hrank
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlow : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ((Real.sqrt (chart.constant a) * (2 * Real.pi) + 2)⁻¹) ^ T.rank * ε ^ T.rank ≤
        1 / (universalDeadline src tgt a ε : ℝ) := by
    filter_upwards [hmem] with ε hε
    have hεpos : 0 < ε := hε.1
    have hup := universalDeadline_le_of_lt_one chart ha hεpos (le_of_lt hε.2)
    rw [le_div_iff₀ (hDpos ε hεpos)]
    have hpow : ((Real.sqrt (chart.constant a) * (2 * Real.pi) + 2) / ε) ^ T.rank *
        (((Real.sqrt (chart.constant a) * (2 * Real.pi) + 2)⁻¹) ^ T.rank * ε ^ T.rank) = 1 := by
      rw [← mul_pow, ← mul_pow,
        show (Real.sqrt (chart.constant a) * (2 * Real.pi) + 2) / ε *
            ((Real.sqrt (chart.constant a) * (2 * Real.pi) + 2)⁻¹ * ε) = 1 from by field_simp]
      exact one_pow _
    nlinarith [hup, hc₁pos, pow_pos hεpos T.rank, hDpos ε hεpos,
      mul_pos hc₁pos (pow_pos hεpos T.rank)]
  have hhigh : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      1 / (universalDeadline src tgt a ε : ℝ) ≤
        (2 * chart.upperConstant a) * ε ^ T.rank := by
    filter_upwards [hmem] with ε hε
    have hεpos : 0 < ε := hε.1
    have hlow' := lt_universalDeadline_quantitative chart ha hpos hεpos
    rw [div_le_iff₀ (hDpos ε hεpos)]
    have hposprod : 0 < 2 * chart.upperConstant a * ε ^ T.rank := by positivity
    have hkey : 1 / (2 * chart.upperConstant a * ε ^ T.rank) *
        (2 * chart.upperConstant a * ε ^ T.rank) = 1 :=
      one_div_mul_cancel (ne_of_gt hposprod)
    have hmul := mul_lt_mul_of_pos_right hlow' hposprod
    rw [hkey] at hmul
    nlinarith [hmul]
  have hmain := GaloisForLFunctions.HTGeometry.tendsto_log_div_log_of_power_sandwich
    hc₁pos hc₂pos hlow hhigh
  refine hmain.congr' ?_
  filter_upwards [hmem] with ε hε
  have hεpos : 0 < ε := hε.1
  have hne : (universalDeadline src tgt a ε : ℝ) ≠ 0 := ne_of_gt (hDpos ε hεpos)
  rw [Real.log_div one_ne_zero hne, Real.log_div one_ne_zero (ne_of_gt hεpos),
    Real.log_one, zero_sub, zero_sub, neg_div, div_neg]

/-! ## The first return clock of a fixed spectrum -/

/-- The first positive clock at which a fixed phase vector reaches chord energy `ε²`. -/
def firstReturn (src tgt : E → V) (a : E → ℝ) (ω : V → UnitAddCircle) (ε : ℝ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ graphChordEnergy src tgt a ((n : ℤ) • ω) ≤ ε ^ 2}

omit [Fintype V] in
theorem firstReturn_spec {src tgt : E → V} {a : E → ℝ} {ω : V → UnitAddCircle} {ε : ℝ}
    (h : ∃ n : ℕ, 0 < n ∧ graphChordEnergy src tgt a ((n : ℤ) • ω) ≤ ε ^ 2) :
    0 < firstReturn src tgt a ω ε ∧
      graphChordEnergy src tgt a ((firstReturn src tgt a ω ε : ℤ) • ω) ≤ ε ^ 2 :=
  Nat.sInf_mem h

omit [Fintype V] in
theorem firstReturn_le {src tgt : E → V} {a : E → ℝ} {ω : V → UnitAddCircle} {ε : ℝ} {n : ℕ}
    (hn : 0 < n) (hval : graphChordEnergy src tgt a ((n : ℤ) • ω) ≤ ε ^ 2) :
    firstReturn src tgt a ω ε ≤ n :=
  Nat.sInf_le ⟨hn, hval⟩

/-- **The universal deadline dominates every first return.** -/
theorem firstReturn_le_universalDeadline {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ε : ℝ} (hε : 0 < ε)
    (ω : V → UnitAddCircle) :
    firstReturn src tgt a ω ε ≤ universalDeadline src tgt a ε := by
  have hne : ∃ M, IsUniversalDeadline src tgt a ε M := exists_isUniversalDeadline chart ha hε
  have hmem : IsUniversalDeadline src tgt a ε (universalDeadline src tgt a ε) :=
    Nat.sInf_mem hne
  obtain ⟨n, hn, hnD, hval⟩ := hmem ω
  exact le_trans (firstReturn_le hn hval) hnD

/-! ## Almost every spectrum has no exact return -/

omit [Fintype V] in
theorem graphChordEnergy_nonneg {src tgt : E → V} {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (x : V → UnitAddCircle) : 0 ≤ graphChordEnergy src tgt a x :=
  Finset.sum_nonneg fun e _ => mul_nonneg (ha e) (sq_nonneg _)

/-- **A positive rank forbids an exact zero of the chord energy on a positive mass.** -/
theorem volume_zeroEnergy_eq_zero {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) (hrank : 0 < T.rank) :
    volume {x : V → UnitAddCircle | graphChordEnergy src tgt a x = 0} = 0 := by
  have hCpos : 0 < chart.upperConstant a := chart.upperConstant_pos hpos
  refine le_antisymm ?_ zero_le
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro η hη _
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  set ε : ℝ := min 1 ((η : ℝ) / chart.upperConstant a) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε * chart.upperConstant a ≤ (η : ℝ) := by
    have h2 : ε ≤ (η : ℝ) / chart.upperConstant a := min_le_right _ _
    rw [le_div_iff₀ hCpos] at h2
    exact h2
  have hsub : {x : V → UnitAddCircle | graphChordEnergy src tgt a x = 0} ⊆
      energyTarget src tgt a ε := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [energyTarget, Set.mem_setOf_eq, hx]
    positivity
  have hbound := measure_energyTarget_le chart ha hpos (le_of_lt hεpos)
  have hpow : ε ^ T.rank ≤ ε := by
    calc ε ^ T.rank ≤ ε ^ 1 := pow_le_pow_of_le_one (le_of_lt hεpos) hε1 hrank
      _ = ε := pow_one ε
  calc volume {x : V → UnitAddCircle | graphChordEnergy src tgt a x = 0}
      ≤ volume (energyTarget src tgt a ε) := measure_mono hsub
    _ ≤ ENNReal.ofReal (ε ^ T.rank * chart.upperConstant a) := hbound
    _ ≤ ENNReal.ofReal ((η : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hpow, hCpos, hεη]
    _ = 0 + (η : ℝ≥0∞) := by rw [zero_add, ENNReal.ofReal_coe_nnreal]

/-- **Almost every spectrum has strictly positive chord energy at every positive clock.** -/
theorem ae_forall_pos_graphChordEnergy {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) (hrank : 0 < T.rank) :
    ∀ᵐ ω : V → UnitAddCircle,
      ∀ n : ℕ, 0 < n → 0 < graphChordEnergy src tgt a ((n : ℤ) • ω) := by
  have hzero := volume_zeroEnergy_eq_zero chart ha hpos hrank
  have hbad : volume (⋃ n : ℕ, (fun ω : V → UnitAddCircle => ((n + 1 : ℕ) : ℤ) • ω) ⁻¹'
      {x : V → UnitAddCircle | graphChordEnergy src tgt a x = 0}) = 0 := by
    refine measure_iUnion_null fun n => ?_
    have hmp := Measure.measurePreserving_zsmul (G := V → UnitAddCircle) volume
      (n := ((n + 1 : ℕ) : ℤ)) (by omega)
    have hms : MeasurableSet {x : V → UnitAddCircle | graphChordEnergy src tgt a x = 0} :=
      measurableSet_eq_fun (continuous_graphChordEnergy src tgt a).measurable measurable_const
    rw [← Measure.map_apply hmp.measurable hms, hmp.map_eq, hzero]
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null ?_ hbad
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω
  push Not at hω
  obtain ⟨n, hn, hval⟩ := hω
  rw [Set.mem_iUnion]
  refine ⟨n - 1, ?_⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ((n - 1 : ℕ) + 1 : ℕ) = n from by omega]
  exact le_antisymm hval (graphChordEnergy_nonneg ha _)

/-! ## Borel--Cantelli: almost every spectrum avoids the shrinking targets -/

/-- **First Borel--Cantelli for the shrinking chord targets.**  If `s · rank > 1` then almost every
spectrum eventually misses the target of radius `n^{-s}` at clock `n`. -/
theorem ae_eventually_lt_graphChordEnergy {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) {s : ℝ}
    (hsr : 1 < s * T.rank) :
    ∀ᵐ ω : V → UnitAddCircle, ∀ᶠ n : ℕ in Filter.atTop,
      (((n : ℝ) ^ (-s)) ^ 2 : ℝ) < graphChordEnergy src tgt a ((n : ℤ) • ω) := by
  classical
  have hCpos : 0 < chart.upperConstant a := chart.upperConstant_pos hpos
  set A : ℕ → Set (V → UnitAddCircle) := fun n =>
    (fun ω : V → UnitAddCircle => ((n + 1 : ℕ) : ℤ) • ω) ⁻¹'
      energyTarget src tgt a (((n + 1 : ℕ) : ℝ) ^ (-s)) with hA
  have hbase : ∀ n : ℕ, (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hpowid : ∀ n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ (-s)) ^ T.rank : ℝ)
      = ((n + 1 : ℕ) : ℝ) ^ (-(s * T.rank)) := by
    intro n
    rw [← Real.rpow_natCast (((n + 1 : ℕ) : ℝ) ^ (-s)) T.rank,
      ← Real.rpow_mul (hbase n)]
    ring_nf
  have hmeas : ∀ n : ℕ, volume (A n) ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (-(s * T.rank)) * chart.upperConstant a) := by
    intro n
    have hzs := measure_energyTarget_zsmul_preimage src tgt a
      (((n + 1 : ℕ) : ℝ) ^ (-s)) (n := ((n + 1 : ℕ) : ℤ)) (by omega)
    rw [hA]
    simp only
    rw [hzs]
    have hnn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (hbase n) _
    have h := measure_energyTarget_le chart ha hpos hnn
    rwa [hpowid n] at h
  have hsum : Summable fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (-(s * T.rank)) * chart.upperConstant a := by
    refine Summable.mul_right _ ?_
    have hbaseSum : Summable fun n : ℕ => ((n : ℝ)) ^ (-(s * T.rank)) := by
      have := (Real.summable_one_div_nat_rpow (p := s * T.rank)).2 hsr
      simpa [Real.rpow_neg, one_div] using this
    exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(s * T.rank))) 1).2 hbaseSum
  have hfinite : ∑' n : ℕ, volume (A n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeas)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  have hlimsup := MeasureTheory.measure_limsup_atTop_eq_zero (μ := (volume :
    Measure (V → UnitAddCircle))) hfinite
  have hae : ∀ᵐ ω : V → UnitAddCircle, ω ∉ Filter.limsup A Filter.atTop :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hlimsup
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently] at hω
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hω
  refine Filter.eventually_atTop.2 ⟨N + 1, fun m hm => ?_⟩
  have hm1 : m - 1 ≥ N := by omega
  have := hN (m - 1) hm1
  rw [hA] at this
  simp only [Set.mem_preimage, energyTarget, Set.mem_setOf_eq, not_le] at this
  rw [show ((m - 1 : ℕ) + 1 : ℕ) = m from by omega] at this
  exact this


/-! ## The almost-sure recurrence exponent -/

omit [Fintype V] in
/-- A uniform positive floor for the chord energy along the first `M` positive clocks. -/
theorem exists_uniform_pos_energy {src tgt : E → V} {a : E → ℝ} {ω : V → UnitAddCircle}
    (hω : ∀ n : ℕ, 0 < n → 0 < graphChordEnergy src tgt a ((n : ℤ) • ω)) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 0 < n → n ≤ M →
      δ ≤ graphChordEnergy src tgt a ((n : ℤ) • ω) := by
  induction M with
  | zero => exact ⟨1, one_pos, fun n hn hle => absurd hle (by omega)⟩
  | succ M ih =>
      obtain ⟨δ, hδ, hbound⟩ := ih
      refine ⟨min δ (graphChordEnergy src tgt a (((M + 1 : ℕ) : ℤ) • ω)),
        lt_min hδ (hω (M + 1) (by omega)), ?_⟩
      intro n hn hle
      rcases Nat.lt_or_ge n (M + 1) with h | h
      · exact le_trans (min_le_left _ _) (hbound n hn (by omega))
      · have hn' : n = M + 1 := by omega
        subst hn'
        exact min_le_right _ _

/-- Every positive resolution admits a return clock. -/
theorem exists_return {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ε : ℝ} (hε : 0 < ε)
    (ω : V → UnitAddCircle) :
    ∃ n : ℕ, 0 < n ∧ graphChordEnergy src tgt a ((n : ℤ) • ω) ≤ ε ^ 2 := by
  have hne : ∃ M, IsUniversalDeadline src tgt a ε M := exists_isUniversalDeadline chart ha hε
  obtain ⟨n, hn, -, hval⟩ :=
    (Nat.sInf_mem hne : IsUniversalDeadline src tgt a ε (universalDeadline src tgt a ε)) ω
  exact ⟨n, hn, hval⟩

/-- **The first return diverges.**  If a spectrum never has an exact return, its first return
clock exceeds any prescribed budget once the resolution is fine enough. -/
theorem eventually_le_firstReturn {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) {ω : V → UnitAddCircle}
    (hω : ∀ n : ℕ, 0 < n → 0 < graphChordEnergy src tgt a ((n : ℤ) • ω)) (M : ℕ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), M ≤ firstReturn src tgt a ω ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_pos_energy hω M
  have hmem : Set.Ioo (0 : ℝ) (Real.sqrt δ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :=
    Ioo_mem_nhdsGT (Real.sqrt_pos.2 hδ)
  filter_upwards [Filter.eventually_of_mem hmem fun _ h => h] with ε hε
  by_contra hcon
  push Not at hcon
  obtain ⟨hposR, hval⟩ := firstReturn_spec (exists_return chart ha hε.1 ω)
  have hlow := hbound _ hposR (le_of_lt hcon)
  have hε2 : ε ^ 2 < δ := by
    nlinarith [Real.sq_sqrt (le_of_lt hδ), Real.sqrt_nonneg δ, hε.1, hε.2]
  linarith

/-- **The almost-sure recurrence exponent.**  For almost every spectrum the first chord-energy
return clock at resolution `ε` has logarithmic exponent exactly the graph rank. -/
theorem ae_tendsto_log_firstReturn {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hpos : ∀ v, T.depth v ≠ 0 → 0 < a (chart.edgeAt v)) (hrank : 0 < T.rank) :
    ∀ᵐ ω : V → UnitAddCircle,
      Filter.Tendsto
        (fun ε : ℝ => Real.log (firstReturn src tgt a ω ε : ℝ) / Real.log (1 / ε))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (T.rank : ℝ)) := by
  classical
  have hrankR : (0 : ℝ) < T.rank := by exact_mod_cast hrank
  have hBC : ∀ᵐ ω : V → UnitAddCircle, ∀ q : ℚ, 1 < (q : ℝ) * T.rank →
      ∀ᶠ n : ℕ in Filter.atTop,
        ((((n : ℝ)) ^ (-(q : ℝ))) ^ 2 : ℝ) < graphChordEnergy src tgt a ((n : ℤ) • ω) := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    by_cases hq : 1 < (q : ℝ) * T.rank
    · filter_upwards [ae_eventually_lt_graphChordEnergy chart ha hpos hq] with ω hω using
        fun _ => hω
    · filter_upwards with ω using fun h => absurd h hq
  have hDead := tendsto_log_universalDeadline chart ha hpos hrank
  filter_upwards [ae_forall_pos_graphChordEnergy chart ha hpos hrank, hBC] with ω hωpos hωBC
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :=
    Ioo_mem_nhdsGT one_pos
  have hmem : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ε ∈ Set.Ioo (0 : ℝ) 1 :=
    Filter.eventually_of_mem hIoo fun _ h => h
  have hlogpos : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → 0 < Real.log (1 / ε) := by
    intro ε hε
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hε.1, one_mul]
    exact hε.2
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [hmem, eventually_le_firstReturn chart ha hωpos 2] with ε hε hR
      have hL := hlogpos ε hε
      have hlog2 : (0 : ℝ) < Real.log (firstReturn src tgt a ω ε : ℝ) := by
        refine Real.log_pos ?_
        have : (2 : ℝ) ≤ (firstReturn src tgt a ω ε : ℝ) := by exact_mod_cast hR
        linarith
      have : 0 < Real.log (firstReturn src tgt a ω ε : ℝ) / Real.log (1 / ε) := by positivity
      linarith
    · obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ, 1 / (T.rank : ℝ) < (q : ℝ) ∧ (q : ℝ) < 1 / b :=
        exists_rat_btwn (one_div_lt_one_div_of_lt hb0 hb)
      have hqpos : (0 : ℝ) < (q : ℝ) := lt_trans (by positivity) hq1
      have hqrank : 1 < (q : ℝ) * T.rank := by
        rw [div_lt_iff₀ hrankR] at hq1
        linarith
      have hbq : b < 1 / (q : ℝ) := by
        rw [lt_div_iff₀ hqpos]
        rw [lt_div_iff₀ hb0] at hq2
        linarith
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hωBC q hqrank)
      filter_upwards [hmem, eventually_le_firstReturn chart ha hωpos (max N 1)] with ε hε hR
      have hRN : N ≤ firstReturn src tgt a ω ε := le_trans (le_max_left _ _) hR
      have hR1 : 1 ≤ firstReturn src tgt a ω ε := le_trans (le_max_right _ _) hR
      have hmpos : (0 : ℝ) < (firstReturn src tgt a ω ε : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hR1
      obtain ⟨-, hval⟩ := firstReturn_spec (exists_return chart ha hε.1 ω)
      have hgt := hN _ hRN
      have hsq : (((firstReturn src tgt a ω ε : ℝ)) ^ (-(q : ℝ))) ^ 2 < ε ^ 2 :=
        lt_of_lt_of_le hgt hval
      have hnn : (0 : ℝ) ≤ ((firstReturn src tgt a ω ε : ℝ)) ^ (-(q : ℝ)) :=
        Real.rpow_nonneg (le_of_lt hmpos) _
      have hlt : ((firstReturn src tgt a ω ε : ℝ)) ^ (-(q : ℝ)) < ε := by
        by_contra hcon
        push Not at hcon
        nlinarith [hε.1]
      have hApos : (0 : ℝ) < ((firstReturn src tgt a ω ε : ℝ)) ^ ((q : ℝ)) :=
        Real.rpow_pos_of_pos hmpos _
      have hinv : (((firstReturn src tgt a ω ε : ℝ)) ^ ((q : ℝ)))⁻¹ < ε := by
        rwa [Real.rpow_neg (le_of_lt hmpos)] at hlt
      have hone : 1 / ε < ((firstReturn src tgt a ω ε : ℝ)) ^ ((q : ℝ)) := by
        rw [div_lt_iff₀ hε.1]
        have hcancel : ((firstReturn src tgt a ω ε : ℝ)) ^ ((q : ℝ)) *
            (((firstReturn src tgt a ω ε : ℝ)) ^ ((q : ℝ)))⁻¹ = 1 :=
          mul_inv_cancel₀ (ne_of_gt hApos)
        nlinarith [mul_lt_mul_of_pos_left hinv hApos]
      have hloglt : Real.log (1 / ε) <
          (q : ℝ) * Real.log (firstReturn src tgt a ω ε : ℝ) := by
        have := Real.log_lt_log (div_pos one_pos hε.1) hone
        rwa [Real.log_rpow hmpos] at this
      have hL := hlogpos ε hε
      rw [lt_div_iff₀ hL]
      have h1 : b * Real.log (1 / ε) < (1 / (q : ℝ)) * Real.log (1 / ε) :=
        mul_lt_mul_of_pos_right hbq hL
      have h2 : (1 / (q : ℝ)) * Real.log (1 / ε) <
          (1 / (q : ℝ)) * ((q : ℝ) * Real.log (firstReturn src tgt a ω ε : ℝ)) :=
        mul_lt_mul_of_pos_left hloglt (by positivity)
      have h3 : (1 / (q : ℝ)) * ((q : ℝ) * Real.log (firstReturn src tgt a ω ε : ℝ)) =
          Real.log (firstReturn src tgt a ω ε : ℝ) := by
        field_simp
      linarith
  · intro b hb
    have hDlt := (tendsto_order.1 hDead).2 b hb
    filter_upwards [hmem, hDlt, eventually_le_firstReturn chart ha hωpos 1] with ε hε hD hR
    have hL := hlogpos ε hε
    have hmpos : (0 : ℝ) < (firstReturn src tgt a ω ε : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hR
    have hle : (firstReturn src tgt a ω ε : ℝ) ≤ (universalDeadline src tgt a ε : ℝ) := by
      exact_mod_cast firstReturn_le_universalDeadline chart ha hε.1 ω
    have hlog := Real.log_le_log hmpos hle
    have : Real.log (firstReturn src tgt a ω ε : ℝ) / Real.log (1 / ε) ≤
        Real.log (universalDeadline src tgt a ε : ℝ) / Real.log (1 / ε) := by
      gcongr
    linarith

/-! ## The rank-zero stationary boundary -/

/-- At rank zero every clock is already a return, so one is a universal deadline. -/
theorem isUniversalDeadline_one_of_rank_zero {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (h : T.rank = 0) (a : E → ℝ) (ε : ℝ) :
    IsUniversalDeadline src tgt a ε 1 := by
  intro x
  refine ⟨1, one_pos, le_rfl, ?_⟩
  rw [graphChordEnergy_eq_zero_of_rank_zero chart h a _]
  positivity

/-- **The rank-zero deadline.**  A stationary coherence graph returns at the first clock. -/
theorem universalDeadline_eq_one_of_rank_zero {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (h : T.rank = 0) (a : E → ℝ) (ε : ℝ) :
    universalDeadline src tgt a ε = 1 := by
  refine le_antisymm (universalDeadline_le (isUniversalDeadline_one_of_rank_zero chart h a ε))
    (Nat.one_le_iff_ne_zero.2 ?_)
  intro hzero
  have hne : ∃ M, IsUniversalDeadline src tgt a ε M :=
    ⟨1, isUniversalDeadline_one_of_rank_zero chart h a ε⟩
  have hmem : IsUniversalDeadline src tgt a ε (universalDeadline src tgt a ε) := Nat.sInf_mem hne
  rw [hzero] at hmem
  obtain ⟨n, hn, hn0, -⟩ := hmem 0
  omega

/-- **The rank-zero first return.**  Every spectrum recurs at clock one. -/
theorem firstReturn_eq_one_of_rank_zero {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (h : T.rank = 0) (a : E → ℝ) (ω : V → UnitAddCircle)
    (ε : ℝ) : firstReturn src tgt a ω ε = 1 := by
  have hone : graphChordEnergy src tgt a ((1 : ℤ) • ω) ≤ ε ^ 2 := by
    rw [graphChordEnergy_eq_zero_of_rank_zero chart h a _]
    positivity
  refine le_antisymm (firstReturn_le one_pos (by exact_mod_cast hone)) ?_
  have hmem : ∃ n : ℕ, 0 < n ∧ graphChordEnergy src tgt a ((n : ℤ) • ω) ≤ ε ^ 2 :=
    ⟨1, one_pos, by exact_mod_cast hone⟩
  exact (firstReturn_spec hmem).1

end

end RHTower
