import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewRecurrence
import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrenceCapstoneLaw

/-!
# Countable projective-future universality

For a countable pure-point spectrum, global phase is removed by anchoring
all energies at one level.  Maximal projective freedom is then exactly the
absence of finite integer relations among the anchored gaps.  The compact
relation-hull theorem consequently identifies the closure of the future
phase orbit with the full product torus.

Combined with countable trace-class saturation, every countable real
spectrum lies arbitrarily close to a self-adjoint Hamiltonian whose phase
orbit after every starting time is dense in its entire projective torus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Energy gaps relative to one projective anchor. -/
def anchoredProjectiveGap
    {I : Type*} (energy : I → ℝ) (anchor : I)
    (j : {i : I // i ≠ anchor}) : ℝ :=
  energy j.1 - energy anchor

/-- Maximal projective freedom is equivalent to absence of every finite
integer relation among gaps from any chosen anchor. -/
theorem screwRelationLattice_anchoredProjectiveGap_eq_zero
    {I : Type*} (energy : I → ℝ) (anchor : I)
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy) :
    screwRelationLattice (anchoredProjectiveGap energy anchor) = {0} := by
  classical
  ext n
  constructor
  · intro hn
    let e : {i : I // i ≠ anchor} ↪ I :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let raw : I →₀ ℤ := n.embDomain e
    let q : ℤ := integerCharacterCharge _ n
    let kraw : I →₀ ℤ :=
      raw + Finsupp.single anchor (-q)
    have hcharge : integerCharacterCharge I kraw = 0 := by
      have hraw : integerCharacterCharge I raw = q := by
        change raw.sum (fun _ m => m) = q
        rw [Finsupp.sum_embDomain]
        rfl
      have hsingle : integerCharacterCharge I
          (Finsupp.single anchor (-q)) = -q := by
        change (Finsupp.single anchor (-q)).sum
          (fun _ m => m) = -q
        rw [Finsupp.sum_single_index]
        simp
      change integerCharacterCharge I
        (raw + Finsupp.single anchor (-q)) = 0
      rw [map_add, hraw, hsingle, add_neg_cancel]
    let k : ProjectiveCharacter I := ⟨kraw, hcharge⟩
    have hdetune :
        infiniteTorusCharacterDetuning kraw energy = 0 := by
      have hn' : infiniteTorusCharacterDetuning n
          (anchoredProjectiveGap energy anchor) = 0 := hn
      have hraw : infiniteTorusCharacterDetuning raw energy =
          n.sum (fun j m => (m : ℝ) * energy j.1) := by
        unfold infiniteTorusCharacterDetuning raw
        rw [Finsupp.sum_embDomain]
        simp [e]
      have hsingle : infiniteTorusCharacterDetuning
          (Finsupp.single anchor (-q)) energy =
          (-q : ℤ) * energy anchor := by
        unfold infiniteTorusCharacterDetuning
        rw [Finsupp.sum_single_index (by simp)]
      have hadd : infiniteTorusCharacterDetuning kraw energy =
          infiniteTorusCharacterDetuning raw energy +
            infiniteTorusCharacterDetuning
              (Finsupp.single anchor (-q)) energy := by
        unfold infiniteTorusCharacterDetuning kraw
        rw [Finsupp.sum_add_index]
        · intro i hi
          simp
        · intro i hi a b
          push_cast
          ring
      have hq : (q : ℝ) =
          n.sum (fun _ m => (m : ℝ)) := by
        unfold q integerCharacterCharge
        norm_cast
      have hgap :
          n.sum (fun j m => (m : ℝ) *
              anchoredProjectiveGap energy anchor j) =
            n.sum (fun j m => (m : ℝ) * energy j.1) -
              (q : ℝ) * energy anchor := by
        calc
          n.sum (fun j m => (m : ℝ) *
              anchoredProjectiveGap energy anchor j) =
              n.sum (fun j m =>
                (m : ℝ) * energy j.1 -
                  (m : ℝ) * energy anchor) := by
            apply Finsupp.sum_congr
            intro j hj
            simp [anchoredProjectiveGap]
            ring
          _ = n.sum (fun j m => (m : ℝ) * energy j.1) -
              n.sum (fun _ m => (m : ℝ) * energy anchor) :=
            Finsupp.sum_sub
          _ = n.sum (fun j m => (m : ℝ) * energy j.1) -
              (n.sum (fun _ m => (m : ℝ))) *
                energy anchor := by
            rw [Finsupp.sum_mul]
          _ = _ := by rw [← hq]
      rw [hadd, hraw, hsingle]
      have hn'' : n.sum (fun j m => (m : ℝ) *
          anchoredProjectiveGap energy anchor j) = 0 := hn'
      rw [hgap] at hn''
      push_cast
      linarith
    have hkzero : k = 0 := by
      apply hmax k
      exact hdetune
    change n = 0
    apply Finsupp.ext
    intro j
    have hval := congrArg Subtype.val hkzero
    have hj := DFunLike.congr_fun hval (e j)
    have hrawj : raw (e j) = n j :=
      Finsupp.embDomain_apply_self e n j
    have hsinglej :
        Finsupp.single anchor (-q) (e j) = 0 := by
      simp [e, j.property]
    change (raw + Finsupp.single anchor (-q)) (e j) = 0 at hj
    simp only [Finsupp.add_apply, hrawj, hsinglej, add_zero] at hj
    exact hj
  · intro hn
    rw [Set.mem_singleton_iff] at hn
    subst n
    simp [screwRelationLattice, infiniteTorusCharacterDetuning]

/-- A maximally projective countable spectrum has the full anchored product
torus as its compact phase hull. -/
theorem screwHull_anchoredProjectiveGap_eq_univ
    {I : Type*} [Countable I]
    (energy : I → ℝ) (anchor : I)
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy) :
    screwHull (anchoredProjectiveGap energy anchor) = Set.univ := by
  rw [screwHull_eq_screwAnnihilator]
  unfold screwAnnihilator
  rw [screwRelationLattice_anchoredProjectiveGap_eq_zero
    energy anchor hmax]
  ext z
  simp [infiniteTorusFourier]

/-- Every forward tail of a maximally projective countable phase orbit is
dense in the full anchored product torus. -/
theorem
    closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
    {I : Type*} [Countable I]
    (energy : I → ℝ) (anchor : I)
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy)
    (T : ℝ) :
    closure
        (screwPhase (anchoredProjectiveGap energy anchor) '' Set.Ici T) =
      Set.univ := by
  rw [closure_screwPhase_image_Ici,
    screwHull_anchoredProjectiveGap_eq_univ energy anchor hmax]

/-- **Arbitrarily weak full-projective-future law.**  Every nonempty
countable real spectrum admits an arbitrarily operator-norm-small
domain-preserving self-adjoint Schatten-1 perturbation whose future phase
orbit, after every starting time and relative to every anchor, is dense in
the entire countable projective product torus. -/
theorem exists_arbitrarilyWeak_fullProjectiveFuture
    {I : Type*} [Countable I] [Nonempty I]
    (energy : I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      IsSelfAdjoint
        (RHTower.maximalRealDiagonal (fun i => energy i + w i)) ∧
      ∀ (anchor : I) (T : ℝ),
        closure
            (screwPhase
              (anchoredProjectiveGap
                (fun i => energy i + w i) anchor) '' Set.Ici T) =
          Set.univ := by
  obtain ⟨w, hw, _, hnorm, _, htrace, hdomain, hself, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  refine ⟨w, hw, hnorm, htrace, hdomain, hself, ?_⟩
  intro anchor T
  exact
    closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
      (fun i => energy i + w i) anchor hmax T

/-- **Separable full-projective-future law.**  For every pair of nonempty
countable spectra, the full-projective-future perturbation can be forced to
be one separable interaction `w(i,j)=u(i)v(j)` with absolutely summable
factors. -/
theorem exists_arbitrarilyWeak_separable_fullProjectiveFuture
    {A B : Type*} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (u : A → ℝ) (v : B → ℝ),
      ∃ hw : Summable (fun x : A × B => |u x.1 * v x.2|),
        Summable (fun i => |u i|) ∧
        Summable (fun j => |v j|) ∧
        ‖realSummableDiagonalOperator
          (fun x : A × B => u x.1 * v x.2) hw‖ < δ ∧
        RHTower.MemSchattenClass 1
          (realSummableDiagonalOperator
            (fun x : A × B => u x.1 * v x.2) hw) ∧
        RHTower.maximalRealDiagonalDomain
            (fun x : A × B =>
              left x.1 + right x.2 + u x.1 * v x.2) =
          RHTower.maximalRealDiagonalDomain
            (fun x : A × B => left x.1 + right x.2) ∧
        ∀ (anchor : A × B) (T : ℝ),
          closure
              (screwPhase
                (anchoredProjectiveGap
                  (fun x : A × B =>
                    left x.1 + right x.2 + u x.1 * v x.2)
                  anchor) '' Set.Ici T) =
            Set.univ := by
  obtain ⟨u, v, hw, hu, hv, _, hnorm, _, htrace, hdomain,
      _, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassSeparableHamiltonian_saturating
      left right δ hδ
  refine ⟨u, v, hw, hu, hv, hnorm, htrace, hdomain, ?_⟩
  intro anchor T
  exact
    closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
      (fun x : A × B =>
        left x.1 + right x.2 + u x.1 * v x.2)
      anchor hmax T

/-- A maximally projective spectrum on an infinite carrier has finite
windows of every temporal rank.  This gives a precise finite-resolution
meaning to infinite projective temporal dimension. -/
theorem
    FinitelySupportedMaximallyProjectiveEnergy.unboundedFiniteWindowTemporalRank
    {I : Type*} [Infinite I] {energy : I → ℝ}
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy) :
    ∀ n : ℕ, ∃ e : Fin (n + 1) ↪ I,
      projectiveTemporalRank (energy ∘ e) = n := by
  intro n
  let e : Fin (n + 1) ↪ I :=
    Fin.valEmbedding.trans (Infinite.natEmbedding I)
  have hfinite : MaximallyProjectiveEnergy (energy ∘ e) :=
    (finitelySupportedMaximallyProjectiveEnergy_iff
      (energy ∘ e)).1 (hmax.comp_embedding e)
  exact ⟨e, projectiveTemporalRank_eq hfinite⟩

/-- **Arbitrarily weak infinite-temporal-rank law.**  Every countably
infinite real spectrum lies arbitrarily close to a domain-preserving
self-adjoint Schatten-1 perturbation whose finite windows realize every
temporal rank and whose every forward projective phase orbit is dense in
the full anchored product torus. -/
theorem exists_arbitrarilyWeak_infiniteTemporalRank
    {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      IsSelfAdjoint
        (RHTower.maximalRealDiagonal (fun i => energy i + w i)) ∧
      (∀ n : ℕ, ∃ e : Fin (n + 1) ↪ I,
        projectiveTemporalRank
          ((fun i => energy i + w i) ∘ e) = n) ∧
      ∀ (anchor : I) (T : ℝ),
        closure
            (screwPhase
              (anchoredProjectiveGap
                (fun i => energy i + w i) anchor) '' Set.Ici T) =
          Set.univ := by
  obtain ⟨w, hw, _, hnorm, _, htrace, hdomain, hself, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  refine ⟨w, hw, hnorm, htrace, hdomain, hself,
    hmax.unboundedFiniteWindowTemporalRank, ?_⟩
  intro anchor T
  exact
    closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
      (fun i => energy i + w i) anchor hmax T

/-- On an infinite maximally projective spectrum, zero is the only exact
global projective return time.  Approximate recurrence survives, but exact
simultaneous phase closure does not. -/
theorem
    FinitelySupportedMaximallyProjectiveEnergy.no_nonzeroExactProjectiveReturn
    {I : Type*} [Infinite I]
    {energy : I → ℝ}
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy)
    (anchor : I) :
    ∀ t : ℝ,
      screwPhase (anchoredProjectiveGap energy anchor) t = 0 → t = 0 := by
  classical
  intro t ht
  by_contra ht0
  let J := {i : I // i ≠ anchor}
  have hJinf : ({i : I | i ≠ anchor} : Set I).Infinite := by
    have hset : ({i : I | i ≠ anchor} : Set I) = {anchor}ᶜ := by
      ext i
      simp
    rw [hset]
    exact Set.Finite.infinite_compl (Set.finite_singleton anchor)
  haveI : Infinite J := hJinf.to_subtype
  obtain ⟨j, k, hjk⟩ := exists_pair_ne J
  have hjphase := congrFun ht j
  have hkphase := congrFun ht k
  change (((anchoredProjectiveGap energy anchor j * t /
    (2 * Real.pi) : ℝ) : UnitAddCircle) = 0) at hjphase
  change (((anchoredProjectiveGap energy anchor k * t /
    (2 * Real.pi) : ℝ) : UnitAddCircle) = 0) at hkphase
  obtain ⟨m, hm⟩ :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hjphase
  obtain ⟨n, hn⟩ :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hkphase
  have hm' : (m : ℝ) = anchoredProjectiveGap energy anchor j * t /
      (2 * Real.pi) := by simpa using hm
  have hn' : (n : ℝ) = anchoredProjectiveGap energy anchor k * t /
      (2 * Real.pi) := by simpa using hn
  let r : J →₀ ℤ :=
    Finsupp.single j n + Finsupp.single k (-m)
  have hrrel : r ∈ screwRelationLattice
      (anchoredProjectiveGap energy anchor) := by
    change infiniteTorusCharacterDetuning r
      (anchoredProjectiveGap energy anchor) = 0
    change (Finsupp.single j n + Finsupp.single k (-m)).sum
      (fun i q => (q : ℝ) * anchoredProjectiveGap energy anchor i) = 0
    rw [Finsupp.sum_add_index]
    · rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
      push_cast
      field_simp [Real.pi_ne_zero] at hm' hn' ⊢
      have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) Real.pi_ne_zero
      have hnMul := congrArg
        (fun x : ℝ => anchoredProjectiveGap energy anchor j * x) hn'
      have hmMul := congrArg
        (fun x : ℝ => x * anchoredProjectiveGap energy anchor k) hm'
      have hprod :
          (2 * Real.pi) *
              (anchoredProjectiveGap energy anchor j * (n : ℝ) -
                (m : ℝ) * anchoredProjectiveGap energy anchor k) = 0 := by
        calc
          _ = anchoredProjectiveGap energy anchor j *
                ((2 * Real.pi) * (n : ℝ)) -
              ((m : ℝ) * 2 * Real.pi) *
                anchoredProjectiveGap energy anchor k := by ring
          _ = anchoredProjectiveGap energy anchor j *
                (t * anchoredProjectiveGap energy anchor k) -
              (anchoredProjectiveGap energy anchor j * t) *
                anchoredProjectiveGap energy anchor k := by
              exact congrArg₂ (· - ·) hnMul hmMul
          _ = 0 := by ring
      have hrel := (mul_eq_zero.mp hprod).resolve_left htwoPi
      linarith
      all_goals norm_num
    · intro i hi
      simp only [Int.cast_zero, zero_mul]
    · intro i hi a b
      push_cast
      ring
  have hrzero : r = 0 := by
    have hz := screwRelationLattice_anchoredProjectiveGap_eq_zero
      energy anchor hmax
    rw [hz] at hrrel
    simpa using hrrel
  have hrj := DFunLike.congr_fun hrzero j
  have hrk := DFunLike.congr_fun hrzero k
  have hnzero : n = 0 := by
    simpa [r, hjk] using hrj
  have hmzero : m = 0 := by
    have hkj : k ≠ j := Ne.symm hjk
    simpa [r, hkj] using hrk
  have hgapjzero : anchoredProjectiveGap energy anchor j = 0 := by
    rw [hmzero] at hm'
    simp only [Int.cast_zero] at hm'
    field_simp [Real.pi_ne_zero] at hm'
    norm_num at hm'
    exact hm'.resolve_right ht0
  let onej : J →₀ ℤ := Finsupp.single j 1
  have honejrel : onej ∈ screwRelationLattice
      (anchoredProjectiveGap energy anchor) := by
    change infiniteTorusCharacterDetuning onej
      (anchoredProjectiveGap energy anchor) = 0
    simp [onej, infiniteTorusCharacterDetuning, hgapjzero]
  have honejzero : onej = 0 := by
    have hz := screwRelationLattice_anchoredProjectiveGap_eq_zero
      energy anchor hmax
    rw [hz] at honejrel
    simpa using honejrel
  have := DFunLike.congr_fun honejzero j
  simp [onej] at this

/-- **Complete saturated recurrence law.**  A countably infinite maximally
projective spectrum has no nonzero exact global projective return, but every
future tail is dense in the full projective torus.  Every strictly positive
summable phase-defect probe has lower limit zero, upper limit its absolute
maximum, and crosses every intermediate level within a uniformly bounded
waiting window from every starting time. -/
theorem completeSaturatedProjectiveRecurrenceLaw
    {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ)
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy)
    (anchor : I)
    (a : {i : I // i ≠ anchor} → ℝ)
    (hpos : ∀ i, 0 < a i) (hsum : Summable a) :
    screwRelationLattice (anchoredProjectiveGap energy anchor) = {0} ∧
    screwHull (anchoredProjectiveGap energy anchor) = Set.univ ∧
    (∀ T : ℝ,
      closure
          (screwPhase (anchoredProjectiveGap energy anchor) '' Set.Ici T) =
        Set.univ) ∧
    (∀ t : ℝ,
      screwPhase (anchoredProjectiveGap energy anchor) t = 0 → t = 0) ∧
    liminf (screwSeries a (anchoredProjectiveGap energy anchor)) atTop = 0 ∧
    limsup (screwSeries a (anchoredProjectiveGap energy anchor)) atTop =
      2 * ∑' i, a i ∧
    (∀ y : ℝ, 0 ≤ y → y ≤ 2 * ∑' i, a i →
      ∀ ε : ℝ, 0 < ε →
        ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
          ∃ t ∈ Set.Icc tau (tau + L),
            |screwSeries a (anchoredProjectiveGap energy anchor) t - y| < ε) ∧
    ∀ y : ℝ, 0 < y → y < 2 * ∑' i, a i →
      ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
        ∃ t ∈ Set.Icc tau (tau + L),
          screwSeries a (anchoredProjectiveGap energy anchor) t = y := by
  have hrel := screwRelationLattice_anchoredProjectiveGap_eq_zero
    energy anchor hmax
  have hhull := screwHull_anchoredProjectiveGap_eq_univ
    energy anchor hmax
  have htail :=
    closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
      energy anchor hmax
  have hnoret := hmax.no_nonzeroExactProjectiveReturn anchor
  have hpos' : ∀ i, 0 ≤ a i := fun i => (hpos i).le
  have hliminf := screwSeries_liminf_eq_zero
    (omega := anchoredProjectiveGap energy anchor) hpos' hsum
  have htrivial :
      ∀ n : {i : I // i ≠ anchor} →₀ ℤ,
        n ∈ screwRelationLattice (anchoredProjectiveGap energy anchor) → n = 0 := by
    intro n hn
    rw [hrel] at hn
    simpa using hn
  have hparity := parity_of_screwRelationLattice_trivial htrivial
  have hmaxval :
      screwHullMax a (anchoredProjectiveGap energy anchor) =
        2 * ∑' i, a i :=
    (screwHullMax_eq_two_mul_tsum_iff hpos hsum).2 hparity
  have hlimsup :
      limsup (screwSeries a (anchoredProjectiveGap energy anchor)) atTop =
        2 * ∑' i, a i := by
    rw [screwSeries_limsup_eq_screwHullMax hpos' hsum, hmaxval]
  refine ⟨hrel, hhull, htail, hnoret, hliminf, hlimsup, ?_, ?_⟩
  · intro y hy0 hymax ε hε
    apply exists_window_screwSeries_near hpos' hsum
    · rw [hmaxval]
      exact ⟨hy0, hymax⟩
    · exact hε
  · intro y hy0 hymax
    apply exists_window_screwSeries_eq hpos' hsum hy0
    rwa [hmaxval]

/-- **Arbitrarily weak complete projective-recurrence law.**  Every
countably infinite real pure-point Hamiltonian admits an arbitrarily
operator-norm-small, domain-preserving, self-adjoint Schatten-1 diagonal
perturbation with unbounded finite-window temporal rank.  Relative to every
anchor, its only exact global projective return is at time zero, every future
tail is dense in the full projective torus, and every strictly positive
summable defect probe recurrently sweeps its entire allowed interval. -/
theorem exists_arbitrarilyWeak_completeProjectiveRecurrenceLaw
    {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      IsSelfAdjoint
        (RHTower.maximalRealDiagonal (fun i => energy i + w i)) ∧
      (∀ n : ℕ, ∃ e : Fin (n + 1) ↪ I,
        projectiveTemporalRank
          ((fun i => energy i + w i) ∘ e) = n) ∧
      ∀ anchor : I,
        (∀ T : ℝ,
          closure
              (screwPhase
                (anchoredProjectiveGap
                  (fun i => energy i + w i) anchor) '' Set.Ici T) =
            Set.univ) ∧
        (∀ t : ℝ,
          screwPhase
              (anchoredProjectiveGap
                (fun i => energy i + w i) anchor) t = 0 →
            t = 0) ∧
        ∀ (a : {i : I // i ≠ anchor} → ℝ),
          (∀ i, 0 < a i) → Summable a →
          liminf
              (screwSeries a
                (anchoredProjectiveGap
                  (fun i => energy i + w i) anchor)) atTop = 0 ∧
          limsup
              (screwSeries a
                (anchoredProjectiveGap
                  (fun i => energy i + w i) anchor)) atTop =
            2 * ∑' i, a i ∧
          (∀ y : ℝ, 0 ≤ y → y ≤ 2 * ∑' i, a i →
            ∀ ε : ℝ, 0 < ε →
              ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
                ∃ t ∈ Set.Icc tau (tau + L),
                  |screwSeries a
                      (anchoredProjectiveGap
                        (fun i => energy i + w i) anchor) t - y| < ε) ∧
          ∀ y : ℝ, 0 < y → y < 2 * ∑' i, a i →
            ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ,
              ∃ t ∈ Set.Icc tau (tau + L),
                screwSeries a
                    (anchoredProjectiveGap
                      (fun i => energy i + w i) anchor) t = y := by
  obtain ⟨w, hw, _, hnorm, _, htrace, hdomain, hself, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  refine ⟨w, hw, hnorm, htrace, hdomain, hself,
    hmax.unboundedFiniteWindowTemporalRank, ?_⟩
  intro anchor
  refine ⟨?_, hmax.no_nonzeroExactProjectiveReturn anchor, ?_⟩
  · intro T
    exact
      closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
        (fun i => energy i + w i) anchor hmax T
  · intro a hpos hsum
    have hcomplete := completeSaturatedProjectiveRecurrenceLaw
      (fun i => energy i + w i) hmax anchor a hpos hsum
    exact ⟨hcomplete.2.2.2.2.1,
      hcomplete.2.2.2.2.2.1,
      hcomplete.2.2.2.2.2.2.1,
      hcomplete.2.2.2.2.2.2.2⟩

end

end GaloisForLFunctions.HTGeometry
