import GaloisForLFunctions.HTGeometry.CompletedTimeSmallBall
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Exact anchored projective recurrence density

For a rationally independent finite frequency packet, the anchored operator-chord
return target has exact Haar measure
`(2 * arcsin (ε / 2) / π) ^ d`.  Its boundary is Haar-null, so weak spectral
phase equidistribution upgrades to an exact asymptotic completed-time density.

The module also isolates the sharp exact-return threshold. Two or more relative
frequencies have no nonzero common return; equivalently, a maximally projective
spectrum needs at least three energy levels. A two-level spectrum has one relative
circle and is periodic, so no stronger unconditional statement is possible.
-/

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_fourier_one_coe_sub_one_eq
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    ‖fourier 1 (x : UnitAddCircle) - 1‖ =
      2 * Real.sin (Real.pi * |x|) := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ) =
        Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * |x|) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have habs : |x| ≤ 1 / 2 := (abs_le).2 hx
      nlinarith [Real.pi_pos]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hsabs : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * |x|) := by
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
        have := hx.2
        nlinarith [Real.pi_pos])
    · have hsinneg : Real.sin (Real.pi * x) ≤ 0 := by
        rw [← neg_nonneg, ← Real.sin_neg]
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · nlinarith [Real.pi_pos]
        · have := hx.1
          nlinarith [Real.pi_pos]
      rw [abs_of_nonpos hsinneg, ← Real.sin_neg]
      congr 2
      rw [abs_of_nonpos hx0]
      ring
  rw [hsabs]

theorem chord_le_iff_abs_le_arcsin
    {x ε : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) :
    ‖fourier 1 (x : UnitAddCircle) - 1‖ ≤ ε ↔
      |x| ≤ Real.arcsin (ε / 2) / Real.pi := by
  rw [norm_fourier_one_coe_sub_one_eq hx]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hhalf : ε / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  have hxabs : |x| ≤ 1 / 2 := (abs_le).2 hx
  have hangle : Real.pi * |x| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [abs_nonneg x, Real.pi_pos]
    · nlinarith
  constructor
  · intro h
    have hsin : Real.sin (Real.pi * |x|) ≤ ε / 2 := by linarith
    have harc : Real.pi * |x| ≤ Real.arcsin (ε / 2) :=
      (Real.le_arcsin_iff_sin_le hangle hhalf).2 hsin
    exact (le_div_iff₀ hπ).2 (by simpa [mul_comm] using harc)
  · intro h
    have harc : Real.pi * |x| ≤ Real.arcsin (ε / 2) := by
      have := (le_div_iff₀ hπ).mp h
      simpa [mul_comm] using this
    have hsin : Real.sin (Real.pi * |x|) ≤ ε / 2 :=
      (Real.le_arcsin_iff_sin_le hangle hhalf).1 harc
    linarith

/-- Closed one-circle anchored chord target. -/
def circleAnchoredReturnTarget (ε : ℝ) : Set UnitAddCircle :=
  {z | ‖fourier 1 z - 1‖ ≤ ε}

/-- Strict one-circle anchored chord target. -/
def circleStrictAnchoredReturnTarget (ε : ℝ) : Set UnitAddCircle :=
  {z | ‖fourier 1 z - 1‖ < ε}

theorem isClosed_circleAnchoredReturnTarget (ε : ℝ) :
    IsClosed (circleAnchoredReturnTarget ε) := by
  exact isClosed_le (by fun_prop) continuous_const

theorem isOpen_circleStrictAnchoredReturnTarget (ε : ℝ) :
    IsOpen (circleStrictAnchoredReturnTarget ε) := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem preimage_mk_circleAnchoredReturnTarget_inter
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε < 2) :
    (((↑) : ℝ → UnitAddCircle) ⁻¹' circleAnchoredReturnTarget ε) ∩
        Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) =
      Icc (-(Real.arcsin (ε / 2) / Real.pi))
        (Real.arcsin (ε / 2) / Real.pi) := by
  have hr0 : 0 ≤ Real.arcsin (ε / 2) / Real.pi := by
    exact div_nonneg (Real.arcsin_nonneg.mpr (by linarith)) Real.pi_pos.le
  have hrlt : Real.arcsin (ε / 2) / Real.pi < 1 / 2 := by
    have ha := Real.arcsin_lt_pi_div_two.mpr (by linarith : ε / 2 < 1)
    exact (div_lt_iff₀ Real.pi_pos).2 (by nlinarith [Real.pi_pos])
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, Set.mem_Icc,
    circleAnchoredReturnTarget, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxchord, hxlo, hxhi⟩
    have hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      constructor <;> norm_num at hxhi ⊢ <;> linarith
    have habs := (chord_le_iff_abs_le_arcsin hx hε0 hε2.le).mp hxchord
    exact (abs_le.mp habs)
  · rintro ⟨hxlo, hxhi⟩
    have hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      constructor <;> linarith
    refine ⟨(chord_le_iff_abs_le_arcsin hx hε0 hε2.le).mpr ?_, by linarith, ?_⟩
    · exact abs_le.mpr ⟨hxlo, hxhi⟩
    · norm_num
      linarith

theorem preimage_mk_circleStrictAnchoredReturnTarget_inter
    {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    (((↑) : ℝ → UnitAddCircle) ⁻¹' circleStrictAnchoredReturnTarget ε) ∩
        Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) =
      Ioo (-(Real.arcsin (ε / 2) / Real.pi))
        (Real.arcsin (ε / 2) / Real.pi) := by
  have hr0 : 0 < Real.arcsin (ε / 2) / Real.pi := by
    exact div_pos (Real.arcsin_pos.mpr (by linarith)) Real.pi_pos
  have hrlt : Real.arcsin (ε / 2) / Real.pi < 1 / 2 := by
    have ha := Real.arcsin_lt_pi_div_two.mpr (by linarith : ε / 2 < 1)
    exact (div_lt_iff₀ Real.pi_pos).2 (by nlinarith [Real.pi_pos])
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, Set.mem_Ioo,
    circleStrictAnchoredReturnTarget, Set.mem_setOf_eq]
  have hxchar :
      ∀ hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        ‖fourier 1 (x : UnitAddCircle) - 1‖ < ε ↔
          |x| < Real.arcsin (ε / 2) / Real.pi := by
    intro hx
    rw [norm_fourier_one_coe_sub_one_eq hx]
    have hhalf : ε / 2 ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith
    have hangle : Real.pi * |x| ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      have habs : |x| ≤ 1 / 2 := (abs_le).2 hx
      constructor
      · nlinarith [abs_nonneg x, Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [show 2 * Real.sin (Real.pi * |x|) < ε ↔
        Real.sin (Real.pi * |x|) < ε / 2 by
          constructor <;> intro h <;> linarith]
    rw [← Real.lt_arcsin_iff_sin_lt hangle hhalf]
    constructor
    · intro h
      exact (lt_div_iff₀ Real.pi_pos).2 (by simpa [mul_comm] using h)
    · intro h
      have := (lt_div_iff₀ Real.pi_pos).mp h
      simpa [mul_comm] using this
  constructor
  · rintro ⟨hxchord, hxlo, hxhi⟩
    have hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      constructor <;> norm_num at hxhi ⊢ <;> linarith
    exact abs_lt.mp ((hxchar hx).mp hxchord)
  · rintro ⟨hxlo, hxhi⟩
    have hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      constructor <;> linarith
    refine ⟨(hxchar hx).mpr (abs_lt.mpr ⟨hxlo, hxhi⟩), by linarith, ?_⟩
    norm_num
    linarith

theorem haarAddCircle_circleAnchoredReturnTarget
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε < 2) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (circleAnchoredReturnTarget ε) =
      ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) := by
  have hmp := AddCircle.measurePreserving_mk (T := 1) (t := -(1 / 2))
  have hpre := hmp.measure_preimage
    (isClosed_circleAnchoredReturnTarget ε).measurableSet.nullMeasurableSet
  rw [← volume_eq_haarAddCircle, ← hpre,
    Measure.restrict_apply
      (measurableSet_preimage (AddCircle.measurable_mk' (a := (1 : ℝ)))
        (isClosed_circleAnchoredReturnTarget ε).measurableSet),
    preimage_mk_circleAnchoredReturnTarget_inter hε0 hε2, Real.volume_Icc]
  congr 1
  ring

theorem haarAddCircle_circleStrictAnchoredReturnTarget
    {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (circleStrictAnchoredReturnTarget ε) =
      ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) := by
  have hmp := AddCircle.measurePreserving_mk (T := 1) (t := -(1 / 2))
  have hpre := hmp.measure_preimage
    (isOpen_circleStrictAnchoredReturnTarget ε).measurableSet.nullMeasurableSet
  rw [← volume_eq_haarAddCircle, ← hpre,
    Measure.restrict_apply
      (measurableSet_preimage (AddCircle.measurable_mk' (a := (1 : ℝ)))
        (isOpen_circleStrictAnchoredReturnTarget ε).measurableSet),
    preimage_mk_circleStrictAnchoredReturnTarget_inter hε0 hε2, Real.volume_Ioo]
  congr 1
  ring

/-- Closed anchored operator-chord target on a finite relative phase torus. -/
def anchoredProjectiveReturnTarget {d : Type*}
    (ε : ℝ) : Set (UnitAddTorus d) :=
  {x | ∀ i, ‖fourier 1 (x i) - 1‖ ≤ ε}

/-- Strict anchored operator-chord target on a finite relative phase torus. -/
def strictAnchoredProjectiveReturnTarget {d : Type*}
    (ε : ℝ) : Set (UnitAddTorus d) :=
  {x | ∀ i, ‖fourier 1 (x i) - 1‖ < ε}

theorem anchoredProjectiveReturnTarget_eq_pi {d : Type*} (ε : ℝ) :
    anchoredProjectiveReturnTarget (d := d) ε =
      Set.univ.pi (fun _ => circleAnchoredReturnTarget ε) := by
  ext x
  simp [anchoredProjectiveReturnTarget, circleAnchoredReturnTarget]

theorem strictAnchoredProjectiveReturnTarget_eq_pi {d : Type*} (ε : ℝ) :
    strictAnchoredProjectiveReturnTarget (d := d) ε =
      Set.univ.pi (fun _ => circleStrictAnchoredReturnTarget ε) := by
  ext x
  simp [strictAnchoredProjectiveReturnTarget, circleStrictAnchoredReturnTarget]

theorem isClosed_anchoredProjectiveReturnTarget
    {d : Type*} (ε : ℝ) :
    IsClosed (anchoredProjectiveReturnTarget (d := d) ε) := by
  rw [anchoredProjectiveReturnTarget_eq_pi]
  rw [Set.univ_pi_eq_iInter]
  exact isClosed_iInter fun i =>
    (isClosed_circleAnchoredReturnTarget ε).preimage (continuous_apply i)

theorem isOpen_strictAnchoredProjectiveReturnTarget
    {d : Type*} [Finite d] (ε : ℝ) :
    IsOpen (strictAnchoredProjectiveReturnTarget (d := d) ε) := by
  rw [strictAnchoredProjectiveReturnTarget_eq_pi]
  rw [Set.univ_pi_eq_iInter]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_circleStrictAnchoredReturnTarget ε).preimage (continuous_apply i)

theorem strictAnchoredProjectiveReturnTarget_subset
    {d : Type*} (ε : ℝ) :
    strictAnchoredProjectiveReturnTarget (d := d) ε ⊆
      anchoredProjectiveReturnTarget (d := d) ε := by
  intro x hx i
  exact (hx i).le

theorem finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget
    {d : Type*} [Fintype d] {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε < 2) :
    (finiteTorusHaarProbabilityMeasure d : Measure (UnitAddTorus d))
        (anchoredProjectiveReturnTarget ε) =
      ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^ Fintype.card d := by
  show (Measure.pi fun _ => AddCircle.haarAddCircle)
      (anchoredProjectiveReturnTarget ε) = _
  rw [anchoredProjectiveReturnTarget_eq_pi, Measure.pi_pi]
  rw [Finset.prod_congr rfl fun _i (_ : _ ∈ Finset.univ) =>
    haarAddCircle_circleAnchoredReturnTarget hε0 hε2]
  rw [Finset.prod_const, Finset.card_univ]

theorem finiteTorusHaarProbabilityMeasure_strictAnchoredProjectiveReturnTarget
    {d : Type*} [Fintype d] {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    (finiteTorusHaarProbabilityMeasure d : Measure (UnitAddTorus d))
        (strictAnchoredProjectiveReturnTarget ε) =
      ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^ Fintype.card d := by
  show (Measure.pi fun _ => AddCircle.haarAddCircle)
      (strictAnchoredProjectiveReturnTarget ε) = _
  rw [strictAnchoredProjectiveReturnTarget_eq_pi, Measure.pi_pi]
  rw [Finset.prod_congr rfl fun _i (_ : _ ∈ Finset.univ) =>
    haarAddCircle_circleStrictAnchoredReturnTarget hε0 hε2]
  rw [Finset.prod_const, Finset.card_univ]

theorem finiteTorusHaarProbabilityMeasure_frontier_anchoredProjectiveReturnTarget
    {d : Type*} [Fintype d] {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    (finiteTorusHaarProbabilityMeasure d : Measure (UnitAddTorus d))
        (frontier (anchoredProjectiveReturnTarget ε)) = 0 := by
  let μ : Measure (UnitAddTorus d) := finiteTorusHaarProbabilityMeasure d
  let A : Set (UnitAddTorus d) := anchoredProjectiveReturnTarget ε
  let U : Set (UnitAddTorus d) := strictAnchoredProjectiveReturnTarget ε
  have hUA : U ⊆ A := strictAnchoredProjectiveReturnTarget_subset ε
  have hUopen : IsOpen U := isOpen_strictAnchoredProjectiveReturnTarget ε
  have hAclosed : IsClosed A := isClosed_anchoredProjectiveReturnTarget ε
  have hfront : frontier A ⊆ A \ U := by
    intro x hx
    refine ⟨hAclosed.frontier_subset hx, ?_⟩
    intro hxU
    have hxint : x ∈ interior A :=
      (interior_maximal hUA hUopen) hxU
    exact (mem_frontier_iff_notMem_interior (hAclosed.frontier_subset hx)).mp hx hxint
  apply measure_mono_null hfront
  rw [measure_sdiff hUA hUopen.measurableSet.nullMeasurableSet (measure_ne_top μ U)]
  rw [show μ A = ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^
      Fintype.card d by
        exact finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget hε0.le hε2,
    show μ U = ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^
      Fintype.card d by
        exact finiteTorusHaarProbabilityMeasure_strictAnchoredProjectiveReturnTarget hε0 hε2,
    tsub_self]

theorem rationallyIndependent_anchoredProjectiveReturnFrequency
    {d : Type*} [Fintype d]
    (frequency : d → ℝ)
    (hindependent : RationallyIndependentFrequency frequency)
    {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    Tendsto
      (fun A =>
        (finiteTorusPhaseProbabilityMeasure frequency A :
          Measure (UnitAddTorus d))
            (anchoredProjectiveReturnTarget ε))
      atTop
      (𝓝 (ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^
        Fintype.card d)) := by
  have hweak := finiteTorusPhaseProbabilityMeasure_tendsto_haar
    frequency hindependent
  have htarget :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hweak
      (finiteTorusHaarProbabilityMeasure_frontier_anchoredProjectiveReturnTarget
        hε0 hε2)
  simpa [finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget
    hε0.le hε2] using htarget

theorem RationallyIndependentFrequency.ne_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    {frequency : d → ℝ}
    (hindependent : RationallyIndependentFrequency frequency) (i : d) :
    frequency i ≠ 0 := by
  intro hi
  let n : d → ℤ := fun j => if j = i then 1 else 0
  have hdet : finiteTorusCharacterDetuning n frequency = 0 := by
    simp [finiteTorusCharacterDetuning, n, hi]
  have hn := hindependent n hdet
  have := congrFun hn i
  simp [n] at this

/-- Two or more rationally independent circle frequencies admit no nonzero
exact simultaneous phase return.  The dimension hypothesis is sharp: one
nonzero circle frequency is periodic. -/
theorem rationallyIndependent_no_nonzeroExactReturn
    {d : Type*} [Fintype d] [DecidableEq d] [Nontrivial d]
    (frequency : d → ℝ)
    (hindependent : RationallyIndependentFrequency frequency) :
    ∀ t : ℝ, screwPhase frequency t = 0 → t = 0 := by
  intro t ht
  obtain ⟨i, j, hij⟩ := exists_pair_ne d
  have hi := congrFun ht i
  have hj := congrFun ht j
  change (((frequency i * t / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0) at hi
  change (((frequency j * t / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0) at hj
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hi
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hj
  have hm' : (m : ℝ) = frequency i * t / (2 * Real.pi) := by simpa using hm
  have hn' : (n : ℝ) = frequency j * t / (2 * Real.pi) := by simpa using hn
  let k : d → ℤ := fun x => if x = i then n else if x = j then -m else 0
  have hdet : finiteTorusCharacterDetuning k frequency = 0 := by
    rw [finiteTorusCharacterDetuning]
    have hsum : (∑ x, (k x : ℝ) * frequency x) =
        (n : ℝ) * frequency i + (-m : ℤ) * frequency j := by
      have hterm : ∀ x : d,
          (k x : ℝ) * frequency x =
            (if x = i then (n : ℝ) * frequency x else 0) +
            (if x = j then ((-m : ℤ) : ℝ) * frequency x else 0) := by
        intro x
        by_cases hxi : x = i
        · subst x
          simp [k, hij]
        · by_cases hxj : x = j
          · subst x
            simp [k, hxi]
          · simp [k, hxi, hxj]
      rw [Finset.sum_congr rfl fun x _ => hterm x,
        Finset.sum_add_distrib]
      simp
    rw [hsum]
    push_cast
    rw [hm', hn']
    ring
  have hk := hindependent k hdet
  have hki := congrFun hk i
  have hkj := congrFun hk j
  have hn0 : n = 0 := by simpa [k, hij] using hki
  have hm0 : m = 0 := by simpa [k, hij, hij.symm] using hkj
  have hprod : frequency i * t = 0 := by
    have hden : 2 * Real.pi ≠ 0 := by positivity
    rw [hm0, Int.cast_zero] at hm'
    exact (div_eq_zero_iff.mp hm'.symm).resolve_right hden
  exact (mul_eq_zero.mp hprod).resolve_left (hindependent.ne_zero i)

/-- Exact anchored return-density law for a finite maximally projective spectrum. -/
theorem maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (reference : I) {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    Tendsto
      (fun A =>
        (finiteTorusPhaseProbabilityMeasure
          (projectiveFrequency energy reference) A :
          Measure (UnitAddTorus {i : I // i ≠ reference}))
            (anchoredProjectiveReturnTarget ε))
      atTop
      (𝓝 (ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^
        (Fintype.card I - 1))) := by
  have h := rationallyIndependent_anchoredProjectiveReturnFrequency
    (projectiveFrequency energy reference)
    (maximallyProjectiveEnergy_projectiveFrequency_independent
      energy hmax reference)
    hε0 hε2
  have hcard : Fintype.card {i : I // i ≠ reference} = Fintype.card I - 1 := by
    rw [Fintype.card_subtype_compl (fun i : I => i = reference),
      Fintype.card_subtype_eq]
  simpa [hcard] using h

/-- A maximally projective spectrum with at least three levels has no
nonzero exact anchored projective return.  The three-level threshold is
necessary because every two-level spectrum has one periodic relative phase. -/
theorem MaximallyProjectiveEnergy.no_nonzeroExactAnchoredReturn
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (reference : I) (hcard : 3 ≤ Fintype.card I) :
    ∀ t : ℝ,
      screwPhase (projectiveFrequency energy reference) t = 0 → t = 0 := by
  have hsubcard :
      Fintype.card {i : I // i ≠ reference} = Fintype.card I - 1 := by
    rw [Fintype.card_subtype_compl (fun i : I => i = reference),
      Fintype.card_subtype_eq]
  letI : Nontrivial {i : I // i ≠ reference} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact rationallyIndependent_no_nonzeroExactReturn
    (projectiveFrequency energy reference)
    (maximallyProjectiveEnergy_projectiveFrequency_independent
      energy hmax reference)

end
end GaloisForLFunctions.HTGeometry
