import GaloisForLFunctions.RHTower.FieldOneFiniteStageModule
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Haar scaling characters for finite-stage adelic factors

This file supplies measure-theoretic infrastructure needed to compare the
finite-stage norm module with additive Haar scaling:

* distributive Haar characters multiply over binary and finite dependent
  products;
* the real Haar character of multiplication by a unit is its norm;
* norm-one units have Haar character one in a locally compact
  nontrivially normed field;
* missing topology and measurability instances on rational adic completions
  are transported from their explicit `ℚ_p` models; and
* the sign and every rational prime viewed at a different finite place have
  local Haar character one.

The remaining local theorem is the same-place formula: multiplication by the
prime at its own adic completion has Haar character `p⁻¹`. No quotient
measure or `L²` conclusion is made here.
-/

open MeasureTheory
open MeasureTheory.Measure
open Filter
open scoped ENNReal NNReal Pointwise Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- Distributive Haar characters multiply under a diagonal action on a binary
product. -/
theorem fieldOne_distribHaarChar_prod
    {G A B : Type*}
    [Group G]
    [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B]
    [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B]
    [BorelSpace A] [BorelSpace B]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    [LocallyCompactSpace A] [LocallyCompactSpace B]
    [SecondCountableTopology A] [SecondCountableTopology B]
    [ContinuousConstSMul G A] [ContinuousConstSMul G B]
    (g : G) :
    distribHaarChar (A × B) g =
      distribHaarChar A g * distribHaarChar B g := by
  let μ : Measure A := addHaar
  let ν : Measure B := addHaar
  obtain ⟨s, hs_compact, hs_nhds⟩ :=
    exists_compact_mem_nhds (0 : A)
  obtain ⟨t, ht_compact, ht_nhds⟩ :=
    exists_compact_mem_nhds (0 : B)
  have hs_interior : (interior s).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.mpr hs_nhds⟩
  have ht_interior : (interior t).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.mpr ht_nhds⟩
  have hs_ne_zero : μ s ≠ 0 := by
    intro hs
    exact
      (IsOpenPosMeasure.open_pos (interior s) isOpen_interior
        hs_interior)
      (measure_mono_null interior_subset hs)
  have ht_ne_zero : ν t ≠ 0 := by
    intro ht
    exact
      (IsOpenPosMeasure.open_pos (interior t) isOpen_interior
        ht_interior)
      (measure_mono_null interior_subset ht)
  have hs_ne_top : μ s ≠ ∞ :=
    ne_of_lt hs_compact.measure_lt_top
  have ht_ne_top : ν t ≠ ∞ :=
    ne_of_lt ht_compact.measure_lt_top
  have hprod_ne_zero : μ.prod ν (s ×ˢ t) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero hs_ne_zero ht_ne_zero
  have hprod_ne_top : μ.prod ν (s ×ˢ t) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hs_ne_top ht_ne_top
  apply
    distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := μ.prod ν) hprod_ne_zero hprod_ne_top
  rw [Set.smul_set_prod]
  rw [Measure.prod_prod, Measure.prod_prod]
  rw [← distribHaarChar_mul μ g s]
  rw [← distribHaarChar_mul ν g t]
  rw [ENNReal.coe_mul]
  ac_rfl

/-- For multiplication of the real additive group by a real unit, the
distributive Haar character is the ordinary nonnegative norm. -/
theorem fieldOne_realUnits_distribHaarChar
    (u : ℝˣ) :
    distribHaarChar ℝ u = ‖(u : ℝ)‖₊ := by
  apply
    distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := (volume : Measure ℝ))
      (s := Set.Icc (0 : ℝ) 1)
  · simp [Real.volume_Icc]
  · simp [Real.volume_Icc]
  · change
      volume ((u : ℝ) • Set.Icc (0 : ℝ) 1) =
        (‖(u : ℝ)‖₊ : ℝ≥0∞) *
          volume (Set.Icc (0 : ℝ) 1)
    rw [addHaar_smul]
    simp only [Module.finrank_self, pow_one, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one, mul_one]
    rw [← Real.norm_eq_abs, ofReal_norm, enorm_eq_nnnorm]

/-- Distributive Haar characters multiply under a diagonal action on a finite
dependent product. -/
theorem fieldOne_distribHaarChar_pi
    {ι G : Type*} {A : ι → Type*}
    [Fintype ι] [Group G]
    [∀ i, AddCommGroup (A i)]
    [∀ i, DistribMulAction G (A i)]
    [∀ i, TopologicalSpace (A i)]
    [∀ i, MeasurableSpace (A i)]
    [∀ i, BorelSpace (A i)]
    [∀ i, IsTopologicalAddGroup (A i)]
    [∀ i, LocallyCompactSpace (A i)]
    [∀ i, SecondCountableTopology (A i)]
    [∀ i, ContinuousConstSMul G (A i)]
    (g : G) :
    distribHaarChar ((i : ι) → A i) g =
      ∏ i, distribHaarChar (A i) g := by
  classical
  let μ : (i : ι) → Measure (A i) := fun _ => addHaar
  let s : (i : ι) → Set (A i) :=
    fun i => (exists_compact_mem_nhds (0 : A i)).choose
  have hs_compact (i : ι) : IsCompact (s i) :=
    (exists_compact_mem_nhds (0 : A i)).choose_spec.1
  have hs_nhds (i : ι) : s i ∈ 𝓝 (0 : A i) :=
    (exists_compact_mem_nhds (0 : A i)).choose_spec.2
  have hs_ne_zero (i : ι) : μ i (s i) ≠ 0 := by
    intro hs
    exact
      (IsOpenPosMeasure.open_pos (interior (s i)) isOpen_interior
        ⟨0, mem_interior_iff_mem_nhds.mpr (hs_nhds i)⟩)
      (measure_mono_null interior_subset hs)
  have hs_ne_top (i : ι) : μ i (s i) ≠ ∞ :=
    ne_of_lt (hs_compact i).measure_lt_top
  have hpi_ne_zero :
      Measure.pi μ (Set.univ.pi s) ≠ 0 := by
    rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _ => hs_ne_zero i)
  have hpi_ne_top :
      Measure.pi μ (Set.univ.pi s) ≠ ∞ := by
    rw [Measure.pi_pi]
    exact ne_of_lt
      (WithTop.prod_lt_top fun i _ => (hs_ne_top i).lt_top)
  have hlocal (i : ι) :
      μ i (g • s i) =
        distribHaarChar (A i) g * μ i (s i) :=
    (distribHaarChar_mul (μ i) g (s i)).symm
  apply
    distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := Measure.pi μ) hpi_ne_zero hpi_ne_top
  rw [Set.smul_set_pi]
  rw [Measure.pi_pi, Measure.pi_pi]
  change
    (∏ i, μ i (g • s i)) =
      (↑(∏ i, distribHaarChar (A i) g) : ℝ≥0∞) *
        ∏ i, μ i (s i)
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  rw [ENNReal.ofNNReal_finsetProd]

/-- A norm-one unit of a locally compact nontrivially normed field preserves
the closed unit ball, hence has distributive Haar character one. -/
theorem fieldOne_units_distribHaarChar_eq_one_of_norm_eq_one
    {K : Type*}
    [NontriviallyNormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    (u : Kˣ) (hu : ‖(u : K)‖ = 1) :
    distribHaarChar K u = 1 := by
  letI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  let μ : Measure K := addHaar
  let s : Set K := Metric.closedBall 0 1
  have hs_ne_zero : μ s ≠ 0 := by
    intro hs
    have hopen : IsOpen (Metric.ball (0 : K) 1) :=
      Metric.isOpen_ball
    have hnonempty : (Metric.ball (0 : K) 1).Nonempty :=
      ⟨0, Metric.mem_ball_self zero_lt_one⟩
    exact
      (IsOpenPosMeasure.open_pos
        (Metric.ball (0 : K) 1) hopen hnonempty)
      (measure_mono_null Metric.ball_subset_closedBall hs)
  have hs_ne_top : μ s ≠ ∞ :=
    ne_of_lt (isCompact_closedBall (0 : K) 1).measure_lt_top
  apply
    distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := μ) (s := s) hs_ne_zero hs_ne_top
  have hset : u • s = s := by
    change
      (u : K) • Metric.closedBall (0 : K) 1 =
        Metric.closedBall (0 : K) 1
    rw [smul_unitClosedBall]
    exact congrArg (Metric.closedBall (0 : K)) hu
  rw [hset]
  simp

/-! ## Rational adic completion instances -/

/-- A rational adic completion is nontrivially normed. The inverse of its
associated rational prime has norm greater than one. -/
noncomputable instance fieldOneAdicCompletionNontriviallyNormedField
    (v : HeightOneSpectrum ℤ) :
    NontriviallyNormedField (v.adicCompletion ℚ) where
  toNormedField := inferInstance
  non_trivial := by
    let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
    refine
      ⟨(algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ))⁻¹, ?_⟩
    rw [norm_inv, fieldOneRationalPrimeUnit_localNorm_self v]
    have hp : (1 : ℝ) < p := by
      exact_mod_cast
        (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt
    simpa only [inv_inv] using hp

/-- Second countability transported from the explicit rational adic
completion equivalence with `ℚ_p`. -/
noncomputable instance fieldOneAdicCompletionSecondCountableTopology
    (v : HeightOneSpectrum ℤ) :
    SecondCountableTopology (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.secondCountableTopology

/-- Canonical Borel measurable structure on a rational adic completion. -/
noncomputable instance fieldOneAdicCompletionMeasurableSpace
    (v : HeightOneSpectrum ℤ) :
    MeasurableSpace (v.adicCompletion ℚ) :=
  borel (v.adicCompletion ℚ)

/-- The chosen measurable structure on a rational adic completion is Borel. -/
noncomputable instance fieldOneAdicCompletionBorelSpace
    (v : HeightOneSpectrum ℤ) :
    BorelSpace (v.adicCompletion ℚ) :=
  ⟨rfl⟩

/-- Local compactness transported from the explicit rational adic completion
equivalence with `ℚ_p`. -/
noncomputable instance fieldOneAdicCompletionLocallyCompactSpace
    (v : HeightOneSpectrum ℤ) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isOpenEmbedding.locallyCompactSpace

/-- Properness of rational adic completions, obtained from local compactness
of their nontrivially normed field topology. -/
noncomputable instance fieldOneAdicCompletionProperSpace
    (v : HeightOneSpectrum ℤ) :
    ProperSpace (v.adicCompletion ℚ) :=
  ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _

/-! ## Norm-one rational generators -/

/-- The diagonal sign has local distributive Haar character one at every
rational finite place. -/
theorem fieldOneRationalLocalUnit_distribHaarChar_negOne
    (v : HeightOneSpectrum ℤ) :
    distribHaarChar (v.adicCompletion ℚ)
      (fieldOneRationalLocalUnit v (-1)) = 1 := by
  apply fieldOne_units_distribHaarChar_eq_one_of_norm_eq_one
  simp [fieldOneRationalLocalUnit]

/-- A rational prime has local distributive Haar character one at every
different rational finite place. -/
theorem fieldOneRationalPrimeUnit_localDistribHaarChar_of_ne
    (v w : HeightOneSpectrum ℤ)
    (hvw : w ≠ v) :
    distribHaarChar (w.adicCompletion ℚ)
      (fieldOneRationalLocalUnit w
        (fieldOneRationalPrimeUnit v)) = 1 := by
  apply fieldOne_units_distribHaarChar_eq_one_of_norm_eq_one
  change
    ‖algebraMap ℚ (w.adicCompletion ℚ)
        (Rat.HeightOneSpectrum.primesEquiv v : ℚ)‖ = 1
  exact fieldOneRationalPrimeUnit_localNorm_of_ne v w hvw

end

end GaloisForLFunctions.RHTower
