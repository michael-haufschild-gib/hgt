import GaloisForLFunctions.RHTower.SuzukiApertureRecurrence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Almost every aperture has recurrence exponent zero

For a fixed rate `c > 0`, the apertures approximated to depth `e^{-cN}` by some valuation of
`ℓ¹` length `N` form a set of measure at most `(2N+1)^{#P} e^{-cN}`: each valuation contributes an
interval of length `e^{-cN}`, and there are at most `(2N+1)^{#P}` valuations of that length.  That
majorant is summable, so Borel–Cantelli leaves almost every aperture with only finitely many such
approximations — the finite recurrence type is generic.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Valuations of a given `ℓ¹` length live in a box. -/
theorem orbitLength_le_of_eq {P : Type*} [Fintype P] {ν : P → ℤ} {N : ℕ}
    (h : orbitLength ν = N) (p : P) : (ν p).natAbs ≤ N := by
  rw [← h, orbitLength]
  exact Finset.single_le_sum (f := fun q => (ν q).natAbs) (fun q _ => Nat.zero_le _)
    (Finset.mem_univ p)

/-- The finite index set of valuations of `ℓ¹` length `N`. -/
def orbitLevel (P : Type*) [Fintype P] [DecidableEq P] (N : ℕ) : Finset (P → ℤ) :=
  (Fintype.piFinset fun _ : P => Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    fun ν => orbitLength ν = N

theorem mem_orbitLevel {P : Type*} [Fintype P] [DecidableEq P] {N : ℕ} {ν : P → ℤ}
    (h : orbitLength ν = N) : ν ∈ orbitLevel P N := by
  rw [orbitLevel, Finset.mem_filter]
  refine ⟨?_, h⟩
  rw [Fintype.mem_piFinset]
  intro p
  rw [Finset.mem_Icc]
  have hp := orbitLength_le_of_eq h p
  omega

theorem card_orbitLevel_le {P : Type*} [Fintype P] [DecidableEq P] (N : ℕ) :
    (orbitLevel P N).card ≤ (2 * N + 1) ^ Fintype.card P := by
  have hsub : (orbitLevel P N).card
      ≤ (Fintype.piFinset fun _ : P => Finset.Icc (-(N : ℤ)) (N : ℤ)).card :=
    Finset.card_filter_le _ _
  refine hsub.trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  have hcard : ∀ _p : P, (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    intro _
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun p _ => hcard p, Finset.prod_const, Finset.card_univ]

/-- The set of apertures approximated at depth `e^{-cN}` by a valuation of length `N`. -/
def apertureApproxSet {P : Type*} [Fintype P] [DecidableEq P] (ℓ : (P → ℤ) → ℝ) (c : ℝ)
    (N : ℕ) : Set ℝ :=
  ⋃ ν ∈ orbitLevel P N, {a : ℝ | |2 * a - ℓ ν| < Real.exp (-(c * N))}

theorem apertureApproxSet_subset {P : Type*} [Fintype P] [DecidableEq P] (ℓ : (P → ℤ) → ℝ)
    (c : ℝ) (N : ℕ) :
    apertureApproxSet ℓ c N
      ⊆ ⋃ ν ∈ orbitLevel P N,
          Ioo ((ℓ ν - Real.exp (-(c * N))) / 2) ((ℓ ν + Real.exp (-(c * N))) / 2) := by
  intro a ha
  rw [apertureApproxSet, mem_iUnion₂] at ha
  obtain ⟨ν, hν, hlt⟩ := ha
  simp only [Set.mem_setOf_eq] at hlt
  rw [mem_iUnion₂]
  refine ⟨ν, hν, ?_⟩
  have habs := abs_lt.mp hlt
  constructor
  · linarith [habs.1]
  · linarith [habs.2]

theorem measurableSet_apertureApproxSet {P : Type*} [Fintype P] [DecidableEq P]
    (ℓ : (P → ℤ) → ℝ) (c : ℝ) (N : ℕ) : MeasurableSet (apertureApproxSet ℓ c N) := by
  rw [apertureApproxSet]
  refine Finset.measurableSet_biUnion _ fun ν _ => ?_
  have hcont : Continuous fun a : ℝ => |2 * a - ℓ ν| := by fun_prop
  exact measurableSet_lt (hcont.measurable) measurable_const

/-- **`(27)`: the measure of the approximated apertures at length `N`.** -/
theorem volume_apertureApproxSet_le {P : Type*} [Fintype P] [DecidableEq P]
    (ℓ : (P → ℤ) → ℝ) (c : ℝ) (N : ℕ) :
    volume (apertureApproxSet ℓ c N)
      ≤ ENNReal.ofReal ((2 * N + 1) ^ Fintype.card P * Real.exp (-(c * N))) := by
  have hsub := apertureApproxSet_subset ℓ c N
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hterm : ∀ ν ∈ orbitLevel P N,
      volume (Ioo ((ℓ ν - Real.exp (-(c * N))) / 2) ((ℓ ν + Real.exp (-(c * N))) / 2))
        ≤ ENNReal.ofReal (Real.exp (-(c * N))) := by
    intro ν _
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    have := Real.exp_pos (-(c * N))
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((orbitLevel P N).card : ℝ≥0∞) ≤ ((2 * N + 1) ^ Fintype.card P : ℕ) := by
    exact_mod_cast Nat.cast_le.mpr (card_orbitLevel_le N)
  refine le_trans (mul_le_mul' hcard (le_refl (ENNReal.ofReal (Real.exp (-(c * N)))))) ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  push_cast
  ring

/-- The approximation majorant is summable. -/
theorem summable_apertureMajorant (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun N : ℕ => (2 * (N : ℝ) + 1) ^ d * Real.exp (-(c * N)) := by
  set r : ℝ := Real.exp (-c) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hrlt : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0, hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable fun M : ℕ => (M : ℝ) ^ d * r ^ M :=
    summable_pow_mul_geometric_of_norm_lt_one d hrlt
  have hshift : Summable fun N : ℕ => ((N : ℝ) + 1) ^ d * r ^ N := by
    have h1 : Summable fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ d * r ^ (N + 1) :=
      (summable_nat_add_iff 1).mpr hgeo
    have h2 : Summable fun N : ℕ => r⁻¹ * (((N + 1 : ℕ) : ℝ) ^ d * r ^ (N + 1)) :=
      h1.mul_left _
    refine h2.congr fun N => ?_
    have hne : r ≠ 0 := ne_of_gt hr0
    push_cast
    field_simp
    ring
  have hexp : ∀ N : ℕ, Real.exp (-(c * N)) = r ^ N := by
    intro N
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hdom : Summable fun N : ℕ => (3:ℝ) ^ d * (((N : ℝ) + 1) ^ d * r ^ N) := hshift.mul_left _
  refine hdom.of_nonneg_of_le (fun N => by positivity) ?_
  intro N
  rw [hexp N]
  have hbound : (2 * (N : ℝ) + 1) ^ d ≤ 3 ^ d * ((N : ℝ) + 1) ^ d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hrpow : (0:ℝ) ≤ r ^ N := pow_nonneg hr0.le N
  nlinarith [hbound, hrpow]

/-- **`(27)`, Borel–Cantelli: almost every aperture is approximated only finitely often.** -/
theorem ae_finite_apertureApprox {P : Type*} [Fintype P] [DecidableEq P]
    (ℓ : (P → ℤ) → ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ a : ℝ, a ∉ Filter.atTop.limsup (apertureApproxSet ℓ c) := by
  have hmaj := summable_apertureMajorant (Fintype.card P) hc
  have hnn : ∀ N : ℕ, 0 ≤ (2 * (N : ℝ) + 1) ^ Fintype.card P * Real.exp (-(c * N)) := by
    intro N
    positivity
  have hsum : (∑' N : ℕ, volume (apertureApproxSet ℓ c N)) ≠ ⊤ := by
    have hle : ∀ N : ℕ, volume (apertureApproxSet ℓ c N)
        ≤ ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ Fintype.card P * Real.exp (-(c * N))) := by
      intro N
      exact volume_apertureApproxSet_le ℓ c N
    have hbound : (∑' N : ℕ, volume (apertureApproxSet ℓ c N))
        ≤ ∑' N : ℕ, ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ Fintype.card P * Real.exp (-(c * N))) :=
      ENNReal.tsum_le_tsum hle
    have hfin : (∑' N : ℕ,
        ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ Fintype.card P * Real.exp (-(c * N)))) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hmaj]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin hbound
  have hmeas : ∀ N : ℕ, MeasurableSet (apertureApproxSet ℓ c N) :=
    fun N => measurableSet_apertureApproxSet ℓ c N
  have hzero := measure_limsup_atTop_eq_zero hsum
  rw [ae_iff]
  simpa using hzero

end

end RHTower
