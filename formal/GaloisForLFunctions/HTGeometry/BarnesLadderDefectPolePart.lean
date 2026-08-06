import GaloisForLFunctions.HTGeometry.BarnesLadderStepDA

/-!
# The exact ladder defect and its single pole

The multi-period ladder defect is not merely differentially algebraic: it is an explicit rational
function of the argument,

```text
σ_{ω_j} Ψ_ω - Ψ_ω + Ψ_{ω^{(j)}} = N_j(z) / (z + ω_j),
```

and the numerator takes the value `-1` at `z = -ω_j`.  Hence the defect splits as

```text
N_j / (X + ω_j) = P_j - 1/(X + ω_j),
```

with `P_j` a polynomial: the whole pole part of the ladder defect is one simple pole at `-ω_j` with
residue `-1`.

That is the shape the multiple-sine correction consumes.  The reflected ladder produces the defect
together with its reflection, so the poles occur in pairs whose residues cancel along the period,
and a rational correction turns the ladder into the exact multiple-sine difference equation.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ### The ladder defect is an explicit rational function -/

theorem hasPuncturedMeromorphicRep_barnesSource_ladder (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (j : ι) [Nonempty {i : ι // i ≠ j}] :
    HasPuncturedMeromorphicRep
      (addTranslationMeroEquiv (ω j) (barnesSourceLogDerivMero ω hω)
          - barnesSourceLogDerivMero ω hω
        + barnesSourceLogDerivMero (deletedFrame ω j) (deletedFrame_im_pos hω j))
      (fun z => (barnesLadderNumerator ω j).eval z /
        (Polynomial.X + Polynomial.C (ω j)).eval z) := by
  refine (((hasPuncturedMeromorphicRep_addTranslation_barnesSourceLogDerivMero ω hω
      (ω j)).sub (hasPuncturedMeromorphicRep_barnesSourceLogDerivMero ω hω)).add
    (hasPuncturedMeromorphicRep_barnesSourceLogDerivMero (deletedFrame ω j)
      (deletedFrame_im_pos hω j))).congr_fun ?_
  intro z₀
  have hshift := (tendsto_nhdsNE_add (ω j) z₀).eventually
    (eventually_nhdsNE_conePeriod_add_ne_zero ω hω (z₀ + ω j))
  filter_upwards [eventually_nhdsNE_conePeriod_add_ne_zero ω hω z₀, hshift,
    eventually_nhdsNE_conePeriod_add_ne_zero (deletedFrame ω j) (deletedFrame_im_pos hω j) z₀]
    with w hw hw' hwD
  show (logDeriv (barnesConeProduct ω) (w + ω j) - logDeriv (barnesConeProduct ω) w)
      + logDeriv (barnesConeProduct (deletedFrame ω j)) w
    = (barnesLadderNumerator ω j).eval w / (Polynomial.X + Polynomial.C (ω j)).eval w
  exact barnesSource_ladder_ratio ω hω j hw hw' hwD

/-- **The ladder defect, exactly.**  The translation defect of the Barnes source is the embedded
rational function `N_j / (X + ω_j)`. -/
theorem barnesSource_ladder_defect_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (j : ι) [Nonempty {i : ι // i ≠ j}] :
    addTranslationMeroEquiv (ω j) (barnesSourceLogDerivMero ω hω)
          - barnesSourceLogDerivMero ω hω
        + barnesSourceLogDerivMero (deletedFrame ω j) (deletedFrame_im_pos hω j)
      = ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesLadderNumerator ω j) /
          algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C (ω j))) :=
  eq_ratfuncToMero_of_hasPuncturedMeromorphicRep_ratio
    (Polynomial.X_add_C_ne_zero (ω j))
    (hasPuncturedMeromorphicRep_barnesSource_ladder ω hω j)

/-! ### The numerator at the pole -/

omit [Nonempty ι] in
/-- **The residue of the ladder defect is `-1`.**  The numerator takes the value `-1` at the pole
`z = -ω_j`. -/
theorem barnesLadderNumerator_eval_neg_period (ω : ι → ℂ) (j : ι) (hωj : ω j ≠ 0) :
    (barnesLadderNumerator ω j).eval (-(ω j)) = -1 := by
  rw [barnesLadderNumerator]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  have hzero : -(ω j) + ω j = 0 := by ring
  rw [hzero, mul_zero, zero_sub]
  have hpow : ((-1) / ω j) ^ Fintype.card ι * (-(ω j)) ^ Fintype.card ι = 1 := by
    rw [← mul_pow]
    have : (-1) / ω j * -(ω j) = 1 := by field_simp
    rw [this, one_pow]
  rw [hpow]

/-! ### The polynomial part -/

omit [Nonempty ι] in
theorem linear_dvd_barnesLadderNumerator_add_one (ω : ι → ℂ) (j : ι) (hωj : ω j ≠ 0) :
    (Polynomial.X + Polynomial.C (ω j)) ∣ (barnesLadderNumerator ω j + 1) := by
  have hroot : (barnesLadderNumerator ω j + 1).IsRoot (-(ω j)) := by
    rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_one,
      barnesLadderNumerator_eval_neg_period ω j hωj]
    ring
  have hdvd := (Polynomial.dvd_iff_isRoot (a := -(ω j))
    (p := barnesLadderNumerator ω j + 1)).mpr hroot
  have hXC : Polynomial.X - Polynomial.C (-(ω j)) = Polynomial.X + Polynomial.C (ω j) := by
    rw [map_neg, sub_neg_eq_add]
  rwa [hXC] at hdvd

/-- The polynomial part of the ladder defect. -/
def barnesLadderPolyPart (ω : ι → ℂ) (j : ι) : Polynomial ℂ :=
  (barnesLadderNumerator ω j + 1) /ₘ (Polynomial.X + Polynomial.C (ω j))

omit [Nonempty ι] in
theorem barnesLadderNumerator_eq (ω : ι → ℂ) (j : ι) (hωj : ω j ≠ 0) :
    barnesLadderNumerator ω j
      = barnesLadderPolyPart ω j * (Polynomial.X + Polynomial.C (ω j)) - 1 := by
  have hmonic : (Polynomial.X + Polynomial.C (ω j)).Monic := Polynomial.monic_X_add_C (ω j)
  obtain ⟨r, hr⟩ := linear_dvd_barnesLadderNumerator_add_one ω j hωj
  have hpp : barnesLadderPolyPart ω j = r := by
    rw [barnesLadderPolyPart, hr, Polynomial.mul_divByMonic_cancel_left r hmonic]
  rw [hpp, mul_comm, ← hr]
  ring

omit [Nonempty ι] in
/-- **The ladder defect splits into a polynomial and one simple pole.** -/
theorem barnesLadderRatio_eq (ω : ι → ℂ) (j : ι) (hωj : ω j ≠ 0) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesLadderNumerator ω j) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C (ω j))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesLadderPolyPart ω j)
        - 1 / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C (ω j)) := by
  have hne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C (ω j)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (ω j))
  rw [barnesLadderNumerator_eq ω j hωj, map_sub, map_mul, map_one]
  field_simp

end

end GaloisForLFunctions.HTGeometry
