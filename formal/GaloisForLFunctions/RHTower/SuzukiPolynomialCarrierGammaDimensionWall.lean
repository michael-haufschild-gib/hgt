import GaloisForLFunctions.RHTower.SuzukiGammaStripCarrierIntegrability
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Polynomial-carrier Gamma dimension wall

A polynomial orbit weight of degree `κ` distorts the squared Gamma propagator by
`|x|^(2κ)`.  Its exact tail is therefore `|x|^(-1-2σ+2κ)`, so it is integrable precisely when
`κ < σ`.  Lattice square summability simultaneously requires `d/2 < κ`; because the literal
Gamma strip has `σ < 1`, the two requirements have a common window exactly in ranks zero and one.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Squared Gamma carrier after a polynomially growing transport of degree `κ`. -/
def suzukiPolynomialDistortedGammaNormSq (κ σ x : ℝ) : ℝ :=
  |x| ^ (2 * κ) * suzukiGammaStripNormSq σ x

@[simp] theorem suzukiPolynomialDistortedGammaNormSq_neg (κ σ x : ℝ) :
    suzukiPolynomialDistortedGammaNormSq κ σ (-x) =
      suzukiPolynomialDistortedGammaNormSq κ σ x := by
  simp [suzukiPolynomialDistortedGammaNormSq]

/-- Exact tail exponent after polynomial transport. -/
theorem suzukiPolynomialDistortedGammaNormSq_rpow_tendsto
    {κ σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun x : ℝ =>
      suzukiPolynomialDistortedGammaNormSq κ σ x *
        x ^ (1 + 2 * σ - 2 * κ)) atTop (nhds 1) := by
  have hbase := suzukiGammaStripNormSq_rpow_tendsto hσ0 hσ1
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [suzukiPolynomialDistortedGammaNormSq, abs_of_pos hx]
  have hpow : x ^ (2 * κ) * x ^ (1 + 2 * σ - 2 * κ) =
      x ^ (1 + 2 * σ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc
    suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ) =
        suzukiGammaStripNormSq σ x *
          (x ^ (2 * κ) * x ^ (1 + 2 * σ - 2 * κ)) := by rw [hpow]
    _ = (x ^ (2 * κ) * suzukiGammaStripNormSq σ x) *
        x ^ (1 + 2 * σ - 2 * κ) := by
      calc
        suzukiGammaStripNormSq σ x *
            (x ^ (2 * κ) * x ^ (1 + 2 * σ - 2 * κ)) =
            (suzukiGammaStripNormSq σ x * x ^ (2 * κ)) *
              x ^ (1 + 2 * σ - 2 * κ) := (mul_assoc _ _ _).symm
        _ = (x ^ (2 * κ) * suzukiGammaStripNormSq σ x) *
              x ^ (1 + 2 * σ - 2 * κ) := by
              rw [mul_comm (suzukiGammaStripNormSq σ x) (x ^ (2 * κ))]
        _ = (x ^ (2 * κ) * suzukiGammaStripNormSq σ x) *
              x ^ (1 + 2 * σ - 2 * κ) := rfl

theorem continuous_suzukiPolynomialDistortedGammaNormSq
    {κ σ : ℝ} (hκ : 0 < κ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (suzukiPolynomialDistortedGammaNormSq κ σ) := by
  exact (continuous_abs.rpow_const (fun _ => Or.inr (by linarith))).mul
    (continuous_suzukiGammaStripNormSq hσ0 hσ1)

/-- Polynomial transport below the shifted Gamma exponent preserves square integrability. -/
theorem integrable_suzukiPolynomialDistortedGammaNormSq
    {κ σ : ℝ} (hκ : 0 < κ) (hκσ : κ < σ) (hσ1 : σ < 1) :
    Integrable (suzukiPolynomialDistortedGammaNormSq κ σ) := by
  have hσ0 : 0 < σ := hκ.trans hκσ
  have hlocal : LocallyIntegrable (suzukiPolynomialDistortedGammaNormSq κ σ) volume :=
    (continuous_suzukiPolynomialDistortedGammaNormSq hκ hσ0 hσ1).locallyIntegrable
  have htend := suzukiPolynomialDistortedGammaNormSq_rpow_tendsto
    (κ := κ) (σ := σ) hσ0.le hσ1
  have hev : ∀ᶠ x : ℝ in atTop,
      suzukiPolynomialDistortedGammaNormSq κ σ x *
          x ^ (1 + 2 * σ - 2 * κ) < 2 :=
    htend.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hbigO : suzukiPolynomialDistortedGammaNormSq κ σ =O[atTop]
      (fun x : ℝ => x ^ (-(1 + 2 * σ - 2 * κ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with x hxprod hx
    have hpow : 0 < x ^ (1 + 2 * σ - 2 * κ) := Real.rpow_pos_of_pos hx _
    have hdensity : 0 ≤ suzukiPolynomialDistortedGammaNormSq κ σ x := by
      unfold suzukiPolynomialDistortedGammaNormSq suzukiGammaStripNormSq
      positivity
    have hle : suzukiPolynomialDistortedGammaNormSq κ σ x ≤
        2 * x ^ (-(1 + 2 * σ - 2 * κ)) := by
      rw [Real.rpow_neg hx.le]
      apply (le_div_iff₀ hpow).mpr
      nlinarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdensity,
      abs_of_pos (Real.rpow_pos_of_pos hx _)]
    exact hle
  have hsymm : norm ∘ suzukiPolynomialDistortedGammaNormSq κ σ =ᵐ[volume]
      norm ∘ suzukiPolynomialDistortedGammaNormSq κ σ ∘ Neg.neg := by
    filter_upwards [] with x
    simp [Function.comp_def]
  apply hlocal.integrable_of_isBigO_atTop_of_norm_isNegInvariant hsymm hbigO
  rw [integrableAtFilter_rpow_atTop_iff]
  linarith

/-- At or above the shifted Gamma exponent, polynomial transport destroys square integrability. -/
theorem not_integrable_suzukiPolynomialDistortedGammaNormSq
    {κ σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hσκ : σ ≤ κ) :
    ¬ Integrable (suzukiPolynomialDistortedGammaNormSq κ σ) := by
  intro hint
  have htend := suzukiPolynomialDistortedGammaNormSq_rpow_tendsto
    (κ := κ) (σ := σ) hσ0.le hσ1
  have hlower : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) < suzukiPolynomialDistortedGammaNormSq κ σ x *
        x ^ (1 + 2 * σ - 2 * κ) :=
    htend.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨A, hA⟩ := mem_atTop_sets.mp hlower
  let C : ℝ := max A 1
  have htail : IntegrableOn (suzukiPolynomialDistortedGammaNormSq κ σ) (Ici C) volume :=
    hint.integrableOn
  have hpower : IntegrableOn (fun x : ℝ => x ^ (-(1 + 2 * σ - 2 * κ)))
      (Ici C) volume := by
    apply (htail.const_mul 2).mono'
    · exact (continuousOn_id.rpow_const (fun x hx => Or.inl (by
          have hx1 : 1 ≤ x := (le_max_right A 1).trans hx
          have hx0 : 0 < id x := by simpa only [id_eq] using zero_lt_one.trans_le hx1
          exact hx0.ne'))).aestronglyMeasurable measurableSet_Ici
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx1 : 1 ≤ x := (le_max_right A 1).trans hx
      have hx0 : 0 < x := zero_lt_one.trans_le hx1
      have hprod := hA x ((le_max_left A 1).trans hx)
      have hpowpos : 0 < x ^ (1 + 2 * σ - 2 * κ) := Real.rpow_pos_of_pos hx0 _
      have hinvpos : 0 < x ^ (-(1 + 2 * σ - 2 * κ)) := Real.rpow_pos_of_pos hx0 _
      have hpows : x ^ (-(1 + 2 * σ - 2 * κ)) *
          x ^ (1 + 2 * σ - 2 * κ) = 1 := by
        rw [← Real.rpow_add hx0]
        norm_num
      have hdensity : 0 ≤ suzukiPolynomialDistortedGammaNormSq κ σ x := by
        unfold suzukiPolynomialDistortedGammaNormSq suzukiGammaStripNormSq
        positivity
      have hscaled : x ^ (-(1 + 2 * σ - 2 * κ)) * (1 / 2 : ℝ) <
          suzukiPolynomialDistortedGammaNormSq κ σ x := by
        calc
          x ^ (-(1 + 2 * σ - 2 * κ)) * (1 / 2 : ℝ) <
              x ^ (-(1 + 2 * σ - 2 * κ)) *
                (suzukiPolynomialDistortedGammaNormSq κ σ x *
                  x ^ (1 + 2 * σ - 2 * κ)) :=
            mul_lt_mul_of_pos_left hprod hinvpos
          _ = suzukiPolynomialDistortedGammaNormSq κ σ x *
                (x ^ (-(1 + 2 * σ - 2 * κ)) *
                  x ^ (1 + 2 * σ - 2 * κ)) := by ring
          _ = suzukiPolynomialDistortedGammaNormSq κ σ x := by rw [hpows, mul_one]
      rw [Real.norm_eq_abs, abs_of_pos hinvpos]
      nlinarith
  have hatTop : IntegrableAtFilter
      (fun x : ℝ => x ^ (-(1 + 2 * σ - 2 * κ))) atTop volume :=
    ⟨Ici C, Ici_mem_atTop C, hpower⟩
  have hexponent : -(1 + 2 * σ - 2 * κ) < -1 :=
    integrableAtFilter_rpow_atTop_iff.mp hatTop
  linarith

/-- Sharp polynomial-distortion threshold for the literal Gamma homogeneous carrier. -/
theorem integrable_suzukiPolynomialDistortedGammaNormSq_iff
    {κ σ : ℝ} (hκ : 0 < κ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Integrable (suzukiPolynomialDistortedGammaNormSq κ σ) ↔ κ < σ := by
  constructor
  · intro h
    exact lt_of_not_ge fun hσκ =>
      not_integrable_suzukiPolynomialDistortedGammaNormSq hσ0 hσ1 hσκ h
  · exact fun hκσ => integrable_suzukiPolynomialDistortedGammaNormSq hκ hκσ hσ1

/-- Lattice square summability and Gamma transport integrability have a common exponent window. -/
def suzukiPolynomialGammaDimensionWindow (d : ℕ) : Prop :=
  ∃ κ σ : ℝ, (d : ℝ) / 2 < κ ∧ κ < σ ∧ σ < 1

/-- **Sharp dimension wall.**  A radial polynomial carrier can be both lattice-square-summable
and Gamma-Hardy-integrable exactly in ranks zero and one. -/
theorem suzukiPolynomialGammaDimensionWindow_iff (d : ℕ) :
    suzukiPolynomialGammaDimensionWindow d ↔ d ≤ 1 := by
  constructor
  · rintro ⟨κ, σ, hdκ, hκσ, hσ1⟩
    by_contra hd
    have h2d : 2 ≤ d := Nat.lt_of_not_ge hd
    have h2d' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2d
    have h1 : (1 : ℝ) ≤ (d : ℝ) / 2 := by linarith
    linarith
  · intro hd
    refine ⟨2 / 3, 3 / 4, ?_, by norm_num, by norm_num⟩
    have hd' : (d : ℝ) ≤ 1 := by exact_mod_cast hd
    linarith

/-- Concrete one-prime exponent `κ = 2/3` is square summable. -/
theorem summable_suzukiOnePrimePolynomialWeightSq :
    Summable fun n : ℤ =>
      1 / ((1 + (n.natAbs : ℝ)) ^ (4 / 3 : ℝ)) := by
  have hbase : Summable fun k : ℕ =>
      1 / |(k : ℝ) + 1| ^ (4 / 3 : ℝ) :=
    (Real.summable_one_div_nat_add_rpow 1 (4 / 3)).2 (by norm_num)
  have hbase' : Summable fun k : ℕ =>
      1 / ((1 + (k : ℝ)) ^ (4 / 3 : ℝ)) := by
    refine hbase.congr fun k => ?_
    rw [abs_of_pos (by positivity)]
    congr 2
    ring
  refine Summable.of_nat_of_neg (f := fun n : ℤ =>
      1 / ((1 + (n.natAbs : ℝ)) ^ (4 / 3 : ℝ))) ?_ ?_
  · refine hbase'.congr fun k => ?_
    simp
  · refine hbase'.congr fun k => ?_
    simp

/-- A one-prime carrier realizes the common window at `κ = 2/3`, `σ = 3/4`. -/
theorem suzukiOnePrimePolynomialGammaWindow :
    Summable (fun n : ℤ =>
      1 / ((1 + (n.natAbs : ℝ)) ^ (4 / 3 : ℝ))) ∧
    Integrable (suzukiPolynomialDistortedGammaNormSq (2 / 3) (3 / 4)) := by
  refine ⟨summable_suzukiOnePrimePolynomialWeightSq, ?_⟩
  exact integrable_suzukiPolynomialDistortedGammaNormSq
    (by norm_num) (by norm_num) (by norm_num)

end GaloisForLFunctions.RHTower
