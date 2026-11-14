import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianSpectral

/-!
# Gaussian compensation bounds

A bounded horizontal depth controls the Gaussian envelope. Outside a fixed
ordinate window, that envelope is a small multiple of the Lorentzian kernel.
A negative real contribution must have a definite horizontal depth.
-/

open Filter Topology Complex
noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open RiemannGaussian

/-- The strip of half-width three eighths gives an explicit Gaussian envelope. -/
theorem abs_gaussianContribution_le_strip_envelope {ε a : ℝ} (hε : 0 ≤ ε)
    (ha : |a| ≤ 3 / 8) (T γ : ℝ) :
    |offAxisSingleContribution ε T γ a| ≤
      Real.exp (9 * ε / 64) * Real.exp (-ε * (γ - T) ^ 2) := by
  have hs := pow_le_pow_left₀ (abs_nonneg a) ha 2
  rw [sq_abs] at hs
  norm_num at hs
  refine (abs_offAxisSingleContribution_le_envelope ε T γ a).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hs hε
  linarith only [hh]

/-- A Gaussian of inverse variance at least one is dominated in its tail by
an exponentially small multiple of the unit Lorentzian kernel. -/
theorem gaussian_lorentz_tail_le {ε R u : ℝ} (hε : 1 ≤ ε) (hR : 0 ≤ R)
    (hu : R ≤ |u|) :
    Real.exp (-ε * u ^ 2) ≤
      (2 * Real.exp (-(ε * R ^ 2 / 2))) / (1 + u ^ 2) := by
  have hε0 : 0 < ε := by linarith only [hε]
  have hq := Real.add_one_le_exp (ε * u ^ 2 / 2)
  have hbase : 1 + u ^ 2 ≤ 2 * Real.exp (ε * u ^ 2 / 2) := by
    have hm := mul_le_mul_of_nonneg_right hε (sq_nonneg u)
    nlinarith only [hq, hm]
  have hh := mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg (-ε * u ^ 2))
  have heq : (2 * Real.exp (ε * u ^ 2 / 2)) * Real.exp (-ε * u ^ 2) =
      2 * Real.exp (-(ε * u ^ 2 / 2)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hh
  have hs := pow_le_pow_left₀ hR hu 2
  rw [sq_abs] at hs
  have he : Real.exp (-(ε * u ^ 2 / 2)) ≤ Real.exp (-(ε * R ^ 2 / 2)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hs hε0.le
    linarith only [hm]
  apply (le_div_iff₀ (by positivity : 0 < 1 + u ^ 2)).mpr
  have hhe := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [hh, hhe]

/-- A negative Gaussian contribution in a bounded ordinate window lies a
positive distance from the critical line. -/
theorem gaussian_negative_depth_ge {ε R a T γ : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (hu : |γ - T| ≤ R) (hneg : offAxisSingleContribution ε T γ a < 0) :
    Real.pi / (4 * ε * R) ≤ |a| := by
  by_contra hh
  have hs : |a| < Real.pi / (4 * ε * R) := lt_of_not_ge hh
  have hm := (lt_div_iff₀ (by positivity : 0 < 4 * ε * R)).mp hs
  have hu' := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * ε * |a| by positivity)
  have harg : |2 * ε * a * (γ - T)| < Real.pi / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * ε)]
    nlinarith only [hm, hu']
  have hc : 0 < Real.cos (2 * ε * a * (γ - T)) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp harg)
  have hp : 0 < offAxisSingleContribution ε T γ a :=
    mul_pos (Real.exp_pos _) hc
  linarith only [hneg, hp]

/-- A finite indicator has total mass equal to its cardinality. -/
private theorem tsum_finiteIndicator {ι : Type*} [DecidableEq ι] (F : Finset ι) :
    (∑' q, if q ∈ F then (1 : ℝ) else 0) = F.card := by
  rw [tsum_eq_sum (s := F) (fun q hq => if_neg hq)]
  calc (∑ q ∈ F, if q ∈ F then (1 : ℝ) else 0) = ∑ _q ∈ F, (1 : ℝ) :=
      Finset.sum_congr rfl fun q hq => if_pos hq
    _ = F.card := by simp

/-- Summing a pointwise compensation inequality turns negative local mass
into a lower bound on the number of compensating copies. -/
theorem finite_gaussian_compensation_count {ι : Type*} [DecidableEq ι]
    (target bad : Finset ι) {g w : ι → ℝ} {A κ : ℝ}
    (hg : Summable g) (hw : Summable w)
    (hb : ∀ q, (if q ∈ target then (1 : ℝ) else 0) ≤
      g q + A * (if q ∈ bad then (1 : ℝ) else 0) + κ * w q) :
    (target.card : ℝ) ≤ (∑' q, g q) + A * bad.card + κ * ∑' q, w q := by
  have ht : Summable (fun q => if q ∈ target then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := target) fun q hq => if_neg hq
  have hbad : Summable (fun q => if q ∈ bad then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := bad) fun q hq => if_neg hq
  have hs := Summable.tsum_le_tsum hb ht
    ((hg.add (hbad.mul_left A)).add (hw.mul_left κ))
  rw [tsum_finiteIndicator,
    (hg.add (hbad.mul_left A)).tsum_add (hw.mul_left κ),
    hg.tsum_add (hbad.mul_left A), tsum_mul_left, tsum_mul_left,
    tsum_finiteIndicator] at hs
  exact hs

/-- The explicit compensation radius makes the Lorentzian tail smaller than
one eighth of the prescribed logarithmic multiplicity. -/
theorem gaussian_explicit_radius_tail {h A C c : ℝ}
    (hh : 0 < h) (hA : 0 < A) (hC : 0 < C) (hc : 0 < c) :
    let R := 1 + 2 * Real.pi * h ^ 2 / 3 +
      h * Real.sqrt (2 * Real.log (1 + 16 * A * C / c))
    2 * A * Real.exp (-(R ^ 2 / (2 * h ^ 2))) * C ≤ c / 8 := by
  dsimp only
  let B : ℝ := 1 + 16 * A * C / c
  have hB : 1 < B := by
    have hp : 0 < 16 * A * C / c := by positivity
    dsimp [B]
    linarith only [hp]
  have hlog : 0 < Real.log B := Real.log_pos hB
  have hsqrt : (Real.sqrt (2 * Real.log B)) ^ 2 = 2 * Real.log B :=
    Real.sq_sqrt (by positivity)
  have hbase : 0 ≤ h * Real.sqrt (2 * Real.log B) := by positivity
  have hR : h * Real.sqrt (2 * Real.log B) ≤
      1 + 2 * Real.pi * h ^ 2 / 3 + h * Real.sqrt (2 * Real.log B) := by
    have hp : 0 ≤ 2 * Real.pi * h ^ 2 / 3 := by positivity
    linarith only [hp]
  have hsq := pow_le_pow_left₀ hbase hR 2
  rw [mul_pow, hsqrt] at hsq
  have hratio : Real.log B ≤
      (1 + 2 * Real.pi * h ^ 2 / 3 + h * Real.sqrt (2 * Real.log B)) ^ 2 /
        (2 * h ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * h ^ 2)).mpr
    nlinarith only [hsq]
  have he : Real.exp (-((1 + 2 * Real.pi * h ^ 2 / 3 +
      h * Real.sqrt (2 * Real.log B)) ^ 2 / (2 * h ^ 2))) ≤ 1 / B := by
    calc _ ≤ Real.exp (-Real.log B) := Real.exp_le_exp.mpr (neg_le_neg hratio)
      _ = 1 / B := by rw [Real.exp_neg, Real.exp_log (by linarith only [hB]), one_div]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * A by positivity)) hC.le
  have hlast : 2 * A * (1 / B) * C ≤ c / 8 := by
    have hB0 : 0 < B := by linarith only [hB]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have heq : (2 * A * (1 / B) * C) * 8 = 16 * A * C / B := by ring
    rw [heq]
    apply (div_le_iff₀ hB0).mpr
    dsimp [B]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hc.ne']
    linarith only [hc]
  exact hm.trans hlast

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussian_lorentz_tail_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussian_negative_depth_ge

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussian_explicit_radius_tail
