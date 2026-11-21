import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.BinaryBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Time scale attainable by the repeated-word error certificate -/
open Filter
namespace GaloisForLFunctions.HTGeometry.IncrementClocks

/-- The sufficient error and gate inequalities of the product formula can
certify at most this amount of integrated time, at every order. -/
theorem certified_increment_mass_bound (j q m P : ℕ) (hq : 0 < q) (M t : ℝ) (hM : 0 ≤ M)
    (ht : 7^j*(1+M)*|t| ≤ (q:ℝ)^(j+1)/100)
    (hcost : 2*(q^(j+2)*(3^j*m)) ≤ P) :
    200*(1+M)*|t| * (m:ℝ) ≤ P := by
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hcost' : 2*((q:ℝ)^(j+2)*(3^j*(m:ℝ))) ≤ P := by exact_mod_cast hcost
  have hsmall : (1+M)*|t| ≤ 7^j*((1+M)*|t|) :=
    le_mul_of_one_le_left (mul_nonneg (by linarith only [hM]) (abs_nonneg _)) (one_le_pow₀ (by norm_num))
  have htime : 100*((1+M)*|t|) ≤ (q:ℝ)^(j+1) := by
    have h := (le_div_iff₀ (by norm_num)).mp ht
    linarith only [h,hsmall]
  have hg : (q:ℝ)^(j+1) ≤ (q:ℝ)^(j+2)*3^j :=
    (pow_le_pow_right₀ hq' (by omega : j+1 ≤ j+2)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
  calc
    _ = 2*((100*((1+M)*|t|))*(m:ℝ)) := by ring
    _ ≤ 2*((q:ℝ)^(j+2)*3^j*m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (htime.trans hg) (by positivity)) (by norm_num)
    _ ≤ _ := by simpa only [mul_assoc] using hcost'

/-- The logarithm to base two of the constructed width, divided by qubit
count, tends to one. -/
theorem crossingWidth_exponent_ratio :
    Tendsto (fun N : ℕ => Real.logb 2 (crossingWidth N)/N) atTop (nhds 1) := by
  simp only [crossingWidth,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a : ℕ,ha⟩ := exists_nat_gt (26/ε)
  let b := max 27 a
  refine ⟨b*b,?_⟩
  intro N hN
  have hbs : b ≤ N.sqrt := Nat.le_sqrt.mpr hN
  have hs : 27 ≤ N.sqrt := (le_max_left ..).trans hbs
  have ha' : a ≤ N.sqrt := (le_max_right ..).trans hbs
  have hs' : (0:ℝ) < N.sqrt := by exact_mod_cast (show 0<N.sqrt by omega)
  have hNs := Nat.sqrt_le' N
  have hmul := Nat.mul_le_mul_right N.sqrt (show 26 ≤ N.sqrt by omega)
  have hsub : 26*N.sqrt ≤ N := by nlinarith only [hmul,hNs]
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hsq : (N.sqrt:ℝ)^2 ≤ N := by exact_mod_cast hNs
  have hgap : 26 < ε*(N.sqrt:ℝ) := by
    have ha'' : (a:ℝ) ≤ N.sqrt := by exact_mod_cast ha'
    linarith only [(div_lt_iff₀ hε).mp (ha.trans_le ha'')]
  rw [Real.dist_eq,Nat.cast_sub hsub,Nat.cast_mul,Nat.cast_ofNat,div_sub_one hNr.ne',show (N:ℝ)-26*(N.sqrt:ℝ)-N = -(26*(N.sqrt:ℝ)) by ring,
    abs_div,abs_neg,abs_of_pos hNr,abs_of_nonneg (by positivity : 0 ≤ 26*(N.sqrt:ℝ))]
  apply (div_lt_iff₀ hNr).mpr
  nlinarith only [mul_lt_mul_of_pos_right hgap hs',mul_le_mul_of_nonneg_left hsq hε.le]

#print axioms certified_increment_mass_bound
#print axioms crossingWidth_exponent_ratio
end GaloisForLFunctions.HTGeometry.IncrementClocks
