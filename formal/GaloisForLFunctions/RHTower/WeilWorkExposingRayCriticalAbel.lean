import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalTwists
import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalSeries
import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalAbel

/-!
# A uniform signed Abel ceiling for actual critical separators

Finite positive-integer harmonic twists and signed Abel integration give
one bound uniform in every real frequency. Absolute convergence is paid
from the actual separator, before series and integral are interchanged.
No coefficient signs, full positive completion or Laurent expansion is
assumed. Paper: CRITICAL-ONE-POLE-PROOF.md, preferred section3 proof.
-/

open MeasureTheory Filter Topology Set Real
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilOneSided

/-- The actual cosine-twisted coefficients in the standard Dirichlet normalization. -/
def criticalCosineCoeff (b : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  b n*Real.sqrt n*Real.cos (t*Real.log n)

/-- Real part of the actual absolutely convergent series at 1/2+s+i*t. -/
def criticalCosineSeries (b : ℕ → ℝ) (s t : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then criticalCosineCoeff b t n else 0)*(n : ℝ)^(-(1+s))

/-- The positive harmonic Dirichlet factor. -/
def criticalHarmonicFactor (s : ℝ) : ℝ := ∑' m : ℕ, (m : ℝ)^(-(1+s))

private theorem criticalCosineTerm_norm_le (b : ℕ → ℝ) (s t : ℝ) (n : ℕ) :
    ‖(if 2 ≤ n then criticalCosineCoeff b t n else 0)*(n : ℝ)^(-(1+s))‖ ≤
      |b n| / (n : ℝ)^(1/2+s) := by
  by_cases hn : 2 ≤ n
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have he : Real.sqrt n*(n : ℝ)^(-(1+s))=1/(n : ℝ)^(1/2+s) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add hn0]
      rw [show (1/2 : ℝ)+(-(1+s))=-(1/2+s) by ring,Real.rpow_neg hn0.le]
      simp only [one_div]
    simp only [if_pos hn,criticalCosineCoeff,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    calc
      _ ≤ |b n| * Real.sqrt n*1*(n : ℝ)^(-(1+s)) := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = |b n| / (n : ℝ)^(1/2+s) := by rw [mul_one,mul_assoc,he]; ring
  · simp only [if_neg hn,zero_mul,norm_zero]
    positivity

/-- Absolute convergence of every actual twisted coefficient series. -/
theorem summable_critical_cosine_terms
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable fun n : ℕ =>
      ‖(if 2 ≤ n then criticalCosineCoeff b t n else 0)*(n : ℝ)^(-(1+s))‖ := by
  exact (summable_critical_separator_coefficients h (by linarith : 1/2 < 1/2+s)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (criticalCosineTerm_norm_le b s t)

/-- The weight of one integer-product pair in the harmonic cumulative sum. -/
def criticalPairWeight (lam : ℕ → ℝ) (q : ℕ × ℕ) : ℝ :=
  if 2 ≤ q.1 ∧ 1 ≤ q.2 then lam q.1 / ((q.1 : ℝ) * q.2) else 0

def criticalPairLevel (q : ℕ × ℕ) : ℝ := log ((q.1 : ℝ) * q.2)

private theorem criticalPairLevel_nonneg (q : ℕ × ℕ) : 0 ≤ criticalPairLevel q := by
  by_cases hn : q.1 = 0
  · simp [criticalPairLevel, hn]
  by_cases hm : q.2 = 0
  · simp [criticalPairLevel, hm]
  apply Real.log_nonneg
  have hn1 : (1:ℝ) ≤ q.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hm1 : (1:ℝ) ≤ q.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  nlinarith

/-- The cumulative function is exactly the finite harmonic density already bounded by resonators. -/
private theorem criticalPair_cumulative (lam : ℕ → ℝ) (t : ℝ) :
    WeilWorkPBAP.signedCumulative (criticalPairWeight lam) criticalPairLevel t =
      signedHarmonicDensity lam ⌊exp t⌋₊ := by
  classical
  let N := ⌊exp t⌋₊
  have hcut (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) :
      log ((n:ℝ)*m) ≤ t ↔ n*m ≤ N := by
    have hpos : 0 < (n:ℝ)*m := mul_pos (by exact_mod_cast (by omega : 0 < n))
      (by exact_mod_cast (by omega : 0 < m))
    rw [Real.log_le_iff_le_exp hpos, Nat.le_floor_iff (exp_pos t).le]
    norm_cast
  rw [WeilWorkPBAP.signedCumulative, tsum_eq_sum (s := (Finset.Icc 2 N).product (Finset.Icc 1 N))]
  · refine (Finset.sum_product (Finset.Icc 2 N) (Finset.Icc 1 N)
      (fun q : ℕ × ℕ => if criticalPairLevel q ≤ t then criticalPairWeight lam q else 0)).trans ?_
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    simp only [criticalPairWeight, criticalPairLevel,
      (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hm).1, and_self, if_true]
    simp only [hcut n m (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1, N]
  · rintro ⟨n,m⟩ hq
    by_cases hn : 2 ≤ n
    · by_cases hm : 1 ≤ m
      · have hnmlt : ¬ n*m ≤ N := by
          intro hnm
          have hnN : n ≤ N := by nlinarith [Nat.mul_le_mul_left n hm]
          have hmN : m ≤ N := by
            nlinarith [Nat.mul_le_mul_right m (show 1 ≤ n by omega)]
          exact hq (Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨hn,hnN⟩, Finset.mem_Icc.mpr ⟨hm,hmN⟩⟩)
        simp only [criticalPairLevel, (hcut n m hn hm), if_neg hnmlt]
      · simp [criticalPairWeight, hm]
    · simp [criticalPairWeight, hn]

/-- Individual pair transform, including the zero indices. -/
private theorem criticalPair_transform (lam : ℕ → ℝ) {s : ℝ} (hs : 0 < s) (q : ℕ × ℕ) :
    criticalPairWeight lam q * exp (-s*criticalPairLevel q) =
      ((if 2 ≤ q.1 then lam q.1 else 0) * (q.1 : ℝ)^(-(1+s))) *
        (q.2 : ℝ)^(-(1+s)) := by
  rcases q with ⟨n,m⟩
  by_cases hn : 2 ≤ n
  · by_cases hm : 1 ≤ m
    · have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hmpos : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
      have he : exp (-s * log ((n:ℝ)*m)) = ((n:ℝ)*m)^(-s) := by
        rw [Real.rpow_def_of_pos (mul_pos hnpos hmpos)]
        congr 1
        ring
      simp only [criticalPairWeight, criticalPairLevel, hn, hm, and_self, if_true]
      rw [he, Real.mul_rpow hnpos.le hmpos.le,
        show -(1+s) = (-1:ℝ)+(-s) by ring,
        Real.rpow_add hnpos, Real.rpow_add hmpos, Real.rpow_neg_one, Real.rpow_neg_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · have hm0 : m=0 := by omega
      subst m
      have hzpow : (0:ℝ)^(-(1+s)) = 0 := Real.zero_rpow (by linarith : -(1+s) ≠ 0)
      simp only [Nat.cast_zero, hzpow, mul_zero]
      simp [criticalPairWeight]
  · simp [criticalPairWeight, hn]


private theorem criticalPair_summable
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable fun q : ℕ × ℕ =>
      |criticalPairWeight (criticalCosineCoeff b t) q| * exp (-s*criticalPairLevel q) := by
  have hn := summable_critical_cosine_terms h hs t
  have hm : Summable fun m : ℕ => (m : ℝ)^(-(1+s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hp := hn.mul_of_nonneg hm.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply hp.congr
  intro q
  have he := congrArg norm (criticalPair_transform (criticalCosineCoeff b t) hs q)
  simpa only [norm_mul,Real.norm_eq_abs,abs_of_pos (exp_pos _)] using he.symm

private theorem criticalPair_tsum
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (∑' q : ℕ × ℕ, criticalPairWeight (criticalCosineCoeff b t) q * exp (-s*criticalPairLevel q)) =
      criticalCosineSeries b s t*criticalHarmonicFactor s := by
  have hn := summable_critical_cosine_terms h hs t
  have hm : Summable fun m : ℕ => (m : ℝ)^(-(1+s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simp_rw [criticalPair_transform (criticalCosineCoeff b t) hs]
  exact (tsum_mul_tsum_of_summable_norm hn hm.norm).symm

/-- A single source-derived Abel ceiling for every positive damping and every
real twist. The coefficient sequence may have arbitrary signs. -/
theorem critical_cosine_dirichlet_product_ceiling
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 < s → ∀ t : ℝ,
      s^2*(criticalCosineSeries b s t*criticalHarmonicFactor s) ≤ K*(2+s^2) := by
  obtain ⟨C,hC,hceil⟩ := critical_harmonic_cosine_ceiling h
  refine ⟨2*C,by positivity,fun s hs t => ?_⟩
  have hu : ∀ y : ℝ, 0 ≤ y →
      WeilWorkPBAP.signedCumulative (criticalPairWeight (criticalCosineCoeff b t))
        criticalPairLevel y ≤ (2*C)*y^2+2*C := by
    intro y hy
    rw [criticalPair_cumulative]
    have hN : 1 ≤ ⌊exp y⌋₊ :=
      (Nat.le_floor_iff (exp_pos y).le).mpr (by simpa using Real.one_le_exp_iff.mpr hy)
    have hlog0 : 0 ≤ log (⌊exp y⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlog : log (⌊exp y⌋₊ : ℝ) ≤ y :=
      (Real.log_le_iff_le_exp (by exact_mod_cast (by omega : 0 < ⌊exp y⌋₊))).mpr
        (Nat.floor_le (exp_pos y).le)
    have hh := hceil ⌊exp y⌋₊ hN t
    change signedHarmonicDensity (criticalCosineCoeff b t) ⌊exp y⌋₊ ≤ _ at hh
    have hsq : (1+log (⌊exp y⌋₊ : ℝ))^2 ≤ 2*(y^2+1) := by nlinarith [sq_nonneg (y-1)]
    have hm := mul_le_mul_of_nonneg_left hsq hC
    linarith
  have hc := WeilWorkPBAP.signedCumulative_laplace_ceiling
    (criticalPairWeight (criticalCosineCoeff b t)) criticalPairLevel hs
    (show 0 ≤ 2*C by positivity) (show 0 ≤ 2*C by positivity)
    criticalPairLevel_nonneg (criticalPair_summable h hs t) hu
  rw [criticalPair_tsum h hs t] at hc
  have hh := mul_le_mul_of_nonneg_left hc (pow_pos hs 3).le
  field_simp [hs.ne'] at hh
  nlinarith only [hh]

end RHTower.ExposingRayTransfer
