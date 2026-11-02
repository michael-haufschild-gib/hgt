import GaloisForLFunctions.RenormalizedIntersectionTheory.FinitePrimeRemovalHasBoundedHarmonicError
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheZeroDensityTwinCarriesTheConductorSeries
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheSparseFlipHasAnEventuallyPositiveHarmonicMean
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger

/-!
# Uniformly bounded fixed-scale harmonic defect

Finite prime removal has bounded additive error. On a smooth fibre indexed by
`a`, moving the horizon from `N` to `N/a` costs only `O(1 + log a)`. The smooth
reciprocal logarithmic second moment is finite, so the total squared defect at
any fixed prime cutoff is bounded independently of the horizon.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- The reciprocal logarithmic second moment of a fixed smooth sector is finite,
uniformly over all finite integer horizons. -/
theorem exists_sum_smoothSet_log_sq_div_le (T : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      ∑ a ∈ smoothSet T N, (1 + Real.log a) ^ (2 : ℕ) / a ≤ K := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invSqrtHom p‖ < 1 := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    change ‖(p : ℝ) ^ (-(1 / 2 : ℝ))‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  obtain ⟨_, hhas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := invSqrtHom) hlt T
  let K := ∑' m : Nat.smoothNumbers T, invSqrtHom m
  have hK : 0 ≤ K := tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨36 * K, mul_nonneg (by norm_num) hK, fun N => ?_⟩
  have hterm (a : ℕ) (ha : a ∈ smoothSet T N) :
      (1 + Real.log a) ^ (2 : ℕ) / a ≤ 36 * invSqrtHom a := by
    have ha1 := (mem_smoothSet.mp ha).1
    rcases eq_or_ne a 1 with rfl | haone
    · norm_num [invSqrtHom]
    have ha2 : 2 ≤ a := by omega
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hlog := Real.log_natCast_nonneg a
    have hsq : (1 + Real.log a) ^ (2 : ℕ) ≤ 36 * Real.sqrt a := by
      refine (pow_le_pow_left₀ (by linarith only [hlog])
        (show 1 + Real.log a ≤ Real.log a + 2 by linarith) 2).trans
        (RHTower.sq_log_add_two_le ha2)
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
    calc
      _ ≤ 36 * Real.sqrt a / a := div_le_div_of_nonneg_right hsq ha0.le
      _ = 36 * invSqrtHom a := by
        change _ = 36 * (a : ℝ) ^ (-(1 / 2 : ℝ))
        rw [Real.rpow_neg ha0.le, ← Real.sqrt_eq_rpow]
        field_simp [ha0.ne', hs.ne']
        nlinarith only [Real.sq_sqrt ha0.le]
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hinj : ∀ a ∈ smoothSet T N, a ∈ Nat.smoothNumbers T := by
    intro a ha
    obtain ⟨ha1, _, hap⟩ := mem_smoothSet.mp ha
    exact Nat.mem_smoothNumbers'.mpr fun p hp hpa =>
      hap p (Nat.mem_primeFactors.mpr ⟨hp, hpa, by omega⟩)
  calc
    ∑ a ∈ smoothSet T N, invSqrtHom a =
        ∑ m ∈ (smoothSet T N).subtype (· ∈ Nat.smoothNumbers T), invSqrtHom m := by
      rw [sum_subtype_of_mem (f := fun a => invSqrtHom a) hinj]
    _ ≤ K := hhas.summable.sum_le_tsum _ fun m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem abs_harmonicMean_le_ordinary {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    (N : ℕ) : |gaugeHarmonicSum ω N| ≤ gaugeHarmonicSum (fun _ => 1) N := by
  refine (abs_gaugeHarmonicSum_le_absHarmonic ω N).trans ?_
  change (∑ n ∈ Icc 1 N, |ω n| / n) ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ)
  exact sum_le_sum fun n _ => div_le_div_of_nonneg_right (hbd n) (Nat.cast_nonneg n)

/-- At a fixed prime cutoff, each fibre differs from its Euler-normalized global
mean by at most a constant times `1 + log a`, with no density assumption. -/
theorem exists_fixedScale_fibre_error_le_log (P : Set ℕ) (T : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N a : ℕ, 1 ≤ a → a ≤ N →
      |gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        (gaugeHarmonicSum (primeSetFlip P) N /
          gaugeHarmonicSum (fun _ => 1) N / flipDensityBelow (primeSetFlip P) T) *
            roughHarmonic T (N / a)| ≤ K * (1 + Real.log a) := by
  let ω := primeSetFlip P
  let Hω := ∏ p ∈ Nat.primesBelow T, (1 - ω p / p)
  let H₁ := ∏ p ∈ Nat.primesBelow T, (1 - 1 / (p : ℝ))
  let δ := flipDensityBelow ω T
  have hbd : ∀ n, |ω n| ≤ 1 := abs_primeSetFlip_le P
  have hδ : 0 < δ := (flipDensityBelow_pos_le_one hbd T).1
  have hhead : Hω * δ = H₁ := by
    simpa only [one_mul] using mul_flipDensityBelow hbd 1 T
  obtain ⟨C, hC, hCerr⟩ := exists_abs_roughMean_sub_eulerHead_mul_le
    (fun _ _ hm hn => (primeSetFlip_isSignGauge P).mul hm hn) hbd T
  obtain ⟨D, hD, hDerr⟩ := exists_abs_roughMean_sub_eulerHead_mul_le
    (ω := fun _ => 1) (fun _ _ _ _ => by ring) (fun _ => by norm_num) T
  let B := C + D / δ
  let b := 2 * |Hω|
  let c := 2 + Real.log 2
  let K := B + b * c
  have hB : 0 ≤ B := add_nonneg hC (div_nonneg hD hδ.le)
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (abs_nonneg _)
  have hc : 1 ≤ c := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    dsimp only [c]
    linarith only [h]
  have hK : 0 ≤ K := add_nonneg hB (mul_nonneg hb (zero_le_one.trans hc))
  have hbK : b ≤ K := by
    have h := mul_le_mul_of_nonneg_left hc hb
    dsimp only [K]
    linarith only [h, hB]
  refine ⟨K, hK, fun N a ha haN => ?_⟩
  have hN : 1 ≤ N := ha.trans haN
  let HN := gaugeHarmonicSum (fun _ => 1) N
  let r := gaugeHarmonicSum ω N / HN
  have hHN : 0 < HN := by
    have h := one_le_roughHarmonic 0 hN
    rw [← gaugeHarmonicSum_roughGauge_one, roughGauge_zero] at h
    exact zero_lt_one.trans_le h
  have hr : |r| ≤ 1 := by
    rw [abs_div, abs_of_pos hHN, div_le_one hHN]
    exact abs_harmonicMean_le_ordinary hbd N
  have hrHN : r * HN = gaugeHarmonicSum ω N := div_mul_cancel₀ _ hHN.ne'
  have hfactor : (r / δ) * H₁ = r * Hω := by
    rw [← hhead]
    field_simp [hδ.ne']
  have hSdiff := abs_gaugeHarmonicSum_sub_natDiv_le hbd ha N
  have hHdiff := abs_gaugeHarmonicSum_sub_natDiv_le
    (ω := fun _ => 1) (fun _ => by norm_num) ha N
  have hDerror := hDerr (N / a)
  rw [gaugeHarmonicSum_roughGauge_one] at hDerror
  have hsecond : |Hω * (gaugeHarmonicSum ω (N / a) - gaugeHarmonicSum ω N)| ≤
      |Hω| * (2 + Real.log (2 * a)) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hSdiff (abs_nonneg _)
  have hthird : |r * Hω * (HN - gaugeHarmonicSum (fun _ => 1) (N / a))| ≤
      |Hω| * (2 + Real.log (2 * a)) := by
    rw [abs_mul, abs_mul]
    have h := mul_le_mul hr hHdiff (abs_nonneg _) zero_le_one
    have hw := mul_le_mul_of_nonneg_left h (abs_nonneg Hω)
    nlinarith only [hw]
  have hfourth : |(r / δ) * (roughHarmonic T (N / a) -
      H₁ * gaugeHarmonicSum (fun _ => 1) (N / a))| ≤ D / δ := by
    rw [abs_mul, abs_div, abs_of_pos hδ]
    have h := mul_le_mul hr hDerror (abs_nonneg _) zero_le_one
    have hw := div_le_div_of_nonneg_right h hδ.le
    simpa only [one_mul, div_mul_eq_mul_div] using hw
  have heq : gaugeHarmonicSum (roughGauge T ω) (N / a) - (r / δ) * roughHarmonic T (N / a) =
      (gaugeHarmonicSum (roughGauge T ω) (N / a) - Hω * gaugeHarmonicSum ω (N / a)) +
      Hω * (gaugeHarmonicSum ω (N / a) - gaugeHarmonicSum ω N) +
      r * Hω * (HN - gaugeHarmonicSum (fun _ => 1) (N / a)) -
      (r / δ) * (roughHarmonic T (N / a) - H₁ * gaugeHarmonicSum (fun _ => 1) (N / a)) := by
    have hcancel := congrArg (Hω * ·) hrHN
    have hfactor' := congrArg (· * gaugeHarmonicSum (fun _ => 1) (N / a)) hfactor
    nlinarith only [hcancel, hfactor']
  change |gaugeHarmonicSum (roughGauge T ω) (N / a) -
    (r / δ) * roughHarmonic T (N / a)| ≤ _
  have hraw : |gaugeHarmonicSum (roughGauge T ω) (N / a) -
      (r / δ) * roughHarmonic T (N / a)| ≤ B + b * (2 + Real.log (2 * a)) := by
    rw [heq]
    let x := gaugeHarmonicSum (roughGauge T ω) (N / a) - Hω * gaugeHarmonicSum ω (N / a)
    let y := Hω * (gaugeHarmonicSum ω (N / a) - gaugeHarmonicSum ω N)
    let z := r * Hω * (HN - gaugeHarmonicSum (fun _ => 1) (N / a))
    let w := (r / δ) * (roughHarmonic T (N / a) - H₁ * gaugeHarmonicSum (fun _ => 1) (N / a))
    have htriangle := (abs_sub (x + y + z) w).trans
      (add_le_add ((abs_add_le (x + y) z).trans (add_le_add (abs_add_le x y) le_rfl)) le_rfl)
    have herr := add_le_add (add_le_add (add_le_add (hCerr (N / a)) hsecond) hthird) hfourth
    exact htriangle.trans (herr.trans_eq (by dsimp only [B, b]; ring))
  have hloga : 0 ≤ Real.log a := Real.log_natCast_nonneg a
  have hlogmul : Real.log (2 * (a : ℝ)) = Real.log 2 + Real.log a :=
    Real.log_mul (by norm_num) (by exact_mod_cast (show a ≠ 0 by omega))
  refine hraw.trans ?_
  rw [hlogmul]
  have h := mul_le_mul_of_nonneg_right hbK hloga
  dsimp only [K, c] at ⊢ h
  nlinarith only [h]

/-- Every prime flip has uniformly bounded squared fixed-scale defect. Density
assumptions enter only when comparing this bound with the growing global correlation. -/
theorem exists_fixedScaleDefect_le_constant (P : Set ℕ) (T : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ a ∈ smoothSet T N,
        (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
          (gaugeHarmonicSum (primeSetFlip P) N /
            gaugeHarmonicSum (fun _ => 1) N / flipDensityBelow (primeSetFlip P) T) *
              roughHarmonic T (N / a)) ^ (2 : ℕ) / (a * roughHarmonic T (N / a)) ≤ K := by
  obtain ⟨A, _, hfibre⟩ := exists_fixedScale_fibre_error_le_log P T
  obtain ⟨B, hB, hmoment⟩ := exists_sum_smoothSet_log_sq_div_le T
  refine ⟨A ^ (2 : ℕ) * B, mul_nonneg (sq_nonneg _) hB, fun N _ => ?_⟩
  have hterm (a : ℕ) (ha : a ∈ smoothSet T N) :
      (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        (gaugeHarmonicSum (primeSetFlip P) N /
          gaugeHarmonicSum (fun _ => 1) N / flipDensityBelow (primeSetFlip P) T) *
            roughHarmonic T (N / a)) ^ (2 : ℕ) / (a * roughHarmonic T (N / a)) ≤
          A ^ (2 : ℕ) * ((1 + Real.log a) ^ (2 : ℕ) / a) := by
    obtain ⟨ha1, haN, _⟩ := mem_smoothSet.mp ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hY : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hR := one_le_roughHarmonic T hY
    have h := pow_le_pow_left₀ (abs_nonneg _) (hfibre N a ha1 haN) 2
    rw [sq_abs, mul_pow] at h
    let E := gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
      (gaugeHarmonicSum (primeSetFlip P) N /
        gaugeHarmonicSum (fun _ => 1) N / flipDensityBelow (primeSetFlip P) T) *
          roughHarmonic T (N / a)
    change E ^ (2 : ℕ) / (a * roughHarmonic T (N / a)) ≤ _
    calc
      E ^ (2 : ℕ) / (a * roughHarmonic T (N / a)) =
          (E ^ (2 : ℕ) / roughHarmonic T (N / a)) / a := by ring
      _ ≤ E ^ (2 : ℕ) / a :=
        div_le_div_of_nonneg_right (div_le_self (sq_nonneg E) hR) ha0.le
      _ ≤ (A ^ (2 : ℕ) * (1 + Real.log a) ^ (2 : ℕ)) / a :=
        div_le_div_of_nonneg_right h ha0.le
      _ = _ := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (hmoment N) (sq_nonneg _)

/-- Fixed-scale smooth projection differs from the Euler-normalized finite flip
by a uniformly bounded vector, for every prime pattern. -/
theorem exists_fixedScale_projection_error_le_constant (P : Set ℕ) {T : ℕ} (hT : 1 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ‖(smoothFibreSpace T N).starProjection (gaugeVector N (fun n => primeSetFlip P n -
        (harmonicCorrelation (primeSetFlip P) N / flipDensityBelow (primeSetFlip P) T) *
          finiteFlip (primeSetCutoff P (T - 1)) n))‖ ^ (2 : ℕ) ≤ K := by
  obtain ⟨K, hK, hdef⟩ := exists_fixedScaleDefect_le_constant P T
  refine ⟨K, hK, fun N hN => ?_⟩
  let μ := harmonicCorrelation (primeSetFlip P) N / flipDensityBelow (primeSetFlip P) T
  let f := fun n => primeSetFlip P n - μ * finiteFlip (primeSetCutoff P (T - 1)) n
  let M := ∑ a ∈ smoothSet T N,
    (∑ b ∈ roughInterval T (N / a), f (a * b) / b) ^ (2 : ℕ) /
      (a * roughHarmonic T (N / a))
  have hM : M ≤ K := by
    have heq : M = ∑ a ∈ smoothSet T N,
        (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
          μ * roughHarmonic T (N / a)) ^ (2 : ℕ) / (a * roughHarmonic T (N / a)) := by
      apply sum_congr rfl
      intro a ha
      dsimp only [f]
      rw [fibreSum_twin_sub_finiteFlip P hT μ ha, mul_pow,
        show primeSetFlip P a ^ (2 : ℕ) = 1 by rw [sq]; exact primeSetFlip_mul_self P a,
        one_mul]
    rw [heq]
    exact hdef N hN
  have hinner : ∀ v ∈ smoothFibreSpace T N, ⟪gaugeVector N f, v⟫ ^ (2 : ℕ) ≤
      K * ‖v‖ ^ (2 : ℕ) := by
    intro v hv
    have h := inner_sq_le_of_mem_smoothFibreSpace f hv
    change ⟪gaugeVector N f, v⟫ ^ (2 : ℕ) ≤ ‖v‖ ^ (2 : ℕ) * M at h
    exact h.trans ((mul_le_mul_of_nonneg_left hM (sq_nonneg _)).trans_eq (by ring))
  exact norm_starProjection_sq_le (gaugeVector N f) hK hinner

/-- At zero prime density the bounded fixed-scale defect is negligible relative
to the global squared harmonic correlation mass. -/
theorem eventually_zeroDensity_fixedScaleDefect_le (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∑ a ∈ smoothSet T N,
        (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
          (harmonicCorrelation (primeSetFlip P) N / flipDensityBelow (primeSetFlip P) T) *
            roughHarmonic T (N / a)) ^ (2 : ℕ) / (a * roughHarmonic T (N / a)) ≤
        ε * gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) /
          gaugeHarmonicSum (fun _ => 1) N := by
  obtain ⟨K, hK, hdef⟩ := exists_fixedScaleDefect_le_constant P T
  have hlim := tendsto_sparse_signedMean_div_log_rpow_atTop P hP
    (show (1 / 2 : ℝ) < 1 by norm_num)
  filter_upwards [hlim.eventually (eventually_ge_atTop (Real.sqrt (2 * K / ε))),
    eventually_ge_atTop (3 : ℕ)] with N hbig hN
  have hL : 0 < Real.log N := zero_lt_one.trans_le (one_le_log_of_three_le hN)
  have hH : 0 < gaugeHarmonicSum (fun _ => 1) N :=
    gaugeHarmonicSum_one_pos (by omega)
  have hHu : gaugeHarmonicSum (fun _ => 1) N ≤ 2 * Real.log N := by
    have h := (abs_le.mp (abs_harmonic_sub_log_le N)).2
    linarith only [h, one_le_log_of_three_le hN]
  have hS : Real.sqrt (2 * K / ε) * Real.log N ^ (1 / 2 : ℝ) ≤
      gaugeHarmonicSum (primeSetFlip P) N :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).mp hbig
  have hsq := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg hL.le _)) hS 2
  have hpower : (Real.log N ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = Real.log N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  rw [mul_pow, Real.sq_sqrt (by positivity), hpower] at hsq
  have hpaid := mul_le_mul_of_nonneg_left hsq hε.le
  have hpaid' : 2 * K * Real.log N ≤ ε * gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) := by
    have heq : ε * ((2 * K / ε) * Real.log N) = 2 * K * Real.log N := by
      field_simp [hε.ne']
    rwa [heq] at hpaid
  refine (hdef N (by omega)).trans ?_
  rw [le_div_iff₀ hH]
  exact (mul_le_mul_of_nonneg_left hHu hK).trans (by simpa only [mul_assoc, mul_left_comm] using hpaid')

end GaloisForLFunctions.RenormalizedIntersectionTheory
