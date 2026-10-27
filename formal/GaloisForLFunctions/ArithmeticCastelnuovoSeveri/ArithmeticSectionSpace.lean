import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch

/-!
# Independently varying arithmetic sections

An arithmetic section is a sum `Σ g_n(u − log n)` of independently varying smooth profiles
supported in a common short interval. Below the integer-log spacing, prime lags read precisely
the Hecke incidence pairing of the profiles. Mixed archimedean correlations are controlled by
their separate square masses, so the source estimates apply to the whole linear section space.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- A smooth section with an independent profile at each arithmetic point `log n`. -/
def arithmeticSection (N : ℕ) (g : ℕ → ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, g n (u - Real.log n)

/-- The square mass of one local section. -/
def sectionMass (g : ℝ → ℝ) : ℝ := ∫ u, g u ^ 2

/-- The mixed correlation of two local sections. -/
def sectionCorr (g h : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u, g u * h (u + t)

variable {g h : ℝ → ℝ} {w : ℝ}

theorem sectionMass_nonneg (g : ℝ → ℝ) : 0 ≤ sectionMass g :=
  integral_nonneg fun _ => sq_nonneg _

theorem profile_hasCompactSupport (hs : ∀ u, u ∉ Set.Icc 0 w → g u = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro isCompact_Icc hs

theorem integrable_section_product (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (a b : ℝ) :
    Integrable fun u => g (u - a) * h (u + b) :=
  ((hg.comp (continuous_sub_right a)).mul
    (hh.comp (continuous_add_const b))).integrable_of_hasCompactSupport
      (hgc.comp_homeomorph (Homeomorph.subRight a)).mul_right

/-- Young's inequality bounds a mixed correlation by the two independent masses. -/
theorem abs_sectionCorr_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) (t : ℝ) :
    |sectionCorr g h t| ≤ (sectionMass g + sectionMass h) / 2 := by
  have h1 := integrable_sq_of_continuous hg hgc
  have h2 : Integrable fun u => h (u + t) ^ 2 :=
    (integrable_sq_of_continuous hh hhc).comp_add_right t
  have h3 : Integrable fun u => g u * h (u + t) := by
    simpa only [sub_zero] using integrable_section_product hg hgc hh 0 t
  calc |sectionCorr g h t| ≤ ∫ u, |g u * h (u + t)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (g u ^ 2 + h (u + t) ^ 2) / 2 := by
      refine integral_mono h3.abs ((h1.add h2).div_const 2) fun u => ?_
      rw [abs_mul]
      nlinarith only [sq_nonneg (|g u| - |h (u + t)|), sq_abs (g u), sq_abs (h (u + t))]
    _ = (sectionMass g + sectionMass h) / 2 := by
      rw [integral_div, integral_add h1 h2,
        integral_add_right_eq_self (fun u => h u ^ 2) t]
      rfl

theorem sectionCorr_eq_zero (hg : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hh : ∀ u, u ∉ Set.Icc 0 w → h u = 0) {t : ℝ} (ht : w < |t|) :
    sectionCorr g h t = 0 := by
  have hp : ∀ u, g u * h (u + t) = 0 := by
    intro u
    by_cases hu : u ∈ Set.Icc 0 w
    · by_cases hut : u + t ∈ Set.Icc 0 w
      · have : |t| ≤ w := abs_le.mpr
          ⟨by linarith only [hu.2, hut.1], by linarith only [hu.1, hut.2]⟩
        exact (not_lt_of_ge this ht).elim
      · rw [hh _ hut, mul_zero]
    · rw [hg _ hu, zero_mul]
  simp only [sectionCorr, hp, integral_zero]

theorem sectionCorr_zero_self (g : ℝ → ℝ) : sectionCorr g g 0 = sectionMass g := by
  simp only [sectionCorr, sectionMass, add_zero, ← pow_two]

theorem sectionCorr_zero_comm (g h : ℝ → ℝ) : sectionCorr g h 0 = sectionCorr h g 0 := by
  simp only [sectionCorr, add_zero, mul_comm]

variable {G : ℕ → ℝ → ℝ}

theorem contDiff_arithmeticSection (hg : ∀ n, ContDiff ℝ 2 (G n)) (N : ℕ) :
    ContDiff ℝ 2 (arithmeticSection N G) :=
  ContDiff.sum fun n _ => (hg n).comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_arithmeticSection
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (N : ℕ) :
    HasCompactSupport (arithmeticSection N G) := by
  refine HasCompactSupport.intro (K := Set.Icc 0 (Real.log N + w)) isCompact_Icc ?_
  intro u hu
  refine sum_eq_zero fun n hn => ?_
  have hn1 := (mem_Icc.mp hn).1
  have hlog0 := Real.log_natCast_nonneg n
  have hlogN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (mem_Icc.mp hn).2)
  apply hs n
  intro hm
  exact hu ⟨by linarith only [hm.1, hlog0], by linarith only [hm.2, hlogN]⟩

/-- Finite mixed-correlation expansion, retaining each profile. -/
theorem integral_arithmeticSection_mul_shift (hg : ∀ n, Continuous (G n))
    (hgc : ∀ n, HasCompactSupport (G n)) (N : ℕ) (y : ℝ) :
    ∫ u, arithmeticSection N G u * arithmeticSection N G (u + y) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, sectionCorr (G m) (G n) (y - logGap m n) := by
  have hp : ∀ u, arithmeticSection N G u * arithmeticSection N G (u + y) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        G m (u - Real.log m) * G n (u + (y - Real.log n)) := by
    intro u
    simp only [arithmeticSection, sum_mul_sum]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by
      rw [show u + y - Real.log n = u + (y - Real.log n) by ring]
  simp_rw [hp]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    integrable_section_product (hg m) (hgc m) (hg n) _ _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => integrable_section_product (hg m) (hgc m) (hg n) _ _]
  refine sum_congr rfl fun n _ => ?_
  rw [sectionCorr, ← integral_sub_right_eq_self
    (fun v => G m v * G n (v + (y - logGap m n))) (Real.log m)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show u - Real.log m + (y - logGap m n) = u + (y - Real.log n) by
    simp only [logGap]; ring]

/-- The arithmetic supports are disjoint, so their square masses add exactly. -/
theorem integral_arithmeticSection_sq (hg : ∀ n, Continuous (G n))
    (hgc : ∀ n, HasCompactSupport (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    ∫ u, arithmeticSection N G u ^ 2 = ∑ n ∈ Icc 1 N, sectionMass (G n) := by
  have he := integral_arithmeticSection_mul_shift hg hgc N 0
  simp only [add_zero, ← pow_two] at he
  rw [he]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_eq_single m]
  · simp only [logGap, sub_self, sectionCorr_zero_self]
  · intro n hn hnm
    apply sectionCorr_eq_zero (hs m) (hs n)
    rw [zero_sub, abs_neg]
    exact hw.trans_le (atomSpacing_le_abs_logGap hm hn hnm.symm)
  · exact fun h => (h hm).elim

theorem atomSpacing_le_abs_log_sub_of_min {N a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hmin : min a b ≤ N) (hab : a ≠ b) :
    atomSpacing N ≤ |Real.log a - Real.log b| := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hbnd : a ≤ N := by rwa [min_eq_left hlt.le] at hmin
    have hd := atomSpacing_le_log_sub ha hbnd hlt
    have : Real.log b - Real.log a ≤ |Real.log a - Real.log b| := by
      simpa only [neg_sub] using neg_le_abs (Real.log a - Real.log b)
    exact hd.trans this
  · have hbnd : b ≤ N := by rwa [min_eq_right hgt.le] at hmin
    exact (atomSpacing_le_log_sub hb hbnd hgt).trans (le_abs_self _)

theorem sectionCorr_log_hecke
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N m n k : ℕ}
    (hw : w < atomSpacing N) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hk : 1 ≤ k) :
    sectionCorr (G m) (G n) (Real.log k - logGap m n) =
      if n = m * k then sectionCorr (G m) (G n) 0 else 0 := by
  have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
  have hk0 : k ≠ 0 := by omega
  have hlog : Real.log ((m * k : ℕ) : ℝ) = Real.log m + Real.log k := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm0) (by exact_mod_cast hk0)]
  split_ifs with heq
  · rw [logGap, heq, hlog]
    congr 1
    ring
  · apply sectionCorr_eq_zero (hs m) (hs n)
    have hd := atomSpacing_le_abs_log_sub_of_min (mem_Icc.mp hn).1
      (Nat.mul_pos (mem_Icc.mp hm).1 hk)
      ((min_le_left n (m * k)).trans (mem_Icc.mp hn).2) heq
    rw [hlog] at hd
    have habs : |Real.log k - logGap m n| = |Real.log n - (Real.log m + Real.log k)| := by
      rw [show Real.log k - logGap m n = -(Real.log n - (Real.log m + Real.log k)) by
        simp only [logGap]; ring, abs_neg]
    rw [habs]
    exact hw.trans_le hd

theorem sectionCorr_neg_log_hecke
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N m n k : ℕ}
    (hw : w < atomSpacing N) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hk : 1 ≤ k) :
    sectionCorr (G m) (G n) (-Real.log k - logGap m n) =
      if m = n * k then sectionCorr (G m) (G n) 0 else 0 := by
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hk0 : k ≠ 0 := by omega
  have hlog : Real.log ((n * k : ℕ) : ℝ) = Real.log n + Real.log k := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hn0) (by exact_mod_cast hk0)]
  split_ifs with heq
  · rw [logGap, heq, hlog]
    congr 1
    ring
  · apply sectionCorr_eq_zero (hs m) (hs n)
    have hd := atomSpacing_le_abs_log_sub_of_min (mem_Icc.mp hm).1
      (Nat.mul_pos (mem_Icc.mp hn).1 hk)
      ((min_le_left m (n * k)).trans (mem_Icc.mp hm).2) heq
    rw [hlog] at hd
    have he : -Real.log k - logGap m n = Real.log m - (Real.log n + Real.log k) := by
      simp only [logGap]; ring
    rw [he]
    exact hw.trans_le hd

/-- All non-ratio prime lags vanish; the surviving pairing is the exact Hecke form. -/
theorem primeSum_arithmeticSection (hg : ∀ n, Continuous (G n))
    (hgc : ∀ n, HasCompactSupport (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    primeSum (arithmeticSection N G) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        sectionCorr (G m) (G n) 0 * ArithmeticEffectivityTheory.weilPrimeKernel m n := by
  have hk : ∀ k : ℕ, vonMangoldtAtom k *
      ((∫ u, arithmeticSection N G u * arithmeticSection N G (u - Real.log k)) +
        ∫ u, arithmeticSection N G u * arithmeticSection N G (u + Real.log k)) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, sectionCorr (G m) (G n) 0 *
        (vonMangoldtAtom k * ((if m = n * k then 1 else 0) +
          (if n = m * k then 1 else 0))) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [vonMangoldtAtom]
    have hneg : (fun u => arithmeticSection N G u * arithmeticSection N G (u - Real.log k)) =
        (fun u => arithmeticSection N G u * arithmeticSection N G (u + -Real.log k)) := by
      simp only [sub_eq_add_neg]
    rw [hneg, integral_arithmeticSection_mul_shift hg hgc,
      integral_arithmeticSection_mul_shift hg hgc, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [sectionCorr_neg_log_hecke hs hw hm hn hk1, sectionCorr_log_hecke hs hw hm hn hk1]
    split_ifs <;> ring
  have hvanish : ∀ k ∉ range (N + 1), vonMangoldtAtom k *
      ((∫ u, arithmeticSection N G u * arithmeticSection N G (u - Real.log k)) +
        ∫ u, arithmeticSection N G u * arithmeticSection N G (u + Real.log k)) = 0 := by
    intro k hk'
    have hkN : N < k := by simpa using hk'
    rw [hk k]
    refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
    have hm1 := mem_Icc.mp hm
    have hn1 := mem_Icc.mp hn
    rw [if_neg (by intro h; nlinarith only [hm1.2, hn1.1, hkN, h]),
      if_neg (by intro h; nlinarith only [hn1.2, hm1.1, hkN, h])]
    ring
  rw [primeSum, tsum_eq_sum hvanish, sum_congr rfl fun k _ => hk k, sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [← mul_sum, sum_vonMangoldtAtom_hecke hm hn]

/-- The prime charge is the integral of the finite prime form on the profile vector. -/
theorem primeSum_arithmeticSection_eq_integral (hg : ∀ n, Continuous (G n))
    (hgc : ∀ n, HasCompactSupport (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    primeSum (arithmeticSection N G) = ∫ u, atomicWeilForm N (fun n => G n u) := by
  rw [primeSum_arithmeticSection hg hgc hs hw]
  simp only [ArithmeticElectrostatics.atomicWeilForm]
  have hi (m n : ℕ) : Integrable fun u => G m u * G n u :=
    ((hg m).mul (hg n)).integrable_of_hasCompactSupport (hgc m).mul_right
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => (hi m n).mul_const _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => (hi m n).mul_const _]
  refine sum_congr rfl fun n _ => ?_
  rw [integral_mul_const]
  simp only [sectionCorr, add_zero]

/-- The tilted prime estimate is valid on the full linear space of independent profiles. -/
theorem primeSum_arithmeticSection_le (hg : ∀ n, Continuous (G n))
    (hgc : ∀ n, HasCompactSupport (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    primeSum (arithmeticSection N G) ≤ ∑ m ∈ Icc 1 N, sectionMass (G m) *
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
  rw [primeSum_arithmeticSection_eq_integral hg hgc hs hw]
  have hp : Integrable fun u => atomicWeilForm N (fun n => G n u) :=
    integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
      (((hg m).mul (hg n)).integrable_of_hasCompactSupport (hgc m).mul_right).mul_const _
  have hi (m : ℕ) := (integrable_sq_of_continuous (hg m) (hgc m)).mul_const
    (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m)
  calc (∫ u, atomicWeilForm N (fun n => G n u)) ≤ ∫ u, ∑ m ∈ Icc 1 N, G m u ^ 2 *
        (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) :=
      integral_mono hp (integrable_finsetSum _ fun m _ => hi m)
        fun u => atomicWeilForm_le_tilted N (fun n => G n u)
    _ = _ := by
      rw [integral_finsetSum _ fun m _ => hi m]
      exact sum_congr rfl fun m _ => integral_mul_const _ _

/-- The mass available to a mixed pair; the diagonal has no shifted overlap. -/
def sectionCrossMass (G : ℕ → ℝ → ℝ) (m n : ℕ) : ℝ :=
  if m = n then 0 else (sectionMass (G m) + sectionMass (G n)) / 2

theorem sectionCrossMass_nonneg (G : ℕ → ℝ → ℝ) (m n : ℕ) :
    0 ≤ sectionCrossMass G m n := by
  unfold sectionCrossMass
  split_ifs
  · exact le_rfl
  · exact div_nonneg (add_nonneg (sectionMass_nonneg _) (sectionMass_nonneg _)) (by norm_num)

theorem sectionCorr_le_pairWindow (hg : ∀ n, Continuous (G n))
    (hgc : ∀ n, HasCompactSupport (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {y : ℝ} (hw0 : 0 ≤ w) (hy : w < y)
    (m n : ℕ) :
    sectionCorr (G m) (G n) (y - logGap m n) ≤
      sectionCrossMass G m n * (pairWindow w (logGap m n)).indicator 1 y := by
  by_cases hmn : m = n
  · subst n
    rw [sectionCrossMass, if_pos rfl, zero_mul, logGap, sub_self, sub_zero,
      sectionCorr_eq_zero (hs m) (hs m) (by rwa [abs_of_pos (lt_of_le_of_lt hw0 hy)])]
  · rw [sectionCrossMass, if_neg hmn]
    by_cases hwin : y ∈ pairWindow w (logGap m n)
    · rw [Set.indicator_of_mem hwin, Pi.one_apply, mul_one]
      exact (le_abs_self _).trans (abs_sectionCorr_le (hg m) (hgc m) (hg n) (hgc n) _)
    · rw [Set.indicator_of_notMem hwin, mul_zero]
      apply le_of_eq
      apply sectionCorr_eq_zero (hs m) (hs n)
      by_contra h
      have hb := abs_le.mp (le_of_not_gt h)
      exact hwin ⟨by linarith only [hb.1], by linarith only [hb.2]⟩

theorem integral_sub_shift_sq_arithmeticSection_ge (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 ≤ w)
    (N : ℕ) {y : ℝ} (hy : w < y) :
    2 * (∫ u, arithmeticSection N G u ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          sectionCrossMass G m n * (pairWindow w (logGap m n)).indicator 1 y ≤
      ∫ u, (arithmeticSection N G u - arithmeticSection N G (u + y)) ^ 2 := by
  have hgc (n : ℕ) := profile_hasCompactSupport (hs n)
  rw [integral_sub_shift_sq_eq (contDiff_arithmeticSection hg N).continuous
    (hasCompactSupport_arithmeticSection hs N),
    integral_arithmeticSection_mul_shift (fun n => (hg n).continuous) hgc]
  have hsum := sum_le_sum (s := Icc 1 N) fun m _ => sum_le_sum (s := Icc 1 N) fun n _ =>
    sectionCorr_le_pairWindow (fun n => (hg n).continuous) hgc hs hw0 hy m n
  linarith only [hsum]

/-- Symmetry charges each profile once, independently of its shape. -/
theorem sum_sectionCrossMass_crossBound (N : ℕ) (G : ℕ → ℝ → ℝ) (w : ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, sectionCrossMass G m n * crossBound w (logGap m n) =
      ∑ m ∈ Icc 1 N, sectionMass (G m) *
        ∑ n ∈ Icc 1 N, (if m = n then 0 else crossBound w (logGap m n)) := by
  let B : ℕ → ℕ → ℝ := fun m n => if m = n then 0 else crossBound w (logGap m n)
  have hB : ∀ m n, B n m = B m n := by
    intro m n
    by_cases hmn : m = n
    · subst n; rfl
    · simp only [B, if_neg hmn, if_neg (Ne.symm hmn), crossBound_logGap_comm]
  have hp : ∀ m n, sectionCrossMass G m n * crossBound w (logGap m n) =
      (sectionMass (G m) * B m n + sectionMass (G n) * B n m) / 2 := by
    intro m n
    rw [hB m n]
    simp only [sectionCrossMass, B]
    split_ifs <;> ring
  simp_rw [hp]
  have hswap : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, sectionMass (G n) * B n m =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, sectionMass (G m) * B m n := sum_comm
  simp only [← sum_div, sum_add_distrib, hswap, mul_sum]
  ring

/-- The constant-one self-energy survives independent local profiles. -/
theorem levyEnergy_arithmeticSection_ge (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ atomSpacing N / 2) :
    ∑ m ∈ Icc 1 N, sectionMass (G m) *
        (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) ≤
      levyEnergy (arithmeticSection N G) := by
  have hδ := atomSpacing_pos hN
  have hw1 : w < 1 := by linarith only [hw, atomSpacing_le_one hN]
  have hgc (n : ℕ) := profile_hasCompactSupport (hs n)
  have hf := contDiff_arithmeticSection hg N
  have hfc := hasCompactSupport_arithmeticSection hs N
  let F2 := ∫ u, arithmeticSection N G u ^ 2
  have hF2 : F2 = ∑ m ∈ Icc 1 N, sectionMass (G m) :=
    integral_arithmeticSection_sq (fun n => (hg n).continuous) hgc hs (by linarith)
  have hF0 : 0 ≤ F2 := integral_nonneg fun _ => sq_nonneg _
  let c := sectionCrossMass G
  let ω := archLevyDensity
  let L : ℝ → ℝ := fun y => ω y * ∫ u,
    (arithmeticSection N G u - arithmeticSection N G (u + y)) ^ 2
  let lower : ℝ → ℝ := fun y => 2 * F2 * ω y -
    2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n * (pairWindow w (logGap m n)).indicator ω y
  have hω : IntegrableOn ω (Set.Ioc w 1) := integrableOn_archLevyDensity_Ioc hw0
  have hind : ∀ m n, IntegrableOn ((pairWindow w (logGap m n)).indicator ω) (Set.Ioc w 1) :=
    fun m n => hω.indicator measurableSet_Icc
  have hlower : IntegrableOn lower (Set.Ioc w 1) :=
    (hω.const_mul _).sub ((integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
      (hind m n).const_mul _).const_mul _)
  have hL : IntegrableOn L (Set.Ioi 0) := integrableOn_levyIntegrand hf hfc
  have hrestrict : ∫ y in Set.Ioc w 1, L y ≤ levyEnergy (arithmeticSection N G) :=
    setIntegral_mono_set hL (levyIntegrand_nonneg _)
      (Filter.Eventually.of_forall fun y hy => lt_trans hw0 hy.1)
  have hlower_le : ∫ y in Set.Ioc w 1, lower y ≤ ∫ y in Set.Ioc w 1, L y := by
    refine setIntegral_mono_on hlower (hL.mono_set fun y hy => lt_trans hw0 hy.1)
      measurableSet_Ioc fun y hy => ?_
    have hωy : 0 ≤ ω y := (archLevyDensity_pos (lt_trans hw0 hy.1)).le
    have hp := integral_sub_shift_sq_arithmeticSection_ge hg hs hw0.le N hy.1
    have he : ∀ m n, c m n * (pairWindow w (logGap m n)).indicator ω y =
        ω y * (c m n * (pairWindow w (logGap m n)).indicator 1 y) := by
      intro m n
      by_cases hm : y ∈ pairWindow w (logGap m n)
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Pi.one_apply]; ring
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]; ring
    have heq : lower y = ω y * (2 * F2 -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n * (pairWindow w (logGap m n)).indicator 1 y) := by
      simp only [lower, he, ← mul_sum]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hp hωy
  have heval : ∫ y in Set.Ioc w 1, lower y = 2 * F2 * (∫ y in Set.Ioc w 1, ω y) -
      2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        c m n * ∫ y in Set.Ioc w 1, (pairWindow w (logGap m n)).indicator ω y := by
    simp only [lower]
    rw [integral_sub (hω.const_mul _) ((integrable_finsetSum _ fun m _ => integrable_finsetSum _
      fun n _ => (hind m n).const_mul _).const_mul _), integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => (hind m n).const_mul _]
    congr 2
    refine sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ fun n _ => (hind m n).const_mul _]
    exact sum_congr rfl fun n _ => integral_const_mul _ _
  have hpairs : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      c m n * ∫ y in Set.Ioc w 1, (pairWindow w (logGap m n)).indicator ω y ≤
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n * crossBound w (logGap m n) := by
    refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
    by_cases hmn : m = n
    · simp only [c, sectionCrossMass, if_pos hmn, zero_mul, le_refl]
    · have hsep := atomSpacing_le_abs_logGap hm hn hmn
      exact mul_le_mul_of_nonneg_left
        (setIntegral_indicator_archLevyDensity_le hw0 hw1 (by linarith only [hw, hsep]))
        (sectionCrossMass_nonneg G m n)
  rw [sum_sectionCrossMass_crossBound] at hpairs
  have hrows : ∑ m ∈ Icc 1 N, sectionMass (G m) *
      ∑ n ∈ Icc 1 N, (if m = n then 0 else crossBound w (logGap m n)) ≤
      ∑ m ∈ Icc 1 N, sectionMass (G m) *
        (4 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) :=
    sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
      (sum_crossBound_le hm hw0.le) (sectionMass_nonneg _)
  have hdiag : Real.log (1 / w) ≤ 2 * ∫ y in Set.Ioc w 1, ω y :=
    log_div_le_two_mul_setIntegral_archLevyDensity hw0 hw1.le le_rfl
  have hmain : ∑ m ∈ Icc 1 N, sectionMass (G m) *
      (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) =
      F2 * Real.log (1 / w) - 2 * ∑ m ∈ Icc 1 N, sectionMass (G m) *
        (4 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) := by
    rw [hF2]
    simp only [sum_mul, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hmain]
  rw [heval] at hlower_le
  have hc := hpairs.trans hrows
  have hd := mul_le_mul_of_nonneg_left hdiag hF0
  linarith only [hd, hc, hlower_le, hrestrict]


/-- The two places match on the full linear space of arithmetic sections. -/
theorem markovEnergy_arithmeticSection_ge (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ spacingRatio * atomSpacing N) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) *
        ∫ u, arithmeticSection N G u ^ 2 ≤
      markovEnergy (fun u => (arithmeticSection N G u : ℂ)) := by
  have hδ := atomSpacing_pos hN
  have hw2 : w ≤ atomSpacing N / 2 := by
    nlinarith only [hw, spacingRatio_lt_half, hδ]
  have hw' : w < atomSpacing N := by linarith only [hw2, hδ]
  have hwN : w ≤ spacingRatio / N := by
    calc w ≤ spacingRatio * atomSpacing N := hw
      _ ≤ spacingRatio * (1 / N) :=
        mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN) spacingRatio_pos.le
      _ = spacingRatio / N := by ring
  have hgc (n : ℕ) := profile_hasCompactSupport (hs n)
  have hf := contDiff_arithmeticSection hg N
  have hfc := hasCompactSupport_arithmeticSection hs N
  have hL := levyEnergy_arithmeticSection_ge hg hs hN hw0 hw2
  have hP := primeSum_arithmeticSection_le (fun n => (hg n).continuous) hgc hs hw'
  have hmass := integral_arithmeticSection_sq (fun n => (hg n).continuous) hgc hs hw'
  have hrow : ∀ m ∈ Icc 1 N,
      2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant ≤
      2 * gammaHardyPhaseRate 0 +
        (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    intro m hm
    have hc := crossRow_le_saving (mem_Icc.mp hm).1 (mem_Icc.mp hm).2 hwN
    unfold spacingConstant
    linarith only [hc]
  have hsum := sum_le_sum (s := Icc 1 N) fun m hm =>
    mul_le_mul_of_nonneg_left (hrow m hm) (sectionMass_nonneg (G m))
  have hexpand : ∑ m ∈ Icc 1 N, sectionMass (G m) *
      (2 * gammaHardyPhaseRate 0 +
        (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m)) =
      2 * gammaHardyPhaseRate 0 * (∫ u, arithmeticSection N G u ^ 2) +
        (∑ m ∈ Icc 1 N, sectionMass (G m) *
          (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1)))) -
        ∑ m ∈ Icc 1 N, sectionMass (G m) *
          (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    rw [hmass]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hexpand, ← sum_mul, ← hmass] at hsum
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
  nlinarith only [hsum, hL, hP]

/-- A fixed arithmetic spacing ratio with one unit of source coercivity. -/
def arithmeticSectionRatio : ℝ := spacingWidthRatio * Real.exp (-1)

theorem arithmeticSectionRatio_pos : 0 < arithmeticSectionRatio :=
  mul_pos spacingWidthRatio_pos (Real.exp_pos _)

theorem arithmeticSectionRatio_le : arithmeticSectionRatio ≤ spacingWidthRatio := by
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  exact (mul_le_mul_of_nonneg_left he spacingWidthRatio_pos.le).trans_eq (mul_one _)

theorem arithmeticSectionGain_ge_one {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ arithmeticSectionRatio * atomSpacing N) :
    1 ≤ 2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant := by
  have hcancel : Real.exp (1 : ℝ) * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hwscaled : Real.exp 1 * w ≤ spacingWidthRatio * atomSpacing N := by
    have hh := mul_le_mul_of_nonneg_left hw (Real.exp_pos 1).le
    have he : Real.exp 1 * (arithmeticSectionRatio * atomSpacing N) =
        spacingWidthRatio * atomSpacing N := by
      unfold arithmeticSectionRatio
      calc Real.exp 1 * (spacingWidthRatio * Real.exp (-1) * atomSpacing N) =
          spacingWidthRatio * atomSpacing N * (Real.exp 1 * Real.exp (-1)) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rwa [he] at hh
  have hbase := spacingGain_nonneg hN (mul_pos (Real.exp_pos 1) hw0) hwscaled
  have he : Real.log (1 / (Real.exp 1 * w)) = Real.log (1 / w) - 1 := by
    rw [Real.log_div (by norm_num) (mul_pos (Real.exp_pos 1) hw0).ne',
      Real.log_mul (Real.exp_pos 1).ne' hw0.ne', Real.log_exp,
      Real.log_div (by norm_num) hw0.ne', Real.log_one]
    ring
  rw [he] at hbase
  linarith only [hbase]

/-- A positive source floor, uniform in the number of arithmetic points and in all profiles. -/
theorem integral_sq_le_markovEnergy_arithmeticSection (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ arithmeticSectionRatio * atomSpacing N) :
    (∫ u, arithmeticSection N G u ^ 2) ≤
      markovEnergy (fun u => (arithmeticSection N G u : ℂ)) := by
  have hw' : w ≤ spacingRatio * atomSpacing N :=
    hw.trans (mul_le_mul_of_nonneg_right
      (arithmeticSectionRatio_le.trans spacingWidthRatio_le) (atomSpacing_pos hN).le)
  have hfloor := markovEnergy_arithmeticSection_ge hg hs hN hw0 hw'
  have hgain := arithmeticSectionGain_ge_one hN hw0 hw
  have hmass : 0 ≤ ∫ u, arithmeticSection N G u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain hmass).trans hfloor

/-- Real linear sections, with no condition involving the Weil form or its zeros. -/
def arithmeticSectionTests (N : ℕ) (w : ℝ) : Submodule ℝ realTests where
  carrier := {f | ∃ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) ∧
    (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) ∧ f.1 = arithmeticSection N G}
  zero_mem' := by
    refine ⟨fun _ _ => 0, fun _ => contDiff_const, fun _ _ _ => rfl, ?_⟩
    funext u
    simp only [Submodule.coe_zero, Pi.zero_apply, arithmeticSection, sum_const_zero]
  add_mem' := by
    rintro f h ⟨G, hG, hsG, heG⟩ ⟨H, hH, hsH, heH⟩
    refine ⟨fun n u => G n u + H n u, fun n => (hG n).add (hH n), ?_, ?_⟩
    · intro n u hu
      rw [hsG n u hu, hsH n u hu, add_zero]
    · funext u
      simp only [Submodule.coe_add, Pi.add_apply, heG, heH, arithmeticSection, sum_add_distrib]
  smul_mem' := by
    rintro r f ⟨G, hG, hsG, heG⟩
    refine ⟨fun n u => r * G n u, fun n => (hG n).const_smul r, ?_, ?_⟩
    · intro n u hu
      rw [hsG n u hu, mul_zero]
    · funext u
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, heG, arithmeticSection, mul_sum]

/-- The odd pole moment is a linear source reading. -/
def sectionSinhMoment : realTests →ₗ[ℝ] ℝ where
  toFun f := sinhHalfMoment f.1
  map_add' f g := by
    simpa only [Submodule.coe_add, Pi.add_apply, one_mul] using
      sinhHalfMoment_linear_comb f.2.1.continuous f.2.2 g.2.1.continuous g.2.2 1 1
  map_smul' r f := by
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      zero_mul, add_zero] using
      sinhHalfMoment_linear_comb f.2.1.continuous f.2.2 f.2.1.continuous f.2.2 r 0

/-- Arithmetic sections with the single adverse pole reading removed. -/
def arithmeticPrimitiveSections (N : ℕ) (w : ℝ) : Submodule ℝ realTests :=
  arithmeticSectionTests N w ⊓ sectionSinhMoment.ker

/-- The full Weil floor includes the Gamma, prime, and both pole terms. -/
theorem integral_sq_le_weilPair_arithmeticPrimitiveSection {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ arithmeticSectionRatio * atomSpacing N)
    (f : arithmeticPrimitiveSections N w) :
    (∫ u, f.1.1 u ^ 2) ≤ weilPair f.1.1 f.1.1 := by
  obtain ⟨G, hG, hsG, heG⟩ := f.2.1
  have hsin : sinhHalfMoment f.1.1 = 0 := f.2.2
  have hM : (∫ u, f.1.1 u ^ 2) ≤ markovEnergy (cx f.1.1) := by
    rw [heG]
    exact integral_sq_le_markovEnergy_arithmeticSection hG hsG hN hw0 hw
  have hcd := cx_contDiff f.1.2.1
  have hcs := cx_hasCompactSupport f.1.2.2
  have he := markovEnergy_eq_W_sub hcd hcs
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq
    f.1.2.1.continuous f.1.2.2, hsin, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero] at he
  have hW : (Zeta23.zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re =
      weilPair f.1.1 f.1.1 := by
    rw [weilPair, zeta_W_eq_weilFullFunctional_mixed hcd hcs hcd hcs]
  rw [hW] at he
  nlinarith only [hM, he, sq_nonneg (coshHalfMoment f.1.1)]

/-- Arithmetic source sections supply Riemann–Roch and ampleness on the same subsurface. -/
theorem arithmeticPrimitiveSections_effectivity {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ arithmeticSectionRatio * atomSpacing N) :
    (scalingSubsurface (arithmeticPrimitiveSections N w)).RiemannRochAxiom
        (l2SourceCone 1 (arithmeticPrimitiveSections N w)) ∧
      (scalingSubsurface (arithmeticPrimitiveSections N w)).AmpleAxiom
        (l2SourceCone 1 (arithmeticPrimitiveSections N w)) ∧
      (scalingSubsurface (arithmeticPrimitiveSections N w)).HodgeIndex := by
  have hc : (0 : ℝ) < 1 := zero_lt_one
  have hf := integral_sq_le_weilPair_arithmeticPrimitiveSection hN hw0 hw
  refine ⟨(l2SourceCone_riemannRoch_iff_weilPair_ge hc _).mpr ?_,
    l2SourceCone_ample hc _, (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mpr ?_⟩
  · intro f
    simpa only [one_mul] using hf f
  · intro f
    exact (integral_nonneg fun _ => sq_nonneg _).trans (hf f)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
