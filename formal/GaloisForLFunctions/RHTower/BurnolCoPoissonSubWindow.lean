import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinZeta
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Sub-window reciprocal seeds

The reciprocal function on an arbitrary multiplicative sub-window `[c,d]` is again a co-Poisson
seed, and its co-Poisson value is again a difference of two fractional parts,

`P(t) = (fract(t/d) - fract(t/c)) / t`,

with Mellin transform `(d^(-w) - c^(-w)) * (-zeta(w)/w)` on the critical strip.  Taking `d = 1/c`
recovers the symmetric window.  This turns the single explicit inhabitant into a two-parameter
family, all of whose Mellin transforms carry the factor `zeta(w)`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The reciprocal seed of a multiplicative sub-window. -/
def coPoissonSubWindowSeed (c d : ℝ) : ℝ → ℂ :=
  Set.indicator (Icc c d) fun v : ℝ => ((v : ℝ) : ℂ)⁻¹

theorem support_coPoissonSubWindowSeed (c d : ℝ) :
    Function.support (coPoissonSubWindowSeed c d) ⊆ Icc c d := by
  intro x hx
  by_contra h
  exact hx (by rw [coPoissonSubWindowSeed, Set.indicator_of_notMem h])

theorem coPoissonSubWindowSeed_of_mem {c d x : ℝ} (h : x ∈ Icc c d) :
    coPoissonSubWindowSeed c d x = ((x : ℝ) : ℂ)⁻¹ := by
  rw [coPoissonSubWindowSeed, Set.indicator_of_mem h]

theorem coPoissonSubWindowSeed_of_notMem {c d x : ℝ} (h : x ∉ Icc c d) :
    coPoissonSubWindowSeed c d x = 0 := by
  rw [coPoissonSubWindowSeed, Set.indicator_of_notMem h]

/-- Membership of the contributing window for a sub-window seed. -/
theorem subWindow_scale_mem {c d t : ℝ} (hc : 0 < c) {k : ℕ} (hk : 0 < k)
    (h1 : t / d ≤ (k : ℝ)) (h2 : (k : ℝ) ≤ t / c) (hd : 0 < d) :
    t / (k : ℝ) ∈ Icc c d := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hkpos, mul_comm]
    exact (le_div_iff₀ hc).mp h2
  · rw [div_le_iff₀ hkpos, mul_comm]
    exact (div_le_iff₀ hd).mp h1

/-- **The co-Poisson sum of a sub-window seed is a finite window sum.** -/
theorem coPoissonSum_eq_subWindow_finset_sum {c d t : ℝ} (hc : 0 < c) (hd : 0 < d) (ht : 0 < t)
    {h : ℝ → ℂ} (hsupp : Function.support h ⊆ Icc c d) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * h (t / ((n + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊, (((k : ℕ) : ℝ) : ℂ)⁻¹ * h (t / ((k : ℕ) : ℝ)) := by
  set m : ℕ := ⌈t / d⌉₊ with hm
  set N : ℕ := ⌊t / c⌋₊ with hN
  have hmpos : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hvanish : ∀ n : ℕ, n ∉ Finset.range N →
      (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * h (t / ((n + 1 : ℕ) : ℝ)) = 0 := by
    intro n hn
    by_cases hz : h (t / ((n + 1 : ℕ) : ℝ)) = 0
    · rw [hz, mul_zero]
    · exfalso
      have hmem : t / ((n + 1 : ℕ) : ℝ) ∈ Icc c d := hsupp (Function.mem_support.mpr hz)
      have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hlow : c ≤ t / ((n + 1 : ℕ) : ℝ) := hmem.1
      rw [le_div_iff₀ hnpos] at hlow
      have hle : ((n + 1 : ℕ) : ℝ) ≤ t / c := by
        rw [le_div_iff₀ hc, mul_comm]
        exact hlow
      have : n + 1 ≤ N := Nat.le_floor hle
      exact (Finset.mem_range.not.mp hn) (by omega)
  rw [tsum_eq_sum hvanish]
  have hreindex : ∀ f : ℕ → ℂ, ∑ n ∈ Finset.range N, f (n + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc, zero_add]
  rw [hreindex (fun k => (((k : ℕ) : ℝ) : ℂ)⁻¹ * h (t / ((k : ℕ) : ℝ)))]
  have hsubset : Finset.Icc m N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_left hmpos
  have houtside : ∀ k ∈ Finset.Icc 1 N, k ∉ Finset.Icc m N →
      (((k : ℕ) : ℝ) : ℂ)⁻¹ * h (t / ((k : ℕ) : ℝ)) = 0 := by
    intro k hk hkn
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hklt : k < m := by
      by_contra hcon
      exact hkn (Finset.mem_Icc.mpr ⟨not_lt.mp hcon, hkN⟩)
    have hkreal : (k : ℝ) < t / d := Nat.lt_ceil.mp hklt
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hout : t / (k : ℝ) ∉ Icc c d := by
      rintro ⟨-, h2⟩
      rw [div_le_iff₀ hkpos, mul_comm] at h2
      have hkd : (k : ℝ) * d < t := (lt_div_iff₀ hd).mp hkreal
      linarith
    have hz : h (t / ((k : ℕ) : ℝ)) = 0 := by
      by_contra hne
      exact hout (hsupp (Function.mem_support.mpr hne))
    rw [hz, mul_zero]
  exact (Finset.sum_subset hsubset houtside).symm

/-- **The co-Poisson sum of a sub-window seed counts window indices.** -/
theorem coPoissonSubWindowSum_eq {c d t : ℝ} (hc : 0 < c) (hd : 0 < d) (ht : 0 < t) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonSubWindowSeed c d (t / ((n + 1 : ℕ) : ℝ))) =
      ((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℂ) * ((t : ℝ) : ℂ)⁻¹ := by
  rw [coPoissonSum_eq_subWindow_finset_sum hc hd ht (support_coPoissonSubWindowSeed c d)]
  have hmpos : 1 ≤ ⌈t / d⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hterm : ∀ k ∈ Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊,
      (((k : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonSubWindowSeed c d (t / ((k : ℕ) : ℝ)) =
        ((t : ℝ) : ℂ)⁻¹ := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hkpos : 0 < k := lt_of_lt_of_le hmpos hk1
    have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have hlow : t / d ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk1)
    have hhigh : (k : ℝ) ≤ t / c := le_trans (by exact_mod_cast hk2) (Nat.floor_le (by positivity))
    rw [coPoissonSubWindowSeed_of_mem (subWindow_scale_mem hc hkpos hlow hhigh hd)]
    have hkc : ((k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.cast_ne_zero.mpr hkpos.ne'
    have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]



/-! ## Fractional-part form -/

theorem subWindow_natCeil_le_natFloor_add_one {c d t : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (ht : 0 < t) : ⌈t / d⌉₊ ≤ ⌊t / c⌋₊ + 1 := by
  refine Nat.ceil_le.mpr ?_
  have h1 : t / d ≤ t / c := by
    refine div_le_div_of_nonneg_left ht.le hc hcd
  have h2 : t / c < ((⌊t / c⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  push_cast
  linarith

/-- **The sub-window index count in fractional-part form.** -/
theorem subWindowCard_eq_fract {c d t : ℝ} (hc : 0 < c) (hd : 0 < d) (hcd : c ≤ d) (ht : 0 < t)
    (hfr : Int.fract (t / d) ≠ 0) :
    ((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) =
      t / c - t / d + Int.fract (t / d) - Int.fract (t / c) := by
  have hle := subWindow_natCeil_le_natFloor_add_one hc hcd ht
  have hcard : ((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) =
      ((⌊t / c⌋₊ : ℕ) : ℝ) + 1 - ((⌈t / d⌉₊ : ℕ) : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub hle]
    push_cast
    ring
  rw [hcard, natFloor_cast_eq_sub_fract (by positivity : (0 : ℝ) ≤ t / c),
    natCeil_cast_eq_add_sub_fract (by positivity : (0 : ℝ) ≤ t / d) hfr]
  ring

/-- The correction constant of a sub-window seed is the length of the inverted window. -/
theorem coPoissonCorrectionConstant_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    coPoissonCorrectionConstant (coPoissonSubWindowSeed c d) = ((c⁻¹ - d⁻¹ : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hinv : d⁻¹ ≤ c⁻¹ := by
    rw [inv_le_inv₀ hd hc]
    exact hcd
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ((y : ℝ) : ℂ)⁻¹ * coPoissonSubWindowSeed c d y⁻¹ =
      Set.indicator (Icc d⁻¹ c⁻¹) (fun _ : ℝ => (1 : ℂ)) y := by
    intro y hy
    have hypos : (0 : ℝ) < y := mem_Ioi.mp hy
    have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hypos)
    have hiff : y⁻¹ ∈ Icc c d ↔ y ∈ Icc d⁻¹ c⁻¹ := by
      rw [mem_Icc, mem_Icc, le_inv_comm₀ hc hypos, inv_le_comm₀ hypos hd, and_comm]
    by_cases h : y ∈ Icc d⁻¹ c⁻¹
    · rw [Set.indicator_of_mem h, coPoissonSubWindowSeed_of_mem (hiff.mpr h),
        Complex.ofReal_inv, inv_inv, inv_mul_cancel₀ hyne]
    · rw [Set.indicator_of_notMem h,
        coPoissonSubWindowSeed_of_notMem (fun hcon => h (hiff.mp hcon)), mul_zero]
  have hsub : Ioi (0 : ℝ) ∩ Icc d⁻¹ c⁻¹ = Icc d⁻¹ c⁻¹ := by
    rw [Set.inter_eq_right]
    intro y hy
    exact lt_of_lt_of_le (inv_pos.mpr hd) hy.1
  rw [coPoissonCorrectionConstant, setIntegral_congr_fun measurableSet_Ioi hpt,
    setIntegral_indicator measurableSet_Icc, hsub, setIntegral_const,
    Real.volume_real_Icc_of_le hinv, Complex.real_smul, mul_one, Complex.ofReal_sub,
    Complex.ofReal_inv, Complex.ofReal_inv]

/-- **The co-Poisson value of a sub-window seed is a difference of fractional parts.** -/
theorem burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_fract {c d t : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (ht : 0 < t) (hfr : Int.fract (t / d) ≠ 0) :
    burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t =
      (((Int.fract (t / d) - Int.fract (t / c)) / t : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos ht,
    coPoissonSubWindowSum_eq hc hd ht,
    coPoissonCorrectionConstant_coPoissonSubWindowSeed hc hcd]
  have hcardR := subWindowCard_eq_fract hc hd hcd ht hfr
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd
  have hreal : ((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) / t - (c⁻¹ - d⁻¹) =
      (Int.fract (t / d) - Int.fract (t / c)) / t := by
    rw [hcardR]
    field_simp
    ring
  rw [← hreal]
  push_cast
  rw [div_eq_mul_inv]
  ring

/-! ## The Mellin transform of a sub-window co-Poisson value -/

theorem burnolCoPoissonRightSum_coPoissonSubWindowSeed_ae_fract {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) :
    burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ => (((Int.fract (t / d) - Int.fract (t / c)) / t : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hcompl : ∀ᵐ t ∂(volume : Measure ℝ), Int.fract (t / d) ≠ 0 := by
    have h := measure_zero_fract_eq_zero (b := d⁻¹) (inv_pos.mpr hd)
    rw [Filter.eventually_iff, mem_ae_iff]
    convert h using 2
    ext t
    simp [div_eq_mul_inv]
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcompl] with t ht hfr
  exact burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_fract hc hcd (mem_Ioi.mp ht) hfr

/-- **The Mellin transform of a sub-window co-Poisson value.**  It is the difference of the two
endpoint powers times the zeta factor. -/
theorem integral_Ioi_burnolCoPoisson_subWindow_cpow {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t * (t : ℂ) ^ (-w)) =
      (((d : ℝ) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) * (-(riemannZeta w / w)) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hdinv : (0 : ℝ) < d⁻¹ := inv_pos.mpr hd
  have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  have hint1 := integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 hdinv
  have hint2 := integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 hcinv
  have hae : (fun t : ℝ =>
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t * (t : ℂ) ^ (-w))
        =ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ => ((Int.fract (d⁻¹ * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) -
        ((Int.fract (c⁻¹ * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
    filter_upwards [burnolCoPoissonRightSum_coPoissonSubWindowSeed_ae_fract hc hcd,
      ae_restrict_mem measurableSet_Ioi] with t ht htpos
    have htp : (0 : ℝ) < t := mem_Ioi.mp htpos
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htp)
    have hpow : ((t : ℝ) : ℂ)⁻¹ * (t : ℂ) ^ (-w) = (t : ℂ) ^ (-(w + 1)) := by
      rw [show (-(w + 1) : ℂ) = -1 + -w by ring, Complex.cpow_add _ _ htne,
        show ((t : ℝ) : ℂ) ^ (-1 : ℂ) = ((t : ℝ) : ℂ)⁻¹ by
          rw [Complex.cpow_neg, Complex.cpow_one]]
    rw [ht]
    have harg1 : t / d = d⁻¹ * t := by rw [div_eq_mul_inv, mul_comm]
    have harg2 : t / c = c⁻¹ * t := by rw [div_eq_mul_inv, mul_comm]
    rw [harg1, harg2]
    push_cast
    rw [← hpow]
    ring
  rw [integral_congr_ae hae, integral_sub hint1 hint2,
    integral_Ioi_zero_fract_dilate_cpow hw0 hw1 hdinv,
    integral_Ioi_zero_fract_dilate_cpow hw0 hw1 hcinv,
    ofReal_inv_cpow_eq_cpow_neg hd, ofReal_inv_cpow_eq_cpow_neg hc]
  ring

/-- **Every sub-window co-Poisson value is annihilated at a zeta zero.**  The whole two-parameter
family of explicit inhabitants carries the factor `zeta(w)`. -/
theorem integral_Ioi_burnolCoPoisson_subWindow_cpow_eq_zero {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hz : riemannZeta w = 0) :
    (∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t * (t : ℂ) ^ (-w)) = 0 := by
  have hw1 : w.re < 1 := riemannZeta_zero_re_lt_one hz
  rw [integral_Ioi_burnolCoPoisson_subWindow_cpow hc hcd hw0 hw1, hz]
  simp



/-! ## Size of the sub-window co-Poisson value -/

theorem burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_card {c d t : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (ht : 0 < t) :
    burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t =
      ((((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) / t - (c⁻¹ - d⁻¹) : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos ht,
    coPoissonSubWindowSum_eq hc hd ht,
    coPoissonCorrectionConstant_coPoissonSubWindowSeed hc hcd]
  push_cast
  ring

/-- **The sub-window index count is the expected count up to one unit.** -/
theorem abs_subWindowCard_sub_le {c d t : ℝ} (hc : 0 < c) (hcd : c ≤ d) (ht : 0 < t) :
    |((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) - t * (c⁻¹ - d⁻¹)| ≤ 1 := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  set m : ℕ := ⌈t / d⌉₊ with hm
  set N : ℕ := ⌊t / c⌋₊ with hN
  have hNle : ((N : ℕ) : ℝ) ≤ t / c := Nat.floor_le (by positivity)
  have hNlt : t / c < ((N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmle : t / d ≤ ((m : ℕ) : ℝ) := Nat.le_ceil _
  have hmlt : ((m : ℕ) : ℝ) < t / d + 1 := Nat.ceil_lt_add_one (by positivity)
  have hexp : t * (c⁻¹ - d⁻¹) = t / c - t / d := by
    rw [mul_sub, div_eq_mul_inv, div_eq_mul_inv]
  have hmono : t / d ≤ t / c := div_le_div_of_nonneg_left ht.le hc hcd
  rw [Nat.card_Icc, hexp]
  rcases le_or_gt m (N + 1) with hle | hgt
  · have hcast : (((N + 1 - m : ℕ)) : ℝ) = ((N : ℕ) : ℝ) + 1 - ((m : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hcast, abs_le]
    constructor <;> linarith
  · have hzero : N + 1 - m = 0 := by omega
    have hlt : ((N : ℕ) : ℝ) + 1 < ((m : ℕ) : ℝ) := by
      have hcon : (N : ℕ) + 1 < m := hgt
      exact_mod_cast hcon
    rw [hzero, Nat.cast_zero, abs_le]
    constructor <;> linarith

theorem norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) {t : ℝ} (ht : 0 < t) :
    ‖burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t‖ ≤ 1 / t := by
  rw [burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_card hc hcd ht, Complex.norm_real,
    Real.norm_eq_abs]
  have hval : (((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) / t - (c⁻¹ - d⁻¹)) =
      (((Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card : ℝ) - t * (c⁻¹ - d⁻¹)) / t := by
    field_simp
  rw [hval, abs_div, abs_of_pos ht, div_le_div_iff_of_pos_right ht]
  exact abs_subWindowCard_sub_le hc hcd ht

theorem norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le_global {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (t : ℝ) :
    ‖burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t‖ ≤ 2 / c := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hgap : (0 : ℝ) ≤ c⁻¹ - d⁻¹ := by
    rw [sub_nonneg, inv_le_inv₀ hd hc]
    exact hcd
  have hcinv : c⁻¹ ≤ 2 / c := by
    rw [le_div_iff₀ hc, inv_mul_cancel₀ (ne_of_gt hc)]
    norm_num
  have habs : burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t =
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) |t| := by
    simp only [burnolCoPoissonRightSum, abs_abs]
  have hdinv : (0 : ℝ) ≤ d⁻¹ := le_of_lt (inv_pos.mpr hd)
  rcases eq_or_lt_of_le (abs_nonneg t) with hz | hpos
  · have hzero : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonSubWindowSeed c d (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
      intro n
      rw [← hz, zero_div, coPoissonSubWindowSeed_of_notMem (by
        rintro ⟨h1, -⟩
        linarith), mul_zero]
    rw [habs, burnolCoPoissonRightSum, abs_abs, tsum_congr hzero, tsum_zero, zero_sub]
    rw [show (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * coPoissonSubWindowSeed c d y⁻¹)) =
        ((c⁻¹ - d⁻¹ : ℝ) : ℂ) from coPoissonCorrectionConstant_coPoissonSubWindowSeed hc hcd,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap]
    linarith
  · rw [habs, burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_card hc hcd hpos,
      Complex.norm_real, Real.norm_eq_abs]
    have hmpos : 1 ≤ ⌈|t| / d⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    have hcardNat : (Finset.Icc ⌈|t| / d⌉₊ ⌊|t| / c⌋₊).card ≤ ⌊|t| / c⌋₊ := by
      rw [Nat.card_Icc]
      omega
    have hcard : ((Finset.Icc ⌈|t| / d⌉₊ ⌊|t| / c⌋₊).card : ℝ) ≤ |t| / c := by
      calc ((Finset.Icc ⌈|t| / d⌉₊ ⌊|t| / c⌋₊).card : ℝ) ≤ ((⌊|t| / c⌋₊ : ℕ) : ℝ) := by
            exact_mod_cast hcardNat
        _ ≤ |t| / c := Nat.floor_le (by positivity)
    have hq : ((Finset.Icc ⌈|t| / d⌉₊ ⌊|t| / c⌋₊).card : ℝ) / |t| ≤ c⁻¹ := by
      rw [div_le_iff₀ hpos]
      calc ((Finset.Icc ⌈|t| / d⌉₊ ⌊|t| / c⌋₊).card : ℝ) ≤ |t| / c := hcard
        _ = c⁻¹ * |t| := by
            rw [div_eq_mul_inv]
            ring
    have hnn : (0 : ℝ) ≤ ((Finset.Icc ⌈|t| / d⌉₊ ⌊|t| / c⌋₊).card : ℝ) / |t| := by positivity
    rw [abs_le]
    constructor <;> linarith



/-! ## The sub-window seed as a window seed -/

theorem measurable_coPoissonSubWindowSeed (c d : ℝ) : Measurable (coPoissonSubWindowSeed c d) :=
  (Complex.measurable_ofReal.inv).indicator measurableSet_Icc

/-- A sub-window sits inside the symmetric window of its own aperture. -/
theorem support_coPoissonSubWindowSeed_symmetric {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    Function.support (coPoissonSubWindowSeed c d) ⊆ Icc (min c d⁻¹) (min c d⁻¹)⁻¹ := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hbpos : (0 : ℝ) < min c d⁻¹ := lt_min hc (inv_pos.mpr hd)
  refine (support_coPoissonSubWindowSeed c d).trans ?_
  intro x hx
  refine ⟨le_trans (min_le_left _ _) hx.1, ?_⟩
  have h1 : min c d⁻¹ ≤ d⁻¹ := min_le_right _ _
  have h2 : d ≤ (min c d⁻¹)⁻¹ := by
    rw [le_inv_comm₀ hd hbpos]
    exact h1
  exact le_trans hx.2 h2

theorem measurable_burnolCoPoissonRightSum_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) : Measurable (burnolCoPoissonRightSum (coPoissonSubWindowSeed c d)) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  exact measurable_burnolCoPoissonRightSum (lt_min hc (inv_pos.mpr hd))
    (measurable_coPoissonSubWindowSeed c d) (support_coPoissonSubWindowSeed_symmetric hc hcd)

/-- **A square-integrable decay profile for the sub-window co-Poisson value.** -/
theorem norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le_profile {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) (t : ℝ) :
    ‖burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t‖ ≤ (2 + 4 / c) * (1 + |t|)⁻¹ := by
  have habs : burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t =
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) |t| := by
    simp only [burnolCoPoissonRightSum, abs_abs]
  have hden : (0 : ℝ) < 1 + |t| := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hden]
  rcases le_or_gt 1 |t| with hfar | hnear
  · have hpos : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos hfar
    have hA := norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le hc hcd hpos
    rw [← habs] at hA
    have hstep : ‖burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t‖ * (1 + |t|) ≤
        1 / |t| * (2 * |t|) := by
      have h1 : 1 + |t| ≤ 2 * |t| := by linarith
      have h2 : (0 : ℝ) ≤ 1 / |t| := by positivity
      nlinarith [norm_nonneg (burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t)]
    have hval : 1 / |t| * (2 * |t|) = 2 := by field_simp
    have hc4 : (0 : ℝ) ≤ 4 / c := by positivity
    linarith [hstep, hval.le, hval.ge]
  · have hB := norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le_global hc hcd t
    have h1t : 1 + |t| ≤ 2 := by linarith
    have hnn : (0 : ℝ) ≤ 2 / c := by positivity
    have h1 : ‖burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t‖ * (1 + |t|) ≤
        2 / c * (1 + |t|) := mul_le_mul_of_nonneg_right hB hden.le
    have h2 : 2 / c * (1 + |t|) ≤ 2 / c * 2 := mul_le_mul_of_nonneg_left h1t hnn
    have h3 : 2 / c * 2 = 4 / c := by ring
    linarith

/-- **The sub-window co-Poisson value is square integrable.** -/
theorem memLp_two_burnolCoPoissonRightSum_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) :
    MemLp (burnolCoPoissonRightSum (coPoissonSubWindowSeed c d)) 2 volume :=
  HTGeometry.memLp_two_of_decayProfile
    (measurable_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd).aestronglyMeasurable
    (norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le_profile hc hcd)

/-- **The sub-window co-Poisson value is real.** -/
theorem star_burnolCoPoissonRightSum_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (t : ℝ) :
    (starRingEnd ℂ) (burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t) =
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t := by
  have habs : burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t =
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) |t| := by
    simp only [burnolCoPoissonRightSum, abs_abs]
  rcases eq_or_lt_of_le (abs_nonneg t) with hz | hpos
  · have hzero : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonSubWindowSeed c d (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
      intro n
      rw [← hz, zero_div, coPoissonSubWindowSeed_of_notMem (by
        rintro ⟨h1, -⟩
        linarith), mul_zero]
    rw [habs, burnolCoPoissonRightSum, abs_abs, tsum_congr hzero, tsum_zero, zero_sub]
    rw [show (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * coPoissonSubWindowSeed c d y⁻¹)) =
        ((c⁻¹ - d⁻¹ : ℝ) : ℂ) from coPoissonCorrectionConstant_coPoissonSubWindowSeed hc hcd,
      map_neg, Complex.conj_ofReal]
  · rw [habs, burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_card hc hcd hpos]
    exact Complex.conj_ofReal _


theorem integrableOn_inv_Icc {c d : ℝ} (hc : 0 < c) :
    IntegrableOn (fun v : ℝ => ((v : ℝ) : ℂ)⁻¹) (Icc c d) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  intro v hv
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hc hv.1
  exact ContinuousAt.continuousWithinAt
    ((Complex.continuous_ofReal.continuousAt).inv₀
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hvpos)))

theorem integrable_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c) :
    Integrable (coPoissonSubWindowSeed c d) :=
  (integrableOn_inv_Icc (d := d) hc).integrable_indicator measurableSet_Icc

end RHTower
