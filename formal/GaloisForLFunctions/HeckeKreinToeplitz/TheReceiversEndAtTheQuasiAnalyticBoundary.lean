import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDenjoyCarlemanProfiles

/-!
# The receivers end at the quasi-analytic boundary

The index-carrying receivers place a compactly supported profile at each atom. Their reach is
limited by the regularity class of the profile, so the theory's test class has a Denjoy–Carleman
boundary.

**The quasi-analytic side** (`eq_zero_of_gevrey_le_one`). A smooth compactly supported function with
Gevrey bounds `|f^{(n)}| ≤ C Aⁿ (n!)^s` of class `s ≤ 1` vanishes identically. It vanishes to all
orders at the left edge of its support. Taylor's theorem then makes it vanish on a step of length
`1/(2A)`, since the remainder is at most `C (n + 1) 2^{−(n+1)} → 0`, and the steps cover the line.

**The boundary** (`exists_compactSupport_gevrey_iff`). Nonzero compactly supported profiles of
Gevrey class `s` exist iff `s > 1`. For `s > 1` the Denjoy–Carleman bumps `E_r(1 + x) E_r(1 − x)`,
`r` odd with `1/r ≤ s − 1`, have class `1 + 1/r`.

**The receivers** (`atomicReceivers_quasiAnalytic_boundary`). For every `α > 1` the atomic families
of width `(log log N)^α/N` of a Denjoy–Carleman profile decide RH. A profile for the Gevrey window
at exponent `α` must have class `s < α`, and for `α ≤ 1` no nonzero compactly supported profile of
class `s < α` exists. So the window method reaches exactly the non-quasi-analytic range, and the
exponent `1` at which the receivers stop is the quasi-analytic boundary.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- A smooth function vanishing on `(−∞, b]` vanishes there to all orders. -/
theorem iteratedDeriv_eq_zero_of_eq_zero_Iic {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {b : ℝ}
    (h0 : ∀ y ≤ b, f y = 0) (k : ℕ) : iteratedDeriv k f b = 0 := by
  have hopen : ∀ y < b, iteratedDeriv k f y = 0 := fun y hy => by
    have hloc : f =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz using h0 z hz.le
    rw [hloc.iteratedDeriv_eq]
    simp
  have hcont : Continuous (iteratedDeriv k f) := (contDiff_infty.mp hf k).continuous_iteratedDeriv k le_rfl
  have hsub := (isClosed_eq hcont continuous_const).closure_subset_iff.mpr
    (fun y (hy : y ∈ Iio b) => hopen y hy)
  rw [closure_Iio] at hsub
  exact hsub self_mem_Iic

/-- **One Taylor step.** Gevrey-`1` bounds propagate vanishing on `(−∞, b]` to
`(−∞, b + 1/(2A)]`. -/
theorem eq_zero_Iic_of_gevrey_one {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {C A : ℝ} (hA : 0 < A)
    (hbd : ∀ n x, |iteratedDeriv n f x| ≤ C * A ^ n * n.factorial) {b : ℝ}
    (h0 : ∀ y ≤ b, f y = 0) : ∀ y ≤ b + (2 * A)⁻¹, f y = 0 := by
  intro x hx
  rcases le_or_gt x b with hxb | hxb
  · exact h0 x hxb
  have hC : 0 ≤ C := by
    have := hbd 0 x
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at this
    exact (abs_nonneg _).trans this
  have hAx0 : 0 ≤ A * (x - b) := by nlinarith
  have hAx : A * (x - b) ≤ 1 / 2 := by
    have : x - b ≤ (2 * A)⁻¹ := by linarith
    calc A * (x - b) ≤ A * (2 * A)⁻¹ := mul_le_mul_of_nonneg_left this hA.le
      _ = 1 / 2 := by field_simp
  have hle : ∀ n : ℕ, |f x| ≤ C * (((n + 1 : ℕ) : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n + 1)) := fun n => by
    have hT := taylor_mean_remainder_bound (f := f) (n := n)
      (C := C * A ^ (n + 1) * ((n + 1).factorial : ℝ)) hxb.le
      (by simpa using (contDiff_infty.mp hf (n + 1)).contDiffOn) (right_mem_Icc.mpr hxb.le)
      (fun y hy => by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxb)
          (contDiff_infty.mp hf (n + 1)).contDiffAt hy, Real.norm_eq_abs]
        exact hbd (n + 1) y)
    have htay : taylorWithinEval f n (Icc b x) b x = 0 := by
      rw [taylor_within_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxb)
        (contDiff_infty.mp hf k).contDiffAt (left_mem_Icc.mpr hxb.le),
        iteratedDeriv_eq_zero_of_eq_zero_Iic hf h0 k, smul_zero]
    rw [htay, sub_zero, Real.norm_eq_abs] at hT
    have hfac : ((n + 1).factorial : ℝ) / n.factorial = ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    have hpow : (A * (x - b)) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_le_pow_left₀ hAx0 hAx _
    calc |f x| ≤ C * A ^ (n + 1) * ((n + 1).factorial : ℝ) * (x - b) ^ (n + 1) / n.factorial := hT
      _ = C * (((n + 1 : ℕ) : ℝ) * (A * (x - b)) ^ (n + 1)) := by
          rw [← hfac, mul_pow]
          field_simp
      _ ≤ C * (((n + 1 : ℕ) : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n + 1)) := by
          rw [pow_one]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) hC
  have hlim : Tendsto (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n + 1))) atTop
      (𝓝 (C * 0)) :=
    ((tendsto_add_atTop_iff_nat 1).mpr (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
      (by norm_num : |(1 / 2 : ℝ)| < 1))).const_mul C
  rw [mul_zero] at hlim
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto' hlim hle) (abs_nonneg _))

/-- **The quasi-analytic side.** A smooth compactly supported function of Gevrey class `s ≤ 1`
vanishes identically. -/
theorem eq_zero_of_gevrey_le_one {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {s C A : ℝ} (hs : s ≤ 1) (hA : 0 < A)
    (hbd : ∀ n x, |iteratedDeriv n f x| ≤ C * A ^ n * (n.factorial : ℝ) ^ s) : f = 0 := by
  have hbd1 : ∀ n x, |iteratedDeriv n f x| ≤ C * A ^ n * n.factorial := fun n x => by
    have hC : 0 ≤ C := by
      have := hbd 0 x
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Real.one_rpow] at this
      exact (abs_nonneg _).trans this
    refine (hbd n x).trans ?_
    have hf1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h1 : (n.factorial : ℝ) ^ s ≤ (n.factorial : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hf1 hs
    rw [Real.rpow_one] at h1
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  obtain ⟨m, hm⟩ := hc.isCompact.bddBelow
  have hR : ∀ y ≤ m - 1, f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => by linarith [hm h]
  have hk : ∀ k : ℕ, ∀ y ≤ m - 1 + k * (2 * A)⁻¹, f y = 0 := by
    intro k
    induction k with
    | zero => simpa using hR
    | succ k ih =>
      intro y hy
      refine eq_zero_Iic_of_gevrey_one hf hA hbd1 ih y ?_
      push_cast at hy
      linarith
  funext x
  obtain ⟨k, hk'⟩ := exists_nat_gt ((x - (m - 1)) * (2 * A))
  refine hk k x ?_
  have h2A : 0 < 2 * A := by positivity
  have : x - (m - 1) ≤ k * (2 * A)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ h2A]
    exact hk'.le
  linarith

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis in
/-- **The Denjoy–Carleman boundary of the test class.** Nonzero smooth compactly supported profiles of
Gevrey class `s` exist iff `s > 1`. -/
theorem exists_compactSupport_gevrey_iff (s : ℝ) :
    (∃ f : ℝ → ℝ, f ≠ 0 ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ ∃ C A : ℝ, 0 < A ∧
      ∀ n x, |iteratedDeriv n f x| ≤ C * A ^ n * (n.factorial : ℝ) ^ s) ↔ 1 < s := by
  constructor
  · rintro ⟨f, hf0, hf, hc, C, A, hA, hb⟩
    by_contra hs
    exact hf0 (eq_zero_of_gevrey_le_one hf hc (not_lt.mp hs) hA hb)
  · intro hs
    set m := ⌈(s - 1)⁻¹⌉₊
    set r := 2 * m + 1
    have hr : Odd r := odd_two_mul_add_one m
    have hs1 : 0 < s - 1 := by linarith
    have hrs : (r : ℝ)⁻¹ ≤ s - 1 := by
      have hm : (s - 1)⁻¹ ≤ m := Nat.le_ceil _
      have hrpos : (0 : ℝ) < r := by positivity
      have : (s - 1)⁻¹ ≤ (r : ℝ) := by
        simp only [r]; push_cast; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
      rw [inv_le_comm₀ hrpos hs1]
      exact this
    refine ⟨dcBump r, fun h => ?_, contDiff_dcBump r, ?_, 1,
      2 * ((r : ℝ) + 1) ^ (2 + (r : ℝ)⁻¹), by positivity, fun n x => ?_⟩
    · have h0 : 0 < dcBump r 0 := by
        show 0 < glueR r (1 + 0) * glueR r (1 - 0)
        exact mul_pos (glueR_pos (by norm_num)) (glueR_pos (by norm_num))
      rw [h] at h0
      exact lt_irrefl _ h0
    · refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => ?_
      refine dcBump_vanishesOff hr x ?_
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact hx
    · refine (abs_iteratedDeriv_dcBump_le hr n x).trans ?_
      have hf1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf1 (by linarith))
        (by positivity)

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  RHTower in
/-- **The receivers end at the quasi-analytic boundary.** For every `α > 1` the atomic families of
width `(log log N)^α/N` of a Denjoy–Carleman profile decide RH. Below the boundary no admissible
profile exists: a compactly supported profile of Gevrey class `s ≤ 1` is zero. -/
theorem atomicReceivers_quasiAnalytic_boundary :
    (∀ α : ℝ, 1 < α → ∃ r : ℕ, Odd r ∧ (RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log (Real.log N) ^ α)
        (dcProfile r))))) ∧
    ∀ s : ℝ, s ≤ 1 → ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∃ C A : ℝ, 0 < A ∧ ∀ n x, |iteratedDeriv n f x| ≤ C * A ^ n * (n.factorial : ℝ) ^ s) →
        f = 0 :=
  ⟨fun _ hα => exists_dcProfile_loglog hα, fun _ hs _ hf hc ⟨_, _, hA, hb⟩ =>
    eq_zero_of_gevrey_le_one hf hc hs hA hb⟩

end GaloisForLFunctions.HeckeKreinToeplitz
