import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilSourceContraction

open Filter Finset
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Literal odd pole source at the matched anchor. -/
def ccmMatchedOddPoleSource (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  (1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) - ccmPolarApertureVector a (-1 / 2))

theorem norm_ccmMatchedOddPoleSource_le (a : SuzukiPositiveAperture) :
    ‖ccmMatchedOddPoleSource a‖ ≤ Real.exp (a.1 / 2) := by
  have he : (Real.exp (a.1 / 2)) ^ 2 = Real.exp a.1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbound (f : suzukiApertureHilbert a) (hf : ‖f‖ ^ 2 = 2 * Real.sinh a.1) :
      ‖f‖ ≤ Real.exp (a.1 / 2) := by
    rw [Real.sinh_eq] at hf
    nlinarith [Real.exp_pos (-a.1), Real.exp_pos (a.1 / 2)]
  have hp := hbound _ (norm_sq_ccmPolarApertureVector_half a)
  have hm := hbound _ (norm_sq_ccmPolarApertureVector_neg_half a)
  unfold ccmMatchedOddPoleSource
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_smul, hhalf]
  have hs := norm_sub_le (ccmPolarApertureVector a (1 / 2))
    (ccmPolarApertureVector a (-1 / 2))
  linarith

private theorem matched_odd_budget (a : SuzukiPositiveAperture) :
    CCMFiniteExponentialBudget (ccmMatchedOddPoleSource a : SoninL2) (Real.exp (a.1 / 2)) := by
  simpa only [ccmMatchedOddPoleSource, Function.iterate_zero, id_eq, pow_zero, one_mul] using
    ccmNormalizedWeilRemainder_odd_iterate_budget a 0

private theorem source_iterate_budget (a : SuzukiPositiveAperture)
    (p : suzukiApertureHilbert a) {V : ℝ} (hp : CCMFiniteExponentialBudget p.1 V) (n : ℕ) :
    CCMFiniteExponentialBudget (((ccmNormalizedWeilRemainder a)^[n]) p : SoninL2)
      ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * V) := by
  induction n with
  | zero => simpa only [Function.iterate_zero, id_eq, pow_zero, one_mul] using hp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      convert CCMFiniteExponentialBudget.normalized_remainder a _ ih using 1
      ring

private theorem recurrence_bound (d : ℕ → ℝ) {q C E η : ℝ}
    (hq : 0 ≤ q) (hC : q + 1 ≤ C) (hη : 0 ≤ η) (hzero : d 0 ≤ E)
    (hstep : ∀ n, d (n + 1) ≤ q * d n + η * C ^ n) (n : ℕ) :
    d n ≤ q ^ n * E + η * C ^ n := by
  have hC0 : 0 ≤ C := by linarith
  induction n with
  | zero => simpa using hzero.trans (le_add_of_nonneg_right hη)
  | succ n ih =>
    calc
      _ ≤ q * d n + η * C ^ n := hstep n
      _ ≤ q * (q ^ n * E + η * C ^ n) + η * C ^ n := by gcongr
      _ = q ^ (n + 1) * E + (q + 1) * (η * C ^ n) := by ring
      _ ≤ q ^ (n + 1) * E + C * (η * C ^ n) := by gcongr
      _ = _ := by ring

private theorem sum_geom_small {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ j ∈ range n, q ^ j ≤ 1 / (1 - q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq1)).2
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hq n]

private theorem sum_geom_large {C : ℝ} (hC : 2 ≤ C) (n : ℕ) :
    ∑ j ∈ range n, C ^ j ≤ C ^ n := by
  have hsum : 0 ≤ ∑ j ∈ range n, C ^ j := by positivity
  have hprod := geom_sum_mul C n
  nlinarith

/-- Source-uniform finite orbit control. The source amplitude is retained,
so transported smaller-aperture sources keep their original scale. -/
theorem eventually_ccmFiniteExponentialSource_finite_orbit_decay :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
        ‖p‖ ≤ V → CCMFiniteExponentialBudget p.1 V →
        ‖(ccmNormalizedWeilRemainder ⟨a, ha⟩)^[⌈a⌉₊] p‖ ≤ R * V * Real.exp (-4 * a) ∧
          ∑ j ∈ range ⌈a⌉₊, ‖(ccmNormalizedWeilRemainder ⟨a, ha⟩)^[j] p‖ ≤ M * V := by
  let C := 2 * (‖ccmArchimedeanRemainderScalar‖ + 46)
  let L := 4 * (‖ccmArchimedeanRemainderScalar‖ + 46) / Real.pi
  let q := Real.exp (-4)
  let K := 2 * Real.log C + 10
  have hC : 2 ≤ C := by dsimp [C]; linarith [norm_nonneg ccmArchimedeanRemainderScalar]
  have hCpos : 0 < C := by linarith
  have hlog : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
  have hL : 0 < L := by dsimp [L]; positivity
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by dsimp [q]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hK : 0 < K := by dsimp [K]; linarith
  let M := 1 / (1 - q) + L * C
  let R := 1 + L * C
  refine ⟨M, R, by dsimp [M]; positivity, by dsimp [R]; positivity, ?_⟩
  filter_upwards [eventually_ccmNormalizedWeilRemainder_budget_contraction K q hK hq]
    with a hrec
  intro ha p V hpNorm hpBudget
  let H := ccmNormalizedWeilRemainder ⟨a, ha⟩
  let η := L * V / Real.sqrt (Real.exp (K * a))
  have hV : 0 ≤ V := hpBudget.nonneg
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hnlo : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  have hnhi : (⌈a⌉₊ : ℝ) ≤ a + 1 := (Nat.ceil_lt_add_one ha.le).le
  have hstep (n : ℕ) : ‖H^[n + 1] p‖ ≤ q * ‖H^[n] p‖ + η * C ^ n := by
    rw [Function.iterate_succ_apply']
    convert hrec ha (H^[n] p) (C ^ n * V)
      (source_iterate_budget ⟨a, ha⟩ p hpBudget n) using 1
    all_goals dsimp only [H, η, C, L]
    all_goals ring
  have hb (n : ℕ) : ‖H^[n] p‖ ≤ q ^ n * V + η * C ^ n :=
    recurrence_bound (fun n => ‖H^[n] p‖) (q := q) (C := C) (E := V) (η := η)
      hq.le (by linarith) hη hpNorm
      hstep n
  have hqN : q ^ ⌈a⌉₊ * V ≤ V * Real.exp (-4 * a) := by
    have hqBound : q ^ ⌈a⌉₊ ≤ Real.exp (-4 * a) := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_right hqBound hV).trans_eq (mul_comm _ _)
  have hCN : C ^ ⌈a⌉₊ ≤ C * Real.exp (Real.log C * a) := by
    calc
      _ = Real.exp ((⌈a⌉₊ : ℝ) * Real.log C) := by rw [Real.exp_nat_mul, Real.exp_log hCpos]
      _ ≤ Real.exp ((a + 1) * Real.log C) := Real.exp_le_exp.mpr (by nlinarith)
      _ = C * Real.exp (Real.log C * a) := by
        rw [show (a + 1) * Real.log C = Real.log C + Real.log C * a by ring,
          Real.exp_add, Real.exp_log hCpos]
  have htailRate : η * C ^ ⌈a⌉₊ ≤ (L * C * V) * Real.exp (-5 * a) := by
    calc
      _ ≤ η * (C * Real.exp (Real.log C * a)) := mul_le_mul_of_nonneg_left hCN hη
      _ = (L * C * V) * Real.exp (-5 * a) := by
        dsimp [η, K]
        rw [sqrt_exp_eq_exp_half, div_eq_mul_inv, ← Real.exp_neg]
        rw [show L * V * Real.exp (-((2 * Real.log C + 10) * a / 2)) *
            (C * Real.exp (Real.log C * a)) = L * C * V *
              (Real.exp (-((2 * Real.log C + 10) * a / 2)) *
                Real.exp (Real.log C * a)) by ring]
        rw [← Real.exp_add]
        congr 2
        ring
  have htail : η * C ^ ⌈a⌉₊ ≤ L * C * V := by
    have hexp : Real.exp (-5 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact htailRate.trans ((mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq (mul_one _))
  constructor
  · have htailDecay : η * C ^ ⌈a⌉₊ ≤ L * C * V * Real.exp (-4 * a) :=
      htailRate.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (by positivity))
    exact (hb _).trans ((add_le_add hqN htailDecay).trans_eq (by dsimp [R]; ring))
  · calc
      _ ≤ ∑ j ∈ range ⌈a⌉₊, (q ^ j * V + η * C ^ j) := sum_le_sum (fun j _ => hb j)
      _ = (∑ j ∈ range ⌈a⌉₊, q ^ j) * V + η * (∑ j ∈ range ⌈a⌉₊, C ^ j) := by
        rw [sum_add_distrib, sum_mul, mul_sum]
      _ ≤ (1 / (1 - q)) * V + η * C ^ ⌈a⌉₊ :=
        add_le_add (mul_le_mul_of_nonneg_right (sum_geom_small hq.le hq1 _) hV)
          (mul_le_mul_of_nonneg_left (sum_geom_large hC _) hη)
      _ ≤ (1 / (1 - q)) * V + L * C * V := add_le_add (le_refl _) htail
      _ = M * V := by dsimp [M]; ring

/-- A growing number of actual source iterates has a uniform residual norm
and a source-scale bound for its complete finite norm sum. -/
theorem eventually_ccmMatchedOddPoleSource_finite_orbit_decay :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        let p := ccmMatchedOddPoleSource ⟨a, ha⟩
        let H := ccmNormalizedWeilRemainder ⟨a, ha⟩
        ‖H^[⌈a⌉₊] p‖ ≤ R * Real.exp (-7 * a / 2) ∧
          ∑ j ∈ range ⌈a⌉₊, ‖H^[j] p‖ ≤ M * Real.exp (a / 2) := by
  obtain ⟨M, R, hM, hR, hbound⟩ := eventually_ccmFiniteExponentialSource_finite_orbit_decay
  refine ⟨M, R, hM, hR, ?_⟩
  filter_upwards [hbound] with a haBound
  intro ha
  have h := haBound ha (ccmMatchedOddPoleSource ⟨a, ha⟩) (Real.exp (a / 2))
    (norm_ccmMatchedOddPoleSource_le ⟨a, ha⟩) (matched_odd_budget ⟨a, ha⟩)
  refine ⟨?_, h.2⟩
  convert h.1 using 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Coarse orbit bound retained for the uniform-energy interface. -/
theorem eventually_ccmMatchedOddPoleSource_finite_orbit_bound :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        let p := ccmMatchedOddPoleSource ⟨a, ha⟩
        let H := ccmNormalizedWeilRemainder ⟨a, ha⟩
        ‖H^[⌈a⌉₊] p‖ ≤ R ∧
          ∑ j ∈ range ⌈a⌉₊, ‖H^[j] p‖ ≤ M * Real.exp (a / 2) := by
  obtain ⟨M, R, hM, hR, h⟩ := eventually_ccmMatchedOddPoleSource_finite_orbit_decay
  refine ⟨M, R, hM, hR, ?_⟩
  filter_upwards [h] with a ha
  intro hap
  have he : Real.exp (-7 * a / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact ⟨(ha hap).1.trans (by nlinarith), (ha hap).2⟩

/-- Actual prescribed-shift bounded part of the completed Weil form. -/
def ccmShiftedBoundedWeil (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) • 1 +
    ccmRestrictedWeilBoundedRemainder a

/-- Literal finite Neumann vector for an arbitrary physical source. -/
def ccmFiniteNeumannVector (a : SuzukiPositiveAperture) (p : suzukiApertureHilbert a)
    (n : ℕ) : suzukiApertureHilbert a :=
  ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a))⁻¹ : ℂ) •
    ∑ j ∈ range n, (-1 : ℂ) ^ j • (ccmNormalizedWeilRemainder a)^[j] p

/-- Literal finite Neumann vector, with the prescribed interval shift. -/
def ccmMatchedOddNeumannVector (a : SuzukiPositiveAperture) (n : ℕ) :
    suzukiApertureHilbert a :=
  ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a))⁻¹ : ℂ) •
    ∑ j ∈ range n, (-1 : ℂ) ^ j • (ccmNormalizedWeilRemainder a)^[j]
      (ccmMatchedOddPoleSource a)

/-- The canonical finite vector preserves the full source endpoint budget. -/
theorem ccmFiniteNeumannVector_budget (a : SuzukiPositiveAperture)
    (p : suzukiApertureHilbert a) {V : ℝ} (hp : CCMFiniteExponentialBudget p.1 V) (n : ℕ) :
    CCMFiniteExponentialBudget (ccmFiniteNeumannVector a p n : SoninL2)
      ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * V /
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)) := by
  let C := 2 * (‖ccmArchimedeanRemainderScalar‖ + 46)
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let H := ccmNormalizedWeilRemainder a
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hC : 2 ≤ C := by dsimp [C]; linarith [norm_nonneg ccmArchimedeanRemainderScalar]
  have hj (j : ℕ) : CCMFiniteExponentialBudget
      (((-1 : ℂ) ^ j • H^[j] p : suzukiApertureHilbert a) : SoninL2)
      (C ^ j * V) := by
    have h := CCMFiniteExponentialBudget.smul ((-1 : ℂ) ^ j)
      (source_iterate_budget a p hp j)
    simpa only [C, H, Submodule.coe_smul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul] using h
  have hsum : CCMFiniteExponentialBudget
      ((∑ j ∈ range n, (-1 : ℂ) ^ j • H^[j] p : suzukiApertureHilbert a) : SoninL2)
      (∑ j ∈ range n, C ^ j * V) := by
    simpa only [Submodule.coe_sum] using CCMFiniteExponentialBudget.finset_sum (range n)
      (fun j => (((-1 : ℂ) ^ j • H^[j] p : suzukiApertureHilbert a) : SoninL2))
      (fun j => C ^ j * V) (fun j _ => hj j)
  apply (CCMFiniteExponentialBudget.smul (c⁻¹ : ℂ) hsum).mono
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, ← sum_mul]
  change c⁻¹ * ((∑ j ∈ range n, C ^ j) * V) ≤ _
  calc
    _ ≤ c⁻¹ * (C ^ n * V) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (sum_geom_large hC n) hp.nonneg)
        (inv_nonneg.mpr hc.le)
    _ = _ := by ring

/-- The actual finite test vector retains a certified Fourier endpoint budget. -/
theorem ccmMatchedOddNeumannVector_budget (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMFiniteExponentialBudget (ccmMatchedOddNeumannVector a n : SoninL2)
      ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a.1 / 2) /
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)) := by
  exact ccmFiniteNeumannVector_budget a (ccmMatchedOddPoleSource a) (matched_odd_budget a) n

private theorem finite_neumann_identity (a : SuzukiPositiveAperture)
    (p : suzukiApertureHilbert a) (n : ℕ) :
    let H := ccmNormalizedWeilRemainder a
    let S := ∑ j ∈ range n, (-1 : ℂ) ^ j • H^[j] p
    p - (S + H S) = (-1 : ℂ) ^ n • H^[n] p := by
  let H := ccmNormalizedWeilRemainder a
  let s := fun j : ℕ => (-1 : ℂ) ^ j • H^[j] p
  let S := fun n : ℕ => ∑ j ∈ range n, s j
  have hnext (j : ℕ) : H (s j) = -s (j + 1) := by
    change H ((-1 : ℂ) ^ j • H^[j] p) = -((-1 : ℂ) ^ (j + 1) • H^[j + 1] p)
    rw [map_smul, Function.iterate_succ_apply', pow_succ]
    simp only [mul_neg_one, neg_smul, neg_neg]
  have htel (n : ℕ) : S n + H (S n) = p - s n := by
    induction n with
    | zero => simp [S, s]
    | succ n ih =>
      change (∑ j ∈ range (n + 1), s j) + H (∑ j ∈ range (n + 1), s j) = _
      rw [Finset.sum_range_succ, map_add, hnext]
      change (S n + s n) + (H (S n) + -s (n + 1)) = _
      rw [show (S n + s n) + (H (S n) + -s (n + 1)) =
          (S n + H (S n)) + s n - s (n + 1) by abel, ih]
      abel
  change p - (S n + H (S n)) = s n
  rw [htel]
  abel

/-- Uniform finite inverse construction for every admitted physical source. -/
theorem eventually_ccmFiniteExponentialSource_neumann_decay :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
        ‖p‖ ≤ V → CCMFiniteExponentialBudget p.1 V →
        let u := ccmFiniteNeumannVector ⟨a, ha⟩ p ⌈a⌉₊
        ‖u‖ ≤ M * V / boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ⟨a, ha⟩) ∧
        ‖p - ccmShiftedBoundedWeil ⟨a, ha⟩ u‖ ≤ R * V * Real.exp (-4 * a) := by
  obtain ⟨M, R, hM, hR, hbound⟩ := eventually_ccmFiniteExponentialSource_finite_orbit_decay
  refine ⟨M, R, hM, hR, ?_⟩
  filter_upwards [hbound] with a haBound
  intro ha p V hpNorm hpBudget
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let H := ccmNormalizedWeilRemainder ap
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let S := ∑ j ∈ range ⌈a⌉₊, (-1 : ℂ) ^ j • H^[j] p
  let u := (c⁻¹ : ℂ) • S
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hnorm (j : ℕ) : ‖(-1 : ℂ) ^ j • H^[j] p‖ = ‖H^[j] p‖ := by
    rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hS : ‖S‖ ≤ M * V := by
    calc
      _ ≤ ∑ j ∈ range ⌈a⌉₊, ‖(-1 : ℂ) ^ j • H^[j] p‖ := norm_sum_le _ _
      _ = ∑ j ∈ range ⌈a⌉₊, ‖H^[j] p‖ := sum_congr rfl (fun j _ => hnorm j)
      _ ≤ _ := (haBound ha p V hpNorm hpBudget).2
  have hu : ‖u‖ ≤ M * V / c := by
    change ‖(c⁻¹ : ℂ) • S‖ ≤ _
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hc.le)
  have hA : ccmShiftedBoundedWeil ap u = S + H S := by
    change (c : ℂ) • ((c⁻¹ : ℂ) • S) +
      ccmRestrictedWeilBoundedRemainder ap ((c⁻¹ : ℂ) • S) = _
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul, map_smul]
    rfl
  refine ⟨hu, ?_⟩
  change ‖p - ccmShiftedBoundedWeil ap u‖ ≤ R * V * Real.exp (-4 * a)
  rw [hA]
  have hid := finite_neumann_identity ap p ⌈a⌉₊
  change p - (S + H S) = (-1 : ℂ) ^ ⌈a⌉₊ • H^[⌈a⌉₊] p at hid
  rw [hid, hnorm]
  exact (haBound ha p V hpNorm hpBudget).1

/-- A finite source-specific Neumann test vector for the actual bounded
Weil operator. All constants and the source recurrence are discharged. -/
theorem eventually_ccmMatchedOddPoleSource_neumann_decay :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        let u := ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊
        ‖u‖ ≤ M * Real.exp (a / 2) /
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ⟨a, ha⟩) ∧
        ‖ccmMatchedOddPoleSource ⟨a, ha⟩ - ccmShiftedBoundedWeil ⟨a, ha⟩ u‖ ≤
          R * Real.exp (-7 * a / 2) := by
  obtain ⟨M, R, hM, hR, hbound⟩ := eventually_ccmFiniteExponentialSource_neumann_decay
  refine ⟨M, R, hM, hR, ?_⟩
  filter_upwards [hbound] with a haBound
  intro ha
  have h := haBound ha (ccmMatchedOddPoleSource ⟨a, ha⟩) (Real.exp (a / 2))
    (norm_ccmMatchedOddPoleSource_le ⟨a, ha⟩) (matched_odd_budget ⟨a, ha⟩)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Uniform-residual interface, obtained from the literal decaying vector. -/
theorem eventually_ccmMatchedOddPoleSource_neumann_approximation :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        ∃ u : suzukiApertureHilbert ⟨a, ha⟩,
          ‖u‖ ≤ M * Real.exp (a / 2) /
            boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ⟨a, ha⟩) ∧
          ‖ccmMatchedOddPoleSource ⟨a, ha⟩ - ccmShiftedBoundedWeil ⟨a, ha⟩ u‖ ≤ R := by
  obtain ⟨M, R, hM, hR, h⟩ := eventually_ccmMatchedOddPoleSource_neumann_decay
  refine ⟨M, R, hM, hR, ?_⟩
  filter_upwards [h] with a ha
  intro hap
  have he : Real.exp (-7 * a / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact ⟨ccmMatchedOddNeumannVector ⟨a, hap⟩ ⌈a⌉₊, (ha hap).1,
    (ha hap).2.trans (by nlinarith)⟩

end RHTower
end
