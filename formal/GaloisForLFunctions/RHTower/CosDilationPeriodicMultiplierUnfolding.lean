import GaloisForLFunctions.RHTower.CosDilationDisjointSupportRigidity

/-!
# Periodic-multiplier unfolding, half-period annihilation, and support-boundary window rigidity

Let `f : ℝ → ℝ` be continuous and supported in `[α, β]` (`0 < α ≤ β`), with dilation
autocorrelation `A_f(r) = ∫_0^∞ f(y) f(ry) dy` (`dilationAutocorr`) and cosine–dilation kernel
`Ψ_f = Cf ⋆ f` (`cosDilationKernel`).

* **General periodic-multiplier unfolding** (`integral_tsum_dilationAutocorr_abs_mul_periodic`,
  `integral_tsum_dilationAutocorr_abs_mul_periodic_even`): for any continuous `1`-periodic
  multiplier `w : ℝ → ℝ` (`Function.Periodic w 1`),
  `∫ x in 0..1, (∑' k : ℤ, A_f(|x + k|)) * w(x) dx = ∫ r, A_f(|r|) * w(r) dr`,
  and when `w` is also even (`∀ r, w(-r) = w(r)`),
  `= 2 * ∫_{r > 0} A_f(r) * w(r) dr`.
* **Blind-core periodic-multiplier evaluation**
  (`integral_dilationAutocorr_abs_mul_periodic_of_blind`,
  `integral_Ioi_dilationAutocorr_mul_periodic_of_blind`): if `Ψ_f(n) = 0` for all `n ≥ 2`, then
  `∫ r, A_f(|r|) * w(r) dr = Ψ_f(0) ∫_0^1 w(x) dx + 2 Ψ_f(1) ∫_0^1 cos(2πx) w(x) dx`.
  When `Ψ_f(0) = 0` and `w` is even,
  `∫_{r > 0} A_f(r) * w(r) dr = Ψ_f(1) ∫_0^1 cos(2πx) w(x) dx`.
* **Half-period annihilation and sign-pattern rigidity**
  (`integral_half_periodic_mul_cos_two_pi_eq_zero`,
  `integral_dilationAutocorr_abs_mul_half_periodic_eq_zero`,
  `integral_Ioi_dilationAutocorr_mul_half_periodic_eq_zero`,
  `eq_zero_of_cosDilationKernel_blind_of_half_periodic_mul_nonneg`):
  every continuous `(1/2)`-periodic multiplier `w` (`Function.Periodic w (1/2)`) is orthogonal to
  `cos(2πx)` on `[0, 1]`, and therefore annihilates `A_f` whenever `Ψ_f(0) = 0` and `f` is blind:
  `∫_{r > 0} A_f(r) * w(r) dr = 0`. In particular, if `w(r) A_f(r) ≥ 0` on `(0, ∞)` and `w(1) ≠ 0`,
  then `f = 0`.
* **Subinterval periodization integral laws**
  (`intervalIntegral_tsum_dilationAutocorr_abs_eq`,
  `intervalIntegral_zero_quarter_tsum_dilationAutocorr_abs`,
  `intervalIntegral_quarter_half_tsum_dilationAutocorr_abs`,
  `intervalIntegral_zero_half_tsum_dilationAutocorr_abs`):
  `∫ x in a..b, (∑' k : ℤ, A_f(|x + k|)) dx = (Ψ_f(1) / π) (sin(2πb) − sin(2πa))`.
* **Support-boundary window law** (`dilationAutocorr_boundary_window_eq`):
  for `β ≤ (5/2)α` and `max(0, β/α − 2) ≤ x ≤ α/β`, the `k = 0` term `A_f(x)` vanishes identically
  and the Poisson periodization collapses to the three-term identity
  `A_f(1 − x) + A_f(1 + x) + A_f(2 − x) = 2 Ψ_f(1) cos(2πx)`.
-/

open MeasureTheory Set Real Filter

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### General periodic-multiplier unfolding for `dilationAutocorr` -/

/-- **General periodic-multiplier unfolding.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) and any continuous `1`-periodic
multiplier `w : ℝ → ℝ`, unfolding the periodization over `[0, 1]` yields
`∫ x in 0..1, (∑' k : ℤ, A_f(|x + k|)) * w(x) dx = ∫ r, A_f(|r|) * w(r) dr`. -/
theorem integral_tsum_dilationAutocorr_abs_mul_periodic (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w 1) :
    ∫ x in (0 : ℝ)..1, (∑' k : ℤ, dilationAutocorr f |x + k|) * w x =
      ∫ r, dilationAutocorr f |r| * w r := by
  set g : ℝ → ℝ := fun r => dilationAutocorr f |r| * w r with hg
  have hgc : Continuous g :=
    ((continuous_dilationAutocorr hf hα hsupp).comp continuous_abs).mul hwc
  obtain ⟨K, hK⟩ := exists_nat_gt (β / α + 1)
  have hzero : ∀ r, β / α < |r| → dilationAutocorr f |r| = 0 := fun r hr =>
    dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun h => by linarith [h.2]
  have hba : 0 ≤ β / α := div_nonneg (by linarith) hα.le
  have hK1 : (1 : ℝ) < K := by linarith
  have hgk : ∀ k : ℤ, Continuous fun x : ℝ => g (x + k) := fun k =>
    hgc.comp (continuous_id.add continuous_const)
  have hw_int : ∀ (k : ℤ) (x : ℝ), w (x + k) = w x := by
    intro k x
    simpa [mul_one] using hw.int_mul k x
  have hloc : ∀ x ∈ Icc (0 : ℝ) 1, (∑' k : ℤ, dilationAutocorr f |x + k|) * w x =
      ∑ k ∈ Finset.Ico (-(K : ℤ)) K, g (x + k) := by
    intro x hx
    rw [tsum_eq_sum (s := Finset.Ico (-(K : ℤ)) K) fun k hk => ?_, Finset.sum_mul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hg, hw_int]
    · refine hzero _ ?_
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
      rcases hk with hk | hk
      · have : (k : ℝ) ≤ -(K : ℝ) - 1 := by
          have : k ≤ -(K : ℤ) - 1 := by omega
          exact_mod_cast this
        rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2]
      · have : (K : ℝ) ≤ k := by exact_mod_cast hk
        rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1]
  rw [intervalIntegral.integral_congr fun x hx => hloc x (by rwa [uIcc_of_le zero_le_one] at hx),
    intervalIntegral.integral_finsetSum fun k _ => (hgk k).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_comp_add_right (fun r => g r), zero_add]
  have htile : ∑ k ∈ Finset.Ico (-(K : ℤ)) K, ∫ r in (k : ℝ)..1 + (k : ℝ), g r =
      ∫ r in (-(K : ℝ))..(K : ℝ), g r := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun j : ℕ => -(K : ℝ) + j) (n := 2 * K) fun j _ => hgc.intervalIntegrable _ _
    have e0 : (-(K : ℝ) + ((0 : ℕ) : ℝ)) = -(K : ℝ) := by simp
    have e1 : (-(K : ℝ) + ((2 * K : ℕ) : ℝ)) = K := by push_cast; ring
    simp only [e0, e1] at h
    rw [← h]
    refine Finset.sum_nbij' (fun k => (k + K).toNat) (fun j => (j : ℤ) - K) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_range]; omega
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Ico]; omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      omega
    · intro j _
      omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      have hk' : (((k + K).toNat : ℕ) : ℝ) = (k : ℝ) + K := by
        have : (((k + K).toNat : ℕ) : ℤ) = k + K := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      simp only [hk', Nat.cast_add, Nat.cast_one]
      congr 1 <;> ring
  rw [htile]
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  rw [intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => ?_]
  simp only [hg]
  rw [hzero r ?_, zero_mul]
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hr
  rcases hr with hr | hr
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **Half-line unfolding for even `1`-periodic multipliers.**
If `w : ℝ → ℝ` is continuous, `1`-periodic, and even (`∀ r, w(-r) = w(r)`), then
`∫ x in 0..1, (∑' k : ℤ, A_f(|x + k|)) * w(x) dx = 2 * ∫_{r > 0} A_f(r) * w(r) dr`. -/
theorem integral_tsum_dilationAutocorr_abs_mul_periodic_even (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w 1)
    (hwe : ∀ r, w (-r) = w r) :
    ∫ x in (0 : ℝ)..1, (∑' k : ℤ, dilationAutocorr f |x + k|) * w x =
      2 * ∫ r in Ioi (0 : ℝ), dilationAutocorr f r * w r := by
  rw [integral_tsum_dilationAutocorr_abs_mul_periodic hf hα hαβ hsupp hwc hw]
  have h := integral_comp_abs (f := fun r => dilationAutocorr f r * w r)
  have e : ∀ r : ℝ, w |r| = w r := by
    intro r
    rcases le_or_gt 0 r with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, hwe]
  simp only [e] at h
  exact h

/-! ### Blind-core periodic-multiplier evaluation -/

/-- **Blind-core periodic-multiplier evaluation.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(n) = 0` for all
`n ≥ 2`, then for any continuous `1`-periodic multiplier `w : ℝ → ℝ`,
`∫ r, A_f(|r|) * w(r) dr = Ψ_f(0) ∫_0^1 w(x) dx + 2 Ψ_f(1) ∫_0^1 cos(2πx) w(x) dx`. -/
theorem integral_dilationAutocorr_abs_mul_periodic_of_blind (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w 1) :
    ∫ r, dilationAutocorr f |r| * w r =
      cosDilationKernel f 0 * (∫ x in (0 : ℝ)..1, w x) +
        2 * cosDilationKernel f 1 * (∫ x in (0 : ℝ)..1, Real.cos (2 * π * x) * w x) := by
  rw [← integral_tsum_dilationAutocorr_abs_mul_periodic hf hα hαβ hsupp hwc hw]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP : ∀ x : ℝ, (∑' k : ℤ, dilationAutocorr f |x + k|) * w x =
      cosDilationKernel f 0 * w x +
        (2 * cosDilationKernel f 1) * (Real.cos (2 * π * x) * w x) := by
    intro x
    have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ x
    rw [← Complex.ofReal_tsum] at h
    rw [Complex.ofReal_injective h]
    ring
  simp_rw [hP]
  have hi1 : IntervalIntegrable (fun x => cosDilationKernel f 0 * w x) volume 0 1 :=
    (continuous_const.mul hwc).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun x => (2 * cosDilationKernel f 1) * (Real.cos (2 * π * x) * w x)) volume 0 1 :=
    (continuous_const.mul ((by fun_prop : Continuous fun x => Real.cos (2 * π * x)).mul hwc)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- **Half-line periodic-multiplier evaluation for blind cores with `Ψ_f(0) = 0`.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and
`Ψ_f(n) = 0` for all `n ≥ 2`, then for any continuous, even, `1`-periodic multiplier `w : ℝ → ℝ`,
`∫_{r > 0} A_f(r) * w(r) dr = Ψ_f(1) ∫_0^1 cos(2πx) w(x) dx`. -/
theorem integral_Ioi_dilationAutocorr_mul_periodic_of_blind (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w 1)
    (hwe : ∀ r, w (-r) = w r) :
    ∫ r in Ioi (0 : ℝ), dilationAutocorr f r * w r =
      cosDilationKernel f 1 * ∫ x in (0 : ℝ)..1, Real.cos (2 * π * x) * w x := by
  have h1 := integral_tsum_dilationAutocorr_abs_mul_periodic_even hf hα hαβ hsupp hwc hw hwe
  have h2 := integral_tsum_dilationAutocorr_abs_mul_periodic hf hα hαβ hsupp hwc hw
  have h3 := integral_dilationAutocorr_abs_mul_periodic_of_blind hf hα hαβ hsupp hblind hwc hw
  rw [h0, zero_mul, zero_add] at h3
  linarith

/-! ### Half-period annihilation and sign-pattern rigidity -/

/-- Any `(1/2)`-periodic function `w : ℝ → ℝ` is `1`-periodic. -/
theorem periodic_one_of_periodic_half {w : ℝ → ℝ} (hw : Function.Periodic w (1 / 2)) :
    Function.Periodic w 1 := by
  intro x
  have h1 : x + 1 = (x + 1 / 2) + 1 / 2 := by ring
  rw [h1, hw (x + 1 / 2), hw x]

/-- **Orthogonality of `(1/2)`-periodic multipliers to the fundamental harmonic `cos(2πx)`.**
For any continuous `(1/2)`-periodic function `w : ℝ → ℝ`,
`∫_0^1 cos(2πx) w(x) dx = 0`. -/
theorem integral_half_periodic_mul_cos_two_pi_eq_zero {w : ℝ → ℝ} (hwc : Continuous w)
    (hw : Function.Periodic w (1 / 2)) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * x) * w x = 0 := by
  have hcont : Continuous fun x => Real.cos (2 * π * x) * w x :=
    (by fun_prop : Continuous fun x => Real.cos (2 * π * x)).mul hwc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := 0) (b := 1 / 2) (c := 1) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hshift := intervalIntegral.integral_comp_add_right
    (fun x => Real.cos (2 * π * x) * w x) (1 / 2) (a := 0) (b := 1 / 2)
  have e0 : (0 : ℝ) + 1 / 2 = 1 / 2 := by ring
  have e1 : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
  rw [e0, e1] at hshift
  rw [← hshift]
  have hneg : ∀ x : ℝ, Real.cos (2 * π * (x + 1 / 2)) * w (x + 1 / 2) =
      -(Real.cos (2 * π * x) * w x) := by
    intro x
    have hcos : Real.cos (2 * π * (x + 1 / 2)) = -Real.cos (2 * π * x) := by
      rw [show 2 * π * (x + 1 / 2) = 2 * π * x + π by ring, Real.cos_add_pi]
    rw [hcos, hw x, neg_mul]
  simp_rw [hneg, intervalIntegral.integral_neg, add_neg_cancel]

/-- **Full-line half-period annihilation law.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0`, then
for any continuous `(1/2)`-periodic multiplier `w : ℝ → ℝ`,
`∫ r, A_f(|r|) * w(r) dr = 0`. -/
theorem integral_dilationAutocorr_abs_mul_half_periodic_eq_zero (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w (1 / 2)) :
    ∫ r, dilationAutocorr f |r| * w r = 0 := by
  rw [integral_dilationAutocorr_abs_mul_periodic_of_blind hf hα hαβ hsupp hblind hwc
      (periodic_one_of_periodic_half hw),
    h0, zero_mul, zero_add, integral_half_periodic_mul_cos_two_pi_eq_zero hwc hw, mul_zero]

/-- **Half-line half-period annihilation law.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0`, then
for any continuous, even, `(1/2)`-periodic multiplier `w : ℝ → ℝ`,
`∫_{r > 0} A_f(r) * w(r) dr = 0`. -/
theorem integral_Ioi_dilationAutocorr_mul_half_periodic_eq_zero (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w (1 / 2))
    (hwe : ∀ r, w (-r) = w r) :
    ∫ r in Ioi (0 : ℝ), dilationAutocorr f r * w r = 0 := by
  rw [integral_Ioi_dilationAutocorr_mul_periodic_of_blind hf hα hαβ hsupp h0 hblind hwc
      (periodic_one_of_periodic_half hw) hwe,
    integral_half_periodic_mul_cos_two_pi_eq_zero hwc hw, mul_zero]

/-- **Half-periodic multiplier sign-pattern rigidity.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0`, and
there exists a continuous `(1/2)`-periodic multiplier `w : ℝ → ℝ` with `w(1) ≠ 0` such that
`0 ≤ A_f(|r|) * w(r)` for all `r ∈ ℝ`, then `f = 0` everywhere. -/
theorem eq_zero_of_cosDilationKernel_blind_of_half_periodic_mul_nonneg (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw : Function.Periodic w (1 / 2))
    (hw1 : w 1 ≠ 0) (hnonneg : ∀ r : ℝ, 0 ≤ dilationAutocorr f |r| * w r) (y : ℝ) :
    f y = 0 := by
  set g : ℝ → ℝ := fun r => dilationAutocorr f |r| * w r with hg
  have hgc : Continuous g :=
    ((continuous_dilationAutocorr hf hα hsupp).comp continuous_abs).mul hwc
  have hg_supp : HasCompactSupport g :=
    (hasCompactSupport_dilationAutocorr_abs hα hαβ hsupp).mul_right
  have hg_int : Integrable g := hgc.integrable_of_hasCompactSupport hg_supp
  have hiz := integral_dilationAutocorr_abs_mul_half_periodic_eq_zero
    hf hα hαβ hsupp h0 hblind hwc hw
  have hae : g =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hg_int).mp hiz
  have heq := (Continuous.ae_eq_iff_eq volume hgc continuous_const).mp hae
  have hg1 : g 1 = 0 := congrFun heq 1
  simp only [hg, abs_one, mul_eq_zero] at hg1
  have hA1 : dilationAutocorr f 1 = 0 := hg1.resolve_right hw1
  exact eq_zero_of_dilationAutocorr_one_le_zero hf hα hsupp hA1.le y

/-! ### Subinterval periodization integral laws -/

/-- **Subinterval periodization integral law.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and
`Ψ_f(n) = 0` for all `n ≥ 2`, and any `a, b ∈ ℝ`,
`∫ x in a..b, (∑' k : ℤ, A_f(|x + k|)) dx = (Ψ_f(1) / π) * (sin(2πb) − sin(2πa))`. -/
theorem intervalIntegral_tsum_dilationAutocorr_abs_eq (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (a b : ℝ) :
    ∫ x in a..b, (∑' k : ℤ, dilationAutocorr f |x + k|) =
      cosDilationKernel f 1 / π * (Real.sin (2 * π * b) - Real.sin (2 * π * a)) := by
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP : ∀ x : ℝ, (∑' k : ℤ, dilationAutocorr f |x + k|) =
      2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by
    intro x
    have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ x
    rw [← Complex.ofReal_tsum, h0, zero_add] at h
    exact Complex.ofReal_injective h
  simp_rw [hP]
  rw [intervalIntegral.integral_const_mul]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcos := intervalIntegral.integral_comp_mul_left (a := a) (b := b) Real.cos h2pi
  simp only [integral_cos, smul_eq_mul] at hcos
  rw [hcos]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **First-quadrant periodization integral (`[0, 1/4]`).**
`∫ x in 0..(1/4), (∑' k : ℤ, A_f(|x + k|)) dx = Ψ_f(1) / π`. -/
theorem intervalIntegral_zero_quarter_tsum_dilationAutocorr_abs (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    ∫ x in (0 : ℝ)..(1 / 4), (∑' k : ℤ, dilationAutocorr f |x + k|) =
      cosDilationKernel f 1 / π := by
  rw [intervalIntegral_tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp h0 hblind]
  rw [mul_zero, Real.sin_zero, show 2 * π * (1 / 4 : ℝ) = π / 2 by ring, Real.sin_pi_div_two]
  ring

/-- **Second-quadrant periodization integral (`[1/4, 1/2]`).**
`∫ x in (1/4)..(1/2), (∑' k : ℤ, A_f(|x + k|)) dx = −Ψ_f(1) / π`. -/
theorem intervalIntegral_quarter_half_tsum_dilationAutocorr_abs (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    ∫ x in (1 / 4 : ℝ)..(1 / 2), (∑' k : ℤ, dilationAutocorr f |x + k|) =
      -(cosDilationKernel f 1 / π) := by
  rw [intervalIntegral_tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp h0 hblind]
  rw [show 2 * π * (1 / 2 : ℝ) = π by ring, Real.sin_pi,
    show 2 * π * (1 / 4 : ℝ) = π / 2 by ring, Real.sin_pi_div_two]
  ring

/-- **Half-period integral cancellation (`[0, 1/2]`).**
`∫ x in 0..(1/2), (∑' k : ℤ, A_f(|x + k|)) dx = 0`. -/
theorem intervalIntegral_zero_half_tsum_dilationAutocorr_abs (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    ∫ x in (0 : ℝ)..(1 / 2), (∑' k : ℤ, dilationAutocorr f |x + k|) = 0 := by
  rw [intervalIntegral_tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp h0 hblind]
  rw [mul_zero, Real.sin_zero, show 2 * π * (1 / 2 : ℝ) = π by ring, Real.sin_pi]
  ring

/-! ### Three-term support-boundary window law (`max(0, β/α − 2) ≤ x ≤ α/β`) -/

/-- **Three-term support-boundary window identity.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β ≤ (5/2)α`) with `Ψ_f(0) = 0` and
`Ψ_f(n) = 0` for all `n ≥ 2`, then for every `x ∈ ℝ` satisfying `0 ≤ x`, `β / α - 2 ≤ x`, and
`x ≤ α / β` (in particular at `x = α / β` whenever `β / α ≤ 1 + √2`), the `k = 0` term `A_f(x)`
vanishes identically and the Poisson periodization collapses to the three-term law
`A_f(1 − x) + A_f(1 + x) + A_f(2 − x) = 2 Ψ_f(1) cos(2πx)`. -/
theorem dilationAutocorr_boundary_window_eq (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 5 / 2 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {x : ℝ} (hx0 : 0 ≤ x) (hx_lo : β / α - 2 ≤ x) (hx_hi : x ≤ α / β) :
    dilationAutocorr f (1 - x) + dilationAutocorr f (1 + x) +
      dilationAutocorr f (2 - x) = 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hx1 : x ≤ 1 := hx_hi.trans ((div_le_one hβ0).mpr hαβ)
  have h3_bound : β / α ≤ 3 - x := by
    have h_quad : β * α + α * α ≤ 3 * (α * β) - β ^ 2 + β * α := by
      nlinarith [sq_nonneg (β - 3 / 2 * α)]
    have h_div : β / α + α / β ≤ 3 := by
      rw [div_add_div _ _ hα.ne' hβ0.ne', div_le_iff₀ (mul_pos hα hβ0)]
      nlinarith [sq_nonneg (β - 3 / 2 * α)]
    linarith
  have hZ : ∀ r : ℝ, (r ≤ α / β ∨ β / α ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ x
  rw [tsum_eq_sum (s := {-2, -1, 0, 1}) fun k hk => ?_] at hP
  rotate_left
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hZ _ ?_, Complex.ofReal_zero]
    right
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [abs_of_nonneg (by linarith)]; linarith
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [abs_of_neg (by linarith)]; linarith
  have a1 : |x + ((-2 : ℤ) : ℝ)| = 2 - x := by
    rw [Int.cast_neg, Int.cast_ofNat, abs_of_neg (by linarith)]; ring
  have a2 : |x + ((-1 : ℤ) : ℝ)| = 1 - x := by
    rw [Int.cast_neg, Int.cast_one, abs_of_nonpos (by linarith)]; ring
  have a3 : |x + ((0 : ℤ) : ℝ)| = x := by
    rw [Int.cast_zero, add_zero, abs_of_nonneg hx0]
  have a4 : |x + ((1 : ℤ) : ℝ)| = 1 + x := by
    rw [Int.cast_one, abs_of_pos (by linarith)]; ring
  have hxZ : dilationAutocorr f x = 0 := hZ x (Or.inl hx_hi)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    a1, a2, a3, a4, hxZ, h0] at hP
  have hP_re := congrArg Complex.re hP
  simp only [Complex.add_re, Complex.ofReal_re] at hP_re
  linarith

/-- **Support-boundary node identity at `x = α / β` for `β ≤ (1 + √2) α` (`β² − 2αβ − α² ≤ 0`).**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `β² − 2αβ − α² ≤ 0`, `Ψ_f(0) = 0`,
and `Ψ_f(n) = 0` for all `n ≥ 2`, then
`A_f(1 − α/β) + A_f(1 + α/β) + A_f(2 − α/β) = 2 Ψ_f(1) cos(2π α/β)`. -/
theorem dilationAutocorr_support_boundary_node_eq (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ_quad : β ^ 2 - 2 * α * β - α ^ 2 ≤ 0)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    dilationAutocorr f (1 - α / β) + dilationAutocorr f (1 + α / β) +
      dilationAutocorr f (2 - α / β) = 2 * cosDilationKernel f 1 * Real.cos (2 * π * (α / β)) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hβ52 : β ≤ 5 / 2 * α := by
    by_contra hlt
    have hgt : 5 / 2 * α < β := not_le.mp hlt
    nlinarith [sq_nonneg (β - 5 / 2 * α)]
  have hx_lo : β / α - 2 ≤ α / β := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_sub_div _ _ hα.ne' hβ0.ne',
      div_le_iff₀ (mul_pos hα hβ0)]
    linarith
  exact dilationAutocorr_boundary_window_eq hf hα hαβ hβ52 hsupp h0 hblind
    (div_nonneg hα.le hβ0.le) hx_lo le_rfl

end

end RHTower
