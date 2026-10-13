import GaloisForLFunctions.RHTower.DilationAutocorrelationPeriodization

/-!
# Blind cores and the Mayer transfer operator at `s = ½`

Let `A : (0, ∞) → ℝ` satisfy the inversion law `A(1/r) = r A(r)`, and put

`Q_A(t) = A(t/(1−t))/(1−t)`   (`mayerProfile`),   `(L Q)(x) = Σ_{m≥1} Q(1/(m+x))/(m+x)`
(`mayerTransferHalf`, the Mayer transfer operator of the Gauss map at `s = ½`).

* `Q_A(1 − t) = Q_A(t)` (`mayerProfile_one_sub`), and `A(y) = Q_A(1/(1+y))/(1+y)` for `y > 0`
  (`eq_mayerProfile`): the inversion law is exactly the symmetry `t ↦ 1 − t` of the profile.
* **Periodization as a transfer operator** (`tsum_abs_add_eq_mayerTransferHalf`): if `A` vanishes on
  `[R, ∞)`, then for `0 < x < 1`

  `Σ_{k ∈ ℤ} A(|x + k|) = (L Q_A)(x) + (L Q_A)(1 − x)`.

  The terms `k ≥ 0` are `A(x + k) = Q_A(1/(k+1+x))/(k+1+x)`, and the terms `k = −(j+1)` are
  `A(j + 1 − x) = Q_A(1/(j+1+(1−x)))/(j+1+(1−x))`.
* For the dilation autocorrelation `A_f` of a continuous core `f` supported in `[α, β] ⊂ (0, ∞)`
  (`mayerTransferHalf_eq_of_cosDilationKernel_blind`): if `Ψ_f = Cf ⋆ f` vanishes at every integer
  `|n| ≥ 2`, then `(1 + σ) L Q_{A_f} = Ψ_f(0) + 2Ψ_f(1) cos 2πx` on `(0, 1)`, with `σ x = 1 − x`.  So blindness of
  a compact core is an inhomogeneous transfer equation of the Gauss map at the centre of the critical
  strip.
* Conversely (`cosDilationKernel_eq_zero_of_mayerTransferHalf_eq`), if `(1 + σ) L Q_{A_f}` equals some
  `a + b cos 2πx` on `(0, 1)`, then `Ψ_f(n) = 0` for all `|n| ≥ 2`: unfolding `∫_0^1 Σ_k A(|x+k|) cos 2πnx`
  gives `Ψ_f(n)`.  Together: blindness `⟺` the Mayer equation (`cosDilationKernel_blind_iff_mayerTransferHalf`).
-/

open MeasureTheory Set Real

namespace RHTower

noncomputable section

/-- The profile `Q_A(t) = A(t/(1−t))/(1−t)`. -/
def mayerProfile (A : ℝ → ℝ) (t : ℝ) : ℝ := A (t / (1 - t)) / (1 - t)

/-- The Mayer transfer operator at `s = ½`: `(L Q)(x) = Σ_{m≥1} Q(1/(m+x))/(m+x)`. -/
def mayerTransferHalf (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' m : ℕ, Q (1 / ((m : ℝ) + 1 + x)) / ((m : ℝ) + 1 + x)

/-- **The inversion law is the symmetry of the profile.** -/
theorem mayerProfile_one_sub {A : ℝ → ℝ} (hinv : ∀ r, 0 < r → A r⁻¹ = r * A r) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : mayerProfile A (1 - t) = mayerProfile A t := by
  unfold mayerProfile
  have h1 : 0 < 1 - t := by linarith
  have hr : 0 < t / (1 - t) := div_pos ht0 h1
  have e1 : (1 - t) / (1 - (1 - t)) = (t / (1 - t))⁻¹ := by
    rw [inv_div, show 1 - (1 - t) = t by ring]
  rw [e1, hinv _ hr, show 1 - (1 - t) = t by ring]
  field_simp

/-- `A(y) = Q_A(1/(1+y))/(1+y)` for `y > 0`. -/
theorem eq_mayerProfile {A : ℝ → ℝ} (hinv : ∀ r, 0 < r → A r⁻¹ = r * A r) {y : ℝ} (hy : 0 < y) :
    A y = mayerProfile A (1 / (1 + y)) / (1 + y) := by
  unfold mayerProfile
  have h1 : (0 : ℝ) < 1 + y := by linarith
  have e1 : 1 / (1 + y) / (1 - 1 / (1 + y)) = y⁻¹ := by
    rw [show 1 - 1 / (1 + y) = y / (1 + y) by field_simp; ring]
    field_simp
  have e2 : 1 - 1 / (1 + y) = y / (1 + y) := by field_simp; ring
  rw [e1, hinv _ hy, e2]
  field_simp

/-- **The periodization is `(1 + σ) L Q_A`.** -/
theorem tsum_abs_add_eq_mayerTransferHalf {A : ℝ → ℝ} (hinv : ∀ r, 0 < r → A r⁻¹ = r * A r)
    {R : ℝ} (hR : ∀ r, R ≤ r → A r = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' k : ℤ, A |x + k| =
      mayerTransferHalf (mayerProfile A) x + mayerTransferHalf (mayerProfile A) (1 - x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt R
  have hpos : ∀ n : ℕ, A |x + ((n : ℤ) : ℝ)| =
      mayerProfile A (1 / ((n : ℝ) + 1 + x)) / ((n : ℝ) + 1 + x) := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [Int.cast_natCast, abs_of_pos (by linarith), eq_mayerProfile hinv (by linarith)]
    rw [show 1 + (x + (n : ℝ)) = (n : ℝ) + 1 + x by ring]
  have hneg : ∀ n : ℕ, A |x + ((-((n : ℤ) + 1) : ℤ) : ℝ)| =
      mayerProfile A (1 / ((n : ℝ) + 1 + (1 - x))) / ((n : ℝ) + 1 + (1 - x)) := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have e : x + ((-((n : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + 1 - x) := by push_cast; ring
    rw [e, abs_neg, abs_of_pos (by linarith), eq_mayerProfile hinv (by linarith)]
    rw [show 1 + ((n : ℝ) + 1 - x) = (n : ℝ) + 1 + (1 - x) by ring]
  have hv1 : ∀ n ∉ Finset.range N, A |x + ((n : ℤ) : ℝ)| = 0 := fun n hn => by
    have : N ≤ n := by simpa using hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast this
    rw [Int.cast_natCast, abs_of_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
    exact hR _ (by linarith)
  have hv2 : ∀ n ∉ Finset.range N, A |x + ((-((n : ℤ) + 1) : ℤ) : ℝ)| = 0 := fun n hn => by
    have : N ≤ n := by simpa using hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast this
    have e : x + ((-((n : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + 1 - x) := by push_cast; ring
    rw [e, abs_neg, abs_of_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
    exact hR _ (by linarith)
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ => A |x + (k : ℝ)|)
    (summable_of_ne_finset_zero hv1) (summable_of_ne_finset_zero hv2)]
  unfold mayerTransferHalf
  congr 1
  · exact tsum_congr hpos
  · exact tsum_congr hneg

/-- **Blind cores solve the inhomogeneous Mayer equation at `s = ½`.** -/
theorem mayerTransferHalf_eq_of_cosDilationKernel_blind {f : ℝ → ℝ} (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) :
    mayerTransferHalf (mayerProfile (dilationAutocorr f)) x +
        mayerTransferHalf (mayerProfile (dilationAutocorr f)) (1 - x) =
      cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by
  have hinv : ∀ r, 0 < r → dilationAutocorr f r⁻¹ = r * dilationAutocorr f r :=
    fun r hr => dilationAutocorr_inv f hr
  have hR : ∀ r, β / α + 1 ≤ r → dilationAutocorr f r = 0 := fun r hr =>
    dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun h => by linarith [h.2]
  rw [← tsum_abs_add_eq_mayerTransferHalf hinv hR hx0 hx1]
  have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblind x
  rw [← Complex.ofReal_tsum] at h
  exact Complex.ofReal_injective h

/-! ### The converse: the Mayer equation forces blindness -/

theorem integral_cos_two_pi_nonzero_int_mul {m : ℤ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * m * x) = 0 := by
  have hc : (2 * π * m : ℝ) ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    positivity
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) Real.cos hc
  simp only [mul_zero, mul_one, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul] at h
  rw [h, show 2 * π * (m : ℝ) = ((2 * m : ℤ) : ℝ) * π by push_cast; ring, Real.sin_int_mul_pi,
    mul_zero]

/-- Degree-one cosine polynomials are orthogonal to `cos 2πnx` for `|n| ≥ 2`. -/
theorem integral_affine_cos_mul_cos_eq_zero (a b : ℝ) {n : ℤ} (hn : 2 ≤ |n|) :
    ∫ x in (0 : ℝ)..1, (a + b * Real.cos (2 * π * x)) * Real.cos (2 * π * (n * x)) = 0 := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; norm_num at hn
  have hn1 : n - 1 ≠ 0 := by
    intro h
    have : n = 1 := by omega
    rw [this] at hn; norm_num at hn
  have hn2 : n + 1 ≠ 0 := by
    intro h
    have : n = -1 := by omega
    rw [this] at hn; norm_num at hn
  have e : ∀ x : ℝ, (a + b * Real.cos (2 * π * x)) * Real.cos (2 * π * (n * x)) =
      a * Real.cos (2 * π * (n : ℤ) * x) + (b / 2) * Real.cos (2 * π * ((n - 1 : ℤ) : ℝ) * x) +
        (b / 2) * Real.cos (2 * π * ((n + 1 : ℤ) : ℝ) * x) := by
    intro x
    have h1 : Real.cos (2 * π * ((n - 1 : ℤ) : ℝ) * x) =
        Real.cos (2 * π * (n * x) - 2 * π * x) := by push_cast; ring_nf
    have h2 : Real.cos (2 * π * ((n + 1 : ℤ) : ℝ) * x) =
        Real.cos (2 * π * (n * x) + 2 * π * x) := by push_cast; ring_nf
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_two_pi_nonzero_int_mul hn0, integral_cos_two_pi_nonzero_int_mul hn1,
    integral_cos_two_pi_nonzero_int_mul hn2]
  · ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- **Unfolding**: the Fourier coefficients of the periodization of `A_f(|·|)` are `Ψ_f(n)`. -/
theorem integral_tsum_dilationAutocorr_abs_mul_cos {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (n : ℤ) :
    ∫ x in (0 : ℝ)..1, (∑' k : ℤ, dilationAutocorr f |x + k|) * Real.cos (2 * π * (n * x)) =
      cosDilationKernel f n := by
  set g : ℝ → ℝ := fun r => dilationAutocorr f |r| * Real.cos (2 * π * ((n : ℝ) * r)) with hg
  have hgc : Continuous g :=
    ((continuous_dilationAutocorr hf hα hsupp).comp continuous_abs).mul (by fun_prop)
  obtain ⟨K, hK⟩ := exists_nat_gt (β / α + 1)
  have hzero : ∀ r, β / α < |r| → dilationAutocorr f |r| = 0 := fun r hr =>
    dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun h => by linarith [h.2]
  have hba : 0 ≤ β / α := div_nonneg (by linarith) hα.le
  have hK1 : (1 : ℝ) < K := by linarith
  have hgk : ∀ k : ℤ, Continuous fun x : ℝ => g (x + k) := fun k =>
    hgc.comp (continuous_id.add continuous_const)
  -- on `[0, 1]` the periodization is a finite sum of translates of `g`
  have hloc : ∀ x ∈ Icc (0 : ℝ) 1, (∑' k : ℤ, dilationAutocorr f |x + k|) *
      Real.cos (2 * π * (n * x)) = ∑ k ∈ Finset.Ico (-(K : ℤ)) K, g (x + k) := by
    intro x hx
    rw [tsum_eq_sum (s := Finset.Ico (-(K : ℤ)) K) fun k hk => ?_, Finset.sum_mul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hg]
      congr 1
      have : 2 * π * ((n : ℝ) * (x + k)) = 2 * π * (n * x) + ((n * k : ℤ) : ℝ) * (2 * π) := by
        push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
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
  -- the translates tile `[−K, K]`
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
    · intro j hj
      omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      have hk' : (((k + K).toNat : ℕ) : ℝ) = (k : ℝ) + K := by
        have : (((k + K).toNat : ℕ) : ℤ) = k + K := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      simp only [hk', Nat.cast_add, Nat.cast_one]
      congr 1 <;> ring
  rw [htile]
  -- outside `[−K, K]` the integrand vanishes
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  rw [intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => ?_,
    cosDilationKernel_eq_integral_abs hf hα hαβ hsupp]
  · simp only [hg]
    rw [hzero r ?_, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hr
    rcases hr with hr | hr
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- **The Mayer equation forces blindness.**  If `(1 + σ) L Q_{A_f}` is a cosine polynomial of
degree at most one on `(0, 1)`, then `Ψ_f(n) = 0` for every integer `|n| ≥ 2`. -/
theorem cosDilationKernel_eq_zero_of_mayerTransferHalf_eq {f : ℝ → ℝ} (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (a b : ℝ)
    (hM : ∀ x ∈ Ioo (0 : ℝ) 1, mayerTransferHalf (mayerProfile (dilationAutocorr f)) x +
        mayerTransferHalf (mayerProfile (dilationAutocorr f)) (1 - x) =
      a + b * Real.cos (2 * π * x))
    {n : ℤ} (hn : 2 ≤ |n|) : cosDilationKernel f n = 0 := by
  have hinv : ∀ r, 0 < r → dilationAutocorr f r⁻¹ = r * dilationAutocorr f r :=
    fun r hr => dilationAutocorr_inv f hr
  have hR : ∀ r, β / α + 1 ≤ r → dilationAutocorr f r = 0 := fun r hr =>
    dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun h => by linarith [h.2]
  rw [← integral_tsum_dilationAutocorr_abs_mul_cos hf hα hαβ hsupp n]
  refine (intervalIntegral.integral_congr_ae ?_).trans (integral_affine_cos_mul_cos_eq_zero a b hn)
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 1] with x hx1 hx
  rw [uIoc_of_le zero_le_one] at hx
  rw [tsum_abs_add_eq_mayerTransferHalf hinv hR hx.1 (lt_of_le_of_ne hx.2 hx1),
    hM x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩]

/-- **Blindness of a compact core is the Mayer equation at `s = ½`.** -/
theorem cosDilationKernel_blind_iff_mayerTransferHalf {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    (∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) ↔
      ∃ a b : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1,
        mayerTransferHalf (mayerProfile (dilationAutocorr f)) x +
          mayerTransferHalf (mayerProfile (dilationAutocorr f)) (1 - x) =
        a + b * Real.cos (2 * π * x) := by
  constructor
  · intro hblind
    refine ⟨cosDilationKernel f 0, 2 * cosDilationKernel f 1, fun x hx => ?_⟩
    rw [mayerTransferHalf_eq_of_cosDilationKernel_blind hf hα hαβ hsupp hblind hx.1 hx.2]
  · rintro ⟨a, b, hM⟩ n hn
    exact cosDilationKernel_eq_zero_of_mayerTransferHalf_eq hf hα hαβ hsupp a b hM hn

end

end RHTower
