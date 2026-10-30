import Mathlib

/-!
# The amplifier law

An **amplifier** bounds the frequencies of a trace `a(n) = Σ_i c_i α_iⁿ` (an iteration parameter
`n`: Frobenius powers over `𝔽_q`, Hecke scales over `ℤ`) through the moments of a family that
contains it. Three facts make it work and fix what it can give.

1. **Rate = depth** (`norm_le_of_eventually_norm_le`). If `|a(n)| ≤ K Rⁿ` eventually, every
   frequency with nonzero coefficient has `|α_i| ≤ R`. The top frequencies, normalized, form an
   almost periodic sum tending to `0`; the difference operator `b(n + 1) − u_j b(n)` peels off one
   frequency at a time (`coeff_eq_zero_of_tendsto`), so all their coefficients vanish.
2. **Moments lose a root** (`norm_le_of_moment_bound`). A bound `|a(n)|^{2k} ≤ C (B^{2k} D)ⁿ` gives
   `|α_i| ≤ B D^{1/2k}`. Positivity transfers a family moment to each member
   (`norm_le_of_family_moment_bound`).
3. **Only the growth of the loss matters.** A *fixed* loss `D` for all `k` gives the sharp bound
   `|α_i| ≤ B` (`norm_le_of_fixed_loss`), and forces every frequency above `B` — a pole — to carry
   coefficient `0` (`pole_coefficient_eq_zero`): the family must kill its pole. An *envelope* loss
   `D_k = e^{2kλ}` gives `|α_i| ≤ B e^{λ}`, and this is attained (`envelope_moment_bound_attained`):
   loss exponents are strip widths and tensor powers add nothing.
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {ι : Type*} [DecidableEq ι]

/-! ## Rate = depth for finite exponential sums -/

/-- **Almost periodic sums that vanish at infinity are zero.** If `Σ_{i ∈ s} c_i u_iⁿ → 0` with
distinct unimodular `u_i`, every `c_i` is `0`. -/
theorem coeff_eq_zero_of_tendsto (s : Finset ι) (c u : ι → ℂ) (hu : ∀ i ∈ s, ‖u i‖ = 1)
    (hinj : Set.InjOn u s) (h : Tendsto (fun n : ℕ => ∑ i ∈ s, c i * u i ^ n) atTop (𝓝 0)) :
    ∀ i ∈ s, c i = 0 := by
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | insert j s hj ih =>
    have hus : ∀ i ∈ s, ‖u i‖ = 1 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hinjs : Set.InjOn u s := hinj.mono (by simp)
    -- the difference operator removes the frequency `u j`
    have hdiff : ∀ i ∈ s, c i * (u i - u j) = 0 := by
      refine ih (fun i => c i * (u i - u j)) hus hinjs ?_
      have h1 := (h.comp (tendsto_add_atTop_nat 1)).sub (h.const_mul (u j))
      rw [mul_zero, sub_zero] at h1
      refine h1.congr fun n => ?_
      have hterm : ∀ i, c i * (u i - u j) * u i ^ n = c i * u i ^ (n + 1) - u j * (c i * u i ^ n) :=
        fun i => by ring
      simp only [Function.comp, Finset.sum_insert hj, Finset.sum_congr rfl fun i _ => hterm i,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    have hs0 : ∀ i ∈ s, c i = 0 := fun i hi => by
      have hne : u i - u j ≠ 0 := sub_ne_zero.mpr fun he =>
        hj (by rw [hinj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self j s) he] at hi; exact hi)
      exact (mul_eq_zero.mp (hdiff i hi)).resolve_right hne
    -- what remains is `c_j u_jⁿ`, of constant modulus `|c_j|`
    have hj0 : c j = 0 := by
      have h2 : Tendsto (fun n : ℕ => c j * u j ^ n) atTop (𝓝 0) := by
        refine h.congr fun n => ?_
        rw [Finset.sum_insert hj, Finset.sum_eq_zero fun i hi => by rw [hs0 i hi, zero_mul],
          add_zero]
      have h3 := h2.norm
      simp only [norm_mul, norm_pow, hu j (Finset.mem_insert_self j s), one_pow, mul_one,
        norm_zero] at h3
      exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds h3)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hj0
    · exact hs0 i hi

/-- **Rate = depth.** If `|Σ_{i ∈ s} c_i α_iⁿ| ≤ K Rⁿ` for all large `n`, with distinct `α_i`, then
every `α_i` with `c_i ≠ 0` has `|α_i| ≤ R`. -/
theorem norm_le_of_eventually_norm_le (s : Finset ι) (c α : ι → ℂ) (hinj : Set.InjOn α s)
    {K R : ℝ} (hR : 0 ≤ R) (hK : ∀ᶠ n : ℕ in atTop, ‖∑ i ∈ s, c i * α i ^ n‖ ≤ K * R ^ n) :
    ∀ i ∈ s, c i ≠ 0 → ‖α i‖ ≤ R := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hc₀, hα₀⟩ := hcon
  -- the frequencies that are present, and their top modulus `M > R`
  set t := s.filter fun i => c i ≠ 0 with ht
  have hi₀t : i₀ ∈ t := Finset.mem_filter.mpr ⟨hi₀, hc₀⟩
  have htne : t.Nonempty := ⟨i₀, hi₀t⟩
  set M := t.sup' htne fun i => ‖α i‖ with hM
  have hMge : ‖α i₀‖ ≤ M := Finset.le_sup' (fun i => ‖α i‖) hi₀t
  have hRM : R < M := hα₀.trans_le hMge
  have hM0 : 0 < M := hR.trans_lt hRM
  obtain ⟨j₀, hj₀t, hj₀M⟩ := Finset.exists_mem_eq_sup' htne fun i => ‖α i‖
  set top := t.filter fun i => ‖α i‖ = M with htop
  have hj₀top : j₀ ∈ top := Finset.mem_filter.mpr ⟨hj₀t, hj₀M.symm⟩
  -- the normalized top part tends to `0`
  set u : ι → ℂ := fun i => α i / M with hu
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hsplit : ∀ n : ℕ, ∑ i ∈ top, c i * u i ^ n =
      (∑ i ∈ s, c i * α i ^ n) / (M : ℂ) ^ n -
        ∑ i ∈ t.filter (fun i => ¬ ‖α i‖ = M), c i * u i ^ n := by
    intro n
    have h1 : ∑ i ∈ s, c i * α i ^ n = ∑ i ∈ t, c i * α i ^ n := by
      rw [ht]
      exact (Finset.sum_filter_of_ne (p := fun i => c i ≠ 0)
        fun i _ hne hc => hne (by rw [hc, zero_mul])).symm
    rw [h1, Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not t (fun i => ‖α i‖ = M)]
    simp only [hu, div_pow, mul_div_assoc]
    ring
  have hlim1 : Tendsto (fun n : ℕ => (∑ i ∈ s, c i * α i ^ n) / (M : ℂ) ^ n) atTop (𝓝 0) := by
    have hq : Tendsto (fun n : ℕ => K * (R / M) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hM0.le)
        ((div_lt_one hM0).mpr hRM)).const_mul K
    refine squeeze_zero_norm' ?_ hq
    filter_upwards [hK] with n hn
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, div_pow,
      div_le_iff₀ (by positivity)]
    calc ‖∑ i ∈ s, c i * α i ^ n‖ ≤ K * R ^ n := hn
      _ = K * (R ^ n / M ^ n) * M ^ n := by field_simp
  have hlim2 : Tendsto (fun n : ℕ => ∑ i ∈ t.filter (fun i => ¬ ‖α i‖ = M), c i * u i ^ n)
      atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ i ∈ t.filter (fun i => ¬ ‖α i‖ = M), c i * 0 by simp]
    refine tendsto_finsetSum _ fun i hi => (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_).const_mul _
    obtain ⟨hit, hne⟩ := Finset.mem_filter.mp hi
    have hle : ‖α i‖ ≤ M := Finset.le_sup' (fun i => ‖α i‖) hit
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, div_lt_one hM0]
    exact lt_of_le_of_ne hle hne
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ top, c i * u i ^ n) atTop (𝓝 0) := by
    have := hlim1.sub hlim2
    rw [sub_zero] at this
    exact this.congr fun n => (hsplit n).symm
  -- so the top coefficients vanish, against `c j₀ ≠ 0`
  have hutop : ∀ i ∈ top, ‖u i‖ = 1 := fun i hi => by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0,
      (Finset.mem_filter.mp hi).2, div_self hM0.ne']
  have hinjtop : Set.InjOn u top := fun i hi j hj hij => by
    have hi' : i ∈ s := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hj' : j ∈ s := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
    exact hinj hi' hj' (by simpa [hu, div_left_inj' hMc] using hij)
  have := coeff_eq_zero_of_tendsto top c u hutop hinjtop hlim j₀ hj₀top
  exact (Finset.mem_filter.mp hj₀t).2 this

/-! ## Moments and losses -/

/-- `x ≤ C^{1/m} (y^{1/m})ⁿ` from `x^m ≤ C yⁿ`, for `x, y, C ≥ 0`. -/
theorem le_of_pow_le_mul_pow {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C) {m : ℕ}
    (hm : m ≠ 0) {n : ℕ} (h : x ^ m ≤ C * y ^ n) :
    x ≤ C ^ ((m : ℝ)⁻¹) * (y ^ ((m : ℝ)⁻¹)) ^ n := by
  have h1 : (x ^ m) ^ ((m : ℝ)⁻¹) ≤ (C * y ^ n) ^ ((m : ℝ)⁻¹) :=
    Real.rpow_le_rpow (pow_nonneg hx m) h (by positivity)
  rw [Real.pow_rpow_inv_natCast hx hm, Real.mul_rpow hC (pow_nonneg hy n)] at h1
  have hyn : (y ^ n) ^ ((m : ℝ)⁻¹) = (y ^ ((m : ℝ)⁻¹)) ^ n := by
    rw [← Real.rpow_natCast y n, ← Real.rpow_natCast (y ^ ((m : ℝ)⁻¹)) n, ← Real.rpow_mul hy,
      ← Real.rpow_mul hy, mul_comm]
  rwa [hyn] at h1

/-- **Moments lose a root.** If `|a(n)|^{2k} ≤ C (B^{2k} D)ⁿ` eventually, every frequency of
`a` with nonzero coefficient has `|α_i| ≤ B D^{1/2k}`. -/
theorem norm_le_of_moment_bound (s : Finset ι) (c α : ι → ℂ) (hinj : Set.InjOn α s) {B D C : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) {k : ℕ} (hk : k ≠ 0)
    (hmom : ∀ᶠ n : ℕ in atTop, ‖∑ i ∈ s, c i * α i ^ n‖ ^ (2 * k) ≤ C * (B ^ (2 * k) * D) ^ n) :
    ∀ i ∈ s, c i ≠ 0 → ‖α i‖ ≤ B * D ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
  have hm : 2 * k ≠ 0 := by omega
  have hy : 0 ≤ B ^ (2 * k) * D := by positivity
  have hroot : (B ^ (2 * k) * D) ^ (((2 * k : ℕ) : ℝ)⁻¹) = B * D ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
    rw [Real.mul_rpow (by positivity) hD, Real.pow_rpow_inv_natCast hB hm]
  refine norm_le_of_eventually_norm_le s c α hinj (K := (max C 0) ^ (((2 * k : ℕ) : ℝ)⁻¹))
    (by positivity) ?_
  filter_upwards [hmom] with n hn
  have h := le_of_pow_le_mul_pow (norm_nonneg _) hy (le_max_right C 0) hm
    (hn.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hy n)))
  rwa [hroot] at h

/-- **Positivity transfers a family moment to each member.** -/
theorem norm_le_of_family_moment_bound {X : Type*} (F : Finset X) (s : X → Finset ι)
    (c α : X → ι → ℂ) (hinj : ∀ x ∈ F, Set.InjOn (α x) (s x)) {B D C : ℝ} (hB : 0 ≤ B)
    (hD : 0 ≤ D) {k : ℕ} (hk : k ≠ 0)
    (hmom : ∀ᶠ n : ℕ in atTop,
      ∑ x ∈ F, ‖∑ i ∈ s x, c x i * α x i ^ n‖ ^ (2 * k) ≤ C * (B ^ (2 * k) * D) ^ n) :
    ∀ x ∈ F, ∀ i ∈ s x, c x i ≠ 0 → ‖α x i‖ ≤ B * D ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
  intro x hx
  refine norm_le_of_moment_bound (s x) (c x) (α x) (hinj x hx) (C := C) hB hD hk ?_
  filter_upwards [hmom] with n hn
  exact (Finset.single_le_sum (f := fun x => ‖∑ i ∈ s x, c x i * α x i ^ n‖ ^ (2 * k))
    (fun _ _ => by positivity) hx).trans hn

/-- **Fixed loss gives the sharp bound.** If for every tensor power `k ≥ 1` the moment bound holds
with the same loss `D`, every frequency with nonzero coefficient has `|α_i| ≤ B`. -/
theorem norm_le_of_fixed_loss (s : Finset ι) (c α : ι → ℂ) (hinj : Set.InjOn α s) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 < D)
    (hmom : ∀ k : ℕ, k ≠ 0 → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ‖∑ i ∈ s, c i * α i ^ n‖ ^ (2 * k) ≤ C * (B ^ (2 * k) * D) ^ n) :
    ∀ i ∈ s, c i ≠ 0 → ‖α i‖ ≤ B := by
  intro i hi hci
  have hle : ∀ k : ℕ, k ≠ 0 → ‖α i‖ ≤ B * D ^ (((2 * k : ℕ) : ℝ)⁻¹) := fun k hk => by
    obtain ⟨C, hC⟩ := hmom k hk
    exact norm_le_of_moment_bound s c α hinj hB hD.le hk hC i hi hci
  -- `D^{1/2k} → 1`
  have hlim : Tendsto (fun k : ℕ => B * D ^ (((2 * k : ℕ) : ℝ)⁻¹)) atTop (𝓝 (B * 1)) := by
    refine Tendsto.const_mul B ?_
    have h0 : Tendsto (fun k : ℕ => (((2 * k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp ?_
      exact tendsto_natCast_atTop_atTop.comp (tendsto_id.const_mul_atTop' (by norm_num))
    have hc := (Real.continuousAt_const_rpow (a := D) (b := 0) hD.ne').tendsto
    rw [Real.rpow_zero] at hc
    exact hc.comp h0
  rw [mul_one] at hlim
  exact ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun k hk => hle k (by omega))

/-- **The pole must be killed.** Under fixed-loss moment bounds, a frequency above `B` carries
coefficient `0`. -/
theorem pole_coefficient_eq_zero (s : Finset ι) (c α : ι → ℂ) (hinj : Set.InjOn α s) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 < D)
    (hmom : ∀ k : ℕ, k ≠ 0 → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ‖∑ i ∈ s, c i * α i ^ n‖ ^ (2 * k) ≤ C * (B ^ (2 * k) * D) ^ n)
    {j : ι} (hj : j ∈ s) (hpole : B < ‖α j‖) : c j = 0 := by
  by_contra hc
  exact absurd (norm_le_of_fixed_loss s c α hinj hB hD hmom j hj hc) (not_le.mpr hpole)

/-- **Envelope losses are attained.** The single frequency `α = B e^{λ}` satisfies the moment bound
with loss `D_k = e^{2kλ}` at every tensor power, so the bound `B e^{λ}` given by an envelope loss
cannot be improved by taking `k` larger. -/
theorem envelope_moment_bound_attained {B : ℝ} (hB : 0 ≤ B) (lam : ℝ) (k n : ℕ) :
    ‖((B * Real.exp lam : ℝ) : ℂ) ^ n‖ ^ (2 * k) =
      1 * (B ^ (2 * k) * Real.exp (2 * k * lam)) ^ n := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul,
    ← pow_mul, mul_comm n, pow_mul, mul_pow, ← Real.exp_nat_mul]
  push_cast
  ring_nf

end GaloisForLFunctions.ArithmeticResonanceTheory
