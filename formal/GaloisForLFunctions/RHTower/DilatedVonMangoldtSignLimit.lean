import GaloisForLFunctions.RHTower.VonMangoldtSignBlock
import GaloisForLFunctions.HTGeometry.SignedHarmonicPair
import GaloisForLFunctions.HTGeometry.SgnSinIntegral

/-!
# The dilated von Mangoldt square wave

For every `α` with `0 < α ≤ π`,

`(1/T) ∑_{m ≤ T} Λ(m) sgn (sin (α T / m)) → 1 - 2 α log 2 / π`.

The square wave `sgn (sin (α T / m))` is constant equal to `(-1)^k` on the block of `m` for which
`α T / m` lies in the `k`-th half period, so the sum telescopes into an alternating difference of
Chebyshev sums at the block endpoints `⌊α T /(k π)⌋`.  Each endpoint carries the proportion
`α/(k π)` by the prime number theorem, and the resulting alternating series of harmonic gaps
`∑_{k ≥ 1} (-1)^k (1/k - 1/(k+1)) = 1 - 2 log 2` supplies the constant.

The limit is the value `α ∫_α^∞ sgn (sin x)/x² dx` of the corresponding square-wave integral.
-/

open Filter ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators
open Real

namespace RHTower

theorem blockScale_zero (α : ℝ) : blockScale α 0 = 1 := by
  rw [blockScale, if_pos rfl]

/-- Below the first half period the scale is exactly the harmonic proportion. -/
theorem blockScale_of_le_pi {α : ℝ} (hα : 0 < α) (hαπ : α ≤ π) {k : ℕ} (hk : 1 ≤ k) :
    blockScale α k = α / ((k : ℝ) * π) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkπ : (0 : ℝ) < (k : ℝ) * π := by nlinarith
  rw [blockScale, if_neg (by omega : ¬k = 0)]
  refine min_eq_right ?_
  rw [div_le_one hkπ]
  nlinarith

/-- The alternating telescope of the block scales is the signed harmonic gap series. -/
theorem sum_blockScale_telescope {α : ℝ} (hα : 0 < α) (hαπ : α ≤ π) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * (blockScale α k - blockScale α (k + 1))
      = (1 - α / π) + (α / π) * ∑ j ∈ Finset.range K, signedHarmonicPair j := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  induction K with
  | zero =>
      rw [Finset.sum_range_one, Finset.sum_range_zero, blockScale_zero,
        blockScale_of_le_pi hα hαπ (le_refl 1)]
      norm_num
  | succ K ih =>
      have h1 : blockScale α (K + 1) = α / (((K : ℝ) + 1) * π) := by
        rw [blockScale_of_le_pi hα hαπ (by omega : 1 ≤ K + 1)]
        push_cast
        ring
      have h2 : blockScale α (K + 1 + 1) = α / (((K : ℝ) + 2) * π) := by
        rw [blockScale_of_le_pi hα hαπ (by omega : 1 ≤ K + 1 + 1)]
        push_cast
        ring
      have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
      have key : α / (((K : ℝ) + 1) * π) - α / (((K : ℝ) + 2) * π)
          = α / π * (1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 2)) := by
        field_simp
      rw [Finset.sum_range_succ (n := K + 1), ih, Finset.sum_range_succ (n := K),
        h1, h2, signedHarmonicPair, key]
      ring

theorem tendsto_sum_blockScale_telescope {α : ℝ} (hα : 0 < α) (hαπ : α ≤ π) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K,
        (-1 : ℝ) ^ k * (blockScale α k - blockScale α (k + 1))) atTop
      (𝓝 (1 - 2 * α * Real.log 2 / π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hpart : Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, signedHarmonicPair j) atTop
      (𝓝 (1 - 2 * Real.log 2)) :=
    summable_signedHarmonicPair.hasSum_iff_tendsto_nat.mp hasSum_signedHarmonicPair
  have hlim := (hpart.const_mul (α / π)).const_add (1 - α / π)
  have hval : (1 - α / π) + α / π * (1 - 2 * Real.log 2) = 1 - 2 * α * Real.log 2 / π := by
    field_simp
    ring
  rw [hval] at hlim
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  exact hlim.congr fun K => (sum_blockScale_telescope hα hαπ K).symm

/-- A von Mangoldt sum against a weight of modulus at most one is dominated by `psi`. -/
theorem abs_sum_Ioc_vonMangoldt_mul_le (N : ℕ) (g : ℕ → ℝ) (hg : ∀ m, |g m| ≤ 1) :
    |∑ m ∈ Finset.Ioc 0 N, (vonMangoldt m : ℝ) * g m| ≤ chebyshevPsi N := by
  calc |∑ m ∈ Finset.Ioc 0 N, (vonMangoldt m : ℝ) * g m|
      ≤ ∑ m ∈ Finset.Ioc 0 N, |(vonMangoldt m : ℝ) * g m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ioc 0 N, (vonMangoldt m : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        nlinarith [hg m, vonMangoldt_nonneg (n := m), abs_nonneg (g m)]
    _ = chebyshevPsi N := (chebyshevPsi_eq_sum_Ioc N).symm

/-- **The dilated von Mangoldt square-wave limit.** -/
theorem tendsto_dilated_vonMangoldt_sign_sum {α : ℝ} (hα : 0 < α) (hαπ : α ≤ π) :
    Tendsto (fun T : ℝ => (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
        (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))) / T) atTop
      (𝓝 (1 - 2 * α * Real.log 2 / π)) := by
  obtain ⟨C, hC0, hCle⟩ := exists_chebyshevPsiReal_le_linear
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose a block count `K` making both the Chebyshev tail and the series tail small.
  have htend : Tendsto (fun K : ℕ => C * α / (π * (K : ℝ))) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.Tendsto.const_mul_atTop hπ tendsto_natCast_atTop_atTop)
  have hKA : ∀ᶠ K : ℕ in atTop, C * α / (π * (K : ℝ)) < ε / 4 :=
    htend.eventually (eventually_lt_nhds (by linarith))
  have hKB : ∀ᶠ K : ℕ in atTop,
      |(∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * (blockScale α k - blockScale α (k + 1)))
        - (1 - 2 * α * Real.log 2 / π)| < ε / 4 := by
    have h := (tendsto_sum_blockScale_telescope hα hαπ).eventually
      (Metric.ball_mem_nhds (1 - 2 * α * Real.log 2 / π) (by linarith : (0 : ℝ) < ε / 4))
    filter_upwards [h] with K hK
    rwa [Real.dist_eq] at hK
  obtain ⟨K, ⟨hKa, hKb⟩, hK1⟩ := ((hKA.and hKB).and (eventually_ge_atTop 1)).exists
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  set L : ℝ := ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * (blockScale α k - blockScale α (k + 1))
    with hLdef
  -- The `T`-side conditions, all for this fixed `K`.
  have hT2 : ∀ᶠ T : ℝ in atTop, (K : ℝ) * Real.log T / T < ε / 4 := by
    have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h := (hlog.const_mul (K : ℝ))
    rw [mul_zero] at h
    have h' := h.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 4))
    filter_upwards [h'] with T hT
    calc (K : ℝ) * Real.log T / T = (K : ℝ) * (Real.log T / T) := by ring
      _ < ε / 4 := hT
  have hT3 : ∀ᶠ T : ℝ in atTop,
      |(∑ k ∈ Finset.range K, (-1 : ℝ) ^ k *
          (chebyshevPsi (blockEndpoint α T k) - chebyshevPsi (blockEndpoint α T (k + 1)))) / T
        - L| < ε / 4 := by
    have h := (tendsto_head_blocks hα K).eventually
      (Metric.ball_mem_nhds L (by linarith : (0 : ℝ) < ε / 4))
    filter_upwards [h] with T hT
    rwa [Real.dist_eq] at hT
  have hT4 : ∀ᶠ T : ℝ in atTop, (1 : ℝ) ≤ blockScale α K * T := by
    have h : Tendsto (fun T : ℝ => blockScale α K * T) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (blockScale_pos hα K) tendsto_id
    exact h.eventually_ge_atTop 1
  obtain ⟨T₀, hT₀⟩ :=
    (((eventually_ge_atTop (1 : ℝ)).and hT2).and (hT3.and hT4)).exists_forall_of_atTop
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨⟨hTge1, hTlog⟩, hTtel, hTscale⟩ := hT₀ T hT
  have hTpos : (0 : ℝ) < T := by linarith
  set n : ℕ := blockEndpoint α T K with hndef
  set tail : ℝ := ∑ m ∈ Finset.Ioc 0 n, (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))
    with htaildef
  set S : ℝ := ∑ m ∈ Finset.Ioc n ⌊T⌋₊, (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))
    with hSdef
  set Tel : ℝ := ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k *
      (chebyshevPsi (blockEndpoint α T k) - chebyshevPsi (blockEndpoint α T (k + 1))) with hTeldef
  have hsum : ∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
      (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)) = tail + S :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (blockEndpoint_le_floor α T K)).symm
  rw [Real.dist_eq, hsum]
  have hdecomp : (tail + S) / T - (1 - 2 * α * Real.log 2 / π)
      = tail / T + (S - Tel) / T + (Tel / T - L) + (L - (1 - 2 * α * Real.log 2 / π)) := by
    field_simp
    ring
  rw [hdecomp]
  -- The four pieces.
  have b1 : |tail / T| < ε / 4 := by
    have hb : |tail| ≤ chebyshevPsi n :=
      abs_sum_Ioc_vonMangoldt_mul_le n _ fun m => abs_sign_sin_le_one _
    have hpsi : chebyshevPsi n = chebyshevPsiReal (blockScale α K * T) := by
      rw [chebyshevPsiReal, hndef, blockEndpoint_eq_floor_scale hα hTpos K]
    have hle : chebyshevPsiReal (blockScale α K * T) ≤ C * (blockScale α K * T) := hCle _ hTscale
    have hbs : blockScale α K = α / ((K : ℝ) * π) := blockScale_of_le_pi hα hαπ hK1
    have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
    have hfin : C * (α / ((K : ℝ) * π) * T) = C * α / (π * (K : ℝ)) * T := by
      field_simp
    rw [abs_div, abs_of_pos hTpos, div_lt_iff₀ hTpos]
    calc |tail| ≤ C * (blockScale α K * T) := by rw [hpsi] at hb; linarith
      _ = C * α / (π * (K : ℝ)) * T := by rw [hbs]; exact hfin
      _ < ε / 4 * T := by
          exact mul_lt_mul_of_pos_right hKa hTpos
  have b2 : |(S - Tel) / T| < ε / 4 := by
    have hblk := abs_sum_blocks_vonMangoldt_sign_sub_le hα hTge1 K
    have hfl : (1 : ℕ) ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hTge1)
    have hflR : (1 : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast hfl
    have hlogle : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log T :=
      Real.log_le_log (by linarith) (Nat.floor_le hTpos.le)
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := by linarith
    rw [abs_div, abs_of_pos hTpos, div_lt_iff₀ hTpos]
    calc |S - Tel| ≤ (K : ℝ) * Real.log (⌊T⌋₊ : ℝ) := hblk
      _ ≤ (K : ℝ) * Real.log T := by nlinarith
      _ < ε / 4 * T := by
          have := hTlog
          rw [div_lt_iff₀ hTpos] at this
          linarith
  have b3 : |Tel / T - L| < ε / 4 := hTtel
  have b4 : |L - (1 - 2 * α * Real.log 2 / π)| < ε / 4 := hKb
  have h2 := abs_add_le (tail / T) ((S - Tel) / T)
  have h3 := abs_add_le (tail / T + (S - Tel) / T) (Tel / T - L)
  have h4 := abs_add_le (tail / T + (S - Tel) / T + (Tel / T - L))
    (L - (1 - 2 * α * Real.log 2 / π))
  linarith

/-- **The square-wave limit in integral form.**  For `1 ≤ α ≤ π` the dilated von Mangoldt sum
converges to `α ∫_α^∞ sgn (sin x)/x² dx`. -/
theorem tendsto_dilated_vonMangoldt_sign_sum_integral {α : ℝ} (hα1 : 1 ≤ α) (hαπ : α ≤ π) :
    Tendsto (fun T : ℝ => (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
        (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))) / T) atTop
      (𝓝 (α * ∫ x in Set.Ici α, Real.sign (Real.sin x) * (x ^ 2)⁻¹)) := by
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le zero_lt_one hα1
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hval : α * (∫ x in Set.Ici α, Real.sign (Real.sin x) * (x ^ 2)⁻¹)
      = 1 - 2 * α * Real.log 2 / π := by
    rw [GaloisForLFunctions.HTGeometry.integral_sign_sin_mul_inv_sq_Ici hα1 hαπ]
    field_simp
  rw [hval]
  exact tendsto_dilated_vonMangoldt_sign_sum hα0 hαπ

/-- The dilation `α = 1`. -/
theorem tendsto_dilated_vonMangoldt_sign_sum_one :
    Tendsto (fun T : ℝ => (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
        (vonMangoldt m : ℝ) * Real.sign (Real.sin (T / m))) / T) atTop
      (𝓝 (1 - 2 * Real.log 2 / π)) := by
  have h := tendsto_dilated_vonMangoldt_sign_sum (α := 1) zero_lt_one
    (by linarith [Real.two_le_pi])
  simpa using h

/-- The dilation `α = 2`, legitimate because `2 < π`. -/
theorem tendsto_dilated_vonMangoldt_sign_sum_two :
    Tendsto (fun T : ℝ => (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
        (vonMangoldt m : ℝ) * Real.sign (Real.sin (2 * T / m))) / T) atTop
      (𝓝 (1 - 4 * Real.log 2 / π)) := by
  have h := tendsto_dilated_vonMangoldt_sign_sum (α := 2) (by norm_num) Real.two_le_pi
  have hval : (1 : ℝ) - 2 * 2 * Real.log 2 / π = 1 - 4 * Real.log 2 / π := by ring
  rwa [hval] at h

/-- **The parity-corrected cancellation.**  The two dilations of the von Mangoldt square wave
differ, in the limit, by exactly the square-wave defect `(2/π) log 2`. -/
theorem tendsto_dilated_vonMangoldt_sign_sum_difference :
    Tendsto (fun T : ℝ => (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
          (vonMangoldt m : ℝ) * Real.sign (Real.sin (T / m))) / T
        - (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
          (vonMangoldt m : ℝ) * Real.sign (Real.sin (2 * T / m))) / T) atTop
      (𝓝 (2 / π * Real.log 2)) := by
  have h := tendsto_dilated_vonMangoldt_sign_sum_one.sub tendsto_dilated_vonMangoldt_sign_sum_two
  have hval : (1 - 2 * Real.log 2 / π) - (1 - 4 * Real.log 2 / π) = 2 / π * Real.log 2 := by ring
  rwa [hval] at h

/-! ### Restriction to odd moduli -/

/-- The even part of a von Mangoldt sum is carried by the powers of two, hence is `O(log N)`. -/
theorem sum_Ioc_not_odd_vonMangoldt_le_log {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ (Finset.Ioc 0 N).filter (fun m => ¬Odd m), (vonMangoldt m : ℝ) ≤ Real.log N := by
  classical
  set E := (Finset.Ioc 0 N).filter (fun m => ¬Odd m) with hEdef
  set E' := E.filter (fun m => (vonMangoldt m : ℝ) ≠ 0) with hE'def
  have hpow : ∀ m ∈ E', ∃ k : ℕ, 1 ≤ k ∧ m = 2 ^ k := by
    intro m hm
    rw [hE'def, hEdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨⟨hm0, hmN⟩, hodd⟩, hΛ⟩ := hm
    obtain ⟨p, k, hp, hk, hpk⟩ := vonMangoldt_ne_zero_iff.mp hΛ
    have hpn : Nat.Prime p := Nat.prime_iff.mpr hp
    have h2m : 2 ∣ m := (Nat.not_odd_iff_even.mp hodd).two_dvd
    have h2p : 2 ∣ p := by
      rw [← hpk] at h2m
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2m
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpn).mp h2p).symm
    exact ⟨k, hk, by rw [← hpk, hp2]⟩
  have hcard : E'.card ≤ Nat.log 2 N := by
    have hIcc : (Finset.Icc 1 (Nat.log 2 N)).card = Nat.log 2 N := by
      rw [Nat.card_Icc]
      omega
    rw [← hIcc]
    refine Finset.card_le_card_of_injOn (fun m => Nat.log 2 m) ?_ ?_
    · intro m hm
      rw [Finset.mem_coe] at hm
      obtain ⟨k, hk1, hk2⟩ := hpow m hm
      have hmN : m ≤ N := by
        rw [hE'def, hEdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hm
        exact hm.1.1.2
      simp only [Finset.mem_coe, Finset.mem_Icc]
      rw [hk2, Nat.log_pow one_lt_two]
      refine ⟨hk1, (Nat.le_log_iff_pow_le one_lt_two (by omega)).mpr ?_⟩
      rw [← hk2]
      exact hmN
    · intro m₁ h₁ m₂ h₂ heq
      rw [Finset.mem_coe] at h₁ h₂
      obtain ⟨k₁, _, e₁⟩ := hpow m₁ h₁
      obtain ⟨k₂, _, e₂⟩ := hpow m₂ h₂
      simp only at heq
      rw [e₁, e₂, Nat.log_pow one_lt_two, Nat.log_pow one_lt_two] at heq
      rw [e₁, e₂, heq]
  have hterm : ∀ m ∈ E', (vonMangoldt m : ℝ) ≤ Real.log 2 := by
    intro m hm
    obtain ⟨k, hk1, hk2⟩ := hpow m hm
    rw [hk2, vonMangoldt_apply_pow (by omega : k ≠ 0), vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  calc ∑ m ∈ E, (vonMangoldt m : ℝ) = ∑ m ∈ E', (vonMangoldt m : ℝ) :=
        (Finset.sum_filter_ne_zero E).symm
    _ ≤ ∑ _m ∈ E', Real.log 2 := Finset.sum_le_sum hterm
    _ = (E'.card : ℝ) * Real.log 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.log 2 N : ℝ) * Real.log 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by norm_num))
        exact_mod_cast hcard
    _ = Real.log ((2 : ℝ) ^ (Nat.log 2 N)) := by rw [Real.log_pow]
    _ ≤ Real.log N := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)

/-- **The square-wave limit over odd moduli.**  Dropping the even moduli changes the sum only at
the powers of two, hence not the limit. -/
theorem tendsto_dilated_vonMangoldt_sign_sum_odd {α : ℝ} (hα : 0 < α) (hαπ : α ≤ π) :
    Tendsto (fun T : ℝ => (∑ m ∈ (Finset.Ioc 0 ⌊T⌋₊).filter (fun m => Odd m),
        (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))) / T) atTop
      (𝓝 (1 - 2 * α * Real.log 2 / π)) := by
  have hfull := tendsto_dilated_vonMangoldt_sign_sum hα hαπ
  have hdiff : Tendsto (fun T : ℝ =>
      (∑ m ∈ (Finset.Ioc 0 ⌊T⌋₊).filter (fun m => Odd m),
          (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))) / T
        - (∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
          (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))) / T) atTop (𝓝 0) := by
    have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hTpos : (0 : ℝ) < T := by linarith
    have hfl : (1 : ℕ) ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT)
    have hflR : (1 : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast hfl
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊T⌋₊) (fun m => Odd m)
      (fun m => (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
    have heven : |∑ m ∈ (Finset.Ioc 0 ⌊T⌋₊).filter (fun m => ¬Odd m),
        (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m))| ≤ Real.log (⌊T⌋₊ : ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun m _ => ?_)) (sum_Ioc_not_odd_vonMangoldt_le_log hfl)
      rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      nlinarith [abs_sign_sin_le_one (α * T / m), vonMangoldt_nonneg (n := m),
        abs_nonneg (Real.sign (Real.sin (α * T / m)))]
    have hlogle : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log T :=
      Real.log_le_log (by linarith) (Nat.floor_le hTpos.le)
    rw [Real.norm_eq_abs, div_sub_div_same, ← hsplit]
    rw [show ∀ a b : ℝ, a - (a + b) = -b from fun a b => by ring, abs_div, abs_neg,
      abs_of_pos hTpos, div_le_div_iff_of_pos_right hTpos]
    linarith
  have hres := hfull.add hdiff
  rw [add_zero] at hres
  refine hres.congr fun T => ?_
  ring

end RHTower
