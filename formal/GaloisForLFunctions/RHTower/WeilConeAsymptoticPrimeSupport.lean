import GaloisForLFunctions.RHTower.WeilConeMultiplesOfPrimeLaw

/-!
# Asymptotic prime support of the bounded nonnegative Weil cone

**Theorem** (`tendsto_nonprimeMass_div_log`). Let `lam ≥ 0` be full-cone Weil-positive, with
`lam(n) ≤ K (1 + Λ(n))` on the non-primes. Then
`Σ_{n≤N, n not prime} lam(n)/n = o(log N)`.

The harmonic mass of `lam` up to `N` is `log N + O(1)` by window pinning. So the theorem says that
such a weight system lives asymptotically on the primes: composite support of positive harmonic
density is impossible, with no condition on its sign pattern or arithmetic structure.

**Proof.** Fix `z`. A non-prime `n ≥ 2` either has a prime factor `p ≤ z`, and then `n ∈ pℕ`,
`n > p`, or all its prime factors exceed `z`.
* The first part is bounded by `Σ_{p≤z} Σ_{p∣n, n>p} lam(n)/n`, which is finite by the
  multiples-of-a-prime law for the nonnegative cone (`summable_multiples_of_weilPositiveFull_of_nonneg`).
* The second part is at most `K Σ_{n≤N, P⁻(n)>z} 1/n + K Σ_{n not prime} Λ(n)/n`. The rough
  harmonic sum is at most `(1 + 2 log N)/log(z + 1)` (`sum_rough_inv_le`): the products `n s` of a
  `z`-rough `n ≤ N` and an `s ≤ z` are distinct and at most `N z`, and `Σ_{s≤z} 1/s ≥ log(z + 1)`.

Hence the non-prime mass is at most `B_z + 2K log N/log(z + 1) + O(1)` for every `z`.
-/

noncomputable section

open Filter Topology RHTower

namespace RHTower.WeilAbscissa

/-- All prime factors of `n` exceed `z`. -/
def IsRoughAbove (z n : ℕ) : Prop := ∀ p ∈ n.primeFactors, z < p

instance (z : ℕ) : DecidablePred (IsRoughAbove z) := fun n => by
  unfold IsRoughAbove; infer_instance

/-- **Rough harmonic sums.** For `1 ≤ z ≤ N`, `Σ_{1≤n≤N, P⁻(n)>z} 1/n ≤ (1 + 2 log N)/log(z + 1)`. -/
theorem sum_rough_inv_le {z N : ℕ} (hz : 1 ≤ z) (hzN : z ≤ N) :
    ∑ n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n ∧ IsRoughAbove z n), (n : ℝ)⁻¹ ≤
      (1 + 2 * Real.log N) / Real.log (z + 1) := by
  classical
  set A := (Finset.range (N + 1)).filter (fun n => 1 ≤ n ∧ IsRoughAbove z n) with hA
  set B := Finset.Icc 1 z with hB
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log ((z : ℝ) + 1) := Real.log_pos (by linarith)
  have hS : Real.log ((z : ℝ) + 1) ≤ ∑ s ∈ B, (s : ℝ)⁻¹ := by
    have h := log_add_one_le_harmonic z
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    exact h.trans (le_of_eq (Finset.sum_congr rfl fun s _ => one_div _))
  have hA0 : 0 ≤ ∑ n ∈ A, (n : ℝ)⁻¹ := Finset.sum_nonneg fun n _ => by positivity
  -- injectivity of `(n, s) ↦ n s`
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (A ×ˢ B : Finset (ℕ × ℕ)) := by
    rintro ⟨n, s⟩ hx ⟨n', s'⟩ hy h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hA, hB, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_range] at hx hy h
    obtain ⟨⟨-, hn1, hnr⟩, hs1, hsz⟩ := hx
    obtain ⟨⟨-, hn1', hnr'⟩, hs1', hsz'⟩ := hy
    have hcop : ∀ {a b : ℕ}, 1 ≤ b → IsRoughAbove z b → 1 ≤ a → a ≤ z → a.Coprime b := by
      intro a b hb hbr ha haz
      refine Nat.coprime_of_dvd fun k hk hka hkb => ?_
      have hkle : k ≤ z := (Nat.le_of_dvd (by omega) hka).trans haz
      have hmem : k ∈ b.primeFactors := Nat.mem_primeFactors.mpr ⟨hk, hkb, by omega⟩
      have := hbr k hmem
      omega
    have h1 : s ∣ s' := (hcop hn1' hnr' hs1 hsz).dvd_of_dvd_mul_left (h ▸ dvd_mul_left s n)
    have h2 : s' ∣ s := (hcop hn1 hnr hs1' hsz').dvd_of_dvd_mul_left (h.symm ▸ dvd_mul_left s' n')
    have hss : s = s' := Nat.dvd_antisymm h1 h2
    subst hss
    have hnn : n = n' := Nat.eq_of_mul_eq_mul_right (by omega) h
    rw [hnn]
  have hprod : (∑ n ∈ A, (n : ℝ)⁻¹) * (∑ s ∈ B, (s : ℝ)⁻¹) ≤ 1 + 2 * Real.log N := by
    rw [Finset.sum_mul_sum]
    have e : ∑ n ∈ A, ∑ s ∈ B, (n : ℝ)⁻¹ * (s : ℝ)⁻¹ =
        ∑ m ∈ (A ×ˢ B).image (fun x : ℕ × ℕ => x.1 * x.2), (m : ℝ)⁻¹ := by
      rw [Finset.sum_image hinj, Finset.sum_product]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun s _ => ?_
      push_cast; rw [mul_inv]
    rw [e]
    have hsub : (A ×ˢ B).image (fun x : ℕ × ℕ => x.1 * x.2) ⊆ Finset.range (N * z + 1) := by
      intro m hm
      obtain ⟨⟨n, s⟩, hx, rfl⟩ := Finset.mem_image.mp hm
      simp only [Finset.mem_product, hA, hB, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_range] at hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.mul_le_mul (by omega) hx.2.2))
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity).trans ?_
    refine (PrimeSmallDeviation.sum_range_inv_le (N * z)).trans ?_
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hz.trans hzN
    have hzN' : (z : ℝ) ≤ N := by exact_mod_cast hzN
    push_cast
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_log (by linarith) hzN'
    linarith
  rw [le_div_iff₀ hlogz]
  calc (∑ n ∈ A, (n : ℝ)⁻¹) * Real.log ((z : ℝ) + 1)
      ≤ (∑ n ∈ A, (n : ℝ)⁻¹) * ∑ s ∈ B, (s : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hS hA0
    _ ≤ 1 + 2 * Real.log N := hprod

/-- **Asymptotic prime support of the bounded nonnegative Weil cone.** If `lam ≥ 0` is full-cone
Weil-positive and `lam(n) ≤ K (1 + Λ(n))` for every non-prime `n ≥ 2`, then the harmonic mass of
`lam` on the non-primes is `o(log N)`. -/
theorem tendsto_nonprimeMass_div_log {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n, 2 ≤ n → ¬ n.Prime → lam n ≤ K * (1 + ArithmeticFunction.vonMangoldt n)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
      (if 2 ≤ n ∧ ¬ n.Prime then lam n / n else 0)) / Real.log N) atTop (𝓝 0) := by
  classical
  set mass : ℕ → ℝ := fun N => ∑ n ∈ Finset.range (N + 1),
    (if 2 ≤ n ∧ ¬ n.Prime then lam n / n else 0) with hmass
  have hterm0 : ∀ n, 0 ≤ (if 2 ≤ n ∧ ¬ n.Prime then lam n / n else 0) := fun n => by
    split_ifs with h
    · exact div_nonneg (hnn n h.1) (Nat.cast_nonneg n)
    · exact le_rfl
  have hmass0 : ∀ N, 0 ≤ mass N := fun N => Finset.sum_nonneg fun n _ => hterm0 n
  -- the multiples series and the composite `Λ` series
  set f : ℕ → ℕ → ℝ := fun p n => if p ∣ n ∧ n ≠ p then lam n / n else 0 with hf
  have hnnp : ∀ p, p.Prime → ∀ n, p ∣ n → p < n → 0 ≤ lam n := fun p hp n _ hpn =>
    hnn n (by have := hp.two_le; omega)
  have hf0 : ∀ p, p.Prime → ∀ n, 0 ≤ f p n := fun p hp n =>
    multiples_term_nonneg (hnnp p hp) n
  have hfs : ∀ p, p.Prime → Summable (f p) := fun p hp =>
    summable_multiples_of_weilPositiveFull_of_nonneg hW hnn hp
  set gΛ : ℕ → ℝ := fun n => if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ) / n
    with hgΛ
  have hgΛs : Summable gΛ := RHTower.WeilPrimeDeficit.summable_nonprime_vonMangoldt_div
  have hgΛ0 : ∀ n, 0 ≤ gΛ n := fun n => by
    simp only [hgΛ]
    split_ifs
    · exact le_rfl
    · have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
  set TΛ : ℝ := ∑' n, gΛ n with hTΛ
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N => ?_, fun b hb => ?_⟩
  · exact lt_of_lt_of_le ha (div_nonneg (hmass0 N) (Real.log_natCast_nonneg N))
  -- choose `z` with `2K/log(z+1) ≤ b/3`
  set z : ℕ := ⌈Real.exp (6 * K / b)⌉₊ with hzdef
  have hz1 : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr (by
    rw [hzdef]; exact (Nat.ceil_pos.mpr (Real.exp_pos _)).ne')
  have hlogz : 6 * K / b ≤ Real.log ((z : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact (Nat.le_ceil _).trans (by linarith)
  have hlogz0 : 0 < Real.log ((z : ℝ) + 1) :=
    Real.log_pos (by have : (1 : ℝ) ≤ z := (by exact_mod_cast hz1); linarith)
  set Pz := (Finset.range (z + 1)).filter Nat.Prime with hPz
  set Bz : ℝ := ∑ p ∈ Pz, ∑' n, f p n with hBz
  have hBz0 : 0 ≤ Bz := Finset.sum_nonneg fun p hp =>
    tsum_nonneg (hf0 p (Finset.mem_filter.mp hp).2)
  set Cst : ℝ := Bz + K * TΛ + K / Real.log ((z : ℝ) + 1) with hCst
  have hTΛ0 : 0 ≤ TΛ := tsum_nonneg hgΛ0
  have hCst0 : 0 ≤ Cst := by
    have : 0 ≤ K / Real.log ((z : ℝ) + 1) := div_nonneg hK0 hlogz0.le
    have := mul_nonneg hK0 hTΛ0
    linarith
  -- the mass bound for `N ≥ z`
  have hbound : ∀ N : ℕ, z ≤ N →
      mass N ≤ Cst + 2 * K / Real.log ((z : ℝ) + 1) * Real.log N := by
    intro N hzN
    have hpt : ∀ n ∈ Finset.range (N + 1), (if 2 ≤ n ∧ ¬ n.Prime then lam n / n else 0) ≤
        ∑ p ∈ Pz, f p n + K * (if 1 ≤ n ∧ IsRoughAbove z n then (n : ℝ)⁻¹ else 0) + K * gΛ n := by
      intro n _
      have hsum0 : 0 ≤ ∑ p ∈ Pz, f p n :=
        Finset.sum_nonneg fun p hp => hf0 p (Finset.mem_filter.mp hp).2 n
      have hr0 : 0 ≤ K * (if 1 ≤ n ∧ IsRoughAbove z n then (n : ℝ)⁻¹ else 0) :=
        mul_nonneg hK0 (by split_ifs <;> positivity)
      have hg0 : 0 ≤ K * gΛ n := mul_nonneg hK0 (hgΛ0 n)
      by_cases h : 2 ≤ n ∧ ¬ n.Prime
      · rw [if_pos h]
        obtain ⟨h2, hnp⟩ := h
        by_cases hsmall : ∃ p ∈ Pz, p ∣ n
        · obtain ⟨p, hp, hpn⟩ := hsmall
          have hpr := (Finset.mem_filter.mp hp).2
          have hfp : f p n = lam n / n := by
            simp only [hf]
            rw [if_pos ⟨hpn, fun h => hnp (h ▸ hpr)⟩]
          have hle : f p n ≤ ∑ p ∈ Pz, f p n :=
            Finset.single_le_sum (f := fun p => f p n)
              (fun p hp => hf0 p (Finset.mem_filter.mp hp).2 n) hp
          rw [hfp] at hle
          linarith
        · push Not at hsmall
          have hrough : IsRoughAbove z n := fun k hk => by
            obtain ⟨hkp, hkn, -⟩ := Nat.mem_primeFactors.mp hk
            by_contra hkz
            exact hsmall k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hkp⟩) hkn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          rw [if_pos ⟨by omega, hrough⟩]
          have hgn : gΛ n = (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
            simp only [hgΛ]; rw [if_neg hnp]
          rw [hgn]
          have hl := hK n h2 hnp
          have : lam n / n ≤ K * (n : ℝ)⁻¹ + K * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            have hi : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0.le
            nlinarith
          linarith
      · rw [if_neg h]; linarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_comm] at hsum
    -- the three pieces
    have h1 : ∑ p ∈ Pz, ∑ n ∈ Finset.range (N + 1), f p n ≤ Bz :=
      Finset.sum_le_sum fun p hp =>
        (hfs p (Finset.mem_filter.mp hp).2).sum_le_tsum _
          fun n _ => hf0 p (Finset.mem_filter.mp hp).2 n
    have h2 : ∑ n ∈ Finset.range (N + 1), (if 1 ≤ n ∧ IsRoughAbove z n then (n : ℝ)⁻¹ else 0) ≤
        (1 + 2 * Real.log N) / Real.log ((z : ℝ) + 1) := by
      rw [← Finset.sum_filter]
      exact sum_rough_inv_le hz1 hzN
    have h3 : ∑ n ∈ Finset.range (N + 1), gΛ n ≤ TΛ := hgΛs.sum_le_tsum _ fun n _ => hgΛ0 n
    have h2' := mul_le_mul_of_nonneg_left h2 hK0
    have h3' := mul_le_mul_of_nonneg_left h3 hK0
    have e : K * ((1 + 2 * Real.log N) / Real.log ((z : ℝ) + 1)) =
        K / Real.log ((z : ℝ) + 1) + 2 * K / Real.log ((z : ℝ) + 1) * Real.log N := by
      field_simp
    show mass N ≤ _
    simp only [hmass]
    linarith
  -- the coefficient `2K/log(z+1) ≤ b/3`
  have hcoef : 2 * K / Real.log ((z : ℝ) + 1) ≤ b / 3 := by
    rw [div_le_iff₀ hlogz0]
    have := mul_le_mul_of_nonneg_left hlogz (by linarith : (0 : ℝ) ≤ b / 3)
    have e : b / 3 * (6 * K / b) = 2 * K := by field_simp; ring
    linarith
  -- large `N`
  have hev : ∀ᶠ N : ℕ in atTop, Cst / Real.log N < b / 2 ∧ z ≤ N ∧ 1 < N := by
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 := (hlog.eventually_gt_atTop (2 * Cst / b))
    filter_upwards [h1, eventually_ge_atTop z, eventually_gt_atTop 1] with N hN hzN hN1
    refine ⟨?_, hzN, hN1⟩
    have hlog0 : 0 < Real.log N := by
      have : 0 ≤ 2 * Cst / b := by positivity
      linarith
    rw [div_lt_iff₀ hlog0]
    have : 2 * Cst / b * (b / 2) = Cst := by field_simp
    nlinarith
  filter_upwards [hev] with N ⟨hC, hzN, hN1⟩
  have hlog0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN1)
  have hb := hbound N hzN
  show mass N / Real.log N < b
  rw [div_lt_iff₀ hlog0]
  rw [div_lt_iff₀ hlog0] at hC
  have := mul_le_mul_of_nonneg_right hcoef hlog0.le
  linarith

end RHTower.WeilAbscissa
