import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerConvolutionsPreserveTheReceiver

/-!
# The first pronic moment is the von Mangoldt pairing

The receiver prefix is a superposition of sawtooth modes, `A_c(n) = Σ_d c(d) ψ_d(n)`,
`ψ_d(n) = ⌊n/d⌋ − n/d`. Summation by parts along the counting step `n ↦ n + 1`, where
`ψ_d(n) − ψ_d(n−1) = 1_{d|n} − 1/d`, gives the exact partial sums
`Σ_{n≤N} ψ_d(n)/(n(n+1)) = (H_{⌊N/d⌋} − H_N)/d − ψ_d(N)/(N+1)`,
and the harmonic numbers along the dilation `k ↦ dk` leave the logarithm:
`Σ_n ψ_d(n)/(n(n+1)) = −log d / d`.
Hence, for every weight of the damped class,
`Σ_n A_c(n)/(n(n+1)) = −Σ_d c(d) log d / d = −Σ_e Λ(e) W_c(e)`:
**the first pronic moment of the receiver is the von Mangoldt pairing of the Ramanujan
coefficients**, a signed first-order observable supported on the prime powers.

It separates every real-character parity pair: with `L = L(1+ε, χ)`,
`M(c_χ) − M(c_+) = Σ_e Λ(e) e^{-1-ε} (|L| χ(e)² − L χ(e)) > 0`, the mass of the prime powers on which
the twist acts (`χ(e) = −sgn L`), counted with the weight `2|L| Λ(e) e^{-1-ε}`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The sawtooth mode `ψ_d(n) = ⌊n/d⌋ − n/d`. -/
def sawtooth (d n : ℕ) : ℝ := ((n / d : ℕ) : ℝ) - (n : ℝ) / d

theorem sawtooth_nonpos (d n : ℕ) : sawtooth d n ≤ 0 := by
  unfold sawtooth; linarith [Nat.cast_div_le (α := ℝ) (m := n) (n := d)]

theorem sawtooth_zero_left (n : ℕ) : sawtooth 0 n = 0 := by simp [sawtooth]

theorem sawtooth_zero_right (d : ℕ) : sawtooth d 0 = 0 := by simp [sawtooth]

/-- **Summation by parts.** `Σ_{n≤N} ψ_d(n)/(n(n+1)) = (H_{⌊N/d⌋} − H_N)/d − ψ_d(N)/(N+1)`. -/
theorem sum_range_sawtooth_div_pronic {d : ℕ} (hd : 1 ≤ d) (N : ℕ) :
    ∑ n ∈ range (N + 1), sawtooth d n / ((n : ℝ) * ((n : ℝ) + 1)) =
      (((harmonic (N / d) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ)) / d - sawtooth d N / ((N : ℝ) + 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  induction N with
  | zero => simp [sawtooth_zero_right]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ, Nat.succ_div]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by positivity
    split_ifs with hdvd
    · -- `d ∣ N + 1`: the floor jumps by one
      have hstep : sawtooth d (N + 1) = sawtooth d N + 1 - 1 / d := by
        simp only [sawtooth, Nat.succ_div, if_pos hdvd]; push_cast; ring
      have hq : (((N + 1) / d : ℕ) : ℝ) = ((N : ℝ) + 1) / d := by
        rw [Nat.cast_div hdvd hd0.ne']; push_cast; ring
      have hq' : ((N / d + 1 : ℕ) : ℝ) = ((N : ℝ) + 1) / d := by
        rw [← hq, Nat.succ_div, if_pos hdvd]
      rw [harmonic_succ (N / d)]
      push_cast
      rw [hstep]
      have hq'' : ((N / d : ℕ) : ℝ) + 1 = ((N : ℝ) + 1) / d := by exact_mod_cast hq'
      rw [hq'']
      field_simp
      ring
    · have hstep : sawtooth d (N + 1) = sawtooth d N - 1 / d := by
        simp only [sawtooth, Nat.succ_div, if_neg hdvd, add_zero]; push_cast; ring
      rw [add_zero, hstep]
      push_cast
      field_simp
      ring

/-- `H_{⌊N/d⌋} − H_N → −log d`. -/
theorem tendsto_harmonic_div_sub_harmonic {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun N : ℕ => ((harmonic (N / d) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ)) atTop
      (𝓝 (-Real.log d)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ := Real.tendsto_harmonic_sub_log
  have hdiv : Tendsto (fun N : ℕ => N / d) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  have hγd := hγ.comp hdiv
  -- the ratio `N / ⌊N/d⌋ → d`
  have hratio : Tendsto (fun N : ℕ => (N : ℝ) / ((N / d : ℕ) : ℝ)) atTop (𝓝 d) := by
    have hlow : ∀ᶠ N : ℕ in atTop, (d : ℝ) ≤ (N : ℝ) / ((N / d : ℕ) : ℝ) := by
      filter_upwards [eventually_ge_atTop d] with N hN
      have hpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
        have : 0 < N / d := Nat.div_pos hN (by omega)
        exact_mod_cast this
      rw [le_div_iff₀ hpos]
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := d)
      rw [le_div_iff₀ hd0] at this
      linarith
    have hup : ∀ᶠ N : ℕ in atTop, (N : ℝ) / ((N / d : ℕ) : ℝ) ≤ d + d ^ 2 / ((N : ℝ) - d) := by
      filter_upwards [eventually_gt_atTop (2 * d)] with N hN
      have hNd : (2 * (d : ℝ)) < N := by exact_mod_cast hN
      have hpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
        have : 0 < N / d := Nat.div_pos (by omega) (by omega)
        exact_mod_cast this
      have hfl : (N : ℝ) - d < d * ((N / d : ℕ) : ℝ) := by
        have h := Nat.lt_mul_div_succ N (show 0 < d by omega)
        have h' : (N : ℝ) < d * (((N / d : ℕ) : ℝ) + 1) := by exact_mod_cast h
        linarith
      have hNd' : (0 : ℝ) < (N : ℝ) - d := by linarith
      rw [div_le_iff₀ hpos]
      have : (d : ℝ) + d ^ 2 / ((N : ℝ) - d) = d * N / ((N : ℝ) - d) := by
        field_simp; ring
      rw [this, div_mul_eq_mul_div, le_div_iff₀ hNd']
      nlinarith
    have hlim : Tendsto (fun N : ℕ => (d : ℝ) + d ^ 2 / ((N : ℝ) - d)) atTop (𝓝 d) := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) - d) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h2 := (h1.inv_tendsto_atTop).const_mul ((d : ℝ) ^ 2)
      simpa [div_eq_mul_inv] using h2.const_add (d : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlow hup
  have hlog : Tendsto (fun N : ℕ => Real.log N - Real.log ((N / d : ℕ) : ℝ)) atTop
      (𝓝 (Real.log d)) := by
    have h := (Real.continuousAt_log hd0.ne').tendsto.comp hratio
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop d] with N hN
    have hpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
      have : 0 < N / d := Nat.div_pos hN (by omega)
      exact_mod_cast this
    have hN0 : (0 : ℝ) < N := by
      have : 0 < N := lt_of_lt_of_le (by omega) hN
      exact_mod_cast this
    simp only [Function.comp_apply]
    rw [Real.log_div hN0.ne' hpos.ne']
  have := (hγd.sub hγ).sub hlog
  simp only [sub_self, zero_sub] at this
  refine this.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp_apply]
  ring

/-- **The sawtooth series.** `Σ_n ψ_d(n)/(n(n+1)) = −log d / d`. -/
theorem hasSum_sawtooth_div_pronic {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun n : ℕ => sawtooth d n / ((n : ℝ) * ((n : ℝ) + 1))) (-Real.log d / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hnn : ∀ n : ℕ, 0 ≤ -(sawtooth d n / ((n : ℝ) * ((n : ℝ) + 1))) := fun n => by
    rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg (sawtooth_nonpos d n) (by positivity)
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), sawtooth d n / ((n : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 (-Real.log d / d)) := by
    simp_rw [sum_range_sawtooth_div_pronic hd]
    have h1 := (tendsto_harmonic_div_sub_harmonic hd).div_const (d : ℝ)
    have h2 : Tendsto (fun N : ℕ => sawtooth d N / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have hb : ∀ N : ℕ, |sawtooth d N / ((N : ℝ) + 1)| ≤ 1 / ((N : ℝ) + 1) := fun N => by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
        exact div_le_div_of_nonneg_right (abs_natDiv_sub_div_le N d hd) (by positivity)
      exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N)
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.sub h2
  have hneg : HasSum (fun n : ℕ => -(sawtooth d n / ((n : ℝ) * ((n : ℝ) + 1)))) (Real.log d / d) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    have h := hlim.neg
    simp only [← Finset.sum_neg_distrib] at h
    rwa [neg_div, neg_neg] at h
  rw [neg_div]
  simpa using hneg.neg

/-! ### The first-moment law -/

/-- **Sawtooth superposition.** `A_c(n) = Σ_d c(d) ψ_d(n)` for an admissible weight. -/
theorem weightCenteredPrefix_eq_tsum_sawtooth (c : ℕ → ℝ) (hs : Summable (fun d : ℕ => c d / d))
    (n : ℕ) : weightCenteredPrefix c (∑' d : ℕ, c d / d) n = ∑' d : ℕ, c d * sawtooth d n := by
  have hshift : ∀ k : ℕ, c (k + (n + 1)) * sawtooth (k + (n + 1)) n =
      -(n : ℝ) * (c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ)) := by
    intro k
    rw [sawtooth, Nat.div_eq_of_lt (by omega), Nat.cast_zero, zero_sub]; ring
  have htail : Summable (fun k : ℕ => c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ)) :=
    (summable_nat_add_iff (f := fun d : ℕ => c d / d) (n + 1)).mpr hs
  have hsum : Summable (fun d : ℕ => c d * sawtooth d n) := by
    refine (summable_nat_add_iff (f := fun d : ℕ => c d * sawtooth d n) (n + 1)).mp ?_
    exact (htail.mul_left (-(n : ℝ))).congr fun k => (hshift k).symm
  rw [← hsum.sum_add_tsum_nat_add (n + 1), tsum_congr hshift, tsum_mul_left,
    weightCenteredPrefix_eq_split c hs n]
  have hr : range (n + 1) = insert 0 (Icc 1 n) := by
    ext d; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hr, sum_insert (by simp), sawtooth_zero_left, mul_zero, zero_add]
  simp only [sawtooth]
  ring

/-- **The first-moment law.** For an admissible weight with `Σ |c(d)| log d / d < ∞`,
`Σ_n A_c(n)/(n(n+1)) = −Σ_d c(d) log d / d`. -/
theorem hasSum_weightCenteredPrefix_div_pronic {c : ℕ → ℝ} (hs : Summable (fun d : ℕ => c d / d))
    (hlog : Summable (fun d : ℕ => |c d| * Real.log d / d)) :
    HasSum (fun n : ℕ => weightCenteredPrefix c (∑' d : ℕ, c d / d) n / ((n : ℝ) * ((n : ℝ) + 1)))
      (-∑' d : ℕ, c d * Real.log d / d) := by
  set F : ℕ × ℕ → ℝ := fun p => c p.1 * sawtooth p.1 p.2 / ((p.2 : ℝ) * ((p.2 : ℝ) + 1))
  have hrow : ∀ d : ℕ, HasSum (fun n => F (d, n)) (-(c d * Real.log d / d)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [F, sawtooth_zero_left]
    · have h := (hasSum_sawtooth_div_pronic hd).mul_left (c d)
      rw [show -(c d * Real.log d / d) = c d * (-Real.log d / d) by ring]
      exact h.congr_fun fun n => by simp only [F]; ring
  have hrowabs : ∀ d : ℕ, HasSum (fun n => ‖F (d, n)‖) (|c d| * Real.log d / d) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [F, sawtooth_zero_left]
    · have h := ((hasSum_sawtooth_div_pronic hd).neg).mul_left |c d|
      rw [show |c d| * Real.log d / d = |c d| * -(-Real.log d / d) by ring]
      refine h.congr_fun fun n => ?_
      simp only [F, Real.norm_eq_abs]
      rw [abs_div, abs_mul, abs_of_nonpos (sawtooth_nonpos d n),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))]
      ring
  have hF : Summable F := by
    refine Summable.of_norm ((summable_prod_of_nonneg fun p => norm_nonneg (F p)).mpr
      ⟨fun d => (hrowabs d).summable, ?_⟩)
    exact hlog.congr fun d => ((hrowabs d).tsum_eq).symm
  have htot : ∑' p, F p = -∑' d : ℕ, c d * Real.log d / d := by
    rw [← tsum_neg]
    exact (hF.hasSum.prod_fiberwise hrow).tsum_eq.symm
  -- columns
  set G : ℕ × ℕ → ℝ := fun p => F (p.2, p.1)
  have hG : Summable G := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hF
  have hGtot : ∑' p, G p = ∑' p, F p := (Equiv.prodComm ℕ ℕ).tsum_eq F
  have hcol : ∀ n : ℕ, HasSum (fun d => G (n, d))
      (weightCenteredPrefix c (∑' d : ℕ, c d / d) n / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n
    rw [weightCenteredPrefix_eq_tsum_sawtooth c hs n, ← tsum_div_const]
    exact (hG.prod_factor n).hasSum
  rw [← htot, ← hGtot]
  exact hG.hasSum.prod_fiberwise hcol

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- **The von Mangoldt pairing.** `Σ_d c(d) log d / d = Σ_e Λ(e) W_c(e)`. -/
theorem tsum_log_eq_tsum_vonMangoldt {c : ℕ → ℝ} (hs : Summable (fun d : ℕ => c d / d))
    (hlog : Summable (fun d : ℕ => |c d| * Real.log d / d)) :
    ∑' d : ℕ, c d * Real.log d / d =
      ∑' e : ℕ, Λ e * weightRamanujanCoeff c e := by
  set H : ℕ × ℕ → ℝ := fun p => Λ p.1 * (c (p.1 * p.2) / ((p.1 * p.2 : ℕ) : ℝ))
  have hfiber : ∀ d : ℕ, d ≠ 0 → ∀ (f : ℝ → ℝ),
      ∑ p ∈ d.divisorsAntidiagonal, Λ p.1 * f (c (p.1 * p.2) / ((p.1 * p.2 : ℕ) : ℝ)) =
        Real.log d * f (c d / d) := by
    intro d hd f
    rw [Nat.sum_divisorsAntidiagonal (fun a b => Λ a * f (c (a * b) / ((a * b : ℕ) : ℝ))),
      ← ArithmeticFunction.vonMangoldt_sum, sum_mul]
    exact sum_congr rfl fun e he => by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)]
  have hH0 : ∀ p : ℕ × ℕ, p.1 * p.2 = 0 → H p = 0 := fun p hp => by
    simp only [H, hp, Nat.cast_zero, div_zero, mul_zero]
  -- absolute summability, fibre by fibre
  have hHabs : Summable (fun p => |H p|) := by
    refine summable_of_sum_le (c := ∑' d : ℕ, |c d| * Real.log d / d) (fun p => abs_nonneg _)
      fun u => ?_
    have hmaps : ∀ p ∈ u, p.1 * p.2 ∈ u.image (fun p : ℕ × ℕ => p.1 * p.2) :=
      fun p hp => mem_image_of_mem _ hp
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine (sum_le_sum fun d _ => ?_).trans (hlog.sum_le_tsum _ fun d _ => by
      have := Real.log_natCast_nonneg d; positivity)
    rcases eq_or_ne d 0 with rfl | hd
    · rw [sum_eq_zero fun p hp => by rw [hH0 p (mem_filter.mp hp).2, abs_zero]]
      simp
    · calc ∑ p ∈ u with p.1 * p.2 = d, |H p| ≤ ∑ p ∈ d.divisorsAntidiagonal, |H p| :=
            sum_le_sum_of_subset_of_nonneg (fun p hp => by
              rw [mem_filter] at hp; exact Nat.mem_divisorsAntidiagonal.mpr ⟨hp.2, hd⟩)
              fun _ _ _ => abs_nonneg _
        _ = Real.log d * |c d / d| := by
            have := hfiber d hd (fun x => |x|)
            rw [← this]
            exact sum_congr rfl fun p _ => by
              simp only [H]; rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        _ = |c d| * Real.log d / d := by
            rw [abs_div, Nat.abs_cast]; ring
  have hH : Summable H := hHabs.of_abs
  -- regroup by the product
  have hprod : ∑' p, H p = ∑' d : ℕ, c d * Real.log d / d := by
    refine (hH.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)).tsum_eq.symm.trans ?_
    refine tsum_congr fun d => ?_
    rcases eq_or_ne d 0 with rfl | hd
    · have h0 : ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}), H p = 0 := by
        rw [tsum_congr (fun p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}) => hH0 p.1 p.2),
          tsum_zero]
      rw [h0]; simp
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {d} = d.divisorsAntidiagonal by ext; simp [hd],
        Finset.tsum_subtype' d.divisorsAntidiagonal H]
      have := hfiber d hd id
      simp only [id] at this
      rw [this]; ring
  -- regroup by the modulus
  have hrow : ∀ e : ℕ, HasSum (fun k => H (e, k)) (Λ e * weightRamanujanCoeff c e) := by
    intro e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [H]
    · have hinj : Function.Injective (fun k : ℕ => e * k) := fun a b h =>
        Nat.eq_of_mul_eq_mul_left he h
      have hk := (hs.comp_injective hinj).hasSum.mul_left (Λ e)
      rw [weightRamanujanCoeff]
      exact hk
  rw [← hprod]
  exact (hH.hasSum.prod_fiberwise hrow).tsum_eq.symm

/-! ### The damped class -/

theorem summable_abs_mul_log_div_of_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) : Summable (fun d : ℕ => |c d| * Real.log d / d) := by
  have hK := nonneg_of_dampedClass hc
  refine ((Real.summable_nat_rpow.mpr (show -1 - ε / 2 < -1 by linarith)).mul_left
    (K * (2 / ε))).of_nonneg_of_le (fun d => by
      have := Real.log_natCast_nonneg d; positivity) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Real.zero_rpow (show -1 - ε / 2 ≠ 0 by linarith)]
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hlog := Real.log_le_rpow_div (x := d) hd0.le (by linarith : 0 < ε / 2)
    have hlog0 := Real.log_natCast_nonneg d
    rw [div_le_iff₀ hd0]
    calc |c d| * Real.log d ≤ K * (d : ℝ) ^ (-ε) * ((d : ℝ) ^ (ε / 2) / (ε / 2)) :=
          mul_le_mul (hc d) hlog hlog0 (by positivity)
      _ = K * (2 / ε) * (d : ℝ) ^ (-1 - ε / 2) * d := by
          rw [mul_assoc (K * (2 / ε)), ← Real.rpow_add_one hd0.ne',
            show -1 - ε / 2 + 1 = -ε + ε / 2 by ring, Real.rpow_add hd0]
          field_simp

/-- **The first pronic moment of the damped class.** For `|c(d)| ≤ K d^{-ε}`, `ε > 0`:
`Σ_n A_c(n)/(n(n+1)) = −Σ_e Λ(e) W_c(e)`. -/
theorem hasSum_firstPronicMoment {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    HasSum (fun n : ℕ => weightCenteredPrefix c (∑' d : ℕ, c d / d) n / ((n : ℝ) * ((n : ℝ) + 1)))
      (-∑' e : ℕ, Λ e * weightRamanujanCoeff c e) := by
  have hs := summable_div_of_dampedClass hε hc
  have hlog := summable_abs_mul_log_div_of_dampedClass hε hc
  rw [← tsum_log_eq_tsum_vonMangoldt hs hlog]
  exact hasSum_weightCenteredPrefix_div_pronic hs hlog

/-! ### The first moment separates the real-character pairs -/

variable {q : ℕ} [NeZero q]

theorem charSign_trichotomy (χ : MulChar (ZMod q) ℤ) (d : ℕ) :
    charSign χ d = 0 ∨ charSign χ d = 1 ∨ charSign χ d = -1 := by
  have h := charSign_sq_eq χ d
  split_ifs at h
  · right
    have : (charSign χ d - 1) * (charSign χ d + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  · left; exact pow_eq_zero_iff (two_ne_zero) |>.mp h

/-- A real character that is `−1` somewhere is `−1` at a prime. -/
theorem exists_prime_charSign_eq_neg_one_of (χ : MulChar (ZMod q) ℤ) :
    ∀ n : ℕ, 1 ≤ n → charSign χ n = -1 → ∃ p : ℕ, p.Prime ∧ charSign χ p = -1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hneg
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [charSign_one] at hneg; norm_num at hneg
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨m, rfl⟩ := hpn
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · omega
        · exact h
      rw [charSign_mul] at hneg
      rcases charSign_trichotomy χ p with h0 | h1 | hm1
      · rw [h0, zero_mul] at hneg; norm_num at hneg
      · rw [h1, one_mul] at hneg
        exact ih m (by
          have := hp.two_le
          nlinarith) hm hneg
      · exact ⟨p, hp, hm1⟩

/-- A non-principal real character is `−1` at some prime. -/
theorem exists_prime_charSign_eq_neg_one {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ charSign χ p = -1 := by
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hχ
  have hu : IsUnit (χ (a : ZMod q)) := (a.isUnit).map χ.toMonoidHom
  have hval : χ (a : ZMod q) = -1 := (Int.isUnit_iff.mp hu).resolve_left ha
  set n := (a : ZMod q).val
  have hn : charSign χ (q * 1 + n) = -1 := by
    rw [charSign_mul_period_add]
    simp only [charSign, n, ZMod.natCast_zmod_val, hval]; norm_num
  have hn1 : 1 ≤ q * 1 + n := by have := NeZero.pos q; omega
  exact exists_prime_charSign_eq_neg_one_of χ _ hn1 hn

/-- A real character is `1` at the square of every prime not dividing the modulus. -/
theorem exists_prime_charSign_sq_eq_one (χ : MulChar (ZMod q) ℤ) :
    ∃ p : ℕ, p.Prime ∧ charSign χ (p ^ 2) = 1 := by
  obtain ⟨p, hpq, hp⟩ := Nat.exists_infinite_primes (q + 1)
  have hq : 0 < q := NeZero.pos q
  have hcop : Nat.Coprime p q :=
    (Nat.coprime_or_dvd_of_prime hp q).resolve_right fun h => by
      have := Nat.le_of_dvd hq h; omega
  have hunit : IsUnit ((p : ℕ) : ZMod q) := by
    rw [← ZMod.coe_unitOfCoprime p hcop]; exact Units.isUnit _
  refine ⟨p, hp, ?_⟩
  rw [sq, charSign_mul, ← sq, charSign_sq_eq, if_pos hunit]

/-- **The first pronic moment separates every real-character parity pair.** With
`L = L(1+ε, χ)`: `M(c_χ) − M(c_+) = Σ_e Λ(e) e^{-1-ε} (|L| χ(e)² − L χ(e)) > 0`. -/
theorem firstPronicMoment_char_sub_twin {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ}
    (hε : 0 < ε) :
    (∑' n : ℕ, weightCenteredPrefix (dampedSignWeight (charSign χ) ε)
        (∑' d : ℕ, dampedSignWeight (charSign χ) ε d / d) n / ((n : ℝ) * ((n : ℝ) + 1))) -
      (∑' n : ℕ, weightCenteredPrefix (charTwinWeight χ ε)
        (∑' d : ℕ, charTwinWeight χ ε d / d) n / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑' e : ℕ, Λ e * ((e : ℝ) ^ (-ε) / e) *
        (|charDampedMass χ ε| * charSign χ e ^ 2 - charDampedMass χ ε * charSign χ e) ∧
    0 < ∑' e : ℕ, Λ e * ((e : ℝ) ^ (-ε) / e) *
        (|charDampedMass χ ε| * charSign χ e ^ 2 - charDampedMass χ ε * charSign χ e) := by
  set L := charDampedMass χ ε with hLdef
  have hL : L ≠ 0 := charDampedMass_ne_zero hε
  have hO := (charUnitMass_pos χ hε).ne'
  have hclassχ : DampedClass 1 ε (dampedSignWeight (charSign χ) ε) := fun d => by
    rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), one_mul]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (abs_charSign_le χ d)
  have hclassP := charTwinWeight_mem_dampedClass χ hε
  -- Ramanujan coefficients
  have hWχ : ∀ e, weightRamanujanCoeff (dampedSignWeight (charSign χ) ε) e =
      (e : ℝ) ^ (-ε) / e * (L * charSign χ e) := fun e => by
    rw [weightRamanujanCoeff_char, dampedSignWeight]; ring
  have hWp : ∀ e, weightRamanujanCoeff (charTwinWeight χ ε) e =
      (e : ℝ) ^ (-ε) / e * (|L| * charSign χ e ^ 2) := fun e => by
    rw [hLdef]
    unfold weightRamanujanCoeff charTwinWeight
    have hterm : ∀ k : ℕ, |charDampedMass χ ε| / charUnitMass χ ε *
        dampedSignWeight (charUnit χ) ε (e * k) / ((e * k : ℕ) : ℝ) =
        |charDampedMass χ ε| / charUnitMass χ ε * ((dampedSignWeight (charUnit χ) ε e / e) *
          (dampedSignWeight (charUnit χ) ε k / k)) := fun k => by
      rw [mul_div_assoc, dampedSignWeight_mul_div (charUnit_mul χ) e k]
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left, ← charUnitMass, dampedSignWeight, charUnit]
    field_simp
  -- the two first moments
  have hMχ := (hasSum_firstPronicMoment hε hclassχ).tsum_eq
  have hMp := (hasSum_firstPronicMoment hε hclassP).tsum_eq
  -- summability of the von Mangoldt pairings
  have hlog1 := summable_abs_mul_log_div_of_dampedClass hε
    (show DampedClass 1 ε (dampedSignWeight unitSign ε) from fun d => by
      rw [dampedSignWeight, unitSign, one_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)])
  have hbound : ∀ e : ℕ, ∀ a : ℝ, |a| ≤ 2 * |L| →
      |Λ e * ((e : ℝ) ^ (-ε) / e * a)| ≤ 2 * |L| *
        (|dampedSignWeight unitSign ε e| * Real.log e / e) := fun e a ha => by
    rw [dampedSignWeight, unitSign, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _),
      abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _) (Nat.cast_nonneg e))]
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := e)
    have hp : 0 ≤ (e : ℝ) ^ (-ε) / e := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _)
      (Nat.cast_nonneg e)
    calc Λ e * ((e : ℝ) ^ (-ε) / e * |a|) ≤ Real.log e * ((e : ℝ) ^ (-ε) / e * (2 * |L|)) :=
          mul_le_mul hΛ (mul_le_mul_of_nonneg_left ha hp) (by positivity)
            (Real.log_natCast_nonneg e)
      _ = 2 * |L| * ((e : ℝ) ^ (-ε) * Real.log e / e) := by ring
  have hsumχ : Summable (fun e : ℕ => Λ e * weightRamanujanCoeff (dampedSignWeight (charSign χ) ε) e) :=
    ((hlog1.mul_left (2 * |L|)).of_norm_bounded fun e => by
      rw [Real.norm_eq_abs, hWχ]
      exact hbound e _ (by
        rw [abs_mul]
        nlinarith [abs_charSign_le χ e, abs_nonneg L, abs_nonneg (charSign χ e)]))
  have hsump : Summable (fun e : ℕ => Λ e * weightRamanujanCoeff (charTwinWeight χ ε) e) :=
    ((hlog1.mul_left (2 * |L|)).of_norm_bounded fun e => by
      rw [Real.norm_eq_abs, hWp]
      exact hbound e _ (by
        rw [abs_mul, abs_abs, abs_of_nonneg (sq_nonneg (charSign χ e))]
        have h1 : charSign χ e ^ 2 ≤ 1 := by
          rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_charSign_le χ e)
        nlinarith [abs_nonneg L]))
  have hgap : ∀ e : ℕ, Λ e * weightRamanujanCoeff (charTwinWeight χ ε) e -
      Λ e * weightRamanujanCoeff (dampedSignWeight (charSign χ) ε) e =
      Λ e * ((e : ℝ) ^ (-ε) / e) * (|L| * charSign χ e ^ 2 - L * charSign χ e) := fun e => by
    rw [hWp, hWχ]; ring
  have hdiff : (∑' n : ℕ, weightCenteredPrefix (dampedSignWeight (charSign χ) ε)
        (∑' d : ℕ, dampedSignWeight (charSign χ) ε d / d) n / ((n : ℝ) * ((n : ℝ) + 1))) -
      (∑' n : ℕ, weightCenteredPrefix (charTwinWeight χ ε)
        (∑' d : ℕ, charTwinWeight χ ε d / d) n / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑' e : ℕ, Λ e * ((e : ℝ) ^ (-ε) / e) * (|L| * charSign χ e ^ 2 - L * charSign χ e) := by
    rw [hMχ, hMp, neg_sub_neg, ← hsump.tsum_sub hsumχ]
    exact tsum_congr hgap
  refine ⟨hdiff, ?_⟩
  -- every term is nonnegative, and one is positive
  have hterm_nn : ∀ e : ℕ, 0 ≤ Λ e * ((e : ℝ) ^ (-ε) / e) *
      (|L| * charSign χ e ^ 2 - L * charSign χ e) := fun e => by
    have hp : 0 ≤ (e : ℝ) ^ (-ε) / e := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _)
      (Nat.cast_nonneg e)
    refine mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp) ?_
    rcases charSign_trichotomy χ e with h | h | h <;> rw [h]
    · simp
    · nlinarith [le_abs_self L]
    · nlinarith [neg_abs_le L]
  have hsumgap : Summable (fun e : ℕ => Λ e * ((e : ℝ) ^ (-ε) / e) *
      (|L| * charSign χ e ^ 2 - L * charSign χ e)) :=
    (hsump.sub hsumχ).congr hgap
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · -- `L < 0`: the squares of primes coprime to `q`
    obtain ⟨p, hp, hp1⟩ := exists_prime_charSign_sq_eq_one χ
    refine hsumgap.tsum_pos hterm_nn (p ^ 2) ?_
    rw [hp1, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hpp : (0 : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by have := hp.pos; positivity
    have : 0 < (((p ^ 2 : ℕ) : ℝ)) ^ (-ε) / ((p ^ 2 : ℕ) : ℝ) := by positivity
    rw [abs_of_neg hneg]
    have h2 : 0 < -L * 1 ^ 2 - L * 1 := by nlinarith
    positivity
  · -- `L > 0`: the primes where `χ = −1`
    obtain ⟨p, hp, hpm⟩ := exists_prime_charSign_eq_neg_one hχ
    refine hsumgap.tsum_pos hterm_nn p ?_
    rw [hpm, ArithmeticFunction.vonMangoldt_apply_prime hp, abs_of_pos hpos]
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have : 0 < (p : ℝ) ^ (-ε) / p := by positivity
    have h2 : 0 < L * (-1) ^ 2 - L * (-1) := by nlinarith
    positivity

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
