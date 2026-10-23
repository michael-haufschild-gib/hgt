import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HalfDampingIsTheExactThresholdOfTheParityPair
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip

/-!
# The half-damped receiver reads the Dirichlet series at the critical point

For a weight `c` of the half-damped class `|c(d)| ≤ K d^{-1/2}`, write `m = Σ c(d)/d`,
`A(n) = weightCenteredPrefix c m n` and `C(σ) = Σ c(d) d^{-σ}`. The Mellin pairing of the centred
prefix with the cells `Δ_n(σ) = n^{-σ} − (n+1)^{-σ}` is, for every real `1/2 < σ < 1`,

`Σ_n A(n) Δ_n(σ) = ζ(σ) (C(σ) − m)`  (`mellinPairing_eq_zeta_mul`).

* The prefix is a sum over moduli of the single-modulus defects `α_d(n) = ⌊n/d⌋ − n/d`
  (`weightCenteredPrefix_eq_tsum_modulusDefect`).
* One modulus pairs to `ζ(σ)(d^{-σ} − 1/d)` (`hasSum_modulusDefect_mul_mellinCell`): summation by
  parts turns the cells into `([d ∣ n] − 1/d) n^{-σ}`, and along `N = dM` the two growing terms
  `d^{-σ} M^{1-σ}` and `(dM)^{1-σ}/d` cancel exactly, leaving the partial-sum asymptotic of `ζ`
  inside the strip.
* Fubini is paid by `min(1, n/d) ≤ (n/d)^θ` with `1/2 < θ < σ`.
* On `(0, 1)`, `Re ζ(σ) ≤ −σ/(1 − σ)` (`riemannZeta_re_le_of_lt_one`), so `|ζ(σ)| ≥ 1` on `[1/2, 1)`.

Combined with the Cauchy–Schwarz bound of a paid receiver this gives the **general pole law**
(`abs_dirichletSeries_sub_mean_le_of_energy`): a paid half-damped weight has
`|C(σ) − m| ≤ 2√E (2σ − 1)^{-1/2}` for `1/2 < σ < 1`. The pole law of the critical Wiener
algebra (`not_receiverBounded_dirichletConv_of_drift_critical`) is the special case `c = k ⋆ q`;
here no factorisation is needed: the receiver at half damping reads the size of the weight's own
Dirichlet series as `σ ↓ 1/2`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The single-modulus defect -/

/-- The single-modulus defect `α_d(n) = ⌊n/d⌋ − n/d`. -/
def modulusDefect (d n : ℕ) : ℝ := ((n / d : ℕ) : ℝ) - (n : ℝ) / d

theorem modulusDefect_zero_right (d : ℕ) : modulusDefect d 0 = 0 := by simp [modulusDefect]

theorem modulusDefect_zero_left (n : ℕ) : modulusDefect 0 n = 0 := by simp [modulusDefect]

/-- The defect vanishes at the multiples of the modulus. -/
theorem modulusDefect_mul {d : ℕ} (hd : 0 < d) (M : ℕ) : modulusDefect d (d * M) = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [modulusDefect, Nat.mul_div_cancel_left M hd]
  push_cast
  field_simp
  ring

/-- One step of the defect: `α_d(n+1) = α_d(n) + [d ∣ n+1] − 1/d`. -/
theorem modulusDefect_succ {d : ℕ} (hd : 0 < d) (n : ℕ) :
    modulusDefect d (n + 1) = modulusDefect d n + (if d ∣ n + 1 then 1 else 0) - 1 / d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [modulusDefect, Nat.succ_div]
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- `|α_d(n)| ≤ (n/d)^θ` for `0 < θ ≤ 1`. -/
theorem abs_modulusDefect_le_rpow {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (d n : ℕ) :
    |modulusDefect d n| ≤ ((n : ℝ) / d) ^ θ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [modulusDefect_zero_left, Real.zero_rpow hθ.ne']
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [modulusDefect_zero_right, Real.zero_rpow hθ.ne']
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hnd : d ≤ n
  · have h1 : (1 : ℝ) ≤ (n : ℝ) / d := by
      rw [le_div_iff₀ hd0, one_mul]; exact_mod_cast hnd
    exact (abs_natDiv_sub_div_le n d hd).trans (Real.one_le_rpow h1 hθ.le)
  · have hlt : n < d := lt_of_not_ge hnd
    have hdiv : n / d = 0 := Nat.div_eq_of_lt hlt
    have hx1 : (n : ℝ) / d ≤ 1 := by
      rw [div_le_one hd0]; exact_mod_cast hlt.le
    have hx0 : (0 : ℝ) < (n : ℝ) / d := div_pos hn0 hd0
    rw [modulusDefect, hdiv, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hx0]
    calc (n : ℝ) / d = ((n : ℝ) / d) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((n : ℝ) / d) ^ θ := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hθ1

/-! ### The prefix as a sum over moduli -/

/-- **The centred prefix is a sum of single-modulus defects**: `A(n) = Σ_d c(d) α_d(n)`. -/
theorem weightCenteredPrefix_eq_tsum_modulusDefect (c : ℕ → ℝ)
    (hs : Summable (fun d : ℕ => c d / d)) (n : ℕ) :
    weightCenteredPrefix c (∑' d : ℕ, c d / d) n = ∑' d : ℕ, c d * modulusDefect d n := by
  have htail : ∀ k : ℕ, c (k + (n + 1)) * modulusDefect (k + (n + 1)) n =
      -(n : ℝ) * (c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ)) := by
    intro k
    have hdiv : n / (k + (n + 1)) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [modulusDefect, hdiv, Nat.cast_zero, zero_sub]
    ring
  have hsum : Summable (fun d : ℕ => c d * modulusDefect d n) := by
    rw [← summable_nat_add_iff (n + 1)]
    simp_rw [htail]
    exact ((summable_nat_add_iff (n + 1)).mpr hs).mul_left _
  rw [weightCenteredPrefix_eq_split c hs n, ← hsum.sum_add_tsum_nat_add (n + 1)]
  simp_rw [htail]
  rw [tsum_mul_left]
  have hr : range (n + 1) = insert 0 (Icc 1 n) := by
    ext d; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hr, sum_insert (by simp), modulusDefect_zero_left, mul_zero, zero_add]
  simp only [modulusDefect]
  ring

/-! ### One modulus against the Mellin cells -/

/-- Summation by parts along `n ↦ n + 1`. -/
theorem sum_range_modulusDefect_mul_mellinCell {d : ℕ} (hd : 0 < d) (σ : ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), modulusDefect d n * mellinCell σ n =
      ∑ n ∈ Icc 1 N, ((if d ∣ n then 1 else 0) - 1 / d) * (n : ℝ) ^ (-σ)
        - modulusDefect d N * ((N : ℝ) + 1) ^ (-σ) := by
  induction N with
  | zero => simp [modulusDefect_zero_right]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), modulusDefect_succ hd N,
      mellinCell]
    push_cast
    ring

/-- The divisible terms of `Icc 1 (dM)` are the dilates of `Icc 1 M`. -/
theorem sum_Icc_dvd_rpow {d : ℕ} (hd : 0 < d) (σ : ℝ) (M : ℕ) :
    ∑ n ∈ Icc 1 (d * M), (if d ∣ n then 1 else 0) * (n : ℝ) ^ (-σ) =
      (d : ℝ) ^ (-σ) * ∑ k ∈ Icc 1 M, (k : ℝ) ^ (-σ) := by
  have hfilt : (Icc 1 (d * M)).filter (fun n => d ∣ n) =
      (Icc 1 M).map ⟨(d * ·), mul_right_injective₀ hd.ne'⟩ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1
        · exact hk
      · exact Nat.le_of_mul_le_mul_left h2 hd
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd.ne' (by omega)),
        Nat.mul_le_mul_left d hk2⟩, dvd_mul_right d k⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← sum_filter, hfilt, sum_map, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  push_cast
  exact Real.mul_rpow hd0 (Nat.cast_nonneg k)

/-- The real remainder of the zeta partial sums inside the strip. -/
def zetaStripRemainder (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, (k : ℝ) ^ (-σ) - (N : ℝ) ^ (1 - σ) / (1 - σ)

/-- The real remainders converge to `ζ(σ)` for `0 < σ < 1`. -/
theorem tendsto_zetaStripRemainder {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun N : ℕ => ((zetaStripRemainder σ N : ℝ) : ℂ)) atTop (𝓝 (riemannZeta σ)) := by
  have hw0 : 0 < ((σ : ℂ)).re := by simpa using hσ0
  have hw1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  refine (RHTower.tendsto_sum_cpow_sub_pow hw0 hw1).congr fun N => ?_
  simp only [zetaStripRemainder]
  push_cast
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg k)]
    push_cast
    ring_nf
  · rw [Complex.ofReal_cpow (Nat.cast_nonneg N)]
    push_cast
    ring_nf

/-- **One modulus pairs to `ζ(σ)(d^{-σ} − 1/d)`.** -/
theorem hasSum_modulusDefect_mul_mellinCell {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {d : ℕ}
    (hd : 0 < d) :
    HasSum (fun n => ((modulusDefect d n * mellinCell σ n : ℝ) : ℂ))
      (riemannZeta σ * (((d : ℝ) ^ (-σ) - 1 / d : ℝ) : ℂ)) := by
  have hsR : Summable (fun n => modulusDefect d n * mellinCell σ n) :=
    summable_mul_mellinCell (a := 0) (C := 1) hσ0 hσ0 (modulusDefect_zero_right d) fun n _ => by
      rw [Real.rpow_zero, mul_one]
      exact abs_natDiv_sub_div_le n d hd
  have hs : Summable (fun n => ((modulusDefect d n * mellinCell σ n : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hsR
  -- the partial sums along `N = dM` in closed form
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ1' : (1 : ℝ) - σ ≠ 0 := by linarith
  have hpart : ∀ M : ℕ, ∑ n ∈ range (d * M + 1), modulusDefect d n * mellinCell σ n =
      (d : ℝ) ^ (-σ) * zetaStripRemainder σ M - zetaStripRemainder σ (d * M) / d := by
    intro M
    rw [sum_range_modulusDefect_mul_mellinCell hd σ, modulusDefect_mul hd, zero_mul, sub_zero]
    simp_rw [sub_mul]
    rw [sum_sub_distrib, sum_Icc_dvd_rpow hd σ M, ← mul_sum]
    simp only [zetaStripRemainder]
    have hcancel : (d : ℝ) ^ (-σ) * ((M : ℝ) ^ (1 - σ) / (1 - σ)) =
        ((d * M : ℕ) : ℝ) ^ (1 - σ) / (1 - σ) / d := by
      push_cast
      rw [Real.mul_rpow hdpos.le (Nat.cast_nonneg M),
        show (1 : ℝ) - σ = -σ + 1 by ring, Real.rpow_add_one hd0]
      field_simp
    rw [mul_sub, hcancel]
    ring
  have hlimit : Tendsto (fun M : ℕ => ((∑ n ∈ range (d * M + 1),
      modulusDefect d n * mellinCell σ n : ℝ) : ℂ)) atTop
      (𝓝 (riemannZeta σ * (((d : ℝ) ^ (-σ) - 1 / d : ℝ) : ℂ))) := by
    have hdM : Tendsto (fun M : ℕ => d * M) atTop atTop :=
      tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M hd) tendsto_id
    have h1 := (tendsto_zetaStripRemainder hσ0 hσ1).const_mul (((d : ℝ) ^ (-σ) : ℝ) : ℂ)
    have h2 := ((tendsto_zetaStripRemainder hσ0 hσ1).comp hdM).div_const ((d : ℝ) : ℂ)
    refine (h1.sub h2).congr' (Eventually.of_forall fun M => ?_) |>.trans_eq ?_
    · rw [hpart M]
      simp only [Function.comp]
      push_cast
      ring
    · push_cast
      ring_nf
  have hseq : Tendsto (fun M : ℕ => d * M + 1) atTop atTop :=
    tendsto_atTop_mono (fun M => (Nat.le_mul_of_pos_left M hd).trans (Nat.le_succ _)) tendsto_id
  have hfull := (hs.hasSum.tendsto_sum_nat).comp hseq
  have heq : ∑' n, ((modulusDefect d n * mellinCell σ n : ℝ) : ℂ) =
      riemannZeta σ * (((d : ℝ) ^ (-σ) - 1 / d : ℝ) : ℂ) := by
    refine tendsto_nhds_unique hfull ?_
    refine hlimit.congr fun M => ?_
    simp only [Function.comp]
    push_cast
    rfl
  rw [← heq]
  exact hs.hasSum

/-! ### The Mellin pairing of the prefix -/

theorem zero_of_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    c 0 = 0 := by
  have h := hc 0
  rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hε.ne'), mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- The Dirichlet series of a weight of `𝒞(K, ε)` converges absolutely on `σ > 1 − ε`. -/
theorem summable_mul_rpow_of_dampedClass {K ε σ : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (hσ : 1 - ε < σ) : Summable (fun d : ℕ => c d * (d : ℝ) ^ (-σ)) := by
  refine ((Real.summable_nat_rpow.mpr (show -ε - σ < -1 by linarith)).mul_left K)
    |>.of_norm_bounded fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [zero_of_dampedClass hε hc, Real.zero_rpow (show -ε - σ ≠ 0 by intro h; linarith)]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd0 _),
    show -ε - σ = -ε + -σ by ring, Real.rpow_add hd0, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hc d) (Real.rpow_pos_of_pos hd0 _).le

/-- The double family `c(d) α_d(n) Δ_n(σ)` of the Mellin pairing and its product majorant. -/
theorem norm_pairingFamily_le {c : ℕ → ℝ} {θ σ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hσ0 : 0 < σ)
    (n d : ℕ) :
    ‖c d * modulusDefect d n * mellinCell σ n‖ ≤
      (σ * (n : ℝ) ^ (θ - σ - 1)) * (|c d| * (d : ℝ) ^ (-θ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [modulusDefect_zero_right, mul_zero, zero_mul, norm_zero]; positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [modulusDefect_zero_left, mul_zero, zero_mul, norm_zero]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hΔ := mellinCell_nonneg hσ0 hn
  have hb := (mellinCell_bounds hσ0 hn).2
  have hα := abs_modulusDefect_le_rpow hθ0 hθ1 d n
  rw [Real.div_rpow hn0.le hd0.le] at hα
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΔ]
  calc |c d| * |modulusDefect d n| * mellinCell σ n
      ≤ |c d| * ((n : ℝ) ^ θ / (d : ℝ) ^ θ) * (σ * (n : ℝ) ^ (-σ - 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hα (abs_nonneg _)) hb hΔ (by positivity)
    _ = _ := by
        rw [show θ - σ - 1 = θ + (-σ - 1) by ring, Real.rpow_add hn0, Real.rpow_neg hd0.le θ]
        field_simp

/-- **The Mellin pairing identity, absolute-convergence form.** If `Σ_d |c(d)| d^{-θ} < ∞` for
some `0 < θ < σ < 1`, then the Mellin pairing of the centred prefix converges absolutely and
`Σ_n A(n) Δ_n(σ) = ζ(σ) (C(σ) − m)`. -/
theorem mellinPairing_eq_zeta_mul_of_summable {c : ℕ → ℝ} {θ σ : ℝ} (hθ0 : 0 < θ) (hθσ : θ < σ)
    (hσ1 : σ < 1) (hc : Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ))) :
    Summable (fun n => weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell σ n) ∧
      ((∑' n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell σ n : ℝ) : ℂ) =
        riemannZeta σ * (((∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d : ℝ) : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  -- the three absolutely convergent series of `c`
  have hcomp : ∀ τ : ℝ, θ ≤ τ → Summable (fun d : ℕ => c d * (d : ℝ) ^ (-τ)) := fun τ hτ =>
    hc.of_norm_bounded fun d => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [Real.zero_rpow (show -τ ≠ 0 by intro h; linarith), Real.zero_rpow (show -θ ≠ 0 by intro h; linarith)]
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd) (by linarith)
  have hs : Summable (fun d : ℕ => c d / d) := (hcomp 1 hθ1).congr fun d => by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hCsum := hcomp σ hθσ.le
  -- the double family
  set F : ℕ → ℕ → ℝ := fun n d => c d * modulusDefect d n * mellinCell σ n with hF
  set g : ℕ → ℝ := fun n => σ * (n : ℝ) ^ (θ - σ - 1)
  set h : ℕ → ℝ := fun d => |c d| * (d : ℝ) ^ (-θ)
  have hg : Summable g :=
    (Real.summable_nat_rpow.mpr (show θ - σ - 1 < -1 by linarith)).mul_left _
  have hg0 : 0 ≤ g := fun n => by positivity
  have hh0 : 0 ≤ h := fun d => by positivity
  have hbound : ∀ n d, ‖F n d‖ ≤ g n * h d := fun n d =>
    norm_pairingFamily_le hθ0 hθ1 hσ0 n d
  have hFsum : Summable (Function.uncurry F) :=
    (Summable.mul_of_nonneg hg hc hg0 hh0).of_norm_bounded fun p => hbound p.1 p.2
  have hrow : ∀ n, Summable (F n) := fun n =>
    ((hc.mul_left (g n))).of_norm_bounded fun d => hbound n d
  have hcol : ∀ d, Summable (fun n => F n d) := fun d =>
    ((hg.mul_right (h d))).of_norm_bounded fun n => hbound n d
  have hrowval : ∀ n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell σ n =
      ∑' d, F n d := fun n => by
    rw [weightCenteredPrefix_eq_tsum_modulusDefect c hs n, ← tsum_mul_right]
  have hsumA : Summable (fun n => weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell σ n) := by
    refine ((hg.mul_right (∑' d, h d))).of_norm_bounded fun n => ?_
    rw [hrowval n]
    calc ‖∑' d, F n d‖ ≤ ∑' d, ‖F n d‖ := norm_tsum_le_tsum_norm (hrow n).norm
      _ ≤ ∑' d, g n * h d := Summable.tsum_le_tsum (hbound n) (hrow n).norm (hc.mul_left (g n))
      _ = g n * ∑' d, h d := tsum_mul_left
  refine ⟨hsumA, ?_⟩
  have hcomm : ∑' n, ∑' d, F n d = ∑' d, ∑' n, F n d := (hFsum.tsum_comm' hrow hcol).symm
  have hinner : ∀ d, ((∑' n, F n d : ℝ) : ℂ) =
      riemannZeta σ * ((c d * ((d : ℝ) ^ (-σ) - 1 / d) : ℝ) : ℂ) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hF, modulusDefect_zero_left, Real.zero_rpow (show -σ ≠ 0 by intro h; linarith)]
    have hcd : ∀ n, F n d = c d * (modulusDefect d n * mellinCell σ n) := fun n => by
      simp only [hF]; ring
    simp_rw [hcd]
    rw [tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_tsum,
      (hasSum_modulusDefect_mul_mellinCell hσ0 hσ1 hd).tsum_eq]
    push_cast
    ring
  rw [tsum_congr hrowval, hcomm, Complex.ofReal_tsum]
  simp_rw [hinner]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  congr 2
  rw [← hCsum.tsum_sub hs]
  refine tsum_congr fun d => ?_
  ring

/-- A weight of `𝒞(K, ε)` is absolutely summable against `d^{-θ}` for `θ > 1 − ε`. -/
theorem summable_abs_mul_rpow_of_dampedClass {K ε θ : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (hθ : 1 - ε < θ) : Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)) :=
  (summable_mul_rpow_of_dampedClass hε hc hθ).abs.congr fun d => by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]

/-- **The Mellin pairing identity.** For a weight of `𝒞(K, ε)`, `0 < ε < 1`, and
`1 − ε < σ < 1`, `Σ_n A(n) Δ_n(σ) = ζ(σ) (C(σ) − m)`. -/
theorem mellinPairing_eq_zeta_mul {K ε σ : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c)
    (hσ0 : 0 < σ) (hσ : 1 - ε < σ) (hσ1 : σ < 1) :
    ((∑' n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell σ n : ℝ) : ℂ) =
      riemannZeta σ * (((∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d : ℝ) : ℂ) := by
  have h1 := le_max_left (1 - ε) 0
  have h2 := le_max_right (1 - ε) 0
  have h3 : max (1 - ε) 0 < σ := max_lt hσ hσ0
  exact (mellinPairing_eq_zeta_mul_of_summable (θ := (σ + max (1 - ε) 0) / 2) (by linarith)
    (by linarith) hσ1 (summable_abs_mul_rpow_of_dampedClass hε hc (by linarith))).2

/-! ### ζ on `(0, 1)` -/

/-- The strip remainders are at most `1 − 1/(1 − σ)`. -/
theorem zetaStripRemainder_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    zetaStripRemainder σ N ≤ 1 - 1 / (1 - σ) := by
  have h1σ : 0 < 1 - σ := by linarith
  -- one step: `(k+1)^{-σ} ≤ ((k+1)^{1-σ} − k^{1-σ})/(1−σ)`
  have hstep : ∀ k : ℕ, 1 ≤ k → ((k : ℝ) + 1) ^ (-σ) ≤
      (((k : ℝ) + 1) ^ (1 - σ) - (k : ℝ) ^ (1 - σ)) / (1 - σ) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hint : (∫ x in (k : ℝ)..((k : ℝ) + 1), x ^ (-σ)) =
        (((k : ℝ) + 1) ^ (1 - σ) - (k : ℝ) ^ (1 - σ)) / (1 - σ) := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show -σ + 1 = 1 - σ by ring]
    rw [← hint]
    have hconst : (∫ _x in (k : ℝ)..((k : ℝ) + 1), ((k : ℝ) + 1) ^ (-σ)) = ((k : ℝ) + 1) ^ (-σ) := by
      simp
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by linarith) (by simp) ?_ ?_
    · exact (continuousOn_id.rpow_const fun x hx =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hk0 hx.1))).intervalIntegrable_of_Icc (by linarith)
    · intro x hx
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2 (by linarith)
  induction N, hN using Nat.le_induction with
  | base => simp [zetaStripRemainder]
  | succ N hN ih =>
    simp only [zetaStripRemainder] at ih ⊢
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have := hstep N hN
    rw [sub_div] at this
    linarith

/-- **`Re ζ(σ) ≤ −σ/(1 − σ)` on `(0, 1)`.** -/
theorem riemannZeta_re_le_of_lt_one {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (riemannZeta σ).re ≤ -σ / (1 - σ) := by
  have h1σ : 0 < 1 - σ := by linarith
  have hre : Tendsto (fun N : ℕ => zetaStripRemainder σ N) atTop (𝓝 (riemannZeta σ).re) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_zetaStripRemainder hσ0 hσ1)
  have hb : -σ / (1 - σ) = 1 - 1 / (1 - σ) := by field_simp; ring
  rw [hb]
  exact le_of_tendsto hre (eventually_atTop.mpr ⟨1, fun N hN => zetaStripRemainder_le hσ0 hσ1 hN⟩)

/-- `|ζ(σ)| ≥ σ/(1 − σ)` on `(0, 1)`. -/
theorem div_le_norm_riemannZeta {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    σ / (1 - σ) ≤ ‖riemannZeta σ‖ := by
  have h := riemannZeta_re_le_of_lt_one hσ0 hσ1
  have hn := Complex.abs_re_le_norm (riemannZeta σ)
  have : σ / (1 - σ) = -(-σ / (1 - σ)) := by ring
  rw [this]
  exact (neg_le_neg h).trans ((neg_le_abs _).trans hn)

/-! ### The general pole law -/

/-- **The general pole law.** Let `Σ_d |c(d)| d^{-θ} < ∞` for some `0 < θ < σ`, with
`1/2 < σ < 1`. If every pronic energy of `c` is at most `E`, then
`|C(σ) − m| ≤ ((1 − σ)/σ) √E √(2σ²(1 + 1/(2σ − 1)))`. -/
theorem abs_dirichletSeries_sub_mean_le_of_energy_of_summable {E θ σ : ℝ} {c : ℕ → ℝ}
    (hθ0 : 0 < θ) (hθσ : θ < σ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hc : Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) :
    |(∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d| ≤
      (1 - σ) / σ * (Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))) := by
  have hσ0 : 0 < σ := by linarith
  have h1σ : 0 < 1 - σ := by linarith
  obtain ⟨hsA, hid⟩ := mellinPairing_eq_zeta_mul_of_summable hθ0 hθσ hσ1 hc
  have hbound := abs_tsum_mul_mellinCell_le hσ (weightCenteredPrefix_zero c _) hsA hE
  have hnorm : |∑' n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell σ n| =
      ‖riemannZeta σ‖ * |(∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hid, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have hz := div_le_norm_riemannZeta hσ0 hσ1
  set X := |(∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d|
  have hX : 0 ≤ X := abs_nonneg _
  have hkey : σ / (1 - σ) * X ≤ Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) :=
    (mul_le_mul_of_nonneg_right hz hX).trans (hnorm ▸ hbound)
  rw [div_mul_eq_mul_div, div_le_iff₀ h1σ] at hkey
  rw [div_mul_eq_mul_div, le_div_iff₀ hσ0]
  nlinarith

/-- **The general pole law on `𝒞(K, ε)`**, for `max(1/2, 1 − ε) < σ < 1`. -/
theorem abs_dirichletSeries_sub_mean_le_of_energy {K E ε σ : ℝ} {c : ℕ → ℝ} (hε : 0 < ε)
    (hc : DampedClass K ε c) (hσ : 1 / 2 < σ) (hσε : 1 - ε < σ) (hσ1 : σ < 1)
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) :
    |(∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d| ≤
      (1 - σ) / σ * (Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))) := by
  have h1 := le_max_left (1 - ε) 0
  have h2 := le_max_right (1 - ε) 0
  have h3 : max (1 - ε) 0 < σ := max_lt hσε (by linarith)
  exact abs_dirichletSeries_sub_mean_le_of_energy_of_summable (θ := (σ + max (1 - ε) 0) / 2)
    (by linarith) (by linarith) hσ hσ1 (summable_abs_mul_rpow_of_dampedClass hε hc (by linarith)) hE

/-- **The pole law in its asymptotic form**: a paid half-damped weight has
`|C(σ) − m| ≤ 2√E (2σ − 1)^{-1/2}` for `1/2 < σ < 1`. -/
theorem abs_dirichletSeries_sub_mean_le_rpow {K E σ : ℝ} {c : ℕ → ℝ}
    (hc : DampedClass K (1 / 2) c) (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) :
    |(∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d| ≤
      2 * Real.sqrt E * (2 * σ - 1) ^ (-(1 / 2 : ℝ)) := by
  have h := abs_dirichletSeries_sub_mean_le_of_energy (by norm_num) hc hσ (by linarith) hσ1 hE
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  have hσ0 : 0 < σ := by linarith
  have h2σ : 0 < 2 * σ - 1 := by linarith
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  -- `(1−σ)/σ · √(2σ²(1 + 1/(2σ−1))) ≤ 2 (2σ−1)^{-1/2}`
  have hfac : (1 - σ) / σ * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) ≤
      2 * (2 * σ - 1) ^ (-(1 / 2 : ℝ)) := by
    have hinv : (2 * σ - 1) ^ (-(1 / 2 : ℝ)) = Real.sqrt (1 / (2 * σ - 1)) := by
      rw [Real.rpow_neg h2σ.le, ← Real.sqrt_eq_rpow, Real.sqrt_div' 1 h2σ.le, Real.sqrt_one,
        one_div]
    rw [hinv]
    have hle1 : 1 ≤ 1 / (2 * σ - 1) := by rw [le_div_iff₀ h2σ]; linarith
    have hin : 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) ≤ (2 * σ / (1 - σ)) ^ 2 * (1 / (2 * σ - 1)) := by
      have h1σ : 0 < 1 - σ := by linarith
      have hσ2 : 2 * σ ^ 2 ≤ (2 * σ / (1 - σ)) ^ 2 / 2 := by
        rw [div_pow, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ (by positivity)]
        have h01 : 0 ≤ 1 - (1 - σ) ^ 2 := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg σ) h01]
      nlinarith [mul_le_mul_of_nonneg_left hσ2 (by positivity : (0 : ℝ) ≤ 1 / (2 * σ - 1))]
    calc (1 - σ) / σ * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))
        ≤ (1 - σ) / σ * Real.sqrt ((2 * σ / (1 - σ)) ^ 2 * (1 / (2 * σ - 1))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hin) (by
            have : 0 < 1 - σ := by linarith
            positivity)
      _ = 2 * Real.sqrt (1 / (2 * σ - 1)) := by
          have h1σ : 0 < 1 - σ := by linarith
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
          field_simp
  calc _ ≤ (1 - σ) / σ * (Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))) := h
    _ = Real.sqrt E * ((1 - σ) / σ * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))) := by ring
    _ ≤ Real.sqrt E * (2 * (2 * σ - 1) ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hfac hsE
    _ = 2 * Real.sqrt E * (2 * σ - 1) ^ (-(1 / 2 : ℝ)) := by ring

/-! ### Sign patterns with few flipped primes

For a completely multiplicative `f` with `|f(p)| ≤ 1`, the Euler product reads
`Σ f(n) n^{-w} = exp(Σ_p −log(1 − f(p) p^{-w}))` on `w > 1`. Comparing with the all-ones pattern
prime by prime, a flipped prime (`f(p) = −1`) costs at most `2p^{-w} + 2p^{-2w}` in the exponent,
so flipping a set of primes of upper Dirichlet density `δ` keeps
`Σ f(n) n^{-w} ≥ κ (w − 1)^{-(1-2δ)}`. At half damping the receiver of `f(d) d^{-1/2}` reads this
series at `w = σ + 1/2`, and the pole law caps it by `O((σ − 1/2)^{-1/2})`: below `δ = 1/4` the
two exponents are incompatible. -/

/-- A completely multiplicative function bounded by one at the primes is bounded by one. -/
theorem abs_le_one_of_primes (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (n : ℕ) :
    |f n| ≤ 1 := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact hf p hp
  | mul a b ha hb =>
    rw [map_mul, abs_mul]
    exact mul_le_one₀ ha (abs_nonneg _) hb

/-- The weighted pattern `n ↦ f(n) n^{-w}` as a completely multiplicative function to `ℂ`. -/
def weightedPatternHom (f : ℕ →*₀ ℝ) (w : ℝ) : ℕ →*₀ ℂ where
  toFun n := ((f n * (n : ℝ) ^ (-w) : ℝ) : ℂ)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    push_cast [map_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    push_cast
    ring

/-- **The real Euler product**: `Σ f(n) n^{-w} = exp(Σ_p −log(1 − f(p) p^{-w}))` for `w > 1`. -/
theorem tsum_pattern_eq_exp (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {w : ℝ}
    (hw : 1 < w) :
    ∑' n : ℕ, f n * (n : ℝ) ^ (-w) =
      Real.exp (∑' p : Nat.Primes, -Real.log (1 - f p * ((p : ℕ) : ℝ) ^ (-w))) := by
  have hsum : Summable (fun n => ‖weightedPatternHom f w n‖) := by
    refine (Real.summable_nat_rpow.mpr (show -w < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    simp only [weightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (abs_le_one_of_primes f hf n)
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum hsum
  -- every Euler factor is a positive real
  have hpos : ∀ p : Nat.Primes, 0 < 1 - f p * ((p : ℕ) : ℝ) ^ (-w) := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    have hx : ((p : ℕ) : ℝ) ^ (-w) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have := abs_le_one_of_primes f hf p
    have h2 : f p * ((p : ℕ) : ℝ) ^ (-w) ≤ |f p| * ((p : ℕ) : ℝ) ^ (-w) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) (-w)]
  have hlog : ∀ p : Nat.Primes, -Complex.log (1 - weightedPatternHom f w p) =
      ((-Real.log (1 - f p * ((p : ℕ) : ℝ) ^ (-w)) : ℝ) : ℂ) := by
    intro p
    simp only [weightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log (hpos p).le]
    push_cast
    ring
  simp_rw [hlog] at hE
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp] at hE
  have hR : ∑' n : ℕ, weightedPatternHom f w n = ((∑' n : ℕ, f n * (n : ℝ) ^ (-w) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; rfl
  rw [hR] at hE
  exact_mod_cast hE.symm

/-- The all-ones pattern, `n ↦ [n ≠ 0]`. -/
def onesPatternHom : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]

/-- **The all-ones Euler product is at least `1/(w − 1)`.** -/
theorem one_div_sub_one_le_exp_primes {w : ℝ} (hw : 1 < w) :
    1 / (w - 1) ≤ Real.exp (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-w))) := by
  have hones1 : ∀ p : ℕ, p.Prime → |onesPatternHom p| ≤ 1 := fun p hp => by
    simp [onesPatternHom, hp.ne_zero]
  have h := tsum_pattern_eq_exp onesPatternHom hones1 hw
  have hL1eq : ∀ p : Nat.Primes, -Real.log (1 - onesPatternHom p * ((p : ℕ) : ℝ) ^ (-w)) =
      -Real.log (1 - ((p : ℕ) : ℝ) ^ (-w)) := fun p => by
    simp [onesPatternHom, p.2.ne_zero]
  simp_rw [hL1eq] at h
  rw [← h]
  have hshift := HTGeometry.tsum_shift_rpow_ge (q := 1 - w) (by linarith) 0
  simp only [Nat.cast_zero, zero_add, Real.one_rpow, show -(1 - w) = w - 1 by ring,
    show 1 - w - 1 = -w by ring] at hshift
  have hsw : Summable (fun n : ℕ => onesPatternHom n * (n : ℝ) ^ (-w)) :=
    (Real.summable_nat_rpow.mpr (show -w < -1 by linarith)).of_nonneg_of_le
      (fun n => by simp only [onesPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk];
                   split_ifs <;> positivity)
      fun n => by simp only [onesPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk];
                  split_ifs <;> simp [Real.rpow_nonneg]
  rw [hsw.tsum_eq_zero_add]
  have hterm : ∀ k : ℕ, onesPatternHom (k + 1) * ((k + 1 : ℕ) : ℝ) ^ (-w) = (1 + (k : ℝ)) ^ (-w) :=
    fun k => by
      rw [show onesPatternHom (k + 1) = 1 by simp [onesPatternHom], one_mul]
      push_cast
      rw [add_comm]
  have h0 : onesPatternHom 0 * ((0 : ℕ) : ℝ) ^ (-w) = 0 := by simp [onesPatternHom]
  rw [h0, zero_add, tsum_congr hterm]
  exact hshift

/-- The prime-by-prime cost of flipping: `−log(1 + x) ≥ −log(1 − x) − 2x − 2x²` on `[0, 1/2]`. -/
theorem neg_log_one_add_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) - 2 * x - 2 * x ^ 2 ≤ -Real.log (1 + x) := by
  have h1 : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith); linarith
  have h2 : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) := Real.one_sub_inv_le_log_of_pos (by linarith)
  have h3 : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  linarith

/-- **Flipping a set of primes of Dirichlet density `δ` costs `(w − 1)^{2δ}`.** If
`Σ_{f(p) = −1} p^{-w} ≤ δ log(1/(w−1)) + B` on `1 < w < 3/2` and `f(p) = ±1` at every prime, then
`Σ f(n) n^{-w} ≥ e^{-2B-2S} (w − 1)^{-(1-2δ)}` with `S = Σ_p p^{-2}`. -/
theorem tsum_pattern_ge_rpow (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1)
    {δ B : ℝ}
    (hP : ∀ w : ℝ, 1 < w → w < 3 / 2 →
      ∑' p : Nat.Primes, (if f p = -1 then ((p : ℕ) : ℝ) ^ (-w) else 0) ≤
        δ * Real.log (1 / (w - 1)) + B)
    {w : ℝ} (hw : 1 < w) (hw2 : w < 3 / 2) :
    Real.exp (-2 * B - 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)) *
        (w - 1) ^ (-(1 - 2 * δ)) ≤ ∑' n : ℕ, f n * (n : ℝ) ^ (-w) := by
  have hf1 : ∀ p : ℕ, p.Prime → |f p| ≤ 1 := fun p hp => by
    rcases hf p hp with h | h <;> simp [h]
  set x : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-w) with hx
  have hx0 : ∀ p, 0 ≤ x p := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxhalf : ∀ p : Nat.Primes, x p ≤ 1 / 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    calc x p ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hxs : Summable x := Nat.Primes.summable_rpow.mpr (by linarith)
  have hx2s : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hxsq : ∀ p, x p ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)
  -- the two exponents
  set Lf : Nat.Primes → ℝ := fun p => -Real.log (1 - f p * x p)
  set L1 : Nat.Primes → ℝ := fun p => -Real.log (1 - x p)
  have hlogbound : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → |Real.log (1 - y)| ≤ 2 * y := by
    intro y hy0 hy
    have h2 : 1 - (1 - y)⁻¹ ≤ Real.log (1 - y) := Real.one_sub_inv_le_log_of_pos (by linarith)
    have h3 : (1 - y)⁻¹ ≤ 1 + 2 * y := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    have h4 : Real.log (1 - y) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    rw [abs_le]; constructor <;> linarith
  have hlogbound' : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → |Real.log (1 + y)| ≤ y := by
    intro y hy0 _
    have h1 : Real.log (1 + y) ≤ y := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith); linarith
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]; exact h1
  have hL1s : Summable L1 := (hxs.mul_left 2).of_norm_bounded fun p => by
    simp only [L1, Real.norm_eq_abs, abs_neg]; exact hlogbound _ (hx0 p) (hxhalf p)
  have hLfs : Summable Lf := (hxs.mul_left 2).of_norm_bounded fun p => by
    simp only [Lf, Real.norm_eq_abs, abs_neg]
    rcases hf p p.2 with h | h
    · rw [h, one_mul]; exact hlogbound _ (hx0 p) (hxhalf p)
    · rw [h, neg_one_mul, sub_neg_eq_add]
      exact (hlogbound' _ (hx0 p) (hxhalf p)).trans (by linarith [hx0 p])
  set I : Nat.Primes → ℝ := fun p => if f p = -1 then x p else 0
  have hIs : Summable I := hxs.of_nonneg_of_le (fun p => by
    simp only [I]; split_ifs <;> simp [hx0 p]) fun p => by
      simp only [I]; split_ifs <;> simp [hx0 p]
  have hterm : ∀ p, L1 p - 2 * I p - 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ Lf p := by
    intro p
    simp only [L1, Lf, I]
    rcases hf p p.2 with h | h
    · have hne : f p ≠ -1 := by rw [h]; norm_num
      rw [if_neg hne, h, one_mul]
      have := Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) (-2 : ℝ)
      linarith
    · rw [if_pos h, h, neg_one_mul, sub_neg_eq_add]
      have := neg_log_one_add_ge (hx0 p) (hxhalf p)
      nlinarith [hxsq p]
  have hsumle : ∑' p, L1 p - 2 * ∑' p, I p - 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤
      ∑' p, Lf p := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← hL1s.tsum_sub (hIs.mul_left 2),
      ← (hL1s.sub (hIs.mul_left 2)).tsum_sub (hx2s.mul_left 2)]
    exact Summable.tsum_le_tsum hterm ((hL1s.sub (hIs.mul_left 2)).sub (hx2s.mul_left 2)) hLfs
  -- the all-ones series is at least `1/(w − 1)`
  have hones : 1 / (w - 1) ≤ Real.exp (∑' p, L1 p) := one_div_sub_one_le_exp_primes hw
  -- assemble
  have hlog1 : Real.log (1 / (w - 1)) ≤ ∑' p, L1 p := by
    rw [← Real.log_exp (∑' p, L1 p)]
    exact Real.log_le_log (one_div_pos.mpr (by linarith)) hones
  have hIle := hP w hw hw2
  have hkey : (1 - 2 * δ) * Real.log (1 / (w - 1)) - 2 * B -
      2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ ∑' p, Lf p := by
    have : ∑' p, I p ≤ δ * Real.log (1 / (w - 1)) + B := hIle
    nlinarith [hsumle]
  rw [tsum_pattern_eq_exp f hf1 hw]
  have hw1 : 0 < w - 1 := by linarith
  have hrpow : (w - 1) ^ (-(1 - 2 * δ)) = Real.exp ((1 - 2 * δ) * Real.log (1 / (w - 1))) := by
    rw [Real.rpow_def_of_pos hw1, one_div, Real.log_inv]; ring_nf
  rw [hrpow, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **A pattern series growing faster than `(w − 1)^{-1/2}` is never paid.** If `f` is completely
multiplicative with `|f(p)| ≤ 1` and `Σ f(n) n^{-w} ≥ κ (w − 1)^{-α}` on `1 < w < 3/2` with `α > 1/2`,
then the half-damped weight `f(d) d^{-1/2}` has unbounded receiver: the pole law caps the series at
`w = σ + 1/2` by `O((σ − 1/2)^{-1/2})`. -/
theorem not_receiverBounded_of_pattern_ge (f : ℕ →*₀ ℝ) (hf1 : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    {κ α : ℝ} (hκ : 0 < κ) (hα : 1 / 2 < α)
    (hlow : ∀ w : ℝ, 1 < w → w < 3 / 2 → κ * (w - 1) ^ (-α) ≤ ∑' n : ℕ, f n * (n : ℝ) ^ (-w)) :
    ¬ ReceiverBounded (fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rintro ⟨E, hE⟩
  set c : ℕ → ℝ := fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : DampedClass 1 (1 / 2) c := by
    intro d
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_le_one_of_primes f hf1 d)
  set m := ∑' d : ℕ, c d / d with hmdef
  set β := α - 1 / 2
  have hβ : 0 < β := by simp only [β]; linarith
  -- on `u = σ − 1/2 ∈ (0, 1/2)`: `κ u^{-β} ≤ |m| + 2√E`
  have hup : ∀ u : ℝ, 0 < u → u < 1 / 2 → κ * u ^ (-β) ≤ |m| + 2 * Real.sqrt E := by
    intro u hu0 hu
    set σ := u + 1 / 2
    have hσ : 1 / 2 < σ := by simp only [σ]; linarith
    have hσ1 : σ < 1 := by simp only [σ]; linarith
    have hpole := abs_dirichletSeries_sub_mean_le_rpow hc hσ hσ1 hE
    rw [← hmdef] at hpole
    have hCeq : ∑' d : ℕ, c d * (d : ℝ) ^ (-σ) = ∑' n : ℕ, f n * (n : ℝ) ^ (-(σ + 1 / 2)) := by
      refine tsum_congr fun d => ?_
      simp only [c]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
        rw [mul_assoc, ← Real.rpow_add hd0]; ring_nf
    have hlw := hlow (σ + 1 / 2) (by linarith) (by linarith)
    have hw1 : σ + 1 / 2 - 1 = u := by simp only [σ]; ring
    rw [hw1] at hlw
    rw [hCeq] at hpole
    have h2σ : 2 * σ - 1 = 2 * u := by simp only [σ]; ring
    rw [h2σ] at hpole
    have hupper : κ * u ^ (-α) ≤ |m| + 2 * Real.sqrt E * (2 * u) ^ (-(1 / 2 : ℝ)) := by
      have := (le_abs_self _).trans hpole
      have hm := le_abs_self m
      linarith
    -- multiply by `u^{1/2}`
    have hu12 : 0 < u ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hu0 _
    have hmul := mul_le_mul_of_nonneg_left hupper hu12.le
    have e1 : u ^ (1 / 2 : ℝ) * (κ * u ^ (-α)) = κ * u ^ (-β) := by
      rw [mul_left_comm, ← Real.rpow_add hu0]; congr 2; simp only [β]; ring
    have e2 : u ^ (1 / 2 : ℝ) * (2 * u) ^ (-(1 / 2 : ℝ)) = 2 ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hu0.le, mul_left_comm, ← Real.rpow_add hu0]
      simp
    have hu12le : u ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hu0.le (by linarith) (by norm_num)
    have h2le : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hsE := Real.sqrt_nonneg E
    rw [e1, mul_add, show u ^ (1 / 2 : ℝ) * (2 * Real.sqrt E * (2 * u) ^ (-(1 / 2 : ℝ))) =
      2 * Real.sqrt E * (u ^ (1 / 2 : ℝ) * (2 * u) ^ (-(1 / 2 : ℝ))) by ring, e2] at hmul
    nlinarith [abs_nonneg m, mul_le_mul_of_nonneg_left hu12le (abs_nonneg m),
      mul_le_mul_of_nonneg_left h2le (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt E)]
  -- but `u^{-β} → ∞` as `u ↓ 0`
  have htend : Tendsto (fun u : ℝ => κ * u ^ (-β)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith)).const_mul_atTop hκ
  obtain ⟨u, hu1, hu2⟩ := ((htend.eventually_gt_atTop (|m| + 2 * Real.sqrt E)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  exact absurd (hup u hu2.1 hu2.2) (not_le.mpr hu1)

/-- **Sign patterns with few flipped primes are never paid at half damping.** Let `f` be completely
multiplicative with `f(p) = ±1` at every prime, and let its flipped primes have upper Dirichlet
density `δ < 1/4`: `Σ_{f(p) = −1} p^{-w} ≤ δ log(1/(w−1)) + B` on `1 < w < 3/2`. Then the receiver
of the half-damped weight `f(d) d^{-1/2}` is unbounded. -/
theorem not_receiverBounded_of_flippedDensity_lt_quarter (f : ℕ →*₀ ℝ)
    (hf : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1) {δ B : ℝ} (hδ : δ < 1 / 4)
    (hP : ∀ w : ℝ, 1 < w → w < 3 / 2 →
      ∑' p : Nat.Primes, (if f p = -1 then ((p : ℕ) : ℝ) ^ (-w) else 0) ≤
        δ * Real.log (1 / (w - 1)) + B) :
    ¬ ReceiverBounded (fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hf1 : ∀ p : ℕ, p.Prime → |f p| ≤ 1 := fun p hp => by
    rcases hf p hp with h | h <;> simp [h]
  exact not_receiverBounded_of_pattern_ge f hf1 (Real.exp_pos _) (by linarith)
    fun w hw hw2 => tsum_pattern_ge_rpow f hf hP hw hw2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
