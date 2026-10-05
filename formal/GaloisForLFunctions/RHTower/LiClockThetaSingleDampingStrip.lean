import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingSource
import GaloisForLFunctions.RHTower.SpectralBlaschkeMatching
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The exact single-damping strip classification

For `p > 0` let `T_n(p) = (-1)^n H^{(n)}(p)/(n-1)!`, `H(p) = log Φ(1/p)`, so that
`T_n(p) = (1/2) Σ_q Re C_n(p, w_q)` for `n ≥ 1`.

* (forward, strict) if every copy satisfies `|Im α_q| ≤ 1/(2p)`, then `Re C_n(p, w_q) > 0` for every
  copy and `T_n(p) > 0` for every `n ≥ 1`: both `|p ± iw_q| ≥ p`, at least one strictly;
* (S3) `T_n(p) > 0` for every `0 < p ≤ 1` and `n ≥ 1`, from `|Im α_q| < 1/2`;
* (converse, strengthened) if some copy has `|Im α_q| > 1/(2p)`, then `T_n(p) < 0` for infinitely
  many `n`: the smallest shift modulus `ρ < p` is attained on a finite packet `S`,
  `2ρ^n T_n(p) = -Σ_{S} Re u_i^n + o(1)` with `|u_i| = 1`, and simultaneous recurrence of the
  `u_i^n` near `1` makes it negative;
* (S2) `(∀ n ≥ 1, T_n(p) ≥ 0) ⟺ (∀ q, |Im α_q| ≤ 1/(2p)) ⟺ (eventually T_n(p) ≥ 0)`;
* (radius) under the strip condition the Taylor series of `H` at `p` has radius exactly `p`;
* (receiver) RH ⟺ all signs at every `p > 0` ⟺ all signs on an unbounded set of dampings.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

local notation "Φ" => liClockThetaGeneratorReal
local notation "C" => liClockStripAtom
local notation "T" => liClockStripCoefficient
local notation "w" => fun q : XiZeroCopy => (xiSpectralPoint q)⁻¹

/-! ## Shift moduli under and outside the strip -/

private theorem sq_norm_shift (p : ℝ) (q : XiZeroCopy) :
    ‖(p : ℂ) + I * w q‖ ^ 2 =
        p ^ 2 + (1 + 2 * p * (xiSpectralPoint q).im) / normSq (xiSpectralPoint q) ∧
      ‖(p : ℂ) - I * w q‖ ^ 2 =
        p ^ 2 + (1 - 2 * p * (xiSpectralPoint q).im) / normSq (xiSpectralPoint q) := by
  rw [Complex.sq_norm, Complex.sq_norm]
  exact normSq_ofReal_add_I_mul_inv p (xiSpectralPoint_ne_zero q)

private theorem le_norm_of_sq {p : ℝ} (hp : 0 < p) {x : ℂ} (h : p ^ 2 ≤ ‖x‖ ^ 2) : p ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ hp.le (norm_nonneg x) two_ne_zero).1 h

private theorem lt_norm_of_sq {p : ℝ} (hp : 0 < p) {x : ℂ} (h : p ^ 2 < ‖x‖ ^ 2) : p < ‖x‖ :=
  (pow_lt_pow_iff_left₀ hp.le (norm_nonneg x) two_ne_zero).1 h

/-- Under the closed strip both shift moduli are at least `p`, and at least one exceeds `p`. -/
theorem norm_shift_of_strip {p : ℝ} (hp : 0 < p) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) :
    p ≤ ‖(p : ℂ) - I * w q‖ ∧ p ≤ ‖(p : ℂ) + I * w q‖ ∧
      (p < ‖(p : ℂ) - I * w q‖ ∨ p < ‖(p : ℂ) + I * w q‖) := by
  obtain ⟨hplus, hminus⟩ := sq_norm_shift p q
  have hN := normSq_pos.2 (xiSpectralPoint_ne_zero q)
  set B := (xiSpectralPoint q).im
  have hB : 2 * p * |B| ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hq; linarith
  have hm1 := mul_le_mul_of_nonneg_left (neg_abs_le B) (by positivity : (0 : ℝ) ≤ 2 * p)
  have hm2 := mul_le_mul_of_nonneg_left (le_abs_self B) (by positivity : (0 : ℝ) ≤ 2 * p)
  have h1 : 0 ≤ 1 + 2 * p * B := by nlinarith
  have h2 : 0 ≤ 1 - 2 * p * B := by nlinarith
  refine ⟨le_norm_of_sq hp (by rw [hminus]; have := div_nonneg h2 hN.le; linarith),
    le_norm_of_sq hp (by rw [hplus]; have := div_nonneg h1 hN.le; linarith), ?_⟩
  rcases lt_or_ge 0 (1 - 2 * p * B) with h | h
  · exact Or.inl (lt_norm_of_sq hp (by rw [hminus]; have := div_pos h hN; linarith))
  · have hpos : (0 : ℝ) < 1 + 2 * p * B := by linarith
    exact Or.inr (lt_norm_of_sq hp (by rw [hplus]; have := div_pos hpos hN; linarith))

/-- Outside the strip one shift modulus is below `p`. -/
theorem norm_shift_lt_of_not_strip {p : ℝ} (hp : 0 < p) {q : XiZeroCopy}
    (hq : 1 / (2 * p) < |(xiSpectralPoint q).im|) :
    ‖(p : ℂ) - I * w q‖ < p ∨ ‖(p : ℂ) + I * w q‖ < p := by
  obtain ⟨hplus, hminus⟩ := sq_norm_shift p q
  have hN := normSq_pos.2 (xiSpectralPoint_ne_zero q)
  set B := (xiSpectralPoint q).im
  have hB : 1 < 2 * p * |B| := by
    rw [div_lt_iff₀ (by positivity)] at hq; linarith
  have hsq : ∀ x : ℂ, ‖x‖ ^ 2 < p ^ 2 → ‖x‖ < p := fun x h =>
    (pow_lt_pow_iff_left₀ (norm_nonneg x) hp.le two_ne_zero).1 h
  rcases le_total 0 B with hB0 | hB0
  · rw [abs_of_nonneg hB0] at hB
    have hneg : 1 - 2 * p * B < 0 := by linarith
    exact Or.inl (hsq _ (by rw [hminus]; have := div_neg_of_neg_of_pos hneg hN; linarith))
  · rw [abs_of_nonpos hB0] at hB
    have hneg : 1 + 2 * p * B < 0 := by linarith
    exact Or.inr (hsq _ (by rw [hplus]; have := div_neg_of_neg_of_pos hneg hN; linarith))

/-! ## Forward direction -/

private theorem re_inv_pow_le {x : ℂ} {p : ℝ} (hp : 0 < p) (hx : p ≤ ‖x‖) (n : ℕ) :
    ((x ^ n)⁻¹).re ≤ (p ^ n)⁻¹ :=
  (re_le_norm _).trans (by
    rw [norm_inv, norm_pow]; exact inv_anti₀ (pow_pos hp n) (pow_le_pow_left₀ hp.le hx n))

private theorem re_inv_pow_lt {x : ℂ} {p : ℝ} (hp : 0 < p) (hx : p < ‖x‖) {n : ℕ} (hn : 1 ≤ n) :
    ((x ^ n)⁻¹).re < (p ^ n)⁻¹ :=
  (re_le_norm _).trans_lt (by
    rw [norm_inv, norm_pow]
    exact inv_strictAnti₀ (pow_pos hp n) (pow_lt_pow_left₀ hx hp.le (by omega)))

theorem re_liClockStripAtom_eq (n : ℕ) (p : ℝ) (v : ℂ) :
    (C n p v).re = 2 * (p ^ n)⁻¹ - (((p : ℂ) - I * v) ^ n)⁻¹.re - (((p : ℂ) + I * v) ^ n)⁻¹.re := by
  unfold liClockStripAtom
  rw [show (2 : ℂ) * ((p : ℂ) ^ n)⁻¹ = ((2 * (p ^ n)⁻¹ : ℝ) : ℂ) by push_cast; ring, sub_re,
    sub_re, ofReal_re]

/-- Under the closed strip every cancelled atom has strictly positive real part. -/
theorem re_liClockStripAtom_pos_of_strip {p : ℝ} (hp : 0 < p) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) {n : ℕ} (hn : 1 ≤ n) :
    0 < (C n p (w q)).re := by
  obtain ⟨ha, hb, hs⟩ := norm_shift_of_strip hp hq
  rw [re_liClockStripAtom_eq]
  have h1 := re_inv_pow_le hp ha n
  have h2 := re_inv_pow_le hp hb n
  rcases hs with h | h
  · have := re_inv_pow_lt hp h hn; linarith
  · have := re_inv_pow_lt hp h hn; linarith

/-- **Strict forward direction.**  Under the closed strip, `T_n(p) > 0` for every `n ≥ 1`. -/
theorem liClockStripCoefficient_pos_of_strip {p : ℝ} (hp : 0 < p)
    (hstrip : ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) {n : ℕ} (hn : 1 ≤ n) : 0 < T n p := by
  have h := hasSum_liClockStripCoefficient hp hn
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  have hle := le_hasSum h q₀ fun q _ =>
    (div_pos (re_liClockStripAtom_pos_of_strip hp (hstrip q) hn) two_pos).le
  linarith [div_pos (re_liClockStripAtom_pos_of_strip hp (hstrip q₀) hn) two_pos]

/-- **(S3)** `T_n(p) > 0` for every `0 < p ≤ 1` and `n ≥ 1`. -/
theorem liClockStripCoefficient_pos_of_le_one {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) : 0 < T n p := by
  refine liClockStripCoefficient_pos_of_strip hp (fun q => ?_) hn
  have h := xiSpectralPoint_im_mem_openHalf q
  have h1 : |(xiSpectralPoint q).im| < 1 / 2 := abs_lt.2 ⟨by linarith [h.1], h.2⟩
  have h2 : (1 : ℝ) / 2 ≤ 1 / (2 * p) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-! ## Simultaneous recurrence of finitely many unimodular powers -/

/-- Finitely many unit complex numbers have arbitrarily late common powers within `ε` of `1`. -/
theorem exists_simultaneous_pow_recurrence {ι : Type*} [Fintype ι] (u : ι → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∀ i, ‖u i ^ n - 1‖ ≤ ε := by
  classical
  set v : ℕ → (ι → ℂ) := fun k i => u i ^ ((N + 1) * k)
  have hmem : ∀ k, v k ∈ Metric.closedBall (0 : ι → ℂ) 1 := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    simp [v, norm_pow, hu]
  obtain ⟨a, _, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hmem
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  have hkk : φ K < φ (K + 1) := hφ (Nat.lt_succ_self K)
  have hdist : ‖v (φ (K + 1)) - v (φ K)‖ ≤ ε := by
    have h1 : dist (v (φ (K + 1))) a < ε / 2 := hK (K + 1) (Nat.le_succ K)
    have h2 : dist (v (φ K)) a < ε / 2 := hK K le_rfl
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (v (φ (K + 1))) (v (φ K)) a]
  refine ⟨(N + 1) * (φ (K + 1) - φ K), ?_, fun i => ?_⟩
  · have : 1 ≤ φ (K + 1) - φ K := by omega
    nlinarith
  · have hsplit : v (φ (K + 1)) i - v (φ K) i =
        u i ^ ((N + 1) * φ K) * (u i ^ ((N + 1) * (φ (K + 1) - φ K)) - 1) := by
      simp only [v]
      rw [mul_sub, mul_one, ← pow_add,
        show (N + 1) * φ K + (N + 1) * (φ (K + 1) - φ K) = (N + 1) * φ (K + 1) by
          rw [← mul_add]; congr 1; omega]
    have hnorm : ‖v (φ (K + 1)) i - v (φ K) i‖ = ‖u i ^ ((N + 1) * (φ (K + 1) - φ K)) - 1‖ := by
      rw [hsplit, norm_mul, norm_pow, hu, one_pow, one_mul]
    rw [← hnorm]
    exact (norm_le_pi_norm (v (φ (K + 1)) - v (φ K)) i).trans hdist

/-! ## Converse: infinitely many negative coefficients outside the strip -/

/-- The damping shifts `p + iw_q` (`true`) and `p - iw_q` (`false`). -/
def liClockStripShift (p : ℝ) (i : XiZeroCopy × Bool) : ℂ :=
  if i.2 then (p : ℂ) + I * (xiSpectralPoint i.1)⁻¹ else (p : ℂ) - I * (xiSpectralPoint i.1)⁻¹

local notation "z" => liClockStripShift

private theorem atom_scaled (n : ℕ) (p ρ : ℝ) (hp : 0 < p) (v : ℂ) :
    ρ ^ n * (C n p v).re = 2 * (ρ / p) ^ n - (((ρ : ℂ) / ((p : ℂ) + I * v)) ^ n).re -
      (((ρ : ℂ) / ((p : ℂ) - I * v)) ^ n).re := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hC : (ρ : ℂ) ^ n * C n p v = (((2 * (ρ / p) ^ n : ℝ)) : ℂ) -
      ((ρ : ℂ) / ((p : ℂ) + I * v)) ^ n - ((ρ : ℂ) / ((p : ℂ) - I * v)) ^ n := by
    unfold liClockStripAtom
    push_cast
    rw [div_pow, div_pow, div_pow]
    ring
  have h := congrArg Complex.re hC
  rw [← ofReal_pow, re_ofReal_mul, sub_re, sub_re, ofReal_re] at h
  rw [h]

private theorem abs_re_div_pow_le {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) {x : ℂ} (hx : m ≤ ‖x‖)
    (n : ℕ) : |(((ρ : ℂ) / x) ^ n).re| ≤ (ρ / m) ^ n := by
  refine (abs_re_le_norm _).trans ?_
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hρ.le hm hx) n

private theorem tendsto_norm_liClockStripShift {p : ℝ} (hp : 0 < p) (b : Bool) :
    Tendsto (fun q => ‖z p (q, b)‖) cofinite (𝓝 p) := by
  have h := tendsto_inv_xiSpectralPoint_cofinite
  cases b
  · simpa [liClockStripShift, abs_of_pos hp] using ((tendsto_const_nhds (x := (p : ℂ))).sub
      ((tendsto_const_nhds (x := I)).mul h)).norm
  · simpa [liClockStripShift, abs_of_pos hp] using ((tendsto_const_nhds (x := (p : ℂ))).add
      ((tendsto_const_nhds (x := I)).mul h)).norm

/-- **Dominant packet.**  Outside the strip the smallest shift modulus `ρ < p` is attained on a
finite nonempty packet `S`, and all other shifts have modulus at least some `ρ₂ ∈ (ρ, p]`. -/
private theorem exists_dominant_packet {p : ℝ} (hp : 0 < p) {q₀ : XiZeroCopy}
    (hq₀ : 1 / (2 * p) < |(xiSpectralPoint q₀).im|) :
    ∃ (S : Finset (XiZeroCopy × Bool)) (ρ ρ₂ : ℝ), 0 < ρ ∧ ρ < ρ₂ ∧ ρ₂ ≤ p ∧ S.Nonempty ∧
      (∀ i ∈ S, ‖z p i‖ = ρ) ∧ ∀ i, i ∉ S → ρ₂ ≤ ‖z p i‖ := by
  classical
  obtain ⟨δ, hδ, -, hgap⟩ := exists_liClockStrip_gap hp
  have hνδ : ∀ i, δ ≤ ‖z p i‖ := by
    rintro ⟨q, b⟩
    cases b
    · exact (hgap q).1
    · exact (hgap q).2
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, ‖z p (q₀, b₀)‖ < p := by
    rcases norm_shift_lt_of_not_strip hp hq₀ with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨L, hL0, hLp⟩ : ∃ L, ‖z p (q₀, b₀)‖ < L ∧ L < p := exists_between hb₀
  have hfin : ∀ b, {q | ‖z p (q, b)‖ ≤ L}.Finite := by
    intro b
    have hev := (tendsto_norm_liClockStripShift hp b).eventually (lt_mem_nhds hLp)
    rw [Filter.eventually_cofinite] at hev
    simpa [not_lt] using hev
  set F : Finset (XiZeroCopy × Bool) :=
    (((hfin true).toFinset ∪ (hfin false).toFinset) ×ˢ Finset.univ).filter fun i => ‖z p i‖ ≤ L
  have hmemF : ∀ i, i ∈ F ↔ ‖z p i‖ ≤ L := by
    rintro ⟨q, b⟩
    simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h
  have hFne : F.Nonempty := ⟨(q₀, b₀), (hmemF _).2 hL0.le⟩
  obtain ⟨i₁, hi₁, hmin⟩ := F.exists_min_image (fun i => ‖z p i‖) hFne
  have hρL : ‖z p i₁‖ < L := (hmin _ ((hmemF _).2 hL0.le)).trans_lt hL0
  have hρle : ∀ i, ‖z p i₁‖ ≤ ‖z p i‖ := fun i => by
    by_cases hi : ‖z p i‖ ≤ L
    · exact hmin i ((hmemF i).2 hi)
    · exact hρL.le.trans (le_of_lt (not_le.1 hi))
  set S := F.filter fun i => ‖z p i‖ = ‖z p i₁‖
  have hSne : S.Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨hi₁, rfl⟩⟩
  set R := F.filter fun i => ‖z p i‖ ≠ ‖z p i₁‖
  obtain ⟨ρ₂, hρρ₂, hρ₂L, hρ₂⟩ : ∃ ρ₂, ‖z p i₁‖ < ρ₂ ∧ ρ₂ ≤ L ∧
      ∀ i, i ∉ S → ρ₂ ≤ ‖z p i‖ := by
    by_cases hR : R.Nonempty
    · obtain ⟨j, hj, hjmin⟩ := R.exists_min_image (fun i => ‖z p i‖) hR
      have hjF := Finset.mem_filter.1 hj
      refine ⟨min L ‖z p j‖, lt_min hρL (lt_of_le_of_ne (hρle j) (Ne.symm hjF.2)),
        min_le_left _ _, fun i hi => ?_⟩
      by_cases hiL : ‖z p i‖ ≤ L
      · have hiF := (hmemF i).2 hiL
        have hiR : i ∈ R :=
          Finset.mem_filter.2 ⟨hiF, fun h => hi (Finset.mem_filter.2 ⟨hiF, h⟩)⟩
        exact (min_le_right _ _).trans (hjmin i hiR)
      · exact (min_le_left _ _).trans (le_of_lt (not_le.1 hiL))
    · refine ⟨L, hρL, le_rfl, fun i hi => ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have hiF := (hmemF i).2 hlt.le
      exact hR ⟨i, Finset.mem_filter.2 ⟨hiF, fun h => hi (Finset.mem_filter.2 ⟨hiF, h⟩)⟩⟩
  exact ⟨S, ‖z p i₁‖, ρ₂, hδ.trans_le (hνδ i₁), hρρ₂, hρ₂L.trans hLp.le, hSne,
    fun i hi => (Finset.mem_filter.1 hi).2, hρ₂⟩

/-- Away from a finite set `QS` of copies whose shifts all have modulus `≥ ρ₂`, the cancelled
family has total size at most `2n²A/ρ₂^{n+2}`. -/
private theorem abs_two_mul_coefficient_sub_head_le {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n)
    {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (hρ₂p : ρ₂ ≤ p) (QS : Finset XiZeroCopy)
    (hout : ∀ q, q ∉ QS → ∀ b, ρ₂ ≤ ‖z p (q, b)‖) :
    |2 * T n p - ∑ q ∈ QS, (C n p (w q)).re| ≤
      2 * n ^ 2 * (∑' q, ‖(xiSpectralPoint q)⁻¹‖ ^ 2) / ρ₂ ^ (n + 2) := by
  classical
  have hpn : ‖(p : ℂ)‖ = p := by simp [abs_of_pos hp]
  have hf : HasSum (fun q => (C n p (w q)).re) (2 * T n p) := by
    have hT := (hasSum_liClockStripCoefficient hp hn).mul_left 2
    have e : (fun i => 2 * ((C n p (w i)).re / 2)) = fun q => (C n p (w q)).re := by
      funext q; ring
    rwa [e] at hT
  have hhead : HasSum (fun q => if q ∈ QS then (C n p (w q)).re else 0)
      (∑ q ∈ QS, (C n p (w q)).re) := by
    have h : HasSum (fun q => if q ∈ QS then (C n p (w q)).re else 0)
        (∑ q ∈ QS, if q ∈ QS then (C n p (w q)).re else 0) :=
      hasSum_sum_of_ne_finset_zero fun q hq => if_neg hq
    have e : ∑ q ∈ QS, (if q ∈ QS then (C n p (w q)).re else 0) = ∑ q ∈ QS, (C n p (w q)).re :=
      Finset.sum_congr rfl fun q hq => if_pos hq
    rwa [e] at h
  have hg := hf.sub hhead
  have hB := (summable_norm_inv_xiSpectralPoint_sq.hasSum.mul_left (2 * (n : ℝ) ^ 2)).div_const
    (ρ₂ ^ (n + 2))
  have hbound : ∀ q, |(C n p (w q)).re - (if q ∈ QS then (C n p (w q)).re else 0)| ≤
      2 * (n : ℝ) ^ 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 / ρ₂ ^ (n + 2) := by
    intro q
    by_cases hq : q ∈ QS
    · rw [if_pos hq, sub_self, abs_zero]; positivity
    · rw [if_neg hq, sub_zero]
      exact (abs_re_le_norm _).trans (norm_liClockStripAtom_le n hρ₂ (by rw [hpn]; exact hρ₂p)
        (hout q hq false) (hout q hq true))
  rw [abs_le]
  constructor
  · have := hasSum_le (fun q => neg_le_of_abs_le (hbound q)) hB.neg hg
    linarith
  · exact hasSum_le (fun q => le_of_abs_le (hbound q)) hg hB

private theorem head_identity {p : ℝ} (hp : 0 < p) (ρ : ℝ) (n : ℕ) (QS : Finset XiZeroCopy) :
    ∑ q ∈ QS, ρ ^ n * (C n p (w q)).re = 2 * QS.card * (ρ / p) ^ n -
      ∑ i ∈ QS ×ˢ (Finset.univ : Finset Bool), (((ρ : ℂ) / z p i) ^ n).re := by
  rw [Finset.sum_product]
  simp only [Fintype.sum_bool]
  rw [show (2 * (QS.card : ℝ) * (ρ / p) ^ n) = ∑ q ∈ QS, 2 * (ρ / p) ^ n by
    rw [Finset.sum_const, nsmul_eq_mul]; ring, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [atom_scaled n p ρ hp]
  simp only [liClockStripShift, if_true, Bool.false_eq_true, if_false]
  ring

/-- **Strengthened converse.**  If some copy violates the closed strip at damping `p`, then
`T_n(p) < 0` for infinitely many `n`. -/
theorem frequently_liClockStripCoefficient_neg {p : ℝ} (hp : 0 < p) {q₀ : XiZeroCopy}
    (hq₀ : 1 / (2 * p) < |(xiSpectralPoint q₀).im|) :
    ∃ᶠ n in atTop, T n p < 0 := by
  classical
  obtain ⟨S, ρ, ρ₂, hρ, hρρ₂, hρ₂p, hSne, hSρ, hρ₂⟩ := exists_dominant_packet hp hq₀
  have hρ₂pos : 0 < ρ₂ := hρ.trans hρρ₂
  have hρp : ρ < p := hρρ₂.trans_le hρ₂p
  set QS : Finset XiZeroCopy := S.image Prod.fst
  have hSsub : S ⊆ QS ×ˢ Finset.univ := fun i hi =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ _⟩
  have hout : ∀ q, q ∉ QS → ∀ b, ρ₂ ≤ ‖z p (q, b)‖ := fun q hq b =>
    hρ₂ (q, b) fun hb => hq (Finset.mem_image.2 ⟨(q, b), hb, rfl⟩)
  set A := ∑' q, ‖(xiSpectralPoint q)⁻¹‖ ^ 2
  set c₁ : ℝ := 2 * QS.card
  set c₂ : ℝ := (((QS ×ˢ Finset.univ) \ S).card : ℝ)
  set c₃ : ℝ := 2 * A / ρ₂ ^ 2
  -- the error term and its bound
  have herr : ∀ n, 1 ≤ n →
      |2 * ρ ^ n * T n p + ∑ i ∈ S, (((ρ : ℂ) / z p i) ^ n).re| ≤
        c₁ * (ρ / p) ^ n + c₂ * (ρ / ρ₂) ^ n + c₃ * (n ^ 2 * (ρ / ρ₂) ^ n) := by
    intro n hn
    set G := 2 * T n p - ∑ q ∈ QS, (C n p (w q)).re
    have hG := abs_two_mul_coefficient_sub_head_le hp hn hρ₂pos hρ₂p QS hout
    have hsplit := Finset.sum_sdiff (f := fun i => (((ρ : ℂ) / z p i) ^ n).re) hSsub
    have heq : 2 * ρ ^ n * T n p + ∑ i ∈ S, (((ρ : ℂ) / z p i) ^ n).re =
        c₁ * (ρ / p) ^ n - ∑ i ∈ (QS ×ˢ Finset.univ) \ S, (((ρ : ℂ) / z p i) ^ n).re +
          ρ ^ n * G := by
      have h1 : 2 * ρ ^ n * T n p = ∑ q ∈ QS, ρ ^ n * (C n p (w q)).re + ρ ^ n * G := by
        rw [← Finset.mul_sum]; simp only [G]; ring
      rw [h1, head_identity hp ρ n QS, ← hsplit]
      simp only [c₁]
      ring
    rw [heq]
    have h1 : |∑ i ∈ (QS ×ˢ Finset.univ) \ S, (((ρ : ℂ) / z p i) ^ n).re| ≤ c₂ * (ρ / ρ₂) ^ n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [show c₂ * (ρ / ρ₂) ^ n = ∑ _i ∈ (QS ×ˢ Finset.univ) \ S, (ρ / ρ₂) ^ n by
        rw [Finset.sum_const, nsmul_eq_mul]]
      exact Finset.sum_le_sum fun i hi =>
        abs_re_div_pow_le hρ hρ₂pos (hρ₂ i (Finset.mem_sdiff.1 hi).2) n
    have h2 : |ρ ^ n * G| ≤ c₃ * (n ^ 2 * (ρ / ρ₂) ^ n) := by
      rw [abs_mul, abs_of_pos (pow_pos hρ n)]
      calc ρ ^ n * |G| ≤ ρ ^ n * (2 * n ^ 2 * A / ρ₂ ^ (n + 2)) :=
            mul_le_mul_of_nonneg_left hG (pow_pos hρ n).le
        _ = c₃ * (n ^ 2 * (ρ / ρ₂) ^ n) := by
            simp only [c₃]; rw [div_pow, pow_add]; field_simp
    have h0 : 0 ≤ c₁ * (ρ / p) ^ n := by positivity
    calc |c₁ * (ρ / p) ^ n - ∑ i ∈ (QS ×ˢ Finset.univ) \ S, (((ρ : ℂ) / z p i) ^ n).re +
          ρ ^ n * G|
        ≤ |c₁ * (ρ / p) ^ n| + |∑ i ∈ (QS ×ˢ Finset.univ) \ S, (((ρ : ℂ) / z p i) ^ n).re| +
          |ρ ^ n * G| := (abs_add_le _ _).trans (by gcongr; exact abs_sub _ _)
      _ ≤ c₁ * (ρ / p) ^ n + c₂ * (ρ / ρ₂) ^ n + c₃ * (n ^ 2 * (ρ / ρ₂) ^ n) := by
          rw [abs_of_nonneg h0]; linarith
  have hlim : Tendsto (fun n : ℕ => c₁ * (ρ / p) ^ n + c₂ * (ρ / ρ₂) ^ n +
      c₃ * (n ^ 2 * (ρ / ρ₂) ^ n)) atTop (𝓝 0) := by
    have hr1 : ρ / p < 1 := (div_lt_one hp).2 hρp
    have hr2 : ρ / ρ₂ < 1 := (div_lt_one hρ₂pos).2 hρρ₂
    have t1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1).const_mul c₁
    have t2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr2).const_mul c₂
    have hr2' : |ρ / ρ₂| < 1 := by rw [abs_of_pos (div_pos hρ hρ₂pos)]; exact hr2
    have t3 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr2').const_mul c₃
    have h := (t1.add t2).add t3
    simp only [mul_zero, add_zero] at h
    exact h
  -- recurrence on the dominant packet
  have hu : ∀ i : S, ‖(ρ : ℂ) / z p i‖ = 1 := fun i => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hSρ i i.2, div_self hρ.ne']
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 2)))
  obtain ⟨n, hn, hrec⟩ := exists_simultaneous_pow_recurrence (fun i : S => (ρ : ℂ) / z p i) hu
    (by norm_num : (0 : ℝ) < 1 / 2) (max N (max N₁ 1))
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hE := (herr n hn1).trans_lt (hN₁ n hnN₁)
  have hre : ∀ i ∈ S, (1 : ℝ) / 2 ≤ (((ρ : ℂ) / z p i) ^ n).re := by
    intro i hi
    have h := hrec ⟨i, hi⟩
    have h2 := (abs_re_le_norm ((((ρ : ℂ) / z p i) ^ n) - 1)).trans h
    rw [sub_re, one_re] at h2
    linarith [neg_abs_le ((((ρ : ℂ) / z p i) ^ n).re - 1)]
  have hsumS : (1 : ℝ) / 2 ≤ ∑ i ∈ S, (((ρ : ℂ) / z p i) ^ n).re := by
    obtain ⟨i₀, hi₀⟩ := hSne
    exact (hre i₀ hi₀).trans (Finset.single_le_sum
      (fun i hi => (by linarith [hre i hi] : (0 : ℝ) ≤ (((ρ : ℂ) / z p i) ^ n).re)) hi₀)
  have hneg : 2 * ρ ^ n * T n p < 0 := by
    have := (abs_lt.1 hE).2
    linarith
  by_contra hT
  rw [not_lt] at hT
  linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ρ ^ n) hT]

/-! ## The strip classification -/

/-- **(S2)** At a fixed damping `p > 0`, all signs `T_n(p) ≥ 0` (`n ≥ 1`), or merely eventual
signs, are equivalent to the closed strip `|Im α_q| ≤ 1/(2p)` for every copy. -/
theorem liClockStripCoefficient_nonneg_iff {p : ℝ} (hp : 0 < p) :
    ((∀ n, 1 ≤ n → 0 ≤ T n p) ↔ ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) ∧
      ((∀ᶠ n in atTop, 0 ≤ T n p) ↔ ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) := by
  have hstrip_of_ev : (∀ᶠ n in atTop, 0 ≤ T n p) → ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p) := by
    intro hev q
    by_contra hq
    rw [not_le] at hq
    obtain ⟨n, hneg, hnn⟩ := ((frequently_liClockStripCoefficient_neg hp hq).and_eventually hev).exists
    linarith
  have hev_of_strip : (∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) → ∀ n, 1 ≤ n → 0 ≤ T n p :=
    fun hs n hn => (liClockStripCoefficient_pos_of_strip hp hs hn).le
  refine ⟨⟨fun h => hstrip_of_ev ((eventually_ge_atTop 1).mono h), hev_of_strip⟩,
    ⟨hstrip_of_ev, fun hs => (eventually_ge_atTop 1).mono (hev_of_strip hs)⟩⟩

/-- RH is the reality of every multiplicity copy. -/
theorem riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
  rw [riemannHypothesis_iff_forall_xiSpectralPointSupport_im_eq_zero]
  constructor
  · intro h q
    rw [xiSpectralPoint_eq_support]
    exact h q.1
  · intro h ρ
    have hpos := xi_divisor_pos_on_support ρ
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
    simpa only [xiSpectralPoint_eq_support] using h ⟨ρ, ⟨0, hn⟩⟩

/-- **Receiver.**  RH holds iff all single-damping signs hold at every `p > 0`, iff they hold on an
unbounded set of dampings. -/
theorem rh_iff_liClockStripCoefficient_nonneg :
    (RiemannHypothesis ↔ ∀ p, 0 < p → ∀ n, 1 ≤ n → 0 ≤ T n p) ∧
      (RiemannHypothesis ↔ ∀ P : ℝ, ∃ p, P ≤ p ∧ 0 < p ∧ ∀ n, 1 ≤ n → 0 ≤ T n p) := by
  have h1 : RiemannHypothesis → ∀ p, 0 < p → ∀ n, 1 ≤ n → 0 ≤ T n p := by
    intro hRH p hp n hn
    refine ((liClockStripCoefficient_nonneg_iff hp).1.2 fun q => ?_) n hn
    rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero.1 hRH q, abs_zero]
    positivity
  have h3 : (∀ P : ℝ, ∃ p, P ≤ p ∧ 0 < p ∧ ∀ n, 1 ≤ n → 0 ≤ T n p) → RiemannHypothesis := by
    intro h
    rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero]
    intro q
    by_contra hne
    have hB : 0 < |(xiSpectralPoint q).im| := abs_pos.2 hne
    obtain ⟨p, hpP, hp, hall⟩ := h (1 / |(xiSpectralPoint q).im|)
    have hstrip := (liClockStripCoefficient_nonneg_iff hp).1.1 hall q
    have hp' : 1 / |(xiSpectralPoint q).im| ≤ p := hpP
    rw [div_le_iff₀ hB] at hp'
    rw [le_div_iff₀ (by positivity)] at hstrip
    nlinarith
  refine ⟨⟨h1, fun h => h3 fun P => ⟨max P 1, le_max_left _ _,
    lt_of_lt_of_le one_pos (le_max_right _ _), h _ (lt_of_lt_of_le one_pos (le_max_right _ _))⟩⟩,
    ⟨fun hRH P => ⟨max P 1, le_max_left _ _, lt_of_lt_of_le one_pos (le_max_right _ _),
      h1 hRH _ (lt_of_lt_of_le one_pos (le_max_right _ _))⟩, h3⟩⟩

/-! ## The Taylor radius under the strip -/

private theorem abs_iteratedDeriv_div_factorial {p : ℝ} (hp : 0 < p)
    (hstrip : ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) {n : ℕ} (hn : 1 ≤ n) :
    |iteratedDeriv n (fun q : ℝ => Real.log (Φ q⁻¹)) p| / (n.factorial : ℝ) = T n p / n := by
  have hT := liClockStripCoefficient_pos_of_strip hp hstrip hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdef : T (m + 1) p * (m.factorial : ℝ) =
      (-1) ^ (m + 1) * iteratedDeriv (m + 1) (fun q : ℝ => Real.log (Φ q⁻¹)) p := by
    unfold liClockStripCoefficient
    rw [Nat.add_sub_cancel]
    field_simp
  have habs : |iteratedDeriv (m + 1) (fun q : ℝ => Real.log (Φ q⁻¹)) p| =
      T (m + 1) p * (m.factorial : ℝ) := by
    rw [show |iteratedDeriv (m + 1) (fun q : ℝ => Real.log (Φ q⁻¹)) p| =
        |(-1) ^ (m + 1) * iteratedDeriv (m + 1) (fun q : ℝ => Real.log (Φ q⁻¹)) p| by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul], ← hdef,
      abs_of_pos (mul_pos hT (by positivity))]
  rw [habs, Nat.factorial_succ]
  push_cast
  field_simp

/-- Under the strip, `T_n(p) ≤ n² A/p^{n+2}`, `A = Σ_q |w_q|²`. -/
private theorem liClockStripCoefficient_le {p : ℝ} (hp : 0 < p)
    (hstrip : ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) {n : ℕ} (hn : 1 ≤ n) :
    T n p ≤ n ^ 2 * (∑' q, ‖(xiSpectralPoint q)⁻¹‖ ^ 2) / p ^ (n + 2) := by
  have hpn : ‖(p : ℂ)‖ = p := by simp [abs_of_pos hp]
  have hB := (summable_norm_inv_xiSpectralPoint_sq.hasSum.mul_left ((n : ℝ) ^ 2)).div_const
    (p ^ (n + 2))
  refine hasSum_le (fun q => ?_) (hasSum_liClockStripCoefficient hp hn) hB
  obtain ⟨ha, hb, -⟩ := norm_shift_of_strip hp (hstrip q)
  have h := (re_le_norm _).trans (norm_liClockStripAtom_le n hp (by rw [hpn]) ha hb)
  linarith [show 2 * (n : ℝ) ^ 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 / p ^ (n + 2) / 2 =
    (n : ℝ) ^ 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 / p ^ (n + 2) by ring]

/-- **Exact Taylor radius.**  Under the closed strip the Taylor series of `H(p) = log Φ(1/p)` at
`p` converges absolutely on `|u| < p` and diverges absolutely at `|u| = p`: its radius is `p`. -/
theorem liClockStrip_taylor_radius {p : ℝ} (hp : 0 < p)
    (hstrip : ∀ q, |(xiSpectralPoint q).im| ≤ 1 / (2 * p)) :
    (∀ r, 0 ≤ r → r < p → Summable fun n =>
        |iteratedDeriv n (fun q : ℝ => Real.log (Φ q⁻¹)) p| / (n.factorial : ℝ) * r ^ n) ∧
      ¬ Summable fun n =>
        |iteratedDeriv n (fun q : ℝ => Real.log (Φ q⁻¹)) p| / (n.factorial : ℝ) * p ^ n := by
  set A := ∑' q, ‖(xiSpectralPoint q)⁻¹‖ ^ 2
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  constructor
  · intro r hr hrp
    rw [← summable_nat_add_iff 1]
    have hρ : ‖r / p‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact (div_lt_one hp).2 hrp
    have hgeo := ((summable_pow_mul_geometric_of_norm_lt_one 2 hρ).mul_left (A / p ^ 2))
    rw [← summable_nat_add_iff 1] at hgeo
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
    rw [abs_iteratedDeriv_div_factorial hp hstrip (by omega)]
    have hT := liClockStripCoefficient_le hp hstrip (n := n + 1) (by omega)
    have hTpos := (liClockStripCoefficient_pos_of_strip hp hstrip (n := n + 1) (by omega)).le
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 n
    calc T (n + 1) p / ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) ≤ T (n + 1) p * r ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (div_le_self hTpos hn1) (by positivity)
      _ ≤ (n + 1 : ℕ) ^ 2 * A / p ^ (n + 1 + 2) * r ^ (n + 1) := by gcongr
      _ = A / p ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2 * (r / p) ^ (n + 1)) := by
          rw [div_pow, pow_add p (n + 1) 2]; field_simp
  · intro hsum
    obtain ⟨q₀⟩ := nonempty_xiZeroCopy
    obtain ⟨ha, hb, hs⟩ := norm_shift_of_strip hp (hstrip q₀)
    -- one shift ratio is strictly below one
    obtain ⟨κ, hκ0, hκ1, hκ⟩ : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ n, 1 ≤ n →
        (1 - κ) / 2 ≤ T n p * p ^ n := by
      have hbase : ∀ {x : ℂ}, p ≤ ‖x‖ → ∀ n, ((x ^ n)⁻¹).re * p ^ n ≤ (p / ‖x‖) ^ n := by
        intro x hx n
        have hx0 : 0 < ‖x‖ := hp.trans_le hx
        refine (mul_le_mul_of_nonneg_right (re_le_norm _) (by positivity)).trans_eq ?_
        rw [norm_inv, norm_pow, div_pow]; field_simp
      have hT : ∀ n, 1 ≤ n → (C n p (w q₀)).re / 2 ≤ T n p := fun n hn =>
        le_hasSum (hasSum_liClockStripCoefficient hp hn) q₀ fun q _ =>
          (div_pos (re_liClockStripAtom_pos_of_strip hp (hstrip q) hn) two_pos).le
      have key : ∀ {x y : ℂ}, p ≤ ‖x‖ → p < ‖y‖ → ∀ n, 1 ≤ n →
          (1 - p / ‖y‖) / 2 ≤ (2 * (p ^ n)⁻¹ - ((x ^ n)⁻¹).re - ((y ^ n)⁻¹).re) / 2 * p ^ n := by
        intro x y hx hy n hn
        have hy0 : 0 < ‖y‖ := hp.trans hy
        have h1 := hbase hx n
        have h2 := hbase hy.le n
        have hxle : (p / ‖x‖) ^ n ≤ 1 :=
          pow_le_one₀ (by positivity) ((div_le_one (hp.trans_le hx)).2 hx)
        have hyle : (p / ‖y‖) ^ n ≤ p / ‖y‖ :=
          pow_le_of_le_one (by positivity) ((div_le_one hy0).2 hy.le) (by omega)
        have hpn : (p ^ n)⁻¹ * p ^ n = 1 := inv_mul_cancel₀ (pow_pos hp n).ne'
        nlinarith
      rcases hs with h | h
      · refine ⟨p / ‖(p : ℂ) - I * w q₀‖, by positivity, (div_lt_one (hp.trans h)).2 h,
          fun n hn => (key hb h n hn |>.trans_eq ?_).trans
            (mul_le_mul_of_nonneg_right (hT n hn) (by positivity))⟩
        rw [re_liClockStripAtom_eq]; ring
      · refine ⟨p / ‖(p : ℂ) + I * w q₀‖, by positivity, (div_lt_one (hp.trans h)).2 h,
          fun n hn => (key ha h n hn |>.trans_eq ?_).trans
            (mul_le_mul_of_nonneg_right (hT n hn) (by positivity))⟩
        rw [re_liClockStripAtom_eq]
    have hc : 0 < (1 - κ) / 2 := by linarith
    have hharm : Summable fun n : ℕ => (1 - κ) / 2 * (1 / ((n + 1 : ℕ) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        ((summable_nat_add_iff 1).2 hsum)
      rw [abs_iteratedDeriv_div_factorial hp hstrip (by omega)]
      have := hκ (n + 1) (by omega)
      rw [show T (n + 1) p / ((n + 1 : ℕ) : ℝ) * p ^ (n + 1) =
          T (n + 1) p * p ^ (n + 1) / ((n + 1 : ℕ) : ℝ) by ring,
        show (1 - κ) / 2 * (1 / ((n + 1 : ℕ) : ℝ)) = (1 - κ) / 2 / ((n + 1 : ℕ) : ℝ) by ring]
      exact div_le_div_of_nonneg_right this (by positivity)
    have hκne : 1 - κ ≠ 0 := by linarith
    have h2 : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) :=
      (hharm.mul_left (2 / (1 - κ))).congr fun n => by field_simp
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h2)

end RHTower
