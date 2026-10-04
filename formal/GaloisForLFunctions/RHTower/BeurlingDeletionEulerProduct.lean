import GaloisForLFunctions.RHTower.BeurlingDeletionZeta

/-!
# The Dirichlet series of the integers free of deleted primes

Let `S` be a square-root thinning of the primes (`DeletionData`) and `N' = {n : p ∣ n ⇒ p ∉ S}`.

**Counting `S`** (`summable_indicator_rpow`).  `Σ_{p ∈ S} p^{−σ}` converges for every `σ > α`:
`Σ_{p ≤ x} p^{α−1} ≤ x^α/α` (Bernoulli) and the discrepancy at `t = 0` bound the counting
function of `S` by `x^{α+o(1)}`.

**Prime-power remainders.**  With `r(z) = −log(1 − z) − z`,
`rem₁(s) = Σ_{p ∈ S} r(p^{−s})` and `rem₂(s) = Σ_p r(p^{−(s+1−α)})` converge absolutely and are
holomorphic and bounded on every half-plane `Re s ≥ α/2 + δ` (`differentiableOn_rem₁`,
`norm_rem₁_le`, and the same for `rem₂`).

**Euler product** (`LSeries_sFree_eq`).  For `Re s > 1`,

`Σ_{n ∈ N'} n^{−s} = ζ(s) · exp(−corr(s) − rem₁(s) + rem₂(s)) / ζ(s + 1 − α)`.
-/

open Complex Finset Filter Topology
open GaloisForLFunctions.HTGeometry.BoundedPartialSums

noncomputable section

namespace RHTower.BeurlingDeletion

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

/-! ## Counting the deleted primes -/

theorem rpow_sub_one_le {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) {N : ℕ} :
    ((N : ℝ) + 1) ^ (α - 1) ≤ (((N : ℝ) + 1) ^ α - (N : ℝ) ^ α) / α := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / ((N : ℝ) + 1)) (by
    rw [neg_div, neg_le_neg_iff, div_le_one hN1]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
    hα0.le hα
  have hN : (N : ℝ) = ((N : ℝ) + 1) * (1 + -1 / ((N : ℝ) + 1)) := by field_simp; ring
  have hpow : (N : ℝ) ^ α = ((N : ℝ) + 1) ^ α * (1 + -1 / ((N : ℝ) + 1)) ^ α := by
    conv_lhs => rw [hN]
    have h1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hN1]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    rw [Real.mul_rpow hN1.le (by rw [neg_div]; linarith)]
  have hsub : ((N : ℝ) + 1) ^ (α - 1) = ((N : ℝ) + 1) ^ α / ((N : ℝ) + 1) := by
    rw [Real.rpow_sub hN1, Real.rpow_one]
  rw [le_div_iff₀ hα0, hsub, hpow]
  have hA : 0 < ((N : ℝ) + 1) ^ α := Real.rpow_pos_of_pos hN1 α
  have : ((N : ℝ) + 1) ^ α * (1 + -1 / ((N : ℝ) + 1)) ^ α ≤
      ((N : ℝ) + 1) ^ α * (1 + α * (-1 / ((N : ℝ) + 1))) := mul_le_mul_of_nonneg_left hb hA.le
  have e : ((N : ℝ) + 1) ^ α * (1 + α * (-1 / ((N : ℝ) + 1))) =
      ((N : ℝ) + 1) ^ α - ((N : ℝ) + 1) ^ α / ((N : ℝ) + 1) * α := by field_simp; ring
  linarith

theorem sum_rpow_le {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (α - 1) ≤ (N : ℝ) ^ α / α := by
  induction N with
  | zero => simp [Real.zero_rpow hα0.ne']
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := rpow_sub_one_le hα0 hα (N := N)
    have e : ((N : ℝ) + 1) ^ α / α = (N : ℝ) ^ α / α + (((N : ℝ) + 1) ^ α - (N : ℝ) ^ α) / α := by
      ring
    push_cast
    linarith

theorem sum_delWeight_le (hα0 : 0 < α) (hα : α < 1) (n : ℕ) :
    ∑ p ∈ (Finset.Iic n).filter Nat.Prime, delWeight α p ≤ (n : ℝ) ^ α / α := by
  refine le_trans ?_ (sum_rpow_le hα0 hα.le n)
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => delWeight_nonneg α p)
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_Icc.mpr ⟨h2.one_lt.le, Finset.mem_Iic.mp h1⟩

/-- The indicator of `S` as a complex sequence. -/
def ind (n : ℕ) : ℂ := D.S.indicator (fun _ => (1 : ℂ)) n

theorem ind_zero : D.ind 0 = 0 := by
  unfold ind
  rw [Set.indicator_of_notMem fun h => Nat.not_prime_zero (D.prime 0 h)]

theorem partialSum_ind (n : ℕ) :
    partialSum D.ind (n + 1) = ∑ p ∈ (Finset.Iic n).filter Nat.Prime, D.ind p := by
  unfold partialSum
  rw [range_succ_eq_Iic, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rfl
  · unfold ind
    rw [Set.indicator_of_notMem fun h => hp (D.prime p h)]

/-- **The counting function of `S` grows at most like `x^{α + δ}`.** -/
theorem norm_partialSum_ind_le (hα0 : 0 < α) (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (hn : 1 ≤ n) :
    ‖partialSum D.ind (n + 1)‖ ≤ (1 / α + D.C * Real.sqrt (Real.log 2) * (1 + 2 / δ)) *
      (n : ℝ) ^ (α + δ / 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [D.partialSum_ind]
  have h := D.disc (n : ℝ) hn1 0
  rw [Nat.floor_natCast] at h
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one, abs_zero,
    zero_add] at h
  have hsplit : ∑ p ∈ (Finset.Iic n).filter Nat.Prime, D.ind p =
      (∑ p ∈ (Finset.Iic n).filter Nat.Prime,
        (D.S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ))) +
      ((∑ p ∈ (Finset.Iic n).filter Nat.Prime, delWeight α p : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by unfold ind; ring
  rw [hsplit]
  have hw := sum_delWeight_le hα0 hα n
  have hw0 : 0 ≤ ∑ p ∈ (Finset.Iic n).filter Nat.Prime, delWeight α p :=
    Finset.sum_nonneg fun p _ => delWeight_nonneg α p
  have hlog := log_add_one_le hδ hn1
  have hα1 : (n : ℝ) ^ α ≤ (n : ℝ) ^ (α + δ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hα2 : (n : ℝ) ^ (α / 2) * (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) ^ (α + δ / 2) := by
    rw [← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hC := D.C_nonneg
  have hs2 : 0 ≤ Real.sqrt (Real.log 2) := Real.sqrt_nonneg _
  calc _ ≤ ‖∑ p ∈ (Finset.Iic n).filter Nat.Prime,
          (D.S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ))‖ +
        ‖((∑ p ∈ (Finset.Iic n).filter Nat.Prime, delWeight α p : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ D.C * (n : ℝ) ^ (α / 2) * (Real.log n + 1) * Real.sqrt (Real.log 2) + (n : ℝ) ^ α / α := by
        gcongr
        rw [Complex.norm_real, Real.norm_of_nonneg hw0]; exact hw
    _ ≤ D.C * (n : ℝ) ^ (α / 2) * ((1 + 2 / δ) * (n : ℝ) ^ (δ / 2)) * Real.sqrt (Real.log 2) +
          (n : ℝ) ^ (α + δ / 2) / α := by
        gcongr
    _ ≤ _ := by
        have h3 : D.C * (n : ℝ) ^ (α / 2) * ((1 + 2 / δ) * (n : ℝ) ^ (δ / 2)) *
            Real.sqrt (Real.log 2) ≤
            D.C * Real.sqrt (Real.log 2) * (1 + 2 / δ) * (n : ℝ) ^ (α + δ / 2) := by
          have : 0 ≤ D.C * Real.sqrt (Real.log 2) * (1 + 2 / δ) := by positivity
          nlinarith
        have h4 : (n : ℝ) ^ (α + δ / 2) / α = 1 / α * (n : ℝ) ^ (α + δ / 2) := by ring
        nlinarith

/-- **`Σ_{p ∈ S} p^{−σ}` converges for `σ > α`.** -/
theorem summable_indicator_rpow (hα0 : 0 < α) (hα : α < 1) {σ : ℝ} (hσ : α < σ) :
    Summable fun n : ℕ => D.S.indicator (fun n => (n : ℝ) ^ (-σ)) n := by
  classical
  set δ := σ - α with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set K := 1 / α + D.C * Real.sqrt (Real.log 2) * (1 + 2 / δ) with hK
  have hK0 : 0 ≤ K := by have := D.C_nonneg; positivity
  have hb := fun N => norm_sum_mul_powNeg_le_of_growth (a := D.ind) (θ := α + δ / 2) (K := K)
    (by linarith) hK0 D.ind_zero (fun n hn => D.norm_partialSum_ind_le hα0 hα hδ0 n hn)
    (z := (σ : ℂ)) (by rw [Complex.ofReal_re]; linarith) N
  refine summable_of_sum_range_le
    (c := K * (1 + ‖(σ : ℂ)‖ * ∑' i : ℕ, (i : ℝ) ^ (α + δ / 2 - ((σ : ℂ)).re - 1)))
    (fun n => ?_) (fun N => ?_)
  · rw [Set.indicator_apply]; split_ifs <;> positivity
  · have hre : ∀ n, D.S.indicator (fun n => (n : ℝ) ^ (-σ)) n =
        (D.ind n * powNeg (σ : ℂ) n).re := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [D.ind_zero]
        intro h; exact absurd (D.prime 0 h) Nat.not_prime_zero
      · unfold ind powNeg
        rw [Set.indicator_apply, Set.indicator_apply]
        split_ifs
        · rw [one_mul, show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
            ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_re]
        · simp
    simp_rw [hre]
    rw [← Complex.re_sum]
    exact (Complex.re_le_norm _).trans (hb N)

/-! ## The prime-power remainders -/

/-- `r(z) = −log(1 − z) − z`. -/
def logRem (z : ℂ) : ℂ := -Complex.log (1 - z) - z

theorem norm_logRem_le {z : ℂ} (hz : ‖z‖ < 1) : ‖logRem z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := -z) (by rwa [norm_neg])
  rw [norm_neg] at h
  unfold logRem
  rw [show -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) by ring_nf, norm_neg]
  exact h

theorem differentiableAt_logRem_cpow {n : ℕ} (hn : 0 < n) {c : ℂ} {s : ℂ}
    (hs : ‖(n : ℂ) ^ (-(s + c))‖ < 1) :
    DifferentiableAt ℂ (fun s => logRem ((n : ℂ) ^ (-(s + c)))) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (-(s + c))) s :=
    ((differentiableAt_id.add_const c).neg).const_cpow (Or.inl hn0)
  have hslit : 1 - (n : ℂ) ^ (-(s + c)) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have := Complex.re_le_norm ((n : ℂ) ^ (-(s + c)))
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  unfold logRem
  exact ((Complex.differentiableAt_log hslit).comp s (hpow.const_sub 1)).neg.sub hpow

theorem norm_natCast_cpow_neg (n : ℕ) (hn : 0 < n) (z : ℂ) :
    ‖(n : ℂ) ^ (-z)‖ = (n : ℝ) ^ (-z.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

/-- The geometric ratio `2^{−a}` bounds `n^{−a}` for `n ≥ 2`, `a ≥ 0`. -/
theorem rpow_neg_le_two {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (n : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-a) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-b) ≤ (n : ℝ) ^ (-a) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (2 : ℝ) ^ (-a) := Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith)

/-- A remainder term `r(n^{−(s+c)})` is at most `n^{−2σ}/(2(1 − 2^{−a}))` when
`Re(s + c) ≥ σ ≥ a > 0`. -/
theorem norm_logRem_cpow_le {n : ℕ} (hn : 2 ≤ n) {c s : ℂ} {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ)
    (hσ : σ ≤ (s + c).re) :
    ‖logRem ((n : ℂ) ^ (-(s + c)))‖ ≤
      (n : ℝ) ^ (-(2 * σ)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2 := by
  have hn0 : 0 < n := by omega
  have hz : ‖(n : ℂ) ^ (-(s + c))‖ = (n : ℝ) ^ (-(s + c).re) := norm_natCast_cpow_neg n hn0 _
  have hq : (2 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hzq : ‖(n : ℂ) ^ (-(s + c))‖ ≤ (2 : ℝ) ^ (-a) := by
    rw [hz]; exact rpow_neg_le_two hn ha.le (haσ.trans hσ)
  have hzσ : ‖(n : ℂ) ^ (-(s + c))‖ ≤ (n : ℝ) ^ (-σ) := by
    rw [hz]; exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) (by linarith)
  refine (norm_logRem_le (hzq.trans_lt hq)).trans ?_
  have h1 : 0 < 1 - ‖(n : ℂ) ^ (-(s + c))‖ := by linarith
  have h2 : (1 - ‖(n : ℂ) ^ (-(s + c))‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-a))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h3 : ‖(n : ℂ) ^ (-(s + c))‖ ^ 2 ≤ (n : ℝ) ^ (-(2 * σ)) := by
    calc ‖(n : ℂ) ^ (-(s + c))‖ ^ 2 ≤ ((n : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hzσ 2
      _ = (n : ℝ) ^ (-(2 * σ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  have h4 : 0 ≤ (1 - ‖(n : ℂ) ^ (-(s + c))‖)⁻¹ := by positivity
  calc ‖(n : ℂ) ^ (-(s + c))‖ ^ 2 * (1 - ‖(n : ℂ) ^ (-(s + c))‖)⁻¹ / 2
      ≤ (n : ℝ) ^ (-(2 * σ)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2 := by gcongr

/-- `rem₁(s) = Σ_{p ∈ S} r(p^{−s})`. -/
def rem₁ (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, D.S.indicator (fun n : ℕ => logRem ((n : ℂ) ^ (-(s + 0)))) (p : ℕ)

/-- `rem₂(s) = Σ_p r(p^{−(s+1−α)})`. -/
def rem₂ (α : ℝ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, logRem (((p : ℕ) : ℂ) ^ (-(s + ((1 - α : ℝ) : ℂ))))

/-- The majorant of `rem₁` on `Re s ≥ α/2 + δ`. -/
def maj₁ (δ : ℝ) (p : Nat.Primes) : ℝ :=
  D.S.indicator (fun n : ℕ => (n : ℝ) ^ (-(2 * (α / 2 + δ)))) (p : ℕ) *
    (1 - (2 : ℝ) ^ (-(α / 2)))⁻¹ / 2

/-- The majorant of `rem₂` on `Re s ≥ α/2 + δ`. -/
def maj₂ (α δ : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ) ^ (-(2 * (1 - α / 2 + δ))) * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ / 2

theorem summable_maj₁ (hα0 : 0 < α) (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) :
    Summable (D.maj₁ δ) := by
  have h := (D.summable_indicator_rpow hα0 hα (σ := 2 * (α / 2 + δ)) (by linarith)).subtype
    (fun n => n.Prime)
  exact (h.mul_right _).div_const _

theorem summable_maj₂ (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) : Summable (maj₂ α δ) := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * (1 - α / 2 + δ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact ((h.subtype (fun n => n.Prime)).mul_right _).div_const _

theorem norm_rem₁_term_le (hα0 : 0 < α) {δ : ℝ} (hδ : 0 < δ) (p : Nat.Primes) {s : ℂ}
    (hs : α / 2 + δ ≤ s.re) :
    ‖D.S.indicator (fun n : ℕ => logRem ((n : ℂ) ^ (-(s + 0)))) (p : ℕ)‖ ≤ D.maj₁ δ p := by
  classical
  unfold maj₁
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs with h
  · exact norm_logRem_cpow_le p.2.two_le (by linarith) (by linarith) (by simpa using hs)
  · simp

theorem norm_rem₂_term_le (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) (p : Nat.Primes)
    {s : ℂ} (hs : α / 2 + δ ≤ s.re) :
    ‖logRem (((p : ℕ) : ℂ) ^ (-(s + ((1 - α : ℝ) : ℂ))))‖ ≤ maj₂ α δ p :=
  norm_logRem_cpow_le p.2.two_le (by norm_num) (by linarith)
    (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)

theorem differentiableOn_rem₁ (hα0 : 0 < α) (hα : α < 1) :
    DifferentiableOn ℂ D.rem₁ {s | α / 2 < s.re} := by
  classical
  intro s hs
  have hs' : α / 2 < s.re := hs
  set δ := (s.re - α / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set U : Set ℂ := {w | α / 2 + δ < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ D.rem₁ U := by
    refine differentiableOn_tsum_of_summable_norm (D.summable_maj₁ hα0 hα hδ0) (fun p => ?_) hUo
      (fun p w hw => D.norm_rem₁_term_le hα0 hδ0 p (le_of_lt hw))
    intro w hw
    by_cases h : (p : ℕ) ∈ D.S
    · simp only [Set.indicator_of_mem h]
      refine (differentiableAt_logRem_cpow p.2.pos ?_).differentiableWithinAt
      have := norm_natCast_cpow_neg (p : ℕ) p.2.pos (w + 0)
      rw [this]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
        (by simp only [add_zero]; have : α / 2 + δ < w.re := hw; linarith)
    · simp only [Set.indicator_of_notMem h]
      exact differentiableWithinAt_const _
  exact (hd.differentiableAt (hUo.mem_nhds (by show α / 2 + δ < s.re; rw [hδ]; linarith))).differentiableWithinAt

theorem differentiableOn_rem₂ (hα0 : 0 < α) (hα : α < 1) :
    DifferentiableOn ℂ (rem₂ α) {s | α / 2 < s.re} := by
  intro s hs
  have hs' : α / 2 < s.re := hs
  set δ := (s.re - α / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set U : Set ℂ := {w | α / 2 + δ < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (rem₂ α) U := by
    refine differentiableOn_tsum_of_summable_norm (summable_maj₂ hα hδ0) (fun p => ?_) hUo
      (fun p w hw => norm_rem₂_term_le hα hδ0 p (le_of_lt hw))
    intro w hw
    refine (differentiableAt_logRem_cpow p.2.pos ?_).differentiableWithinAt
    rw [norm_natCast_cpow_neg (p : ℕ) p.2.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
      (by simp only [Complex.add_re, Complex.ofReal_re]; have : α / 2 + δ < w.re := hw; linarith)
  exact (hd.differentiableAt (hUo.mem_nhds (by show α / 2 + δ < s.re; rw [hδ]; linarith))).differentiableWithinAt

theorem norm_rem₁_le (hα0 : 0 < α) (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : α / 2 + δ ≤ s.re) : ‖D.rem₁ s‖ ≤ ∑' p, D.maj₁ δ p := by
  have hsum := D.summable_maj₁ hα0 hα hδ
  have hb := fun p => D.norm_rem₁_term_le hα0 hδ p hs
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum)).trans
    (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum) hsum)

theorem norm_rem₂_le (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : α / 2 + δ ≤ s.re) : ‖rem₂ α s‖ ≤ ∑' p, maj₂ α δ p := by
  have hsum := summable_maj₂ hα hδ
  have hb := fun p => norm_rem₂_term_le hα hδ p hs
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum)).trans
    (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum) hsum)

/-! ## The Euler product of the integers free of deleted primes -/

open Classical in
/-- `n` has no prime factor in `S`. -/
def sFree (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∉ D.S

open Classical in
/-- The indicator of the integers free of deleted primes. -/
def sFreeInd (n : ℕ) : ℂ := if D.sFree n then 1 else 0

theorem sFree_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    D.sFree (m * n) ↔ D.sFree m ∧ D.sFree n := by
  unfold sFree
  rw [Nat.primeFactors_mul hm hn]
  simp only [ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

/-- The completely multiplicative summand `1_{N'}(n) n^{−s}`. -/
def sFreeHom (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := D.sFreeInd n * (n : ℂ) ^ (-s)
  map_zero' := by simp [sFreeInd, sFree]
  map_one' := by simp [sFreeInd, sFree]
  map_mul' m n := by
    classical
    by_cases hm : m = 0
    · simp [hm, sFreeInd, sFree]
    by_cases hn : n = 0
    · simp [hn, sFreeInd, sFree]
    simp only [sFreeInd, D.sFree_mul hm hn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    split_ifs <;> simp_all

theorem sFreeHom_apply (s : ℂ) (n : ℕ) : D.sFreeHom s n = D.sFreeInd n * (n : ℂ) ^ (-s) := rfl

theorem sFreeHom_prime (s : ℂ) (p : Nat.Primes) :
    D.sFreeHom s p = (1 - D.ind p) * ((p : ℕ) : ℂ) ^ (-s) := by
  classical
  rw [sFreeHom_apply]
  congr 1
  unfold sFreeInd sFree ind
  rw [p.2.primeFactors, Set.indicator_apply]
  by_cases h : (p : ℕ) ∈ D.S
  · rw [if_neg (by simp [h]), if_pos h]; ring
  · rw [if_pos ⟨p.2.ne_zero, by simpa using h⟩, if_neg h]; ring

theorem summable_norm_sFreeHom {s : ℂ} (hs : 1 < s.re) : Summable fun n => ‖D.sFreeHom s n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith))
  rw [sFreeHom_apply, norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sFreeInd, sFree, Real.zero_rpow (show -s.re ≠ 0 by linarith)]
  · rw [norm_natCast_cpow_neg n hn]
    have : ‖D.sFreeInd n‖ ≤ 1 := by unfold sFreeInd; split_ifs <;> simp
    calc ‖D.sFreeInd n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := one_mul _

theorem LSeries_sFreeInd_eq_tsum (s : ℂ) :
    LSeries D.sFreeInd s = ∑' n, D.sFreeHom s n := by
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sFreeHom_apply, sFreeInd, sFree]
  · rw [LSeries.term_of_ne_zero hn.ne', sFreeHom_apply, div_eq_mul_inv, Complex.cpow_neg]

/-- `|log(1 − z)| ≤ (3/2)|z|` on `|z| ≤ 1/2`. -/
theorem norm_log_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖Complex.log (1 - z)‖ ≤ 3 / 2 * ‖z‖ := by
  have := Complex.norm_log_one_add_half_le_self (z := -z) (by rwa [norm_neg])
  rwa [← sub_eq_add_neg, norm_neg] at this

theorem norm_prime_cpow_le_half (p : Nat.Primes) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_natCast_cpow_neg _ p.2.pos]
  calc ((p : ℕ) : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_neg_le_two p.2.two_le (by norm_num) hs
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem summable_prime_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) :=
  (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)).subtype _

theorem summable_neg_log (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
    ((summable_prime_rpow hs).mul_left (3 / 2))
  rw [norm_neg]
  refine (norm_log_one_sub_le (norm_prime_cpow_le_half p hs.le)).trans ?_
  rw [norm_natCast_cpow_neg _ p.2.pos]

theorem cpow_delWeight (p : ℕ) (hp : 0 < p) (s : ℂ) :
    (delWeight α p : ℂ) * (p : ℂ) ^ (-s) = (p : ℂ) ^ (-(s + ((1 - α : ℝ) : ℂ))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold delWeight
  rw [Complex.ofReal_cpow (Nat.cast_nonneg p), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hp0]
  congr 1
  push_cast
  ring

theorem tsum_primes_eq_LSeries (c : ℕ → ℂ) (hc : ∀ n, ¬ n.Prime → c n = 0) (s : ℂ) :
    ∑' p : Nat.Primes, c p * ((p : ℕ) : ℂ) ^ (-s) = LSeries c s := by
  unfold LSeries
  have hsupp : Function.support (LSeries.term c s) ⊆ {n | n.Prime} := by
    intro n hn
    by_contra h
    exact hn (by simp [LSeries.term_def, hc n h])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun p => ?_
  rw [LSeries.term_of_ne_zero p.2.ne_zero, div_eq_mul_inv, Complex.cpow_neg]

/-- **The Euler product.**  For `Re s > 1`,
`Σ_{n ∈ N'} n^{−s} = ζ(s) exp(−corr(s) − rem₁(s) + rem₂(s)) / ζ(s + 1 − α)`. -/
theorem LSeries_sFree_eq (hα0 : 0 < α) (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries D.sFreeInd s = riemannZeta s *
      Complex.exp (-D.corr s - D.rem₁ s + rem₂ α s) / riemannZeta (s + ((1 - α : ℝ) : ℂ)) := by
  classical
  set w : ℂ := s + ((1 - α : ℝ) : ℂ) with hw
  have hw1 : 1 < w.re := by rw [hw]; simp; linarith
  set A : Nat.Primes → ℂ := fun p => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) with hA
  set B : Nat.Primes → ℂ := fun p => D.ind p * A p with hB
  have hAs : Summable A := (summable_neg_log s hs).of_norm
  have hBs : Summable B := by
    refine Summable.of_norm_bounded (summable_neg_log s hs) fun p => ?_
    rw [hB, norm_mul]
    have : ‖D.ind p‖ ≤ 1 := by unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp
    exact mul_le_of_le_one_left (norm_nonneg _) this
  -- the Euler product of `N'`
  have h1 : LSeries D.sFreeInd s = Complex.exp (∑' p : Nat.Primes, (A p - B p)) := by
    rw [D.LSeries_sFreeInd_eq_tsum s, ← EulerProduct.exp_tsum_primes_log_eq_tsum
      (D.summable_norm_sFreeHom hs)]
    congr 1
    refine tsum_congr fun p => ?_
    rw [sFreeHom_prime, hB, hA]
    simp only
    unfold ind
    rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [hAs.tsum_sub hBs, Complex.exp_sub, riemannZeta_eulerProduct_exp_log hs] at h1
  -- the sum over `S`
  set P : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w) with hP
  set Lw : Nat.Primes → ℂ := fun p => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-w)) with hLw
  have hPs : Summable P := by
    refine Summable.of_norm_bounded (summable_prime_rpow hw1) fun p => ?_
    rw [hP, norm_natCast_cpow_neg _ p.2.pos]
  have hLws : Summable Lw := (summable_neg_log w hw1).of_norm
  have hcoeff : Summable fun p : Nat.Primes => D.coeff p * ((p : ℕ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded ((summable_prime_rpow hs).mul_left 2) fun p => ?_
    rw [norm_mul, norm_natCast_cpow_neg _ p.2.pos]
    exact mul_le_mul_of_nonneg_right (D.norm_coeff_le hα p) (by positivity)
  have hr1 : Summable fun p : Nat.Primes =>
      D.S.indicator (fun n : ℕ => logRem ((n : ℂ) ^ (-(s + 0)))) (p : ℕ) :=
    Summable.of_norm_bounded (D.summable_maj₁ hα0 hα (δ := 1 / 2)
      (by norm_num)) fun p => D.norm_rem₁_term_le hα0 (by norm_num) p (by linarith)
  have hr2 : Summable fun p : Nat.Primes => logRem (((p : ℕ) : ℂ) ^ (-w)) :=
    Summable.of_norm_bounded (summable_maj₂ hα (δ := 1 / 2) (by norm_num)) fun p =>
      norm_rem₂_term_le hα (by norm_num) p (by linarith)
  have hBdec : ∀ p : Nat.Primes, B p = P p + D.coeff p * ((p : ℕ) : ℂ) ^ (-s) +
      D.S.indicator (fun n : ℕ => logRem ((n : ℂ) ^ (-(s + 0)))) (p : ℕ) := by
    intro p
    have hcf : D.coeff p = D.ind p - (delWeight α p : ℂ) := by
      unfold coeff ind; rw [if_pos p.2]
    have hdw := cpow_delWeight (α := α) (p : ℕ) p.2.pos s
    rw [← hw] at hdw
    simp only [hB, hA, hP]
    rw [hcf, ← hdw]
    unfold ind logRem
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp only [add_zero] <;> ring
  have hPdec : ∀ p : Nat.Primes, P p = Lw p - logRem (((p : ℕ) : ℂ) ^ (-w)) := by
    intro p; simp only [hP, hLw, logRem]; ring
  have hsumB : ∑' p, B p = (∑' p, Lw p) - rem₂ α s + D.corr s + D.rem₁ s := by
    rw [tsum_congr hBdec, (hPs.add hcoeff).tsum_add hr1, hPs.tsum_add hcoeff,
      tsum_congr hPdec, hLws.tsum_sub hr2, tsum_primes_eq_LSeries D.coeff
        (fun n hn => by unfold coeff; rw [if_neg hn]) s, ← D.corr_eq_LSeries hα0 hα hs]
    unfold rem₂ rem₁
    rw [← hw]
  rw [hsumB] at h1
  have hzw := riemannZeta_eulerProduct_exp_log hw1
  rw [h1, show (∑' p, Lw p) - rem₂ α s + D.corr s + D.rem₁ s =
      (∑' p, Lw p) + (D.corr s + D.rem₁ s - rem₂ α s) by ring, Complex.exp_add, hzw]
  have hz0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw1.le
  have he : Complex.exp (D.corr s + D.rem₁ s - rem₂ α s) ≠ 0 := Complex.exp_ne_zero _
  rw [show -D.corr s - D.rem₁ s + rem₂ α s = -(D.corr s + D.rem₁ s - rem₂ α s) by ring,
    Complex.exp_neg]
  field_simp

end DeletionData

end RHTower.BeurlingDeletion
