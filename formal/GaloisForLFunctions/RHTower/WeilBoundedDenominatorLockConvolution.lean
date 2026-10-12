import GaloisForLFunctions.RHTower.WeilRationalCuspLockSpectrum

/-!
# Bounded-denominator locks: the periodic convolution

Let `G` be a Herglotz producer for the weights `lam`, with Dirichlet coefficients
`a = exp⋆(lam/log)`.  Suppose that on the lower critical line

`G(1 − s) = N^{s−½} D(s) G(s)`,   `D(s) = Σ_k P(k) k^{−(s−½)}`,   `Σ |P(k)| < ∞`.

On the line `s = ½ − iy` the lock is an almost-periodic function with frequencies `log(k/N)`, a
two-sided rational spectrum whose denominators divide `N`.

**Theorem** (`sqrtConv_periodic`).  The sequence `h(j) = √j Σ_{nm = j} a(n) n^{−1/2} P(m)` is
`N`-periodic on the positive integers.

**Theorem** (`LSeries_sqrtConv`).  For `Re s > 1`, `Σ_j h(j) j^{−s} = F(s) D(s)` with
`F(s) = Σ_n a(n) n^{−s}`.

**Proof.**  The twisted radial limit at the real height `x = j/N` is
`√x Σ_n a(n) n^{−1/2} R(x/n)` (`tendsto_far_real_height`), where `R(k/N) = P(k)` is the lock
coefficient at the frequency `k/N`.  Only the divisors `n | j` contribute, and the value is
`N^{−1/2} h(j)`.  The radial limits at the heights `x` and `x + 1` agree
(`tendsto_far_translation`), hence `h(j + N) = h(j)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral

noncomputable section

/-! ### The lock factor as an exponential sum -/

/-- The frequencies `(k + 1)/N` of a lock with denominators dividing `N`. -/
def denFreq (N : ℕ) (k : ℕ) : ℝ := ((k : ℝ) + 1) / N

theorem denFreq_pos {N : ℕ} (hN : 0 < N) (k : ℕ) : 0 < denFreq N k :=
  div_pos (by positivity) (Nat.cast_pos.mpr hN)

theorem denFreq_cpow {N : ℕ} (hN : 0 < N) (k : ℕ) (z : ℂ) :
    ((denFreq N k : ℝ) : ℂ) ^ (-z) = (N : ℂ) ^ z * (((k + 1 : ℕ) : ℂ) ^ z)⁻¹ := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq := denFreq_pos hN k
  have h0 : ((denFreq N k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hlN : Complex.log (N : ℂ) = ((Real.log N : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_log hNr.le]
  have hlk : Complex.log ((k + 1 : ℕ) : ℂ) = ((Real.log ((k : ℝ) + 1) : ℝ) : ℂ) := by
    rw [show ((k + 1 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_log hk.le]
  rw [cpow_def_of_ne_zero h0, cpow_def_of_ne_zero hN0, cpow_def_of_ne_zero hk0,
    ← Complex.exp_neg, ← Complex.exp_add, ← ofReal_log hq.le, denFreq,
    Real.log_div hk.ne' hNr.ne', hlN, hlk]
  congr 1; push_cast; ring

/-- On the strip `½ ≤ Re s ≤ 3/2` the lock factor `N^{s−½} D(s)` is the exponential sum with
frequencies `(k + 1)/N` and coefficients `P(k + 1)`. -/
theorem apLock_denFreq {N : ℕ} (hN : 0 < N) {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {s : ℂ}
    (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    apLock (fun k => P (k + 1)) (denFreq N) s = (N : ℂ) ^ (s - 1 / 2) * LSeries P (s - 1 / 2) := by
  rw [apLock_of_mem _ _ h1 h2, LSeries]
  have hz : 0 ≤ (s - 1 / 2).re := by rw [Complex.sub_re]; norm_num; linarith
  rw [(lseriesSummable_of_nonneg hP hz).tsum_eq_zero_add, LSeries.term_zero, zero_add,
    ← tsum_mul_left]
  congr 1; funext k
  rw [denFreq_cpow hN, LSeries.term_of_ne_zero (Nat.succ_ne_zero k), div_eq_mul_inv]
  push_cast; ring

theorem summable_denFreq_weight {N : ℕ} (hN : 0 < N) {P : ℕ → ℂ}
    (hP : Summable fun k => ‖P k‖) :
    Summable fun k => ‖P (k + 1)‖ * max 1 (denFreq N k)⁻¹ := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (((summable_nat_add_iff 1).mpr hP).mul_left (N : ℝ))
  have hle : max 1 (denFreq N k)⁻¹ ≤ N := by
    refine max_le hNr ?_
    rw [denFreq, inv_div, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  calc ‖P (k + 1)‖ * max 1 (denFreq N k)⁻¹ ≤ ‖P (k + 1)‖ * N :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = N * ‖P (k + 1)‖ := by ring

/-! ### The resonance sums at the heights `j/N` -/

/-- At the height `j/N` the frequency `(k + 1)/N` resonates with `n` iff `n (k + 1) = j`. -/
theorem ratSpec_denFreq {N : ℕ} (hN : 0 < N) (P : ℕ → ℂ) {j n : ℕ} (hj : 0 < j) (hn : 0 < n) :
    ratSpec 0 (fun k => P (k + 1)) (denFreq N) ((j : ℝ) / N) n =
      if n ∣ j then (n : ℂ) * P (j / n) else 0 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hiff : ∀ k : ℕ, (n : ℝ) * (denFreq N k / ((j : ℝ) / N)) = ((1 : ℕ) : ℝ) ↔
      n * (k + 1) = j := by
    intro k
    have e : (n : ℝ) * (denFreq N k / ((j : ℝ) / N)) = (n : ℝ) * ((k : ℝ) + 1) / j := by
      rw [denFreq]; field_simp
    rw [e, Nat.cast_one, div_eq_one_iff_eq hjr.ne']
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  unfold ratSpec
  simp only [Pi.zero_apply, mul_zero, ite_self, tsum_zero, zero_add]
  by_cases hd : n ∣ j
  · obtain ⟨m, rfl⟩ := hd
    have hm : 0 < m := Nat.pos_of_mul_pos_left hj
    rw [if_pos (dvd_mul_right n m), Nat.mul_div_cancel_left m hn]
    rw [tsum_eq_single (m - 1)]
    · rw [if_pos ((hiff (m - 1)).mpr (by rw [Nat.sub_add_cancel hm])), Nat.sub_add_cancel hm]
    · intro k hk
      rw [if_neg]
      rw [hiff]
      intro h
      have : k + 1 = m := Nat.eq_of_mul_eq_mul_left hn h
      omega
  · rw [if_neg hd]
    refine (tsum_congr fun k => if_neg fun h => hd ⟨k + 1, ((hiff k).mp h).symm⟩).trans tsum_zero

/-- The twisted radial limit at the height `j/N`, as a Dirichlet convolution. -/
theorem tsum_ratSpec_denFreq (a : ℕ → ℂ) {N : ℕ} (hN : 0 < N) (P : ℕ → ℂ) {j : ℕ} (hj : 0 < j) :
    ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
        ratSpec 0 (fun k => P (k + 1)) (denFreq N) ((j : ℝ) / N) n =
      LSeries.convolution (halfCoeff a) P j := by
  rw [tsum_eq_sum (s := j.divisors)]
  · rw [LSeries.convolution_def]
    show _ = ∑ p ∈ j.divisorsAntidiagonal, halfCoeff a p.1 * P p.2
    rw [Nat.sum_divisorsAntidiagonal (fun i k => halfCoeff a i * P k)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hd : n ∣ j := (Nat.mem_divisors.mp hn).1
    have hn0 : 0 < n := Nat.pos_of_mem_divisors hn
    rw [ratSpec_denFreq hN P hj hn0, if_pos hd, ← mul_assoc, term_three_halves_mul a hn0.ne']
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have : ¬ n ∣ j := fun hd => hn (Nat.mem_divisors.mpr ⟨hd, hj.ne'⟩)
    rw [ratSpec_denFreq hN P hj hn0, if_neg this, mul_zero]

/-! ### The period law -/

/-- The weighted convolution `h(j) = √j Σ_{nm = j} a(n) n^{−1/2} P(m)`. -/
def sqrtConv (a P : ℕ → ℂ) (j : ℕ) : ℂ :=
  ((Real.sqrt j : ℝ) : ℂ) * LSeries.convolution (halfCoeff a) P j

/-- **The period law of a bounded-denominator lock.**  `h(j + N) = h(j)` for `j ≥ 1`. -/
theorem sqrtConv_periodic {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {N : ℕ} (hN : 0 < N) {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (N : ℂ) ^ (lineS τ - 1 / 2) * LSeries P (lineS τ - 1 / 2) * G (lineS τ))
    {j : ℕ} (hj : 0 < j) :
    sqrtConv (dirichletExp (lamLog lam)) P (j + N) = sqrtConv (dirichletExp (lamLog lam)) P j := by
  set a := dirichletExp (lamLog lam) with ha
  have hP0 : Summable fun k => ‖(0 : ℕ → ℂ) k‖ := by simp
  have hu := denFreq_pos hN
  have hc := summable_denFreq_weight hN hP
  have hlockV : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (dirLock 0 (lineS τ) + apLock (fun k => P (k + 1)) (denFreq N) (lineS τ)) * G (lineS τ) := by
    intro τ hτ
    have h1 : 1 / 2 ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have h2 : (lineS τ).re ≤ 3 / 2 := by rw [lineS_re]; norm_num
    rw [hlock τ hτ, apLock_denFreq hN hP h1 h2, dirLock, LSeries_zero]
    simp
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set x : ℝ := (j : ℝ) / N with hx
  have hx0 : 0 < x := div_pos (Nat.cast_pos.mpr hj) hNr
  have hx1 : x + 1 = (((j + N : ℕ) : ℝ)) / N := by rw [hx]; push_cast; field_simp
  have h1 := tendsto_far_real_height hsl hΦre hid hGc hGd hG2 hP0 hu hc hlockV
    (x := x + 1) (by linarith)
  have h0 := tendsto_far_real_height hsl hΦre hid hGc hGd hG2 hP0 hu hc hlockV hx0
  have ht := tendsto_far_translation hsl hΦre hid hGc hGd hG2 hx0
  have hper : ((Real.sqrt (x + 1) : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
        ratSpec 0 (fun k => P (k + 1)) (denFreq N) (x + 1) n =
      ((Real.sqrt x : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
        ratSpec 0 (fun k => P (k + 1)) (denFreq N) x n := by
    refine sub_eq_zero.mp (tendsto_nhds_unique (h1.sub h0) (ht.congr fun ε => ?_))
    rw [mul_sub]
  rw [hx1, tsum_ratSpec_denFreq a hN P (by omega), hx,
    tsum_ratSpec_denFreq a hN P hj] at hper
  have hsq : ∀ m : ℕ, Real.sqrt ((m : ℝ) / N) = Real.sqrt m / Real.sqrt N := fun m =>
    Real.sqrt_div' _ hNr.le
  rw [hsq, hsq] at hper
  have hN0 : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hNr).ne'
  unfold sqrtConv
  push_cast at hper ⊢
  field_simp at hper
  exact hper

/-! ### The Dirichlet series of the convolution -/

theorem natCast_cpow_half_eq_sqrt (n : ℕ) : (n : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt n : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow (Nat.cast_nonneg n)]
  push_cast; ring_nf

theorem natCast_cpow_eq_sub_half_mul (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    (n : ℂ) ^ s = (n : ℂ) ^ (s - 1 / 2) * ((Real.sqrt n : ℝ) : ℂ) := by
  rw [← natCast_cpow_half_eq_sqrt, ← cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  ring_nf

/-- Multiplying the coefficients by `√n` shifts the Dirichlet series by `½`. -/
theorem term_sqrt_mul (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => ((Real.sqrt n : ℝ) : ℂ) * f n) s n = LSeries.term f (s - 1 / 2) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, natCast_cpow_eq_sub_half_mul n hn s]
  have hs : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
  have hc : (n : ℂ) ^ (s - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  field_simp

theorem term_halfCoeff (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (halfCoeff a) (s - 1 / 2) n = LSeries.term a s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, halfCoeff, natCast_cpow_half_eq_sqrt,
    natCast_cpow_eq_sub_half_mul n hn s]
  have hs : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
  have hc : (n : ℂ) ^ (s - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  field_simp

/-- **The Dirichlet series of the convolution.**  `Σ_j h(j) j^{−s} = F(s) D(s)` where `F` and `D`
converge absolutely. -/
theorem LSeries_sqrtConv {a P : ℕ → ℂ} {s : ℂ} (ha : LSeriesSummable a s)
    (hP : LSeriesSummable P (s - 1 / 2)) :
    LSeriesSummable (sqrtConv a P) s ∧
      LSeries (sqrtConv a P) s = LSeries a s * LSeries P (s - 1 / 2) := by
  have hha : LSeriesSummable (halfCoeff a) (s - 1 / 2) :=
    (summable_congr (term_halfCoeff a s)).mpr ha
  have hconv := LSeriesSummable.convolution hha hP
  have heq : ∀ n, LSeries.term (sqrtConv a P) s n =
      LSeries.term (LSeries.convolution (halfCoeff a) P) (s - 1 / 2) n := fun n =>
    term_sqrt_mul _ s n
  refine ⟨?_, ?_⟩
  · exact (summable_congr heq).mpr hconv
  · rw [LSeries, tsum_congr heq, ← LSeries, LSeries_convolution' hha hP]
    congr 1
    rw [LSeries, LSeries]
    exact tsum_congr fun n => term_halfCoeff a s n

end

end AbelianTwist

end RHTower
