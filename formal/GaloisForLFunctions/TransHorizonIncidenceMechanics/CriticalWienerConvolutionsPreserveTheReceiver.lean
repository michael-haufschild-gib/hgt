import GaloisForLFunctions.TransHorizonIncidenceMechanics.DyadicMassesGovernPositiveReceivers
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeHorizonCrossoverScale
import GaloisForLFunctions.RHTower.FloorTransformHarmonicInverse
import GaloisForLFunctions.RHTower.LiouvilleSummatoryRH

/-!
# Critical Wiener convolutions preserve the receiver

For the Dirichlet convolution `(g ⋆ c)(n) = Σ_{q | n} g(q) c(n/q)` the floor sums compose
(`⌊⌊n/q⌋/d⌋ = ⌊n/(qd)⌋`, the dilation `k ↦ qk`), and the receiver prefixes obey the exact
**convolution law**
`A_{g⋆c}(n) = Σ_{q≤n} g(q) A_c(⌊n/q⌋) + m_c A_g(n)`,  mean `m_{g⋆c} = m_g m_c`.
The pronic weight contracts the dilation by `q^{-1/2}`, and the sawtooth `A_{δ_q}(n) = ⌊n/q⌋ − n/q`
has pronic norm at most `√(2/q)`, so
`‖A_{g⋆c}‖ ≤ G (‖A_c‖ + √2 |m_c|)`,  `G = Σ_q |g(q)| q^{-1/2}`.
**Receiver boundedness is preserved by convolution with every kernel of the critical Wiener
algebra** `Σ_q |g(q)| q^{-1/2} < ∞` (Dirichlet series absolutely convergent on `Re s ≥ 1/2`);
the local Euler factors are the finite kernels of this algebra.

Application: `λ(d) = Σ_{j²q = d} μ(q)`, i.e. `λ d^{-ε} = 1_□ d^{-ε} ⋆ μ d^{-ε}`, and the square kernel
has `G = ζ(1+2ε)`. With the bounded receiver of `μ(d)d^{-1/2}` this gives **the Liouville parity
pair at half damping**: `λ(d)d^{-1/2}` has bounded receiver, while the smooth power
`κ d^{-1/2}` — whose Ramanujan coefficients are `|W_λ|`, since `λ` is completely multiplicative of
modulus one — diverges. The parity of `Ω` is the whole difference between the Liouville weight and
the constant weight.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The convolution law -/

theorem weightCenteredPrefix_eq_floorTransform (c : ℕ → ℝ) (m : ℝ) (n : ℕ) :
    weightCenteredPrefix c m n = RHTower.floorTransform c (fun k => (k : ℝ)) n - m * n := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]; rfl

theorem weightCenteredPrefix_zero (c : ℕ → ℝ) (m : ℝ) : weightCenteredPrefix c m 0 = 0 := by
  simp [weightCenteredPrefix]

/-- **The convolution law of receivers.** For any means `m_g`, `m_c`:
`A_{g⋆c}(n) = Σ_{q≤n} g(q) A_c(⌊n/q⌋) + m_c A_g(n)` at mean `m_g m_c`. -/
theorem weightCenteredPrefix_dirichletConv (g c : ℕ → ℝ) (mg mc : ℝ) (n : ℕ) :
    weightCenteredPrefix (RHTower.dirichletConv g c) (mg * mc) n =
      ∑ q ∈ Icc 1 n, g q * weightCenteredPrefix c mc (n / q) +
        mc * weightCenteredPrefix g mg n := by
  simp only [weightCenteredPrefix_eq_floorTransform, ← RHTower.floorTransform_comp]
  simp only [RHTower.floorTransform]
  have h : ∑ q ∈ Icc 1 n, g q * (∑ d ∈ Icc 1 (n / q), c d * ((n / q / d : ℕ) : ℝ) -
      mc * ((n / q : ℕ) : ℝ)) = ∑ q ∈ Icc 1 n, g q * ∑ d ∈ Icc 1 (n / q), c d * ((n / q / d : ℕ) : ℝ) -
      mc * ∑ q ∈ Icc 1 n, g q * ((n / q : ℕ) : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => by ring
  rw [h]
  ring

/-- **The mean law** `m_{g⋆c} = m_g m_c` for absolutely convergent means. -/
theorem hasSum_dirichletConv_div {g c : ℕ → ℝ} {mg mc : ℝ}
    (hg : HasSum (fun q : ℕ => g q / q) mg) (hc : HasSum (fun d : ℕ => c d / d) mc)
    (hg' : Summable (fun q : ℕ => |g q / q|)) (hc' : Summable (fun d : ℕ => |c d / d|)) :
    HasSum (fun n : ℕ => RHTower.dirichletConv g c n / n) (mg * mc) := by
  have hsum : Summable (fun x : ℕ × ℕ => g x.1 / x.1 * (c x.2 / x.2)) :=
    summable_mul_of_summable_norm (f := fun q : ℕ => g q / q) (g := fun d : ℕ => c d / d)
      (by simpa only [Real.norm_eq_abs] using hg') (by simpa only [Real.norm_eq_abs] using hc')
  have hfib := (hg.mul hc hsum).tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  refine hfib.congr_fun fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
        g p.val.1 / p.val.1 * (c p.val.2 / p.val.2) = 0 := by
      rintro ⟨⟨a, b⟩, hp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero] at hp
      rcases hp with rfl | rfl <;> simp
    simp [hzero]
  · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
      Finset.tsum_subtype' n.divisorsAntidiagonal fun p => g p.1 / p.1 * (c p.2 / p.2),
      Nat.sum_divisorsAntidiagonal (fun a b => g a / a * (c b / b)), RHTower.dirichletConv,
      sum_div]
    refine sum_congr rfl fun q hq => ?_
    have hqn := Nat.dvd_of_mem_divisors hq
    have hq0 : (q : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hq; positivity
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [Nat.cast_div hqn hq0]
    field_simp

/-! ### Norm laws -/

theorem pronicNorm_congr {f f' : ℕ → ℝ} {T : ℕ} (h : ∀ n ∈ Icc 1 T, f n = f' n) :
    pronicNorm f T = pronicNorm f' T := by
  unfold pronicNorm
  rw [sum_congr rfl fun n hn => by rw [h n hn]]

theorem pronicNorm_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => ∑ i ∈ s, F i n) T ≤ ∑ i ∈ s, pronicNorm (F i) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pronicNorm]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (pronicNorm_add_le _ _ T).trans (add_le_add le_rfl ih)

/-- The sawtooth `ψ_q(n) = ⌊n/q⌋ − n/q` has pronic norm at most `√2 q^{-1/2}`. -/
theorem pronicNorm_sawtooth_le {q : ℕ} (hq : 1 ≤ q) (T : ℕ) :
    pronicNorm (fun n => ((n / q : ℕ) : ℝ) - (n : ℝ) / q) T ≤
      Real.sqrt 2 * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : Real.sqrt 2 * (q : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt (2 / q) := by
    rw [Real.sqrt_div' 2 hq0.le, Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [hpow]
  unfold pronicNorm
  refine Real.sqrt_le_sqrt ?_
  -- cells below `q` carry `≤ 1/q²`, cells from `q` on carry `≤ 1/(n(n+1))`
  have hcell : ∀ n ∈ Icc 1 T, (((n / q : ℕ) : ℝ) - (n : ℝ) / q) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (if n < q then 1 / (q : ℝ) ^ 2 else 0) + (if q ≤ n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have habs := abs_natDiv_sub_div_le n q hq
    split_ifs with h1 h2 h2
    · omega
    · rw [Nat.div_eq_of_lt h1, Nat.cast_zero, zero_sub, neg_sq, add_zero, div_pow,
        div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [zero_add, div_le_div_iff₀ hden hden]
      have : (((n / q : ℕ) : ℝ) - (n : ℝ) / q) ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) habs
      nlinarith
    · omega
  refine (sum_le_sum hcell).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have h1 : ∑ n ∈ (Icc 1 T).filter (fun n => n < q), 1 / (q : ℝ) ^ 2 ≤ 1 / (q : ℝ) := by
    rw [sum_const, nsmul_eq_mul]
    have hcard : (((Icc 1 T).filter (fun n => n < q)).card : ℝ) ≤ q := by
      have : (Icc 1 T).filter (fun n => n < q) ⊆ range q := fun n hn => by
        simp only [mem_filter] at hn; exact mem_range.mpr hn.2
      exact_mod_cast (card_le_card this).trans (card_range q).le
    calc (((Icc 1 T).filter (fun n => n < q)).card : ℝ) * (1 / (q : ℝ) ^ 2) ≤
          (q : ℝ) * (1 / (q : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / (q : ℝ) := by field_simp
  have h2 : ∑ n ∈ (Icc 1 T).filter (fun n => q ≤ n), 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 / (q : ℝ) := by
    rcases le_or_gt q T with hqT | hTq
    · have hset : (Icc 1 T).filter (fun n => q ≤ n) = Icc q T := by
        ext n; simp only [mem_filter, mem_Icc]; omega
      have htel : ∀ M, q ≤ M → ∑ n ∈ Icc q M, 1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (q : ℝ) - 1 / ((M : ℝ) + 1) := by
        intro M hM
        induction M, hM using Nat.le_induction with
        | base =>
          rw [Icc_self, sum_singleton]; field_simp; ring
        | succ M hqM ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]
          push_cast; field_simp; ring
      rw [hset, htel T hqT]
      have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
      linarith
    · have hset : (Icc 1 T).filter (fun n => q ≤ n) = ∅ := by
        ext n; simp only [mem_filter, mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hset, sum_empty]; positivity
  calc _ ≤ 1 / (q : ℝ) + 1 / (q : ℝ) := add_le_add h1 h2
    _ = 2 / (q : ℝ) := by ring

/-! ### The critical Wiener algebra -/

/-- The critical Wiener algebra: `Σ_q |g(q)| q^{-1/2} < ∞`. -/
def CriticalWiener (g : ℕ → ℝ) : Prop := Summable (fun q : ℕ => |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)))

theorem abs_div_le_critical (g : ℕ → ℝ) (q : ℕ) :
    |g q / q| ≤ |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq0 : (0 : ℝ) < q := by linarith
    rw [abs_div, abs_of_pos hq0, div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)) (abs_nonneg _)

theorem CriticalWiener.summable_abs_div {g : ℕ → ℝ} (hg : CriticalWiener g) :
    Summable (fun q : ℕ => |g q / q|) :=
  hg.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_div_le_critical g)

/-- **The sawtooth expansion of a critical kernel.** For `g` in the critical Wiener algebra,
`‖A_g‖ ≤ (√2 + 1) Σ_q |g(q)| q^{-1/2}` at every cutoff. -/
theorem pronicNorm_weightCenteredPrefix_le_critical {g : ℕ → ℝ} (hg : CriticalWiener g) (T : ℕ) :
    pronicNorm (weightCenteredPrefix g (∑' q : ℕ, g q / q)) T ≤
      (Real.sqrt 2 + 1) * ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hW : Summable (fun q : ℕ => |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) := hg
  set G := ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  set ψ : ℕ → ℕ → ℝ := fun q n => ((n / q : ℕ) : ℝ) - (n : ℝ) / q
  have hs : Summable (fun q : ℕ => g q / q) := hg.summable_abs_div.of_abs
  set τ := ∑ q ∈ Icc 1 T, g q / q - ∑' q : ℕ, g q / q
  -- the representation on the cutoff
  have hrep : ∀ n ∈ Icc 1 T, weightCenteredPrefix g (∑' q : ℕ, g q / q) n =
      ∑ q ∈ Icc 1 T, g q * ψ q n + (n : ℝ) * τ := by
    intro n hn
    have hnT := (mem_Icc.mp hn).2
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
    have hext : ∑ q ∈ Icc 1 n, g q * ((n / q : ℕ) : ℝ) = ∑ q ∈ Icc 1 T, g q * ((n / q : ℕ) : ℝ) :=
      sum_subset (Icc_subset_Icc le_rfl hnT) fun q hq hqn => by
        have : n < q := by simp only [mem_Icc] at hq hqn; omega
        rw [Nat.div_eq_of_lt this, Nat.cast_zero, mul_zero]
    rw [hext]
    simp only [ψ, τ, mul_sub, sum_sub_distrib]
    have : ∀ q ∈ Icc 1 T, g q * ((n : ℝ) / q) = (n : ℝ) * (g q / q) := fun q _ => by ring
    rw [sum_congr rfl this, ← mul_sum]
    ring
  rw [pronicNorm_congr hrep]
  -- the tail `τ` of the mean
  have hG0 : ∀ q : ℕ, 0 ≤ |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hτ : |τ| * Real.sqrt T ≤ G := by
    have hsplit := hs.sum_add_tsum_nat_add (T + 1)
    have hr : range (T + 1) = insert 0 (Icc 1 T) := by
      ext d; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hr, sum_insert (by simp), Nat.cast_zero, div_zero, zero_add] at hsplit
    have hτeq : τ = -∑' k : ℕ, g (k + (T + 1)) / ((k + (T + 1) : ℕ) : ℝ) := by
      simp only [τ]; rw [← hsplit]; ring
    have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hbound : ∀ k : ℕ, ‖g (k + (T + 1)) / ((k + (T + 1) : ℕ) : ℝ)‖ ≤
        ((T : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
          (|g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
      intro k
      have hq : (0 : ℝ) < ((k + (T + 1) : ℕ) : ℝ) := by positivity
      have hqT : (T : ℝ) + 1 ≤ ((k + (T + 1) : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hq]
      have hsplitq : ((k + (T + 1) : ℕ) : ℝ)⁻¹ = ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hq]; norm_num [Real.rpow_neg_one]
      have hmono : ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ((T : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hT1 hqT (by norm_num)
      rw [div_eq_mul_inv, hsplitq]
      have h0 : 0 ≤ |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := hG0 _
      nlinarith [mul_le_mul_of_nonneg_left hmono h0]
    have hsumtail : Summable (fun k : ℕ => |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) :=
      (summable_nat_add_iff (f := fun q : ℕ => |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) (T + 1)).mpr hW
    have htail_le : ∑' k : ℕ, |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G := by
      have h := hW.sum_add_tsum_nat_add (T + 1)
      have h0 : 0 ≤ ∑ q ∈ range (T + 1), |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
        sum_nonneg fun q _ => hG0 q
      simp only [G]; linarith
    have habs : |τ| ≤ ((T : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        ∑' k : ℕ, |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [hτeq, abs_neg, ← tsum_mul_left]
      exact tsum_of_norm_bounded (hsumtail.mul_left _).hasSum hbound
    have hsq : Real.sqrt T * ((T : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hT1.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
        div_le_one (Real.sqrt_pos.mpr hT1)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hGt : 0 ≤ ∑' k : ℕ, |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
      tsum_nonneg fun k => hG0 _
    calc |τ| * Real.sqrt T ≤ ((T : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
          (∑' k : ℕ, |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt T :=
          mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg _)
      _ = (Real.sqrt T * ((T : ℝ) + 1) ^ (-(1 / 2 : ℝ))) *
          ∑' k : ℕ, |g (k + (T + 1))| * ((k + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ 1 * G := mul_le_mul hsq htail_le hGt zero_le_one
      _ = G := one_mul G
  -- the identity profile has pronic norm at most `√T`
  have hid : pronicNorm (fun n => (n : ℝ)) T ≤ Real.sqrt T := by
    unfold pronicNorm
    refine Real.sqrt_le_sqrt ?_
    calc ∑ n ∈ Icc 1 T, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ ∑ _n ∈ Icc 1 T, (1 : ℝ) :=
          sum_le_sum fun n hn => by
            have : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
            rw [div_le_one (by positivity)]; nlinarith
      _ = T := by simp
  -- assemble
  have hfin : ∑ q ∈ Icc 1 T, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G :=
    hW.sum_le_tsum _ fun q _ => hG0 q
  calc pronicNorm (fun n => ∑ q ∈ Icc 1 T, g q * ψ q n + (n : ℝ) * τ) T ≤
        pronicNorm (fun n => ∑ q ∈ Icc 1 T, g q * ψ q n) T + pronicNorm (fun n => (n : ℝ) * τ) T :=
        pronicNorm_add_le _ _ T
    _ ≤ ∑ q ∈ Icc 1 T, |g q| * (Real.sqrt 2 * (q : ℝ) ^ (-(1 / 2 : ℝ))) + |τ| * Real.sqrt T := by
        refine add_le_add ((pronicNorm_sum_le _ _ T).trans (sum_le_sum fun q hq => ?_)) ?_
        · rw [pronicNorm_smul]
          exact mul_le_mul_of_nonneg_left (pronicNorm_sawtooth_le (mem_Icc.mp hq).1 T)
            (abs_nonneg _)
        · rw [show (fun n : ℕ => (n : ℝ) * τ) = fun n : ℕ => τ * (n : ℝ) from funext fun n => mul_comm _ _,
            pronicNorm_smul]
          exact mul_le_mul_of_nonneg_left hid (abs_nonneg _)
    _ ≤ Real.sqrt 2 * G + G := by
        refine add_le_add ?_ hτ
        rw [show ∑ q ∈ Icc 1 T, |g q| * (Real.sqrt 2 * (q : ℝ) ^ (-(1 / 2 : ℝ))) =
          Real.sqrt 2 * ∑ q ∈ Icc 1 T, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) by
            rw [mul_sum]; exact sum_congr rfl fun q _ => by ring]
        exact mul_le_mul_of_nonneg_left hfin (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- **The convolution bound.** `‖A_{g⋆c}‖ ≤ G ‖A_c‖ + (√2 + 1) G |m_c|` at every cutoff. -/
theorem pronicNorm_dirichletConv_le {g c : ℕ → ℝ} (hg : CriticalWiener g) (mc : ℝ) (T : ℕ) :
    pronicNorm (weightCenteredPrefix (RHTower.dirichletConv g c) ((∑' q : ℕ, g q / q) * mc)) T ≤
      (∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * pronicNorm (weightCenteredPrefix c mc) T +
        |mc| * ((Real.sqrt 2 + 1) * ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hW : Summable (fun q : ℕ => |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) := hg
  set mg := ∑' q : ℕ, g q / q
  set G := ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  have hrep : ∀ n ∈ Icc 1 T, weightCenteredPrefix (RHTower.dirichletConv g c) (mg * mc) n =
      ∑ q ∈ Icc 1 T, g q * weightCenteredPrefix c mc (n / q) + mc * weightCenteredPrefix g mg n := by
    intro n hn
    rw [weightCenteredPrefix_dirichletConv]
    congr 1
    exact sum_subset (Icc_subset_Icc le_rfl (mem_Icc.mp hn).2) fun q hq hqn => by
      have : n < q := by simp only [mem_Icc] at hq hqn; omega
      rw [Nat.div_eq_of_lt this, weightCenteredPrefix_zero, mul_zero]
  rw [pronicNorm_congr hrep]
  have hG0 : ∀ q : ℕ, 0 ≤ |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hfin : ∑ q ∈ Icc 1 T, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G :=
    hW.sum_le_tsum _ fun q _ => hG0 q
  have hAc := pronicNorm_nonneg (weightCenteredPrefix c mc) T
  calc _ ≤ pronicNorm (fun n => ∑ q ∈ Icc 1 T, g q * weightCenteredPrefix c mc (n / q)) T +
        pronicNorm (fun n => mc * weightCenteredPrefix g mg n) T := pronicNorm_add_le _ _ T
    _ ≤ (∑ q ∈ Icc 1 T, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * pronicNorm (weightCenteredPrefix c mc) T +
        |mc| * ((Real.sqrt 2 + 1) * G) := by
        refine add_le_add ((pronicNorm_sum_le _ _ T).trans ?_) ?_
        · rw [sum_mul]
          refine sum_le_sum fun q hq => ?_
          rw [pronicNorm_smul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (pronicNorm_dilate_le _ (weightCenteredPrefix_zero c mc)
            (mem_Icc.mp hq).1 T) (abs_nonneg _)
        · rw [pronicNorm_smul]
          exact mul_le_mul_of_nonneg_left (pronicNorm_weightCenteredPrefix_le_critical hg T)
            (abs_nonneg _)
    _ ≤ _ := by gcongr

/-- **Critical Wiener convolutions preserve bounded receivers.** -/
theorem receiverBounded_dirichletConv {g c : ℕ → ℝ} (hg : CriticalWiener g)
    (hc : Summable (fun d : ℕ => |c d / d|)) (hcB : ReceiverBounded c) :
    ReceiverBounded (RHTower.dirichletConv g c) := by
  obtain ⟨E, hE⟩ := hcB
  set mg := ∑' q : ℕ, g q / q
  set mc := ∑' d : ℕ, c d / d
  set G := ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  have hmean : ∑' n : ℕ, RHTower.dirichletConv g c n / n = mg * mc :=
    (hasSum_dirichletConv_div hg.summable_abs_div.of_abs.hasSum hc.of_abs.hasSum
      hg.summable_abs_div hc).tsum_eq
  have hE0 : 0 ≤ E := (by simp [weightPronicEnergy] : 0 ≤ weightPronicEnergy c mc 0).trans (hE 0)
  refine ⟨(G * Real.sqrt E + |mc| * ((Real.sqrt 2 + 1) * G)) ^ 2, fun T => ?_⟩
  have hG : 0 ≤ G := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hAc : pronicNorm (weightCenteredPrefix c mc) T ≤ Real.sqrt E := by
    rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm]
    exact Real.sqrt_le_sqrt (hE T)
  rw [hmean, weightPronicEnergy_eq_sq_pronicNorm]
  have h := pronicNorm_dirichletConv_le (c := c) hg mc T
  have h' : pronicNorm (weightCenteredPrefix (RHTower.dirichletConv g c) (mg * mc)) T ≤
      G * Real.sqrt E + |mc| * ((Real.sqrt 2 + 1) * G) :=
    h.trans (add_le_add (mul_le_mul_of_nonneg_left hAc hG) le_rfl)
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) h' 2

/-! ### The Liouville parity pair -/

theorem liouvilleR_mul (a b : ℕ) :
    RHTower.liouvilleR (a * b) = RHTower.liouvilleR a * RHTower.liouvilleR b := by
  simp [RHTower.liouvilleR, ArithmeticFunction.liouville_apply_mul]

theorem abs_liouvilleR {d : ℕ} (hd : d ≠ 0) : |RHTower.liouvilleR d| = 1 := by
  rw [RHTower.liouvilleR, ArithmeticFunction.liouville_apply hd]
  push_cast
  simp

/-- `λ(d) d^{-ε} = Σ_{q | d} 1_□(q) q^{-ε} · μ(d/q) (d/q)^{-ε}`. -/
theorem dampedLiouville_eq_dirichletConv (ε : ℝ) (n : ℕ) :
    dampedSignWeight RHTower.liouvilleR ε n =
      RHTower.dirichletConv (dampedSignWeight RHTower.squareIndicatorR ε)
        (pmPowerDampedRealWeight ε) n := by
  rw [dampedSignWeight, RHTower.liouvilleR_eq_dirichletConv, RHTower.dirichletConv,
    RHTower.dirichletConv, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hq
  have hq0 : 0 < q := Nat.pos_of_mem_divisors hq
  rw [Nat.mul_div_cancel_left k hq0]
  simp only [dampedSignWeight, pmPowerDampedRealWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), RHTower.moebiusR, moebiusReal]
  ring

/-- The square kernel `1_□(q) q^{-ε}` lies in the critical Wiener algebra, with `G = ζ(1+2ε)`. -/
theorem criticalWiener_dampedSquare {ε : ℝ} (hε : 0 < ε) :
    CriticalWiener (dampedSignWeight RHTower.squareIndicatorR ε) := by
  unfold CriticalWiener
  set f : ℕ → ℝ := fun q =>
    |dampedSignWeight RHTower.squareIndicatorR ε q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  have hinj : Function.Injective (fun j : ℕ => j ^ 2) := Nat.pow_left_injective (by norm_num)
  have hzero : ∀ x ∉ Set.range (fun j : ℕ => j ^ 2), f x = 0 := by
    intro x hx
    have hns : ¬ IsSquare x := by
      rintro ⟨r, rfl⟩; exact hx ⟨r, by ring⟩
    simp [f, dampedSignWeight, RHTower.squareIndicatorR, hns]
  refine (hinj.summable_iff hzero).mp ?_
  refine (Real.summable_nat_rpow.mpr (show -1 - 2 * ε < -1 by linarith)).congr fun j => ?_
  simp only [Function.comp_apply, f, dampedSignWeight, RHTower.squareIndicatorR]
  rw [if_pos ⟨j, sq j⟩, one_mul]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Real.zero_rpow (show -1 - 2 * ε ≠ 0 by linarith),
      Real.zero_rpow (show -ε ≠ 0 by linarith)]
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hcast : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ (2 : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast]; norm_num
    rw [hcast, abs_of_nonneg (by positivity), ← Real.rpow_mul hj0.le, ← Real.rpow_mul hj0.le,
      ← Real.rpow_add hj0]
    congr 1; ring

theorem summable_abs_pmPowerDamped_div {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => |pmPowerDampedRealWeight ε d / d|) := by
  refine (Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  have h := dampedSignWeight_div (s := moebiusReal) hε d
  simp only [dampedSignWeight] at h
  rw [show pmPowerDampedRealWeight ε d = moebiusReal d * (d : ℝ) ^ (-ε) from rfl, h, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have : |moebiusReal d| ≤ 1 := by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) this

/-- The receiver of `μ(d)d^{-1/2}` is bounded. -/
theorem receiverBounded_pmPowerDamped_half : ReceiverBounded (pmPowerDampedRealWeight (1 / 2)) := by
  obtain ⟨B, hB⟩ := RHTower.exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le
    (le_refl (1 / 2 : ℝ))
  refine ⟨B, fun T => ?_⟩
  rw [(hasSum_pmPowerDampedRealWeight_div (by norm_num : (0 : ℝ) < 1 / 2)).tsum_eq,
    weightPronicEnergy_pmPowerDamped]
  exact hB T

/-- **The Liouville receiver is paid by the Möbius receiver** at every damping. -/
theorem receiverBounded_liouville_of_moebius {ε : ℝ} (hε : 0 < ε)
    (h : ReceiverBounded (pmPowerDampedRealWeight ε)) :
    ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) := by
  rw [show dampedSignWeight RHTower.liouvilleR ε = RHTower.dirichletConv
      (dampedSignWeight RHTower.squareIndicatorR ε) (pmPowerDampedRealWeight ε) from
    funext (dampedLiouville_eq_dirichletConv ε)]
  exact receiverBounded_dirichletConv (criticalWiener_dampedSquare hε)
    (summable_abs_pmPowerDamped_div hε) h

/-- The Liouville mean `m_λ = Σ λ(d) d^{-1-ε} = (Σ_j j^{-2-2ε}) ρ_ε > 0`. -/
theorem liouvilleDampedMass_pos {ε : ℝ} (hε : 0 < ε) :
    0 < ∑' d : ℕ, dampedSignWeight RHTower.liouvilleR ε d / d := by
  set g := dampedSignWeight RHTower.squareIndicatorR ε
  have hgW := criticalWiener_dampedSquare hε
  have hg := hgW.summable_abs_div
  have hmean := hasSum_dirichletConv_div hg.of_abs.hasSum (hasSum_pmPowerDampedRealWeight_div hε)
    hg (summable_abs_pmPowerDamped_div hε)
  rw [show dampedSignWeight RHTower.liouvilleR ε = RHTower.dirichletConv g
      (pmPowerDampedRealWeight ε) from funext (dampedLiouville_eq_dirichletConv ε), hmean.tsum_eq]
  have hg1 : 1 ≤ ∑' q : ℕ, g q / q := by
    have h1 : g 1 / ((1 : ℕ) : ℝ) = 1 := by
      simp [g, dampedSignWeight, RHTower.squareIndicatorR]
    have hnn : ∀ q : ℕ, 0 ≤ g q / q := fun q => by
      simp only [g, dampedSignWeight, RHTower.squareIndicatorR]
      split_ifs <;> positivity
    rw [← h1]
    exact hg.of_abs.le_tsum 1 fun q _ => hnn q
  exact mul_pos (by linarith) (RHTower.pmPowerDampedDivisorDensity_re_pos hε)

/-- The constant sign. -/
def unitSign (_d : ℕ) : ℝ := 1

theorem summable_unit_weight {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => dampedSignWeight unitSign ε d / d) := by
  refine (Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).congr fun d => ?_
  rw [dampedSignWeight_div hε, unitSign, mul_one]

theorem unitDampedMass_pos {ε : ℝ} (hε : 0 < ε) :
    0 < ∑' d : ℕ, dampedSignWeight unitSign ε d / d := by
  have h1 : dampedSignWeight unitSign ε 1 / ((1 : ℕ) : ℝ) = 1 := by
    simp [dampedSignWeight, unitSign]
  have := (summable_unit_weight hε).le_tsum 1 fun d _ => by
    rw [dampedSignWeight_div hε, unitSign, mul_one]; positivity
  linarith

/-- The positive twin of the Liouville weight: the smooth power `κ d^{-ε}`, `κ = m_λ/ζ(1+ε)`. -/
def liouvilleTwin (ε : ℝ) (d : ℕ) : ℝ :=
  |∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| /
    (∑' k : ℕ, dampedSignWeight unitSign ε k / k) * dampedSignWeight unitSign ε d

theorem liouvilleTwin_nonneg {ε : ℝ} (hε : 0 < ε) (d : ℕ) : 0 ≤ liouvilleTwin ε d := by
  unfold liouvilleTwin dampedSignWeight unitSign
  have := unitDampedMass_pos hε
  positivity

/-- **Equal amplitudes.** `|W_{twin}(e)| = |W_λ(e)| = |m_λ| e^{-1-ε}`: `λ` is completely
multiplicative of modulus one. -/
theorem abs_weightRamanujanCoeff_liouvilleTwin {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    |weightRamanujanCoeff (liouvilleTwin ε) e| =
      |weightRamanujanCoeff (dampedSignWeight RHTower.liouvilleR ε) e| := by
  set L := ∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k
  set Z := ∑' k : ℕ, dampedSignWeight unitSign ε k / k
  have hZ := (unitDampedMass_pos hε).ne'
  have hW : ∀ s : ℕ → ℝ, (∀ a b, s (a * b) = s a * s b) →
      weightRamanujanCoeff (dampedSignWeight s ε) e =
        dampedSignWeight s ε e / e * ∑' k : ℕ, dampedSignWeight s ε k / k := fun s hs => by
    unfold weightRamanujanCoeff
    simp_rw [dampedSignWeight_mul_div hs e]
    exact tsum_mul_left
  have htwin : weightRamanujanCoeff (liouvilleTwin ε) e =
      |L| / Z * weightRamanujanCoeff (dampedSignWeight unitSign ε) e :=
    weightRamanujanCoeff_smul _ _ e
  rw [htwin, hW unitSign (fun _ _ => by simp [unitSign]), hW RHTower.liouvilleR liouvilleR_mul]
  have hunit : |dampedSignWeight RHTower.liouvilleR ε e / e| = dampedSignWeight unitSign ε e / e := by
    rcases eq_or_ne e 0 with rfl | he
    · simp
    · rw [dampedSignWeight, dampedSignWeight, unitSign, abs_div, abs_mul, abs_liouvilleR he,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _), abs_of_nonneg (Nat.cast_nonneg e)]
  change |(|L| / Z) * (dampedSignWeight unitSign ε e / e * Z)| =
    |dampedSignWeight RHTower.liouvilleR ε e / e * L|
  have hu0 : 0 ≤ dampedSignWeight unitSign ε e / e := by
    unfold dampedSignWeight unitSign; positivity
  have hZ' : Z ≠ 0 := hZ
  rw [abs_mul (dampedSignWeight RHTower.liouvilleR ε e / e), hunit,
    show |L| / Z * (dampedSignWeight unitSign ε e / e * Z) =
      dampedSignWeight unitSign ε e / e * |L| by field_simp,
    abs_mul, abs_of_nonneg hu0, abs_abs]

theorem hasSum_liouvilleTwin_div {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun d : ℕ => liouvilleTwin ε d / d)
      |∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| := by
  have hZ := (unitDampedMass_pos hε).ne'
  have h := (summable_unit_weight hε).hasSum.mul_left
    (|∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| /
      ∑' k : ℕ, dampedSignWeight unitSign ε k / k)
  rw [div_mul_cancel₀ _ hZ] at h
  exact h.congr_fun fun d => by simp only [liouvilleTwin, mul_div_assoc]

/-- The smooth power drifts on `(n, 2n]`. -/
theorem liouvilleTwin_drift_ge {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    (|∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| /
      (∑' k : ℕ, dampedSignWeight unitSign ε k / k)) / 2 * n * (2 * (n : ℝ)) ^ (-ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), liouvilleTwin ε d / d := by
  set κ := |∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| /
    (∑' k : ℕ, dampedSignWeight unitSign ε k / k)
  have hκ : 0 ≤ κ := div_nonneg (abs_nonneg _) (unitDampedMass_pos hε).le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hterm : ∀ d ∈ Ioc n (2 * n), κ * (2 * (n : ℝ)) ^ (-ε) / (2 * n) ≤ liouvilleTwin ε d / d := by
    intro d hd
    have hd := mem_Ioc.mp hd
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
      exact_mod_cast this
    have hdle : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    have htw : liouvilleTwin ε d / d = κ * (d : ℝ) ^ (-(1 + ε)) := by
      rw [liouvilleTwin, mul_div_assoc, dampedSignWeight_div hε, unitSign, mul_one]
    rw [htw, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hκ
    rw [← Real.rpow_sub_one h2n.ne', show -ε - 1 = -(1 + ε) by ring]
    exact Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ioc, show 2 * n - n = n by omega, nsmul_eq_mul] at hsum
  have : (n : ℝ) * (κ * (2 * (n : ℝ)) ^ (-ε) / (2 * n)) = κ / 2 * (2 * (n : ℝ)) ^ (-ε) := by
    field_simp
  rw [this] at hsum
  calc κ / 2 * n * (2 * (n : ℝ)) ^ (-ε) = (n : ℝ) * (κ / 2 * (2 * (n : ℝ)) ^ (-ε)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hn0.le

/-- **The Liouville parity pair.** For `0 < ε ≤ 1/2`, whenever `μ(d)d^{-ε}` has bounded receiver,
`λ(d)d^{-ε}` and the smooth power `κ d^{-ε}` have equal Ramanujan amplitudes, the first has bounded
and the second divergent receiver. -/
theorem liouville_parityPair_of_moebius {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (h : ReceiverBounded (pmPowerDampedRealWeight ε)) :
    (∀ e : ℕ, |weightRamanujanCoeff (liouvilleTwin ε) e| =
        |weightRamanujanCoeff (dampedSignWeight RHTower.liouvilleR ε) e|) ∧
    (∀ d : ℕ, 0 ≤ liouvilleTwin ε d) ∧
    ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) ∧
    Tendsto (fun T => weightPronicEnergy (liouvilleTwin ε)
      (∑' d : ℕ, liouvilleTwin ε d / d) T) atTop atTop := by
  refine ⟨abs_weightRamanujanCoeff_liouvilleTwin hε, liouvilleTwin_nonneg hε,
    receiverBounded_liouville_of_moebius hε h, ?_⟩
  rw [(hasSum_liouvilleTwin_div hε).tsum_eq]
  have hL := liouvilleDampedMass_pos hε
  exact tendsto_weightPronicEnergy_of_drift (liouvilleTwin_nonneg hε) (hasSum_liouvilleTwin_div hε)
    (by have := unitDampedMass_pos hε; positivity) hε2 1 fun n hn => liouvilleTwin_drift_ge hε hn

/-- **The Liouville parity pair at half damping**, unconditionally: `λ(d)d^{-1/2}` and `κ d^{-1/2}`. -/
theorem liouville_parityPair_at_half_damping :
    (∀ e : ℕ, |weightRamanujanCoeff (liouvilleTwin (1 / 2)) e| =
        |weightRamanujanCoeff (dampedSignWeight RHTower.liouvilleR (1 / 2)) e|) ∧
    (∀ d : ℕ, 0 ≤ liouvilleTwin (1 / 2) d) ∧
    ReceiverBounded (dampedSignWeight RHTower.liouvilleR (1 / 2)) ∧
    Tendsto (fun T => weightPronicEnergy (liouvilleTwin (1 / 2))
      (∑' d : ℕ, liouvilleTwin (1 / 2) d / d) T) atTop atTop :=
  liouville_parityPair_of_moebius (by norm_num) le_rfl receiverBounded_pmPowerDamped_half

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
