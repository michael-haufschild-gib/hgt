import GaloisForLFunctions.ArithmeticDefectRigidity.ThePoleTraceDefinesALinearCofactorRenormalization
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta

/-!
# The renormalized cofactor acts on power rows by `ζ(s + ε)`

For `0 < ε < 1`, `α = 1 − ε` and a complex exponent `s` with `0 < Re s < α`, the complete
cofactor sum of the power row `n ↦ n^s` has the exact two-pole expansion
`Σ_{j ≤ n} j^{-ε} ⌊n/j⌋^s = ζ(s + ε) n^s + 𝓛_s n^α + O(n^{(Re s − ε)/2})`
(`norm_powerRowCofactorSum_sub_le`), where `𝓛_s = α⁻¹ Σ_m m^s (m^{-α} − (m+1)^{-α})` is the
absolute Mellin pole trace of the row. Hence on power rows the renormalized operator satisfies
`(I + D̃) n^s = ζ(s + ε) n^s` modulo a row of bounded pronic energy: its symbol is `ζ(s + ε) − 1`.

Proof: the Dirichlet hyperbola at `√n` for the convolution of `j^{-ε}` with the power steps
`k^s − (k−1)^s`; the two power poles come from the partial sums of `d^{-(s+ε)}` and of `d^{-ε}`,
the cross terms of order `n^{(1+s−ε)/2}` cancel, and the pole trace appears through Abel summation
of the Mellin cells with a second-order cell estimate.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (cpowPartialSum norm_cpowPartialSum_sub_le partialSumRate partialSumRate_nonneg mellinCell
    sum_Icc_rpow_neg_one_sub_le)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Elementary power estimates -/

/-- `y ↦ y^z` on the positive reals has derivative `z y^{z−1}`. -/
theorem hasDerivAt_ofReal_cpow' (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ z) (z * ((x : ℝ) : ℂ) ^ (z - 1)) x := by
  have h := TransHorizonIncidenceMechanics.hasDerivAt_ofReal_cpow_neg (w := -z) hx
  simp only [neg_neg] at h
  exact h

/-- Mean value bound for powers with `Re z ≤ 1`: `‖b^z − u^z‖ ≤ ‖z‖ a^{Re z − 1}(b − u)`
for `0 < a ≤ u ≤ b`. -/
theorem norm_ofReal_cpow_sub_le {z : ℂ} (hz : z.re ≤ 1) {a u b : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hub : u ≤ b) :
    ‖((b : ℝ) : ℂ) ^ z - ((u : ℝ) : ℂ) ^ z‖ ≤ ‖z‖ * a ^ (z.re - 1) * (b - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le ha hau
  refine norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => ((y : ℝ) : ℂ) ^ z) (f' := fun y => z * ((y : ℝ) : ℂ) ^ (z - 1))
    (fun y hy => (hasDerivAt_ofReal_cpow' z (lt_of_lt_of_le hu0 hy.1)).hasDerivWithinAt)
    (fun y hy => ?_) b ⟨hub, le_rfl⟩
  have hy0 : 0 < y := lt_of_lt_of_le hu0 hy.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [show (z - 1).re = z.re - 1 by simp]
  exact Real.rpow_le_rpow_of_nonpos ha (hau.trans hy.1) (by linarith)

/-! ### The hyperbola identity for a general convolution -/

/-- **Dirichlet hyperbola identity.** With `q = ⌊√n⌋`,
`Σ_{d ≤ n} f(d) G(⌊n/d⌋) = Σ_{d ≤ q} f(d) G(⌊n/d⌋) + Σ_{k ≤ q} g(k)(F(⌊n/k⌋) − F(q))`, where
`F`, `G` are the partial sums of `f`, `g`. -/
theorem sum_mul_partialSum_div_eq_hyperbola (f g : ℕ → ℂ) (n : ℕ) :
    ∑ d ∈ Icc 1 n, f d * ∑ k ∈ Icc 1 (n / d), g k =
      ∑ d ∈ Icc 1 (Nat.sqrt n), f d * ∑ k ∈ Icc 1 (n / d), g k +
        ∑ k ∈ Icc 1 (Nat.sqrt n),
          g k * (∑ d ∈ Icc 1 (n / k), f d - ∑ d ∈ Icc 1 (Nat.sqrt n), f d) := by
  obtain ⟨q, hq⟩ : ∃ q, q = Nat.sqrt n := ⟨_, rfl⟩
  rw [← hq]
  have hqq : q * q ≤ n := by rw [hq]; exact Nat.sqrt_le n
  have hlt : n < (q + 1) * (q + 1) := by rw [hq]; exact Nat.lt_succ_sqrt n
  have hqn : q ≤ n := by rw [hq]; exact Nat.sqrt_le_self n
  have hsplit : Icc 1 n = Icc 1 q ∪ Ioc q n := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 q) (Ioc q n) :=
    disjoint_left.mpr fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm' (s' := fun k => Ioc q (n / k)) (t' := Icc 1 q)]
  · refine sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkq⟩ := mem_Icc.mp hk
    have hqk : q ≤ n / k :=
      (Nat.le_div_iff_mul_le hk1).mpr ((Nat.mul_le_mul_left q hkq).trans hqq)
    have hunion : Icc 1 (n / k) = Icc 1 q ∪ Ioc q (n / k) := by
      ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hunion, sum_union (disjoint_left.mpr fun d h1 h2 => by
      simp only [mem_Icc, mem_Ioc] at h1 h2; omega), add_sub_cancel_left, mul_sum]
    exact sum_congr rfl fun d _ => by ring
  · intro d k
    simp only [mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hqd, hdn⟩, hk1, hkd⟩
      have hd0 : 0 < d := by omega
      have hkd' : k * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp hkd
      refine ⟨⟨hqd, (Nat.le_div_iff_mul_le hk1).mpr (by rw [Nat.mul_comm]; exact hkd')⟩, hk1, ?_⟩
      by_contra hk
      have h1 : (q + 1) * (q + 1) ≤ k * d :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    · rintro ⟨⟨hqd, hdk⟩, hk1, hkq⟩
      have hd0 : 0 < d := by omega
      have hdk' : d * k ≤ n := (Nat.le_div_iff_mul_le hk1).mp hdk
      exact ⟨⟨hqd, hdk.trans (Nat.div_le_self n k)⟩, hk1,
        (Nat.le_div_iff_mul_le hd0).mpr (by rw [Nat.mul_comm]; exact hdk')⟩

/-! ### Power steps and Mellin cells -/

/-- The power step `δ_s(k) = k^s − (k−1)^s`. -/
def powerStep (s : ℂ) (k : ℕ) : ℂ := (((k : ℕ) : ℝ) : ℂ) ^ s - (((k - 1 : ℕ) : ℝ) : ℂ) ^ s

/-- The power steps telescope: `Σ_{k ≤ m} δ_s(k) = m^s` for `s ≠ 0`. -/
theorem sum_powerStep {s : ℂ} (hs : s ≠ 0) (m : ℕ) :
    ∑ k ∈ Icc 1 m, powerStep s k = (((m : ℕ) : ℝ) : ℂ) ^ s := by
  induction m with
  | zero => simp [Complex.zero_cpow hs]
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega), ih, powerStep, Nat.add_sub_cancel]
    ring

/-- The complex Mellin cell `m^{-α} − (m+1)^{-α}`. -/
theorem ofReal_mellinCell (α : ℝ) (m : ℕ) :
    ((mellinCell α m : ℝ) : ℂ) =
      (((m : ℝ)) : ℂ) ^ (-(α : ℂ)) - ((((m : ℝ) + 1 : ℝ)) : ℂ) ^ (-(α : ℂ)) := by
  rw [mellinCell, Complex.ofReal_sub, Complex.ofReal_cpow (Nat.cast_nonneg m),
    Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]

/-- **Abel summation of the Mellin cells.**
`Σ_{k ≤ q} δ_s(k) k^{-α} = Σ_{m ≤ q} m^s (m^{-α} − (m+1)^{-α}) + q^s (q+1)^{-α}`. -/
theorem sum_powerStep_mul_cpow_eq {s : ℂ} (hs : s ≠ 0) (α : ℝ) (q : ℕ) :
    ∑ k ∈ Icc 1 q, powerStep s k * (((k : ℝ)) : ℂ) ^ (-(α : ℂ)) =
      ∑ m ∈ Icc 1 q, (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) +
        (((q : ℝ)) : ℂ) ^ s * ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (-(α : ℂ)) := by
  induction q with
  | zero => simp [Complex.zero_cpow hs]
  | succ q ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih, ofReal_mellinCell,
      powerStep, Nat.add_sub_cancel]
    push_cast
    ring

/-- **Second-order cell estimate.** With `c = α/(α − s)`, the Mellin cell against `m^s` differs
from the telescoping difference `c(m^{s−α} − (m+1)^{s−α})` by at most `α‖s‖ m^{Re s − α − 2}`:
both are `g(m) − g(m+1)` up to `g(x) = m^s x^{-α} − c x^{s−α}`, and
`g'(x) = α x^{-α-1}(x^s − m^s)`. -/
theorem norm_cell_sub_telescope_le {s : ℂ} {α : ℝ} (hα : 0 < α) (hs1 : s.re ≤ 1)
    (hsα : (α : ℂ) - s ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    ‖(((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) - (α : ℂ) / ((α : ℂ) - s) *
        ((((m : ℝ)) : ℂ) ^ (s - α) - ((((m : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α))‖ ≤
      α * ‖s‖ * (m : ℝ) ^ (s.re - α - 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℂ := (α : ℂ) / ((α : ℂ) - s) with hc
  set M : ℂ := (((m : ℝ)) : ℂ) ^ s with hM
  set g : ℝ → ℂ := fun y => M * ((y : ℝ) : ℂ) ^ (-(α : ℂ)) - c * ((y : ℝ) : ℂ) ^ (s - α) with hg
  have hcs : c * (s - α) = -(α : ℂ) := by
    rw [hc]; field_simp; ring
  have hderiv : ∀ y ∈ Set.Icc (m : ℝ) (m + 1), HasDerivWithinAt g
      ((α : ℂ) * ((y : ℝ) : ℂ) ^ (-(α : ℂ) - 1) * (((y : ℝ) : ℂ) ^ s - M))
      (Set.Icc (m : ℝ) (m + 1)) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
    have hyC : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have h1 := (hasDerivAt_ofReal_cpow' (-(α : ℂ)) hy0).const_mul M
    have h2 := (hasDerivAt_ofReal_cpow' (s - α) hy0).const_mul c
    have h := h1.sub h2
    have hpow : ((y : ℝ) : ℂ) ^ (s - α - 1) = ((y : ℝ) : ℂ) ^ s * ((y : ℝ) : ℂ) ^ (-(α : ℂ) - 1) := by
      rw [← Complex.cpow_add _ _ hyC]; ring_nf
    have heq : M * (-(α : ℂ) * ((y : ℝ) : ℂ) ^ (-(α : ℂ) - 1)) -
        c * ((s - α) * ((y : ℝ) : ℂ) ^ (s - α - 1)) =
        (α : ℂ) * ((y : ℝ) : ℂ) ^ (-(α : ℂ) - 1) * (((y : ℝ) : ℂ) ^ s - M) := by
      rw [hpow, ← mul_assoc c, hcs]; ring
    rw [heq] at h
    exact h.hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Ico (m : ℝ) (m + 1),
      ‖(α : ℂ) * ((y : ℝ) : ℂ) ^ (-(α : ℂ) - 1) * (((y : ℝ) : ℂ) ^ s - M)‖ ≤
        α * ‖s‖ * (m : ℝ) ^ (s.re - α - 2) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-(α : ℂ) - 1).re = -α - 1 := by simp
    rw [hre]
    have h1 : y ^ (-α - 1) ≤ (m : ℝ) ^ (-α - 1) :=
      Real.rpow_le_rpow_of_nonpos hm0 hy.1 (by linarith)
    have h2 : ‖((y : ℝ) : ℂ) ^ s - M‖ ≤ ‖s‖ * (m : ℝ) ^ (s.re - 1) * 1 := by
      refine (norm_ofReal_cpow_sub_le hs1 hm0 le_rfl hy.1).trans ?_
      gcongr; linarith [hy.2]
    have hpow : (m : ℝ) ^ (-α - 1) * (m : ℝ) ^ (s.re - 1) = (m : ℝ) ^ (s.re - α - 2) := by
      rw [← Real.rpow_add hm0]; ring_nf
    calc α * y ^ (-α - 1) * ‖((y : ℝ) : ℂ) ^ s - M‖
        ≤ α * (m : ℝ) ^ (-α - 1) * (‖s‖ * (m : ℝ) ^ (s.re - 1) * 1) := by
          gcongr
      _ = α * ‖s‖ * ((m : ℝ) ^ (-α - 1) * (m : ℝ) ^ (s.re - 1)) := by ring
      _ = _ := by rw [hpow]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound ((m : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  have hgm : (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) - c *
      ((((m : ℝ)) : ℂ) ^ (s - α) - ((((m : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α)) =
      -(g ((m : ℝ) + 1) - g m) := by
    have hmC : (((m : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hsplit : (((m : ℝ)) : ℂ) ^ (s - α) = M * (((m : ℝ)) : ℂ) ^ (-(α : ℂ)) := by
      rw [hM, ← Complex.cpow_add _ _ hmC]; ring_nf
    simp only [hg]
    rw [ofReal_mellinCell, hsplit]
    ring
  rw [hgm, norm_neg]
  calc _ ≤ α * ‖s‖ * (m : ℝ) ^ (s.re - α - 2) * ((m : ℝ) + 1 - m) := hmv
    _ = _ := by ring

/-- The complex Mellin pole sum `Σ_m m^s (m^{-α} − (m+1)^{-α})` of the power row. -/
def powerPoleSum (α : ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ)

/-- The power row has an absolutely summable Mellin pole sum when `0 < Re s < α`. -/
theorem summable_powerPoleSum {α : ℝ} (hα : 0 < α) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < α) :
    Summable fun m : ℕ => (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) := by
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  refine Summable.of_norm_bounded (g := fun m : ℕ => α * (m : ℝ) ^ (s.re - α - 1))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left α) fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Complex.ofReal_zero, Complex.zero_cpow hs, zero_mul, norm_zero]
    exact mul_nonneg hα.le (Real.rpow_nonneg le_rfl _)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hm0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (TransHorizonIncidenceMechanics.mellinCell_nonneg hα hm)]
  have hb := (TransHorizonIncidenceMechanics.mellinCell_bounds hα hm).2
  calc (m : ℝ) ^ s.re * mellinCell α m ≤ (m : ℝ) ^ s.re * (α * (m : ℝ) ^ (-α - 1)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hm0.le _)
    _ = α * ((m : ℝ) ^ s.re * (m : ℝ) ^ (-α - 1)) := by ring
    _ = α * (m : ℝ) ^ (s.re - α - 1) := by rw [← Real.rpow_add hm0]; ring_nf

/-- **The pole-sum tail.** For `q ≥ 1`, with `c = α/(α − s)` and `ν = α + 1 − Re s`,
`‖Σ_m m^s cell_m − Σ_{m ≤ q} m^s cell_m − c (q+1)^{s−α}‖ ≤ α‖s‖(1 + 1/ν)(q+1)^{-ν}`. -/
theorem norm_powerPoleSum_sub_partial_le {α : ℝ} (hα : 0 < α) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < α) (hsle : s.re ≤ 1) {q : ℕ} :
    ‖powerPoleSum α s - ∑ m ∈ Icc 1 q, (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) -
        (α : ℂ) / ((α : ℂ) - s) * ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α)‖ ≤
      α * ‖s‖ * ((1 + 1 / (α + 1 - s.re)) * (((q + 1 : ℕ) : ℝ)) ^ (-(α + 1 - s.re))) := by
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hsα : (α : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this; linarith
  set c : ℂ := (α : ℂ) / ((α : ℂ) - s) with hc
  set f : ℕ → ℂ := fun m => (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) with hf
  set ν : ℝ := α + 1 - s.re with hν
  have hν0 : 0 < ν := by rw [hν]; linarith
  set h : ℕ → ℂ := fun Q => ∑ m ∈ Icc 1 Q, f m - ∑ m ∈ Icc 1 q, f m -
    c * (((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α) - ((((Q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α)) with hh
  -- every partial difference is a sum of second-order cell errors
  have hstep : ∀ Q, q ≤ Q → ‖h Q‖ ≤
      α * ‖s‖ * ∑ m ∈ Icc (q + 1) Q, (m : ℝ) ^ (-(1 + ν)) := by
    intro Q hQ
    induction Q, hQ using Nat.le_induction with
    | base =>
      have : Icc (q + 1) q = ∅ := Finset.Icc_eq_empty (by omega)
      simp only [hh, this, sub_self, sum_empty, norm_zero, mul_zero, le_refl]
    | succ Q hqQ ih =>
      have hcell := norm_cell_sub_telescope_le hα hsle hsα (m := Q + 1) (by omega)
      have hdiff : h (Q + 1) = h Q + (f (Q + 1) - c * (((((Q + 1 : ℕ) : ℝ)) : ℂ) ^ (s - α) -
          (((((Q + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α))) := by
        simp only [hh, sum_Icc_succ_top (show 1 ≤ Q + 1 by omega)]
        push_cast; ring
      rw [hdiff, sum_Icc_succ_top (by omega), mul_add]
      have hexp : ((Q + 1 : ℕ) : ℝ) ^ (s.re - α - 2) = ((Q + 1 : ℕ) : ℝ) ^ (-(1 + ν)) := by
        rw [hν]; ring_nf
      refine (norm_add_le _ _).trans (add_le_add ih ?_)
      rw [← hexp]
      exact hcell
  have htail : ∀ Q, q ≤ Q → ‖h Q‖ ≤ α * ‖s‖ * ((1 + 1 / ν) * (((q + 1 : ℕ) : ℝ)) ^ (-ν)) := by
    intro Q hQ
    refine (hstep Q hQ).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact sum_Icc_rpow_neg_one_sub_le hν0 (by omega) Q
  -- pass to the limit `Q → ∞`
  have hsum := (summable_powerPoleSum hα hs0 hs1).hasSum.tendsto_sum_nat
  have hpart : ∀ Q : ℕ, ∑ m ∈ range (Q + 1), f m = ∑ m ∈ Icc 1 Q, f m := by
    intro Q
    induction Q with
    | zero => simp [hf, Complex.zero_cpow hs]
    | succ Q ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]
  have hlimS : Tendsto (fun Q : ℕ => ∑ m ∈ Icc 1 Q, f m) atTop (𝓝 (powerPoleSum α s)) := by
    have := hsum.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun Q => ?_
    simp only [Function.comp]
    exact hpart Q
  have hpow0 : Tendsto (fun Q : ℕ => ((((Q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun Q : ℕ => ((Q : ℝ) + 1) ^ (-(α - s.re))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine hlim.congr fun Q => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1; simp
  have hlimh : Tendsto h atTop (𝓝 (powerPoleSum α s - ∑ m ∈ Icc 1 q, f m -
      c * ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α))) := by
    have h1 := hlimS.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑ m ∈ Icc 1 q, f m) atTop _)
    have h2 := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - α)) atTop _).sub hpow0
    have h3 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop _).mul h2
    have h4 := h1.sub h3
    rw [sub_zero] at h4
    exact h4.congr fun Q => rfl
  exact le_of_tendsto hlimh.norm (eventually_atTop.mpr ⟨q, fun Q hQ => htail Q hQ⟩)

/-! ### The two-pole expansion -/

/-- `q^t ≤ 2^{|t|} r^t` when `q ≤ r ≤ 2q`. -/
theorem rpow_le_two_rpow_abs_mul {q r t : ℝ} (hq : 0 < q) (hqr : q ≤ r) (hrq : r ≤ 2 * q) :
    q ^ t ≤ (2 : ℝ) ^ |t| * r ^ t := by
  have hr0 : 0 < r := lt_of_lt_of_le hq hqr
  rcases le_or_gt 0 t with ht | ht
  · calc q ^ t ≤ r ^ t := Real.rpow_le_rpow hq.le hqr ht
      _ ≤ (2 : ℝ) ^ |t| * r ^ t :=
          le_mul_of_one_le_left (Real.rpow_nonneg hr0.le _)
            (Real.one_le_rpow (by norm_num) (abs_nonneg t))
  · have h1 : q ^ t ≤ (r / 2) ^ t :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) ht.le
    rw [Real.div_rpow hr0.le (by norm_num)] at h1
    rw [abs_of_neg ht, Real.rpow_neg (by norm_num)]
    calc q ^ t ≤ r ^ t / (2 : ℝ) ^ t := h1
      _ = ((2 : ℝ) ^ t)⁻¹ * r ^ t := by ring

/-- The complete power-row cofactor sum `Σ_{j ≤ n} j^{-ε} ⌊n/j⌋^s`. -/
def powerRowCofactorSum (ε : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, (((j : ℝ)) : ℂ) ^ (-(ε : ℂ)) * ((((n / j : ℕ) : ℝ)) : ℂ) ^ s

/-- The pole trace `𝓛_s = α⁻¹ Σ_m m^s (m^{-α} − (m+1)^{-α})` of the power row, `α = 1 − ε`. -/
def powerPoleTrace (ε : ℝ) (s : ℂ) : ℂ := powerPoleSum (1 - ε) s / ((1 - ε : ℝ) : ℂ)

/-- **The two-pole expansion of the power-row cofactor sum.** For `0 < ε < 1` and
`0 < Re s < 1 − ε` there is `K` with, for every `n ≥ 1`,
`‖Σ_{j ≤ n} j^{-ε}⌊n/j⌋^s − 𝓛_s n^{1−ε} − ζ(s + ε) n^s‖ ≤ K (√n)^{Re s − ε}`. -/
theorem norm_powerRowCofactorSum_sub_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖powerRowCofactorSum ε s n - powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) -
          riemannZeta (s + ε) * (((n : ℝ)) : ℂ) ^ s‖ ≤ K * Real.sqrt n ^ (s.re - ε) := by
  set α : ℝ := 1 - ε with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  set σ := s.re with hσ
  have hσ1 : σ ≤ 1 := by linarith
  have hαC0 : ((α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hsα : ((α : ℝ) : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this; linarith
  -- exponents of the two partial-sum expansions
  set w₁ : ℂ := s + ε with hw₁
  have hw₁re : w₁.re = σ + ε := by simp [hw₁, hσ]
  have hw₁0 : 0 < w₁.re := by rw [hw₁re]; linarith
  have hw₁1 : w₁ ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hw₁re, one_re] at this; linarith
  set w₂ : ℂ := (ε : ℂ) with hw₂
  have hw₂re : w₂.re = ε := by simp [hw₂]
  have hw₂0 : 0 < w₂.re := by rw [hw₂re]; exact hε0
  have hw₂1 : w₂ ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hw₂re, one_re] at this; linarith
  have h1w₁ : 1 - w₁ = ((α : ℝ) : ℂ) - s := by rw [hw₁, hαdef]; push_cast; ring
  have h1w₂ : 1 - w₂ = ((α : ℝ) : ℂ) := by rw [hw₂, hαdef]; push_cast; ring
  set C₁ := partialSumRate w₁ with hC₁
  set C₂ := partialSumRate w₂ with hC₂
  have hC₁0 : 0 ≤ C₁ := partialSumRate_nonneg hw₁0
  have hC₂0 : 0 ≤ C₂ := partialSumRate_nonneg hw₂0
  set ν : ℝ := α + 1 - σ with hν
  have hν0 : 0 < ν := by rw [hν]; linarith
  set Kδ : ℝ := (1 + 2 * ‖s‖) * (1 + 1 / σ) with hKδ
  set K : ℝ := (2 : ℝ) ^ |σ - ε| * (‖s‖ * (1 + 1 / α)) + C₁ + C₂ * Kδ +
    ‖s‖ * (1 + 1 / ν) + C₂ + 1 + 1 with hK
  refine ⟨K, fun n hn => ?_⟩
  -- the cutoffs `q = ⌊√n⌋ ≤ r = √n < q + 1`
  obtain ⟨q, hq⟩ : ∃ q, q = Nat.sqrt n := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.sqrt_pos.mpr hn
  have hqq : q * q ≤ n := by rw [hq]; exact Nat.sqrt_le n
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (n : ℝ) := ⟨_, rfl⟩
  rw [← hr]
  have hr2 : r ^ 2 = n := by rw [hr]; exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hqr : (q : ℝ) ≤ r := by rw [hq, hr]; exact Real.nat_sqrt_le_real_sqrt
  have hrq : r < q + 1 := by rw [hq, hr]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr
  have hr1 : (1 : ℝ) ≤ r := le_trans (by exact_mod_cast hq1) hqr
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr2q : r ≤ 2 * q := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith
  -- partial sums of `d^{-ε}`
  set F : ℕ → ℂ := fun N => cpowPartialSum w₂ N with hF
  have hFdef : ∀ N : ℕ, ∑ d ∈ Icc 1 N, (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) = F N := fun N => rfl
  -- the hyperbola split
  have hS : powerRowCofactorSum ε s n =
      ∑ d ∈ Icc 1 q, (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) * ((((n / d : ℕ) : ℝ)) : ℂ) ^ s +
        (∑ k ∈ Icc 1 q, powerStep s k * F (n / k) - (((q : ℝ)) : ℂ) ^ s * F q) := by
    have h := sum_mul_partialSum_div_eq_hyperbola (fun d => (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)))
      (powerStep s) n
    simp only [sum_powerStep hs, hFdef] at h
    rw [← hq] at h
    rw [powerRowCofactorSum, h]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, sum_powerStep hs]
  -- the head `d ≤ q`
  obtain ⟨EA, hEA⟩ : ∃ E : ℂ, E = ∑ d ∈ Icc 1 q, (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
      (((((n / d : ℕ) : ℝ)) : ℂ) ^ s - (((((n : ℝ) / d : ℝ))) : ℂ) ^ s) := ⟨_, rfl⟩
  have hhead : ∑ d ∈ Icc 1 q, (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) * ((((n / d : ℕ) : ℝ)) : ℂ) ^ s =
      (((n : ℝ)) : ℂ) ^ s * cpowPartialSum w₁ q + EA := by
    rw [hEA, cpowPartialSum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdC : (((d : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hdiv := TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 hd0 s
    have hpow : (((d : ℝ)) : ℂ) ^ (-w₁) = (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) * (((d : ℝ)) : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ hdC, hw₁, hw₂]; ring_nf
    rw [hdiv, hpow]; ring
  have hEAb : ‖EA‖ ≤ (2 : ℝ) ^ |σ - ε| * (‖s‖ * (1 + 1 / α)) * r ^ (σ - ε) := by
    rw [hEA]
    have hterm : ∀ d ∈ Icc 1 q, ‖(((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
        (((((n / d : ℕ) : ℝ)) : ℂ) ^ s - (((((n : ℝ) / d : ℝ))) : ℂ) ^ s)‖ ≤
        (d : ℝ) ^ (-ε) * (‖s‖ * (q : ℝ) ^ (σ - 1)) := by
      intro d hd
      obtain ⟨hd1, hdq⟩ := mem_Icc.mp hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hqnd : q ≤ n / d :=
        (Nat.le_div_iff_mul_le hd1).mpr ((Nat.mul_le_mul_left q hdq).trans hqq)
      have hqnd' : (q : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hqnd
      have hle : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hlt : (n : ℝ) / d - ((n / d : ℕ) : ℝ) ≤ 1 := by
        have := (abs_le.mp (RHTower.Sieve.abs_natDiv_sub_div_le (N := n) hd1)).1
        linarith
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd0, norm_sub_rev]
      have hre : (-(ε : ℂ)).re = -ε := by simp
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hd0.le _)
      calc _ ≤ ‖s‖ * (q : ℝ) ^ (σ - 1) * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) :=
            norm_ofReal_cpow_sub_le hσ1 hq0 hqnd' hle
        _ ≤ ‖s‖ * (q : ℝ) ^ (σ - 1) * 1 := by gcongr
        _ = _ := mul_one _
    have hsumε := RHTower.sum_rpow_neg_head_le (c := ε) hε0 hε1 q
    have hqα : (1 : ℝ) ≤ (q : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast hq1) hα.le
    have hqpow : (q : ℝ) ^ (σ - 1) * (q : ℝ) ^ α = (q : ℝ) ^ (σ - ε) := by
      rw [← Real.rpow_add hq0, hαdef]; ring_nf
    have hq2 := rpow_le_two_rpow_abs_mul (t := σ - ε) hq0 hqr hr2q
    calc _ ≤ ∑ d ∈ Icc 1 q, (d : ℝ) ^ (-ε) * (‖s‖ * (q : ℝ) ^ (σ - 1)) :=
          (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = (∑ d ∈ Icc 1 q, (d : ℝ) ^ (-ε)) * (‖s‖ * (q : ℝ) ^ (σ - 1)) := by rw [sum_mul]
      _ ≤ (1 + (q : ℝ) ^ (1 - ε) / (1 - ε)) * (‖s‖ * (q : ℝ) ^ (σ - 1)) :=
          mul_le_mul_of_nonneg_right hsumε (by positivity)
      _ ≤ ((1 + 1 / α) * (q : ℝ) ^ α) * (‖s‖ * (q : ℝ) ^ (σ - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← hαdef, add_mul, one_mul, div_eq_mul_one_div, mul_comm ((q : ℝ) ^ α)]
          linarith
      _ = ‖s‖ * (1 + 1 / α) * ((q : ℝ) ^ (σ - 1) * (q : ℝ) ^ α) := by ring
      _ = ‖s‖ * (1 + 1 / α) * (q : ℝ) ^ (σ - ε) := by rw [hqpow]
      _ ≤ ‖s‖ * (1 + 1 / α) * ((2 : ℝ) ^ |σ - ε| * r ^ (σ - ε)) :=
          mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ = _ := by ring
  -- the partial-sum expansions at the cutoff `r`
  have hqr1 : r ≤ (q : ℝ) + 1 := hrq.le
  obtain ⟨e₁, he₁⟩ : ∃ e : ℂ, e = cpowPartialSum w₁ q -
      ((r : ℝ) : ℂ) ^ (((α : ℝ) : ℂ) - s) / (((α : ℝ) : ℂ) - s) - riemannZeta w₁ := ⟨_, rfl⟩
  have he₁b : ‖e₁‖ ≤ C₁ * r ^ (-(σ + ε)) := by
    have h := norm_cpowPartialSum_sub_le hw₁0 hw₁1 hq1 hqr hqr1
    rw [h1w₁, hw₁re] at h
    rw [he₁]; exact h
  obtain ⟨e₂, he₂⟩ : ∃ e : ℂ, e = F q - ((r : ℝ) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) -
      riemannZeta w₂ := ⟨_, rfl⟩
  have he₂b : ‖e₂‖ ≤ C₂ * r ^ (-ε) := by
    have h := norm_cpowPartialSum_sub_le hw₂0 hw₂1 hq1 hqr hqr1
    rw [h1w₂, hw₂re] at h
    rw [he₂]; exact h
  -- the long moduli `F(⌊n/k⌋)`
  obtain ⟨EB, hEB⟩ : ∃ E : ℂ, E = ∑ k ∈ Icc 1 q, powerStep s k * (F (n / k) -
      ((((n : ℝ) / k : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) - riemannZeta w₂) := ⟨_, rfl⟩
  have hstepb : ∀ k ∈ Icc 1 q, ‖powerStep s k‖ ≤ (1 + 2 * ‖s‖) * (k : ℝ) ^ (σ - 1) := by
    intro k hk
    obtain ⟨hk1, -⟩ := mem_Icc.mp hk
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · simp [powerStep, Complex.zero_cpow hs]
    · have hk0 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
      have hkk : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk1, Nat.cast_one]
      have hmv := norm_ofReal_cpow_sub_le hσ1 hk0 le_rfl (b := (k : ℝ)) (by rw [hkk]; linarith)
      rw [hkk, sub_sub_cancel, mul_one] at hmv
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hhalf : ((k : ℝ) - 1) ^ (σ - 1) ≤ ((k : ℝ) / 2) ^ (σ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have h2 : ((k : ℝ) / 2) ^ (σ - 1) ≤ 2 * (k : ℝ) ^ (σ - 1) := by
        rw [Real.div_rpow (by linarith) (by norm_num)]
        have h21 : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (σ - 1) := by
          rw [show (1 : ℝ) / 2 = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [div_le_iff₀ (by positivity)]
        have hk0' : 0 ≤ (k : ℝ) ^ (σ - 1) := Real.rpow_nonneg (by linarith) _
        nlinarith
      unfold powerStep
      rw [hkk]
      calc _ ≤ ‖s‖ * ((k : ℝ) - 1) ^ (σ - 1) := hmv
        _ ≤ ‖s‖ * (2 * (k : ℝ) ^ (σ - 1)) :=
            mul_le_mul_of_nonneg_left (hhalf.trans h2) (norm_nonneg _)
        _ ≤ (1 + 2 * ‖s‖) * (k : ℝ) ^ (σ - 1) := by
            have : 0 ≤ (k : ℝ) ^ (σ - 1) := Real.rpow_nonneg (by linarith) _
            nlinarith
  have hstepsum : ∑ k ∈ Icc 1 q, ‖powerStep s k‖ ≤ Kδ * r ^ σ := by
    have hc0 : 0 < 1 - σ := by linarith
    have hc1 : 1 - σ < 1 := by linarith
    have hhead := RHTower.sum_rpow_neg_head_le hc0 hc1 q
    rw [show 1 - (1 - σ) = σ by ring] at hhead
    have hqσ : (q : ℝ) ^ σ ≤ r ^ σ := Real.rpow_le_rpow hq0.le hqr hs0.le
    have h1σ : 1 ≤ r ^ σ := Real.one_le_rpow hr1 hs0.le
    calc _ ≤ ∑ k ∈ Icc 1 q, (1 + 2 * ‖s‖) * (k : ℝ) ^ (σ - 1) := sum_le_sum hstepb
      _ = (1 + 2 * ‖s‖) * ∑ k ∈ Icc 1 q, (k : ℝ) ^ (-(1 - σ)) := by
          rw [mul_sum]; exact sum_congr rfl fun k _ => by ring_nf
      _ ≤ (1 + 2 * ‖s‖) * (1 + (q : ℝ) ^ σ / σ) :=
          mul_le_mul_of_nonneg_left hhead (by positivity)
      _ ≤ (1 + 2 * ‖s‖) * ((1 + 1 / σ) * r ^ σ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((q : ℝ) ^ σ)]
          have : 1 / σ * (q : ℝ) ^ σ ≤ 1 / σ * r ^ σ :=
            mul_le_mul_of_nonneg_left hqσ (by positivity)
          linarith
      _ = Kδ * r ^ σ := by rw [hKδ]; ring
  have hEBb : ‖EB‖ ≤ C₂ * Kδ * r ^ (σ - ε) := by
    rw [hEB]
    have hterm : ∀ k ∈ Icc 1 q, ‖powerStep s k * (F (n / k) -
        ((((n : ℝ) / k : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) - riemannZeta w₂)‖ ≤
        ‖powerStep s k‖ * (C₂ * r ^ (-ε)) := by
      intro k hk
      obtain ⟨hk1, hkq⟩ := mem_Icc.mp hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hqnk : q ≤ n / k :=
        (Nat.le_div_iff_mul_le hk1).mpr ((Nat.mul_le_mul_left q hkq).trans hqq)
      have hN1 : 1 ≤ n / k := hq1.trans hqnk
      have hle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
      have hlt : (n : ℝ) / k ≤ ((n / k : ℕ) : ℝ) + 1 := by
        have := (abs_le.mp (RHTower.Sieve.abs_natDiv_sub_div_le (N := n) hk1)).1
        linarith
      have h := norm_cpowPartialSum_sub_le hw₂0 hw₂1 hN1 hle hlt
      rw [h1w₂, hw₂re] at h
      have hxr : r ≤ (n : ℝ) / k := by
        rw [le_div_iff₀ hk0]
        have hkr : (k : ℝ) ≤ r := le_trans (by exact_mod_cast hkq) hqr
        calc r * k ≤ r * r := mul_le_mul_of_nonneg_left hkr hr0.le
          _ = n := by rw [← sq, hr2]
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left ?_ hC₂0))
        (norm_nonneg _)
      exact Real.rpow_le_rpow_of_nonpos hr0 hxr (by linarith)
    have hrpow : r ^ σ * r ^ (-ε) = r ^ (σ - ε) := by
      rw [← Real.rpow_add hr0]; ring_nf
    calc _ ≤ ∑ k ∈ Icc 1 q, ‖powerStep s k‖ * (C₂ * r ^ (-ε)) :=
          (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = (∑ k ∈ Icc 1 q, ‖powerStep s k‖) * (C₂ * r ^ (-ε)) := by rw [sum_mul]
      _ ≤ (Kδ * r ^ σ) * (C₂ * r ^ (-ε)) :=
          mul_le_mul_of_nonneg_right hstepsum (by positivity)
      _ = C₂ * Kδ * (r ^ σ * r ^ (-ε)) := by ring
      _ = _ := by rw [hrpow]
  -- `Σ_k δ(k) F(⌊n/k⌋)` through the Abel-summed pole sum
  set Q1 : ℂ := ((((q : ℝ) + 1 : ℝ)) : ℂ) with hQ1
  obtain ⟨τ, hτ⟩ : ∃ t : ℂ, t = powerPoleSum α s -
      ∑ m ∈ Icc 1 q, (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) -
      ((α : ℝ) : ℂ) / (((α : ℝ) : ℂ) - s) * Q1 ^ (s - ((α : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hτb : ‖τ‖ ≤ α * ‖s‖ * ((1 + 1 / ν) * r ^ (-ν)) := by
    have h := norm_powerPoleSum_sub_partial_le hα hs0 (by linarith) hσ1 (q := q)
    rw [← hτ] at h
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
      (by positivity))
    push_cast
    exact Real.rpow_le_rpow_of_nonpos hr0 hqr1 (by linarith)
  have hsumF : ∑ k ∈ Icc 1 q, powerStep s k * F (n / k) =
      (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) *
          (powerPoleSum α s - ((α : ℝ) : ℂ) / (((α : ℝ) : ℂ) - s) * Q1 ^ (s - ((α : ℝ) : ℂ)) - τ +
            (((q : ℝ)) : ℂ) ^ s * Q1 ^ (-((α : ℝ) : ℂ))) +
        riemannZeta w₂ * (((q : ℝ)) : ℂ) ^ s + EB := by
    have habel := sum_powerStep_mul_cpow_eq hs α q
    have hk : ∀ k ∈ Icc 1 q, powerStep s k * F (n / k) =
        (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) *
          (powerStep s k * (((k : ℝ)) : ℂ) ^ (-((α : ℝ) : ℂ))) +
        riemannZeta w₂ * powerStep s k +
        powerStep s k * (F (n / k) - ((((n : ℝ) / k : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) -
          riemannZeta w₂) := by
      intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
      rw [TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 hk0]
      field_simp
      ring
    rw [sum_congr rfl hk, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, habel,
      sum_powerStep hs, ← hEB]
    have hM : ∑ m ∈ Icc 1 q, (((m : ℝ)) : ℂ) ^ s * ((mellinCell α m : ℝ) : ℂ) =
        powerPoleSum α s - ((α : ℝ) : ℂ) / (((α : ℝ) : ℂ) - s) * Q1 ^ (s - ((α : ℝ) : ℂ)) - τ := by
      rw [hτ]; ring
    rw [hM]
  -- cpow relations at `r = √n`
  set Rs : ℂ := ((r : ℝ) : ℂ) ^ s with hRs
  set Ra : ℂ := ((r : ℝ) : ℂ) ^ ((α : ℝ) : ℂ) with hRa
  set Rd : ℂ := ((r : ℝ) : ℂ) ^ (s - ((α : ℝ) : ℂ)) with hRd
  set Rb : ℂ := ((r : ℝ) : ℂ) ^ (((α : ℝ) : ℂ) - s) with hRb
  have hnr : (((n : ℝ)) : ℂ) = ((r : ℝ) : ℂ) * ((r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, hr2]
  have hns : (((n : ℝ)) : ℂ) ^ s = Rs * Rs := by
    rw [hnr, Complex.mul_cpow_ofReal_nonneg hr0.le hr0.le]
  have hnα : (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) = Ra * Ra := by
    rw [hnr, Complex.mul_cpow_ofReal_nonneg hr0.le hr0.le]
  have hRsb : Rs * Rb = Ra := by
    rw [hRs, hRb, hRa, ← Complex.cpow_add _ _ hrC]; ring_nf
  have hRad : Ra * Rd = Rs := by
    rw [hRs, hRd, hRa, ← Complex.cpow_add _ _ hrC]; ring_nf
  have hQ1C : Q1 ≠ 0 := by rw [hQ1]; exact_mod_cast (by positivity : (0 : ℝ) < (q : ℝ) + 1).ne'
  have hQinv : Q1 ^ ((α : ℝ) : ℂ) * Q1 ^ (-((α : ℝ) : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ hQ1C, add_neg_cancel, Complex.cpow_zero]
  -- the exact expansion
  set M1 : ℂ := Ra * Ra * (Rd - Q1 ^ (s - ((α : ℝ) : ℂ))) / (((α : ℝ) : ℂ) - s) with hM1
  set M2 : ℂ := (((q : ℝ)) : ℂ) ^ s / ((α : ℝ) : ℂ) * Ra * Q1 ^ (-((α : ℝ) : ℂ)) *
    (Ra - Q1 ^ ((α : ℝ) : ℂ)) with hM2
  have key : powerRowCofactorSum ε s n - powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) -
      riemannZeta (s + ε) * (((n : ℝ)) : ℂ) ^ s =
      M1 + (((n : ℝ)) : ℂ) ^ s * e₁ + EA - (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) * τ +
        M2 + EB - (((q : ℝ)) : ℂ) ^ s * e₂ := by
    have hP1 : cpowPartialSum w₁ q = Rb / (((α : ℝ) : ℂ) - s) + riemannZeta w₁ + e₁ := by
      rw [he₁, hRb]; ring
    have hP2 : F q = Ra / ((α : ℝ) : ℂ) + riemannZeta w₂ + e₂ := by rw [he₂, hRa]; ring
    have hαinv : ((α : ℝ) : ℂ) * (((α : ℝ) : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hαC0
    rw [hS, hhead, hsumF, hP1, hP2, powerPoleTrace, ← hαdef, hM1, hM2, hns, hnα]
    have e3 : Rs * Rs * Rb = Ra * Ra * Rd := by
      rw [mul_assoc, hRsb, ← hRad]; ring
    simp only [div_eq_mul_inv]
    linear_combination (((α : ℝ) : ℂ) - s)⁻¹ * e3 -
      Ra * Ra * Q1 ^ (s - ((α : ℝ) : ℂ)) * (((α : ℝ) : ℂ) - s)⁻¹ * hαinv +
      (((q : ℝ)) : ℂ) ^ s * Ra * (((α : ℝ) : ℂ))⁻¹ * hQinv
  -- norms of the cpow factors
  have hnRa : ‖Ra‖ = r ^ α := by
    rw [hRa, Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.ofReal_re]
  have hnRs : ‖Rs‖ = r ^ σ := by rw [hRs, Complex.norm_cpow_eq_rpow_re_of_pos hr0]
  have hnq : ‖(((q : ℝ)) : ℂ) ^ s‖ = (q : ℝ) ^ σ := Complex.norm_cpow_eq_rpow_re_of_pos hq0 s
  have hqσ : (q : ℝ) ^ σ ≤ r ^ σ := Real.rpow_le_rpow hq0.le hqr hs0.le
  have hQ0 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hrexp : ∀ a b : ℝ, r ^ a * r ^ b = r ^ (a + b) := fun a b => (Real.rpow_add hr0 a b).symm
  have hσε : α + σ - 1 = σ - ε := by rw [hαdef]; ring
  have hb1 : ‖M1‖ ≤ r ^ (σ - ε) := by
    have hz : (s - ((α : ℝ) : ℂ)).re ≤ 1 := by simp; linarith
    have hmv := norm_ofReal_cpow_sub_le hz hr0 le_rfl hqr1
    rw [show (s - ((α : ℝ) : ℂ)).re - 1 = σ - α - 1 by simp [hσ]] at hmv
    have hzn : ‖s - ((α : ℝ) : ℂ)‖ = ‖((α : ℝ) : ℂ) - s‖ := norm_sub_rev _ _
    have hzpos : 0 < ‖((α : ℝ) : ℂ) - s‖ := norm_pos_iff.mpr hsα
    have hdiff : ‖Rd - Q1 ^ (s - ((α : ℝ) : ℂ))‖ ≤ ‖((α : ℝ) : ℂ) - s‖ * r ^ (σ - α - 1) := by
      rw [norm_sub_rev, hRd, hQ1, ← hzn]
      calc _ ≤ ‖s - ((α : ℝ) : ℂ)‖ * r ^ (σ - α - 1) * ((q : ℝ) + 1 - r) := hmv
        _ ≤ ‖s - ((α : ℝ) : ℂ)‖ * r ^ (σ - α - 1) * 1 := by gcongr; linarith
        _ = _ := mul_one _
    rw [hM1, norm_div, norm_mul, norm_mul, hnRa, div_le_iff₀ hzpos]
    calc r ^ α * r ^ α * ‖Rd - Q1 ^ (s - ((α : ℝ) : ℂ))‖
        ≤ r ^ α * r ^ α * (‖((α : ℝ) : ℂ) - s‖ * r ^ (σ - α - 1)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (r ^ α * r ^ α * r ^ (σ - α - 1)) * ‖((α : ℝ) : ℂ) - s‖ := by ring
      _ = r ^ (σ - ε) * ‖((α : ℝ) : ℂ) - s‖ := by
          rw [hrexp, hrexp, ← hσε]; ring_nf
  have hb2 : ‖(((n : ℝ)) : ℂ) ^ s * e₁‖ ≤ C₁ * r ^ (σ - ε) := by
    rw [norm_mul, hns, norm_mul, hnRs]
    calc r ^ σ * r ^ σ * ‖e₁‖ ≤ r ^ σ * r ^ σ * (C₁ * r ^ (-(σ + ε))) :=
          mul_le_mul_of_nonneg_left he₁b (by positivity)
      _ = C₁ * (r ^ σ * r ^ σ * r ^ (-(σ + ε))) := by ring
      _ = C₁ * r ^ (σ - ε) := by rw [hrexp, hrexp]; ring_nf
  have hb3 : ‖(((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) * τ‖ ≤
      ‖s‖ * (1 + 1 / ν) * r ^ (σ - ε) := by
    rw [norm_mul, norm_div, hnα, norm_mul, hnRa, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hα]
    calc r ^ α * r ^ α / α * ‖τ‖ ≤ r ^ α * r ^ α / α * (α * ‖s‖ * ((1 + 1 / ν) * r ^ (-ν))) :=
          mul_le_mul_of_nonneg_left hτb (by positivity)
      _ = ‖s‖ * (1 + 1 / ν) * (r ^ α * r ^ α * r ^ (-ν)) := by field_simp
      _ = ‖s‖ * (1 + 1 / ν) * r ^ (σ - ε) := by
          rw [hrexp, hrexp, hν, hαdef]; ring_nf
  have hb4 : ‖M2‖ ≤ r ^ (σ - ε) := by
    have hz : ((α : ℝ) : ℂ).re ≤ 1 := by simp [hαdef]; linarith
    have hmv := norm_ofReal_cpow_sub_le hz hr0 le_rfl hqr1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα, Complex.ofReal_re] at hmv
    have hdiff : ‖Ra - Q1 ^ ((α : ℝ) : ℂ)‖ ≤ α * r ^ (α - 1) := by
      rw [norm_sub_rev, hRa, hQ1]
      calc _ ≤ α * r ^ (α - 1) * ((q : ℝ) + 1 - r) := hmv
        _ ≤ α * r ^ (α - 1) * 1 := by gcongr; linarith
        _ = _ := mul_one _
    have hQn : ‖Q1 ^ (-((α : ℝ) : ℂ))‖ ≤ r ^ (-α) := by
      rw [hQ1, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
      simp only [neg_re, ofReal_re]
      exact Real.rpow_le_rpow_of_nonpos hr0 hqr1 (by linarith)
    rw [hM2, norm_mul, norm_mul, norm_mul, norm_div, hnq, hnRa, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hα]
    calc (q : ℝ) ^ σ / α * r ^ α * ‖Q1 ^ (-((α : ℝ) : ℂ))‖ * ‖Ra - Q1 ^ ((α : ℝ) : ℂ)‖
        ≤ r ^ σ / α * r ^ α * r ^ (-α) * (α * r ^ (α - 1)) := by
          gcongr
      _ = r ^ σ * r ^ α * r ^ (-α) * r ^ (α - 1) := by field_simp
      _ = r ^ (σ - ε) := by rw [hrexp, hrexp, hrexp, hαdef]; ring_nf
  have hb5 : ‖(((q : ℝ)) : ℂ) ^ s * e₂‖ ≤ C₂ * r ^ (σ - ε) := by
    rw [norm_mul, hnq]
    calc (q : ℝ) ^ σ * ‖e₂‖ ≤ r ^ σ * (C₂ * r ^ (-ε)) :=
          mul_le_mul hqσ he₂b (norm_nonneg _) (by positivity)
      _ = C₂ * (r ^ σ * r ^ (-ε)) := by ring
      _ = C₂ * r ^ (σ - ε) := by rw [hrexp]; ring_nf
  rw [key]
  have htri : ‖M1 + (((n : ℝ)) : ℂ) ^ s * e₁ + EA -
      (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) * τ + M2 + EB - (((q : ℝ)) : ℂ) ^ s * e₂‖ ≤
      ‖M1‖ + ‖(((n : ℝ)) : ℂ) ^ s * e₁‖ + ‖EA‖ +
        ‖(((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) / ((α : ℝ) : ℂ) * τ‖ + ‖M2‖ + ‖EB‖ +
        ‖(((q : ℝ)) : ℂ) ^ s * e₂‖ := by
    refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    exact norm_add_le _ _
  refine htri.trans ?_
  rw [hK]
  nlinarith [hb1, hb2, hEAb, hb3, hb4, hEBb, hb5, Real.rpow_nonneg hr0.le (σ - ε)]

end GaloisForLFunctions.ArithmeticDefectRigidity
