import GaloisForLFunctions.ArithmeticDefectRigidity.ThePoleTraceDefinesALinearCofactorRenormalization
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

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
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg)
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

/-- Rounding error of the hyperbola head `d ≤ ⌊√n⌋`. -/
def powerHeadError (ε : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ Icc 1 (Nat.sqrt n), (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
    (((((n / d : ℕ) : ℝ)) : ℂ) ^ s - (((((n : ℝ) / d : ℝ))) : ℂ) ^ s)

/-- Error of the long moduli: the strip remainders of `Σ_{d ≤ ⌊n/k⌋} d^{-ε}` against the steps. -/
def powerLongError (ε : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 (Nat.sqrt n), powerStep s k * (cpowPartialSum (ε : ℂ) (n / k) -
    ((((n : ℝ) / k : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) - riemannZeta (ε : ℂ))

/-- The cutoffs `q = ⌊√n⌋` and `r = √n` satisfy `1 ≤ q ≤ r < q + 1`, `r ≤ 2q`, `r² = n`. -/
theorem natSqrt_cutoff {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ Nat.sqrt n ∧ ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n ∧ Real.sqrt n < (Nat.sqrt n : ℕ) + 1 ∧
      Real.sqrt n ≤ 2 * ((Nat.sqrt n : ℕ) : ℝ) ∧ Real.sqrt n ^ 2 = n := by
  have hq1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hqr : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hrq : Real.sqrt n < (Nat.sqrt n : ℕ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hq1' : (1 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hq1
  exact ⟨hq1, hqr, hrq, by linarith, Real.sq_sqrt (Nat.cast_nonneg n)⟩

/-- `‖δ_s(k)‖ ≤ (1 + 2‖s‖) k^{Re s − 1}` for `k ≥ 1`, `0 < Re s ≤ 1`. -/
theorem norm_powerStep_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) {k : ℕ} (hk1 : 1 ≤ k) :
    ‖powerStep s k‖ ≤ (1 + 2 * ‖s‖) * (k : ℝ) ^ (s.re - 1) := by
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  rcases eq_or_lt_of_le hk1 with rfl | hk2
  · simp [powerStep, Complex.zero_cpow hs]
  have hk0 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hkk : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hmv := norm_ofReal_cpow_sub_le hs1 hk0 le_rfl (b := (k : ℝ)) (by rw [hkk]; linarith)
  rw [hkk, sub_sub_cancel, mul_one] at hmv
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkσ : 0 ≤ (k : ℝ) ^ (s.re - 1) := Real.rpow_nonneg (by linarith) _
  have hhalf : ((k : ℝ) - 1) ^ (s.re - 1) ≤ ((k : ℝ) / 2) ^ (s.re - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h21 : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s.re - 1) := by
    rw [show (1 : ℝ) / 2 = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : ((k : ℝ) / 2) ^ (s.re - 1) ≤ 2 * (k : ℝ) ^ (s.re - 1) := by
    rw [Real.div_rpow (by linarith) (by norm_num), div_le_iff₀ (by positivity)]
    nlinarith only [h21, hkσ]
  unfold powerStep
  rw [hkk]
  calc _ ≤ ‖s‖ * ((k : ℝ) - 1) ^ (s.re - 1) := hmv
    _ ≤ ‖s‖ * (2 * (k : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_left (hhalf.trans h2) (norm_nonneg _)
    _ ≤ (1 + 2 * ‖s‖) * (k : ℝ) ^ (s.re - 1) := by nlinarith only [hkσ]

/-- `Σ_{k ≤ q} ‖δ_s(k)‖ ≤ (1 + 2‖s‖)(1 + 1/Re s) q^{Re s}` for `q ≥ 1`. -/
theorem sum_norm_powerStep_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {q : ℕ} (hq1 : 1 ≤ q) :
    ∑ k ∈ Icc 1 q, ‖powerStep s k‖ ≤ (1 + 2 * ‖s‖) * (1 + 1 / s.re) * (q : ℝ) ^ s.re := by
  have hc0 : 0 < 1 - s.re := by linarith
  have hc1 : 1 - s.re < 1 := by linarith
  have hhead := RHTower.sum_rpow_neg_head_le hc0 hc1 q
  rw [show 1 - (1 - s.re) = s.re by ring] at hhead
  have h1q : 1 ≤ (q : ℝ) ^ s.re := Real.one_le_rpow (by exact_mod_cast hq1) hs0.le
  calc _ ≤ ∑ k ∈ Icc 1 q, (1 + 2 * ‖s‖) * (k : ℝ) ^ (s.re - 1) :=
        sum_le_sum fun k hk => norm_powerStep_le hs0 hs1.le (mem_Icc.mp hk).1
    _ = (1 + 2 * ‖s‖) * ∑ k ∈ Icc 1 q, (k : ℝ) ^ (-(1 - s.re)) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring_nf
    _ ≤ (1 + 2 * ‖s‖) * (1 + (q : ℝ) ^ s.re / s.re) :=
        mul_le_mul_of_nonneg_left hhead (by positivity)
    _ ≤ (1 + 2 * ‖s‖) * ((1 + 1 / s.re) * (q : ℝ) ^ s.re) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((q : ℝ) ^ s.re)]
        linarith
    _ = _ := by ring

/-- **The head rounding error** is `O(n^{(Re s − ε)/2})`. -/
theorem norm_powerHeadError_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) {n : ℕ} (hn : 1 ≤ n) :
    ‖powerHeadError ε s n‖ ≤
      (2 : ℝ) ^ |s.re - ε| * (‖s‖ * (1 + 1 / (1 - ε))) * Real.sqrt n ^ (s.re - ε) := by
  obtain ⟨hq1, hqr, -, hr2q, -⟩ := natSqrt_cutoff hn
  set q := Nat.sqrt n with hq
  have hqq : q * q ≤ n := Nat.sqrt_le n
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hσ1 : s.re ≤ 1 := by linarith
  have hterm : ∀ d ∈ Icc 1 q, ‖(((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
      (((((n / d : ℕ) : ℝ)) : ℂ) ^ s - (((((n : ℝ) / d : ℝ))) : ℂ) ^ s)‖ ≤
      (d : ℝ) ^ (-ε) * (‖s‖ * (q : ℝ) ^ (s.re - 1)) := by
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
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd0, norm_sub_rev,
      show (-(ε : ℂ)).re = -ε by simp]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hd0.le _)
    calc _ ≤ ‖s‖ * (q : ℝ) ^ (s.re - 1) * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) :=
          norm_ofReal_cpow_sub_le hσ1 hq0 hqnd' hle
      _ ≤ ‖s‖ * (q : ℝ) ^ (s.re - 1) * 1 := by gcongr
      _ = _ := mul_one _
  have hsumε := RHTower.sum_rpow_neg_head_le hε0 hε1 q
  have hα : 0 < 1 - ε := by linarith
  have hqα : (1 : ℝ) ≤ (q : ℝ) ^ (1 - ε) := Real.one_le_rpow (by exact_mod_cast hq1) hα.le
  have hqpow : (q : ℝ) ^ (s.re - 1) * (q : ℝ) ^ (1 - ε) = (q : ℝ) ^ (s.re - ε) := by
    rw [← Real.rpow_add hq0]; ring_nf
  have hq2 := rpow_le_two_rpow_abs_mul (t := s.re - ε) hq0 hqr hr2q
  have hsq : 0 ≤ ‖s‖ * (q : ℝ) ^ (s.re - 1) := by positivity
  calc _ ≤ ∑ d ∈ Icc 1 q, (d : ℝ) ^ (-ε) * (‖s‖ * (q : ℝ) ^ (s.re - 1)) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = (∑ d ∈ Icc 1 q, (d : ℝ) ^ (-ε)) * (‖s‖ * (q : ℝ) ^ (s.re - 1)) := by rw [sum_mul]
    _ ≤ ((1 + 1 / (1 - ε)) * (q : ℝ) ^ (1 - ε)) * (‖s‖ * (q : ℝ) ^ (s.re - 1)) := by
        refine mul_le_mul_of_nonneg_right (hsumε.trans ?_) hsq
        rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((q : ℝ) ^ (1 - ε))]
        linarith
    _ = ‖s‖ * (1 + 1 / (1 - ε)) * ((q : ℝ) ^ (s.re - 1) * (q : ℝ) ^ (1 - ε)) := by ring
    _ = ‖s‖ * (1 + 1 / (1 - ε)) * (q : ℝ) ^ (s.re - ε) := by rw [hqpow]
    _ ≤ ‖s‖ * (1 + 1 / (1 - ε)) * ((2 : ℝ) ^ |s.re - ε| * Real.sqrt n ^ (s.re - ε)) :=
        mul_le_mul_of_nonneg_left hq2 (by positivity)
    _ = _ := by ring

/-- **The long-moduli error** is `O(n^{(Re s − ε)/2})`. -/
theorem norm_powerLongError_le {ε : ℝ} (hε0 : 0 < ε) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) {n : ℕ} (hn : 1 ≤ n) :
    ‖powerLongError ε s n‖ ≤ partialSumRate (ε : ℂ) * ((1 + 2 * ‖s‖) * (1 + 1 / s.re)) *
      Real.sqrt n ^ (s.re - ε) := by
  obtain ⟨hq1, hqr, -, -, hr2⟩ := natSqrt_cutoff hn
  set q := Nat.sqrt n with hq
  set r := Real.sqrt n with hr
  have hqq : q * q ≤ n := Nat.sqrt_le n
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hw0 : 0 < (ε : ℂ).re := by simpa using hε0
  have hw1 : (ε : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h1w : (1 : ℂ) - ε = ((1 - ε : ℝ) : ℂ) := by push_cast; ring
  set C₂ := partialSumRate (ε : ℂ)
  have hC₂0 : 0 ≤ C₂ := partialSumRate_nonneg hw0
  have hterm : ∀ k ∈ Icc 1 q, ‖powerStep s k * (cpowPartialSum (ε : ℂ) (n / k) -
      ((((n : ℝ) / k : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) - riemannZeta (ε : ℂ))‖ ≤
      ‖powerStep s k‖ * (C₂ * r ^ (-ε)) := by
    intro k hk
    obtain ⟨hk1, hkq⟩ := mem_Icc.mp hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hqnk : q ≤ n / k :=
      (Nat.le_div_iff_mul_le hk1).mpr ((Nat.mul_le_mul_left q hkq).trans hqq)
    have hle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
    have hlt : (n : ℝ) / k ≤ ((n / k : ℕ) : ℝ) + 1 := by
      have := (abs_le.mp (RHTower.Sieve.abs_natDiv_sub_div_le (N := n) hk1)).1
      linarith
    have h := norm_cpowPartialSum_sub_le hw0 hw1 (hq1.trans hqnk) hle hlt
    rw [h1w, show (ε : ℂ).re = ε by simp] at h
    have hxr : r ≤ (n : ℝ) / k := by
      rw [le_div_iff₀ hk0]
      have hkr : (k : ℝ) ≤ r := le_trans (by exact_mod_cast hkq) hqr
      calc r * k ≤ r * r := mul_le_mul_of_nonneg_left hkr hr0.le
        _ = n := by rw [← sq, hr2]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left ?_ hC₂0))
      (norm_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos hr0 hxr (by linarith)
  have hsum := sum_norm_powerStep_le hs0 (by linarith) hq1
  have hqσ : (q : ℝ) ^ s.re ≤ r ^ s.re := Real.rpow_le_rpow hq0.le hqr hs0.le
  have hrpow : r ^ s.re * r ^ (-ε) = r ^ (s.re - ε) := by rw [← Real.rpow_add hr0]; ring_nf
  calc _ ≤ ∑ k ∈ Icc 1 q, ‖powerStep s k‖ * (C₂ * r ^ (-ε)) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = (∑ k ∈ Icc 1 q, ‖powerStep s k‖) * (C₂ * r ^ (-ε)) := by rw [sum_mul]
    _ ≤ ((1 + 2 * ‖s‖) * (1 + 1 / s.re) * r ^ s.re) * (C₂ * r ^ (-ε)) := by
        refine mul_le_mul_of_nonneg_right (hsum.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hqσ (by positivity)
    _ = C₂ * ((1 + 2 * ‖s‖) * (1 + 1 / s.re)) * (r ^ s.re * r ^ (-ε)) := by ring
    _ = _ := by rw [hrpow]

/-- **Exact split of the power-row cofactor sum** at `q = ⌊√n⌋`:
`S(n) = n^s P_{s+ε}(q) + head + (n^α/α) Σ_{k ≤ q} δ(k)k^{-α} + ζ(ε) q^s + long − q^s F(q)`. -/
theorem powerRowCofactorSum_eq_split {ε : ℝ} (hε1 : ε < 1) {s : ℂ} (hs : s ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) :
    powerRowCofactorSum ε s n =
      (((n : ℝ)) : ℂ) ^ s * cpowPartialSum (s + ε) (Nat.sqrt n) + powerHeadError ε s n +
        ((((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) *
            ∑ k ∈ Icc 1 (Nat.sqrt n), powerStep s k * (((k : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ)) +
          riemannZeta (ε : ℂ) * (((Nat.sqrt n : ℕ) : ℝ) : ℂ) ^ s + powerLongError ε s n -
          (((Nat.sqrt n : ℕ) : ℝ) : ℂ) ^ s * cpowPartialSum (ε : ℂ) (Nat.sqrt n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hαC : ((1 - ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < 1 - ε).ne'
  -- hyperbola
  have h := sum_mul_partialSum_div_eq_hyperbola (fun d => (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)))
    (powerStep s) n
  simp only [sum_powerStep hs] at h
  have hF : ∀ N : ℕ, ∑ d ∈ Icc 1 N, (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) = cpowPartialSum (ε : ℂ) N :=
    fun N => rfl
  simp only [hF] at h
  rw [powerRowCofactorSum, h]
  -- head
  have hhead : ∑ d ∈ Icc 1 (Nat.sqrt n), (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) *
      ((((n / d : ℕ) : ℝ)) : ℂ) ^ s =
      (((n : ℝ)) : ℂ) ^ s * cpowPartialSum (s + ε) (Nat.sqrt n) + powerHeadError ε s n := by
    rw [powerHeadError, cpowPartialSum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdC : (((d : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hdiv := TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 hd0 s
    have hpow : (((d : ℝ)) : ℂ) ^ (-(s + ε)) =
        (((d : ℝ)) : ℂ) ^ (-(ε : ℂ)) * (((d : ℝ)) : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ hdC]; ring_nf
    rw [hdiv, hpow]; ring
  -- long moduli
  have hlong : ∑ k ∈ Icc 1 (Nat.sqrt n), powerStep s k * cpowPartialSum (ε : ℂ) (n / k) =
      (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) *
          ∑ k ∈ Icc 1 (Nat.sqrt n), powerStep s k * (((k : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ)) +
        riemannZeta (ε : ℂ) * (((Nat.sqrt n : ℕ) : ℝ) : ℂ) ^ s + powerLongError ε s n := by
    rw [powerLongError, mul_sum, ← sum_powerStep hs, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    rw [TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 hk0]
    field_simp
    ring
  rw [hhead]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, sum_powerStep hs, hlong]

/-- **The algebra of the two-pole expansion.** After the partial sums are expanded at `r = √n`,
the cross terms of order `n^{(1+s−ε)/2}` reduce to the two cutoff differences. -/
theorem twoPole_algebra {S A Bs Fq G P P1 τ e₁ e₂ EA EB z₁ z₂ a s Rs Ra Rd Rb Qd Qa Qm qs : ℂ}
    (ha : a ≠ 0) (hS : S = A + (Bs - qs * Fq)) (hA : A = Rs * Rs * P1 + EA)
    (hB : Bs = Ra * Ra / a * G + z₂ * qs + EB) (hG : G = P - a / (a - s) * Qd - τ + qs * Qm)
    (hP1 : P1 = Rb / (a - s) + z₁ + e₁) (hFq : Fq = Ra / a + z₂ + e₂) (h1 : Rs * Rb = Ra)
    (h2 : Ra * Rd = Rs) (h3 : Qa * Qm = 1) :
    S - P / a * (Ra * Ra) - z₁ * (Rs * Rs) =
      Ra * Ra * (Rd - Qd) / (a - s) + Rs * Rs * e₁ + EA - Ra * Ra / a * τ +
        qs / a * Ra * Qm * (Ra - Qa) + EB - qs * e₂ := by
  subst hS hA hB hG hP1 hFq
  have e3 : Rs * Rs * Rb = Ra * Ra * Rd := by rw [mul_assoc, h1, ← h2]; ring
  have hainv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  simp only [div_eq_mul_inv]
  linear_combination (a - s)⁻¹ * e3 - Ra * Ra * Qd * (a - s)⁻¹ * hainv + qs * Ra * a⁻¹ * h3

/-- The first cutoff difference `r^{2α}(r^{s−α} − (q+1)^{s−α})/(α − s)` is `O(r^{Re s − ε})`. -/
theorem norm_twoPole_first_le {ε : ℝ} {s : ℂ} (hs1 : s.re < 1 - ε) {q r : ℝ}
    (hr0 : 0 < r) (hqr : r ≤ q + 1) (hrq : q + 1 - r ≤ 1) :
    ‖((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) *
        (((r : ℝ) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)) - (((q + 1 : ℝ)) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ))) /
        (((1 - ε : ℝ) : ℂ) - s)‖ ≤ r ^ (s.re - ε) := by
  have hsα : ((1 - ε : ℝ) : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hz : (s - ((1 - ε : ℝ) : ℂ)).re ≤ 1 := by simp; linarith
  have hmv := norm_ofReal_cpow_sub_le hz hr0 le_rfl hqr
  rw [show (s - ((1 - ε : ℝ) : ℂ)).re - 1 = s.re - (1 - ε) - 1 by simp] at hmv
  have hzpos : 0 < ‖((1 - ε : ℝ) : ℂ) - s‖ := norm_pos_iff.mpr hsα
  have hnRa : ‖((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ)‖ = r ^ (1 - ε) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.ofReal_re]
  have hdiff : ‖((r : ℝ) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)) -
      (((q + 1 : ℝ)) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ))‖ ≤
      ‖((1 - ε : ℝ) : ℂ) - s‖ * r ^ (s.re - (1 - ε) - 1) := by
    rw [norm_sub_rev, ← norm_neg (((1 - ε : ℝ) : ℂ) - s), neg_sub]
    calc _ ≤ ‖s - ((1 - ε : ℝ) : ℂ)‖ * r ^ (s.re - (1 - ε) - 1) * (q + 1 - r) := hmv
      _ ≤ ‖s - ((1 - ε : ℝ) : ℂ)‖ * r ^ (s.re - (1 - ε) - 1) * 1 := by gcongr
      _ = _ := mul_one _
  rw [norm_div, norm_mul, norm_mul, hnRa, div_le_iff₀ hzpos]
  calc r ^ (1 - ε) * r ^ (1 - ε) * ‖((r : ℝ) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)) -
        (((q + 1 : ℝ)) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ))‖
      ≤ r ^ (1 - ε) * r ^ (1 - ε) * (‖((1 - ε : ℝ) : ℂ) - s‖ * r ^ (s.re - (1 - ε) - 1)) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = (r ^ (1 - ε) * r ^ (1 - ε) * r ^ (s.re - (1 - ε) - 1)) * ‖((1 - ε : ℝ) : ℂ) - s‖ := by
        ring
    _ = r ^ (s.re - ε) * ‖((1 - ε : ℝ) : ℂ) - s‖ := by
        rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]; ring_nf

/-- The second cutoff difference `(q^s/α) r^α (q+1)^{-α}(r^α − (q+1)^α)` is `O(r^{Re s − ε})`. -/
theorem norm_twoPole_second_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {s : ℂ} (hs0 : 0 < s.re)
    {q r : ℝ}
    (hq0 : 0 < q) (hqr' : q ≤ r) (hqr : r ≤ q + 1) (hrq : q + 1 - r ≤ 1) :
    ‖((q : ℝ) : ℂ) ^ s / ((1 - ε : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) *
        (((q + 1 : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ)) *
        (((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) - (((q + 1 : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ))‖ ≤
      r ^ (s.re - ε) := by
  have hα : 0 < 1 - ε := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr'
  have hz : (((1 - ε : ℝ)) : ℂ).re ≤ 1 := by simp; linarith
  have hmv := norm_ofReal_cpow_sub_le hz hr0 le_rfl hqr
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα, Complex.ofReal_re] at hmv
  have hdiff : ‖((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) - (((q + 1 : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ)‖ ≤
      (1 - ε) * r ^ (1 - ε - 1) := by
    rw [norm_sub_rev]
    calc _ ≤ (1 - ε) * r ^ (1 - ε - 1) * (q + 1 - r) := hmv
      _ ≤ (1 - ε) * r ^ (1 - ε - 1) * 1 := by gcongr
      _ = _ := mul_one _
  have hQn : ‖(((q + 1 : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ))‖ ≤ r ^ (-(1 - ε)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [neg_re, ofReal_re]
    exact Real.rpow_le_rpow_of_nonpos hr0 hqr (by linarith)
  have hqσ : q ^ s.re ≤ r ^ s.re := Real.rpow_le_rpow hq0.le hqr' hs0.le
  rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hq0,
    Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα,
    Complex.ofReal_re]
  calc q ^ s.re / (1 - ε) * r ^ (1 - ε) * ‖(((q + 1 : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ))‖ *
        ‖((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) - (((q + 1 : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ)‖
      ≤ r ^ s.re / (1 - ε) * r ^ (1 - ε) * r ^ (-(1 - ε)) * ((1 - ε) * r ^ (1 - ε - 1)) := by
        gcongr
    _ = r ^ s.re * r ^ (1 - ε) * r ^ (-(1 - ε)) * r ^ (1 - ε - 1) := by field_simp
    _ = r ^ (s.re - ε) := by
        rw [← Real.rpow_add hr0, ← Real.rpow_add hr0, ← Real.rpow_add hr0]; ring_nf

/-- Triangle inequality for the seven pieces of the expansion. -/
theorem norm_seven_le (a b c d e f g : ℂ) :
    ‖a + b + c - d + e + f - g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_sub_le (a + b + c - d + e + f) g
  have h2 := norm_add_le (a + b + c - d + e) f
  have h3 := norm_add_le (a + b + c - d) e
  have h4 := norm_sub_le (a + b + c) d
  have h5 := norm_add_le (a + b) c
  have h6 := norm_add_le a b
  linarith

/-- The explicit rate of the two-pole expansion. -/
def powerSymbolRate (ε : ℝ) (s : ℂ) : ℝ :=
  (2 : ℝ) ^ |s.re - ε| * (‖s‖ * (1 + 1 / (1 - ε))) + partialSumRate (s + ε) +
    partialSumRate (ε : ℂ) * ((1 + 2 * ‖s‖) * (1 + 1 / s.re)) +
    ‖s‖ * (1 + 1 / (1 - ε + 1 - s.re)) + partialSumRate (ε : ℂ) + 1 + 1

/-- **The two-pole expansion of the power-row cofactor sum.** For `0 < ε < 1` and
`0 < Re s < 1 − ε`, for every `n ≥ 1`,
`‖Σ_{j ≤ n} j^{-ε}⌊n/j⌋^s − 𝓛_s n^{1−ε} − ζ(s + ε) n^s‖ ≤ K_s (√n)^{Re s − ε}`
with the explicit rate `K_s = powerSymbolRate ε s`. -/
theorem norm_powerRowCofactorSum_sub_le_rate {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) {n : ℕ} (hn : 1 ≤ n) :
    ‖powerRowCofactorSum ε s n - powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) -
        riemannZeta (s + ε) * (((n : ℝ)) : ℂ) ^ s‖ ≤
      powerSymbolRate ε s * Real.sqrt n ^ (s.re - ε) := by
  rw [powerSymbolRate]
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hα : 0 < 1 - ε := by linarith
  have hαC : ((1 - ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hw₁0 : 0 < (s + ε).re := by simp; linarith
  have hw₁1 : s + ε ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hw₂0 : 0 < (ε : ℂ).re := by simpa using hε0
  have hw₂1 : (ε : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set C₁ := partialSumRate (s + ε)
  set C₂ := partialSumRate (ε : ℂ)
  set ν : ℝ := 1 - ε + 1 - s.re
  obtain ⟨hq1, hqr, hrq, -, hr2⟩ := natSqrt_cutoff hn
  set q := Nat.sqrt n with hq
  set r := Real.sqrt n with hr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hqr1 : r ≤ (q : ℝ) + 1 := hrq.le
  have hqr2 : (q : ℝ) + 1 - r ≤ 1 := by linarith
  have hQ1C : ((((q : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < q + 1).ne'
  -- expansions of the two partial sums and of the pole sum at the cutoff
  have he₁ := norm_cpowPartialSum_sub_le hw₁0 hw₁1 hq1 hqr hqr1
  have he₂ := norm_cpowPartialSum_sub_le hw₂0 hw₂1 hq1 hqr hqr1
  have hτ := norm_powerPoleSum_sub_partial_le hα hs0 hs1 (by linarith) (q := q)
  have h1w₁ : 1 - (s + ε) = ((1 - ε : ℝ) : ℂ) - s := by push_cast; ring
  have h1w₂ : 1 - (ε : ℂ) = ((1 - ε : ℝ) : ℂ) := by push_cast; ring
  rw [h1w₁, show (s + ε).re = s.re + ε by simp] at he₁
  rw [h1w₂, show (ε : ℂ).re = ε by simp] at he₂
  have hnr : (((n : ℝ)) : ℂ) = ((r : ℝ) : ℂ) * ((r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, hr2]
  have hns : (((n : ℝ)) : ℂ) ^ s = ((r : ℝ) : ℂ) ^ s * ((r : ℝ) : ℂ) ^ s := by
    rw [hnr, Complex.mul_cpow_ofReal_nonneg hr0.le hr0.le]
  have hnα : (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) =
      ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) := by
    rw [hnr, Complex.mul_cpow_ofReal_nonneg hr0.le hr0.le]
  -- the exact algebra
  have key := twoPole_algebra (s := s) (a := ((1 - ε : ℝ) : ℂ))
    (S := powerRowCofactorSum ε s n) (P := powerPoleSum (1 - ε) s)
    (A := (((n : ℝ)) : ℂ) ^ s * cpowPartialSum (s + ε) q + powerHeadError ε s n)
    (Bs := (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) *
        ∑ k ∈ Icc 1 q, powerStep s k * (((k : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ)) +
      riemannZeta (ε : ℂ) * (((q : ℝ)) : ℂ) ^ s + powerLongError ε s n)
    (Fq := cpowPartialSum (ε : ℂ) q)
    (G := ∑ k ∈ Icc 1 q, powerStep s k * (((k : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ)))
    (P1 := cpowPartialSum (s + ε) q)
    (τ := powerPoleSum (1 - ε) s -
      ∑ m ∈ Icc 1 q, (((m : ℝ)) : ℂ) ^ s * ((mellinCell (1 - ε) m : ℝ) : ℂ) -
      ((1 - ε : ℝ) : ℂ) / (((1 - ε : ℝ) : ℂ) - s) *
        ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)))
    (e₁ := cpowPartialSum (s + ε) q - ((r : ℝ) : ℂ) ^ (((1 - ε : ℝ) : ℂ) - s) /
      (((1 - ε : ℝ) : ℂ) - s) - riemannZeta (s + ε))
    (e₂ := cpowPartialSum (ε : ℂ) q - ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) -
      riemannZeta (ε : ℂ))
    (EA := powerHeadError ε s n) (EB := powerLongError ε s n)
    (z₁ := riemannZeta (s + ε)) (z₂ := riemannZeta (ε : ℂ)) (Rs := ((r : ℝ) : ℂ) ^ s)
    (Ra := ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ)) (Rd := ((r : ℝ) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)))
    (Rb := ((r : ℝ) : ℂ) ^ (((1 - ε : ℝ) : ℂ) - s))
    (Qd := ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)))
    (Qa := ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ))
    (Qm := ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (-((1 - ε : ℝ) : ℂ))) (qs := (((q : ℝ)) : ℂ) ^ s)
    hαC (powerRowCofactorSum_eq_split hε1 hs hn) (by rw [hns]) (by rw [hnα])
    (by rw [sum_powerStep_mul_cpow_eq hs (1 - ε) q]; push_cast; ring) (by ring) (by ring)
    (by rw [← Complex.cpow_add _ _ hrC]; ring_nf)
    (by rw [← Complex.cpow_add _ _ hrC]; ring_nf)
    (by rw [← Complex.cpow_add _ _ hQ1C, add_neg_cancel, Complex.cpow_zero])
  rw [powerPoleTrace, hnα, hns, key]
  -- the seven pieces
  set X := r ^ (s.re - ε) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hr0.le _
  have hrexp : ∀ x y : ℝ, r ^ x * r ^ y = r ^ (x + y) := fun x y => (Real.rpow_add hr0 x y).symm
  have hnRs : ‖((r : ℝ) : ℂ) ^ s‖ = r ^ s.re := Complex.norm_cpow_eq_rpow_re_of_pos hr0 s
  have hnRa : ‖((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ)‖ = r ^ (1 - ε) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.ofReal_re]
  have b1 := norm_twoPole_first_le hs1 hr0 hqr1 hqr2
  have b5 := norm_twoPole_second_le hε0.le hε1 hs0 hq0 hqr hqr1 hqr2
  have b3 := norm_powerHeadError_le hε0 hε1 hs0 hs1 hn
  have b6 := norm_powerLongError_le hε0 hs0 hs1 hn
  have b2 : ‖((r : ℝ) : ℂ) ^ s * ((r : ℝ) : ℂ) ^ s *
      (cpowPartialSum (s + ε) q - ((r : ℝ) : ℂ) ^ (((1 - ε : ℝ) : ℂ) - s) /
        (((1 - ε : ℝ) : ℂ) - s) - riemannZeta (s + ε))‖ ≤ C₁ * X := by
    rw [norm_mul, norm_mul, hnRs]
    calc r ^ s.re * r ^ s.re * ‖_‖ ≤ r ^ s.re * r ^ s.re * (C₁ * r ^ (-(s.re + ε))) :=
          mul_le_mul_of_nonneg_left he₁ (by positivity)
      _ = C₁ * (r ^ s.re * r ^ s.re * r ^ (-(s.re + ε))) := by ring
      _ = C₁ * X := by rw [hrexp, hrexp, hX]; ring_nf
  have b4 : ‖((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) /
      ((1 - ε : ℝ) : ℂ) * (powerPoleSum (1 - ε) s -
        ∑ m ∈ Icc 1 q, (((m : ℝ)) : ℂ) ^ s * ((mellinCell (1 - ε) m : ℝ) : ℂ) -
        ((1 - ε : ℝ) : ℂ) / (((1 - ε : ℝ) : ℂ) - s) *
          ((((q : ℝ) + 1 : ℝ)) : ℂ) ^ (s - ((1 - ε : ℝ) : ℂ)))‖ ≤ ‖s‖ * (1 + 1 / ν) * X := by
    have hQν : ((q + 1 : ℕ) : ℝ) ^ (-ν) ≤ r ^ (-ν) := by
      push_cast
      exact Real.rpow_le_rpow_of_nonpos hr0 hqr1 (by simp only [ν]; linarith)
    rw [norm_mul, norm_div, norm_mul, hnRa, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    calc r ^ (1 - ε) * r ^ (1 - ε) / (1 - ε) * ‖_‖
        ≤ r ^ (1 - ε) * r ^ (1 - ε) / (1 - ε) * ((1 - ε) * ‖s‖ * ((1 + 1 / ν) * r ^ (-ν))) := by
          refine mul_le_mul_of_nonneg_left (hτ.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQν (by
            have : 0 < ν := by simp only [ν]; linarith
            positivity)) (by positivity)
      _ = ‖s‖ * (1 + 1 / ν) * (r ^ (1 - ε) * r ^ (1 - ε) * r ^ (-ν)) := by field_simp
      _ = ‖s‖ * (1 + 1 / ν) * X := by rw [hrexp, hrexp, hX]; simp only [ν]; ring_nf
  have b7 : ‖(((q : ℝ)) : ℂ) ^ s * (cpowPartialSum (ε : ℂ) q -
      ((r : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) / ((1 - ε : ℝ) : ℂ) - riemannZeta (ε : ℂ))‖ ≤ C₂ * X := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    have hqσ : (q : ℝ) ^ s.re ≤ r ^ s.re := Real.rpow_le_rpow hq0.le hqr hs0.le
    calc (q : ℝ) ^ s.re * ‖_‖ ≤ r ^ s.re * (C₂ * r ^ (-ε)) :=
          mul_le_mul hqσ he₂ (norm_nonneg _) (by positivity)
      _ = C₂ * (r ^ s.re * r ^ (-ε)) := by ring
      _ = C₂ * X := by rw [hrexp, hX]; ring_nf
  refine (norm_seven_le _ _ _ _ _ _ _).trans ?_
  have hsum : (2 : ℝ) ^ |s.re - ε| * (‖s‖ * (1 + 1 / (1 - ε))) * X + C₁ * X +
      C₂ * ((1 + 2 * ‖s‖) * (1 + 1 / s.re)) * X + ‖s‖ * (1 + 1 / ν) * X + C₂ * X + X + X =
      ((2 : ℝ) ^ |s.re - ε| * (‖s‖ * (1 + 1 / (1 - ε))) + C₁ +
        C₂ * ((1 + 2 * ‖s‖) * (1 + 1 / s.re)) + ‖s‖ * (1 + 1 / ν) + C₂ + 1 + 1) * X := by ring
  rw [← hsum]
  linarith only [b1, b2, b3, b4, b5, b6, b7]

/-- Existential form of the two-pole expansion. -/
theorem norm_powerRowCofactorSum_sub_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖powerRowCofactorSum ε s n - powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((1 - ε : ℝ) : ℂ) -
          riemannZeta (s + ε) * (((n : ℝ)) : ℂ) ^ s‖ ≤ K * Real.sqrt n ^ (s.re - ε) :=
  ⟨powerSymbolRate ε s, fun _ hn => norm_powerRowCofactorSum_sub_le_rate hε0 hε1 hs0 hs1 hn⟩

/-! ### The symbol of the renormalized cofactor operator -/

/-- The real power row `n ↦ Re(a n^s)`. -/
def powerRow (a s : ℂ) (n : ℕ) : ℝ := (a * (((n : ℝ)) : ℂ) ^ s).re

theorem powerRow_zero (a : ℂ) {s : ℂ} (hs : s ≠ 0) : powerRow a s 0 = 0 := by
  simp [powerRow, Complex.zero_cpow hs]

/-- The Mellin trace series of a power row is the real part of `a` times the complex pole sum. -/
theorem hasSum_powerRow_mul_mellinCell {α : ℝ} (hα : 0 < α) (a : ℂ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < α) :
    HasSum (fun n => powerRow a s n * mellinCell α n) (a * powerPoleSum α s).re := by
  have h := Complex.hasSum_re ((summable_powerPoleSum hα hs0 hs1).hasSum.mul_left a)
  convert h using 1
  · funext n
    simp only [powerRow, ← mul_assoc, Complex.re_mul_ofReal]
  · rfl

/-- Power rows with `0 < Re s < 1 − ε` lie in the absolute pole-trace domain. -/
theorem powerRow_mem_poleTraceDomain (ε : SubcriticalDamping) (a : ℂ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) : powerRow a s ∈ poleTraceDomain ε := by
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  exact ⟨powerRow_zero a hs,
    (hasSum_powerRow_mul_mellinCell (by linarith [ε.property.2]) a hs0 hs1).summable⟩

/-- The power row as a vector of the trace domain. -/
def powerTraceVector (ε : SubcriticalDamping) (a : ℂ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) : poleTraceDomain ε :=
  ⟨powerRow a s, powerRow_mem_poleTraceDomain ε a hs0 hs1⟩

/-- The linear pole trace of a power row is `Re(a 𝓛_s)`. -/
theorem poleTrace_powerTraceVector (ε : SubcriticalDamping) (a : ℂ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 - ε) :
    poleTrace ε (powerTraceVector ε a hs0 hs1) = (a * powerPoleTrace ε s).re := by
  have hα : 0 < 1 - (ε : ℝ) := by linarith [ε.property.2]
  change (∑' n, powerRow a s n * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)) = _
  rw [(hasSum_powerRow_mul_mellinCell hα a hs0 hs1).tsum_eq, powerPoleTrace, mul_div_assoc',
    Complex.div_ofReal_re]

/-- On a power row, `(I + D̃)v(n) = Re(a(S(n) − 𝓛_s n^{1−ε}))` for `n ≥ 1`. -/
theorem powerRow_add_renormalizedCofactorOperator (ε : SubcriticalDamping) (a : ℂ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) {n : ℕ} (hn : 1 ≤ n) :
    powerRow a s n + renormalizedCofactorOperator ε (powerTraceVector ε a hs0 hs1) n =
      (a * (powerRowCofactorSum ε s n -
        powerPoleTrace ε s * (((n : ℝ)) : ℂ) ^ ((1 - (ε : ℝ) : ℝ) : ℂ))).re := by
  change powerRow a s n + ((∑ j ∈ Icc 2 n, (j : ℝ) ^ (-(ε : ℝ)) * powerRow a s (n / j)) -
    poleTrace ε (powerTraceVector ε a hs0 hs1) * (n : ℝ) ^ (1 - (ε : ℝ))) = _
  rw [poleTrace_powerTraceVector, mul_sub, Complex.sub_re, powerRowCofactorSum, mul_sum,
    Complex.re_sum, ← Finset.add_sum_Ioc_eq_sum_Icc hn]
  have hIoc : Ioc 1 n = Icc 2 n := by ext j; simp only [mem_Ioc, mem_Icc]; omega
  have hpow : (((n : ℝ)) : ℂ) ^ ((1 - (ε : ℝ) : ℝ) : ℂ) = (((n : ℝ) ^ (1 - (ε : ℝ)) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow (Nat.cast_nonneg n) _).symm
  have hterm : ∀ j : ℕ, (a * ((((j : ℝ)) : ℂ) ^ (-((ε : ℝ) : ℂ)) *
      ((((n / j : ℕ) : ℝ)) : ℂ) ^ s)).re = (j : ℝ) ^ (-(ε : ℝ)) * powerRow a s (n / j) := by
    intro j
    rw [show (-((ε : ℝ) : ℂ)) = (((-(ε : ℝ)) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (Nat.cast_nonneg j), powerRow, mul_left_comm, Complex.re_ofReal_mul]
  rw [hIoc, hterm, Nat.cast_one, Real.one_rpow, one_mul, Nat.div_one, hpow, ← mul_assoc,
    Complex.re_mul_ofReal]
  simp only [hterm]
  ring

/-- **The symbol law of the renormalized cofactor.** For `0 < Re s < 1 − ε` and every `a`,
`(I + D̃) Re(a n^s) = Re(a ζ(s + ε) n^s)` up to a row of uniformly bounded pronic energy:
on power rows `D̃` acts as multiplication by `ζ(s + ε) − 1`. -/
theorem exists_pronicNorm_powerRow_symbol_le (ε : SubcriticalDamping) (a : ℂ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerRow a s n +
      renormalizedCofactorOperator ε (powerTraceVector ε a hs0 hs1) n -
        powerRow (a * riemannZeta (s + (ε : ℝ))) s n) ≤ B := by
  obtain ⟨K, hK⟩ := norm_powerRowCofactorSum_sub_le ε.property.1
    (by linarith [ε.property.2]) hs0 hs1
  have hε' : 0 < 1 - s.re + ε := by linarith [ε.property.1]
  refine ⟨Real.sqrt ((‖a‖ * K) ^ 2 * (1 + 1 / (1 - s.re + ε))), fun T => ?_⟩
  refine Real.sqrt_le_sqrt (TransHorizonIncidenceMechanics.sum_sq_le_of_abs_le_sqrt_rpow hε'
    (fun n hn => ?_) T)
  rw [powerRow_add_renormalizedCofactorOperator ε a hs0 hs1 hn, powerRow, ← Complex.sub_re,
    mul_assoc, ← mul_sub, show 1 - (1 - s.re + ε) = s.re - ε by ring]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK n hn) (norm_nonneg _)

/-! ### Power rows of positive critical exponent carry unbounded energy -/

/-- **Energy of an oscillating power.** If `Re s ≥ 1/2`, `b ≠ 0`, and `Re b ≠ 0` when `s` is
real, then `n ↦ Re(b n^s)` has unbounded pronic energy: it dominates
`Σ Re(b n^{iγ})²/(2n) = (|b|²/4) H_T + O(1)` for `γ ≠ 0`, and `(Re b)² H_T/2` for `γ = 0`. -/
theorem not_exists_pronicNorm_powerRow_le {b s : ℂ} (hs : 1 / 2 ≤ s.re) (hb : b ≠ 0)
    (hreal : s.im = 0 → b.re ≠ 0) : ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (powerRow b s) ≤ B := by
  rintro ⟨B, hB⟩
  set t := s.im with ht
  set u : ℕ → ℝ := fun n => (b * (((n : ℝ)) : ℂ) ^ ((t : ℂ) * I)).re with hu
  have hsplit : ∀ n : ℕ, 1 ≤ n → powerRow b s n = (n : ℝ) ^ s.re * u n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs' : s = ((s.re : ℝ) : ℂ) + (t : ℂ) * I := (Complex.re_add_im s).symm
    have h1 : (((n : ℝ)) : ℂ) ^ s = (((n : ℝ) ^ s.re : ℝ) : ℂ) * (((n : ℝ)) : ℂ) ^ ((t : ℂ) * I) := by
      conv_lhs => rw [hs']
      rw [Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'), Complex.ofReal_cpow hn0.le]
    simp only [powerRow, hu]
    rw [h1, mul_left_comm, Complex.re_ofReal_mul]
  have hlow : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * B ^ 2 := by
    intro T
    have hB0 : 0 ≤ B := (pronicNorm_nonneg T _).trans (hB T)
    have hsq : ∑ n ∈ Icc 1 T, powerRow b s n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ B ^ 2 := by
      rw [← BezoutValuationIncidence.pronicNorm_sq]
      exact pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB T) 2
    have hterm : ∀ n ∈ Icc 1 T, u n ^ 2 / n ≤
        2 * (powerRow b s n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpow : (n : ℝ) ≤ ((n : ℝ) ^ s.re) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ (s.re * ((2 : ℕ) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
      rw [hsplit n hn1, mul_pow, div_le_iff₀ hn0, mul_comm 2, mul_assoc,
        div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have hu2 : 0 ≤ u n ^ 2 := sq_nonneg _
      calc u n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ u n ^ 2 * (2 * (n : ℝ) * n) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hu2
        _ = ((n : ℝ) * u n ^ 2) * (2 * n) := by ring
        _ ≤ (((n : ℝ) ^ s.re) ^ 2 * u n ^ 2) * (2 * n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hu2) (by positivity)
    calc _ ≤ ∑ n ∈ Icc 1 T, 2 * (powerRow b s n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) :=
          sum_le_sum hterm
      _ = 2 * ∑ n ∈ Icc 1 T, powerRow b s n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by rw [mul_sum]
      _ ≤ 2 * B ^ 2 := by linarith
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- real exponent: `u ≡ Re b`
    have hu0 : ∀ n : ℕ, u n = b.re := fun n => by simp [hu, ht0]
    have hbre : b.re ≠ 0 := hreal ht0
    obtain ⟨T, -, hT⟩ :=
      TransHorizonIncidenceMechanics.not_bddAbove_sum_Icc_one_div (2 * B ^ 2 / b.re ^ 2)
    have h := hlow T
    have heq : ∑ n ∈ Icc 1 T, u n ^ 2 / n = b.re ^ 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hu0]; ring
    rw [heq] at h
    have hb2 : 0 < b.re ^ 2 := by positivity
    rw [div_lt_iff₀ hb2] at hT
    linarith
  · -- oscillating exponent: the cross term is bounded
    have husq : ∀ n : ℕ, 1 ≤ n → u n ^ 2 =
        (‖b‖ ^ 2 + (b ^ 2 * (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I)).re) / 2 := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      set z := b * (((n : ℝ)) : ℂ) ^ ((t : ℂ) * I) with hz
      have hw : ‖(((n : ℝ)) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
      have hz2 : z ^ 2 = b ^ 2 * (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I) := by
        rw [hz, mul_pow, sq ((((n : ℝ)) : ℂ) ^ ((t : ℂ) * I)),
          ← Complex.cpow_add _ _ (by exact_mod_cast hn0.ne')]
        push_cast; ring_nf
      have hnorm : ‖z‖ ^ 2 = ‖b‖ ^ 2 := by rw [hz, norm_mul, hw, mul_one]
      have hre : ∀ x : ℂ, x.re ^ 2 = (‖x‖ ^ 2 + (x ^ 2).re) / 2 := fun x => by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq x, Complex.mul_re]; ring
      show z.re ^ 2 = _
      rw [hre z, hnorm, hz2]
    have hsum : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n =
        ‖b‖ ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) +
          (b ^ 2 * ∑ n ∈ Icc 1 T, (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I) / (((n : ℝ)) : ℂ)).re / 2 := by
      intro T
      rw [mul_sum, mul_sum, Complex.re_sum, sum_div, ← sum_add_distrib]
      refine sum_congr rfl fun n hn => ?_
      have hn1 := (mem_Icc.mp hn).1
      have hdiv : (b ^ 2 * ((((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I) / (((n : ℝ)) : ℂ))).re =
          (b ^ 2 * (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I)).re / n := by
        rw [← mul_div_assoc, Complex.div_ofReal_re]
      rw [husq n hn1, hdiv]
      ring
    set w : ℂ := 1 - ((2 * t : ℝ) : ℂ) * I with hw
    have hwre : 0 < w.re := by simp [hw]
    have hwne : w ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [hw] at this
      exact ht0 this
    set B₂ := 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w with hB₂
    have hS : ∀ T : ℕ, 1 ≤ T →
        ‖∑ n ∈ Icc 1 T, (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I) / (((n : ℝ)) : ℂ)‖ ≤ B₂ := by
      intro T hT
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      have hcp : ∑ n ∈ Icc 1 T, (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I) / (((n : ℝ)) : ℂ) =
          cpowPartialSum w T := by
        rw [cpowPartialSum]
        refine sum_congr rfl fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hnC : (((n : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
        rw [hw, show -(1 - ((2 * t : ℝ) : ℂ) * I) = ((2 * t : ℝ) : ℂ) * I - 1 by ring,
          Complex.cpow_sub _ _ hnC, Complex.cpow_one]
      have h := norm_cpowPartialSum_sub_le hwre hwne hT le_rfl (by linarith)
      rw [show (1 : ℂ) - w = ((2 * t : ℝ) : ℂ) * I by rw [hw]; ring] at h
      have hT1 : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
      have hTpow : (T : ℝ) ^ (-w.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by linarith)
      have hrate0 := partialSumRate_nonneg hwre
      rw [hcp]
      have e : cpowPartialSum w T = ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
          (((2 * t : ℝ) : ℂ) * I) + riemannZeta w +
          (cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
            (((2 * t : ℝ) : ℂ) * I) - riemannZeta w) := by ring
      calc ‖cpowPartialSum w T‖ ≤ ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
            (((2 * t : ℝ) : ℂ) * I)‖ + ‖riemannZeta w‖ +
            ‖cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
              (((2 * t : ℝ) : ℂ) * I) - riemannZeta w‖ :=
            (congrArg norm e).le.trans
              ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
        _ ≤ 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w * 1 := by
            rw [norm_div, hT1]
            gcongr
            exact h.trans (mul_le_mul_of_nonneg_left hTpow hrate0)
        _ = B₂ := by rw [mul_one]
    have hnb : 0 < ‖b‖ ^ 2 := by positivity
    obtain ⟨T, hT1, hT⟩ := TransHorizonIncidenceMechanics.not_bddAbove_sum_Icc_one_div
      ((4 * B ^ 2 + ‖b‖ ^ 2 * B₂) / ‖b‖ ^ 2)
    have h := hlow T
    rw [hsum T] at h
    have hre : |(b ^ 2 * ∑ n ∈ Icc 1 T,
        (((n : ℝ)) : ℂ) ^ ((2 * t : ℝ) * I) / (((n : ℝ)) : ℂ)).re| ≤ ‖b‖ ^ 2 * B₂ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hS T hT1) (by positivity)
    rw [div_lt_iff₀ hnb] at hT
    have := (abs_le.mp hre).1
    nlinarith

/-! ### Power-row eigenstates of the cofactor are translated zeros -/

/-- `ζ` is real on the real axis. -/
theorem riemannZeta_ofReal_im (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have h := riemannZeta_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- **Power-row eigenstates of the renormalized cofactor are exactly the translated zeros.**
For `1/2 ≤ Re s < 1 − ε`, `a ≠ 0` (with `Re a ≠ 0` if `s` is real), the power row
`Re(a n^s)` satisfies the renormalized inversion law — `v + D̃v` has bounded pronic energy,
the approximate eigenrelation `D̃v ≈ −v` — if and only if `ζ(s + ε) = 0`. -/
theorem powerRow_renormalizedInversion_bounded_iff (ε : SubcriticalDamping) {s : ℂ}
    (hs0 : 1 / 2 ≤ s.re) (hs1 : s.re < 1 - ε) {a : ℂ} (ha : a ≠ 0) (hreal : s.im = 0 → a.re ≠ 0) :
    (∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerRow a s n +
        renormalizedCofactorOperator ε (powerTraceVector ε a (by linarith) hs1) n) ≤ B) ↔
      riemannZeta (s + (ε : ℝ)) = 0 := by
  have hs0' : 0 < s.re := by linarith
  obtain ⟨B₁, hB₁⟩ := exists_pronicNorm_powerRow_symbol_le ε a hs0' hs1
  constructor
  · rintro ⟨B, hB⟩
    by_contra hz
    have hb : a * riemannZeta (s + (ε : ℝ)) ≠ 0 := mul_ne_zero ha hz
    have hbre : s.im = 0 → (a * riemannZeta (s + (ε : ℝ))).re ≠ 0 := by
      intro him
      have hsreal : s + (ε : ℝ) = ((s.re + ε : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hzim : (riemannZeta (s + (ε : ℝ))).im = 0 := by
        rw [hsreal]; exact riemannZeta_ofReal_im _
      have hzre : (riemannZeta (s + (ε : ℝ))).re < 0 := by
        rw [hsreal]
        have h := TransHorizonIncidenceMechanics.riemannZeta_re_le_of_lt_one
          (σ := s.re + ε) (by linarith [ε.property.1]) (by linarith)
        have : -(s.re + ε) / (1 - (s.re + ε)) < 0 :=
          div_neg_of_neg_of_pos (by linarith [ε.property.1]) (by linarith)
        linarith
      rw [Complex.mul_re, hzim, mul_zero, sub_zero]
      exact mul_ne_zero (hreal him) hzre.ne
    refine not_exists_pronicNorm_powerRow_le hs0 hb hbre ⟨B + B₁, fun T => ?_⟩
    have h := BezoutValuationIncidence.pronicNorm_add_le T
      (fun n => powerRow a s n + renormalizedCofactorOperator ε (powerTraceVector ε a hs0' hs1) n)
      (fun n => -(powerRow a s n + renormalizedCofactorOperator ε (powerTraceVector ε a hs0' hs1) n -
        powerRow (a * riemannZeta (s + (ε : ℝ))) s n))
    have hneg : pronicNorm T (fun n => -(powerRow a s n +
        renormalizedCofactorOperator ε (powerTraceVector ε a hs0' hs1) n -
        powerRow (a * riemannZeta (s + (ε : ℝ))) s n)) =
        pronicNorm T (fun n => powerRow a s n +
          renormalizedCofactorOperator ε (powerTraceVector ε a hs0' hs1) n -
          powerRow (a * riemannZeta (s + (ε : ℝ))) s n) := by
      simp only [BezoutValuationIncidence.pronicNorm, neg_sq]
    have heq : (fun n => powerRow a s n +
        renormalizedCofactorOperator ε (powerTraceVector ε a hs0' hs1) n +
        -(powerRow a s n + renormalizedCofactorOperator ε (powerTraceVector ε a hs0' hs1) n -
          powerRow (a * riemannZeta (s + (ε : ℝ))) s n)) =
        powerRow (a * riemannZeta (s + (ε : ℝ))) s := by
      funext n; ring
    rw [heq, hneg] at h
    linarith [hB T, hB₁ T]
  · intro hz
    refine ⟨B₁, fun T => ?_⟩
    have h := hB₁ T
    simp only [hz, mul_zero, powerRow, zero_mul, Complex.zero_re, sub_zero] at h
    exact h

/-- **Real power rows are never cofactor eigenstates.** For real `1/2 ≤ σ < 1 − ε`, the row
`n^σ` violates the renormalized inversion law at every subcritical damping, because `ζ < 0` on
`(0, 1)`: a real-exponent escape profile is excluded by the source. -/
theorem not_realPowerRow_renormalizedInversion_bounded (ε : SubcriticalDamping) {σ : ℝ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ < 1 - ε) :
    ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => powerRow 1 (σ : ℂ) n +
      renormalizedCofactorOperator ε
        (powerTraceVector ε 1 (s := (σ : ℂ)) (by simp; linarith) (by simpa using hσ1)) n) ≤ B := by
  intro h
  have hiff := powerRow_renormalizedInversion_bounded_iff ε (s := (σ : ℂ)) (by simpa using hσ0)
    (by simpa using hσ1) one_ne_zero (fun _ => by simp)
  have hz := hiff.mp h
  have hσε : ((σ : ℂ) + (ε : ℝ)) = ((σ + ε : ℝ) : ℂ) := by push_cast; ring
  rw [hσε] at hz
  have h' := TransHorizonIncidenceMechanics.riemannZeta_re_le_of_lt_one
    (σ := σ + ε) (by linarith [ε.property.1]) (by linarith)
  rw [hz, Complex.zero_re] at h'
  have : -(σ + ε) / (1 - (σ + ε)) < 0 :=
    div_neg_of_neg_of_pos (by linarith [ε.property.1]) (by linarith)
  linarith

end GaloisForLFunctions.ArithmeticDefectRigidity
