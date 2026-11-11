import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheLogarithmicMomentsOfTheRowOfTheFlatTailAreSumsOverTheZeros
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCorFourSix

/-!
# The Laguerre tails of the comb tend to the Li coefficients

The Li ladder on the comb, without damping and without smoothing. For the Laguerre polynomial
`P_n(x) = Σ_{k<n} C(n, k+1) (−x)^k/k!` and the tail `c_m = P_n(log(N/m))`, `1 ≤ m ≤ N`,

`(2 d₁ d₂ − D·D)(c) / N → Re 2λ_n`   (`tendsto_combForm_laguerreTail_div`),

with `2λ_n = Σ_ρ (2 − w_ρ^n − w_ρ^{−n})`, `w_ρ = 1 − 1/ρ`, the paired Li coefficient. The flat tail
is `n = 1`.

More generally Weil's form of two logarithmic tails has the limit
(`tendsto_logTailForm_div_zeroMoment`)

`𝔚_{[1,N]}(log^k(N/·), log^l(N/·)) / N → k! l! Re Σ_ρ ρ^{−k−1} (1 − ρ)^{−l−1}`:

a tail with profile `φ(m/N)` pairs through the Mellin transform of `φ` at `ρ` and at `1 − ρ`.

The proof has no explicit formula for a test function with a jump and unbounded support.
* The scaling recursion reduces all pairs `(k, l)` to the pairings with the flat tail.
* The row of the flat tail is the remainder of the prime number theorem plus the jets; its
  logarithmic moments exist by the prime number theorem with error and are sums over the zeros.
* `V(k, l) = Σ_ρ ρ^{−k−1}(1−ρ)^{−l−1}` obeys `V(k, l) = V(k−1, l) + V(k, l−1)` because
  `ρ + (1 − ρ) = 1`, and `V(k, l) = V(l, k)` because the zeros are symmetric under `ρ ↦ 1 − ρ`:
  the recursion of the comb.
* `Σ_{k<n} C(n,k+1)(−1)^k z^{−k−1} = 1 − (1 − 1/z)^n`, and `1 − 1/(1 − ρ) = w_ρ^{−1}`.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower (XiZeroCopy xi)

open HodgeTheoryOfAFixedPart (formBilin tailRow chebyshev)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-! ### The moments of the zeros -/

/-- The term `ρ^{−k−1} (1 − ρ)^{−l−1}` of a zero. -/
def zeroMomentTerm (k l : ℕ) (q : XiZeroCopy) : ℂ :=
  1 / ((q.1 : ℂ) ^ (k + 1) * (1 - (q.1 : ℂ)) ^ (l + 1))

/-- `V(k, l) = Σ_ρ ρ^{−k−1} (1 − ρ)^{−l−1}`. -/
def zeroMoment (k l : ℕ) : ℂ := ∑' q : XiZeroCopy, zeroMomentTerm k l q

theorem norm_zeroMomentTerm_le (k l : ℕ) (q : XiZeroCopy) :
    ‖zeroMomentTerm k l q‖ ≤ 1 / RHTower.xiCopyOrdinate q ^ 2 := by
  have hγ := RHTower.four_lt_abs_xiCopyOrdinate q
  have hγ0 : 0 < |RHTower.xiCopyOrdinate q| := by linarith
  have him : ((q.1 : ℂ)).im = RHTower.xiCopyOrdinate q := rfl
  have h1 : |RHTower.xiCopyOrdinate q| ≤ ‖(q.1 : ℂ)‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h2 : |RHTower.xiCopyOrdinate q| ≤ ‖1 - (q.1 : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, him] at h
    exact h
  have h1' : ‖(q.1 : ℂ)‖ ≤ ‖(q.1 : ℂ)‖ ^ (k + 1) :=
    le_self_pow₀ (by linarith) (Nat.succ_ne_zero k)
  have h2' : ‖1 - (q.1 : ℂ)‖ ≤ ‖1 - (q.1 : ℂ)‖ ^ (l + 1) :=
    le_self_pow₀ (by linarith) (Nat.succ_ne_zero l)
  have hpos : 0 < ‖(q.1 : ℂ)‖ ^ (k + 1) * ‖1 - (q.1 : ℂ)‖ ^ (l + 1) :=
    mul_pos (pow_pos (lt_of_lt_of_le hγ0 h1) _) (pow_pos (lt_of_lt_of_le hγ0 h2) _)
  have hsq : 0 < RHTower.xiCopyOrdinate q ^ 2 := by
    rw [← sq_abs]
    exact pow_pos hγ0 2
  rw [zeroMomentTerm, norm_div, norm_one, norm_mul, norm_pow, norm_pow,
    div_le_div_iff₀ hpos hsq, one_mul, one_mul]
  calc RHTower.xiCopyOrdinate q ^ 2
      = |RHTower.xiCopyOrdinate q| * |RHTower.xiCopyOrdinate q| := by rw [← sq, sq_abs]
    _ ≤ ‖(q.1 : ℂ)‖ ^ (k + 1) * ‖1 - (q.1 : ℂ)‖ ^ (l + 1) :=
        mul_le_mul (h1.trans h1') (h2.trans h2') hγ0.le (pow_nonneg (norm_nonneg _) _)

theorem summable_zeroMomentTerm (k l : ℕ) : Summable (zeroMomentTerm k l) :=
  Summable.of_norm_bounded RHTower.summable_inv_sq_xiCopyOrdinate (norm_zeroMomentTerm_le k l)

/-- **The recursion of the zeros**: `V(k+1, l+1) = V(k, l+1) + V(k+1, l)`, from
`ρ + (1 − ρ) = 1`. -/
theorem zeroMoment_succ_succ (k l : ℕ) :
    zeroMoment (k + 1) (l + 1) = zeroMoment k (l + 1) + zeroMoment (k + 1) l := by
  rw [zeroMoment, zeroMoment, zeroMoment,
    ← (summable_zeroMomentTerm k (l + 1)).tsum_add (summable_zeroMomentTerm (k + 1) l)]
  refine tsum_congr fun q => ?_
  have hρ : (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_ne_zero q
  have h1 : (1 : ℂ) - (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_one_sub_ne_zero q
  rw [zeroMomentTerm, zeroMomentTerm, zeroMomentTerm]
  field_simp
  ring

/-- **The symmetry of the zeros**: `V(k, l) = V(l, k)`, from `ρ ↦ 1 − ρ`. -/
theorem zeroMoment_comm (k l : ℕ) : zeroMoment k l = zeroMoment l k := by
  rw [zeroMoment, zeroMoment, ← RHTower.xiZeroCopyReflectEquiv.tsum_eq (zeroMomentTerm l k)]
  refine tsum_congr fun q => ?_
  rw [zeroMomentTerm, zeroMomentTerm, RHTower.xiZeroCopy_reflect_val, sub_sub_cancel, mul_comm]

/-- The moments of the row of the flat tail are the moments `V(0, j)` of the zeros. -/
theorem rowMoment_eq_zeroMoment (j : ℕ) : rowMoment j = j.factorial * (zeroMoment 0 j).re := by
  have h := congrArg Complex.re (rowMoment_eq_tsum j)
  have hcast : ((j.factorial : ℕ) : ℂ) = ((j.factorial : ℝ) : ℂ) := by push_cast; rfl
  have hsum : ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)) ^ (j + 1)) = zeroMoment 0 j := by
    rw [zeroMoment]
    refine tsum_congr fun q => ?_
    rw [zeroMomentTerm, zero_add, pow_one]
  rw [Complex.ofReal_re, hsum, hcast, Complex.re_ofReal_mul] at h
  exact h

/-! ### The limits of the forms of logarithmic tails -/

/-- The limit of Weil's form of two logarithmic tails per degree point. -/
def logTailLimit (k l : ℕ) : ℝ := k.factorial * l.factorial * (zeroMoment k l).re

theorem logTailLimit_symm (k : ℕ) : logTailLimit k 0 = logTailLimit 0 k := by
  rw [logTailLimit, logTailLimit, zeroMoment_comm]
  ring

theorem logTailLimit_succ_succ (k l : ℕ) :
    logTailLimit (k + 1) (l + 1) =
      ((k : ℝ) + 1) * logTailLimit k (l + 1) + ((l : ℝ) + 1) * logTailLimit (k + 1) l := by
  rw [logTailLimit, logTailLimit, logTailLimit, zeroMoment_succ_succ, Complex.add_re,
    Nat.factorial_succ k, Nat.factorial_succ l]
  push_cast
  ring

/-- **The pairings with the flat tail**: the row against a logarithmic profile, per degree
point, tends to the moment of the row. -/
theorem tendsto_logTailForm_zero_left (j : ℕ) :
    Tendsto (fun N : ℕ => logTailForm 0 j N / N) atTop (𝓝 (logTailLimit 0 j)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- the flat tail with itself
    have hval : logTailLimit 0 0 =
        2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
      have h := RHTower.tsum_inv_zero_mul_one_sub_zero_re
      rw [RHTower.poleSharpConstant] at h
      rw [logTailLimit, zeroMoment, ← h]
      have hterm : ∀ q : XiZeroCopy, zeroMomentTerm 0 0 q =
          (1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := fun q => by
        rw [zeroMomentTerm, zero_add, pow_one, pow_one]
      rw [tsum_congr hterm]
      simp
    rw [hval]
    refine HodgeTheoryOfAFixedPart.tendsto_combForm_flatTail_div.congr fun N => ?_
    have h : logTail 0 N = fun _ => 1 := funext fun m => pow_zero _
    rw [logTailForm, h, HodgeTheoryOfAFixedPart.formBilin_self]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hval : logTailLimit 0 (i + 1) = primeMoment (i + 1) + archMoment (i + 1) := by
      rw [← rowMoment_eq, rowMoment_eq_zeroMoment, logTailLimit]
      simp
    rw [hval]
    refine ((tendsto_sum_logTail_mul_primeRemainder (i + 1)).add
      (tendsto_sum_logTail_mul_jetRow i)).congr fun N => ?_
    rw [logTailForm_zero_left, ← add_div, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [tailRow_eq]
    ring

/-- **Weil's form of two logarithmic tails**, per degree point:
`𝔚_{[1,N]}(log^k(N/·), log^l(N/·)) / N → k! l! Re Σ_ρ ρ^{−k−1} (1 − ρ)^{−l−1}`. -/
theorem tendsto_logTailForm_div_zeroMoment (k l : ℕ) :
    Tendsto (fun N : ℕ => logTailForm k l N / N) atTop
      (𝓝 (k.factorial * l.factorial * (zeroMoment k l).re)) :=
  tendsto_logTailForm_div logTailLimit tendsto_logTailForm_zero_left logTailLimit_symm
    logTailLimit_succ_succ k l

/-! ### The Laguerre tails -/

/-- The coefficients of the Laguerre polynomial `P_n(x) = Σ_{k<n} C(n, k+1) (−x)^k/k!`. -/
def laguerreCoeff (n k : ℕ) : ℝ := (n.choose (k + 1) : ℝ) * (-1) ^ k / k.factorial

/-- The Laguerre tail of degree `n` at scale `N`: `m ↦ P_n(log(N/m))`. -/
def laguerreTail (n N m : ℕ) : ℝ := polyLogTail n (laguerreCoeff n) N m

theorem laguerreTail_apply (n N m : ℕ) :
    laguerreTail n N m = ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * (-1) ^ k / k.factorial * Real.log ((N : ℝ) / m) ^ k := rfl

/-- `Σ_{k<n} C(n, k+1) (−1)^k z^{−k−1} = 1 − (1 − 1/z)^n`. -/
theorem sum_choose_succ_mul_inv_pow (n : ℕ) (z : ℂ) :
    ∑ k ∈ range n, ((n.choose (k + 1) : ℂ) * (-1) ^ k) * (1 / z ^ (k + 1)) =
      1 - (1 - 1 / z) ^ n := by
  have h := add_pow (-(1 / z)) (1 : ℂ) n
  rw [Finset.sum_range_succ'] at h
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one] at h
  have h' : (1 - 1 / z) ^ n =
      ∑ k ∈ range n, (-(1 / z)) ^ (k + 1) * (n.choose (k + 1) : ℂ) + 1 := by
    rw [← h]
    ring
  have hS : ∑ k ∈ range n, (-(1 / z)) ^ (k + 1) * (n.choose (k + 1) : ℂ) =
      -∑ k ∈ range n, ((n.choose (k + 1) : ℂ) * (-1) ^ k) * (1 / z ^ (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow, one_div_pow, pow_succ (-1 : ℂ) k]
    ring
  rw [h', hS]
  ring

/-- The two Laguerre sums at a zero multiply to the paired Li summand. -/
theorem laguerre_product_eq_liTerm (n : ℕ) (q : XiZeroCopy) :
    (1 - (1 - 1 / (q.1 : ℂ)) ^ n) * (1 - (1 - 1 / (1 - (q.1 : ℂ))) ^ n) =
      RHTower.liTerm (RHTower.xiRootW (q.1 : ℂ)) n := by
  have hρ : (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_ne_zero q
  have h1 : (1 : ℂ) - (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_one_sub_ne_zero q
  have hw : RHTower.xiRootW (q.1 : ℂ) = 1 - 1 / (q.1 : ℂ) := rfl
  have hprod : (1 - 1 / (q.1 : ℂ)) * (1 - 1 / (1 - (q.1 : ℂ))) = 1 := by
    field_simp
    ring
  have hwinv : (RHTower.xiRootW (q.1 : ℂ))⁻¹ = 1 - 1 / (1 - (q.1 : ℂ)) := by
    rw [hw]
    exact inv_eq_of_mul_eq_one_right hprod
  have hpow : (1 - 1 / (q.1 : ℂ)) ^ n * (1 - 1 / (1 - (q.1 : ℂ))) ^ n = 1 := by
    rw [← mul_pow, hprod, one_pow]
  rw [RHTower.liTerm, hwinv, hw]
  linear_combination hpow

/-- **The Laguerre combination of the moments of the zeros is the paired Li coefficient.** -/
theorem sum_laguerre_zeroMoment (n : ℕ) :
    ∑ k ∈ range n, ∑ l ∈ range n,
        (((n.choose (k + 1) : ℂ) * (-1) ^ k) * ((n.choose (l + 1) : ℂ) * (-1) ^ l)) *
          zeroMoment k l = RHTower.xiLiPaired n := by
  have h1 : HasSum (fun q : XiZeroCopy => ∑ k ∈ range n, ∑ l ∈ range n,
      (((n.choose (k + 1) : ℂ) * (-1) ^ k) * ((n.choose (l + 1) : ℂ) * (-1) ^ l)) *
        zeroMomentTerm k l q)
      (∑ k ∈ range n, ∑ l ∈ range n,
        (((n.choose (k + 1) : ℂ) * (-1) ^ k) * ((n.choose (l + 1) : ℂ) * (-1) ^ l)) *
          zeroMoment k l) :=
    hasSum_sum fun k _ => hasSum_sum fun l _ =>
      ((summable_zeroMomentTerm k l).hasSum).mul_left _
  have e : (fun q : XiZeroCopy => ∑ k ∈ range n, ∑ l ∈ range n,
      (((n.choose (k + 1) : ℂ) * (-1) ^ k) * ((n.choose (l + 1) : ℂ) * (-1) ^ l)) *
        zeroMomentTerm k l q) =
      fun q : XiZeroCopy => RHTower.liTerm (RHTower.xiRootW (q.1 : ℂ)) n := by
    funext q
    rw [← laguerre_product_eq_liTerm n q, ← sum_choose_succ_mul_inv_pow n (q.1 : ℂ),
      ← sum_choose_succ_mul_inv_pow n (1 - (q.1 : ℂ)), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [zeroMomentTerm, ← one_div_mul_one_div]
    generalize 1 / (q.1 : ℂ) ^ (k + 1) = A
    generalize 1 / (1 - (q.1 : ℂ)) ^ (l + 1) = B
    ring
  rw [e] at h1
  exact h1.unique (RHTower.hasSum_liTerm_xiZeroCopy n)

/-- **The Li ladder as comb forms of the Laguerre tails.** For every `n`, Weil's form on the
comb of the tail `m ↦ P_n(log(N/m))`, `1 ≤ m ≤ N`, per degree point, tends to the paired Li
coefficient `Re 2λ_n`. -/
theorem tendsto_combForm_laguerreTail_div (n : ℕ) :
    Tendsto (fun N : ℕ => combW (Icc 1 N) (laguerreTail n N) / N) atTop
      (𝓝 (RHTower.xiLiPaired n).re) := by
  have h := tendsto_combForm_polyLogTail_div
    (β := fun k l => k.factorial * l.factorial * (zeroMoment k l).re)
    tendsto_logTailForm_div_zeroMoment n (laguerreCoeff n)
  have hval : ∑ k ∈ range n, ∑ l ∈ range n, laguerreCoeff n k * laguerreCoeff n l *
      (k.factorial * l.factorial * (zeroMoment k l).re) = (RHTower.xiLiPaired n).re := by
    rw [← sum_laguerre_zeroMoment n, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hc : (((n.choose (k + 1) : ℂ) * (-1) ^ k) * ((n.choose (l + 1) : ℂ) * (-1) ^ l)) =
        (((n.choose (k + 1) : ℝ) * (-1) ^ k * ((n.choose (l + 1) : ℝ) * (-1) ^ l) : ℝ) : ℂ) := by
      push_cast
      ring
    have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hl : ((l.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hc, Complex.re_ofReal_mul, laguerreCoeff, laguerreCoeff]
    field_simp
  rw [hval] at h
  exact h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
