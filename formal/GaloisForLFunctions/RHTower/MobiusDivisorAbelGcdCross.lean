import GaloisForLFunctions.RHTower.MobiusDivisorAbelHomothety

/-!
# Exact common-divisor components of the literal Abel off-diagonal

The common-divisor label partitions every ordered cross term exactly. Summing
all labels reconstructs the square of the complete channel sum minus its
arithmetic diagonal, with no componentwise sign assumption.
-/

noncomputable section
open Finset
namespace RHTower

/-- Ordered cross-channel contribution having one exact common divisor. -/
def mobiusDivisorGcdCross (M r : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
    if Nat.gcd d e = r ∧ d ≠ e then
      mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0

private theorem finite_cross_decomposition (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, if d ≠ e then f d*f e else 0) =
      (∑ d ∈ s, f d)^(2 : ℕ) - ∑ d ∈ s, f d^(2 : ℕ) := by
  have hdiag : (∑ d ∈ s, ∑ e ∈ s, if d = e then f d*f e else 0) =
      ∑ d ∈ s, f d^(2 : ℕ) := by
    apply sum_congr rfl
    intro d hd
    simp [hd,pow_two]
  have hsplit :
      (∑ d ∈ s, ∑ e ∈ s, f d*f e) =
        (∑ d ∈ s, ∑ e ∈ s, if d = e then f d*f e else 0) +
          ∑ d ∈ s, ∑ e ∈ s, if d ≠ e then f d*f e else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    by_cases hde : d = e <;> simp [hde]
  have hfull : (∑ d ∈ s, ∑ e ∈ s, f d*f e) = (∑ d ∈ s, f d)^(2 : ℕ) := by
    rw [pow_two,sum_mul_sum]
  rw [hdiag,hfull] at hsplit
  linarith only [hsplit]

/-- Every common-divisor component reconstructs the complete signed off-diagonal, without a
componentwise sign assumption or any discarded cutoff term. -/
theorem sum_mobiusDivisorGcdCross (M : ℕ) :
    (∑ r ∈ Icc 1 M, mobiusDivisorGcdCross M r) =
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^(2 : ℕ) -
        ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d^(2 : ℕ) := by
  unfold mobiusDivisorGcdCross
  rw [sum_comm]
  conv_lhs =>
    arg 2
    ext d
    rw [sum_comm]
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 M) (e : ℕ) (_he : e ∈ Icc 1 M) :
      (∑ r ∈ Icc 1 M,
        if Nat.gcd d e = r ∧ d ≠ e then
          mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0) =
        if d ≠ e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0 := by
    have hg : Nat.gcd d e ∈ Icc 1 M := mem_Icc.mpr
      ⟨Nat.gcd_pos_of_pos_left e (mem_Icc.mp hd).1,
        (Nat.le_of_dvd (mem_Icc.mp hd).1 (Nat.gcd_dvd_left d e)).trans (mem_Icc.mp hd).2⟩
    by_cases hde : d ≠ e <;> simp [hde,hg]
  calc
    _ = ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d ≠ e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0 := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      exact hpoint d hd e he
    _ = _ := finite_cross_decomposition (Icc 1 M) (mobiusDivisorDilationChannel M)

private def gcdCrossPairs (M r : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 M ×ˢ Icc 1 M).filter (fun p => Nat.gcd p.1 p.2 = r ∧ p.1 ≠ p.2)

private theorem gcdCross_eq_pairs (M r : ℕ) :
    mobiusDivisorGcdCross M r = ∑ p ∈ gcdCrossPairs M r,
      mobiusDivisorDilationChannel M p.1*mobiusDivisorDilationChannel M p.2 := by
  rw [gcdCrossPairs,sum_filter,sum_product]
  rfl

private theorem sum_gcdCrossPairs_mul {r : ℕ} (hr : 0 < r) (M : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ gcdCrossPairs (r*M) r, f p.1 p.2) =
      ∑ p ∈ gcdCrossPairs M 1, f (r*p.1) (r*p.2) := by
  have hquot (p : ℕ×ℕ) (hp : p ∈ gcdCrossPairs (r*M) r) :
      r*(p.1/r)=p.1 ∧ r*(p.2/r)=p.2 := by
    have hg := (mem_filter.mp hp).2.1
    exact ⟨Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_left _ _),
      Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_right _ _)⟩
  refine sum_nbij' (i := fun p : ℕ×ℕ => (p.1/r,p.2/r))
    (j := fun p : ℕ×ℕ => (r*p.1,r*p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hm1,hm2⟩ := hquot p hp
    rw [gcdCrossPairs,mem_filter,mem_product,mem_Icc,mem_Icc] at hp ⊢
    obtain ⟨⟨⟨ha1,haM⟩,hb1,hbM⟩,hg,hne⟩ := hp
    have h1 : 1 ≤ p.1/r := by nlinarith
    have h2 : 1 ≤ p.2/r := by nlinarith
    have h1M : p.1/r ≤ M := by nlinarith
    have h2M : p.2/r ≤ M := by nlinarith
    refine ⟨⟨⟨h1,h1M⟩,h2,h2M⟩,?_,?_⟩
    · simpa only [hg] using Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_left p.2 ha1)
    · intro h
      change p.1/r = p.2/r at h
      exact hne (by rw [← hm1,← hm2,h])
  · intro p hp
    rw [gcdCrossPairs,mem_filter,mem_product,mem_Icc,mem_Icc] at hp ⊢
    obtain ⟨⟨⟨ha1,haM⟩,hb1,hbM⟩,hg,hne⟩ := hp
    refine ⟨⟨⟨by nlinarith,Nat.mul_le_mul_left r haM⟩,
      by nlinarith,Nat.mul_le_mul_left r hbM⟩,?_,?_⟩
    · simp only [Nat.gcd_mul_left,hg,mul_one]
    · intro h
      exact hne (Nat.eq_of_mul_eq_mul_left hr h)
  · intro p hp
    obtain ⟨h1,h2⟩ := hquot p hp
    exact Prod.ext h1 h2
  · intro p _
    exact Prod.ext (Nat.mul_div_cancel_left _ hr) (Nat.mul_div_cancel_left _ hr)
  · intro p hp
    obtain ⟨h1,h2⟩ := hquot p hp
    rw [h1,h2]

/-- Primitive cross terms with the exact prime exclusions imposed by a common dilation. -/
def mobiusDivisorRestrictedCoprimeCross (M r : ℕ) : ℝ :=
  ∑ p ∈ gcdCrossPairs M 1,
    (if r.Coprime p.1 then mobiusDivisorDilationChannel M p.1 else 0)*
      (if r.Coprime p.2 then mobiusDivisorDilationChannel M p.2 else 0)

/-- Exact common-divisor homothety, retaining both shared-prime masks. -/
theorem mobiusDivisorGcdCross_mul (r M : ℕ) :
    mobiusDivisorGcdCross (r*M) r =
      (r : ℝ)*((ArithmeticFunction.moebius r : ℤ) : ℝ)^(2 : ℕ)*
        mobiusDivisorRestrictedCoprimeCross M r := by
  by_cases hr : r = 0
  · simp [hr,mobiusDivisorGcdCross]
  rw [gcdCross_eq_pairs,sum_gcdCrossPairs_mul (by omega : 0 < r) M
    (fun a b => mobiusDivisorDilationChannel (r*M) a*mobiusDivisorDilationChannel (r*M) b)]
  unfold mobiusDivisorRestrictedCoprimeCross
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  rw [mobiusDivisorDilationChannel_mul_masked,mobiusDivisorDilationChannel_mul_masked]
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) r)
  calc
    _ = (Real.sqrt r)^(2 : ℕ)*((ArithmeticFunction.moebius r : ℤ) : ℝ)^(2 : ℕ)*
        ((if r.Coprime p.1 then mobiusDivisorDilationChannel M p.1 else 0)*
          (if r.Coprime p.2 then mobiusDivisorDilationChannel M p.2 else 0)) := by ring
    _ = _ := by rw [hs]

/-- A prime beyond the base cutoff preserves the complete primitive component. -/
theorem mobiusDivisorGcdCross_mul_prime {p M : ℕ} (hp : Nat.Prime p) (hMp : M < p) :
    mobiusDivisorGcdCross (p*M) p = (p : ℝ)*mobiusDivisorGcdCross M 1 := by
  have hcop (a : ℕ) (ha : a ∈ Icc 1 M) : p.Coprime a := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hpa
    have := Nat.le_of_dvd (mem_Icc.mp ha).1 hpa
    have := (mem_Icc.mp ha).2
    omega
  have hrestricted : mobiusDivisorRestrictedCoprimeCross M p = mobiusDivisorGcdCross M 1 := by
    rw [gcdCross_eq_pairs]
    unfold mobiusDivisorRestrictedCoprimeCross
    apply sum_congr rfl
    intro q hq
    have hmem := mem_product.mp (mem_filter.mp hq).1
    rw [if_pos (hcop q.1 hmem.1),if_pos (hcop q.2 hmem.2)]
  rw [mobiusDivisorGcdCross_mul,hrestricted,ArithmeticFunction.moebius_apply_prime hp]
  norm_num

end RHTower
