/-
# The assembled Sonin Gram is intrinsically Hankel

The all-prime residual construction produces `K_a` and its positive energy `T_a = K_aᴴK_a`.
The two-index Gram family formed from `K_a T_a^m` and `K_a T_a^n` is therefore not an additional
two-index datum: associativity and trace cyclicity force it to be the `(m+n)`-th trace moment of
`T_a`.  Thus the remaining Xi weld is only the arithmetic identification of one source moment
sequence with the centered Xi reciprocal moments.
-/
import GaloisForLFunctions.HilbertSchmidtAlgebra
import GaloisForLFunctions.RHTower.SoninAllPrimeResidualKernel

open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*}

/-- A Hilbert--Schmidt pairing is the trace of the corresponding adjoint product. -/
theorem hsInner_eq_trace_adjoint_comp {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    hsInner K L = ∑' i : ι, hsComp (hsAdjoint K) L (i, i) := by
  rw [hsTrace_hsComp (isHS_hsAdjoint hK) hL, hsAdjoint_hsAdjoint]

/-- Every shifted power of a self-adjoint Hilbert--Schmidt kernel is self-adjoint. -/
theorem hsAdjoint_hsPow_of_selfAdjoint {T : ι × ι → ℂ} (hT : IsHS T)
    [DecidableEq ι]
    (hself : hsAdjoint T = T) : ∀ n : ℕ, hsAdjoint (hsPow T n) = hsPow T n
  | 0 => hself
  | n + 1 => by
      rw [hsPow, hsAdjoint_hsComp, hself, hsAdjoint_hsPow_of_selfAdjoint hT hself n]
      change hsComp (hsPow T n) (hsPow T 0) = hsComp (hsPow T 0) (hsPow T n)
      rw [hsComp_hsPow hT n 0, hsComp_hsPow hT 0 n]
      congr 2
      omega

end HilbertSchmidt

namespace RHTower

noncomputable section

local instance soninAllPrimeHankelDecidableEq : DecidableEq SoninAllPrimeIndex :=
  Classical.decEq _

/-- The single source moment sequence carried by the positive all-prime Sonin energy.  With the
shifted convention for `hsPow`, `soninAllPrimeEnergyMoment a r = Tr(T_a^(r+1))`. -/
def soninAllPrimeEnergyMoment (a : ℝ) (r : ℕ) : ℂ :=
  ∑' i : SoninAllPrimeIndex,
    HilbertSchmidt.hsPow (soninAllPrimeResidualEnergyKernel a) r (i, i)

private theorem gram_zero_zero (a : ℝ) (ha : 0 < a) :
    soninAllPrimePolynomialGramEntry a 0 0 = soninAllPrimeEnergyMoment a 0 := by
  rw [soninAllPrimePolynomialGramEntry, soninAllPrimePolynomialPowerKernel,
    if_pos rfl, soninAllPrimeEnergyMoment]
  rw [HilbertSchmidt.hsInner_eq_trace_adjoint_comp
    (soninAllPrimeResidualKernel_isHS a ha) (soninAllPrimeResidualKernel_isHS a ha)]
  rfl

private theorem gram_zero_pos (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : n ≠ 0) :
    soninAllPrimePolynomialGramEntry a 0 n = soninAllPrimeEnergyMoment a n := by
  let K := soninAllPrimeResidualKernel a
  let T := soninAllPrimeResidualEnergyKernel a
  have hK : HilbertSchmidt.IsHS K := soninAllPrimeResidualKernel_isHS a ha
  have hT : HilbertSchmidt.IsHS T := soninAllPrimeResidualEnergyKernel_isHS a ha
  rw [soninAllPrimePolynomialGramEntry]
  simp only [soninAllPrimePolynomialPowerKernel, if_pos, if_neg hn]
  change HilbertSchmidt.hsInner K
    (HilbertSchmidt.hsComp K (HilbertSchmidt.hsPow T (n - 1))) = _
  rw [HilbertSchmidt.hsInner_eq_trace_adjoint_comp hK
    (HilbertSchmidt.isHS_hsComp hK (HilbertSchmidt.isHS_hsPow hT (n - 1)))]
  rw [← HilbertSchmidt.hsComp_assoc (HilbertSchmidt.isHS_hsAdjoint hK) hK
    (HilbertSchmidt.isHS_hsPow hT (n - 1))]
  change (∑' i : SoninAllPrimeIndex,
      HilbertSchmidt.hsComp T (HilbertSchmidt.hsPow T (n - 1)) (i, i)) = _
  have hnform : n - 1 + 1 = n := by omega
  rw [show HilbertSchmidt.hsComp T (HilbertSchmidt.hsPow T (n - 1)) =
      HilbertSchmidt.hsPow T n by
        change HilbertSchmidt.hsPow T ((n - 1) + 1) = HilbertSchmidt.hsPow T n
        rw [hnform]]
  rfl

private theorem gram_pos_zero (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : m ≠ 0) :
    soninAllPrimePolynomialGramEntry a m 0 = soninAllPrimeEnergyMoment a m := by
  let K := soninAllPrimeResidualKernel a
  let T := soninAllPrimeResidualEnergyKernel a
  have hK : HilbertSchmidt.IsHS K := soninAllPrimeResidualKernel_isHS a ha
  have hT : HilbertSchmidt.IsHS T := soninAllPrimeResidualEnergyKernel_isHS a ha
  have hTm : HilbertSchmidt.IsHS (HilbertSchmidt.hsPow T (m - 1)) :=
    HilbertSchmidt.isHS_hsPow hT (m - 1)
  rw [soninAllPrimePolynomialGramEntry]
  simp only [soninAllPrimePolynomialPowerKernel, if_pos, if_neg hm]
  change HilbertSchmidt.hsInner
    (HilbertSchmidt.hsComp K (HilbertSchmidt.hsPow T (m - 1))) K = _
  rw [HilbertSchmidt.hsInner_eq_trace_adjoint_comp
    (HilbertSchmidt.isHS_hsComp hK hTm) hK,
    HilbertSchmidt.hsAdjoint_hsComp,
    HilbertSchmidt.hsAdjoint_hsPow_of_selfAdjoint hT
      (soninAllPrimeResidualEnergyKernel_selfAdjoint a) (m - 1),
    HilbertSchmidt.hsComp_assoc hTm (HilbertSchmidt.isHS_hsAdjoint hK) hK]
  change (∑' i : SoninAllPrimeIndex,
    HilbertSchmidt.hsComp (HilbertSchmidt.hsPow T (m - 1)) T (i, i)) = _
  change (∑' i : SoninAllPrimeIndex,
    HilbertSchmidt.hsComp (HilbertSchmidt.hsPow T (m - 1))
      (HilbertSchmidt.hsPow T 0) (i, i)) = _
  rw [HilbertSchmidt.hsComp_hsPow hT (m - 1) 0]
  have hmform : m - 1 + 0 + 1 = m := by omega
  simp only [soninAllPrimeEnergyMoment, T, hmform]

private theorem gram_pos_pos (a : ℝ) (ha : 0 < a) (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    soninAllPrimePolynomialGramEntry a m n = soninAllPrimeEnergyMoment a (m + n) := by
  let K := soninAllPrimeResidualKernel a
  let T := soninAllPrimeResidualEnergyKernel a
  have hK : HilbertSchmidt.IsHS K := soninAllPrimeResidualKernel_isHS a ha
  have hT : HilbertSchmidt.IsHS T := soninAllPrimeResidualEnergyKernel_isHS a ha
  have hTm : HilbertSchmidt.IsHS (HilbertSchmidt.hsPow T (m - 1)) :=
    HilbertSchmidt.isHS_hsPow hT (m - 1)
  have hTn : HilbertSchmidt.IsHS (HilbertSchmidt.hsPow T (n - 1)) :=
    HilbertSchmidt.isHS_hsPow hT (n - 1)
  rw [soninAllPrimePolynomialGramEntry]
  simp only [soninAllPrimePolynomialPowerKernel, if_neg hm, if_neg hn]
  change HilbertSchmidt.hsInner
    (HilbertSchmidt.hsComp K (HilbertSchmidt.hsPow T (m - 1)))
    (HilbertSchmidt.hsComp K (HilbertSchmidt.hsPow T (n - 1))) = _
  rw [HilbertSchmidt.hsInner_eq_trace_adjoint_comp
    (HilbertSchmidt.isHS_hsComp hK hTm) (HilbertSchmidt.isHS_hsComp hK hTn),
    HilbertSchmidt.hsAdjoint_hsComp,
    HilbertSchmidt.hsAdjoint_hsPow_of_selfAdjoint hT
      (soninAllPrimeResidualEnergyKernel_selfAdjoint a) (m - 1)]
  rw [HilbertSchmidt.hsComp_assoc hTm (HilbertSchmidt.isHS_hsAdjoint hK)
      (HilbertSchmidt.isHS_hsComp hK hTn),
    ← HilbertSchmidt.hsComp_assoc (HilbertSchmidt.isHS_hsAdjoint hK) hK hTn]
  change (∑' i : SoninAllPrimeIndex,
    HilbertSchmidt.hsComp (HilbertSchmidt.hsPow T (m - 1))
      (HilbertSchmidt.hsComp T (HilbertSchmidt.hsPow T (n - 1))) (i, i)) = _
  change (∑' i : SoninAllPrimeIndex,
    HilbertSchmidt.hsComp (HilbertSchmidt.hsPow T (m - 1))
      (HilbertSchmidt.hsComp (HilbertSchmidt.hsPow T 0)
        (HilbertSchmidt.hsPow T (n - 1))) (i, i)) = _
  rw [HilbertSchmidt.hsComp_hsPow hT 0 (n - 1)]
  have hnindex : 0 + (n - 1) + 1 = n := by omega
  rw [hnindex, HilbertSchmidt.hsComp_hsPow hT (m - 1) n]
  have hindex : m - 1 + n + 1 = m + n := by omega
  simp only [soninAllPrimeEnergyMoment, T, hindex]

/-- **Intrinsic Hankel collapse.** The source Gram entry depends only on the sum of its two
indices; it is exactly the corresponding trace moment of the positive energy `T_a = K_aᴴK_a`.
No Xi divisor, RH hypothesis, or spectral identification is used. -/
theorem soninAllPrimePolynomialGramEntry_eq_energyMoment
    (a : ℝ) (ha : 0 < a) (m n : ℕ) :
    soninAllPrimePolynomialGramEntry a m n = soninAllPrimeEnergyMoment a (m + n) := by
  by_cases hm : m = 0
  · subst m
    by_cases hn : n = 0
    · subst n
      simpa using gram_zero_zero a ha
    · simpa using gram_zero_pos a ha n hn
  · by_cases hn : n = 0
    · subst n
      simpa using gram_pos_zero a ha m hm
    · exact gram_pos_pos a ha m n hm hn

/-- Two source Gram entries on the same anti-diagonal are equal. -/
theorem soninAllPrimePolynomialGramEntry_eq_of_add_eq
    (a : ℝ) (ha : 0 < a) {m n r s : ℕ} (h : m + n = r + s) :
    soninAllPrimePolynomialGramEntry a m n =
      soninAllPrimePolynomialGramEntry a r s := by
  rw [soninAllPrimePolynomialGramEntry_eq_energyMoment a ha,
    soninAllPrimePolynomialGramEntry_eq_energyMoment a ha, h]

/-- The source trace-Hankel form is governed by one trace-moment sequence. -/
theorem soninAllPrimeTraceHankel_eq_energyMoment_sum (a : ℝ) (ha : 0 < a)
    (p : Polynomial ℝ) :
    soninAllPrimeTraceHankel a p =
      ∑ m ∈ p.support, ∑ n ∈ p.support,
        ((p.coeff m : ℝ) : ℂ) * ((p.coeff n : ℝ) : ℂ) *
          soninAllPrimeEnergyMoment a (m + n) := by
  rw [soninAllPrimeTraceHankel_eq_gram_sum a ha p]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [soninAllPrimePolynomialGramEntry_eq_energyMoment a ha]

end

end RHTower
