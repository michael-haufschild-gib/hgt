import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.IntrinsicDirichletCutoffMargin

/-!
# Intrinsic Euler-sieve shell collapse and Dirichlet-hyperbola quotient decomposition above `84.5`

Advancing the intrinsic shell-convolution framework of `IntrinsicDirichletCutoffMargin`:

1. **Sub-radix vanishing of `adjacentCutoff` and sharp `3^(2K - 1)` Möbius inversion
   (`adjacentCutoff_eq_zero_of_lt_tailRadix`, `weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow`,
   `weightedAlignedReconstructed_fullMoebius_eq_sub_one_of_pred_pow`,
   `intrinsicMoebiusTail_eq_triadic_of_two_pow_pred_le`)**:
   because `shellCutoff t j q w = 0` whenever `q < tailRadix t j`, `adjacentCutoff t j q w = 0` for
   all `q < tailRadix t j` and all `w ∈ ℂ`. Consequently, exact Möbius shell inversion holds already
   for `M ≥ C^(2K - 1)` (`K ≥ 1`), full two-prime recovery `= w - 1` holds already for `M ≥ 3^(2K - 1)`
   (one-third of `9^K`), and for `M ≥ 2^(2K - 1)` (including `M = 4^K`) the dyadic channel of
   `intrinsicMoebiusTail M K w` vanishes identically, localizing the entire tail to the triadic channel.
2. **Exact Dirichlet-hyperbola quotient decomposition of `intrinsicMoebiusTail`
   (`moebiusChannelTail_eq_quotient_sum`, `intrinsicMoebiusTail_eq_hyperbola_quotient_sum`)**:
   grouping `M < d ≤ C^(2K - 1)` by the constant integer quotient `q = ⌊C^(2K) / d⌋ ∈ [C, ⌊C^(2K) / (M + 1)⌋]`
   rewrites the short-shell Möbius tail as an exact finite linear combination of incomplete Möbius
   Dirichlet blocks `∑_{max(M + 1, ⌊C^(2K)/(q + 1)⌋ + 1) ≤ d ≤ ⌊C^(2K)/q⌋} μ(d) d^(-w)` weighted by
   `adjacentCutoff t_C 0 q w`.
3. **Intrinsic Euler-sieve shell collapse, growing-primorial zero-threshold decay, and single-aperture
   `RH` equivalence (`weightedAlignedReconstructed_eulerSieve_eq_sub_one`,
   `tendsto_intrinsicZeroThreshold_growing_eulerSieve_zero`,
   `intrinsic_eulerSieve_margin_iff_zeta_ne_zero`,
   `rh_iff_intrinsic_eulerSieve_margin_above_eightyFour_and_half`)**:
   putting `eulerSieveSurgCoeff y` **inside** the prime-gas shells sieves out all multiples of primes
   `p ≤ y`, collapses `weightedAlignedReconstructed` identically to `w - 1` whenever `3^(2K - 1) ≤ y`,
   keeps `intrinsicDirichletZeroThreshold` decaying to `0` along any growing sieve schedule
   `eulerPrimorial (y K) ≤ 2^K` (`1 / 2 < w.re`), and — because `∏_{p ≤ y} (1 - p^(-w)) ≠ 0` on
   `Re w > 0` — gives a mollifier-zero-free intrinsic `RH` equivalence on
   `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}` for **every fixed aperture `y : ℕ`**.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter Set Metric
open scoped Topology ComplexConjugate BigOperators

/-! ### Part 1: Sub-radix vanishing of `adjacentCutoff` and sharp `3^(2K - 1)` Möbius inversion -/

/-- Every integer cutoff `q < tailRadix t j` lies strictly below the first non-trivial occupation
shell at refinements `j` and `j + 1`, so `adjacentCutoff t j q w = 0` identically across `ℂ`. -/
theorem adjacentCutoff_eq_zero_of_lt_tailRadix (t : ExceptionalTime) (j : ℕ)
    {q : ℕ} (hq : q < (tailRadix t j).val) (w : ℂ) :
    adjacentCutoff t j q w = 0 := by
  have hC1 : 1 < (tailRadix t j).val := radix_gt_one t j
  have hsq : (tailRadix t j).val < (tailRadix t j).val ^ 2 := by nlinarith
  have hq_succ : q < (tailRadix t (j + 1)).val := by
    rw [tailRadix_succ, PNat.pow_coe]
    exact hq.trans hsq
  have hsh0 : shellCutoff t j q w = 0 := by
    rw [shellCutoff_eq_sum_log, Nat.log_of_lt hq]; simp
  have hsh1 : shellCutoff t (j + 1) q w = 0 := by
    rw [shellCutoff_eq_sum_log, Nat.log_of_lt hq_succ]; simp
  rw [adjacentCutoff, hsh0, hsh1, mul_zero, sub_zero]

/-- **Sharp `C^(2K - 1)` finite Möbius shell inversion:** for `K ≥ 1` and `M ≥ C^(2K - 1)`
(`C = tailRadix t j`), all divisors `d > C^(2K - 1)` have quotient `⌊C^(2K) / d⌋ < C` where
`adjacentCutoff = 0`, so `weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j (C^(2K)) w`
already equals `(w - 1) · finiteContrastTransfer C K w` for all `w ∈ ℂ`. -/
theorem weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow (t : ExceptionalTime) (j : ℕ)
    {K M : ℕ} (hK : 1 ≤ K) (hM : (tailRadix t j).val ^ (2 * K - 1) ≤ M) (w : ℂ) :
    weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j
        ((tailRadix t j).val ^ (2 * K)) w =
      (w - 1) * finiteContrastTransfer (tailRadix t j) K w := by
  set C := (tailRadix t j).val
  have hC_pos : 0 < C := (tailRadix t j).pos
  have hpow_eq : C * C ^ (2 * K - 1) = C ^ (2 * K) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * K)]
  have hzero_above : ∀ d : ℕ, C ^ (2 * K - 1) < d →
      adjacentCutoff t j (C ^ (2 * K) / d) w = 0 := by
    intro d hd
    have hd_pos : 0 < d := by omega
    have hlt_mul : C ^ (2 * K) < C * d := by
      rw [← hpow_eq]
      exact Nat.mul_lt_mul_of_pos_left hd hC_pos
    have hdiv_lt : C ^ (2 * K) / d < C := by
      by_contra hge
      have hle : C ≤ C ^ (2 * K) / d := not_lt.mp hge
      exact not_le.mpr hlt_mul ((Nat.le_div_iff_mul_le hd_pos).mp hle)
    exact adjacentCutoff_eq_zero_of_lt_tailRadix t j hdiv_lt w
  have htrim : ∀ N : ℕ, C ^ (2 * K - 1) ≤ N →
      weightedAdjacentCutoff (dirichletSurgWeight N moebiusReal) t j (C ^ (2 * K)) w =
        ∑ d ∈ Finset.Icc 1 (C ^ (2 * K - 1)),
          (moebiusReal d : ℂ) * (d : ℂ) ^ (-w) * adjacentCutoff t j (C ^ (2 * K) / d) w := by
    intro N hN
    rw [weightedAdjacentCutoff_dirichletSurgWeight]
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hN) ?_).symm
    intro d hd hnot
    rw [Finset.mem_Icc] at hd hnot
    have hgt : C ^ (2 * K - 1) < d := by omega
    rw [hzero_above d hgt, mul_zero]
  have hfull_le : C ^ (2 * K - 1) ≤ C ^ (2 * K) :=
    Nat.pow_le_pow_right hC_pos (by omega)
  rw [htrim M hM, ← htrim (C ^ (2 * K)) hfull_le]
  exact weightedAdjacentCutoff_fullMoebius_eq t j K le_rfl w

/-- **Sharp `3^(2K - 1)` two-prime recovery of `w - 1`:** for `K ≥ 1`, `M ≥ 3^(2K - 1)`, and
`Re w > 0`, `weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w = w - 1`
identically, and `intrinsicMoebiusTail M K w = 0`. -/
theorem weightedAlignedReconstructed_fullMoebius_eq_sub_one_of_pred_pow
    {K M : ℕ} (hK : 1 ≤ K) (hM : 3 ^ (2 * K - 1) ≤ M) {w : ℂ} (hw : 0 < w.re) :
    weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w = w - 1 ∧
      intrinsicMoebiusTail M K w = 0 := by
  have h23 : 2 ^ (2 * K - 1) ≤ 3 ^ (2 * K - 1) :=
    Nat.pow_le_pow_left (by norm_num) (2 * K - 1)
  have hc2 : weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) halfTurnClock 0
        (2 ^ (2 * K)) w =
      weightedAdjacentCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) halfTurnClock 0
        (2 ^ (2 * K)) w := by
    have hrad2 : (tailRadix halfTurnClock 0).val = 2 := congrArg PNat.val tailRadix_halfTurnClock_zero
    have hM2 : (tailRadix halfTurnClock 0).val ^ (2 * K - 1) ≤ M := by
      rw [hrad2]; exact h23.trans hM
    have h9 : (tailRadix halfTurnClock 0).val ^ (2 * K) ≤ 3 ^ (2 * K) := by
      rw [hrad2]; exact Nat.pow_le_pow_left (by norm_num) (2 * K)
    have h1 := weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow halfTurnClock 0 hK hM2 w
    have h2 := weightedAdjacentCutoff_fullMoebius_eq halfTurnClock 0 K h9 w
    rw [hrad2] at h1 h2
    exact h1.trans h2.symm
  have hc3 : weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) primeThreeClock 0
        (3 ^ (2 * K)) w =
      weightedAdjacentCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) primeThreeClock 0
        (3 ^ (2 * K)) w := by
    have hrad3 : (tailRadix primeThreeClock 0).val = 3 := congrArg PNat.val tailRadix_primeThreeClock_zero
    have hM3 : (tailRadix primeThreeClock 0).val ^ (2 * K - 1) ≤ M := by
      rw [hrad3]; exact hM
    have h9 : (tailRadix primeThreeClock 0).val ^ (2 * K) ≤ 3 ^ (2 * K) := by
      rw [hrad3]
    have h1 := weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow primeThreeClock 0 hK hM3 w
    have h2 := weightedAdjacentCutoff_fullMoebius_eq primeThreeClock 0 K h9 w
    rw [hrad3] at h1 h2
    exact h1.trans h2.symm
  have heq : weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K w =
      weightedAlignedReconstructed (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) K w := by
    unfold weightedAlignedReconstructed
    rw [hc2, hc3]
  have hval := weightedAlignedReconstructed_fullMoebius_eq_sub_one hK le_rfl hw
  refine ⟨heq.trans hval, ?_⟩
  unfold intrinsicMoebiusTail
  rw [heq, sub_self]

/-- **Pure-triadic localization of `intrinsicMoebiusTail` above `2^(2K - 1)`:** whenever `K ≥ 1` and
`2^(2K - 1) ≤ M` (in particular at `M = 2^(2K - 1)` and `M = 4^K = 2^(2K)`), the dyadic channel has
already inverted completely to `(w - 1) · contrastTransfer 2 w`, so `intrinsicMoebiusTail M K w`
depends solely on the triadic shell tail `M < d ≤ 3^(2K - 1)`. -/
theorem intrinsicMoebiusTail_eq_triadic_of_two_pow_pred_le
    {K M : ℕ} (hK : 1 ≤ K) (hM : 2 ^ (2 * K - 1) ≤ M) (w : ℂ) :
    intrinsicMoebiusTail M K w =
      (conj (contrastTransfer 3 w) *
        ((weightedAdjacentCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) primeThreeClock 0
            (3 ^ (2 * K)) w -
          weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) primeThreeClock 0
            (3 ^ (2 * K)) w) /
          (1 - (heat w 3) ^ (2 * K)))) /
        (twoPrimeTransferMass w : ℂ) := by
  have hrad2 : (tailRadix halfTurnClock 0).val = 2 := congrArg PNat.val tailRadix_halfTurnClock_zero
  have hc2 : weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) halfTurnClock 0
        (2 ^ (2 * K)) w =
      weightedAdjacentCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) halfTurnClock 0
        (2 ^ (2 * K)) w := by
    have hM2 : (tailRadix halfTurnClock 0).val ^ (2 * K - 1) ≤ M := by rw [hrad2]; exact hM
    have h9 : (tailRadix halfTurnClock 0).val ^ (2 * K) ≤ 3 ^ (2 * K) := by
      rw [hrad2]; exact Nat.pow_le_pow_left (by norm_num) (2 * K)
    have h1 := weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow halfTurnClock 0 hK hM2 w
    have h2 := weightedAdjacentCutoff_fullMoebius_eq halfTurnClock 0 K h9 w
    rw [hrad2] at h1 h2
    exact h1.trans h2.symm
  unfold intrinsicMoebiusTail weightedAlignedReconstructed
  rw [hc2]
  ring

/-! ### Part 2: Exact finite Dirichlet-hyperbola quotient decomposition of `intrinsicMoebiusTail` -/

/-- Incomplete Möbius Dirichlet block `∑_{a ≤ d ≤ b} μ(d) d^(-w)`. -/
def moebiusDirichletBlock (a b : ℕ) (w : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc a b, (moebiusReal d : ℂ) * (d : ℂ) ^ (-w)

/-- **Exact Dirichlet-hyperbola quotient decomposition on a single prime-gas clock:** for every
`K ≥ 1`, `C = tailRadix t j`, and `M : ℕ`, the short-shell Möbius contrast tail decomposes by
integer quotients `q = ⌊C^(2K) / d⌋ ∈ [C, ⌊C^(2K) / (M + 1)⌋]` into `adjacentCutoff t j q w` times
`moebiusDirichletBlock (max (M + 1) (C^(2K) / (q + 1) + 1)) (C^(2K) / q) w`. -/
theorem moebiusChannelTail_eq_quotient_sum (t : ExceptionalTime) (j : ℕ)
    {K : ℕ} (hK : 1 ≤ K) (M : ℕ) (w : ℂ) :
    let C := (tailRadix t j).val
    let X := C ^ (2 * K)
    (w - 1) * finiteContrastTransfer (tailRadix t j) K w -
        weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j X w =
      ∑ q ∈ Finset.Icc C (X / (M + 1)),
        adjacentCutoff t j q w *
          moebiusDirichletBlock (max (M + 1) (X / (q + 1) + 1)) (X / q) w := by
  dsimp only
  set C := (tailRadix t j).val
  set X := C ^ (2 * K)
  have hC_pos : 0 < C := (tailRadix t j).pos
  have hpow_eq : C * C ^ (2 * K - 1) = X := by
    dsimp only [X]
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * K)]
  have hXC : X / C = C ^ (2 * K - 1) := by
    rw [← hpow_eq, Nat.mul_div_right _ hC_pos]
  by_cases hM_hi : C ^ (2 * K - 1) ≤ M
  · have hlhs0 : (w - 1) * finiteContrastTransfer (tailRadix t j) K w -
        weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) t j X w = 0 := by
      rw [weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow t j hK hM_hi w, sub_self]
    have hlt_C : X / (M + 1) < C := by
      by_contra hge
      have hle : C ≤ X / (M + 1) := not_lt.mp hge
      have hmul : C * (M + 1) ≤ X := (Nat.le_div_iff_mul_le (by omega)).mp hle
      rw [← hpow_eq] at hmul
      have : M + 1 ≤ C ^ (2 * K - 1) := Nat.le_of_mul_le_mul_left hmul hC_pos
      omega
    have hempty : Finset.Icc C (X / (M + 1)) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hlhs0, hempty, Finset.sum_empty]
  · have hM_lt : M < C ^ (2 * K - 1) := not_le.mp hM_hi
    have hfull := (weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow t j hK
      (le_rfl : C ^ (2 * K - 1) ≤ C ^ (2 * K - 1)) w).symm
    rw [hfull, weightedAdjacentCutoff_dirichletSurgWeight,
      weightedAdjacentCutoff_dirichletSurgWeight]
    have hsplit_Icc : Finset.Icc 1 (C ^ (2 * K - 1)) =
        Finset.Icc 1 M ∪ Finset.Icc (M + 1) (X / C) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_union, hXC]
      omega
    have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) (X / C)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rw [Finset.mem_Icc] at hd1 hd2
      omega
    rw [hsplit_Icc, Finset.sum_union hdisj, add_sub_cancel_left]
    have hmaps : ∀ d ∈ Finset.Icc (M + 1) (X / C),
        X / d ∈ Finset.Icc C (X / (M + 1)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      have hd_pos : 0 < d := by omega
      have hq_lo : C ≤ X / d := by
        refine (Nat.le_div_iff_mul_le hd_pos).mpr ?_
        have hmul := Nat.mul_le_mul_left C hd.2
        rw [hXC, hpow_eq] at hmul
        exact hmul
      have hq_hi : X / d ≤ X / (M + 1) := Nat.div_le_div_left hd.1 (by omega)
      exact ⟨hq_lo, hq_hi⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    have hq_pos : 0 < q := by omega
    have hfib_eq : (Finset.Icc (M + 1) (X / C)).filter (fun d => X / d = q) =
        Finset.Icc (max (M + 1) (X / (q + 1) + 1)) (X / q) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff]
      constructor
      · rintro ⟨⟨hd_lo, _⟩, rfl⟩
        have hd_pos : 0 < d := by omega
        have hd_le_Xq : d ≤ X / (X / d) :=
          (Nat.le_div_iff_mul_le (by omega : 0 < X / d)).mpr
            (by rw [mul_comm]; exact Nat.div_mul_le_self X d)
        have hgt_next : X / (X / d + 1) < d := by
          by_contra hle
          have hd_le : d ≤ X / (X / d + 1) := not_lt.mp hle
          have hmul : d * (X / d + 1) ≤ X := (Nat.le_div_iff_mul_le (by omega)).mp hd_le
          have hdiv : d * (X / d) + X % d = X := Nat.div_add_mod X d
          have hmod : X % d < d := Nat.mod_lt X hd_pos
          have hlt_succ : d * (X / d) + X % d < d * (X / d + 1) := by
            rw [Nat.mul_add, mul_one]
            exact Nat.add_lt_add_left hmod (d * (X / d))
          omega
        exact ⟨⟨hd_lo, by omega⟩, hd_le_Xq⟩
      · rintro ⟨⟨hd_lo, hd_gt⟩, hd_hi⟩
        have hd_pos : 0 < d := by omega
        have hd_XC : d ≤ X / C := hd_hi.trans (Nat.div_le_div_left hq.1 hC_pos)
        have hq_le : q ≤ X / d :=
          (Nat.le_div_iff_mul_le hd_pos).mpr
            (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hq_pos).mp hd_hi)
        have hlt_succ : X / d < q + 1 := by
          by_contra hge
          have hge' : q + 1 ≤ X / d := not_lt.mp hge
          have hmul : (q + 1) * d ≤ X := (Nat.le_div_iff_mul_le hd_pos).mp hge'
          have hd_le_next : d ≤ X / (q + 1) :=
            (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hmul)
          omega
        exact ⟨⟨hd_lo, hd_XC⟩, by omega⟩
    have hcongr : ∑ d ∈ (Finset.Icc (M + 1) (X / C)).filter (fun d => X / d = q),
          (moebiusReal d : ℂ) * (d : ℂ) ^ (-w) * adjacentCutoff t j (X / d) w =
        ∑ d ∈ (Finset.Icc (M + 1) (X / C)).filter (fun d => X / d = q),
          adjacentCutoff t j q w * ((moebiusReal d : ℂ) * (d : ℂ) ^ (-w)) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [(Finset.mem_filter.mp hd).2, mul_comm]
    rw [hcongr, hfib_eq, ← Finset.mul_sum]
    rfl

/-- **Two-prime Dirichlet-hyperbola quotient formula for `intrinsicMoebiusTail`:** for every
`K ≥ 1`, `M : ℕ`, and `w ∈ ℂ`, `intrinsicMoebiusTail M K w` is the exact weighted two-prime sum
of `adjacentCutoff t_C 0 q w · moebiusDirichletBlock` over quotients `q ≥ C`. -/
theorem intrinsicMoebiusTail_eq_hyperbola_quotient_sum
    {K : ℕ} (hK : 1 ≤ K) (M : ℕ) (w : ℂ) :
    let s₂ := (∑ q ∈ Finset.Icc 2 (2 ^ (2 * K) / (M + 1)),
      adjacentCutoff halfTurnClock 0 q w *
        moebiusDirichletBlock (max (M + 1) (2 ^ (2 * K) / (q + 1) + 1)) (2 ^ (2 * K) / q) w) /
      (1 - (heat w 2) ^ (2 * K))
    let s₃ := (∑ q ∈ Finset.Icc 3 (3 ^ (2 * K) / (M + 1)),
      adjacentCutoff primeThreeClock 0 q w *
        moebiusDirichletBlock (max (M + 1) (3 ^ (2 * K) / (q + 1) + 1)) (3 ^ (2 * K) / q) w) /
      (1 - (heat w 3) ^ (2 * K))
    intrinsicMoebiusTail M K w =
      (conj (contrastTransfer 2 w) * s₂ + conj (contrastTransfer 3 w) * s₃) /
        (twoPrimeTransferMass w : ℂ) := by
  dsimp only
  have hrad2_val : (tailRadix halfTurnClock 0).val = 2 := congrArg PNat.val tailRadix_halfTurnClock_zero
  have hrad3_val : (tailRadix primeThreeClock 0).val = 3 := congrArg PNat.val tailRadix_primeThreeClock_zero
  have h9_2 : (tailRadix halfTurnClock 0).val ^ (2 * K) ≤ 3 ^ (2 * K) := by
    rw [hrad2_val]; exact Nat.pow_le_pow_left (by norm_num) (2 * K)
  have h9_3 : (tailRadix primeThreeClock 0).val ^ (2 * K) ≤ 3 ^ (2 * K) := by
    rw [hrad3_val]
  have hfull2 := weightedAdjacentCutoff_fullMoebius_eq halfTurnClock 0 K h9_2 w
  have hfull3 := weightedAdjacentCutoff_fullMoebius_eq primeThreeClock 0 K h9_3 w
  have hq2 := moebiusChannelTail_eq_quotient_sum halfTurnClock 0 hK M w
  have hq3 := moebiusChannelTail_eq_quotient_sum primeThreeClock 0 hK M w
  rw [hrad2_val, tailRadix_halfTurnClock_zero] at hfull2 hq2
  rw [hrad3_val, tailRadix_primeThreeClock_zero] at hfull3 hq3
  unfold intrinsicMoebiusTail weightedAlignedReconstructed
  change ((starRingEnd ℂ) (contrastTransfer 2 w) *
            (weightedAdjacentCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) halfTurnClock 0 (2 ^ (2 * K)) w /
              (1 - heat w 2 ^ (2 * K))) +
          (starRingEnd ℂ) (contrastTransfer 3 w) *
            (weightedAdjacentCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) primeThreeClock 0 (3 ^ (2 * K)) w /
              (1 - heat w 3 ^ (2 * K)))) /
        (twoPrimeTransferMass w : ℂ) -
      ((starRingEnd ℂ) (contrastTransfer 2 w) *
            (weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) halfTurnClock 0 (2 ^ (2 * K)) w /
              (1 - heat w 2 ^ (2 * K))) +
          (starRingEnd ℂ) (contrastTransfer 3 w) *
            (weightedAdjacentCutoff (dirichletSurgWeight M moebiusReal) primeThreeClock 0 (3 ^ (2 * K)) w /
              (1 - heat w 3 ^ (2 * K)))) /
        (twoPrimeTransferMass w : ℂ) = _
  rw [hfull2, hfull3, ← hq2, ← hq3]
  ring

/-! ### Part 3: Intrinsic Euler-sieve shell collapse, growing-primorial decay, and `RH` equivalence -/

private theorem weightedRadialCutoff_eulerSieve_of_le {Y y : ℕ} (hY1 : 1 ≤ Y) (hYy : Y ≤ y) (w : ℂ) :
    weightedRadialCutoff (dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y)) Y w = 1 := by
  have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 Y := by
    intro n hn
    rw [Finset.mem_singleton.mp hn]
    exact Finset.mem_Icc.mpr ⟨le_rfl, hY1⟩
  unfold weightedRadialCutoff
  rw [← Finset.sum_subset hsub]
  · simp [dirichletSurgWeight_eulerSieve_eq_coprime_indicator y le_rfl]
  · intro n hn hnot
    rw [Finset.mem_Icc] at hn
    have hn_ne1 : n ≠ 1 := by simpa using hnot
    rw [dirichletSurgWeight_eulerSieve_eq_coprime_indicator y hn.1]
    have hnot_cop : ¬ Nat.Coprime n (eulerPrimorial y) := by
      intro hcop
      set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn_ne1
      have hpn : p ∣ n := Nat.minFac_dvd n
      have hp_le_n : p ≤ n := Nat.minFac_le (by omega)
      have hp_mem : p ∈ eulerPrimeAperture y := by
        unfold eulerPrimeAperture _root_.RHTower.mobiusFinitePrimeAperture
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
      have hpP : p ∣ eulerPrimorial y := Finset.dvd_prod_of_mem (fun x => x) hp_mem
      have hp1 : p ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hpn hpP
      exact hp.not_dvd_one hp1
    rw [if_neg hnot_cop]
    simp

/-- Opaque-weight comparison helper: any two weights `a, b : ℕ → ℝ` whose radial cutoffs equal `1`
through `B^(2K - 1)` produce identical `weightedAdjacentCutoff` at `B^(2K)`. -/
private theorem weightedAdjacentCutoff_congr_of_radial_eq_one
    {a b : ℕ → ℝ} (tc : ExceptionalTime) (B : ℕ) (hB_pos : 0 < B) {K : ℕ} (hK : 1 ≤ K)
    (hrad : (tailRadix tc 0).val = B) {w : ℂ}
    (ha : ∀ Y : ℕ, 1 ≤ Y → Y ≤ B ^ (2 * K - 1) → weightedRadialCutoff a Y w = 1)
    (hb : ∀ Y : ℕ, 1 ≤ Y → Y ≤ B ^ (2 * K - 1) → weightedRadialCutoff b Y w = 1) :
    weightedAdjacentCutoff a tc 0 (B ^ (2 * K)) w =
      weightedAdjacentCutoff b tc 0 (B ^ (2 * K)) w := by
  have hpow_B : B * B ^ (2 * K - 1) = B ^ (2 * K) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * K)]
  have hdiv_B : B ^ (2 * K) / B = B ^ (2 * K - 1) := by
    rw [← hpow_B, Nat.mul_div_right _ hB_pos]
  have hsh : ∀ m : ℕ, B ≤ (tailRadix tc m).val →
      weightedShellCutoff a tc m (B ^ (2 * K)) w =
        weightedShellCutoff b tc m (B ^ (2 * K)) w := by
    intro m hBm
    rw [weightedShellCutoff, weightedShellCutoff]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_lt : i < Nat.log (tailRadix tc m).val (B ^ (2 * K)) := Finset.mem_range.mp hi
    set Cm := (tailRadix tc m).val
    have hCm_pos : 0 < Cm := (tailRadix tc m).pos
    have hdiv_pos : 1 ≤ B ^ (2 * K) / Cm ^ (i + 1) := by
      have hpow_le : Cm ^ (i + 1) ≤ Cm ^ Nat.log Cm (B ^ (2 * K)) :=
        Nat.pow_le_pow_right hCm_pos (by omega)
      have hle_B : Cm ^ (i + 1) ≤ B ^ (2 * K) :=
        hpow_le.trans (Nat.pow_log_le_self Cm (pow_pos hB_pos (2 * K)).ne')
      exact Nat.div_pos hle_B (pow_pos hCm_pos (i + 1))
    have hdiv_le : B ^ (2 * K) / Cm ^ (i + 1) ≤ B ^ (2 * K - 1) := by
      rw [← hdiv_B]
      refine Nat.div_le_div_left ?_ hB_pos
      calc B = B ^ 1 := (pow_one B).symm
        _ ≤ Cm ^ 1 := Nat.pow_le_pow_left hBm 1
        _ ≤ Cm ^ (i + 1) := Nat.pow_le_pow_right hCm_pos (by omega)
    rw [ha _ hdiv_pos hdiv_le, hb _ hdiv_pos hdiv_le]
  have hm0 : B ≤ (tailRadix tc 0).val := by rw [hrad]
  have hm1 : B ≤ (tailRadix tc 1).val := by
    rw [tailRadix_succ, PNat.pow_coe, hrad]
    nlinarith
  rw [weightedAdjacentCutoff, weightedAdjacentCutoff, hsh 0 hm0, hsh 1 hm1]

/-- **Exact finite-depth collapse of the intrinsic Euler sieve:** whenever `K ≥ 1` and
`3^(2K - 1) ≤ y`, sieving primes `p ≤ y` inside the prime-gas shells removes every `n ≥ 2` from all
inner shell cutoffs, collapsing `weightedAlignedReconstructed` identically to `w - 1` on `Re w > 0`. -/
theorem weightedAlignedReconstructed_eulerSieve_eq_sub_one
    {K y : ℕ} (hK : 1 ≤ K) (hy : 3 ^ (2 * K - 1) ≤ y) {w : ℂ} (hw : 0 < w.re) :
    weightedAlignedReconstructed
      (dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y)) K w = w - 1 := by
  have h23 : 2 ^ (2 * K - 1) ≤ 3 ^ (2 * K - 1) :=
    Nat.pow_le_pow_left (by norm_num) (2 * K - 1)
  have h3_le_9 : 3 ^ (2 * K - 1) ≤ 3 ^ (2 * K) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmob_one : ∀ Y : ℕ, 1 ≤ Y → Y ≤ 3 ^ (2 * K - 1) →
      weightedRadialCutoff (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) Y w = 1 := by
    intro Y hY1 hY3
    have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 Y := by
      intro n hn; rw [Finset.mem_singleton.mp hn]; exact Finset.mem_Icc.mpr ⟨le_rfl, hY1⟩
    unfold weightedRadialCutoff
    rw [← Finset.sum_subset hsub]
    · simp [dirichletSurgWeight_moebiusReal_of_le le_rfl (hY1.trans (hY3.trans h3_le_9))]
    · intro n hn hnot
      rw [Finset.mem_Icc] at hn
      rw [dirichletSurgWeight_moebiusReal_of_le hn.1 (hn.2.trans (hY3.trans h3_le_9)),
        if_neg (by simpa using hnot)]
      simp
  have hc2 := weightedAdjacentCutoff_congr_of_radial_eq_one
    (a := dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y))
    (b := dirichletSurgWeight (3 ^ (2 * K)) moebiusReal)
    halfTurnClock 2 (by norm_num) hK (congrArg PNat.val tailRadix_halfTurnClock_zero)
    (fun Y hY1 hY2 => weightedRadialCutoff_eulerSieve_of_le hY1
      ((hY2.trans h23).trans hy) w)
    (fun Y hY1 hY2 => hmob_one Y hY1 (hY2.trans h23))
  have hc3 := weightedAdjacentCutoff_congr_of_radial_eq_one
    (a := dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y))
    (b := dirichletSurgWeight (3 ^ (2 * K)) moebiusReal)
    primeThreeClock 3 (by norm_num) hK (congrArg PNat.val tailRadix_primeThreeClock_zero)
    (fun Y hY1 hY3 => weightedRadialCutoff_eulerSieve_of_le hY1 (hY3.trans hy) w)
    (fun Y hY1 hY3 => hmob_one Y hY1 hY3)
  have heq : weightedAlignedReconstructed
        (dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y)) K w =
      weightedAlignedReconstructed (dirichletSurgWeight (3 ^ (2 * K)) moebiusReal) K w := by
    unfold weightedAlignedReconstructed
    rw [hc2, hc3]
  exact heq.trans (weightedAlignedReconstructed_fullMoebius_eq_sub_one hK le_rfl hw)

private theorem abs_eulerSieveSurgCoeff_le_one (y d : ℕ) : |eulerSieveSurgCoeff y d| ≤ 1 := by
  unfold eulerSieveSurgCoeff
  split_ifs
  · by_cases hsq : Squarefree d
    · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, Int.cast_pow, Int.cast_neg,
        Int.cast_one, abs_pow, abs_neg, abs_one, one_pow]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero, abs_zero]
      exact zero_le_one
  · rw [abs_zero]; exact zero_le_one

private theorem zetaFreeAdjacentBound_nonneg_aux (t : ExceptionalTime) (j : ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) {w : ℂ} (hw : 0 < w.re) :
    0 ≤ zetaFreeAdjacentBound t j Y w := by
  have hzf : ∀ m : ℕ, 0 ≤ zetaFreeTruncationBound t m Y w := by
    intro m
    have hC1 : (1 : ℝ) < (tailRadix t m).val := by exact_mod_cast radix_gt_one t m
    have hYr1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hl : 0 ≤ Real.logb (tailRadix t m).val (Y : ℝ) := Real.logb_nonneg hC1 hYr1
    have hc_nn : 0 ≤ zetaFreeDigitErrorConst t m w := by
      unfold zetaFreeDigitErrorConst; dsimp only
      have h1 : 0 ≤ 2 * ((tailRadix t m).val : ℝ) / (((tailRadix t m).val - 1) * ‖1 - w‖) :=
        div_nonneg (by positivity) (mul_nonneg (sub_pos.mpr hC1).le (norm_nonneg _))
      have h2 : 0 ≤ 2 * ((tailRadix t m).val : ℝ) / ((tailRadix t m).val - 1) + 1 :=
        add_nonneg (div_nonneg (by positivity) (sub_pos.mpr hC1).le) zero_le_one
      have h3 : 0 ≤ (((tailRadix t m).val : ℝ) / ((tailRadix t m).val - 1)) *
          (2 : ℝ) ^ (w.re + 1) * (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1))) :=
        mul_nonneg (mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hC1).le)
          (Real.rpow_nonneg zero_le_two _))
          (add_nonneg (by positivity) (div_nonneg (norm_nonneg _) (by linarith)))
      linarith
    unfold zetaFreeTruncationBound
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  unfold zetaFreeAdjacentBound
  exact add_nonneg (hzf j) (mul_nonneg (by positivity) (hzf (j + 1)))

/-- **Growing-aperture intrinsic Euler-sieve zero-threshold decay across `Re w > 1/2`:** along any
schedule `y : ℕ → ℕ` with `eulerPrimorial (y K) ≤ 2^K` (so `y K` may grow linearly with `K`),
`intrinsicDirichletZeroThreshold (eulerPrimorial (y K)) (eulerSieveSurgCoeff (y K)) K w → 0`
as `K → ∞` whenever `1 / 2 < w.re`. -/
theorem tendsto_intrinsicZeroThreshold_growing_eulerSieve_zero
    {y : ℕ → ℕ} (hy : ∀ᶠ K : ℕ in atTop, eulerPrimorial (y K) ≤ 2 ^ K)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    Tendsto (fun K : ℕ =>
      intrinsicDirichletZeroThreshold (eulerPrimorial (y K)) (eulerSieveSurgCoeff (y K)) K w)
      atTop (𝓝 0) := by
  have hw0 : 0 < w.re := by linarith
  have hmaj := tendsto_intrinsicZeroThreshold_two_pow_zero (c := fun _ => (1 : ℝ))
    (fun _ => by simp) hw
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1, hy] with K hK1 hyK
    have hm_pos : 0 < twoPrimeTransferMass w := two_prime_transfer_mass_pos ⟨w, hw0⟩
    have hchan_nn : ∀ (tc : ExceptionalTime) (B : ℕ), 2 ≤ B →
        0 ≤ (∑ d ∈ Finset.Icc (1 : ℕ) (eulerPrimorial (y K)),
          |eulerSieveSurgCoeff (y K) d| * (d : ℝ) ^ (-w.re) *
            zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) /
          (1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) := by
      intro tc B hB2
      have hBr1 : (1 : ℝ) < B := by exact_mod_cast (by omega : 1 < B)
      have hden : 0 < 1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re) :=
        sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hBr1
          (mul_neg_of_neg_of_pos (by have : (0 : ℝ) < K := Nat.cast_pos.mpr hK1; linarith) hw0))
      refine div_nonneg (Finset.sum_nonneg fun d hd => ?_) hden.le
      rw [Finset.mem_Icc] at hd
      have hle : d ≤ B ^ (2 * K) :=
        (hd.2.trans hyK).trans ((Nat.pow_le_pow_right (by norm_num) (by omega : K ≤ 2 * K)).trans
          (Nat.pow_le_pow_left hB2 (2 * K)))
      have hdiv1 : 1 ≤ B ^ (2 * K) / d :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [one_mul]; exact hle)
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
        (zetaFreeAdjacentBound_nonneg_aux tc 0 hdiv1 hw0)
    unfold intrinsicDirichletZeroThreshold
    exact div_nonneg (add_nonneg
      (mul_nonneg (norm_nonneg _) (hchan_nn halfTurnClock 2 (by norm_num)))
      (mul_nonneg (norm_nonneg _) (hchan_nn primeThreeClock 3 (by norm_num)))) hm_pos.le
  · filter_upwards [eventually_ge_atTop 1, hy] with K hK1 hyK
    have hm_pos : 0 < twoPrimeTransferMass w := two_prime_transfer_mass_pos ⟨w, hw0⟩
    have hchan_le : ∀ (tc : ExceptionalTime) (B : ℕ), 2 ≤ B →
        (∑ d ∈ Finset.Icc (1 : ℕ) (eulerPrimorial (y K)),
          |eulerSieveSurgCoeff (y K) d| * (d : ℝ) ^ (-w.re) *
            zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) /
          (1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) ≤
        (∑ d ∈ Finset.Icc (1 : ℕ) (2 ^ K),
          |(1 : ℝ)| * (d : ℝ) ^ (-w.re) *
            zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w) /
          (1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re)) := by
      intro tc B hB2
      have hBr1 : (1 : ℝ) < B := by exact_mod_cast (by omega : 1 < B)
      have hden : 0 < 1 - (B : ℝ) ^ (-(2 * K : ℝ) * w.re) :=
        sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hBr1
          (mul_neg_of_neg_of_pos (by have : (0 : ℝ) < K := Nat.cast_pos.mpr hK1; linarith) hw0))
      have hzf_nn : ∀ d ∈ Finset.Icc (1 : ℕ) (2 ^ K),
          0 ≤ zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hle : d ≤ B ^ (2 * K) :=
          hd.2.trans ((Nat.pow_le_pow_right (by norm_num) (by omega : K ≤ 2 * K)).trans
            (Nat.pow_le_pow_left hB2 (2 * K)))
        have hdiv1 : 1 ≤ B ^ (2 * K) / d :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [one_mul]; exact hle)
        exact zetaFreeAdjacentBound_nonneg_aux tc 0 hdiv1 hw0
      refine div_le_div_of_nonneg_right ?_ hden.le
      calc ∑ d ∈ Finset.Icc (1 : ℕ) (eulerPrimorial (y K)),
              |eulerSieveSurgCoeff (y K) d| * (d : ℝ) ^ (-w.re) *
                zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w
          ≤ ∑ d ∈ Finset.Icc (1 : ℕ) (eulerPrimorial (y K)),
              |(1 : ℝ)| * (d : ℝ) ^ (-w.re) *
                zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd2 : d ∈ Finset.Icc (1 : ℕ) (2 ^ K) := Finset.Icc_subset_Icc_right hyK hd
            rw [abs_one]
            have h1 := mul_le_mul_of_nonneg_right (abs_eulerSieveSurgCoeff_le_one (y K) d)
              (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) (-w.re)) (hzf_nn d hd2))
            linarith
        _ ≤ ∑ d ∈ Finset.Icc (1 : ℕ) (2 ^ K),
              |(1 : ℝ)| * (d : ℝ) ^ (-w.re) *
                zetaFreeAdjacentBound tc 0 (B ^ (2 * K) / d) w := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hyK) fun d hd _ => ?_
            exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
              (hzf_nn d hd)
    unfold intrinsicDirichletZeroThreshold
    exact div_le_div_of_nonneg_right (add_le_add
      (mul_le_mul_of_nonneg_left (hchan_le halfTurnClock 2 (by norm_num)) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hchan_le primeThreeClock 3 (by norm_num)) (norm_nonneg _)))
      hm_pos.le

/-- **Zero-free intrinsic Euler-sieve margin equivalence across `Re w > 0` (`w ≠ 1`):** for **every**
fixed aperture `y : ℕ`, unlike external Euler multiplication (which preserves the unmollified depth
set) and unlike `moebiusReal` (whose Dirichlet polynomial can vanish), an intrinsic Euler-sieve
shell margin holds at `w` **if and only if** `riemannZeta w ≠ 0`. -/
theorem intrinsic_eulerSieve_margin_iff_zeta_ne_zero (y : ℕ) {w : ℂ}
    (hw : 0 < w.re) (hw1 : w ≠ 1) :
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧ eulerPrimorial y ≤ 2 ^ (2 * K₀) ∧
      intrinsicDirichletZeroThreshold (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ w <
        ‖weightedAlignedReconstructed
          (dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y)) K₀ w‖) ↔
      riemannZeta w ≠ 0 := by
  constructor
  · rintro ⟨K₀, hK1, hM, hmarg⟩
    exact (intrinsicDirichlet_margin_forces_zeta_ne_zero
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hK1 hM hw hw1 hmarg).1
  · intro hzeta
    have hQ_ne := dirichletSurgPoly_eulerSieve_ne_zero y hw
    have hZ_ne : _root_.RHTower.zetaPoleUnit w ≠ 0 := by
      rw [_root_.RHTower.zetaPoleUnit_of_ne hw1]
      exact mul_ne_zero (sub_ne_zero.mpr hw1) hzeta
    have hpos : 0 < ‖dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w *
        _root_.RHTower.zetaPoleUnit w‖ :=
      norm_pos_iff.mpr (mul_ne_zero hQ_ne hZ_ne)
    have hlim := (tendsto_weightedAlignedReconstructed_dirichletSurgWeight
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hw).norm
    have hthr := tendsto_intrinsicDirichletZeroThreshold_zero
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hw
    obtain ⟨K₀, ⟨⟨hK1, hKP⟩, hthr_lt⟩, hw_gt⟩ :=
      ((((eventually_ge_atTop 1).and (eventually_ge_atTop (eulerPrimorial y))).and
        (hthr.eventually (Iio_mem_nhds (half_pos hpos)))).and
        (hlim.eventually (Ioi_mem_nhds (half_lt_self hpos)))).exists
    have hP_le : eulerPrimorial y ≤ 2 ^ (2 * K₀) :=
      hKP.trans ((by omega : K₀ ≤ 2 * K₀).trans (Nat.lt_pow_self (by norm_num : 1 < 2)).le)
    exact ⟨K₀, hK1, hP_le, hthr_lt.trans hw_gt⟩

/-- **Single-aperture intrinsic Euler-sieve `RH` equivalence above `84.5`:** for **every** fixed
sieve aperture `y : ℕ`, `RiemannHypothesis` is unconditionally equivalent to a strict intrinsic
Euler-sieve shell margin at every point in `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}`. -/
theorem rh_iff_intrinsic_eulerSieve_margin_above_eightyFour_and_half (y : ℕ) :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ K₀ : ℕ, 1 ≤ K₀ ∧ eulerPrimorial y ≤ 2 ^ (2 * K₀) ∧
          intrinsicDirichletZeroThreshold (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ w <
            ‖weightedAlignedReconstructed
              (dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y)) K₀ w‖ := by
  rw [rh_iff_zetaFree_margin_above_eightyFour_and_half halfTurnClock 0]
  refine forall_congr' fun w => imp_congr_right fun hlo => imp_congr_right fun hhi =>
    imp_congr_right fun _ => ?_
  have hw0 : 0 < w.re := by linarith
  have hw_lt1 : w.re < 1 := by linarith
  have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
  rw [exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw1,
    intrinsic_eulerSieve_margin_iff_zeta_ne_zero y hw0 hw1]

#print axioms adjacentCutoff_eq_zero_of_lt_tailRadix
#print axioms weightedAdjacentCutoff_fullMoebius_eq_of_pred_pow
#print axioms weightedAlignedReconstructed_fullMoebius_eq_sub_one_of_pred_pow
#print axioms intrinsicMoebiusTail_eq_triadic_of_two_pow_pred_le
#print axioms moebiusChannelTail_eq_quotient_sum
#print axioms intrinsicMoebiusTail_eq_hyperbola_quotient_sum
#print axioms weightedAlignedReconstructed_eulerSieve_eq_sub_one
#print axioms tendsto_intrinsicZeroThreshold_growing_eulerSieve_zero
#print axioms intrinsic_eulerSieve_margin_iff_zeta_ne_zero
#print axioms rh_iff_intrinsic_eulerSieve_margin_above_eightyFour_and_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
