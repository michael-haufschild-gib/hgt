import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedCoefficient
import GaloisForLFunctions.RHTower.Sieve.DirichletDyadicTailAssembly
import GaloisForLFunctions.RHTower.Sieve.HuxleyLargeValues

/-!
# Exact dyadic interface for a raised Maynard factor

This file connects the abstract convolution coefficients to Huxley's dyadic Hilbert rows.  A
finite coefficient vector is extended to anchored positive integers, weighted by `n^{-sigma}`, and
restricted to `[D,2D)`.  The row inner product is exactly the corresponding Dirichlet block, and
each block's Hilbert energy is bounded by the complete unweighted coefficient energy.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Extend a vector indexed by `1,...,M` to all natural anchors, by zero. -/
noncomputable def anchoredCoeff (M : ℕ) (b : Fin M → ℂ) (n : ℕ) : ℂ :=
  if h : 1 ≤ n ∧ n ≤ M then b ⟨n - 1, by omega⟩ else 0

@[simp] theorem anchoredCoeff_add_one (M : ℕ) (b : Fin M → ℂ) (j : Fin M) :
    anchoredCoeff M b ((j : ℕ) + 1) = b j := by
  rw [anchoredCoeff, dif_pos ⟨by omega, by omega⟩]
  congr 1

theorem anchoredCoeff_eq_zero_of_not_mem_Ico (M : ℕ) (b : Fin M → ℂ) {n : ℕ}
    (hn : n ∉ Finset.Ico 1 (M + 1)) : anchoredCoeff M b n = 0 := by
  rw [anchoredCoeff, dif_neg]
  simpa [Finset.mem_Ico] using hn

/-- The `n^{-sigma-it}` term attached to an anchored coefficient. -/
noncomputable def anchoredDirichletTerm (M : ℕ) (b : Fin M → ℂ)
    (sigma t : ℝ) (n : ℕ) : ℂ :=
  anchoredCoeff M b n * ((((n : ℕ) : ℝ) ^ (-sigma) : ℝ) : ℂ) *
    Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- Weighted coefficient vector on `[D,2D)`. -/
noncomputable def dyadicWeightedCoeff (M : ℕ) (b : Fin M → ℂ)
    (sigma : ℝ) (D : ℕ) : EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 (fun j : Fin D =>
    anchoredCoeff M b (D + (j : ℕ)) *
      (((((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma) : ℝ)) : ℂ))

/-- **Exact row/block identity.** -/
theorem inner_dyadicDirRow_dyadicWeightedCoeff (M : ℕ) (b : Fin M → ℂ)
    (sigma t : ℝ) (D : ℕ) :
    ⟪dyadicDirRow D t, dyadicWeightedCoeff M b sigma D⟫_ℂ
      = ∑ n ∈ Finset.Ico D (2 * D), anchoredDirichletTerm M b sigma t n := by
  rw [PiLp.inner_apply]
  simp only [dyadicDirRow, dyadicWeightedCoeff, RCLike.inner_apply]
  have hfin := Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    anchoredCoeff M b (D + j) * (((((D + j : ℕ) : ℝ) ^ (-sigma) : ℝ)) : ℂ) *
      (starRingEnd ℂ)
        (Complex.exp ((((t * Real.log ((D + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))) D
  rw [hfin]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : 2 * D - D = D := by omega
  rw [hlen]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hconj : (starRingEnd ℂ)
      (Complex.exp ((((t * Real.log ((D + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      = Complex.exp (((-(t * Real.log ((D + j : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj]
  simp only [anchoredDirichletTerm]

/-- The anchored extension has exactly the original coefficient energy. -/
theorem sum_normSq_anchoredCoeff_Ico (M : ℕ) (b : Fin M → ℂ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), ‖anchoredCoeff M b n‖ ^ 2
      = ∑ j : Fin M, ‖b j‖ ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : M + 1 - 1 = M := by omega
  rw [hlen]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ‖anchoredCoeff M b (j + 1)‖ ^ 2) M
  simpa [Nat.add_comm] using hfin.symm

/-- Any interval cut from the anchored extension has no more energy than the complete vector. -/
theorem sum_normSq_anchoredCoeff_Ico_le (M D : ℕ) (b : Fin M → ℂ) :
    ∑ n ∈ Finset.Ico D (2 * D), ‖anchoredCoeff M b n‖ ^ 2
      ≤ ∑ j : Fin M, ‖b j‖ ^ 2 := by
  let s := Finset.Ico D (2 * D)
  let u := Finset.Ico 1 (M + 1)
  have hcut : ∑ n ∈ s ∩ u, ‖anchoredCoeff M b n‖ ^ 2
      = ∑ n ∈ s, ‖anchoredCoeff M b n‖ ^ 2 := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hnot
    have hnu : n ∉ u := by
      intro hnu
      exact hnot (Finset.mem_inter.2 ⟨hn, hnu⟩)
    rw [anchoredCoeff_eq_zero_of_not_mem_Ico M b hnu, norm_zero, zero_pow]
    norm_num
  calc
    ∑ n ∈ Finset.Ico D (2 * D), ‖anchoredCoeff M b n‖ ^ 2
        = ∑ n ∈ s ∩ u, ‖anchoredCoeff M b n‖ ^ 2 := hcut.symm
    _ ≤ ∑ n ∈ u, ‖anchoredCoeff M b n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun n _ _ => sq_nonneg _)
    _ = ∑ j : Fin M, ‖b j‖ ^ 2 := sum_normSq_anchoredCoeff_Ico M b

/-- **Every weighted dyadic block is controlled by total unweighted energy.** -/
theorem norm_dyadicWeightedCoeff_sq_le (M D : ℕ) (b : Fin M → ℂ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hD : 1 ≤ D) :
    ‖dyadicWeightedCoeff M b sigma D‖ ^ 2 ≤ ∑ j : Fin M, ‖b j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hterm : ∀ j : Fin D,
      ‖(dyadicWeightedCoeff M b sigma D) j‖ ^ 2
        ≤ ‖anchoredCoeff M b (D + (j : ℕ))‖ ^ 2 := by
    intro j
    have hn1 : (1 : ℝ) ≤ ((D + (j : ℕ) : ℕ) : ℝ) := by
      exact_mod_cast le_trans hD (Nat.le_add_right D (j : ℕ))
    have hw0 : 0 ≤ (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma)) := Real.rpow_nonneg (by positivity) _
    have hw1 : (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    simp only [dyadicWeightedCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw0]
    have hc0 := norm_nonneg (anchoredCoeff M b (D + (j : ℕ)))
    have hmul : ‖anchoredCoeff M b (D + (j : ℕ))‖ *
        (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma))
          ≤ ‖anchoredCoeff M b (D + (j : ℕ))‖ := by
      nlinarith
    exact pow_le_pow_left₀ (mul_nonneg hc0 hw0) hmul 2
  calc
    ∑ j : Fin D, ‖(dyadicWeightedCoeff M b sigma D) j‖ ^ 2
        ≤ ∑ j : Fin D, ‖anchoredCoeff M b (D + (j : ℕ))‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = ∑ n ∈ Finset.Ico D (2 * D), ‖anchoredCoeff M b n‖ ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hlen : 2 * D - D = D := by omega
      rw [hlen]
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ => ‖anchoredCoeff M b (D + j)‖ ^ 2) D
    _ ≤ ∑ j : Fin M, ‖b j‖ ^ 2 := sum_normSq_anchoredCoeff_Ico_le M D b

/-- Complete weighted value of the raised coefficient vector. -/
noncomputable def raisedDirichletValue (N ℓ : ℕ) (a : Fin N → ℂ)
    (sigma t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 (N ^ ℓ + 1),
    anchoredDirichletTerm (N ^ ℓ) (convPow N ℓ a) sigma t n

/-- A nonzero anchored coefficient names a nonzero entry of the original vector. -/
theorem anchoredCoeff_ne_zero_support {M : ℕ} {b : Fin M → ℂ} {n : ℕ}
    (hn : anchoredCoeff M b n ≠ 0) :
    ∃ j : Fin M, b j ≠ 0 ∧ (j : ℕ) + 1 = n := by
  rw [anchoredCoeff] at hn
  split at hn
  next h =>
    rcases h with ⟨hn1, hnM⟩
    refine ⟨⟨n - 1, by omega⟩, hn, ?_⟩
    change n - 1 + 1 = n
    omega
  next h => exact (hn rfl).elim

/-- A nonzero weighted term from a raised dyadic factor lies in its fixed-width multiplicative
support `[A^ℓ,A^ℓ*2^(ℓ+1))`. -/
theorem anchoredDirichletTerm_convPow_support {N A ℓ : ℕ} (hA : 1 ≤ A)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {sigma t : ℝ} {n : ℕ}
    (hn : anchoredDirichletTerm (N ^ ℓ) (convPow N ℓ a) sigma t n ≠ 0) :
    n ∈ Finset.Ico (A ^ ℓ) (A ^ ℓ * 2 ^ (ℓ + 1)) := by
  have hcoeff : anchoredCoeff (N ^ ℓ) (convPow N ℓ a) n ≠ 0 := by
    intro hzero
    exact hn (by simp [anchoredDirichletTerm, hzero])
  obtain ⟨j, hj, hjn⟩ := anchoredCoeff_ne_zero_support hcoeff
  have hraised := convPow_support_dyadic a hsupp j hj
  have hupper_eq : (2 * A) ^ ℓ = A ^ ℓ * 2 ^ ℓ := by
    rw [mul_pow]
    ring
  have hpos : 0 < A ^ ℓ * 2 ^ ℓ := by positivity
  have hstrict : (2 * A) ^ ℓ < A ^ ℓ * 2 ^ (ℓ + 1) := by
    rw [hupper_eq, pow_succ]
    nlinarith
  exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-- Restricting the complete raised polynomial to its multiplicative support changes no term. -/
theorem raisedDirichletValue_eq_sum_support {N A ℓ : ℕ} (hA : 1 ≤ A)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (sigma t : ℝ) :
    raisedDirichletValue N ℓ a sigma t =
      ∑ n ∈ Finset.Ico (A ^ ℓ) (A ^ ℓ * 2 ^ (ℓ + 1)),
        anchoredDirichletTerm (N ^ ℓ) (convPow N ℓ a) sigma t n := by
  let s := Finset.Ico 1 (N ^ ℓ + 1)
  let u := Finset.Ico (A ^ ℓ) (A ^ ℓ * 2 ^ (ℓ + 1))
  let f : ℕ → ℂ := fun n =>
    anchoredDirichletTerm (N ^ ℓ) (convPow N ℓ a) sigma t n
  have hs : ∑ n ∈ s, f n = ∑ n ∈ s ∪ u, f n := by
    apply Finset.sum_subset Finset.subset_union_left
    intro n hn hns
    have hnot : n ∉ s := by
      intro hmem
      exact hns hmem
    have hzero : anchoredCoeff (N ^ ℓ) (convPow N ℓ a) n = 0 :=
      anchoredCoeff_eq_zero_of_not_mem_Ico _ _ hnot
    simp [f, anchoredDirichletTerm, hzero]
  have hu : ∑ n ∈ u, f n = ∑ n ∈ s ∪ u, f n := by
    apply Finset.sum_subset Finset.subset_union_right
    intro n hn hnu
    have hnot : n ∉ u := by
      intro hmem
      exact hnu hmem
    by_contra hne
    exact hnot (anchoredDirichletTerm_convPow_support hA a hsupp hne)
  exact hs.trans hu.symm

/-- **Exact fixed-cardinality dyadic decomposition of a raised factor.**  Raising a factor from
`[A,2A]` to the `ℓ`-th power creates exactly `ℓ+1` Huxley blocks; no logarithmic number of blocks
and no point-dependent choice is needed. -/
theorem raisedDirichletValue_eq_sum_dyadic {N A ℓ : ℕ} (hA : 1 ≤ A)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (sigma t : ℝ) :
    raisedDirichletValue N ℓ a sigma t =
      ∑ r ∈ Finset.range (ℓ + 1),
        ⟪dyadicDirRow (A ^ ℓ * 2 ^ r) t,
          dyadicWeightedCoeff (N ^ ℓ) (convPow N ℓ a) sigma (A ^ ℓ * 2 ^ r)⟫_ℂ := by
  rw [raisedDirichletValue_eq_sum_support hA a hsupp]
  rw [sum_Ico_dyadic (A ^ ℓ)
    (anchoredDirichletTerm (N ^ ℓ) (convPow N ℓ a) sigma t) (ℓ + 1)]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [inner_dyadicDirRow_dyadicWeightedCoeff]
  congr 2
  rw [pow_succ]
  ring

/-- Pointwise triangle inequality after exact raised-factor dyadic decomposition. -/
theorem norm_raisedDirichletValue_le_sum_dyadic {N A ℓ : ℕ} (hA : 1 ≤ A)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (sigma t : ℝ) :
    ‖raisedDirichletValue N ℓ a sigma t‖ ≤
      ∑ r : Fin (ℓ + 1),
        ‖⟪dyadicDirRow (A ^ ℓ * 2 ^ (r : ℕ)) t,
          dyadicWeightedCoeff (N ^ ℓ) (convPow N ℓ a) sigma
            (A ^ ℓ * 2 ^ (r : ℕ))⟫_ℂ‖ := by
  rw [raisedDirichletValue_eq_sum_dyadic hA a hsupp]
  refine (norm_sum_le _ _).trans_eq ?_
  rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    ‖⟪dyadicDirRow (A ^ ℓ * 2 ^ r) t,
      dyadicWeightedCoeff (N ^ ℓ) (convPow N ℓ a) sigma
        (A ^ ℓ * 2 ^ r)⟫_ℂ‖) (ℓ + 1)]

/-- **Raised-factor Huxley theorem.**  This is the complete structural Case 1A estimate: an
`ℓ`-fold power of one dyadic factor is handled by `ℓ+1` simultaneous Huxley rows, each with mass
bounded by the total convolution energy. -/
theorem huxley_raised_factor_large_values {N A ℓ : ℕ} (hA : 1 ≤ A)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (G : ℝ) (henergy : ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2 ≤ G)
    (U B : Fin (ℓ + 1) → ℝ) {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hV : 0 < V)
    (hU : ∀ q : Fin (ℓ + 1), 0 < U q)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : ∀ q : Fin (ℓ + 1),
      3 * U q ≤ 4 * Real.pi * ((A ^ ℓ * 2 ^ (q : ℕ) : ℕ) : ℝ))
    (hlamT : ∀ q : Fin (ℓ + 1),
      logDyadicLambda (A ^ ℓ * 2 ^ (q : ℕ)) T ≤ 1)
    (hB : ∀ q : Fin (ℓ + 1),
      logDyadicSecondEnvelope (A ^ ℓ * 2 ^ (q : ℕ)) (U q) T ≤ B q)
    (hB1 : ∀ q : Fin (ℓ + 1), 1 ≤ B q)
    (R : ℕ)
    (hdiam : ∀ r ∈ Finset.range (R + 1), ∀ s ∈ Finset.range (R + 1),
      |lam s - lam r| ≤ T)
    (hlarge : ∀ r ∈ Finset.range (R + 1),
      V ≤ ‖raisedDirichletValue N ℓ a sigma (lam r)‖)
    (habsorb : ((ℓ + 1 : ℕ) : ℝ) * ∑ q : Fin (ℓ + 1), G * B q ≤ V ^ 2 / 2) :
    ((R : ℝ) + 1) * V ^ 2
      ≤ 2 * ((ℓ + 1 : ℕ) : ℝ) * ∑ q : Fin (ℓ + 1),
          G * ((((A ^ ℓ * 2 ^ (q : ℕ) : ℕ) : ℝ)) +
            (12 * Real.pi * (((A ^ ℓ * 2 ^ (q : ℕ) : ℕ) : ℝ)) / delta) *
              ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1)) := by
  let D : Fin (ℓ + 1) → ℕ := fun q => A ^ ℓ * 2 ^ (q : ℕ)
  let c : ∀ q : Fin (ℓ + 1), EuclideanSpace ℂ (Fin (D q)) := fun q =>
    dyadicWeightedCoeff (N ^ ℓ) (convPow N ℓ a) sigma (D q)
  have hD : ∀ q, 1 ≤ D q := by
    intro q
    dsimp [D]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ℓ (by omega)) (pow_ne_zero (q : ℕ) (by norm_num)))
  have hmass : ∀ q, ‖c q‖ ^ 2 ≤ G := by
    intro q
    exact (norm_dyadicWeightedCoeff_sq_le _ _ _ hsigma (hD q)).trans henergy
  have hbig : ∀ r ∈ Finset.range (R + 1),
      V ≤ ∑ q : Fin (ℓ + 1), ‖⟪dyadicDirRow (D q) (lam r), c q⟫_ℂ‖ := by
    intro r hr
    exact (hlarge r hr).trans
      (norm_raisedDirichletValue_le_sum_dyadic hA a hsupp sigma (lam r))
  have habsorb' : (Fintype.card (Fin (ℓ + 1)) : ℝ) *
      ∑ q : Fin (ℓ + 1), G * B q ≤ V ^ 2 / 2 := by
    simpa using habsorb
  simpa [D, c] using huxley_multiblock_large_values D hD c
    (fun _ => G) U B hdelta hV hmass hU hgap hnear hlamT hB hB1 R hdiam hbig habsorb'

end RHTower.Sieve
