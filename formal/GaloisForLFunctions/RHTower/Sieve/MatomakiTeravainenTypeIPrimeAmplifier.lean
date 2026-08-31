import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIRestrictedMoment
import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedDyadic

/-!
# Matomäki--Teräväinen Type-I prime amplifier

The source amplifier is a positive power of the prime polynomial on `(A,2A]`.  Its convolution
support is therefore `(A^ell,(2A)^ell]`, with the same endpoint convention as the Watt receiver.
This file proves the exact `ell`-block decomposition, the block pigeonhole, and the measurable
finite cover of the amplifier-large set.  Thus no point-dependent amplifier block is hidden in a
downstream hypothesis.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Dyadic decomposition with the source and Watt endpoint convention `(A,2A]`. -/
theorem mtSum_Ioc_dyadic {M : Type*} [AddCommMonoid M]
    (A : ℕ) (f : ℕ → M) (R : ℕ) :
    ∑ n ∈ Finset.Ioc A (A * 2 ^ R), f n =
      ∑ r ∈ Finset.range R,
        ∑ n ∈ Finset.Ioc (A * 2 ^ r) (A * 2 ^ (r + 1)), f n := by
  induction R with
  | zero => simp
  | succ R ih =>
      have hstart : A ≤ A * 2 ^ R := by
        calc
          A = A * 1 := (Nat.mul_one A).symm
          _ ≤ A * 2 ^ R := Nat.mul_le_mul_left A Nat.one_le_two_pow
      have hmono : A * 2 ^ R ≤ A * 2 ^ (R + 1) :=
        Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ioc_consecutive f hstart hmono]

/-- Strict lower support survives a positive convolution power. -/
theorem convPow_support_Ioc {N A ell : ℕ} (hell : 0 < ell)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A < (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (j : Fin (N ^ ell)) (hj : convPow N ell a j ≠ 0) :
    A ^ ell < (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ A ^ ell * 2 ^ ell := by
  have hclosed := convPow_support_dyadic a
    (fun n hn => ⟨(hsupp n hn).1.le, (hsupp n hn).2⟩) j hj
  have hplus := convPow_support_dyadic (A := A + 1) a
    (fun n hn => by
      have hs := hsupp n hn
      exact ⟨by omega, by omega⟩) j hj
  have hpow : A ^ ell < (A + 1) ^ ell :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  refine ⟨hpow.trans_le hplus.1, ?_⟩
  simpa [mul_pow, mul_comm] using hclosed.2

/-- A nonzero anchored raised term lies in the exact source interval
`(A^ell,A^ell*2^ell]`. -/
theorem anchoredDirichletTerm_convPow_support_Ioc
    {N A ell : ℕ} (hell : 0 < ell) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A < (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {t : ℝ} {n : ℕ}
    (hn : anchoredDirichletTerm (N ^ ell) (convPow N ell a) 1 t n ≠ 0) :
    n ∈ Finset.Ioc (A ^ ell) (A ^ ell * 2 ^ ell) := by
  have hcoeff : anchoredCoeff (N ^ ell) (convPow N ell a) n ≠ 0 := by
    intro hzero
    exact hn (by simp [anchoredDirichletTerm, hzero])
  obtain ⟨j, hj, hjn⟩ := anchoredCoeff_ne_zero_support hcoeff
  have hjbounds := convPow_support_Ioc hell a hsupp j hj
  simpa only [Finset.mem_Ioc, ← hjn] using hjbounds

/-- A Perron-line complex power is the real weight times the logarithmic phase used by the
anchored Dirichlet term. -/
theorem perronTerm_eq_anchoredDirichletTerm
    (M : ℕ) (b : Fin M → ℂ) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    anchoredCoeff M b n *
        (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * I)) =
      anchoredDirichletTerm M b 1 t n := by
  change anchoredCoeff M b n *
      (((n : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * I))) = _
  rw [Complex.cpow_eq_exp_log_ofReal (n : ℝ) (by exact_mod_cast hn)]
  simp only [anchoredDirichletTerm, Real.rpow_neg_one]
  have hinv : ((((n : ℝ)⁻¹ : ℝ)) : ℂ) =
      Complex.exp (((-Real.log (n : ℝ) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log (by exact_mod_cast hn)]
  rw [hinv, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A Watt block is exactly the corresponding sum of anchored raised terms on `(B,2B]`. -/
theorem mtWattCoefficientBlock_eq_sum_anchoredDirichletTerm_Ioc
    (M : ℕ) (b : Fin M → ℂ) (B : ℕ) (t : ℝ) :
    mtWattCoefficientBlock (anchoredCoeff M b) B t =
      ∑ n ∈ Finset.Ioc B (2 * B), anchoredDirichletTerm M b 1 t n := by
  rw [mtWattCoefficientBlock, perronPoly]
  have hsub : Finset.Ioc B (2 * B) ⊆ Finset.Icc 1 (2 * B) := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  let f : ℕ → ℂ := fun n =>
    mtRealIntervalAF (anchoredCoeff M b) (B : ℝ) (2 * B : ℝ) n *
      (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * I))
  change (∑ n ∈ Finset.Icc 1 (2 * B), f n) = _
  trans ∑ n ∈ Finset.Ioc B (2 * B), f n
  · symm
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hnpos : 0 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    dsimp only [f]
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
    have hnotrange : ¬((B : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (2 * B : ℝ)) := by
      intro hrange
      apply hnot
      simp only [Finset.mem_Ioc]
      exact_mod_cast hrange
    rw [if_neg hnotrange, zero_mul]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      simp only [Finset.mem_Ioc] at hn
      omega
    dsimp only [f]
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
    have hrange : (B : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (2 * B : ℝ) := by
      simp only [Finset.mem_Ioc] at hn
      exact_mod_cast hn
    rw [if_pos hrange]
    exact perronTerm_eq_anchoredDirichletTerm M b t hnpos

/-- The complete raised value may be restricted to its exact strict-lower dyadic support. -/
theorem raisedDirichletValue_eq_sum_Ioc
    {N A ell : ℕ} (hell : 0 < ell) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A < (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (t : ℝ) :
    raisedDirichletValue N ell a 1 t =
      ∑ n ∈ Finset.Ioc (A ^ ell) (A ^ ell * 2 ^ ell),
        anchoredDirichletTerm (N ^ ell) (convPow N ell a) 1 t n := by
  let s := Finset.Ico 1 (N ^ ell + 1)
  let u := Finset.Ioc (A ^ ell) (A ^ ell * 2 ^ ell)
  let f : ℕ → ℂ := fun n =>
    anchoredDirichletTerm (N ^ ell) (convPow N ell a) 1 t n
  have hs : ∑ n ∈ s, f n = ∑ n ∈ s ∪ u, f n := by
    apply Finset.sum_subset Finset.subset_union_left
    intro n hn hnot
    have hns : n ∉ s := by
      intro hmem
      exact hnot hmem
    have hzero : anchoredCoeff (N ^ ell) (convPow N ell a) n = 0 :=
      anchoredCoeff_eq_zero_of_not_mem_Ico _ _ hns
    simp [f, anchoredDirichletTerm, hzero]
  have hu : ∑ n ∈ u, f n = ∑ n ∈ s ∪ u, f n := by
    apply Finset.sum_subset Finset.subset_union_right
    intro n hn hnot
    have hnu : n ∉ u := by
      intro hmem
      exact hnot hmem
    by_contra hne
    exact hnu (anchoredDirichletTerm_convPow_support_Ioc hell a hsupp hne)
  exact hs.trans hu.symm

/-- Exact decomposition of a strict dyadic raised factor into `ell` Watt blocks. -/
theorem raisedDirichletValue_eq_sum_mtWattCoefficientBlock
    {N A ell : ℕ} (hell : 0 < ell) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A < (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (t : ℝ) :
    raisedDirichletValue N ell a 1 t =
      ∑ r ∈ Finset.range ell,
        mtWattCoefficientBlock
          (anchoredCoeff (N ^ ell) (convPow N ell a))
          (A ^ ell * 2 ^ r) t := by
  rw [raisedDirichletValue_eq_sum_Ioc hell a hsupp,
    mtSum_Ioc_dyadic (A ^ ell)
      (anchoredDirichletTerm (N ^ ell) (convPow N ell a) 1 t) ell]
  apply Finset.sum_congr rfl
  intro r hr
  symm
  rw [mtWattCoefficientBlock_eq_sum_anchoredDirichletTerm_Ioc]
  congr 2
  rw [pow_succ]
  ring

/-- A large raised value forces one of its exact `ell` Watt blocks to be large. -/
theorem exists_mtWattCoefficientBlock_large_of_raisedDirichletValue_large
    {N A ell : ℕ} (hell : 0 < ell) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A < (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    {t V : ℝ} (hlarge : V ≤ ‖raisedDirichletValue N ell a 1 t‖) :
    ∃ r : Fin ell,
      V / (ell : ℝ) ≤
        ‖mtWattCoefficientBlock
          (anchoredCoeff (N ^ ell) (convPow N ell a))
          (A ^ ell * 2 ^ (r : ℕ)) t‖ := by
  have hsum : V ≤ ∑ r : Fin ell,
      ‖mtWattCoefficientBlock
        (anchoredCoeff (N ^ ell) (convPow N ell a))
        (A ^ ell * 2 ^ (r : ℕ)) t‖ := by
    rw [raisedDirichletValue_eq_sum_mtWattCoefficientBlock hell a hsupp] at hlarge
    refine hlarge.trans ?_
    have hnorm := norm_sum_le
      (s := Finset.range ell)
      (f := fun r => mtWattCoefficientBlock
        (anchoredCoeff (N ^ ell) (convPow N ell a))
        (A ^ ell * 2 ^ r) t)
    calc
      ‖∑ r ∈ Finset.range ell,
          mtWattCoefficientBlock
            (anchoredCoeff (N ^ ell) (convPow N ell a))
            (A ^ ell * 2 ^ r) t‖ ≤
          ∑ r ∈ Finset.range ell,
            ‖mtWattCoefficientBlock
              (anchoredCoeff (N ^ ell) (convPow N ell a))
              (A ^ ell * 2 ^ r) t‖ := hnorm
      _ = ∑ r : Fin ell,
          ‖mtWattCoefficientBlock
            (anchoredCoeff (N ^ ell) (convPow N ell a))
            (A ^ ell * 2 ^ (r : ℕ)) t‖ := by
        symm
        exact Fin.sum_univ_eq_sum_range (fun r : ℕ =>
          ‖mtWattCoefficientBlock
            (anchoredCoeff (N ^ ell) (convPow N ell a))
            (A ^ ell * 2 ^ r) t‖) ell
  by_contra hcon
  push Not at hcon
  have hlt : (∑ r : Fin ell,
      ‖mtWattCoefficientBlock
        (anchoredCoeff (N ^ ell) (convPow N ell a))
        (A ^ ell * 2 ^ (r : ℕ)) t‖) < V := by
    calc
      (∑ r : Fin ell,
          ‖mtWattCoefficientBlock
            (anchoredCoeff (N ^ ell) (convPow N ell a))
            (A ^ ell * 2 ^ (r : ℕ)) t‖)
          < ∑ _r : Fin ell, V / (ell : ℝ) :=
            Finset.sum_lt_sum_of_nonempty
              (show (Finset.univ : Finset (Fin ell)).Nonempty from
                ⟨⟨0, hell⟩, Finset.mem_univ _⟩)
              (fun r _ => hcon r)
      _ = V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hellR : (0 : ℝ) < ell := by positivity
        field_simp
  linarith

/-- Integral union bound for a finite measurable-height cover, formulated through restricted
measures so overlapping blocks need not be disjoint. -/
theorem setIntegral_le_sum_setIntegral_of_subset_iUnion
    {ι : Type*} [Fintype ι] {E : Set ℝ} {S : ι → Set ℝ}
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hS : ∀ i, S i ⊆ Set.Icc a b)
    (hcover : E ⊆ ⋃ i, S i) (hnn : ∀ t, 0 ≤ f t) :
    (∫ t in E, f t) ≤ ∑ i : ι, ∫ t in S i, f t := by
  have hfull := hf.integrableOn_Icc (μ := volume) (a := a) (b := b)
  change Integrable f (volume.restrict (Set.Icc a b)) at hfull
  have hfi : ∀ i, Integrable f (volume.restrict (S i)) := fun i =>
    hfull.mono_measure (Measure.restrict_mono (hS i) le_rfl)
  have hsummable : Summable (fun i => ∫ t, ‖f t‖ ∂volume.restrict (S i)) := by
    apply summable_of_hasFiniteSupport
    exact Set.toFinite _
  have hsumInt : Integrable f (Measure.sum fun i => volume.restrict (S i)) :=
    integrable_sum_measure hfi hsummable
  have hμ : volume.restrict E ≤ Measure.sum (fun i => volume.restrict (S i)) :=
    (Measure.restrict_mono hcover le_rfl).trans Measure.restrict_iUnion_le
  have hmono := integral_mono_measure hμ
    (Filter.Eventually.of_forall hnn) hsumInt
  rw [integral_sum_measure hsumInt, tsum_fintype] at hmono
  exact hmono

/-- Indicator of primes in `(A,2A]`, represented on the anchored vector of length `2A`. -/
def mtTypeIPrimeCoeff (A : ℕ) : Fin (2 * A) → ℂ := fun j =>
  if Nat.Prime ((j : ℕ) + 1) ∧ A < (j : ℕ) + 1 then 1 else 0

theorem mtTypeIPrimeCoeff_support {A : ℕ} (j : Fin (2 * A))
    (hj : mtTypeIPrimeCoeff A j ≠ 0) :
    A < (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ 2 * A := by
  rw [mtTypeIPrimeCoeff] at hj
  split at hj
  next h => exact ⟨h.2, by omega⟩
  next h => exact (hj rfl).elim

/-- The literal powered prime amplifier. -/
noncomputable def mtTypeIPrimeAmplifier (A ell : ℕ) (t : ℝ) : ℂ :=
  raisedDirichletValue (2 * A) ell (mtTypeIPrimeCoeff A) 1 t

theorem continuous_mtTypeIPrimeAmplifier (A ell : ℕ) :
    Continuous (mtTypeIPrimeAmplifier A ell) := by
  rw [show mtTypeIPrimeAmplifier A ell = fun t =>
      (dirPoly (2 * A)
        (sigmaWeightedCoeff (2 * A) (mtTypeIPrimeCoeff A) 1) (-t)) ^ ell by
    funext t
    exact raisedDirichletValue_eq_pow (2 * A) ell (mtTypeIPrimeCoeff A) 1 t]
  exact ((continuous_dirPoly _ _).comp continuous_neg).pow ell

/-- Height-restricted large-value set of the complete powered prime amplifier. -/
noncomputable def mtTypeIPrimeAmplifierLargeSet
    (A ell : ℕ) (T V : ℝ) : Set ℝ :=
  Set.Icc (T / 2) T ∩ {t | V ≤ ‖mtTypeIPrimeAmplifier A ell t‖}

/-- Fixed Watt-block large-value set appearing in the exact raised-factor cover. -/
noncomputable def mtTypeIPrimeAmplifierBlockLargeSet
    (A ell : ℕ) (T V : ℝ) (r : Fin ell) : Set ℝ :=
  Set.Icc (T / 2) T ∩
    {t | V / (ell : ℝ) ≤
      ‖mtWattCoefficientBlock
        (anchoredCoeff ((2 * A) ^ ell)
          (convPow (2 * A) ell (mtTypeIPrimeCoeff A)))
        (A ^ ell * 2 ^ (r : ℕ)) t‖}

theorem measurableSet_mtTypeIPrimeAmplifierLargeSet
    (A ell : ℕ) (T V : ℝ) :
    MeasurableSet (mtTypeIPrimeAmplifierLargeSet A ell T V) := by
  exact (isClosed_Icc.inter
    (isClosed_le continuous_const
      (continuous_mtTypeIPrimeAmplifier A ell).norm)).measurableSet

theorem measurableSet_mtTypeIPrimeAmplifierBlockLargeSet
    (A ell : ℕ) (T V : ℝ) (r : Fin ell) :
    MeasurableSet (mtTypeIPrimeAmplifierBlockLargeSet A ell T V r) := by
  exact (isClosed_Icc.inter
    (isClosed_le continuous_const
      (continuous_perronPoly _ _ _).norm)).measurableSet

theorem mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc
    (A ell : ℕ) (T V : ℝ) (r : Fin ell) :
    mtTypeIPrimeAmplifierBlockLargeSet A ell T V r ⊆ Set.Icc (T / 2) T :=
  Set.inter_subset_left

/-- The complete amplifier-large set is covered by its fixed, measurable Watt-block sets. -/
theorem subset_iUnion_mtTypeIPrimeAmplifierBlockLargeSet
    {A ell : ℕ} (hell : 0 < ell) (T V : ℝ) :
    mtTypeIPrimeAmplifierLargeSet A ell T V ⊆
      ⋃ r : Fin ell, mtTypeIPrimeAmplifierBlockLargeSet A ell T V r := by
  intro t ht
  obtain ⟨r, hr⟩ := exists_mtWattCoefficientBlock_large_of_raisedDirichletValue_large
    hell (mtTypeIPrimeCoeff A) mtTypeIPrimeCoeff_support (hlarge := ht.2)
  rw [Set.mem_iUnion]
  exact ⟨r, ht.1, hr⟩

/-- Nonnegative mass on the complete prime-amplifier large set is paid by the sum over its fixed
Watt-block large sets. -/
theorem setIntegral_mtTypeIPrimeAmplifierLargeSet_le_sum_blocks
    {A ell : ℕ} (hell : 0 < ell) (T V : ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet A ell T V, f t) ≤
      ∑ r : Fin ell,
        ∫ t in mtTypeIPrimeAmplifierBlockLargeSet A ell T V r, f t := by
  exact setIntegral_le_sum_setIntegral_of_subset_iUnion hf
    (fun r => mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc A ell T V r)
    (subset_iUnion_mtTypeIPrimeAmplifierBlockLargeSet hell T V) hnn

end

end RHTower.Sieve
