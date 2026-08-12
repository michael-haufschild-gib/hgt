import GaloisForLFunctions.RHTower.Sieve.RouteERamareIntegerIncidence

/-!
# Route E: conditional negativity of the Ramaré incidence complement

The normalized distinct-incidence coefficient is not merely bounded by one.  Its quadratic form
has the exact Gram decomposition

`Q(c) = ‖∑ c_n‖² - ∑ₚ ‖∑_{p ∣ n} c_n / |P(n)|‖²`.

Consequently its restriction to centered histories is negative semidefinite, with exact radical
given by simultaneous cancellation of every normalized prime load.  This removes the centered
incidence covariance from the positive Route E burden: only the noncentered scalar mode and the
source-faithful moving physical seam can contribute positive mass.
-/

namespace RHTower.Sieve

open Finset

/-- Normalized prime-load coordinate of a finite integer history. -/
noncomputable def routeENormalizedIncidenceBlock
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset κ) (F : κ → Finset ι) (c : κ → ℂ) (p : ι) : ℂ :=
  routeEIncidenceBlock S F (fun n => c n / ((F n).card : ℂ)) p

/-- Generic normalized complement of the shared-incidence diagonal. -/
noncomputable def routeEIncidenceComplement
    {ι : Type*} [DecidableEq ι] (A B : Finset ι) : ℝ :=
  1 - ((A ∩ B).card : ℝ) / ((A.card : ℝ) * (B.card : ℝ))

/-- Normalized prime loads sum back to the complete integer history. -/
theorem routeE_sum_normalizedIncidenceBlock
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (S : Finset κ) (F : κ → Finset ι) (c : κ → ℂ)
    (hFsub : ∀ n ∈ S, F n ⊆ P) (hFne : ∀ n ∈ S, (F n).Nonempty) :
    ∑ p ∈ P, routeENormalizedIncidenceBlock S F c p = ∑ n ∈ S, c n := by
  classical
  simp only [routeENormalizedIncidenceBlock, routeEIncidenceBlock]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_filter]
  have hfilter : P.filter (fun p => p ∈ F n) = F n := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.2
    · exact fun hp => ⟨hFsub n hn hp, hp⟩
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((F n).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (hFne n hn)).ne'
  field_simp

/-- Every finite off-diagonal block sum is total Gram mass minus diagonal block energy. -/
theorem routeE_offDiagonalBlock_eq_total_normSq_sub_diagonal
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (B : ι → ℂ) :
    ∑ p ∈ P, ∑ q ∈ P.erase p, (B p * (starRingEnd ℂ) (B q)).re =
      Complex.normSq (∑ p ∈ P, B p) - ∑ p ∈ P, Complex.normSq (B p) := by
  classical
  have hgram :
      Complex.normSq (∑ p ∈ P, B p) =
        ∑ p ∈ P, ∑ q ∈ P, (B p * (starRingEnd ℂ) (B q)).re := by
    calc
      Complex.normSq (∑ p ∈ P, B p) =
          (((∑ p ∈ P, B p) * (starRingEnd ℂ) (∑ q ∈ P, B q))).re := by
            simp [Complex.normSq_apply]
      _ = _ := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
        rw [Finset.sum_comm]
  rw [hgram]
  have hsplit : ∀ p ∈ P,
      (∑ q ∈ P, (B p * (starRingEnd ℂ) (B q)).re) =
        (∑ q ∈ P.erase p, (B p * (starRingEnd ℂ) (B q)).re) +
          Complex.normSq (B p) := by
    intro p hp
    rw [← Finset.sum_erase_add P
      (fun q => (B p * (starRingEnd ℂ) (B q)).re) hp]
    simp [Complex.normSq_apply, Complex.mul_re]
  have hall :
      (∑ p ∈ P, ∑ q ∈ P, (B p * (starRingEnd ℂ) (B q)).re) =
        ∑ p ∈ P, ((∑ q ∈ P.erase p, (B p * (starRingEnd ℂ) (B q)).re) +
          Complex.normSq (B p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hsplit p hp
  rw [hall, Finset.sum_add_distrib]
  ring

/--
Exact Gram decomposition of the normalized incidence-complement quadratic form.
-/
theorem routeE_incidenceComplement_decomposition
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (S : Finset κ) (F : κ → Finset ι) (c : κ → ℂ)
    (hFsub : ∀ n ∈ S, F n ⊆ P) (hFne : ∀ n ∈ S, (F n).Nonempty) :
    ∑ n ∈ S, ∑ m ∈ S,
        routeEIncidenceComplement (F n) (F m) *
          (c n * (starRingEnd ℂ) (c m)).re =
      Complex.normSq (∑ n ∈ S, c n) -
        ∑ p ∈ P, Complex.normSq (routeENormalizedIncidenceBlock S F c p) := by
  classical
  rw [← routeE_sum_normalizedIncidenceBlock P S F c hFsub hFne]
  rw [← routeE_offDiagonalBlock_eq_total_normSq_sub_diagonal P
    (routeENormalizedIncidenceBlock S F c)]
  change _ = ∑ p ∈ P, ∑ q ∈ P.erase p,
    ((routeEIncidenceBlock S F (fun n => c n / ((F n).card : ℂ)) p) *
      (starRingEnd ℂ)
        (routeEIncidenceBlock S F (fun n => c n / ((F n).card : ℂ)) q)).re
  rw [routeE_offDiagonal_incidenceBlock_sum_reindex]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hratio := routeEDistinctIncidenceRatio_eq_one_sub_inter
    (hFsub n hn) (hFsub m hm) (hFne n hn) (hFne m hm)
  rw [routeEIncidenceComplement, ← hratio]
  have hnc : ((F n).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (hFne n hn)).ne'
  have hmc : ((F m).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (hFne m hm)).ne'
  have hnr : ((F n).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (hFne n hn)).ne'
  have hmr : ((F m).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (hFne m hm)).ne'
  simp only [Complex.mul_re, map_div₀, map_natCast, Complex.div_re, Complex.div_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_natCast]
  norm_num
  field_simp
  ring

/-- Sharp centered law: the complement covariance is minus prime-load energy. -/
theorem routeE_centeredIncidenceComplement_eq_neg_energy
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (S : Finset κ) (F : κ → Finset ι) (c : κ → ℂ)
    (hFsub : ∀ n ∈ S, F n ⊆ P) (hFne : ∀ n ∈ S, (F n).Nonempty)
    (hcentered : ∑ n ∈ S, c n = 0) :
    ∑ n ∈ S, ∑ m ∈ S,
        routeEIncidenceComplement (F n) (F m) *
          (c n * (starRingEnd ℂ) (c m)).re =
      -∑ p ∈ P, Complex.normSq (routeENormalizedIncidenceBlock S F c p) := by
  rw [routeE_incidenceComplement_decomposition P S F c hFsub hFne, hcentered]
  simp

theorem routeE_centeredIncidenceComplement_nonpos
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (S : Finset κ) (F : κ → Finset ι) (c : κ → ℂ)
    (hFsub : ∀ n ∈ S, F n ⊆ P) (hFne : ∀ n ∈ S, (F n).Nonempty)
    (hcentered : ∑ n ∈ S, c n = 0) :
    ∑ n ∈ S, ∑ m ∈ S,
        routeEIncidenceComplement (F n) (F m) *
          (c n * (starRingEnd ℂ) (c m)).re ≤ 0 := by
  rw [routeE_centeredIncidenceComplement_eq_neg_energy P S F c hFsub hFne hcentered]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun p hp => Complex.normSq_nonneg _)

/-- Exact radical: centered complement covariance vanishes iff every prime load vanishes. -/
theorem routeE_centeredIncidenceComplement_eq_zero_iff
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (S : Finset κ) (F : κ → Finset ι) (c : κ → ℂ)
    (hFsub : ∀ n ∈ S, F n ⊆ P) (hFne : ∀ n ∈ S, (F n).Nonempty)
    (hcentered : ∑ n ∈ S, c n = 0) :
    (∑ n ∈ S, ∑ m ∈ S,
        routeEIncidenceComplement (F n) (F m) *
          (c n * (starRingEnd ℂ) (c m)).re = 0) ↔
      ∀ p ∈ P, routeENormalizedIncidenceBlock S F c p = 0 := by
  rw [routeE_centeredIncidenceComplement_eq_neg_energy P S F c hFsub hFne hcentered,
    neg_eq_zero]
  constructor
  · intro hsum p hp
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q hq => Complex.normSq_nonneg (routeENormalizedIncidenceBlock S F c q))).mp
      hsum p hp
    exact Complex.normSq_eq_zero.mp hterm
  · intro hzero
    apply Finset.sum_eq_zero
    intro p hp
    rw [hzero p hp, Complex.normSq_zero]

/-- Arithmetic specialization of the exact conditional-negative decomposition. -/
theorem ramareIncidenceComplement_decomposition
    (P : Finset ℕ) (M : ℕ) (c : ℕ → ℂ) :
    ∑ n ∈ ramareActiveSet P M, ∑ m ∈ ramareActiveSet P M,
        ramareIncidenceComplement P n m *
          (c n * (starRingEnd ℂ) (c m)).re =
      Complex.normSq (∑ n ∈ ramareActiveSet P M, c n) -
        ∑ p ∈ P, Complex.normSq
          (routeENormalizedIncidenceBlock (ramareActiveSet P M) (primeFactorsIn P) c p) := by
  have hsub : ∀ n ∈ ramareActiveSet P M, primeFactorsIn P n ⊆ P := by
    intro n hn p hp
    exact (mem_primeFactorsIn.mp hp).1
  have hne : ∀ n ∈ ramareActiveSet P M, (primeFactorsIn P n).Nonempty := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  simpa [routeEIncidenceComplement, ramareIncidenceComplement] using
    routeE_incidenceComplement_decomposition P (ramareActiveSet P M)
      (primeFactorsIn P) c hsub hne

/-- Centered arithmetic histories have exactly negative normalized prime-load energy. -/
theorem ramareCenteredIncidenceComplement_eq_neg_energy
    (P : Finset ℕ) (M : ℕ) (c : ℕ → ℂ)
    (hcentered : ∑ n ∈ ramareActiveSet P M, c n = 0) :
    ∑ n ∈ ramareActiveSet P M, ∑ m ∈ ramareActiveSet P M,
        ramareIncidenceComplement P n m *
          (c n * (starRingEnd ℂ) (c m)).re =
      -∑ p ∈ P, Complex.normSq
        (routeENormalizedIncidenceBlock (ramareActiveSet P M) (primeFactorsIn P) c p) := by
  rw [ramareIncidenceComplement_decomposition P M c, hcentered]
  simp

theorem ramareCenteredIncidenceComplement_nonpos
    (P : Finset ℕ) (M : ℕ) (c : ℕ → ℂ)
    (hcentered : ∑ n ∈ ramareActiveSet P M, c n = 0) :
    ∑ n ∈ ramareActiveSet P M, ∑ m ∈ ramareActiveSet P M,
        ramareIncidenceComplement P n m *
          (c n * (starRingEnd ℂ) (c m)).re ≤ 0 := by
  rw [ramareCenteredIncidenceComplement_eq_neg_energy P M c hcentered]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun p hp => Complex.normSq_nonneg _)

/-- Actual Möbius integrand: scalar active mass minus normalized prime-load energy. -/
theorem ramarePrimeOffDiagonalIntegrand_eq_total_normSq_sub_primeLoadEnergy
    {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) (w : ℝ) :
    ∑ p ∈ P, ∑ q ∈ P.erase p,
        ((moebiusPhase w p * ramareCofactorPoly P M p w) *
          (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re =
      Complex.normSq (∑ n ∈ ramareActiveSet P M, moebiusPhase w n) -
        ∑ p ∈ P, Complex.normSq
          (routeENormalizedIncidenceBlock (ramareActiveSet P M) (primeFactorsIn P)
            (moebiusPhase w) p) := by
  rw [ramarePrimeOffDiagonalIntegrand_eq_integerIncidence hPprime]
  exact ramareIncidenceComplement_decomposition P M (moebiusPhase w)

end RHTower.Sieve
