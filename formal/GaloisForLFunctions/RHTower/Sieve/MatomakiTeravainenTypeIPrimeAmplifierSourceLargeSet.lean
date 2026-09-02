import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeightDichotomy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownEnergyScheduleMoment

/-!
# Source large set for the Type-I prime amplifier

Section 5.1 starts from the set where the unraised prime polynomial is at least
`P^(-epsilon/10)`.  Raising to the canonical degree changes this threshold exactly to
`(P^ell)^(-epsilon/10)`.  This module identifies the source set with the powered-amplifier set
used by the restricted Type-I receiver.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Literal Section-5.1 large set cut out by the unraised prime polynomial. -/
noncomputable def mtTypeIPrimeSourceLargeSet
    (P : ℕ) (T epsilon : ℝ) : Set ℝ :=
  Set.Icc (T / 2) T ∩
    {t | (P : ℝ) ^ (-epsilon / 10) ≤ ‖mtTypeIPrimeAmplifier P 1 t‖}

/-- The powered prime amplifier is the corresponding power of the source prime polynomial. -/
theorem mtTypeIPrimeAmplifier_eq_source_pow
    (P ell : ℕ) (t : ℝ) :
    mtTypeIPrimeAmplifier P ell t =
      (mtTypeIPrimeAmplifier P 1 t) ^ ell := by
  rw [mtTypeIPrimeAmplifier, mtTypeIPrimeAmplifier,
    raisedDirichletValue_eq_pow, raisedDirichletValue_eq_pow]
  simp

/-- The paper's powered length produces exactly the powered source threshold. -/
theorem mtTypeIPrimeSourceThreshold_pow
    {P ell : ℕ} (hP : 1 ≤ P) (epsilon : ℝ) :
    ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) =
      ((P : ℝ) ^ (-epsilon / 10)) ^ ell := by
  have hP0 : (0 : ℝ) ≤ P := by positivity
  push_cast
  rw [← Real.rpow_natCast (P : ℝ) ell,
    ← Real.rpow_mul hP0,
    ← Real.rpow_natCast ((P : ℝ) ^ (-epsilon / 10)) ell,
    ← Real.rpow_mul hP0]
  congr 1
  ring

/-- Exact identification of the source large set with its powered-amplifier receiver set. -/
theorem mtTypeIPrimeAmplifierLargeSet_source_eq
    {P ell : ℕ} (hP : 1 ≤ P) (hell : ell ≠ 0) (T epsilon : ℝ) :
    mtTypeIPrimeAmplifierLargeSet P ell T
        ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) =
      mtTypeIPrimeSourceLargeSet P T epsilon := by
  ext t
  rw [mtTypeIPrimeAmplifierLargeSet, mtTypeIPrimeSourceLargeSet,
    Set.mem_inter_iff, Set.mem_inter_iff]
  apply and_congr_right
  intro _
  simp only [Set.mem_setOf_eq]
  rw [mtTypeIPrimeSourceThreshold_pow hP epsilon,
    mtTypeIPrimeAmplifier_eq_source_pow, norm_pow]
  constructor
  · intro h
    exact le_of_pow_le_pow_left₀ hell (norm_nonneg _) h
  · intro h
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) h ell

/-- At the canonical source degree, positivity of the degree discharges the only set-identity
side condition. -/
theorem mtTypeIPrimeAmplifierLargeSet_sourceDegree_eq
    {P : ℕ} (hP : 2 ≤ P) {T : ℝ} (hT : 1 < T) (epsilon : ℝ) :
    mtTypeIPrimeAmplifierLargeSet P (mtTypeIPrimeDegree P T) T
        ((((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ^ (-epsilon / 10)) =
      mtTypeIPrimeSourceLargeSet P T epsilon := by
  exact mtTypeIPrimeAmplifierLargeSet_source_eq (one_le_two.trans hP)
    (mtTypeIPrimeDegree_pos hP hT).ne' T epsilon

/-- Uniform source-scale set identity on the paper exponent and height ranges.  Prime-scale and
degree positivity are constructed internally. -/
theorem eventually_mtTypeIPrimeAmplifierLargeSet_sourceScale_eq :
    ∀ᶠ X : ℝ in atTop, ∀ alpha T epsilon : ℝ,
      (10999 / 10000 : ℝ) ≤ alpha →
      X ^ (1 / 4 : ℝ) ≤ T →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      2 ≤ P ∧ 1 < T ∧
        mtTypeIPrimeAmplifierLargeSet P ell T
            ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) =
          mtTypeIPrimeSourceLargeSet P T epsilon := by
  have hquarter :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards [hquarter, hlog, hXlarge] with X hquarterX hlogX hX
  intro alpha T epsilon halpha hXT
  dsimp only
  have halpha1 : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
  have hlogOne : (1 : ℝ) ≤ Real.log X :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
  have hscaleReal : Real.exp 2 ≤ (Real.log X) ^ alpha := by
    calc
      Real.exp 2 ≤ Real.log X := hlogX
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hlogOne halpha1
  have hP : 2 ≤ mtTypeIPrimeScale X alpha := mtTypeIPrimeScale_two_le hscaleReal
  have hT : 1 < T := by linarith [hquarterX.trans hXT]
  exact ⟨hP, hT, mtTypeIPrimeAmplifierLargeSet_sourceDegree_eq hP hT epsilon⟩

/-- Source-facing Section-5.1 receiver.  The amplifier threshold is the paper's canonical
`(P^ell)^(-epsilon/10)`, and the unraised source large set is identified with its powered receiver
set internally.  The unit-length/height branch is also selected internally. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceHeightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 2 ≤ N → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        let V := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          if (N : ℝ) ≤ T then
            ∑ r : Fin ell,
              mtTypeIPrimeHeathBrownEpsilonBlockMomentBound
                epsilon a A P ell N T V r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound C epsilon a A P ell N T V r := by
  obtain ⟨C, hC, hreceiver⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_heightDichotomy hepsilon
  refine ⟨C, hC, ?_⟩
  filter_upwards [hreceiver,
    eventually_mtTypeIPrimeAmplifierLargeSet_sourceScale_eq] with X hreceiverX hsetX
  intro alpha T a A N N' halpha halpha2 hXT hTX hA hN hNN' hN'le
  dsimp only
  let V : ℝ :=
    (((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)
  have hready := hsetX alpha T epsilon halpha hXT
  dsimp only at hready
  have hV : 0 < V := by
    dsimp only [V]
    have hPpos : 0 < mtTypeIPrimeScale X alpha := by omega
    have hpowPos : 0 < mtTypeIPrimeScale X alpha ^
        mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T := pow_pos hPpos _
    have hpowReal : (0 : ℝ) <
        (mtTypeIPrimeScale X alpha ^
          mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) := by
      exact_mod_cast hpowPos
    exact Real.rpow_pos_of_pos hpowReal _
  have hbound := hreceiverX alpha T a A N N' V halpha halpha2 hXT hTX
    hA hN hNN' hN'le hV
  dsimp only [V] at hbound
  have hset := hready.2.2
  rw [hset] at hbound
  exact hbound

/-- Canonical source-threshold block bound after sparse-loss and equation-(5.4) energy
absorption. -/
noncomputable def mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound
    (epsilon alpha : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T : ℝ)
    (r : Fin ell) : ℝ :=
  mtTypeIPrimeHeathBrownSparseEnergyBlockMomentBound epsilon alpha a A P ell N T
    ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) r

/-- Source-facing Section-5.1 height dichotomy after the sub-height branch has absorbed the
canonical threshold, fixed sparse saving, and exact powered-prime energy. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceSparseEnergyHeightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 2 ≤ N → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          if (N : ℝ) ≤ T then
            ∑ r : Fin ell,
              mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound
                epsilon alpha a A P ell N T r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound C epsilon a A P ell N T
                ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) r := by
  obtain ⟨C, hC, hlegacy⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceHeightDichotomy hepsilon
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlegacy,
    eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_sparseEnergy_sourceScale hepsilon,
    eventually_mtTypeIPrimeAmplifierLargeSet_sourceScale_eq]
      with X hlegacyX henergyX hsetX
  intro alpha T a A N N' halpha halpha2 hXT hTX hA hN hNN' hN'le
  dsimp only
  have hold := hlegacyX alpha T a A N N' halpha halpha2 hXT hTX
    hA hN hNN' hN'le
  dsimp only at hold
  by_cases hNT : (N : ℝ) ≤ T
  · let P := mtTypeIPrimeScale X alpha
    let ell := mtTypeIPrimeDegree P T
    let V : ℝ := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
    have hready := hsetX alpha T epsilon halpha hXT
    dsimp only [P, ell] at hready
    have hV : 0 < V := by
      dsimp only [V, P, ell]
      have hPpos : 0 < mtTypeIPrimeScale X alpha := by omega
      have hpowPos : 0 < mtTypeIPrimeScale X alpha ^
          mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T := pow_pos hPpos _
      have hpowReal : (0 : ℝ) <
          (mtTypeIPrimeScale X alpha ^
            mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) := by
        exact_mod_cast hpowPos
      exact Real.rpow_pos_of_pos hpowReal _
    have hnew := henergyX alpha T a A N N' V halpha halpha2 hXT hTX
      hN hNT hNN' hN'le hV
    dsimp only [P, ell, V] at hnew
    rw [hready.2.2] at hnew
    simpa only [hNT, if_true,
      mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound] using hnew
  · simpa only [hNT, if_false] using hold

end

end RHTower.Sieve
