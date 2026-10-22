import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPrimeOuterShell
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundForcing
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Arithmetic action of the literal prime operator on pole profiles

The actual aperture-compressed prime operator sends `exp(x/2)` to
`exp(x/2) * [psi(exp(a-x)) + sum_{n≤exp(a+x)} Lambda(n)/n]` inside `[-a,a]`.
Reflection gives the other pole profile. Its exponential Chebyshev main term is
exactly the opposite pole profile and vanishes in every constrained pairing.
Removing the remaining constant pole component gives a spatial ramp, the genuine
Chebyshev error, and a uniformly bounded reciprocal-Mangoldt error.

The final theorem gives this arithmetic integral for the literal prime moment of
every vector in the complete constrained form space. No Gamma profile-domain
claim, arithmetic error sign, or RH assertion is assumed or established here.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct BigOperators
noncomputable section
namespace RHTower

private theorem polar_translation (a : SuzukiPositiveAperture) (s h : ℝ) :
    (fun x => (ccmPolarL2Vector a s : ℝ → ℂ) (x+h)) =ᵐ[volume]
      fun x => (centralInterval a.1).indicator (ccmPolarProfile s) (x+h) :=
  (ccmPolarL2Vector_coeFn a s).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae

private theorem exp_half_log {n : ℕ} (hn : 0 < n) :
    Real.exp (Real.log n / 2) = Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_sqrt hnR.le, Real.exp_log (Real.sqrt_pos.mpr hnR)]

private theorem polar_atom_weights {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (1 / Real.sqrt n : ℝ) * Real.exp ((x + Real.log n) / 2) = Real.exp (x/2) ∧
    (1 / Real.sqrt n : ℝ) * Real.exp ((x - Real.log n) / 2) = Real.exp (x/2) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  rw [show (x + Real.log n)/2=x/2+Real.log n/2 by ring,
    show (x - Real.log n)/2=x/2+ -(Real.log n/2) by ring,
    Real.exp_add, Real.exp_add, Real.exp_neg, exp_half_log hn]
  constructor
  · field_simp
  · have hsq := Real.sq_sqrt hnR.le
    field_simp
    nlinarith

/-- Literal atom action on the positive pole profile, with its two endpoint cutoffs. -/
theorem ccmPrimeTransport_polarPlus_coeFn (a : SuzukiPositiveAperture)
    {n : ℕ} (hn : 2 ≤ n) :
    ((ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] (centralInterval a.1).indicator (fun x =>
        (if Real.log n ≤ a.1-x then (Real.exp (x/2) : ℂ) else 0) +
        (if Real.log n ≤ a.1+x then (Real.exp (x/2) / n : ℂ) else 0)) := by
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog := Real.log_nonneg hn1
  let p := ccmPolarApertureVector a (1/2)
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))
  have hval : (ccmPrimeTransportOperator a n p : SoninL2) =
      ((1/Real.sqrt n : ℝ) : ℂ) • (S p : SoninL2) := rfl
  rw [hval]
  filter_upwards [Lp.coeFn_smul ((1/Real.sqrt n : ℝ) : ℂ) (S p : SoninL2),
    ccmApertureSymmetricTranslation_coeFn a (Real.log n) p,
    polar_translation a (1/2) (Real.log n),
    polar_translation a (1/2) (-Real.log n)] with x hc ht hp hm
  rw [hc]
  change ((1/Real.sqrt n : ℝ) : ℂ) * (S p : SoninL2) x = _
  rw [ht]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    change -a.1 ≤ x ∧ x ≤ a.1 at hx
    change (ccmPolarL2Vector a (1/2) : ℝ → ℂ) (x+Real.log n) = _ at hp
    change (ccmPolarL2Vector a (1/2) : ℝ → ℂ) (x+ -Real.log n) = _ at hm
    change ((1/Real.sqrt n : ℝ) : ℂ) *
      ((ccmPolarL2Vector a (1/2)) (x+Real.log n) +
        (ccmPolarL2Vector a (1/2)) (x-Real.log n)) = _
    rw [hp, sub_eq_add_neg, hm]
    have hplus : x+Real.log n ∈ centralInterval a.1 ↔ Real.log n ≤ a.1-x := by
      change (-a.1 ≤ x+Real.log n ∧ x+Real.log n ≤ a.1) ↔ _
      constructor
      · intro h; linarith [h.2]
      · intro h; constructor <;> linarith [hx.1]
    have hminus : x+ -Real.log n ∈ centralInterval a.1 ↔ Real.log n ≤ a.1+x := by
      change (-a.1 ≤ x+ -Real.log n ∧ x+ -Real.log n ≤ a.1) ↔ _
      constructor
      · intro h; linarith [h.1]
      · intro h; constructor <;> linarith [hx.2]
    have hw := polar_atom_weights hn0 x
    have hwp : ((1/Real.sqrt n : ℝ) : ℂ) * ccmPolarProfile (1/2) (x+Real.log n) =
        (Real.exp (x/2) : ℂ) := by
      change ((1/Real.sqrt n : ℝ) : ℂ) * (Real.exp ((1/2)*(x+Real.log n)) : ℂ) = _
      rw [show (1/2:ℝ)*(x+Real.log n)=(x+Real.log n)/2 by ring]
      exact_mod_cast hw.1
    have hwm : ((1/Real.sqrt n : ℝ) : ℂ) * ccmPolarProfile (1/2) (x+ -Real.log n) =
        (Real.exp (x/2) / n : ℂ) := by
      change ((1/Real.sqrt n : ℝ) : ℂ) * (Real.exp ((1/2)*(x+ -Real.log n)) : ℂ) = _
      rw [show (1/2:ℝ)*(x+ -Real.log n)=(x-Real.log n)/2 by ring]
      exact_mod_cast hw.2
    simp only [Set.indicator, hplus, hminus, mul_add, mul_ite, mul_zero]
    rw [hwp, hwm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- The literal reciprocal von Mangoldt cumulative, including every prime power. -/
def ccmReciprocalMangoldtCumulative (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n / n

private theorem sum_log_cutoff (a : SuzukiPositiveAperture) (f : ℕ → ℂ)
    {y : ℝ} (hy : y ≤ 2*a.1) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      if Real.log n ≤ y then f n else 0) =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp y⌋₊, f n := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hn : 2 ≤ n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heq : Real.log n ≤ y ↔ n ≤ ⌊Real.exp y⌋₊ :=
      (Real.log_le_iff_le_exp hnR).trans (Nat.le_floor_iff (Real.exp_pos y).le).symm
    have hfloor := Nat.floor_mono (Real.exp_le_exp.mpr hy)
    rw [heq]
    omega
  · simp [hn]

private theorem psi_eq_sum_from_two (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨Nat.zero_le _, hn.2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n=0 ∨ n=1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- Exact Chebyshev and reciprocal-Mangoldt action of the actual finite-prime operator. -/
theorem ccmFinitePrimeOperator_polarPlus_coeFn (a : SuzukiPositiveAperture) :
    ((ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] (centralInterval a.1).indicator (fun x =>
        (Real.exp (x/2) : ℂ) * ((Chebyshev.psi (Real.exp (a.1-x)) : ℂ) +
          (ccmReciprocalMangoldtCumulative (Real.exp (a.1+x)) : ℂ))) := by
  classical
  let s := Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊
  let p := ccmPolarApertureVector a (1/2)
  let v : ℕ → SoninL2 := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) • (ccmPrimeTransportOperator a n p : SoninL2)
  have hval : (ccmFinitePrimeOperator a p : SoninL2) = ∑ n ∈ s, v n := by
    simp [ccmFinitePrimeOperator, s, v]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  have hatoms (n : ℕ) : ∀ᵐ x : ℝ, n ∈ s → v n x =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (centralInterval a.1).indicator (fun x =>
        (if Real.log n ≤ a.1-x then (Real.exp (x/2) : ℂ) else 0) +
        (if Real.log n ≤ a.1+x then (Real.exp (x/2) / n : ℂ) else 0)) x := by
    by_cases hn : n ∈ s
    · have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      filter_upwards [Lp.coeFn_smul (ArithmeticFunction.vonMangoldt n : ℂ)
        (ccmPrimeTransportOperator a n p : SoninL2),
        ccmPrimeTransport_polarPlus_coeFn a hn2] with x hs ht _
      change v n x = _ at hs ⊢
      rw [hs]
      change (ArithmeticFunction.vonMangoldt n : ℂ) *
        (ccmPrimeTransportOperator a n p : SoninL2) x = _
      rw [ht]
    · exact Eventually.of_forall fun _ h => (hn h).elim
  rw [hval]
  filter_upwards [Lp.coeFn_fun_finsetSum s v, ae_all_iff.mpr hatoms] with x hs ha
  rw [hs]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    have hx' : -a.1 ≤ x ∧ x ≤ a.1 := hx
    calc
      (∑ n ∈ s, v n x) = (Real.exp (x/2) : ℂ) *
          ((∑ n ∈ s, if Real.log n ≤ a.1-x then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) +
          (∑ n ∈ s, if Real.log n ≤ a.1+x then (ArithmeticFunction.vonMangoldt n / n : ℂ) else 0)) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        rw [ha n hn, indicator_of_mem hx]
        split_ifs <;> ring
      _ = _ := by
        rw [sum_log_cutoff a _ (by linarith [hx'.1]),
          sum_log_cutoff a _ (by linarith [hx'.2]), psi_eq_sum_from_two,
          ccmReciprocalMangoldtCumulative]
        push_cast
        rfl
  · rw [indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro n hn
    rw [ha n hn, indicator_of_notMem hx, mul_zero]

private theorem prime_transport_polar_reflection (a : SuzukiPositiveAperture) (n : ℕ) (s : ℝ) :
    (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (-s)) : SoninL2) =
      l2Reflection (ccmPrimeTransportOperator a n (ccmPolarApertureVector a s) : SoninL2) := by
  change ((1/Real.sqrt n : ℝ) : ℂ) •
      (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))
        (ccmPolarApertureVector a (-s)) : SoninL2) =
    l2Reflection (((1/Real.sqrt n : ℝ) : ℂ) •
      (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))
        (ccmPolarApertureVector a s) : SoninL2))
  rw [map_smul, ccmApertureCompression_val, ccmApertureCompression_val,
    l2Reflection_indicatorCutoff_central]
  congr 1
  change _ = indicatorCutoff _ _
    (l2Reflection (logTranslationCLM (Real.log n) (ccmPolarL2Vector a s) +
      logTranslationCLM (-Real.log n) (ccmPolarL2Vector a s)))
  rw [map_add, l2Reflection_logTranslationCLM, l2Reflection_logTranslationCLM,
    neg_neg, l2Reflection_ccmPolarL2Vector]
  congr 1
  exact add_comm _ _

/-- Reflection swaps the two exponential input profiles for the literal prime operator. -/
theorem ccmFinitePrimeOperator_polar_reflection (a : SuzukiPositiveAperture) (s : ℝ) :
    (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-s)) : SoninL2) =
      l2Reflection (ccmFinitePrimeOperator a (ccmPolarApertureVector a s) : SoninL2) := by
  have hval (t : ℝ) : (ccmFinitePrimeOperator a (ccmPolarApertureVector a t) : SoninL2) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) •
          (ccmPrimeTransportOperator a n (ccmPolarApertureVector a t) : SoninL2) := by
    simp [ccmFinitePrimeOperator]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  rw [hval, hval, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul, prime_transport_polar_reflection]

/-- The reflected pole action exchanges the two endpoint cumulative sums. -/
theorem ccmFinitePrimeOperator_polarMinus_coeFn (a : SuzukiPositiveAperture) :
    ((ccmFinitePrimeOperator a (ccmPolarApertureVector a (-1/2)) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] (centralInterval a.1).indicator (fun x =>
        (Real.exp (-x/2) : ℂ) * ((ccmReciprocalMangoldtCumulative (Real.exp (a.1-x)) : ℂ) +
          (Chebyshev.psi (Real.exp (a.1+x)) : ℂ))) := by
  have heq := ccmFinitePrimeOperator_polar_reflection a (1/2)
  rw [show -(1/2:ℝ)= -1/2 by ring] at heq
  rw [heq]
  have hneg := (ccmFinitePrimeOperator_polarPlus_coeFn a).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae
    (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)) : SoninL2), hneg] with x hr hp
  rw [hr]
  change (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)) : SoninL2) (-x) = _ at hp
  rw [hp]
  simp only [Function.comp_apply]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem ((neg_mem_centralInterval_iff a.1 x).mpr hx)]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  · rw [indicator_of_notMem hx,
      indicator_of_notMem (mt (neg_mem_centralInterval_iff a.1 x).mp hx)]

/-- The exact prime action after removal of the opposite exponential main profile. -/
def ccmPrimePolarDefect (a : SuzukiPositiveAperture) (s : ℝ) : suzukiApertureHilbert a :=
  ccmFinitePrimeOperator a (ccmPolarApertureVector a s) -
    (Real.exp a.1 : ℂ) • ccmPolarApertureVector a (-s)

/-- The positive pole defect is a literal Chebyshev error plus the reciprocal cumulative. -/
theorem ccmPrimePolarDefect_plus_coeFn (a : SuzukiPositiveAperture) :
    ((ccmPrimePolarDefect a (1/2) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => (Real.exp (x/2) : ℂ) *
        (((Chebyshev.psi (Real.exp (a.1-x)) - Real.exp (a.1-x) : ℝ) : ℂ) +
          (ccmReciprocalMangoldtCumulative (Real.exp (a.1+x)) : ℂ))) := by
  let v := (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)) : SoninL2)
  let p := ccmPolarL2Vector a (-(1/2))
  change (fun x => (v - (Real.exp a.1 : ℂ) • p) x) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub v ((Real.exp a.1 : ℂ) • p),
    Lp.coeFn_smul (Real.exp a.1 : ℂ) p,
    ccmFinitePrimeOperator_polarPlus_coeFn a,
    ccmPolarL2Vector_coeFn a (-(1/2))] with x hv hs hp hm
  rw [hv]
  change v x - ((Real.exp a.1 : ℂ) • p) x = _
  rw [hs]
  change v x - (Real.exp a.1 : ℂ) * p x = _
  rw [hp, hm]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, ccmPolarProfile]
    have he : Real.exp a.1 * Real.exp (-(1/2)*x) =
        Real.exp (x/2) * Real.exp (a.1-x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have heC : (Real.exp a.1 : ℂ) * (Real.exp (-(1/2)*x) : ℂ) =
        (Real.exp (x/2) : ℂ) * (Real.exp (a.1-x) : ℂ) := by exact_mod_cast he
    rw [heC]
    push_cast
    ring
  · simp only [indicator_of_notMem hx, mul_zero, sub_zero]

/-- Removing the exponential main term commutes with reflection. -/
theorem ccmPrimePolarDefect_reflection (a : SuzukiPositiveAperture) (s : ℝ) :
    (ccmPrimePolarDefect a (-s) : SoninL2) = l2Reflection (ccmPrimePolarDefect a s : SoninL2) := by
  change (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-s)) : SoninL2) -
      (Real.exp a.1 : ℂ) • ccmPolarL2Vector a (- -s) =
    l2Reflection ((ccmFinitePrimeOperator a (ccmPolarApertureVector a s) : SoninL2) -
      (Real.exp a.1 : ℂ) • ccmPolarL2Vector a (-s))
  rw [map_sub, map_smul, l2Reflection_ccmPolarL2Vector, ccmFinitePrimeOperator_polar_reflection]

/-- The negative pole defect uses the arithmetic error at the reflected endpoint. -/
theorem ccmPrimePolarDefect_minus_coeFn (a : SuzukiPositiveAperture) :
    ((ccmPrimePolarDefect a (-1/2) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => (Real.exp (-x/2) : ℂ) *
        ((ccmReciprocalMangoldtCumulative (Real.exp (a.1-x)) : ℂ) +
          ((Chebyshev.psi (Real.exp (a.1+x)) - Real.exp (a.1+x) : ℝ) : ℂ))) := by
  have heq := ccmPrimePolarDefect_reflection a (1/2)
  rw [show -(1/2:ℝ)= -1/2 by ring] at heq
  rw [heq]
  have hneg := (ccmPrimePolarDefect_plus_coeFn a).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (ccmPrimePolarDefect a (1/2) : SoninL2), hneg] with x hr hp
  rw [hr]
  change (ccmPrimePolarDefect a (1/2) : SoninL2) (-x) = _ at hp
  rw [hp]
  simp only [Function.comp_apply]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem ((neg_mem_centralInterval_iff a.1 x).mpr hx)]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  · rw [indicator_of_notMem hx,
      indicator_of_notMem (mt (neg_mem_centralInterval_iff a.1 x).mp hx)]

/-- Both literal pole moments of prime transport depend only on the defect vectors
when tested on the complete constrained form space. -/
theorem inner_polar_prime_on_constrained (a : SuzukiPositiveAperture)
    (u : ccmPolarConstraintSubmodule a) :
    inner ℂ (ccmPolarApertureVector a (1/2))
        (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u.1)) =
      inner ℂ (ccmPrimePolarDefect a (1/2)) (ccmArchimedeanFormToAperture a u.1) ∧
    inner ℂ (ccmPolarApertureVector a (-1/2))
        (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u.1)) =
      inner ℂ (ccmPrimePolarDefect a (-1/2)) (ccmArchimedeanFormToAperture a u.1) := by
  have hu : IsPolarConstrained a u.1 := u.2
  have hsa := (ccmFinitePrimeOperator_isSelfAdjoint a).isSymmetric
  constructor
  · rw [ccmPrimePolarDefect, inner_sub_left]
    rw [inner_smul_left (ccmPolarApertureVector a (-(1/2)))
      (ccmArchimedeanFormToAperture a u.1) (Real.exp a.1 : ℂ)]
    have hminus : inner ℂ (ccmPolarApertureVector a (-(1/2)))
        (ccmArchimedeanFormToAperture a u.1) = 0 := by
      simpa only [show -(1/2:ℝ)= -1/2 by ring] using hu.2
    rw [hminus, mul_zero, sub_zero]
    exact (hsa _ _).symm
  · rw [ccmPrimePolarDefect, inner_sub_left]
    rw [inner_smul_left (ccmPolarApertureVector a (-(-1/2)))
      (ccmArchimedeanFormToAperture a u.1) (Real.exp a.1 : ℂ)]
    have hplus : inner ℂ (ccmPolarApertureVector a (-(-1/2)))
        (ccmArchimedeanFormToAperture a u.1) = 0 := by
      simpa only [show -(-1/2:ℝ)= 1/2 by ring] using hu.1
    rw [hplus, mul_zero, sub_zero]
    exact (hsa _ _).symm

/-- The reciprocal prime-power cumulative with its exact logarithmic main term removed. -/
def ccmReciprocalMangoldtError (t : ℝ) : ℝ :=
  ccmReciprocalMangoldtCumulative (Real.exp t) - t

/-- Elementary Mertens bounds the reciprocal channel uniformly on the whole nonnegative ray. -/
theorem abs_ccmReciprocalMangoldtError_le {t : ℝ} (ht : 0 ≤ t) :
    |ccmReciprocalMangoldtError t| ≤ Real.log 4 + 5 := by
  let N := ⌊Real.exp t⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos t).le).mpr (by exact_mod_cast Real.one_le_exp ht)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsum : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) =
      ccmReciprocalMangoldtCumulative (Real.exp t) := by
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      exact ⟨by omega, hn.2⟩
    · intro n hn hnot
      simp only [Finset.mem_Icc] at hn hnot
      have hn1 : n=1 := by omega
      simp [hn1]
  have hM := Mertens.mertens_first N hN
  rw [hsum] at hM
  have hfloor : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hfloor' : Real.exp t < (N : ℝ)+1 := Nat.lt_floor_add_one _
  have hdelta0 : 0 ≤ t - Real.log N := by
    have hle := Real.log_le_log hNpos hfloor
    rw [Real.log_exp] at hle
    linarith
  have hdelta1 : t - Real.log N ≤ 1 := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos t) hNpos)
    rw [Real.log_div (ne_of_gt (Real.exp_pos t)) (ne_of_gt hNpos), Real.log_exp] at hlog
    have hratio : Real.exp t / N ≤ 2 := by
      apply (div_le_iff₀ hNpos).mpr
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    linarith
  rw [ccmReciprocalMangoldtError, abs_le]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hM
  constructor <;> linarith

/-- After removing both pole-span main terms, the positive source is exactly a spatial
ramp plus the Chebyshev error and a uniformly bounded reciprocal error. -/
theorem ccmPrimePolarDefect_plus_centered_coeFn (a : SuzukiPositiveAperture) :
    (((ccmPrimePolarDefect a (1/2) - (a.1 : ℂ) • ccmPolarApertureVector a (1/2)) :
      suzukiApertureHilbert a) : SoninL2) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => (Real.exp (x/2) : ℂ) *
        (((Chebyshev.psi (Real.exp (a.1-x)) - Real.exp (a.1-x) : ℝ) : ℂ) +
          (ccmReciprocalMangoldtError (a.1+x) : ℂ) + (x : ℂ))) := by
  let d := (ccmPrimePolarDefect a (1/2) : SoninL2)
  let p := ccmPolarL2Vector a (1/2)
  change (fun x => (d - (a.1 : ℂ) • p) x) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub d ((a.1 : ℂ) • p), Lp.coeFn_smul (a.1 : ℂ) p,
    ccmPrimePolarDefect_plus_coeFn a, ccmPolarL2Vector_coeFn a (1/2)] with x hd hs he hp
  rw [hd]
  change d x - ((a.1 : ℂ) • p) x = _
  rw [hs]
  change d x - (a.1 : ℂ) * p x = _
  rw [he, hp]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, ccmPolarProfile, ccmReciprocalMangoldtError]
    rw [show (1/2:ℝ)*x=x/2 by ring]
    push_cast
    ring
  · simp only [indicator_of_notMem hx, mul_zero, sub_zero]

/-- The centered arithmetic source has the same positive pole pairing on every constrained vector. -/
theorem inner_polar_prime_centered_on_constrained (a : SuzukiPositiveAperture)
    (u : ccmPolarConstraintSubmodule a) :
    inner ℂ (ccmPolarApertureVector a (1/2))
        (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u.1)) =
      inner ℂ (ccmPrimePolarDefect a (1/2) - (a.1 : ℂ) • ccmPolarApertureVector a (1/2))
        (ccmArchimedeanFormToAperture a u.1) := by
  rw [(inner_polar_prime_on_constrained a u).1, inner_sub_left]
  rw [inner_smul_left (ccmPolarApertureVector a (1/2))
    (ccmArchimedeanFormToAperture a u.1) (a.1 : ℂ)]
  have hu : IsPolarConstrained a u.1 := u.2
  rw [hu.1, mul_zero, sub_zero]

/-- Arithmetic integral for the actual positive pole moment of prime transport,
with both excluded main profiles removed exactly. -/
theorem inner_polar_prime_constrained_eq_arithmetic_integral (a : SuzukiPositiveAperture)
    (u : ccmPolarConstraintSubmodule a) :
    inner ℂ (ccmPolarApertureVector a (1/2))
        (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u.1)) =
      ∫ x : ℝ, (centralInterval a.1).indicator (fun x => (Real.exp (x/2) : ℂ) *
        (((Chebyshev.psi (Real.exp (a.1-x)) - Real.exp (a.1-x) : ℝ) : ℂ) +
          (ccmReciprocalMangoldtError (a.1+x) : ℂ) + (x : ℂ))) x *
        (ccmArchimedeanFormToAperture a u.1 : SoninL2) x := by
  rw [inner_polar_prime_centered_on_constrained]
  change inner ℂ
    ((ccmPrimePolarDefect a (1/2) - (a.1 : ℂ) • ccmPolarApertureVector a (1/2)) : SoninL2)
    (ccmArchimedeanFormToAperture a u.1 : SoninL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmPrimePolarDefect_plus_centered_coeFn a] with x hx
  simp only [RCLike.inner_apply, starRingEnd_apply]
  change ((ccmPrimePolarDefect a (1/2) : SoninL2) -
    (a.1 : ℂ) • (ccmPolarApertureVector a (1/2) : SoninL2)) x = _ at hx
  rw [hx]
  by_cases hmem : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hmem, map_mul, map_add, Complex.star_def,
      Complex.conj_ofReal]
    ring
  · simp only [indicator_of_notMem hmem, star_zero, mul_zero, zero_mul]
end RHTower
