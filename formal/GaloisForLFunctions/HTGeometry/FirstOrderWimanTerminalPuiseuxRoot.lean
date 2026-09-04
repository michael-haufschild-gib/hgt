import GaloisForLFunctions.HTGeometry.FirstOrderWimanTopSymbolLaurentRoot
import GaloisForLFunctions.HTGeometry.NewtonPuiseuxPrescribedEdgeRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open HahnSeries Polynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable def firstOrderCoefficientLaurentValue
    (A : Polynomial ℂ) (U : LaurentSeries ℂ) : LaurentSeries ℂ :=
  ∑ n ∈ A.support, HahnSeries.single (0 : ℤ) (A.coeff n) * U ^ n

private theorem coeff_laurent_sum_single
    (s : Finset ℕ) (f : ℕ → ℤ) (g : ℕ → ℂ) (w : ℤ) :
    (∑ n ∈ s, HahnSeries.single (f n) (g n) : LaurentSeries ℂ).coeff w =
      ∑ n ∈ s, if f n = w then g n else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, Finset.sum_insert hn, HahnSeries.coeff_add, ih]
      congr 1
      by_cases h : f n = w
      · subst h
        simp
      · simp [h, Ne.symm h]

theorem firstOrderCoefficientLaurentValue_at_single_ne_zero
    (A : Polynomial ℂ) (hA : A ≠ 0) (e : ℤ) (he : e ≠ 0) :
    firstOrderCoefficientLaurentValue A (HahnSeries.single e (1 : ℂ)) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun h : LaurentSeries ℂ => h.coeff (((A.natDegree : ℕ) : ℤ) * e)) hzero
  rw [firstOrderCoefficientLaurentValue] at hcoeff
  simp_rw [hahnSingleOne_pow_int, HahnSeries.single_mul_single, zero_add, mul_one] at hcoeff
  rw [coeff_laurent_sum_single, HahnSeries.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single_of_mem A.natDegree
    (Polynomial.natDegree_mem_support_of_nonzero hA)] at hcoeff
  · rw [if_pos rfl, Polynomial.coeff_natDegree] at hcoeff
    exact (Polynomial.leadingCoeff_ne_zero.mpr hA) hcoeff
  · intro n hn hne
    rw [if_neg]
    intro heq
    apply hne
    exact Int.ofNat_injective (mul_right_cancel₀ he heq)

noncomputable def firstOrderTopSymbolLaurentPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U : LaurentSeries ℂ) : Polynomial (LaurentSeries ℂ) :=
  ∑ i ∈ firstOrderTopNewtonFace S A d,
    Polynomial.C (firstOrderCoefficientLaurentValue (A i) U) * Polynomial.X ^ i.2

theorem eval_firstOrderTopSymbolLaurentPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U T : LaurentSeries ℂ) :
    (firstOrderTopSymbolLaurentPolynomial S A d U).eval T =
      firstOrderTopSymbolLaurentValue S A d U T := by
  classical
  rw [firstOrderTopSymbolLaurentPolynomial, firstOrderTopSymbolLaurentValue,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    firstOrderCoefficientLaurentValue, Finset.sum_mul]

theorem coeff_firstOrderTopSymbolLaurentPolynomial_of_mem
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U : LaurentSeries ℂ) (i₀ : ℕ × ℕ)
    (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d) :
    (firstOrderTopSymbolLaurentPolynomial S A d U).coeff i₀.2 =
      firstOrderCoefficientLaurentValue (A i₀) U := by
  classical
  rw [firstOrderTopSymbolLaurentPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem i₀ hi₀]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro i hi hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hsnd
    apply hne
    apply Prod.ext
    · have hiDeg := (Finset.mem_filter.mp hi).2.1
      have hi₀Deg := (Finset.mem_filter.mp hi₀).2.1
      omega
    · exact hsnd.symm

theorem firstOrderTopSymbolLaurentPolynomial_ne_zero_of_mem
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (N q : ℕ) (hN : N ≠ 0) (hq : q ≠ 0) (i₀ : ℕ × ℕ)
    (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d) :
    firstOrderTopSymbolLaurentPolynomial S A d
      (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ)) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun P : Polynomial (LaurentSeries ℂ) ↦ P.coeff i₀.2) hzero
  rw [coeff_firstOrderTopSymbolLaurentPolynomial_of_mem S A d _ i₀ hi₀,
    Polynomial.coeff_zero] at hcoeff
  apply firstOrderCoefficientLaurentValue_at_single_ne_zero (A i₀)
    (Finset.mem_filter.mp hi₀).2.2 (-((N * q : ℕ) : ℤ))
  · exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (mul_ne_zero hN hq))
  · exact hcoeff

abbrev FirstOrderTerminalCoefficientField := AlgebraicClosure (LaurentSeries ℂ)

noncomputable def firstOrderTerminalPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U : LaurentSeries ℂ) : Polynomial (PowerSeries FirstOrderTerminalCoefficientField) :=
  ∑ i ∈ S,
    Polynomial.C
        (PowerSeries.C
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
              (firstOrderCoefficientLaurentValue (A i) U)) *
          (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^
            (d - (i.1 + i.2))) *
      Polynomial.X ^ i.2

theorem specialFiber_firstOrderTerminalPowerSeriesPolynomial
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U : LaurentSeries ℂ)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d)
    (hne : ∀ i ∈ S, A i ≠ 0) :
    (firstOrderTerminalPowerSeriesPolynomial S A d U).map
        (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField)) =
      (firstOrderTopSymbolLaurentPolynomial S A d U).map
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField) := by
  classical
  rw [firstOrderTerminalPowerSeriesPolynomial,
    firstOrderTopSymbolLaurentPolynomial]
  change
    (Polynomial.mapRingHom
      (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField)))
        (∑ i ∈ S,
          Polynomial.C
              (PowerSeries.C
                  (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
                    (firstOrderCoefficientLaurentValue (A i) U)) *
                (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^
                  (d - (i.1 + i.2))) *
            Polynomial.X ^ i.2) =
      (Polynomial.mapRingHom
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField))
          (∑ i ∈ firstOrderTopNewtonFace S A d,
            Polynomial.C (firstOrderCoefficientLaurentValue (A i) U) *
              Polynomial.X ^ i.2)
  rw [map_sum (Polynomial.mapRingHom
      (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField))),
    map_sum (Polynomial.mapRingHom
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField))]
  rw [firstOrderTopNewtonFace, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases htop : i.1 + i.2 = d
  · rw [if_pos ⟨htop, hne i hi⟩]
    simp [htop]
  · rw [if_neg]
    · have hpos : 0 < d - (i.1 + i.2) := Nat.sub_pos_of_lt
        (lt_of_le_of_ne (hdegree i hi) htop)
      simp [PowerSeries.constantCoeff]
      exact Or.inr ⟨PowerSeries.constantCoeff_X, Nat.ne_of_gt hpos⟩
    · intro h
      exact htop h.1

theorem specialFiber_firstOrderTerminalPowerSeriesPolynomial_ne_zero
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d N q : ℕ)
    (hN : N ≠ 0) (hq : q ≠ 0) (i₀ : ℕ × ℕ)
    (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d)
    (hne : ∀ i ∈ S, A i ≠ 0) :
    (firstOrderTerminalPowerSeriesPolynomial S A d
      (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))).map
        (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField)) ≠ 0 := by
  rw [specialFiber_firstOrderTerminalPowerSeriesPolynomial S A d _ hdegree hne]
  intro hzero
  apply firstOrderTopSymbolLaurentPolynomial_ne_zero_of_mem
    S A d N q hN hq i₀ hi₀
  apply (Polynomial.map_injective
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField)
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField).injective)
  simpa using hzero

theorem specialFiber_firstOrderTerminalPowerSeriesPolynomial_isRoot
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U T : LaurentSeries ℂ)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d)
    (hne : ∀ i ∈ S, A i ≠ 0)
    (hroot : firstOrderTopSymbolLaurentValue S A d U T = 0) :
    ((firstOrderTerminalPowerSeriesPolynomial S A d U).map
      (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField))).IsRoot
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField T) := by
  rw [specialFiber_firstOrderTerminalPowerSeriesPolynomial S A d U hdegree hne]
  change ((firstOrderTopSymbolLaurentPolynomial S A d U).map
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField)).eval
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField T) = 0
  have hpolyroot : (firstOrderTopSymbolLaurentPolynomial S A d U).eval T = 0 := by
    rw [eval_firstOrderTopSymbolLaurentPolynomial, hroot]
  have hmapped := congrArg
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField) hpolyroot
  simpa using hmapped

theorem newtonTransform_zero_one
    {K : Type} [Field K] (F : Polynomial (PowerSeries K)) :
    newtonTransform F 0 1 one_ne_zero = F := by
  apply Polynomial.ext
  intro i
  rw [coeff_newtonTransform]
  by_cases hi : i ≤ F.natDegree
  · rw [if_pos hi, zero_mul, shiftPow_zero]
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_expand]
    simp
  · rw [if_neg hi]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hi)).symm

theorem exists_firstOrderTerminalPowerSeriesRoot
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d N q : ℕ)
    (hN : N ≠ 0) (hq : q ≠ 0) (i₀ : ℕ × ℕ)
    (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d)
    (hne : ∀ i ∈ S, A i ≠ 0)
    (T : LaurentSeries ℂ)
    (hroot : firstOrderTopSymbolLaurentValue S A d
      (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ)) T = 0) :
    ∃ (R : ℕ) (_hR : R ≠ 0) (z : PowerSeries FirstOrderTerminalCoefficientField),
      ((firstOrderTerminalPowerSeriesPolynomial S A d
        (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))).map
          (PowerSeries.expand (R := FirstOrderTerminalCoefficientField) R _hR).toRingHom).IsRoot z ∧
      PowerSeries.constantCoeff z =
        algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField T := by
  letI : CharZero (LaurentSeries ℂ) :=
    (RingHom.charZero_iff
      (algebraMap ℂ (LaurentSeries ℂ)).injective).mp inferInstance
  letI : CharZero FirstOrderTerminalCoefficientField :=
    (RingHom.charZero_iff
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField).injective).mp
        inferInstance
  let F := firstOrderTerminalPowerSeriesPolynomial S A d
    (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))
  have hfibne : (newtonTransform F 0 1 one_ne_zero).map
      (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField)) ≠ 0 := by
    rw [newtonTransform_zero_one]
    exact specialFiber_firstOrderTerminalPowerSeriesPolynomial_ne_zero
      S A d N q hN hq i₀ hi₀ hdegree hne
  have hc : ((newtonTransform F 0 1 one_ne_zero).map
      (PowerSeries.constantCoeff (R := FirstOrderTerminalCoefficientField))).IsRoot
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField T) := by
    rw [newtonTransform_zero_one]
    exact specialFiber_firstOrderTerminalPowerSeriesPolynomial_isRoot
      S A d _ T hdegree hne hroot
  have hdvd : ∀ i ≤ F.natDegree,
      (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^
          (0 * (F.natDegree - i)) ∣
        PowerSeries.expand 1 one_ne_zero (F.coeff i) := by
    intro i hi
    simp
  obtain ⟨R, hR, z, hz, hzlead⟩ :=
    exists_isRoot_map_expand_with_prescribed_newton_lead_of_specialFiber_ne
      (K := FirstOrderTerminalCoefficientField) 0 1 one_ne_zero hdvd
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField T) hfibne hc
  refine ⟨R, hR, z, ?_, hzlead⟩
  simpa only [F, Nat.mul_one, Nat.mul_zero, pow_zero, one_mul] using hz

abbrev FirstOrderTerminalLaurentField :=
  LaurentSeries FirstOrderTerminalCoefficientField

noncomputable def firstOrderFullTerminalLaurentValue
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (U : LaurentSeries ℂ)
    (V W : FirstOrderTerminalLaurentField) : FirstOrderTerminalLaurentField :=
  ∑ i ∈ S,
    HahnSeries.single (0 : ℤ)
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (firstOrderCoefficientLaurentValue (A i) U)) *
      V ^ i.1 * W ^ i.2

theorem terminal_algebraMap_expand_C_mul_X_pow
    (R e : ℕ) (hR : R ≠ 0) (c : FirstOrderTerminalCoefficientField) :
    algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
        FirstOrderTerminalLaurentField
      (PowerSeries.expand R hR
        (PowerSeries.C c *
          (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^ e)) =
      HahnSeries.single ((R * e : ℕ) : ℤ) c := by
  change HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField
      (PowerSeries.expand R hR
        (PowerSeries.C c *
          (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^ e)) = _
  rw [map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X]
  rw [map_mul (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField)]
  rw [HahnSeries.ofPowerSeries_C]
  have hXpow :
      (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField)
          ((PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^ R) =
        (HahnSeries.single (1 : ℤ) (1 : FirstOrderTerminalCoefficientField)) ^ R := by
    rw [map_pow (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField),
      HahnSeries.ofPowerSeries_X]
  have hpowE :
      (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField)
          (((PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^ R) ^ e) =
        ((HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField)
          ((PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^ R)) ^ e := by
    exact map_pow (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField) _ e
  rw [hpowE, hXpow]
  rw [← pow_mul]
  induction R * e with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, HahnSeries.single_mul_single]
      simp

theorem terminal_hahnSingleOne_pow_int
    (e : ℤ) (n : ℕ) :
    (HahnSeries.single e (1 : FirstOrderTerminalCoefficientField)) ^ n =
      HahnSeries.single ((n : ℤ) * e) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single]
      congr 1
      · push_cast
        ring_nf
      · simp

theorem firstOrderTerminal_laurent_term_identity
    (R d j k : ℕ) (hR : R ≠ 0) (c : FirstOrderTerminalCoefficientField)
    (z : PowerSeries FirstOrderTerminalCoefficientField) (hdegree : j + k ≤ d) :
    HahnSeries.single ((R * d : ℕ) : ℤ) (1 : FirstOrderTerminalCoefficientField) *
        (HahnSeries.single (0 : ℤ) c *
          HahnSeries.single (-((R : ℕ) : ℤ)) (1 : FirstOrderTerminalCoefficientField) ^ j *
          (HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) *
            algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
              FirstOrderTerminalLaurentField z) ^ k) =
      algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField
          (PowerSeries.expand R hR
            (PowerSeries.C c *
              (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^
                (d - (j + k)))) *
        (algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField z) ^ k := by
  rw [terminal_algebraMap_expand_C_mul_X_pow]
  rw [terminal_hahnSingleOne_pow_int, mul_pow, terminal_hahnSingleOne_pow_int]
  have hsingle :
      HahnSeries.single ((R * d : ℕ) : ℤ) (1 : FirstOrderTerminalCoefficientField) *
          HahnSeries.single ((j : ℤ) * -((R : ℕ) : ℤ)) c *
          HahnSeries.single ((k : ℤ) * -((R : ℕ) : ℤ)) 1 =
        HahnSeries.single ((R * (d - (j + k)) : ℕ) : ℤ) c := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    simp only [one_mul, mul_one]
    apply congrArg (fun e : ℤ => HahnSeries.single e c)
    push_cast
    rw [Nat.cast_sub hdegree]
    push_cast
    ring
  rw [HahnSeries.single_mul_single]
  calc
    _ = (HahnSeries.single ((R * d : ℕ) : ℤ)
            (1 : FirstOrderTerminalCoefficientField) *
          HahnSeries.single ((j : ℤ) * -((R : ℕ) : ℤ)) c *
          HahnSeries.single ((k : ℤ) * -((R : ℕ) : ℤ)) 1) *
          (algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
            FirstOrderTerminalLaurentField z) ^ k := by noncomm_ring
    _ = _ := by rw [hsingle]

theorem firstOrderFullTerminalLaurentValue_mul_eq_compactifiedEval
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d R : ℕ)
    (hR : R ≠ 0) (U : LaurentSeries ℂ)
    (z : PowerSeries FirstOrderTerminalCoefficientField)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d) :
    HahnSeries.single ((R * d : ℕ) : ℤ) (1 : FirstOrderTerminalCoefficientField) *
        firstOrderFullTerminalLaurentValue S A U
          (HahnSeries.single (-((R : ℕ) : ℤ))
            (1 : FirstOrderTerminalCoefficientField))
          (HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) *
            algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
              FirstOrderTerminalLaurentField z) =
      algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField
        (((firstOrderTerminalPowerSeriesPolynomial S A d U).map
          (PowerSeries.expand (R := FirstOrderTerminalCoefficientField) R hR).toRingHom).eval z) := by
  classical
  rw [firstOrderFullTerminalLaurentValue, Finset.mul_sum]
  rw [firstOrderTerminalPowerSeriesPolynomial]
  change (∑ i ∈ S,
      HahnSeries.single ((R * d : ℕ) : ℤ) (1 : FirstOrderTerminalCoefficientField) *
        (HahnSeries.single (0 : ℤ)
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
              (firstOrderCoefficientLaurentValue (A i) U)) *
          HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) ^ i.1 *
          (HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) *
            algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
              FirstOrderTerminalLaurentField z) ^ i.2)) =
    algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField
      ((Polynomial.evalRingHom z)
        ((Polynomial.mapRingHom
          (PowerSeries.expand (R := FirstOrderTerminalCoefficientField) R hR).toRingHom)
          (∑ i ∈ S,
            Polynomial.C
                (PowerSeries.C
                    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
                      (firstOrderCoefficientLaurentValue (A i) U)) *
                  (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^
                    (d - (i.1 + i.2))) *
              Polynomial.X ^ i.2)))
  rw [map_sum (Polynomial.mapRingHom
      (PowerSeries.expand (R := FirstOrderTerminalCoefficientField) R hR).toRingHom),
    map_sum (Polynomial.evalRingHom z),
    map_sum (algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField)]
  apply Finset.sum_congr rfl
  intro i hi
  change
    HahnSeries.single ((R * d : ℕ) : ℤ) (1 : FirstOrderTerminalCoefficientField) *
        (HahnSeries.single (0 : ℤ)
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
              (firstOrderCoefficientLaurentValue (A i) U)) *
          HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) ^ i.1 *
          (HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) *
            algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
              FirstOrderTerminalLaurentField z) ^ i.2) =
      algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
        FirstOrderTerminalLaurentField
        (((Polynomial.C
            (PowerSeries.C
                (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
                  (firstOrderCoefficientLaurentValue (A i) U)) *
              (PowerSeries.X : PowerSeries FirstOrderTerminalCoefficientField) ^
                (d - (i.1 + i.2))) *
            Polynomial.X ^ i.2).map
              (PowerSeries.expand (R := FirstOrderTerminalCoefficientField) R hR).toRingHom).eval z)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow]
  exact firstOrderTerminal_laurent_term_identity R d i.1 i.2 hR
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
      (firstOrderCoefficientLaurentValue (A i) U)) z (hdegree i hi)

theorem firstOrderFullTerminalLaurentValue_eq_zero_of_compactifiedRoot
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d R : ℕ)
    (hR : R ≠ 0) (U : LaurentSeries ℂ)
    (z : PowerSeries FirstOrderTerminalCoefficientField)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d)
    (hroot : ((firstOrderTerminalPowerSeriesPolynomial S A d U).map
      (PowerSeries.expand (R := FirstOrderTerminalCoefficientField) R hR).toRingHom).IsRoot z) :
    firstOrderFullTerminalLaurentValue S A U
        (HahnSeries.single (-((R : ℕ) : ℤ))
          (1 : FirstOrderTerminalCoefficientField))
        (HahnSeries.single (-((R : ℕ) : ℤ))
            (1 : FirstOrderTerminalCoefficientField) *
          algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
            FirstOrderTerminalLaurentField z) = 0 := by
  have hproduct := firstOrderFullTerminalLaurentValue_mul_eq_compactifiedEval
    S A d R hR U z hdegree
  rw [hroot, map_zero] at hproduct
  exact (mul_eq_zero.mp hproduct).resolve_left (by simp)

noncomputable def firstOrderTerminalComplexMap :
    ℂ →+* FirstOrderTerminalLaurentField :=
  (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField).comp
    ((algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField).comp
      (algebraMap ℂ (LaurentSeries ℂ)))

noncomputable def firstOrderTerminalJet
    (U : LaurentSeries ℂ) (V W : FirstOrderTerminalLaurentField) :
    Fin 3 → FirstOrderTerminalLaurentField :=
  ![algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U), V, W]

theorem eval₂_firstOrderMvPoly
    {M : Type*} [CommRing M] (f : ℂ →+* M)
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (z u v : M) :
    MvPolynomial.eval₂ f (fun j : Fin 3 => ![z, u, v] j) (firstOrderMvPoly S A) =
      ∑ p ∈ S, (A p).eval₂ f z * u ^ p.1 * v ^ p.2 := by
  classical
  rw [firstOrderMvPoly]
  change (MvPolynomial.eval₂Hom f (fun j : Fin 3 => ![z, u, v] j))
      (∑ p ∈ S, Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (A p) *
        (MvPolynomial.X 1) ^ p.1 * (MvPolynomial.X 2) ^ p.2) = _
  rw [map_sum (MvPolynomial.eval₂Hom f (fun j : Fin 3 => ![z, u, v] j))]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [map_mul, map_mul, map_pow, map_pow]
  rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  change MvPolynomial.eval₂ f (fun j : Fin 3 => ![z, u, v] j)
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (A p)) *
        u ^ p.1 * v ^ p.2 = _
  congr 1
  congr 1
  rw [← MvPolynomial.coe_eval₂Hom f (fun j : Fin 3 => ![z, u, v] j)]
  induction (A p) using Polynomial.induction_on' with
  | add q r ihq ihr =>
      rw [Polynomial.eval₂_add, map_add, ihq, ihr, Polynomial.eval₂_add]
  | monomial k c =>
      rw [Polynomial.eval₂_monomial, map_mul, map_pow,
        MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
        Polynomial.eval₂_monomial]
      rfl

theorem eval₂_firstOrderCoefficient_terminal
    (A : Polynomial ℂ) (U : LaurentSeries ℂ) :
    A.eval₂ firstOrderTerminalComplexMap
        (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U)) =
      HahnSeries.single (0 : ℤ)
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (firstOrderCoefficientLaurentValue A U)) := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    firstOrderCoefficientLaurentValue]
  change (∑ n ∈ A.support,
      firstOrderTerminalComplexMap (A.coeff n) *
        (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U)) ^ n) =
    HahnSeries.C
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
        (∑ n ∈ A.support,
          HahnSeries.single (0 : ℤ) (A.coeff n) * U ^ n))
  have hconstant : ∀ x : FirstOrderTerminalCoefficientField,
      HahnSeries.C x =
        algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField x := by
    intro x
    change HahnSeries.C x =
      HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField (PowerSeries.C x)
    rw [HahnSeries.ofPowerSeries_C]
  rw [hconstant]
  change (∑ n ∈ A.support,
      firstOrderTerminalComplexMap (A.coeff n) *
        (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U)) ^ n) =
    algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
        (∑ n ∈ A.support, HahnSeries.single (0 : ℤ) (A.coeff n) * U ^ n))
  rw [map_sum (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField),
    map_sum (algebraMap FirstOrderTerminalCoefficientField
      FirstOrderTerminalLaurentField)]
  have hcomplex : ∀ c : ℂ,
      algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.single (0 : ℤ) c := by
    intro c
    change HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C c) =
      HahnSeries.single (0 : ℤ) c
    rw [HahnSeries.ofPowerSeries_C]
    exact HahnSeries.C_apply c
  apply Finset.sum_congr rfl
  intro n hn
  simp only [firstOrderTerminalComplexMap, RingHom.comp_apply, map_mul, map_pow]
  rw [hcomplex]

theorem eval₂_firstOrderMvPoly_terminal
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (U : LaurentSeries ℂ) (V W : FirstOrderTerminalLaurentField) :
    MvPolynomial.eval₂ firstOrderTerminalComplexMap
        (firstOrderTerminalJet U V W) (firstOrderMvPoly S A) =
      firstOrderFullTerminalLaurentValue S A U V W := by
  change MvPolynomial.eval₂ firstOrderTerminalComplexMap
      (fun j : Fin 3 => ![
        algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U), V, W] j)
      (firstOrderMvPoly S A) = _
  rw [eval₂_firstOrderMvPoly, firstOrderFullTerminalLaurentValue]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval₂_firstOrderCoefficient_terminal]

theorem eval₂_entireFirstOrderWiman_polynomial_terminal
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f)
    (U : LaurentSeries ℂ) (V W : FirstOrderTerminalLaurentField) :
    MvPolynomial.eval₂ firstOrderTerminalComplexMap
        (firstOrderTerminalJet U V W) data.P =
      firstOrderFullTerminalLaurentValue data.indexSupport data.coeff U V W := by
  rw [← data.coefficient_reconstruction]
  exact eval₂_firstOrderMvPoly_terminal data.indexSupport data.coeff U V W

/-- **Full prescribed branch of the irreducible first-order relation.**  Both exact
Newton--Puiseux stages assemble into a zero of the original three-coordinate polynomial.  The
first cover, signed Wiman slope, first prescribed coefficient, terminal cover, and terminal
constant root are all retained. -/
theorem exists_entireFirstOrderWiman_fullRelationPuiseuxRoot
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    ∃ (M a q N : ℕ) (_hN : N ≠ 0) (z₀ : PowerSeries ℂ)
        (R : ℕ) (_hR : R ≠ 0)
        (z : PowerSeries FirstOrderTerminalCoefficientField),
      q ≠ 0 ∧ data.slope = ((M : ℚ) - (a : ℚ)) / q ∧
      PowerSeries.constantCoeff z₀ = data.root ∧
      PowerSeries.constantCoeff z =
        algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
            algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
              ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀)) ∧
      MvPolynomial.eval₂ firstOrderTerminalComplexMap
        (firstOrderTerminalJet
          (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))
          (HahnSeries.single (-((R : ℕ) : ℤ))
            (1 : FirstOrderTerminalCoefficientField))
          (HahnSeries.single (-((R : ℕ) : ℤ))
              (1 : FirstOrderTerminalCoefficientField) *
            algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
              FirstOrderTerminalLaurentField z)) data.P = 0 := by
  obtain ⟨M, a, q, N, hN, z₀, hq, hp, hz₀,
      htop⟩ := exists_entireFirstOrderWiman_topSymbolLaurentRoot data
  let U := HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ)
  let T := HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
      ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀)
  obtain ⟨R, hR, z, hroot, hz⟩ := exists_firstOrderTerminalPowerSeriesRoot
    data.indexSupport data.coeff data.totalDegree N q hN hq data.firstIndex
      (Finset.mem_filter.mp data.first_mem_face).1
      data.support_degree_le data.coefficient_ne_zero T htop
  refine ⟨M, a, q, N, hN, z₀, R, hR, z, hq, hp, hz₀, hz, ?_⟩
  rw [eval₂_entireFirstOrderWiman_polynomial_terminal]
  exact firstOrderFullTerminalLaurentValue_eq_zero_of_compactifiedRoot
    data.indexSupport data.coeff data.totalDegree R hR U z
      data.support_degree_le hroot

end

end GaloisForLFunctions.HTGeometry
