import GaloisForLFunctions.HTGeometry.DeformedCriticalObservation
import GaloisForLFunctions.HTGeometry.DeformedFibreUniqueness
import GaloisForLFunctions.HTGeometry.MvPowerSeriesMaximalIdeal
import GaloisForLFunctions.HTGeometry.PureCriticalFactorizationAlgebra
import GaloisForLFunctions.HTGeometry.PureFibreUnramified
import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# Exact cardinality of the universal deformed critical fibre

The universal power-series deformation has exactly one lift of each pure critical factorisation.
Reduction by constant coefficient sends every compatible deformed point to a monic factorisation of
`1 + X^(m+n)`.  Newton lifting supplies a preimage of every pure factorisation, while adic
Hausdorff uniqueness makes reduction injective.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Raw observed tail in the universal deformation. -/
noncomputable def deformedRawTail (K : Type*) [Field K] (m n : ℕ) :
    (deformBase K m n)[X] :=
  X ^ m + rawDeformation K m n

/-- Reciprocal observed tail in the universal deformation. -/
noncomputable def deformedReciprocalTail (K : Type*) [Field K] (m n : ℕ) :
    (deformBase K m n)[X] :=
  X ^ n + reciprocalDeformation K m n

theorem X_pow_dvd_rawDeformation (K : Type*) [Field K] (m n : ℕ) :
    (X : (deformBase K m n)[X]) ^ m ∣ rawDeformation K m n := by
  classical
  rw [rawDeformation]
  refine Finset.dvd_sum fun i _ => ?_
  refine ⟨Polynomial.C (MvPowerSeries.X (Sum.inl i) : deformBase K m n) * X ^ (i : ℕ), ?_⟩
  rw [pow_add]
  ring

theorem X_pow_dvd_reciprocalDeformation (K : Type*) [Field K] (m n : ℕ) :
    (X : (deformBase K m n)[X]) ^ n ∣ reciprocalDeformation K m n := by
  classical
  rw [reciprocalDeformation]
  refine Finset.dvd_sum fun j _ => ?_
  refine ⟨Polynomial.C (MvPowerSeries.X (Sum.inr (Sum.inl j)) : deformBase K m n) *
    X ^ (j : ℕ), ?_⟩
  rw [pow_add]
  ring

theorem X_pow_dvd_deformedRawTail (K : Type*) [Field K] (m n : ℕ) :
    (X : (deformBase K m n)[X]) ^ m ∣ deformedRawTail K m n :=
  dvd_add dvd_rfl (X_pow_dvd_rawDeformation K m n)

theorem X_pow_dvd_deformedReciprocalTail (K : Type*) [Field K] (m n : ℕ) :
    (X : (deformBase K m n)[X]) ^ n ∣ deformedReciprocalTail K m n :=
  dvd_add dvd_rfl (X_pow_dvd_reciprocalDeformation K m n)

private theorem polynomial_map_eq_zero_of_coeffMem_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {p : R[X]}
    (hp : CoeffMem (RingHom.ker f) p) : p.map f = 0 := by
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  exact (RingHom.mem_ker).1 (hp i)

private theorem polynomial_map_constantCoeff_eq_zero_of_coeffMem_deformIdeal
    (K : Type*) [Field K] (m n : ℕ) {p : (deformBase K m n)[X]}
    (hp : CoeffMem (deformIdeal K m n) p) :
    p.map (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = 0 := by
  apply polynomial_map_eq_zero_of_coeffMem_ker
  rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  exact hp

private theorem map_rawDeformation_constantCoeff (K : Type*) [Field K] (m n : ℕ) :
    (rawDeformation K m n).map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = 0 := by
  apply polynomial_map_eq_zero_of_coeffMem_ker
  rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  exact coeffMem_rawDeformation K m n

private theorem map_reciprocalDeformation_constantCoeff
    (K : Type*) [Field K] (m n : ℕ) :
    (reciprocalDeformation K m n).map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = 0 := by
  apply polynomial_map_eq_zero_of_coeffMem_ker
  rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  exact coeffMem_reciprocalDeformation K m n

private theorem map_deformedRawTail_constantCoeff
    (K : Type*) [Field K] (m n : ℕ) :
    (deformedRawTail K m n).map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = X ^ m := by
  rw [deformedRawTail, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    map_rawDeformation_constantCoeff, add_zero]

private theorem map_deformedReciprocalTail_constantCoeff
    (K : Type*) [Field K] (m n : ℕ) :
    (deformedReciprocalTail K m n).map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = X ^ n := by
  rw [deformedReciprocalTail, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    map_reciprocalDeformation_constantCoeff, add_zero]

private theorem map_C_then_constantCoeff
    (K : Type*) [Field K] (m n : ℕ) (p : K[X]) :
    (p.map (MvPowerSeries.C : K →+* deformBase K m n)).map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = p := by
  ext i
  simp

/-- Constant lift of a polynomial over the residue field. -/
noncomputable def deformConstantLift (K : Type*) [Field K] (m n : ℕ)
    (p : (deformBase K m n)[X]) : (deformBase K m n)[X] :=
  (p.map (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K))).map
    (MvPowerSeries.C : K →+* deformBase K m n)

/-- Part of a polynomial lying in the deformation ideal coefficientwise. -/
noncomputable def deformRemainder (K : Type*) [Field K] (m n : ℕ)
    (p : (deformBase K m n)[X]) : (deformBase K m n)[X] :=
  p - deformConstantLift K m n p

theorem coeffMem_deformRemainder (K : Type*) [Field K] (m n : ℕ)
    (p : (deformBase K m n)[X]) :
    CoeffMem (deformIdeal K m n) (deformRemainder K m n p) := by
  change CoeffMem
    (Ideal.span (Set.range (MvPowerSeries.X :
      Fin n ⊕ Fin m ⊕ Unit → deformBase K m n))) (deformRemainder K m n p)
  rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  intro i
  rw [RingHom.mem_ker]
  simp [deformRemainder, deformConstantLift, Polynomial.map_map]

theorem map_deformRemainder_constantCoeff (K : Type*) [Field K] (m n : ℕ)
    (p : (deformBase K m n)[X]) :
    (deformRemainder K m n p).map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) = 0 := by
  apply polynomial_map_eq_zero_of_coeffMem_ker
  rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  exact coeffMem_deformRemainder K m n p

theorem natDegree_deformRemainder_lt (K : Type*) [Field K] {m n r : ℕ}
    {p : (deformBase K m n)[X]} (hr : 0 < r) (hp : p.degree < (r : ℕ)) :
    (deformRemainder K m n p).natDegree < r := by
  have hmap : (p.map
      (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K))).degree < (r : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le hp
  have hlift : (deformConstantLift K m n p).degree < (r : ℕ) := by
    exact lt_of_le_of_lt Polynomial.degree_map_le hmap
  by_cases hzero : deformRemainder K m n p = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hr
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hlift))

/-- Reduction of a universal deformed fibre point to its pure monic factorisation. -/
noncomputable def deformedCriticalFibreReduction
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalFibre (deformBase K m n) m n
      (deformedRawTail K m n) (deformedReciprocalTail K m n) →
      MonicFactorization (pureCriticalCyclicPolynomial (K := K) (m + n)) m n := by
  classical
  intro p
  let ε : deformBase K m n →+* K :=
    MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)
  let A : K[X] := (p.1.1 + deformedRawTail K m n).map ε
  let B : K[X] := (p.1.2 + deformedReciprocalTail K m n).map ε
  have hlowA : (p.1.1.map ε).degree < (m : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le p.2.1
  have hlowB : (p.1.2.map ε).degree < (n : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le p.2.2.1
  have hAeq : A = X ^ m + p.1.1.map ε := by
    dsimp only [A, deformedRawTail, ε]
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      map_rawDeformation_constantCoeff, add_zero]
    ring
  have hBeq : B = X ^ n + p.1.2.map ε := by
    dsimp only [B, deformedReciprocalTail, ε]
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      map_reciprocalDeformation_constantCoeff, add_zero]
    ring
  have hAmonic : A.Monic := by rw [hAeq]; exact monic_X_pow_add hlowA
  have hBmonic : B.Monic := by rw [hBeq]; exact monic_X_pow_add hlowB
  have hAdeg : A.natDegree = m := by
    rw [hAeq]
    calc
      (X ^ m + p.1.1.map ε).natDegree = (X ^ m : K[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = m := Polynomial.natDegree_X_pow m
  have hBdeg : B.natDegree = n := by
    rw [hBeq]
    calc
      (X ^ n + p.1.2.map ε).natDegree = (X ^ n : K[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = n := Polynomial.natDegree_X_pow n
  have hdvdFull : (X : (deformBase K m n)[X]) ^ (m + n) ∣
      inversionError (p.1.1 + deformedRawTail K m n)
        (p.1.2 + deformedReciprocalTail K m n) := by
    exact (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
      (X_pow_dvd_deformedRawTail K m n)
      (X_pow_dvd_deformedReciprocalTail K m n) p.1.1 p.1.2).1 p.2.2.2
  have hdvdMapped : (X : K[X]) ^ (m + n) ∣ A * B - 1 := by
    have h := Polynomial.map_dvd ε hdvdFull
    simpa only [A, B, inversionError, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one] using h
  have hdvdDifference : (X : K[X]) ^ (m + n) ∣
      A * B - pureCriticalCyclicPolynomial (K := K) (m + n) := by
    rw [pureCriticalCyclicPolynomial]
    have heq : A * B - (1 + X ^ (m + n)) = (A * B - 1) - X ^ (m + n) := by ring
    rw [heq]
    exact dvd_sub hdvdMapped dvd_rfl
  have hprod : (A * B).IsMonicOfDegree (m + n) :=
    (show A.IsMonicOfDegree m from ⟨hAdeg, hAmonic⟩).mul
      (show B.IsMonicOfDegree n from ⟨hBdeg, hBmonic⟩)
  have htarget : (pureCriticalCyclicPolynomial (K := K) (m + n)).IsMonicOfDegree
      (m + n) :=
    ⟨pureCriticalCyclicPolynomial_natDegree (m + n),
      pureCriticalCyclicPolynomial_monic (by omega)⟩
  have hzero : A * B - pureCriticalCyclicPolynomial (K := K) (m + n) = 0 :=
    eq_zero_of_X_pow_dvd_of_natDegree_lt_of_commRing hdvdDifference
      (hprod.natDegree_sub_lt (by omega) htarget)
  exact ⟨(Polynomial.MonicDegreeEq.mk A hAmonic hAdeg,
      Polynomial.MonicDegreeEq.mk B hBmonic hBdeg), sub_eq_zero.mp hzero⟩

@[simp] theorem deformedCriticalFibreReduction_fst
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalFibre (deformBase K m n) m n
      (deformedRawTail K m n) (deformedReciprocalTail K m n)) :
    ((deformedCriticalFibreReduction K hm hn p).1.1 : K[X]) =
      (p.1.1 + deformedRawTail K m n).map
        (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) := by
  rfl

@[simp] theorem deformedCriticalFibreReduction_snd
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalFibre (deformBase K m n) m n
      (deformedRawTail K m n) (deformedReciprocalTail K m n)) :
    ((deformedCriticalFibreReduction K hm hn p).1.2 : K[X]) =
      (p.1.2 + deformedReciprocalTail K m n).map
        (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) := by
  rfl

private theorem criticalFibre_dvd_inversionError
    (K : Type*) [Field K] {m n : ℕ}
    (p : criticalFibre (deformBase K m n) m n
      (deformedRawTail K m n) (deformedReciprocalTail K m n)) :
    (X : (deformBase K m n)[X]) ^ (m + n) ∣
      inversionError (p.1.1 + deformedRawTail K m n)
        (p.1.2 + deformedReciprocalTail K m n) :=
  (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
    (X_pow_dvd_deformedRawTail K m n)
    (X_pow_dvd_deformedReciprocalTail K m n) p.1.1 p.1.2).1 p.2.2.2

/-- Reduction is injective: two universal deformed points with the same pure residue are equal. -/
theorem deformedCriticalFibreReduction_injective
    (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (deformedCriticalFibreReduction K hm hn) := by
  classical
  intro p q hpq
  let ε : deformBase K m n →+* K :=
    MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)
  let φ : K →+* deformBase K m n := MvPowerSeries.C
  let A₀ : K[X] := (p.1.1 + deformedRawTail K m n).map ε
  let B₀ : K[X] := (p.1.2 + deformedReciprocalTail K m n).map ε
  let A : (deformBase K m n)[X] := A₀.map φ
  let B : (deformBase K m n)[X] := B₀.map φ
  let P : (deformBase K m n)[X] := deformRemainder K m n p.1.1
  let Q : (deformBase K m n)[X] := deformRemainder K m n p.1.2
  let P' : (deformBase K m n)[X] := deformRemainder K m n q.1.1
  let Q' : (deformBase K m n)[X] := deformRemainder K m n q.1.2
  have hA₀q : A₀ = (q.1.1 + deformedRawTail K m n).map ε := by
    change ((deformedCriticalFibreReduction K hm hn p).1.1 : K[X]) = _
    rw [hpq]
    exact deformedCriticalFibreReduction_fst K hm hn q
  have hB₀q : B₀ = (q.1.2 + deformedReciprocalTail K m n).map ε := by
    change ((deformedCriticalFibreReduction K hm hn p).1.2 : K[X]) = _
    rw [hpq]
    exact deformedCriticalFibreReduction_snd K hm hn q
  have hresA : p.1.1.map ε = q.1.1.map ε := by
    dsimp only [A₀] at hA₀q
    rw [Polynomial.map_add, Polynomial.map_add] at hA₀q
    exact add_right_cancel hA₀q
  have hresB : p.1.2.map ε = q.1.2.map ε := by
    dsimp only [B₀] at hB₀q
    rw [Polynomial.map_add, Polynomial.map_add] at hB₀q
    exact add_right_cancel hB₀q
  have hAmonic : A.Monic := by
    dsimp only [A]
    exact ((deformedCriticalFibreReduction K hm hn p).1.1.monic).map φ
  have hAdeg : A.natDegree = m := by
    dsimp only [A]
    rw [Polynomial.natDegree_map φ]
    exact (deformedCriticalFibreReduction K hm hn p).1.1.natDegree
  have hBdeg : B.natDegree ≤ n := by
    dsimp only [B]
    rw [Polynomial.natDegree_map φ]
    exact le_of_eq (deformedCriticalFibreReduction K hm hn p).1.2.natDegree
  have hcop : IsCoprime A B := by
    dsimp only [A, B]
    exact (isCoprime_of_pureFactorisation
      (Nat.cast_ne_zero.2 (by omega : m + n ≠ 0))
      (deformedCriticalFibreReduction K hm hn p).2).map (Polynomial.mapRingHom φ)
  have hPmem : CoeffMem (deformIdeal K m n) P :=
    coeffMem_deformRemainder K m n p.1.1
  have hQmem : CoeffMem (deformIdeal K m n) Q :=
    coeffMem_deformRemainder K m n p.1.2
  have hP'mem : CoeffMem (deformIdeal K m n) P' :=
    coeffMem_deformRemainder K m n q.1.1
  have hQ'mem : CoeffMem (deformIdeal K m n) Q' :=
    coeffMem_deformRemainder K m n q.1.2
  have hPdeg : P.natDegree < m :=
    natDegree_deformRemainder_lt K hm p.2.1
  have hQdeg : Q.natDegree < n :=
    natDegree_deformRemainder_lt K hn p.2.2.1
  have hP'deg : P'.natDegree < m :=
    natDegree_deformRemainder_lt K hm q.2.1
  have hQ'deg : Q'.natDegree < n :=
    natDegree_deformRemainder_lt K hn q.2.2.1
  have hAform : A = X ^ m + deformConstantLift K m n p.1.1 := by
    dsimp only [A, A₀, ε, φ]
    rw [Polynomial.map_add, map_deformedRawTail_constantCoeff, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_X]
    dsimp only [deformConstantLift]
    ring
  have hBform : B = X ^ n + deformConstantLift K m n p.1.2 := by
    dsimp only [B, B₀, ε, φ]
    rw [Polynomial.map_add, map_deformedReciprocalTail_constantCoeff, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_X]
    dsimp only [deformConstantLift]
    ring
  have hAformq : A = X ^ m + deformConstantLift K m n q.1.1 := by
    rw [hAform]
    simpa only [deformConstantLift] using
      congrArg (fun r : K[X] => (X : (deformBase K m n)[X]) ^ m + r.map φ) hresA
  have hBformq : B = X ^ n + deformConstantLift K m n q.1.2 := by
    rw [hBform]
    simpa only [deformConstantLift] using
      congrArg (fun r : K[X] => (X : (deformBase K m n)[X]) ^ n + r.map φ) hresB
  have hfullAp : A + rawDeformation K m n + P =
      p.1.1 + deformedRawTail K m n := by
    rw [hAform]
    dsimp only [P, deformRemainder, deformedRawTail]
    ring
  have hfullBp : B + reciprocalDeformation K m n + Q =
      p.1.2 + deformedReciprocalTail K m n := by
    rw [hBform]
    dsimp only [Q, deformRemainder, deformedReciprocalTail]
    ring
  have hfullAq : A + rawDeformation K m n + P' =
      q.1.1 + deformedRawTail K m n := by
    rw [hAformq]
    dsimp only [P', deformRemainder, deformedRawTail]
    ring
  have hfullBq : B + reciprocalDeformation K m n + Q' =
      q.1.2 + deformedReciprocalTail K m n := by
    rw [hBformq]
    dsimp only [Q', deformRemainder, deformedReciprocalTail]
    ring
  have huniq : P = P' ∧ Q = Q' := by
    apply deformed_factorisation_unique (deformIdeal K m n) hm hn hAmonic hAdeg hBdeg hcop
      (coeffMem_rawDeformation K m n) (coeffMem_reciprocalDeformation K m n)
      hPmem hQmem hP'mem hQ'mem hPdeg hQdeg hP'deg hQ'deg
    · rw [hfullAp, hfullBp]
      exact criticalFibre_dvd_inversionError K p
    · rw [hfullAq, hfullBq]
      exact criticalFibre_dvd_inversionError K q
  have hpfirst : p.1.1 = q.1.1 := by
    have := huniq.1
    dsimp only [P, P', deformRemainder] at this
    have hlift : deformConstantLift K m n p.1.1 = deformConstantLift K m n q.1.1 := by
      dsimp only [deformConstantLift]
      rw [hresA]
    rw [hlift] at this
    exact sub_left_injective this
  have hpsecond : p.1.2 = q.1.2 := by
    have := huniq.2
    dsimp only [Q, Q', deformRemainder] at this
    have hlift : deformConstantLift K m n p.1.2 = deformConstantLift K m n q.1.2 := by
      dsimp only [deformConstantLift]
      rw [hresB]
    rw [hlift] at this
    exact sub_left_injective this
  apply Subtype.ext
  exact Prod.ext hpfirst hpsecond

/-- Every pure monic factorisation has a point in the universal deformed critical fibre above it. -/
theorem deformedCriticalFibreReduction_surjective
    (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective (deformedCriticalFibreReduction K hm hn) := by
  classical
  haveI : IsAdicComplete (deformIdeal K m n) (deformBase K m n) := inferInstanceAs
    (IsAdicComplete (Ideal.span (Set.range (MvPowerSeries.X :
      Fin n ⊕ Fin m ⊕ Unit → MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K)))
      (MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K))
  intro r
  let ε : deformBase K m n →+* K :=
    MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)
  let φ : K →+* deformBase K m n := MvPowerSeries.C
  let A₀ : K[X] := (r.1.1 : K[X])
  let B₀ : K[X] := (r.1.2 : K[X])
  let A : (deformBase K m n)[X] := A₀.map φ
  let B : (deformBase K m n)[X] := B₀.map φ
  have hAmonic : A.Monic := r.1.1.monic.map φ
  have hBmonic : B.Monic := r.1.2.monic.map φ
  have hAdeg : A.natDegree = m := by
    dsimp only [A]
    rw [Polynomial.natDegree_map φ]
    exact r.1.1.natDegree
  have hBdeg : B.natDegree = n := by
    dsimp only [B]
    rw [Polynomial.natDegree_map φ]
    exact r.1.2.natDegree
  have hcop : IsCoprime A B := by
    exact (isCoprime_of_pureFactorisation
      (Nat.cast_ne_zero.2 (by omega : m + n ≠ 0)) r.2).map (Polynomial.mapRingHom φ)
  have hbase : (X : (deformBase K m n)[X]) ^ (m + n) ∣ inversionError A B := by
    have heq : inversionError A B = (X : (deformBase K m n)[X]) ^ (m + n) := by
      dsimp only [A, B, A₀, B₀, inversionError]
      rw [← Polynomial.map_mul, r.2, pureCriticalCyclicPolynomial,
        Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
        add_sub_cancel_left]
    rw [heq]
  obtain ⟨P, Q, hPdeg, hQdeg, hPmem, hQmem, hdvd⟩ :=
    exists_deformed_factorisation (deformIdeal K m n) hm hn hAmonic hAdeg
      (le_of_eq hBdeg) hcop (coeffMem_rawDeformation K m n)
      (coeffMem_reciprocalDeformation K m n) hbase
  let lowA : (deformBase K m n)[X] := A - X ^ m + P
  let lowB : (deformBase K m n)[X] := B - X ^ n + Q
  have hAminus : (A - X ^ m).natDegree < m :=
    (show A.IsMonicOfDegree m from ⟨hAdeg, hAmonic⟩).natDegree_sub_lt
      (Nat.ne_of_gt hm)
      (show (X ^ m : (deformBase K m n)[X]).IsMonicOfDegree m from
        ⟨Polynomial.natDegree_X_pow m, Polynomial.monic_X_pow m⟩)
  have hBminus : (B - X ^ n).natDegree < n :=
    (show B.IsMonicOfDegree n from ⟨hBdeg, hBmonic⟩).natDegree_sub_lt
      (Nat.ne_of_gt hn)
      (show (X ^ n : (deformBase K m n)[X]).IsMonicOfDegree n from
        ⟨Polynomial.natDegree_X_pow n, Polynomial.monic_X_pow n⟩)
  have hlowAnat : lowA.natDegree < m := by
    dsimp only [lowA]
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hAminus hPdeg)
  have hlowBnat : lowB.natDegree < n := by
    dsimp only [lowB]
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hBminus hQdeg)
  have hlowAdeg : lowA.degree < (m : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hlowAnat)
  have hlowBdeg : lowB.degree < (n : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hlowBnat)
  have hfullB : lowB + deformedReciprocalTail K m n =
      B + reciprocalDeformation K m n + Q := by
    dsimp only [lowB, deformedReciprocalTail]
    ring
  have hfullA' : lowA + deformedRawTail K m n =
      A + rawDeformation K m n + P := by
    dsimp only [lowA, deformedRawTail]
    ring
  have hfibre : (X : (deformBase K m n)[X]) ^ (m + n) ∣
      criticalLowProduct (deformedRawTail K m n) (deformedReciprocalTail K m n)
        lowA lowB - 1 := by
    apply (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
      (X_pow_dvd_deformedRawTail K m n)
      (X_pow_dvd_deformedReciprocalTail K m n) lowA lowB).2
    rw [hfullA', hfullB]
    exact hdvd
  let z : criticalFibre (deformBase K m n) m n
      (deformedRawTail K m n) (deformedReciprocalTail K m n) :=
    ⟨(lowA, lowB), hlowAdeg, hlowBdeg, hfibre⟩
  refine ⟨z, ?_⟩
  have hPzero : P.map ε = 0 :=
    polynomial_map_constantCoeff_eq_zero_of_coeffMem_deformIdeal K m n hPmem
  have hQzero : Q.map ε = 0 :=
    polynomial_map_constantCoeff_eq_zero_of_coeffMem_deformIdeal K m n hQmem
  have hreduceA : (lowA + deformedRawTail K m n).map ε = A₀ := by
    rw [hfullA']
    dsimp only [A, φ]
    rw [Polynomial.map_add, Polynomial.map_add, hPzero, add_zero,
      map_rawDeformation_constantCoeff, add_zero, map_C_then_constantCoeff]
  have hreduceB : (lowB + deformedReciprocalTail K m n).map ε = B₀ := by
    rw [hfullB]
    dsimp only [B, φ]
    rw [Polynomial.map_add, Polynomial.map_add, hQzero, add_zero,
      map_reciprocalDeformation_constantCoeff, add_zero, map_C_then_constantCoeff]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hreduceA
  · apply Subtype.ext
    exact hreduceB

/-- The universal deformed critical fibre is equivalent to the pure monic factorisation fibre. -/
noncomputable def deformedCriticalFibreEquivPureFactorization
    (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalFibre (deformBase K m n) m n
        (deformedRawTail K m n) (deformedReciprocalTail K m n) ≃
      MonicFactorization (pureCriticalCyclicPolynomial (K := K) (m + n)) m n :=
  Equiv.ofBijective (deformedCriticalFibreReduction K hm hn)
    ⟨deformedCriticalFibreReduction_injective K hm hn,
      deformedCriticalFibreReduction_surjective K hm hn⟩

/-- **Exact binomial multiplicity of the universal deformed critical fibre.** -/
theorem nat_card_deformedCriticalFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalFibre (deformBase K m n) m n
      (deformedRawTail K m n) (deformedReciprocalTail K m n)) =
      criticalHorizonMultiplicity m n := by
  rw [Nat.card_congr (deformedCriticalFibreEquivPureFactorization K hm hn)]
  exact nat_card_pureCriticalMonicFactorization (by omega)

end GaloisForLFunctions.HTGeometry
