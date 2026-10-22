import GaloisForLFunctions.HTGeometry.KaehlerAnnihilatorDeterminant
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartPresentationEquiv
import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianDet
import GaloisForLFunctions.HTGeometry.Critical.Observation.CotangentBasis
import GaloisForLFunctions.HTGeometry.HorizonJacobianDeterminant
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Global Jacobian and ramification divisor of the critical source chart

The raw and reciprocal truncations are constructed inside the actual principal-open source chart.
Their truncated inverse identity gives the global Kähler Jacobian factorization.  Its determinant
is an explicit unit times the transported irreducible Schur ramification equation.  Consequently
the determinant annihilates relative differentials, and every source localization that misses it
is formally unramified over the observation chart.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial Polynomial KaehlerDifferential

set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

universe u v w

theorem formallyUnramified_localization_of_mem_annihilator_of_isUnit
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (S : Submonoid B) [IsLocalization S C]
    (d : B) (hd : d ∈ Module.annihilator B Ω[B⁄A])
    (hunit : IsUnit (algebraMap B C d)) :
    Algebra.FormallyUnramified A C := by
  rw [Algebra.formallyUnramified_iff]
  let f := KaehlerDifferential.map A A B C
  rw [Module.mem_annihilator] at hd
  have hall : ∀ z : Ω[C⁄A], z = 0 := by
    intro z
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f z
    change IsLocalizedModule.mk' f w s = 0
    rw [IsLocalizedModule.mk'_eq_zero]
    have hzero := congrArg f (hd w)
    rw [map_zero, LinearMap.map_smul] at hzero
    rw [← IsScalarTower.algebraMap_smul C d (f w)] at hzero
    exact hunit.smul_eq_zero.mp hzero
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

def criticalSourceChartRaw (i : Fin (m + n)) : criticalSourceChartRing K m n :=
  algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n) (X i)

def criticalSourceChartRawPolynomial : (criticalSourceChartRing K m n)[X] :=
  ∑ j : Fin (m + n), Polynomial.C (criticalSourceChartRaw K j) *
    Polynomial.X ^ (j : ℕ)

def criticalSourceChartRecipPolynomial : (criticalSourceChartRing K m n)[X] :=
  ∑ j : Fin (m + n), Polynomial.C (chartRecip K (m := m) (n := n) j.isLt) *
    Polynomial.X ^ (j : ℕ)

theorem map_criticalSourceChartRawPolynomial :
    (criticalSourceChartRawPolynomial K (m := m) (n := n)).map
      (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)) =
      criticalSourceRawPolynomial K m n := by
  rw [criticalSourceChartRawPolynomial, criticalSourceRawPolynomial, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  congr 3
  rw [criticalSourceChartRaw, algebraMap_criticalSourceChartRing_apply,
    MvPolynomial.aeval_X]

theorem map_criticalSourceChartRecipPolynomial :
    (criticalSourceChartRecipPolynomial K (m := m) (n := n)).map
      (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)) =
      criticalSourceReciprocalPolynomial K m n := by
  rw [criticalSourceChartRecipPolynomial, criticalSourceReciprocalPolynomial,
    Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  congr 3
  exact algebraMap_chartRecip K j.isLt

theorem X_pow_dvd_criticalSourceChart_mul_sub_one :
    (X : (criticalSourceChartRing K m n)[X]) ^ (m + n) ∣
      criticalSourceChartRawPolynomial K * criticalSourceChartRecipPolynomial K - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply algebraMap_criticalSourceChartRing_injective K (m := m) (n := n)
  have hfield := X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n
  rw [Polynomial.X_pow_dvd_iff] at hfield
  have := hfield k hk
  rw [← map_criticalSourceChartRawPolynomial K,
    ← map_criticalSourceChartRecipPolynomial K, ← Polynomial.map_mul,
    ← Polynomial.map_one
      (f := algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)),
    ← Polynomial.map_sub, Polynomial.coeff_map] at this
  simpa using this

theorem criticalSourceChartRawPolynomial_coeff (k : ℕ) (hk : k < m + n) :
    (criticalSourceChartRawPolynomial K (m := m) (n := n)).coeff k =
      criticalSourceChartRaw K ⟨k, hk⟩ := by
  classical
  rw [criticalSourceChartRawPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (m + n))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

theorem criticalSourceChartRecipPolynomial_coeff (k : ℕ) (hk : k < m + n) :
    (criticalSourceChartRecipPolynomial K (m := m) (n := n)).coeff k =
      chartRecip K (m := m) (n := n) hk := by
  classical
  rw [criticalSourceChartRecipPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (m + n))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

theorem D_criticalSourceChartRecipPolynomial_coeff (l : ℕ) (hl : l < m + n) :
    KaehlerDifferential.D K (criticalSourceChartRing K m n)
        ((criticalSourceChartRecipPolynomial K (m := m) (n := n)).coeff l) =
      -∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (A := ℕ) l : Finset (ℕ × ℕ)),
          (criticalSourceChartRecipPolynomial K (m := m) (n := n) *
              criticalSourceChartRecipPolynomial K (m := m) (n := n)).coeff x.1 •
            KaehlerDifferential.D K (criticalSourceChartRing K m n)
              ((criticalSourceChartRawPolynomial K (m := m) (n := n)).coeff x.2) :=
  polyD_reciprocal _ (X_pow_dvd_criticalSourceChart_mul_sub_one K) hl

def criticalSourceChartBlockCotangentBasis :
    Module.Basis (Fin m ⊕ Fin n) (criticalSourceChartRing K m n)
      Ω[criticalSourceChartRing K m n⁄K] :=
  (localizationCotangentBasis K (criticalSourceChartRing K m n)
    (Submonoid.powers (criticalSourceChartPoly K m n))).reindex finSumFinEquiv.symm

theorem criticalSourceChartBlockCotangentBasis_apply (t : Fin m ⊕ Fin n) :
    criticalSourceChartBlockCotangentBasis K (m := m) (n := n) t =
      KaehlerDifferential.D K (criticalSourceChartRing K m n)
        (criticalSourceChartRaw K (finSumFinEquiv t)) := by
  rw [criticalSourceChartBlockCotangentBasis, Module.Basis.reindex_apply]
  exact localizationCotangentBasis_apply K _ _ _

def criticalObservationChartBlockCoord (s : Fin m ⊕ Fin n) :
    criticalObservationChartRing K m n :=
  algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
    (MvPolynomial.X (Equiv.sumComm (Fin m) (Fin n) s))

theorem algebraMap_criticalObservationChartBlockCoord (s : Fin m ⊕ Fin n) :
    algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
      (criticalObservationChartBlockCoord K s) =
        chartObservationCoord K (Equiv.sumComm (Fin m) (Fin n) s) := by
  rw [criticalObservationChartBlockCoord]
  rw [show algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
      (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
        (MvPolynomial.X (Equiv.sumComm (Fin m) (Fin n) s))) =
      observationRingToChart K (m := m) (n := n)
        (MvPolynomial.X (Equiv.sumComm (Fin m) (Fin n) s)) from
    IsLocalization.Away.lift_eq _ _ _]
  rw [observationRingToChart, MvPolynomial.aeval_X]

def criticalObservationChartBlockCotangentBasis :
    Module.Basis (Fin m ⊕ Fin n) (criticalObservationChartRing K m n)
      Ω[criticalObservationChartRing K m n⁄K] :=
  (formallyEtaleCotangentBasis K (criticalObservationChartRing K m n)).reindex
    (Equiv.sumComm (Fin n) (Fin m))

theorem criticalObservationChartBlockCotangentBasis_apply (s : Fin m ⊕ Fin n) :
    criticalObservationChartBlockCotangentBasis K (m := m) (n := n) s =
      KaehlerDifferential.D K (criticalObservationChartRing K m n)
        (criticalObservationChartBlockCoord K s) := by
  rw [criticalObservationChartBlockCotangentBasis, Module.Basis.reindex_apply,
    formallyEtaleCotangentBasis_apply, criticalObservationChartBlockCoord]
  congr 3

theorem criticalSourceChart_hgen_block (a : criticalObservationChartRing K m n) :
    KaehlerDifferential.D K (criticalSourceChartRing K m n)
        (algebraMap (criticalObservationChartRing K m n)
          (criticalSourceChartRing K m n) a) ∈
      Submodule.span (criticalSourceChartRing K m n)
        (Set.range fun s : Fin m ⊕ Fin n =>
          KaehlerDifferential.D K (criticalSourceChartRing K m n)
            (algebraMap (criticalObservationChartRing K m n)
              (criticalSourceChartRing K m n)
              (criticalObservationChartBlockCoord K s))) := by
  have hsum := (criticalObservationChartBlockCotangentBasis K (m := m) (n := n)).sum_repr
    (KaehlerDifferential.D K (criticalObservationChartRing K m n) a)
  have hmap := congrArg (KaehlerDifferential.map K K
    (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)) hsum
  rw [KaehlerDifferential.map_D, map_sum] at hmap
  rw [← hmap]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [LinearMap.map_smul, criticalObservationChartBlockCotangentBasis_apply,
    KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_smul
      (criticalSourceChartRing K m n)]
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨s, rfl⟩

def criticalSourceChartJacobian : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n)
    (criticalSourceChartRing K m n) :=
  Matrix.of fun t s =>
    match s with
    | Sum.inl s' =>
        if ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s' : ℕ) then
          -((criticalSourceChartRecipPolynomial K (m := m) (n := n) *
            criticalSourceChartRecipPolynomial K (m := m) (n := n)).coeff
              (n + (s' : ℕ) - ((finSumFinEquiv t : Fin (m + n)) : ℕ)))
        else 0
    | Sum.inr s' => if t = Sum.inr s' then 1 else 0

theorem criticalSourceChartJacobian_apply_inl (t : Fin m ⊕ Fin n) (s : Fin m) :
    criticalSourceChartJacobian K (m := m) (n := n) t (Sum.inl s) =
      if ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s : ℕ) then
        -((criticalSourceChartRecipPolynomial K (m := m) (n := n) *
          criticalSourceChartRecipPolynomial K (m := m) (n := n)).coeff
            (n + (s : ℕ) - ((finSumFinEquiv t : Fin (m + n)) : ℕ)))
      else 0 := rfl

theorem criticalSourceChartJacobian_hvw_inr (s : Fin n) :
    KaehlerDifferential.D K (criticalSourceChartRing K m n)
        (algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
          (criticalObservationChartBlockCoord K (Sum.inr s))) =
      ∑ t : Fin m ⊕ Fin n, criticalSourceChartJacobian K (m := m) (n := n) t (Sum.inr s) •
        criticalSourceChartBlockCotangentBasis K t := by
  classical
  have hsum : ∑ t : Fin m ⊕ Fin n,
      criticalSourceChartJacobian K (m := m) (n := n) t (Sum.inr s) •
        criticalSourceChartBlockCotangentBasis K t =
      criticalSourceChartBlockCotangentBasis K (Sum.inr s) := by
    rw [Finset.sum_eq_single (Sum.inr s)]
    · show (if (Sum.inr s : Fin m ⊕ Fin n) = Sum.inr s then (1 : _) else 0) • _ = _
      rw [if_pos rfl, one_smul]
    · intro t _ ht
      show (if t = (Sum.inr s : Fin m ⊕ Fin n) then (1 : _) else 0) • _ = 0
      rw [if_neg ht, zero_smul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hsum, criticalSourceChartBlockCotangentBasis_apply,
    algebraMap_criticalObservationChartBlockCoord]
  rfl

theorem criticalSourceChartJacobian_hvw_inl (s : Fin m) :
    KaehlerDifferential.D K (criticalSourceChartRing K m n)
        (algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
          (criticalObservationChartBlockCoord K (Sum.inl s))) =
      ∑ t : Fin m ⊕ Fin n, criticalSourceChartJacobian K (m := m) (n := n) t (Sum.inl s) •
        criticalSourceChartBlockCotangentBasis K t := by
  classical
  set B := criticalSourceChartRing K m n with hB
  set g := criticalSourceChartRecipPolynomial K (m := m) (n := n) with hg
  set f := criticalSourceChartRawPolynomial K (m := m) (n := n) with hf
  have hns : n + (s : ℕ) < m + n := by have := s.isLt; omega
  have hL : KaehlerDifferential.D K B
      (algebraMap (criticalObservationChartRing K m n) B
        (criticalObservationChartBlockCoord K (Sum.inl s))) =
      -∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (A := ℕ) (n + (s : ℕ)) :
          Finset (ℕ × ℕ)), (g * g).coeff x.1 •
            KaehlerDifferential.D K B (f.coeff x.2) := by
    change KaehlerDifferential.D K (criticalSourceChartRing K m n)
        (algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
          (criticalObservationChartBlockCoord K (Sum.inl s))) =
      -∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (A := ℕ) (n + (s : ℕ)) :
          Finset (ℕ × ℕ)),
        (criticalSourceChartRecipPolynomial K (m := m) (n := n) *
          criticalSourceChartRecipPolynomial K (m := m) (n := n)).coeff x.1 •
          KaehlerDifferential.D K (criticalSourceChartRing K m n)
            ((criticalSourceChartRawPolynomial K (m := m) (n := n)).coeff x.2)
    rw [algebraMap_criticalObservationChartBlockCoord]
    change KaehlerDifferential.D K (criticalSourceChartRing K m n)
      (chartRecip K (m := m) (n := n) hns) = _
    rw [← criticalSourceChartRecipPolynomial_coeff K (n + (s : ℕ)) hns]
    exact D_criticalSourceChartRecipPolynomial_coeff K (n + (s : ℕ)) hns
  rw [hL]
  have hR : ∑ t : Fin m ⊕ Fin n,
      criticalSourceChartJacobian K (m := m) (n := n) t (Sum.inl s) •
        criticalSourceChartBlockCotangentBasis K t =
      ∑ k ∈ Finset.range (m + n),
        (if k ≤ n + (s : ℕ) then
          (-((g * g).coeff (n + (s : ℕ) - k))) •
            KaehlerDifferential.D K B (f.coeff k)
        else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if k ≤ n + (s : ℕ) then
        (-((g * g).coeff (n + (s : ℕ) - k))) •
          KaehlerDifferential.D K B (f.coeff k) else 0) (m + n)]
    refine (Equiv.sum_comp finSumFinEquiv (fun k : Fin (m + n) =>
      if (k : ℕ) ≤ n + (s : ℕ) then
        (-((g * g).coeff (n + (s : ℕ) - (k : ℕ)))) •
          KaehlerDifferential.D K B (f.coeff (k : ℕ)) else 0)).symm.trans ?_ |>.symm
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [criticalSourceChartJacobian_apply_inl,
      criticalSourceChartBlockCotangentBasis_apply,
      ← criticalSourceChartRawPolynomial_coeff K ((finSumFinEquiv t : Fin (m + n)) : ℕ)
        (finSumFinEquiv t).isLt]
    by_cases hle : ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s : ℕ)
    · rw [if_pos hle, if_pos hle]
    · rw [if_neg hle, if_neg hle, zero_smul]
  rw [hR]
  have hfilter : (Finset.range (m + n)).filter (fun k => k ≤ n + (s : ℕ)) =
      Finset.range (n + (s : ℕ) + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  have hneg : ∀ k : ℕ,
      (-((g * g).coeff (n + (s : ℕ) - k))) • KaehlerDifferential.D K B (f.coeff k) =
        -((g * g).coeff (n + (s : ℕ) - k) •
          KaehlerDifferential.D K B (f.coeff k)) := fun k => neg_smul _ _
  rw [Finset.sum_congr rfl fun k _ => hneg k, Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (g * g).coeff b • KaehlerDifferential.D K B (f.coeff a)) (n + (s : ℕ))

theorem criticalSourceChartJacobian_eq_horizon :
    criticalSourceChartJacobian K (m := m) (n := n) =
      horizonObservationJacobian
        (criticalSourceChartRecipPolynomial K (m := m) (n := n)) n m := by
  apply Matrix.ext
  intro t s
  cases s <;> rfl

theorem det_criticalSourceChartJacobian :
    (criticalSourceChartJacobian K (m := m) (n := n)).det =
      (criticalReciprocalJacobian
        (criticalSourceChartRecipPolynomial K (m := m) (n := n)) n m).det := by
  rw [criticalSourceChartJacobian_eq_horizon, det_horizonObservationJacobian]

theorem algebraMap_det_criticalSourceChartJacobian :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (criticalSourceChartJacobian K (m := m) (n := n)).det =
      (criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m).det := by
  rw [det_criticalSourceChartJacobian]
  let φ : criticalSourceChartRing K m n →+* criticalSourceField K m n :=
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
  calc
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (criticalReciprocalJacobian
          (criticalSourceChartRecipPolynomial K (m := m) (n := n)) n m).det =
      ((criticalReciprocalJacobian
        (criticalSourceChartRecipPolynomial K (m := m) (n := n)) n m).map
          (algebraMap (criticalSourceChartRing K m n)
            (criticalSourceField K m n))).det :=
        RingHom.map_det φ _
    _ = _ := by
      rw [criticalReciprocalJacobian_map, map_criticalSourceChartRecipPolynomial]

def criticalSourceChartRamificationElement : criticalSourceChartRing K m n :=
  (criticalSourceChartRingAlgEquiv K (m := m) (n := n)).symm
    (criticalSchurRamificationChartElement K (m := m) (n := n))

theorem algebraMap_criticalSourceChartRamificationElement :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (criticalSourceChartRamificationElement K (m := m) (n := n)) =
      MvPolynomial.aeval (criticalSourceSchurCoordinates K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) (criticalSourceSchurRamificationPolynomial K m n) := by
  have happ := (criticalSourceChartRingAlgEquiv K (m := m) (n := n)).apply_symm_apply
    (criticalSchurRamificationChartElement K (m := m) (n := n))
  have hcoe := congrArg
    (fun z : criticalSourceChartAlgebra K (m := m) (n := n) =>
      (z : criticalSourceField K m n)) happ
  change ((criticalSourceChartRingToAlgebraRingHom K (m := m) (n := n)
      (criticalSourceChartRamificationElement K (m := m) (n := n)) :
        criticalSourceChartAlgebra K (m := m) (n := n)) :
          criticalSourceField K m n) = _ at hcoe
  rw [coe_criticalSourceChartRingToAlgebraRingHom K] at hcoe
  exact hcoe

def criticalSourceChartJacobianUnitFactor : criticalSourceChartRing K m n :=
  (-1) ^ m * (chartInvX0 K (m := m) (n := n) ^ 2) ^ m

theorem isUnit_criticalSourceChartJacobianUnitFactor :
    IsUnit (criticalSourceChartJacobianUnitFactor K (m := m) (n := n)) := by
  exact (isUnit_neg_one.pow m).mul
    (((isUnit_algebraMap_chartX0 K (m := m) (n := n)).unit⁻¹.isUnit.pow 2).pow m)

theorem criticalSourceChartRamificationElement_prime :
    Prime (criticalSourceChartRamificationElement K (m := m) (n := n)) := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  simpa only [criticalSourceChartRamificationElement] using
    (criticalSchurRamificationChartElement_prime K (m := m) (n := n)).irreducible.map
      (criticalSourceChartRingAlgEquiv K (m := m) (n := n)).symm

theorem det_criticalSourceChartJacobian_eq_unit_mul_ramification :
    (criticalSourceChartJacobian K (m := m) (n := n)).det =
      criticalSourceChartJacobianUnitFactor K * criticalSourceChartRamificationElement K := by
  apply algebraMap_criticalSourceChartRing_injective K (m := m) (n := n)
  rw [algebraMap_det_criticalSourceChartJacobian,
    criticalSourceReciprocalJacobian_det_eq_schurRamification K
      (Fact.out : 0 < m) (Fact.out : 0 < n), map_mul,
    algebraMap_criticalSourceChartRamificationElement]
  simp only [criticalSourceChartJacobianUnitFactor, map_mul, map_pow, map_neg, map_one]
  change _ = ((-1 : criticalSourceField K m n) ^ m *
      (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (chartInvX0 K (m := m) (n := n)) ^ 2) ^ m) * _
  rw [algebraMap_chartInvX0_eq,
    criticalSourceRecip_zero_eq_inv K
      (by have hm : 0 < m := Fact.out; have hn : 0 < n := Fact.out; omega)]
  simp only [criticalSourceScale]
  simp only [inv_pow]

theorem det_criticalSourceChartJacobian_mem_annihilator :
    (criticalSourceChartJacobian K (m := m) (n := n)).det ∈
      Module.annihilator (criticalSourceChartRing K m n)
        Ω[criticalSourceChartRing K m n⁄criticalObservationChartRing K m n] :=
  det_mem_annihilator_kaehler
    (criticalSourceChartBlockCotangentBasis K (m := m) (n := n))
    (criticalObservationChartBlockCoord K (m := m) (n := n))
    (criticalSourceChartJacobian K (m := m) (n := n))
    (criticalSourceChart_hgen_block K)
    (fun s => by
      cases s with
      | inl s' => exact criticalSourceChartJacobian_hvw_inl K s'
      | inr s' => exact criticalSourceChartJacobian_hvw_inr K s')

theorem criticalSourceChart_localization_formallyUnramified_of_det_not_mem
    (P : Ideal (criticalSourceChartRing K m n)) [P.IsPrime]
    (hP : (criticalSourceChartJacobian K (m := m) (n := n)).det ∉ P) :
    Algebra.FormallyUnramified (criticalObservationChartRing K m n)
      (Localization.AtPrime P) := by
  apply formallyUnramified_localization_of_mem_annihilator_of_isUnit P.primeCompl
    (criticalSourceChartJacobian K (m := m) (n := n)).det
    (det_criticalSourceChartJacobian_mem_annihilator K)
  exact IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P)
    ⟨_, hP⟩

end

end GaloisForLFunctions.HTGeometry
