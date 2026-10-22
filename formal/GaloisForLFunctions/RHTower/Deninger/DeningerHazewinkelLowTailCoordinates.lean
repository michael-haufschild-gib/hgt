import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelNextCofactor
import Mathlib.Algebra.MvPolynomial.Supported

namespace RHTower
noncomputable section

abbrev DeningerHazewinkelLowRing (k : ℕ) := MvPolynomial (Fin (2 * k + 1)) ℤ

def deningerHazewinkelLowEmbedding (k : ℕ) : Fin (2 * k + 1) → ℕ := fun i => i.val

def deningerHazewinkelLowTailIndexEquiv (k : ℕ) :
    ℕ ⊕ Fin (2 * k + 1) ≃ ℕ :=
  Equiv.sumComm ℕ (Fin (2 * k + 1)) |>.trans (finSumNatEquiv (2 * k + 1))

def deningerHazewinkelLowTailEquiv (k : ℕ) :
    MvPolynomial ℕ ℤ ≃+*
      MvPolynomial ℕ (DeningerHazewinkelLowRing k) :=
  (MvPolynomial.renameEquiv ℤ
    (deningerHazewinkelLowTailIndexEquiv k).symm).toRingEquiv.trans
    (MvPolynomial.sumRingEquiv ℤ ℕ (Fin (2 * k + 1)))

@[simp] theorem deningerHazewinkelLowTailEquiv_X_low (k : ℕ)
    (i : Fin (2 * k + 1)) :
    deningerHazewinkelLowTailEquiv k
      (MvPolynomial.X (deningerHazewinkelLowEmbedding k i)) =
      MvPolynomial.C (MvPolynomial.X i) := by
  simp only [deningerHazewinkelLowTailEquiv, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, deningerHazewinkelLowEmbedding,
    deningerHazewinkelLowTailIndexEquiv]
  change (MvPolynomial.sumRingEquiv ℤ ℕ (Fin (2 * k + 1)))
      (MvPolynomial.X (((finSumNatEquiv (2 * k + 1)).symm i.val).swap)) = _
  rw [finSumNatEquiv_symm_apply_fin]
  exact MvPolynomial.sumRingEquiv_X_inr ℤ ℕ (Fin (2 * k + 1)) i

@[simp] theorem deningerHazewinkelLowTailEquiv_X_tail (k t : ℕ) :
    deningerHazewinkelLowTailEquiv k
      (MvPolynomial.X (2 * k + 1 + t)) = MvPolynomial.X t := by
  simp [deningerHazewinkelLowTailEquiv, deningerHazewinkelLowTailIndexEquiv]

theorem deningerHazewinkelLeading_succ_vars_lt_low
    (k : ℕ) {v : ℕ}
    (hv : v ∈ (deningerHazewinkelLeadingDeterminant (k + 1)).vars) :
    v < 2 * k + 1 := by
  cases k with
  | zero =>
      simp [deningerHazewinkelLeadingDeterminant,
        deningerHazewinkelUniversalCoeff] at hv
  | succ k =>
      rw [deningerHazewinkelLeadingDeterminant_succ_eq_special] at hv
      have hle := deningerHazewinkelSpecialMinor_vars_le_pivot
        (n := k + 1) (s := k + 1) (by omega) le_rfl hv
      omega

theorem deningerHazewinkelLeading_succ_vars_subset_range (k : ℕ) :
    ↑(deningerHazewinkelLeadingDeterminant (k + 1)).vars ⊆
      Set.range (deningerHazewinkelLowEmbedding k) := by
  intro v hv
  exact ⟨⟨v, deningerHazewinkelLeading_succ_vars_lt_low k hv⟩, rfl⟩

def deningerHazewinkelLowLeading (k : ℕ) : DeningerHazewinkelLowRing k :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range
    (deningerHazewinkelLeadingDeterminant (k + 1))
    (deningerHazewinkelLowEmbedding k)
    (fun _ _ h => Fin.ext h)
    (deningerHazewinkelLeading_succ_vars_subset_range k)).choose

theorem deningerHazewinkelLowLeading_rename (k : ℕ) :
    MvPolynomial.rename (deningerHazewinkelLowEmbedding k)
      (deningerHazewinkelLowLeading k) =
      deningerHazewinkelLeadingDeterminant (k + 1) :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range
    (deningerHazewinkelLeadingDeterminant (k + 1))
    (deningerHazewinkelLowEmbedding k)
    (fun _ _ h => Fin.ext h)
    (deningerHazewinkelLeading_succ_vars_subset_range k)).choose_spec

theorem deningerHazewinkelLowTailEquiv_rename_low (k : ℕ)
    (p : DeningerHazewinkelLowRing k) :
    deningerHazewinkelLowTailEquiv k
      (MvPolynomial.rename (deningerHazewinkelLowEmbedding k) p) =
      MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [deningerHazewinkelLowTailEquiv]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul (MvPolynomial.rename (deningerHazewinkelLowEmbedding k)),
        MvPolynomial.rename_X,
        map_mul (deningerHazewinkelLowTailEquiv k), hp,
        deningerHazewinkelLowTailEquiv_X_low, map_mul]

theorem deningerHazewinkelLowTailEquiv_leading (k : ℕ) :
    deningerHazewinkelLowTailEquiv k
      (deningerHazewinkelLeadingDeterminant (k + 1)) =
      MvPolynomial.C (deningerHazewinkelLowLeading k) := by
  rw [← deningerHazewinkelLowLeading_rename k,
    deningerHazewinkelLowTailEquiv_rename_low]

/-- Primeness of a constant multivariate polynomial reflects to its coefficient. -/
theorem mvPolynomial_prime_of_C_prime
    {R σ : Type*} [CommRing R] {p : R}
    (hp : Prime (MvPolynomial.C p : MvPolynomial σ R)) : Prime p := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hp.ne_zero
    simp [hzero]
  · intro hunit
    exact hp.not_unit (hunit.map (MvPolynomial.C : R →+* MvPolynomial σ R))
  · intro a b hab
    have hCab : (MvPolynomial.C p : MvPolynomial σ R) ∣
        MvPolynomial.C a * MvPolynomial.C b := by
      simpa only [map_mul] using
        map_dvd (MvPolynomial.C : R →+* MvPolynomial σ R) hab
    rcases hp.dvd_or_dvd hCab with ha | hb
    · left
      simpa using
        map_dvd (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) ha
    · right
      simpa using
        map_dvd (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) hb

/-- Every nondegenerate leading determinant remains prime in its finite low-coordinate ring.

The `r + 1` reindexing makes the statement premise-free: it covers determinant sizes `r + 2`. -/
theorem deningerHazewinkelLowLeading_succ_prime (r : ℕ) :
    Prime (deningerHazewinkelLowLeading (r + 1)) := by
  have hbig : Prime (deningerHazewinkelLeadingDeterminant (r + 2)) :=
    deningerHazewinkelLeadingDeterminant_prime_of_two_le (r + 2) (by omega)
  have himage : Prime
      (deningerHazewinkelLowTailEquiv (r + 1)
        (deningerHazewinkelLeadingDeterminant (r + 2))) :=
    (MulEquiv.prime_iff (deningerHazewinkelLowTailEquiv (r + 1)).toMulEquiv).2 hbig
  rw [show r + 2 = (r + 1) + 1 by omega,
    deningerHazewinkelLowTailEquiv_leading] at himage
  exact mvPolynomial_prime_of_C_prime himage

/-- Prime ideal cutting out the leading Hankel divisor in finite low coordinates. -/
def deningerHazewinkelLowLeadingIdeal (r : ℕ) :
    Ideal (DeningerHazewinkelLowRing (r + 1)) :=
  Ideal.span {deningerHazewinkelLowLeading (r + 1)}

instance deningerHazewinkelLowLeadingIdeal_isPrime (r : ℕ) :
    (deningerHazewinkelLowLeadingIdeal r).IsPrime := by
  rw [deningerHazewinkelLowLeadingIdeal,
    Ideal.span_singleton_prime (deningerHazewinkelLowLeading_succ_prime r).ne_zero]
  exact deningerHazewinkelLowLeading_succ_prime r

/-- Coordinate ring of the integral leading-divisor hypersurface. -/
abbrev DeningerHazewinkelLowQuotient (r : ℕ) :=
  DeningerHazewinkelLowRing (r + 1) ⧸ deningerHazewinkelLowLeadingIdeal r

instance deningerHazewinkelLowQuotient_isDomain (r : ℕ) :
    IsDomain (DeningerHazewinkelLowQuotient r) :=
  (Ideal.Quotient.isDomain_iff_prime
    (deningerHazewinkelLowLeadingIdeal r)).mpr inferInstance

/-- Fraction field of the generic point of the leading divisor. -/
abbrev DeningerHazewinkelBoundaryField (r : ℕ) :=
  FractionRing (DeningerHazewinkelLowQuotient r)

/-- Integral low coordinates specialized to the generic point of `D_(r+2)=0`. -/
def deningerHazewinkelLowToBoundary (r : ℕ) :
    DeningerHazewinkelLowRing (r + 1) →+*
      DeningerHazewinkelBoundaryField r :=
  (algebraMap (DeningerHazewinkelLowQuotient r)
      (DeningerHazewinkelBoundaryField r)).comp
    (Ideal.Quotient.mk (deningerHazewinkelLowLeadingIdeal r))

/-- Boundary specialization: split low/tail coordinates, kill the prime leading divisor, then
pass its integral coordinate ring to its fraction field. -/
def deningerHazewinkelBoundarySpecialization (r : ℕ) :
    MvPolynomial ℕ ℤ →+*
      MvPolynomial ℕ (DeningerHazewinkelBoundaryField r) :=
  (MvPolynomial.map (deningerHazewinkelLowToBoundary r)).comp
    (deningerHazewinkelLowTailEquiv (r + 1)).toRingHom

theorem deningerHazewinkelLowToBoundary_lowLeading (r : ℕ) :
    deningerHazewinkelLowToBoundary r
      (deningerHazewinkelLowLeading (r + 1)) = 0 := by
  change algebraMap (DeningerHazewinkelLowQuotient r)
    (DeningerHazewinkelBoundaryField r)
      ((Ideal.Quotient.mk (deningerHazewinkelLowLeadingIdeal r))
        (deningerHazewinkelLowLeading (r + 1))) = 0
  rw [map_eq_zero_iff _
    (IsFractionRing.injective (DeningerHazewinkelLowQuotient r)
      (DeningerHazewinkelBoundaryField r))]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton_self _

theorem deningerHazewinkelBoundarySpecialization_leading (r : ℕ) :
    deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelLeadingDeterminant (r + 2)) = 0 := by
  change MvPolynomial.map (deningerHazewinkelLowToBoundary r)
    (deningerHazewinkelLowTailEquiv (r + 1)
      (deningerHazewinkelLeadingDeterminant (r + 2))) = 0
  rw [show r + 2 = (r + 1) + 1 by omega,
    deningerHazewinkelLowTailEquiv_leading, MvPolynomial.map_C,
    deningerHazewinkelLowToBoundary_lowLeading, map_zero]

theorem deningerHazewinkelNextCofactor_succ_vars_subset_range (r : ℕ) :
    ↑(deningerHazewinkelNextCofactor (r + 1)).vars ⊆
      Set.range (deningerHazewinkelLowEmbedding (r + 1)) := by
  intro v hv
  rw [deningerHazewinkelNextCofactor_eq_special] at hv
  have hle := deningerHazewinkelSpecialMinor_vars_le_pivot
    (n := r + 1) (s := r + 2) (by omega) (by omega) hv
  exact ⟨⟨v, by omega⟩, rfl⟩

/-- Finite low-coordinate representative of the second cofactor `E_(r+2)`. -/
def deningerHazewinkelLowNextCofactor (r : ℕ) :
    DeningerHazewinkelLowRing (r + 1) :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range
    (deningerHazewinkelNextCofactor (r + 1))
    (deningerHazewinkelLowEmbedding (r + 1))
    (fun _ _ h => Fin.ext h)
    (deningerHazewinkelNextCofactor_succ_vars_subset_range r)).choose

theorem deningerHazewinkelLowNextCofactor_rename (r : ℕ) :
    MvPolynomial.rename (deningerHazewinkelLowEmbedding (r + 1))
      (deningerHazewinkelLowNextCofactor r) =
      deningerHazewinkelNextCofactor (r + 1) :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range
    (deningerHazewinkelNextCofactor (r + 1))
    (deningerHazewinkelLowEmbedding (r + 1))
    (fun _ _ h => Fin.ext h)
    (deningerHazewinkelNextCofactor_succ_vars_subset_range r)).choose_spec

theorem deningerHazewinkelLowTailEquiv_nextCofactor (r : ℕ) :
    deningerHazewinkelLowTailEquiv (r + 1)
      (deningerHazewinkelNextCofactor (r + 1)) =
      MvPolynomial.C (deningerHazewinkelLowNextCofactor r) := by
  rw [← deningerHazewinkelLowNextCofactor_rename,
    deningerHazewinkelLowTailEquiv_rename_low]

theorem deningerHazewinkelLowLeading_not_dvd_lowNextCofactor (r : ℕ) :
    ¬ deningerHazewinkelLowLeading (r + 1) ∣
      deningerHazewinkelLowNextCofactor r := by
  intro hdvd
  have hmap := map_dvd
    (MvPolynomial.rename (deningerHazewinkelLowEmbedding (r + 1))) hdvd
  rw [deningerHazewinkelLowLeading_rename,
    deningerHazewinkelLowNextCofactor_rename] at hmap
  exact deningerHazewinkelLeading_succ_not_dvd_nextCofactor (by omega) hmap

/-- Second cofactor does not vanish at the generic point of the leading divisor. -/
theorem deningerHazewinkelLowToBoundary_nextCofactor_ne_zero (r : ℕ) :
    deningerHazewinkelLowToBoundary r
      (deningerHazewinkelLowNextCofactor r) ≠ 0 := by
  intro hzero
  have hquot : (Ideal.Quotient.mk (deningerHazewinkelLowLeadingIdeal r))
      (deningerHazewinkelLowNextCofactor r) = 0 := by
    apply IsFractionRing.injective (DeningerHazewinkelLowQuotient r)
      (DeningerHazewinkelBoundaryField r)
    simpa [deningerHazewinkelLowToBoundary] using hzero
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hquot
  rw [deningerHazewinkelLowLeadingIdeal, Ideal.mem_span_singleton] at hmem
  exact deningerHazewinkelLowLeading_not_dvd_lowNextCofactor r hmem

/-- Exact value of the adjacent cofactor at the generic leading-divisor point. -/
theorem deningerHazewinkelBoundarySpecialization_nextCofactor (r : ℕ) :
    deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelNextCofactor (r + 1)) =
      MvPolynomial.C
        (deningerHazewinkelLowToBoundary r
          (deningerHazewinkelLowNextCofactor r)) := by
  change MvPolynomial.map (deningerHazewinkelLowToBoundary r)
    (deningerHazewinkelLowTailEquiv (r + 1)
      (deningerHazewinkelNextCofactor (r + 1))) = _
  rw [deningerHazewinkelLowTailEquiv_nextCofactor,
    MvPolynomial.map_C]

theorem deningerHazewinkelBoundarySpecialization_nextCofactor_ne_zero (r : ℕ) :
    deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelNextCofactor (r + 1)) ≠ 0 := by
  rw [deningerHazewinkelBoundarySpecialization_nextCofactor]
  simpa using (MvPolynomial.C_injective ℕ
    (DeningerHazewinkelBoundaryField r)).ne
      (deningerHazewinkelLowToBoundary_nextCofactor_ne_zero r)

end
end RHTower
