import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelBoundaryTriangularity
import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelBoundaryMinorNonvanishing

namespace RHTower
noncomputable section

open MvPolynomial

/-- Coefficientwise contraction for a principal quotient of a polynomial coefficient ring. -/
theorem mvPolynomial_C_dvd_of_map_quotient_eq_zero
    {R σ : Type*} [CommRing R] (d : R) (p : MvPolynomial σ R)
    (hzero : MvPolynomial.map
      (Ideal.Quotient.mk (Ideal.span {d})) p = 0) :
    (MvPolynomial.C d : MvPolynomial σ R) ∣ p := by
  have hcoeff : ∀ m : σ →₀ ℕ,
      d ∣ MvPolynomial.coeff m p := by
    intro m
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← MvPolynomial.coeff_map]
    rw [hzero]
    simp
  choose b hb using hcoeff
  refine ⟨∑ m ∈ p.support, MvPolynomial.monomial m (b m), ?_⟩
  calc
    p = ∑ m ∈ p.support, MvPolynomial.monomial m
        (MvPolynomial.coeff m p) := p.as_sum
    _ = ∑ m ∈ p.support,
        MvPolynomial.C d * MvPolynomial.monomial m (b m) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [MvPolynomial.C_mul_monomial, hb]
    _ = MvPolynomial.C d *
        (∑ m ∈ p.support, MvPolynomial.monomial m (b m)) := by
          rw [Finset.mul_sum]

/-- The generic leading-divisor specialization has exactly the principal kernel `(D_(r+2))`. -/
theorem deningerHazewinkelBoundarySpecialization_eq_zero_iff_dvd
    (r : ℕ) (p : MvPolynomial ℕ ℤ) :
    deningerHazewinkelBoundarySpecialization r p = 0 ↔
      deningerHazewinkelLeadingDeterminant (r + 2) ∣ p := by
  constructor
  · intro hzero
    let q := deningerHazewinkelLowTailEquiv (r + 1) p
    have hmapBoundary : MvPolynomial.map (deningerHazewinkelLowToBoundary r) q = 0 := by
      exact hzero
    have hmapQuotient : MvPolynomial.map
        (Ideal.Quotient.mk (deningerHazewinkelLowLeadingIdeal r)) q = 0 := by
      apply MvPolynomial.map_injective
        (algebraMap (DeningerHazewinkelLowQuotient r)
          (DeningerHazewinkelBoundaryField r))
        (IsFractionRing.injective (DeningerHazewinkelLowQuotient r)
          (DeningerHazewinkelBoundaryField r))
      rw [MvPolynomial.map_map]
      simpa [q, deningerHazewinkelLowToBoundary] using hmapBoundary
    have hdvdLow := mvPolynomial_C_dvd_of_map_quotient_eq_zero
      (deningerHazewinkelLowLeading (r + 1)) q hmapQuotient
    have hdvdBack := map_dvd
      (deningerHazewinkelLowTailEquiv (r + 1)).symm.toRingHom hdvdLow
    rw [← deningerHazewinkelLowTailEquiv_leading] at hdvdBack
    change (deningerHazewinkelLowTailEquiv (r + 1)).symm
      ((deningerHazewinkelLowTailEquiv (r + 1))
        (deningerHazewinkelLeadingDeterminant ((r + 1) + 1))) ∣
      (deningerHazewinkelLowTailEquiv (r + 1)).symm q at hdvdBack
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply] at hdvdBack
    simpa [q] using hdvdBack
  · rintro ⟨q, rfl⟩
    rw [map_mul, deningerHazewinkelBoundarySpecialization_leading,
      zero_mul]

/-- Boundary special minor `m_n=D_(n+1)` remains nonzero at generic point of `D_n=0`. -/
theorem deningerHazewinkelBoundarySpecialization_boundaryMinor_ne_zero (r : ℕ) :
    deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelSpecialMinor (r + 2) (r + 2)) ≠ 0 := by
  intro hzero
  have hdvd := (deningerHazewinkelBoundarySpecialization_eq_zero_iff_dvd r _).mp hzero
  rw [← deningerHazewinkelLeadingDeterminant_succ_eq_special] at hdvd
  exact deningerHazewinkelLeading_not_dvd_leading_succ
    (r + 2) (by omega) hdvd

end
end RHTower

