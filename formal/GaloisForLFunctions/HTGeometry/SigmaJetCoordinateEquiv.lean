import GaloisForLFunctions.HTGeometry.SigmaJetCoordinateRing

/-!
# The difference action on the differential coordinate ring is invertible

For an invertible system matrix the difference action of `SigmaJetCoordinateRing` is a ring
automorphism, with the inverse given by the same construction for `σ⁻¹` and the entrywise
`σ⁻¹`-image of the inverse matrix.  On jet variables the verification reduces, because both actions
commute with the derivation, to the zeroth jet, where it is the matrix identity `A A' = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K : Type*} [CommRing K] [Differential K] {n : ℕ}

theorem commutesDeriv_symm {σ : K ≃+* K}
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a)) (a : K) :
    σ.symm (Differential.deriv a) = Differential.deriv (σ.symm a) := by
  apply σ.injective
  rw [σ.apply_symm_apply, hσ, σ.apply_symm_apply]

/-- Iterating the total derivation on a zeroth jet variable produces the higher jets. -/
theorem iterate_jetCoordDeriv_X (p : Fin n × Fin n) (k : ℕ) :
    (⇑(jetCoordDeriv K n))^[k] (MvPolynomial.X (p, 0)) = MvPolynomial.X (p, k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, differentialPolynomialOverDerivation_X]

/-- The inverse action returns the zeroth jets. -/
theorem sigmaJetCoordHom_systemRow (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hAA' : A * A' = 1) (p : Fin n × Fin n) :
    sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K)) (systemRow A p)
      = MvPolynomial.X (p, 0) := by
  classical
  have hrow : sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K)) (systemRow A p)
      = ∑ l : Fin n, ∑ m : Fin n,
        MvPolynomial.C (σ.symm (A p.1 l) * σ.symm (A' l m)) * MvPolynomial.X ((m, p.2), 0) := by
    rw [systemRow, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, sigmaJetCoordHom_C, sigmaJetCoordHom_X]
    show MvPolynomial.C (σ.symm (A p.1 l)) *
        (⇑(jetCoordDeriv K n))^[0] (systemRow (A'.map (σ.symm : K →+* K)) (l, p.2)) = _
    rw [Function.iterate_zero_apply, systemRow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_assoc, ← map_mul]
    rfl
  rw [hrow, Finset.sum_comm]
  have hinner : ∀ m : Fin n,
      (∑ l : Fin n, MvPolynomial.C (σ.symm (A p.1 l) * σ.symm (A' l m))
        * MvPolynomial.X ((m, p.2), 0))
      = MvPolynomial.C (σ.symm ((1 : Matrix (Fin n) (Fin n) K) p.1 m))
        * MvPolynomial.X ((m, p.2), 0) := by
    intro m
    rw [← Finset.sum_mul]
    congr 1
    rw [← map_sum]
    congr 1
    rw [← hAA', Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun l _ => (map_mul σ.symm _ _).symm
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => hinner m)]
  rw [Finset.sum_eq_single p.1]
  · rw [Matrix.one_apply_eq, map_one, map_one, one_mul]
  · intro m _ hm
    rw [Matrix.one_apply_ne (Ne.symm hm), map_zero, map_zero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ p.1) hcon

/-- **The difference action is an automorphism of the differential coordinate ring.** -/
theorem sigmaJetCoordHom_comp_eq_id (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) :
    (sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K))).comp (sigmaJetCoordHom σ A)
      = RingHom.id (DifferentialPolynomial (Fin n × Fin n) K) := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro a
    show sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K))
      (sigmaJetCoordHom σ A (MvPolynomial.C a)) = MvPolynomial.C a
    rw [sigmaJetCoordHom_C, sigmaJetCoordHom_C, σ.symm_apply_apply]
  · rintro ⟨p, k⟩
    show sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K))
      (sigmaJetCoordHom σ A (MvPolynomial.X (p, k))) = MvPolynomial.X (p, k)
    rw [sigmaJetCoordHom_X]
    have hcomm : ∀ (j : ℕ) (f : DifferentialPolynomial (Fin n × Fin n) K),
        sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K))
            ((⇑(jetCoordDeriv K n))^[j] f)
          = (⇑(jetCoordDeriv K n))^[j]
            (sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K)) f) := by
      intro j
      induction j with
      | zero => intro f; rfl
      | succ j ih =>
          intro f
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            sigmaJetCoordHom_commutes σ.symm (commutesDeriv_symm hσ), ih]
    rw [hcomm k, sigmaJetCoordHom_systemRow σ A A' hAA', iterate_jetCoordDeriv_X]

end

end GaloisForLFunctions.HTGeometry
