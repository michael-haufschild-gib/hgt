import GaloisForLFunctions.HTGeometry.FractionRingDifference

/-!
# Difference-constant independence over a domain

A fixed family that is linearly independent over the constant field remains independent over a
difference domain when the fraction field has no new constants.  The proof eliminates coefficients
one at a time: subtracting a transformed relation gives constant coefficient ratios in the fraction
field, then torsion-freeness cancels one nonzero coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C R A ι : Type*} [Field C] [CommRing R] [IsDomain R]
  [CommRing A] [Algebra C R] [Algebra R A] [Algebra C A]
  [IsScalarTower C R A] [Module.IsTorsionFree R A]

/-- Fixed elements independent over the constant field remain independent over a difference domain
whose fraction field has exactly that fixed field. -/
theorem linearIndependent_of_fraction_fixed
    (σR : R ≃+* R) (σA : A ≃+* A)
    (hcompat : ∀ r : R, σA (algebraMap R A r) = algebraMap R A (σR r))
    (b : ι → A) (hb : ∀ i, σA (b i) = b i)
    (hfrac : ∀ x : FractionRing R, fractionRingEquiv σR x = x →
      ∃ c : C, x = algebraMap C (FractionRing R) c)
    (hCindep : LinearIndependent C b) : LinearIndependent R b := by
  classical
  rw [linearIndependent_iff']
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
      intro g hsum i hi
      rw [Finset.sum_insert hj] at hsum
      by_cases hgj : g j = 0
      · have hsumT : ∑ k ∈ t, g k • b k = 0 := by simpa [hgj] using hsum
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hgj
        · exact ih g hsumT i hi
      have hsigma : ∑ k ∈ insert j t, σR (g k) • b k = 0 := by
        have h := congrArg σA (show ∑ k ∈ insert j t, g k • b k = 0 by
          simpa [Finset.sum_insert hj] using hsum)
        simpa only [map_sum, map_zero, Algebra.smul_def, map_mul, hcompat, hb] using h
      let d : ι → R := fun k => g j * σR (g k) - σR (g j) * g k
      have hsumFull : ∑ k ∈ insert j t, g k • b k = 0 := by
        rw [Finset.sum_insert hj]
        exact hsum
      have hcross : ∑ k ∈ insert j t, d k • b k = 0 := by
        calc
          ∑ k ∈ insert j t, d k • b k =
              ∑ k ∈ insert j t,
                (g j • (σR (g k) • b k) - σR (g j) • (g k • b k)) := by
            apply Finset.sum_congr rfl
            intro k _
            simp only [d, sub_smul, mul_smul]
          _ = (∑ k ∈ insert j t, g j • (σR (g k) • b k)) -
              ∑ k ∈ insert j t, σR (g j) • (g k • b k) := by
            rw [Finset.sum_sub_distrib]
          _ = g j • (∑ k ∈ insert j t, σR (g k) • b k) -
              σR (g j) • (∑ k ∈ insert j t, g k • b k) := by
            rw [Finset.smul_sum, Finset.smul_sum]
          _ = 0 := by rw [hsigma, hsumFull]; simp
      have hdj : d j = 0 := by simp only [d]; ring
      have hcrossT : ∑ k ∈ t, d k • b k = 0 := by
        rw [Finset.sum_insert hj] at hcross
        simpa [hdj] using hcross
      have hdT : ∀ k ∈ t, d k = 0 := ih d hcrossT
      have hd : ∀ k ∈ insert j t, d k = 0 := by
        intro k hk
        rw [Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact hdj
        · exact hdT k hk
      have hgjF : algebraMap R (FractionRing R) (g j) ≠ 0 :=
        (IsFractionRing.to_map_eq_zero_iff (R := R) (K := FractionRing R)).not.mpr hgj
      have hratioFixed : ∀ k ∈ insert j t,
          fractionRingEquiv σR
              (algebraMap R (FractionRing R) (g k) /
                algebraMap R (FractionRing R) (g j)) =
            algebraMap R (FractionRing R) (g k) /
              algebraMap R (FractionRing R) (g j) := by
        intro k hk
        rw [map_div₀ (fractionRingEquiv σR)
          (algebraMap R (FractionRing R) (g k))
          (algebraMap R (FractionRing R) (g j)),
          fractionRingEquiv_algebraMap, fractionRingEquiv_algebraMap]
        have hσgj : σR (g j) ≠ 0 := fun h => hgj (σR.injective (by simpa using h))
        have hσgjF : algebraMap R (FractionRing R) (σR (g j)) ≠ 0 :=
          (IsFractionRing.to_map_eq_zero_iff (R := R) (K := FractionRing R)).not.mpr hσgj
        rw [div_eq_div_iff hσgjF hgjF]
        have hdeq : g j * σR (g k) = σR (g j) * g k :=
          sub_eq_zero.mp (hd k hk)
        simpa only [map_mul, mul_comm] using
          congrArg (algebraMap R (FractionRing R)) hdeq
      let c : ι → C := fun k =>
        if hk : k ∈ insert j t then
          Classical.choose (hfrac _ (hratioFixed k hk)) else 0
      have hc : ∀ k ∈ insert j t,
          algebraMap R (FractionRing R) (g k) /
              algebraMap R (FractionRing R) (g j) =
            algebraMap C (FractionRing R) (c k) := by
        intro k hk
        simp only [c, dif_pos hk]
        exact Classical.choose_spec (hfrac _ (hratioFixed k hk))
      have hg : ∀ k ∈ insert j t,
          g k = algebraMap C R (c k) * g j := by
        intro k hk
        apply IsFractionRing.injective R (FractionRing R)
        rw [map_mul, ← IsScalarTower.algebraMap_apply C R (FractionRing R)]
        exact (div_eq_iff hgjF).mp (hc k hk)
      have hfactor : algebraMap R A (g j) *
          (∑ k ∈ insert j t, algebraMap C A (c k) * b k) = 0 := by
        calc
          algebraMap R A (g j) *
              (∑ k ∈ insert j t, algebraMap C A (c k) * b k) =
              ∑ k ∈ insert j t,
                algebraMap R A (algebraMap C R (c k) * g j) * b k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [map_mul, ← IsScalarTower.algebraMap_apply C R A]
            ring
          _ = ∑ k ∈ insert j t, algebraMap R A (g k) * b k := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hg k hk]
          _ = 0 := by simpa only [Algebra.smul_def] using
            (show ∑ k ∈ insert j t, g k • b k = 0 by
              simpa [Finset.sum_insert hj] using hsum)
      have hCsum : ∑ k ∈ insert j t, c k • b k = 0 := by
        have hsmul : g j • (∑ k ∈ insert j t, c k • b k) = 0 := by
          simpa only [Algebra.smul_def] using hfactor
        exact (smul_eq_zero.mp hsmul).resolve_left hgj
      have hcj0 : c j = 0 :=
        (linearIndependent_iff'.mp hCindep) (insert j t) c hCsum j
          (Finset.mem_insert_self j t)
      have hcontra := hc j (Finset.mem_insert_self j t)
      rw [div_self hgjF, hcj0, map_zero] at hcontra
      exact False.elim (one_ne_zero hcontra)

end

end GaloisForLFunctions.HTGeometry
