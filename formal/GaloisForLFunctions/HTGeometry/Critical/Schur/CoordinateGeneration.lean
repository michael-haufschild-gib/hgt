import GaloisForLFunctions.HTGeometry.FiniteJetSubalgebraInversion
import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceCoordinates
import GaloisForLFunctions.HTGeometry.Critical.Schur.JacobianDivisor
import GaloisForLFunctions.HTGeometry.Critical.Reciprocal.Numerator

/-!
# The Schur coordinates generate the source coordinate ring

Every raw source coordinate is a polynomial in the Schur coordinates, and every reciprocal source
coordinate becomes one after multiplication by a power of the scale.  Both statements follow from
the ring-level invertibility of the finite jet transforms together with the cleared-numerator form
of the reciprocal coefficients.

Together with the reverse inclusion this exhibits the chart algebra as a localization of the
Schur coordinate ring, which is what pins the ramified prime of the Schur place.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- A positive coordinate of a normalized jet recovers the original coordinate. -/
theorem finiteJet_succ_eq_zero_mul_normalizedPositive
    {E : Type*} [Field E] {L : ℕ} (x : Fin (L + 1) → E) (hx0 : x 0 ≠ 0) (i : Fin L) :
    x i.succ = x 0 * normalizedPositiveFiniteJet x i := by
  rw [normalizedPositiveFiniteJet, normalizedFiniteJet,
    if_neg (by simp : ¬ ((i.succ : ℕ) = 0))]
  field_simp

/-- The reversed reciprocal-square family has the same range as the plain one. -/
theorem range_criticalSourceReciprocalSquareReversed :
    Set.range (criticalSourceReciprocalSquareReversed K hm hn)
      = Set.range (criticalSourceReciprocalSquarePositive K hm hn) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by simp [criticalSourceReciprocalSquareReversed]⟩

theorem range_criticalSourceReciprocalSquareReversed_subset_schur :
    Set.range (criticalSourceReciprocalSquareReversed K hm hn)
      ⊆ Set.range (criticalSourceSchurCoordinates K hm hn) := by
  rintro _ ⟨i, rfl⟩
  exact ⟨i.succ, by simp [criticalSourceSchurCoordinates]⟩

/-- **The normalized raw coordinates lie in the Schur coordinate subalgebra.** -/
theorem criticalSourceNormalizedPositive_mem_adjoin_schur (i : Fin (m + n - 1)) :
    criticalSourceNormalizedPositive K hm hn i
      ∈ Algebra.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) := by
  have hz : Algebra.adjoin K (Set.range (criticalSourceReciprocalSquarePositive K hm hn))
      = Algebra.adjoin K (Set.range (criticalSourceNormalizedPositive K hm hn)) :=
    adjoinSubalgebra_finiteReciprocalSquarePositive_eq
      (criticalSourceNormalizedPositive K hm hn)
  have hmem : criticalSourceNormalizedPositive K hm hn i
      ∈ Algebra.adjoin K (Set.range (criticalSourceReciprocalSquarePositive K hm hn)) := by
    rw [hz]
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  refine Algebra.adjoin_mono ?_ hmem
  rw [← range_criticalSourceReciprocalSquareReversed K hm hn]
  exact range_criticalSourceReciprocalSquareReversed_subset_schur K hm hn

/-- **Every raw source coordinate lies in the Schur coordinate subalgebra.** -/
theorem criticalSourceRaw_mem_adjoin_schur (j : Fin (m + n)) :
    criticalSourceRaw K m n j
      ∈ Algebra.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) := by
  have hcast : criticalSourceRaw K m n j
      = criticalSourceRawReindexed K hm hn (Fin.cast (by omega) j) := by
    rw [criticalSourceRawReindexed]
    congr 1
  rw [hcast]
  set i : Fin (m + n - 1 + 1) := Fin.cast (by omega) j with hi
  have hscale : criticalSourceRawReindexed K hm hn 0
      ∈ Algebra.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) := by
    refine Algebra.subset_adjoin ⟨0, ?_⟩
    simp [criticalSourceSchurCoordinates, criticalSourceNormalizedRaw, normalizedFiniteJet]
  refine Fin.cases ?_ (fun l => ?_) i
  · exact hscale
  · rw [finiteJet_succ_eq_zero_mul_normalizedPositive _
      (criticalSourceRawReindexed_zero_ne K hm hn) l]
    exact Subalgebra.mul_mem _ hscale
      (criticalSourceNormalizedPositive_mem_adjoin_schur K hm hn l)

/-- The raw coordinate subalgebra sits inside the Schur coordinate subalgebra. -/
theorem adjoin_criticalSourceRaw_le_adjoin_schur :
    Algebra.adjoin K (Set.range (criticalSourceRaw K m n))
      ≤ Algebra.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  exact criticalSourceRaw_mem_adjoin_schur K hm hn j

/-- **Every reciprocal source coordinate lies in the Schur coordinate subalgebra once the scale
is inverted.** -/
theorem criticalSourceScale_pow_mul_recip_mem_adjoin_schur (k : Fin (m + n)) :
    criticalSourceScale K hm hn ^ ((k : ℕ) + 1) * criticalSourceRecip K m n k
      ∈ Algebra.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) := by
  have hk : (k : ℕ) < m + n := k.isLt
  have heq := criticalSourceRecip_eq_numerator_div K hk
  have hkk : (⟨(k : ℕ), hk⟩ : Fin (m + n)) = k := Fin.ext rfl
  rw [hkk] at heq
  have hs : criticalSourceScale K hm hn ≠ 0 := criticalSourceScale_ne_zero K hm hn
  have hval : criticalSourceScale K hm hn ^ ((k : ℕ) + 1) * criticalSourceRecip K m n k
      = MvPolynomial.aeval (criticalSourceRaw K m n)
          (criticalReciprocalNumerator K (m + n) (k : ℕ)) := by
    have hs' : criticalSourceRaw K m n (⟨0, by omega⟩ : Fin (m + n)) ≠ 0 := hs
    rw [heq, criticalSourceScale, mul_div_assoc']
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hs')
  rw [hval]
  refine adjoin_criticalSourceRaw_le_adjoin_schur K hm hn ?_
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨_, rfl⟩

end

end GaloisForLFunctions.HTGeometry
