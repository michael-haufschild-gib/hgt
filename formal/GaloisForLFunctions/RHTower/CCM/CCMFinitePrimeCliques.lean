import GaloisForLFunctions.RHTower.ThetaFinitePrimeCliques
import GaloisForLFunctions.RHTower.CCM.CCMFiniteCliqueBound
import GaloisForLFunctions.RHTower.CCM.CCMPrimeFrustratedTriangle

/-!
# Whole-clique gains on arbitrarily many actual prime packets

Reversing the central packet makes every off-diagonal full Weil coupling
strictly positive. The finite minimum coupling is therefore positive, and
the whole-clique correction applies at every prescribed finite dimension.
No edge sign or arithmetic estimate is left as an endpoint premise.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmWeilRealPolar_neg_left (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a (-u) v = -ccmWeilRealPolar a u v := by
  have h := ccmWeilRealPolar_add_left a u (-u) v
  rw [add_neg_cancel, ccmWeilRealPolar_zero_left] at h
  linarith only [h]

def ccmWeilPrimeCliqueFamily {ι : Type*} {a : SuzukiPositiveAperture}
    (u : CCMArchimedeanFormDomain a) (v : ι → CCMArchimedeanFormDomain a) :
    Option ι → CCMArchimedeanFormDomain a
  | none => -u
  | some i => v i

theorem exists_cofinal_ccmFinitePrime_clique (N k : ℕ) :
    ∃ (p : Fin (k + 2) → ℕ) (r m : ℝ) (a : SuzukiPositiveAperture)
      (u : CCMComplexSmoothInteriorSource a) (v : Fin (k + 2) → CCMComplexSmoothInteriorSource a),
      0 < r ∧ 0 < m ∧
      (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
      (∀ i j, i < j → 2 * p i < p j) ∧
      Function.support u = Metric.ball 0 r ∧
      (∀ i, Function.support (v i) = Metric.ball (Real.log (p i)) r) ∧
      let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
      (∀ i j, i ≠ j → 0 < ccmWeilRealPolar a (f i) (f j)) ∧
      (∀ x : Option (Fin (k + 2)) → ℝ,
        finiteSignedSeparateLower (fun i j => ccmWeilRealPolar a (f i) (f j)) x +
          m * (((Fintype.card (Option (Fin (k + 2))) : ℝ) - 2) * (∑ i, x i ^ 2) +
            (∑ i, x i) ^ 2) ≤
          ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • f i)) := by
  classical
  obtain ⟨p, r, hr, hp, hpair, hnegative, hpositive⟩ := exists_cofinal_thetaFinitePrime_clique N (k + 2)
  let phi := thetaTranslatedBumpGround r hr 0
  let psi := fun i : Fin (k + 2) => thetaTranslatedBumpGround r hr (Real.log (p i))
  have hpc := compact_thetaTranslatedBumpGround r hr 0
  have hqc (i : Fin (k + 2)) := compact_thetaTranslatedBumpGround r hr (Real.log (p i))
  have hcompact : IsCompact (⋃ i : Fin (k + 2), tsupport (psi i)) := isCompact_iUnion hqc
  obtain ⟨A, hA, hbound⟩ := (hpc.union hcompact).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hs : tsupport phi ∪ (⋃ i, tsupport (psi i)) ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x hx)
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := fun _ hx => hs (Or.inl hx)
  have hqs (i : Fin (k + 2)) : tsupport (psi i) ⊆ Ioo (-a.1) a.1 :=
    fun _ hx => hs (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  let u := ccmThetaSourceOfCompactRealProfile a phi hpc hps
  let v := fun i => ccmThetaSourceOfCompactRealProfile a (psi i) (hqc i) (hqs i)
  have hn (i : Fin (k + 2)) : ccmWeilRealPolar a u.toCCMFormVector (v i).toCCMFormVector < 0 := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact hnegative i
  have hpv (i j : Fin (k + 2)) (hij : i < j) :
      0 < ccmWeilRealPolar a (v i).toCCMFormVector (v j).toCCMFormVector := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact hpositive i j hij
  let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
  have hpos (i j : Option (Fin (k + 2))) (hij : i ≠ j) : 0 < ccmWeilRealPolar a (f i) (f j) := by
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        change 0 < ccmWeilRealPolar a (-u.toCCMFormVector) (v j).toCCMFormVector
        rw [ccmWeilRealPolar_neg_left]
        exact neg_pos.mpr (hn j)
    | some i =>
      cases j with
      | none =>
        rw [ccmWeilRealPolar_symm]
        change 0 < ccmWeilRealPolar a (-u.toCCMFormVector) (v i).toCCMFormVector
        rw [ccmWeilRealPolar_neg_left]
        exact neg_pos.mpr (hn i)
      | some j =>
        change 0 < ccmWeilRealPolar a (v i).toCCMFormVector (v j).toCCMFormVector
        rcases lt_trichotomy i j with h | rfl | h
        · exact hpv i j h
        · exact False.elim (hij rfl)
        · rw [ccmWeilRealPolar_symm]
          exact hpv j i h
  let M := fun i j => ccmWeilRealPolar a (f i) (f j)
  let m := finiteSignedCliqueGain M
  have hoff : (Finset.univ : Finset (Option (Fin (k + 2)))).offDiag.Nonempty := by
    refine ⟨(none, some 0), ?_⟩
    simp
  have hm : 0 < m := finiteSignedCliqueGain_pos M hoff hpos
  refine ⟨p, r, m, a, u, v, hr, hm, hp, hpair, ?_, ?_, hpos, ?_⟩
  · rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr 0
  · intro i
    rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr (Real.log (p i))
  · intro x
    have h := finiteSignedClique_lower M (fun i j => ccmWeilRealPolar_symm a (f i) (f j)) x
    rw [← ccmRestrictedWeilSourceQuadratic_real_sum] at h
    exact h

end RHTower
