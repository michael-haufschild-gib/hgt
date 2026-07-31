import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetLoopCurrent
import GaloisForLFunctions.HTGeometry.FreeCoordinateChainRule

/-!
# Annihilation by the loop currents forces constancy

A jet observable involves only finitely many jets, so it has a highest jet order.  Expanding a
depth-`l` loop current by the chain rule leaves three kinds of term: those of a row the current does
not touch, which vanish; those of jet order below `l`, whose falling factorial vanishes; and those
of order above `l`, which vanish once the descent has already reached them.  Only the order-`l`
partial derivative survives, multiplied by `l!` and by a nonzero jet coordinate.

Running this from the highest jet order downwards annihilates every partial derivative of the row,
and one current family per row therefore forces the observable to be constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The loop current of an elementary matrix on a jet coordinate -/

theorem jetLoopDerivation_single_freeCoordinate (k : ℕ) (a b c : n) (m : ℕ) :
    jetLoopDerivation k (Matrix.single a b (1 : K)) (freeCoordinate K (n × ℕ) (c, m)) =
      (if a = c then
        algebraMap K (HomogeneousJetField n K) ((m.descFactorial k : ℕ) : K) *
          freeCoordinate K (n × ℕ) (b, m - k) else 0) := by
  rw [jetLoopDerivation_freeCoordinate]
  by_cases hac : a = c
  · rw [if_pos hac, Finset.sum_eq_single b]
    · rw [Matrix.single_apply, if_pos ⟨hac, rfl⟩, mul_one]
    · intro q _ hq
      rw [Matrix.single_apply, if_neg fun hcon => hq hcon.2.symm, mul_zero, map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ b) hcon
  · rw [if_neg hac]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.single_apply, if_neg fun hcon => hac hcon.1, mul_zero, map_zero, zero_mul]

omit [Fintype n] [DecidableEq n] in
theorem freeCoordinate_ne_zero' (p : n × ℕ) : freeCoordinate K (n × ℕ) p ≠ 0 := by
  rw [freeCoordinate]
  intro hcon
  exact MvPolynomial.X_ne_zero _ ((map_eq_zero_iff _ (IsFractionRing.injective
    (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K))).1 hcon)

/-! ## The descent -/

/-- **The highest-jet descent.**  If a jet observable is annihilated by every depth of the loop
current of one elementary matrix, then every partial derivative along that row vanishes. -/
theorem freeCoordinateDerivation_eq_zero_of_forall_jetLoopDerivation [CharZero K]
    {f : HomogeneousJetField n K} {a b : n}
    (h : ∀ l : ℕ, jetLoopDerivation l (Matrix.single a b (1 : K)) f = 0) (m : ℕ) :
    freeCoordinateDerivation K (n × ℕ) (a, m) f = 0 := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_mem_freeCoordinateField f
  set L := S.sup (fun p : n × ℕ => p.2) with hLdef
  have hker : ∀ p : n × ℕ, p ∉ S → freeCoordinateDerivation K (n × ℕ) p f = 0 := by
    intro p hp
    exact freeCoordinateField_le_commonKernel (↑S : Set (n × ℕ)) hS p
      fun hc => hp (Finset.mem_coe.1 hc)
  have hhigh : ∀ (c : n) (m' : ℕ), L < m' →
      freeCoordinateDerivation K (n × ℕ) (c, m') f = 0 := by
    intro c m' hm'
    refine hker _ fun hmem => ?_
    exact absurd (Finset.le_sup (f := fun p : n × ℕ => p.2) hmem) (not_le.2 hm')
  have hstep : ∀ m' : ℕ,
      (∀ m'' : ℕ, m' < m'' → freeCoordinateDerivation K (n × ℕ) (a, m'') f = 0) →
      freeCoordinateDerivation K (n × ℕ) (a, m') f = 0 := by
    intro m' hIH
    by_cases hmem : (a, m') ∈ S
    · have hchain :=
        freeCoordinate_chainRule S (jetLoopDerivation m' (Matrix.single a b (1 : K))) hS
      rw [h m'] at hchain
      rw [Finset.sum_eq_single (a, m')] at hchain
      · rw [jetLoopDerivation_single_freeCoordinate, if_pos rfl, Nat.sub_self,
          Nat.descFactorial_self] at hchain
        have hfac : algebraMap K (HomogeneousJetField n K)
            ((Nat.factorial m' : ℕ) : K) ≠ 0 := by
          refine fun hcon => ?_
          have hz : ((Nat.factorial m' : ℕ) : K) = 0 :=
            (map_eq_zero_iff _ (algebraMap K (HomogeneousJetField n K)).injective).1 hcon
          exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m') hz
        rcases mul_eq_zero.1 hchain.symm with h1 | h2
        · rcases mul_eq_zero.1 h1 with h3 | h4
          · exact absurd h3 hfac
          · exact absurd h4 (freeCoordinate_ne_zero' _)
        · exact h2
      · rintro ⟨c, m''⟩ _ hp
        rw [jetLoopDerivation_single_freeCoordinate]
        rcases eq_or_ne a c with rfl | hac
        · rw [if_pos rfl]
          rcases lt_trichotomy m'' m' with hlt | heq | hgt
          · rw [Nat.descFactorial_eq_zero_iff_lt.2 hlt, Nat.cast_zero, map_zero, zero_mul,
              zero_mul]
          · exact absurd (by rw [heq]) hp
          · rw [hIH m'' hgt, mul_zero]
        · rw [if_neg hac, zero_mul]
      · intro hcon
        exact absurd hmem hcon
    · exact hker _ hmem
  have hdesc : ∀ k m' : ℕ, L - m' ≤ k → freeCoordinateDerivation K (n × ℕ) (a, m') f = 0 := by
    intro k
    induction k with
    | zero =>
        intro m' hm'
        exact hstep m' fun m'' hm'' => hhigh a m'' (by omega)
    | succ k ih =>
        intro m' hm'
        refine hstep m' fun m'' hm'' => ?_
        rcases le_or_gt m'' L with hle | hgt
        · exact ih m'' (by omega)
        · exact hhigh a m'' hgt
  exact hdesc (L - m) m le_rfl

/-- **The general free-jet fixed field.**  A jet observable annihilated by one loop-current family
per row is constant. -/
theorem exists_algebraMap_of_forall_jetLoopDerivation [CharZero K]
    {f : HomogeneousJetField n K} (b : n → n)
    (h : ∀ (a : n) (l : ℕ), jetLoopDerivation l (Matrix.single a (b a) (1 : K)) f = 0) :
    ∃ c : K, f = algebraMap K (HomogeneousJetField n K) c := by
  refine exists_algebraMap_of_forall_freeCoordinateDerivation_eq_zero ?_
  rintro ⟨a, m⟩
  exact freeCoordinateDerivation_eq_zero_of_forall_jetLoopDerivation (h a) m

end

end GaloisForLFunctions.HTGeometry
