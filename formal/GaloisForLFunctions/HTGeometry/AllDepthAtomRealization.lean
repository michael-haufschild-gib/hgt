import GaloisForLFunctions.HTGeometry.TripticJetAtom
import GaloisForLFunctions.HTGeometry.JetAtomDifferentiallyAlgebraic
import GaloisForLFunctions.HTGeometry.TripticAtomSum
import GaloisForLFunctions.HTGeometry.TripticAtomSumDifferentiallyAlgebraic

/-!
# Realizing a prescribed finite divisor at one order by an atom sum

The descent of the all-depth pair-face theorem needs, for a prescribed finitely supported divisor
on the elliptic quotient `ℂ / (ℤ + ℤσ)` concentrated at one negative order, a differentially
algebraic function with exactly that principal part.  The corpus already owns the *line atom*
`jetAtom σ q j` — the `j`-th derivative of the theta logarithmic derivative translated to `q` —
its exact Laurent data, and the fact that all its jets are differentially algebraic.  This file
assembles a finite combination of atoms realizing an arbitrary prescribed divisor at one order.

* `atomRealization` — the realizing sum;
* **`laurentCoeff_atomRealization_line`** — it has the prescribed coefficient on each prescribed
  line;
* **`laurentCoeff_atomRealization_of_ne_order`**, **`laurentCoeff_atomRealization_of_notMem`** —
  and no other principal part;
* `atomRealization_periodic`, **`differentiallyAlgebraic_toMeromorphicNFOn_atomRealization`**.
-/

open Filter Set Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : ℂ}

/-- The atom sum realizing the prescribed coefficients `c` at order `-(j+1)` on the lines through
the points of `R`. -/
def atomRealization (σ : ℂ) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ q ∈ R, (c q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
    jetAtom σ (q - thetaHalfPeriod σ) j z

theorem atomRealization_periodic (σ : ℂ) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) :
    atomRealization σ j R c (z + 1) = atomRealization σ j R c z := by
  simp only [atomRealization]
  exact Finset.sum_congr rfl fun q _ => by rw [jetAtom_periodic]

theorem meromorphicOn_atomRealization (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ) :
    MeromorphicOn (atomRealization σ j R c) (Set.univ : Set ℂ) := by
  intro z _
  have hfun : atomRealization σ j R c
      = ∑ q ∈ R, fun w => (c q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
          jetAtom σ (q - thetaHalfPeriod σ) j w := by
    funext w
    simp only [atomRealization, Finset.sum_apply]
  rw [hfun]
  refine MeromorphicAt.sum fun q _ => ?_
  exact (analyticAt_const.meromorphicAt).mul (meromorphicAt_jetAtom hσ _ j z)

theorem laurentCoeff_atomRealization (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ)
    (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (atomRealization σ j R c) w ℓ =
      ∑ q ∈ R, (c q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
        laurentCoeff (jetAtom σ (q - thetaHalfPeriod σ) j) w ℓ := by
  classical
  have hmero : ∀ q ∈ R, MeromorphicAt (jetAtom σ (q - thetaHalfPeriod σ) j) w :=
    fun q _ => meromorphicAt_jetAtom hσ _ j w
  have hfun : atomRealization σ j R c = fun z => ∑ q ∈ R,
      (c q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
        jetAtom σ (q - thetaHalfPeriod σ) j z := rfl
  rw [hfun, laurentCoeff_sum R _ _ w ℓ hmero]

/-- **The atom sum is invisible at every order but its own.** -/
theorem laurentCoeff_atomRealization_of_ne_order (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ)
    (c : ℂ → ℂ) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) (hne : ℓ ≠ -((j : ℤ) + 1)) :
    laurentCoeff (atomRealization σ j R c) w ℓ = 0 := by
  rw [laurentCoeff_atomRealization hσ j R c w ℓ]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [laurentCoeff_jetAtom_of_ne_order hσ _ j w hℓ hne, mul_zero]

/-- **Off every prescribed line the atom sum has no principal part.** -/
theorem laurentCoeff_atomRealization_off (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ)
    {w : ℂ} (hw : ∀ q ∈ R, ¬ sameLine σ q w) :
    laurentCoeff (atomRealization σ j R c) w (-((j : ℤ) + 1)) = 0 := by
  classical
  rw [laurentCoeff_atomRealization hσ j R c w (-((j : ℤ) + 1))]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [laurentCoeff_jetAtom_placed hσ q j w, if_neg (hw q hq), mul_zero]

/-- **On a prescribed line the atom sum has exactly the prescribed coefficient**, provided the
representatives lie on pairwise distinct lines. -/
theorem laurentCoeff_atomRealization_line (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ)
    (hdist : ∀ q ∈ R, ∀ r ∈ R, sameLine σ q r → q = r)
    {q : ℂ} (hq : q ∈ R) {w : ℂ} (hw : sameLine σ q w) :
    laurentCoeff (atomRealization σ j R c) w (-((j : ℤ) + 1)) = c q := by
  classical
  rw [laurentCoeff_atomRealization hσ j R c w (-((j : ℤ) + 1))]
  have hterm : ∀ r ∈ R,
      (c r / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
          laurentCoeff (jetAtom σ (r - thetaHalfPeriod σ) j) w (-((j : ℤ) + 1))
        = if r = q then c q else 0 := by
    intro r hr
    rw [laurentCoeff_jetAtom_placed hσ r j w]
    by_cases hrq : r = q
    · subst hrq
      rw [if_pos hw, if_pos rfl]
      have hfac : ((j.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
      have hpow : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
    · have hns : ¬ sameLine σ r w := by
        intro hs
        exact hrq (hdist r hr q hq (sameLine_trans hs (sameLine_symm hw)))
      rw [if_neg hns, if_neg hrq, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' R q (fun _ => c q), if_pos hq]

/-- **Every atom sum is realized by a differentially algebraic germ.** -/
theorem realizedDA_atomRealization (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (c : ℂ → ℂ) :
    RealizedDA (atomRealization σ j R c) := by
  classical
  have hfun : atomRealization σ j R c
      = ∑ q ∈ R, fun z => (c q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
          jetAtom σ (q - thetaHalfPeriod σ) j z := by
    funext z
    simp only [atomRealization, Finset.sum_apply]
  rw [hfun]
  exact RealizedDA.sum R _ fun q _ => (realizedDA_jetAtom hσ _ j).const_mul _

/-- **Every atom sum is differentially algebraic.** -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_atomRealization (hσ : 0 < σ.im) (j : ℕ)
    (R : Finset ℂ) (c : ℂ → ℂ) :
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (atomRealization σ j R c) (Set.univ : Set ℂ)) :=
  (realizedDA_atomRealization hσ j R c).differentiallyAlgebraic

end

end GaloisForLFunctions.HTGeometry
