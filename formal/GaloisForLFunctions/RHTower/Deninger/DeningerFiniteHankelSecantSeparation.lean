import GaloisForLFunctions.RHTower.Deninger.DeningerHankelReducedSecantSeparation
import GaloisForLFunctions.RHTower.Deninger.DeningerHankelDiagonalMonicity

/-!
# Finite higher-rank Hankel secant separation

This module restricts universal reduced-support separation to a finite moment-variable window.
The result is the exact normal-form injectivity statement needed by finite Hankel division.
-/

namespace RHTower
noncomputable section

open MvPolynomial
open scoped BigOperators MonomialOrder

/-- Finite exponent is chain-reduced after embedding its variables in the infinite moment line. -/
def FiniteHankelChainReduced (N r : ℕ) (e : Fin N →₀ ℕ) : Prop :=
  HankelChainReduced r (Finsupp.mapDomain Fin.val e)

/-- Finite ordered-atom parameterization obtained by restricting the universal moment line. -/
def finiteHankelSecantParameterization
    (R : Type*) [CommRing R] (N r : ℕ) :
    MvPolynomial (Fin N) R →+* MvPolynomial (Fin r × Fin 2) R :=
  (deningerHankelSecantParameterization R r).comp
    (MvPolynomial.rename Fin.val).toRingHom

@[simp] theorem finiteHankelSecantParameterization_X
    (R : Type*) [CommRing R] (N r : ℕ) (i : Fin N) :
    finiteHankelSecantParameterization R N r (X i) =
      deningerHankelSecantMoment R r i.val := by
  simp [finiteHankelSecantParameterization]

/-- Finite reduced-support polynomials remain nonzero under the ordered-atom map over every
commutative ring. -/
theorem finiteHankelSecantParameterization_ne_zero_of_reduced
    (R : Type*) [CommRing R] (N r : ℕ) {P : MvPolynomial (Fin N) R}
    (hred : ∀ e ∈ P.support, FiniteHankelChainReduced N r e)
    (hP : P ≠ 0) :
    finiteHankelSecantParameterization R N r P ≠ 0 := by
  let Q := MvPolynomial.rename Fin.val P
  have hQ : Q ≠ 0 :=
    (MvPolynomial.rename_injective Fin.val Fin.val_injective).ne hP
  have hQred : ∀ e ∈ Q.support, HankelChainReduced r e := by
    intro e he
    change e ∈ (MvPolynomial.rename Fin.val P).support at he
    rw [MvPolynomial.support_rename_of_injective Fin.val_injective] at he
    rw [Finset.mem_image] at he
    obtain ⟨d, hd, rfl⟩ := he
    exact hred d hd
  change deningerHankelSecantParameterization R r
    (MvPolynomial.rename Fin.val P) ≠ 0
  change deningerHankelSecantParameterization R r Q ≠ 0
  exact deningerHankelSecantParameterization_ne_zero_of_reduced R r hQred hQ

/-- A finite maximal Hankel minor becomes the corresponding universal generic minor under the
canonical variable embedding. -/
theorem rename_finiteHankelMaximalMinorOver
    (R : Type*) [CommRing R] {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N) :
    MvPolynomial.rename Fin.val (finiteHankelMaximalMinorOver R c hbound) =
      ((deningerGenericMomentHankel R).submatrix Fin.val c).det := by
  rw [finiteHankelMaximalMinorOver, (MvPolynomial.rename Fin.val).map_det]
  congr 1
  ext i j
  simp [finiteHankelIndex, deningerGenericMomentHankel]

/-- Every finite `(r+1)` Hankel minor vanishes under the finite ordered-atom map over arbitrary
commutative rings, including nonreduced rings. -/
theorem finiteHankelSecantParameterization_minor_zero
    (R : Type*) [CommRing R] {N : ℕ} (r : ℕ)
    (c : Fin (r + 1) → ℕ) (hbound : ∀ j, r + 1 + c j ≤ N) :
    finiteHankelSecantParameterization R N r
      (finiteHankelMaximalMinorOver R c hbound) = 0 := by
  rw [finiteHankelSecantParameterization, RingHom.comp_apply]
  change deningerHankelSecantParameterization R r
    (MvPolynomial.rename Fin.val (finiteHankelMaximalMinorOver R c hbound)) = 0
  rw [rename_finiteHankelMaximalMinorOver]
  exact deningerHankelSecantParameterization_minor_zero R r Fin.val c

/-! ## Exact bridge from forbidden chains to leading Hankel diagonals -/

/-- A strictly increasing natural-valued sequence on `Fin (n+1)` dominates the ordinal index.
This is the arithmetic input that turns an enumerated chain into Hankel column offsets. -/
theorem fin_val_le_of_strictMono_nat {n : ℕ} {d : Fin (n + 1) → ℕ}
    (hd : StrictMono d) (j : Fin (n + 1)) : j.val ≤ d j := by
  induction j using Fin.inductionOn with
  | zero => simp
  | succ i ih =>
      have hlt : d i.castSucc < d i.succ :=
        hd (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      change i.val ≤ d i.castSucc at ih
      change i.val + 1 ≤ d i.succ
      omega

/-- Every failure of `r`-chain reduction is divisible by the exact degree-lex leading diagonal
of a canonical finite `(r+1) × (r+1)` Hankel minor.  The columns are constructed by enumerating
the forbidden chain `d₀<⋯<dᵣ` and taking offsets `cⱼ=dⱼ-j`; pairwise chain adjacency gives the
strict gap needed for `c` itself to be strictly increasing. -/
theorem exists_finiteHankelMinor_diagonal_le_of_not_chainReduced
    {N r : ℕ} {e : Fin N →₀ ℕ}
    (hnot : ¬FiniteHankelChainReduced N r e) :
    ∃ (c : Fin (r + 1) → ℕ) (hbound : ∀ j, r + 1 + c j ≤ N),
      StrictMono c ∧ hankelDiagonalExponent c hbound ≤ e := by
  rw [FiniteHankelChainReduced, HankelChainReduced] at hnot
  push Not at hnot
  obtain ⟨J, hJcard, hJchain, hJsub⟩ := hnot
  let d : Fin (r + 1) → ℕ := J.orderEmbOfFin hJcard
  have hd : StrictMono d := (J.orderEmbOfFin hJcard).strictMono
  have hdmem : ∀ j, d j ∈ J := by
    intro j
    exact J.orderEmbOfFin_mem hJcard j
  have hgap : ∀ j : Fin r, d j.castSucc + 1 < d j.succ := by
    intro j
    have hadj := hJchain (hdmem j.castSucc) (hdmem j.succ)
      (ne_of_lt (hd (show j.castSucc < j.succ from Fin.castSucc_lt_succ)))
    change d j.castSucc + 1 < d j.succ ∨ d j.succ + 1 < d j.castSucc at hadj
    have hlt : d j.castSucc < d j.succ :=
      hd (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    omega
  have hdltN : ∀ j, d j < N := by
    intro j
    have hj := hJsub (hdmem j)
    rw [Finsupp.mapDomain_support_of_injective Fin.val_injective] at hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, hid⟩ := hj
    rw [← hid]
    exact i.isLt
  let c : Fin (r + 1) → ℕ := fun j => d j - j.val
  have hc : StrictMono c := by
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    have hgapj := hgap j
    have hjle : j.val ≤ d j.castSucc := by
      simpa only [Fin.val_castSucc] using
        (fin_val_le_of_strictMono_nat hd j.castSucc)
    have hjsle : j.val + 1 ≤ d j.succ := by
      simpa only [Fin.val_succ] using
        (fin_val_le_of_strictMono_nat hd j.succ)
    change d j.castSucc - j.val < d j.succ - (j.val + 1)
    omega
  have hd_eq (j : Fin (r + 1)) : j.val + c j = d j := by
    exact Nat.add_sub_of_le (fin_val_le_of_strictMono_nat hd j)
  have hbound : ∀ j, r + 1 + c j ≤ N := by
    intro j
    have hc_le : c j ≤ c (Fin.last r) := hc.monotone (Fin.le_last j)
    have hlast := hdltN (Fin.last r)
    have hlastEq := hd_eq (Fin.last r)
    simp only [Fin.val_last] at hlastEq
    omega
  refine ⟨c, hbound, hc, ?_⟩
  have hmapdiag :
      Finsupp.mapDomain Fin.val (hankelDiagonalExponent c hbound) =
        hankelChainIndicator J := by
    rw [hankelDiagonalExponent, hankelPermutationExponent,
      Finsupp.mapDomain_finsetSum]
    simp only [Equiv.Perm.one_apply, Finsupp.mapDomain_single]
    have hterm : (fun j : Fin (r + 1) =>
        Finsupp.single ((finiteHankelIndex c hbound j j).val) 1) =
        fun j => Finsupp.single (d j) 1 := by
      funext j
      congr 1
      simp [finiteHankelIndex, hd_eq]
    rw [hterm, hankelChainIndicator]
    rw [← J.image_orderEmbOfFin_univ hJcard]
    rw [Finset.sum_image hd.injective.injOn]
  have hlemap : Finsupp.mapDomain Fin.val (hankelDiagonalExponent c hbound) ≤
      Finsupp.mapDomain Fin.val e := by
    rw [hmapdiag]
    exact hankelChainIndicator_le_iff.mpr hJsub
  intro i
  have hi := hlemap i.val
  rw [Finsupp.mapDomain_apply Fin.val_injective,
    Finsupp.mapDomain_apply Fin.val_injective] at hi
  exact hi

end
end RHTower
