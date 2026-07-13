import GaloisForLFunctions.HTGeometry.LogDerivBellTransfer
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental

/-!
# The power relation from a differential-algebraic relation

Assembling the pieces: a differential-algebraic relation for an analytic nonzero `f`
becomes, through the Bell transfer, a power relation
`∑_d f^d·(uJet u z)(Q_d) = 0` on `Ω = {f ≠ 0}` (`u = f'/f`) with coefficients
`Q_d = finPolyToNat n (bellGraded n (reshapeJet n P) d) ∈ MvPolynomial ℕ ℂ` — the exact input
consumed by `diffPowerRel_yields` / `logDeriv_DA_of_powerRel`.

`xiDA_powerRelation` builds the relation from the reshaped differential polynomial `P` via the
Bell-graded expansion (`eval₂_bell_expansion`), the reshape identity (`eval₂_reshapeJet`), the
generic Bell identity, and the frame translation.  Discharging log-derivative differential
algebraicity end-to-end then needs only the non-vanishing
`P ≠ 0 → ∃ d, finPolyToNat n (bellGraded n (reshapeJet n P) d) ≠ 0`, which is `P ≠ 0` carried
through the injective frame translation and the Bell-surjectivity vanishing argument of
`hypertranscendental_gamma`.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial Filter Topology

/-- **The power relation from a differential-algebraic relation.**  A differential polynomial
`P` annihilating the jets of an analytic nonzero `f` on `Ω` becomes a power relation
`∑_d f^d·(uJet u z)(finPolyToNat n (bellGraded n (reshapeJet n P) d)) = 0` (`u = f'/f`). -/
theorem xiDA_powerRelation {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hfan : ∀ z ∈ Ω, AnalyticAt ℂ f z) (hfne : ∀ z ∈ Ω, f z ≠ 0)
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hPz : ∀ z ∈ Ω, eval (Fin.cons z (fun j : Fin (n + 1) =>
      iteratedDeriv (j : ℕ) f z)) P = 0) :
    ∀ z ∈ Ω, ∑ dd ∈ Finset.range ((reshapeJet n P).totalDegree + 1),
      f z ^ dd * eval (uJet (fun w => deriv f w / f w) z)
        (finPolyToNat n (bellGraded n (reshapeJet n P) dd)) = 0 := by
  set u : ℂ → ℂ := fun w => deriv f w / f w with hu_def
  set H := reshapeJet n P with hH
  intro z hz
  have hexp := eval₂_bell_expansion n H z (f z)
    (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z)
  have hv : (fun j : Fin (n + 1) =>
        f z * eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z)
          (bellAt n (j : ℕ) (le_of_lt j.isLt)))
      = fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z := by
    funext j
    rw [bellAt, eval_rename]
    have hcomp : ((fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z)
          ∘ Fin.castLE (le_of_lt j.isLt))
        = fun i : Fin (j : ℕ) => iteratedDeriv (i : ℕ) u z := by
      funext i; simp [Fin.val_castLE]
    rw [hcomp, ← iteratedDeriv_eq_bellCore_generic hΩ hfan hfne (j : ℕ) hz]
  have hLHS : eval₂ (Polynomial.evalRingHom z)
      (fun j : Fin (n + 1) => f z * eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z)
        (bellAt n (j : ℕ) (le_of_lt j.isLt))) H = 0 := by
    rw [hv, hH, eval₂_reshapeJet]
    exact hPz z hz
  rw [hLHS] at hexp
  have hconv : ∑ dd ∈ Finset.range (H.totalDegree + 1),
      f z ^ dd * eval (uJet u z) (finPolyToNat n (bellGraded n H dd))
      = ∑ dd ∈ Finset.range (H.totalDegree + 1),
        f z ^ dd * eval₂ (Polynomial.evalRingHom z)
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z) (bellGraded n H dd) := by
    refine Finset.sum_congr rfl fun dd _ => ?_
    rw [eval_uJet_finPolyToNat]
  rw [hconv]
  exact hexp.symm

/-- **Log-derivative differential algebraicity from a differential-algebraic relation, modulo
non-vanishing.**  Given the reshaped differential polynomial's Bell-graded coefficients do not
all vanish, an analytic nonzero `f` with a differential-algebraic relation yields a nonzero
differential-algebraic relation for `u = f'/f` on `Ω`. -/
theorem logDeriv_DA_of_DA {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hfan : ∀ z ∈ Ω, AnalyticAt ℂ f z) (hfne : ∀ z ∈ Ω, f z ≠ 0)
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hPz : ∀ z ∈ Ω, eval (Fin.cons z (fun j : Fin (n + 1) =>
      iteratedDeriv (j : ℕ) f z)) P = 0)
    (hne : ∃ dd ∈ Finset.range ((reshapeJet n P).totalDegree + 1),
      finPolyToNat n (bellGraded n (reshapeJet n P) dd) ≠ 0) :
    ∃ R : MvPolynomial ℕ ℂ, R ≠ 0 ∧
      ∀ z ∈ Ω, eval (uJet (fun w => deriv f w / f w) z) R = 0 :=
  logDeriv_DA_of_powerRel hΩ hfan hfne
    (xiDA_powerRelation hΩ hfan hfne n P hPz) hne

/-! ## The non-vanishing, and sub-brick (1) end to end -/

/-- Left inverse of the frame translation: `x₀ ↦ C X`, `x_{k+1} ↦ X_k` (or `0` beyond). -/
def natToFinPoly (n : ℕ) :
    MvPolynomial ℕ ℂ →+* MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
  eval₂Hom ((MvPolynomial.C).comp Polynomial.C)
    (fun k : ℕ => if k = 0 then C Polynomial.X
      else if h2 : k - 1 < n + 1 then X ⟨k - 1, h2⟩ else 0)

theorem finPolyToNat_injective (n : ℕ) : Function.Injective (finPolyToNat n) := by
  have hleft : (natToFinPoly n).comp (finPolyToNat n) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a; simp [finPolyToNat, natToFinPoly, Polynomial.coe_eval₂RingHom]
      · simp [finPolyToNat, natToFinPoly, Polynomial.coe_eval₂RingHom]
    · intro j
      simp only [RingHom.comp_apply, finPolyToNat, eval₂Hom_X', natToFinPoly, RingHom.id_apply]
      have h0 : (j : ℕ) + 1 ≠ 0 := Nat.succ_ne_zero _
      rw [if_neg h0]
      have h2 : (j : ℕ) + 1 - 1 < n + 1 := by have := j.isLt; omega
      rw [dif_pos h2]
      simp
  exact Function.LeftInverse.injective (g := natToFinPoly n)
    (fun x => by rw [← RingHom.comp_apply, hleft, RingHom.id_apply])

/-- If all Bell-graded coefficients of the reshaped `P` vanish, then `P = 0`: the
Bell-surjectivity vanishing argument (`exists_bellAt_solution`). -/
theorem Pzero_of_bellGraded_zero (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hGzero : ∀ dd, dd ≤ (reshapeJet n P).totalDegree →
      bellGraded n (reshapeJet n P) dd = 0) :
    P = 0 := by
  set H := reshapeJet n P with hH_def
  have hvanish : ∀ v : Fin (n + 2) → ℂ, v 1 ≠ 0 → eval v P = 0 := by
    intro v hu1
    obtain ⟨w, hw⟩ := exists_bellAt_solution n (fun k =>
      if h : (k : ℕ) + 2 < n + 2 then v ⟨(k : ℕ) + 2, h⟩ / v 1 else 0)
    have hvec : (Fin.cons (v 0) (fun j : Fin (n + 1) => v 1
        * eval w (bellAt n (j : ℕ) (le_of_lt j.isLt))) : Fin (n + 2) → ℂ) = v := by
      funext i
      induction i using Fin.cases with
      | zero => rw [Fin.cons_zero]
      | succ j =>
          rw [Fin.cons_succ]
          induction j using Fin.cases with
          | zero =>
              rw [show bellAt n ((0 : Fin (n + 1)) : ℕ)
                  (le_of_lt (0 : Fin (n + 1)).isLt) = 1 from bellAt_zero n _]
              rw [map_one, mul_one]
              rfl
          | succ i =>
              have hidx : ((i.succ : Fin (n + 1)) : ℕ)
                  = ((i.castSucc : Fin (n + 1)) : ℕ) + 1 := by simp
              rw [show bellAt n ((i.succ : Fin (n + 1)) : ℕ)
                    (le_of_lt (i.succ : Fin (n + 1)).isLt)
                  = bellAt n (((i.castSucc : Fin (n + 1)) : ℕ) + 1) (i.castSucc).isLt
                  from bellAt_congr hidx _ _]
              rw [hw i.castSucc]
              have hlt : ((i.castSucc : Fin (n + 1)) : ℕ) + 2 < n + 2 := by
                have := i.isLt
                simp only [Fin.val_castSucc]
                omega
              rw [dif_pos hlt, mul_div_cancel₀ _ hu1]
              congr 1
    have hval0 : eval v P
        = ∑ dd ∈ Finset.range (H.totalDegree + 1),
            (v 1) ^ dd * eval₂ (Polynomial.evalRingHom (v 0)) w (bellGraded n H dd) := by
      conv_lhs => rw [← hvec]
      rw [← eval₂_reshapeJet n (v 0)
        (fun j : Fin (n + 1) => v 1 * eval w (bellAt n (j : ℕ) (le_of_lt j.isLt))) P]
      exact eval₂_bell_expansion n H (v 0) (v 1) w
    rw [hval0]
    refine Finset.sum_eq_zero fun dd hdd => ?_
    rw [hGzero dd (Nat.lt_succ_iff.mp (Finset.mem_range.mp hdd)), eval₂_zero, mul_zero]
  have hXP : X 1 * P = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, eval_X, map_zero]
    by_cases hv : v 1 = 0
    · rw [hv, zero_mul]
    · rw [hvanish v hv, mul_zero]
  exact (mul_eq_zero.mp hXP).resolve_left (X_ne_zero 1)

/-- **The non-vanishing.**  A nonzero `P` has a nonzero `ℕ`-frame Bell-graded coefficient. -/
theorem exists_finPolyToNat_bellGraded_ne_zero (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (hP : P ≠ 0) :
    ∃ dd ∈ Finset.range ((reshapeJet n P).totalDegree + 1),
      finPolyToNat n (bellGraded n (reshapeJet n P) dd) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hP
  apply Pzero_of_bellGraded_zero n P
  intro dd hdd
  have hz := hcon dd (Finset.mem_range.mpr (Nat.lt_succ_of_le hdd))
  exact finPolyToNat_injective n (by rw [hz, map_zero])

/-- **Sub-brick (1), end to end.**  An analytic nonzero `f` on the open `Ω` satisfying a
nonzero differential-algebraic relation yields a nonzero differential-algebraic relation for
its logarithmic derivative `u = f'/f` on `Ω`. -/
theorem logDeriv_DA_of_DA_full {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hfan : ∀ z ∈ Ω, AnalyticAt ℂ f z) (hfne : ∀ z ∈ Ω, f z ≠ 0)
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (hP : P ≠ 0)
    (hPz : ∀ z ∈ Ω, eval (Fin.cons z (fun j : Fin (n + 1) =>
      iteratedDeriv (j : ℕ) f z)) P = 0) :
    ∃ R : MvPolynomial ℕ ℂ, R ≠ 0 ∧
      ∀ z ∈ Ω, eval (uJet (fun w => deriv f w / f w) z) R = 0 :=
  logDeriv_DA_of_DA hΩ hfan hfne n P hPz
    (exists_finPolyToNat_bellGraded_ne_zero n P hP)

end GaloisForLFunctions

end
