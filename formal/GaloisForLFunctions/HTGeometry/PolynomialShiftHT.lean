import GaloisForLFunctions.HTGeometry.NonrealFactorialSlopeHT

/-!
# Hypertranscendence is unchanged by a polynomial shift

Two formal series differing by a series with finitely many nonzero coefficients have the same
differential-algebraic behaviour.  The substitution `Yⱼ ↦ Yⱼ + Qⱼ(X)`, where `Qⱼ` is the polynomial
realising the `j`-th derivative of the difference, is an automorphism of the differential polynomial
algebra: it is fixed on the variable slot, so its inverse is the substitution with `-Qⱼ`.  Hence a
nonzero relation for one series transports to a nonzero relation for the other.

This lets an eventual coefficient asymptotic be applied to a sequence whose first terms are
arbitrary.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-! ## Series with finitely many nonzero coefficients -/

/-- A formal series with finitely many nonzero coefficients. -/
def IsPolySeries (F : ℂ⟦X⟧) : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n → PowerSeries.coeff n F = 0

theorem IsPolySeries.derivative {F : ℂ⟦X⟧} (h : IsPolySeries F) :
    IsPolySeries ((d⁄dX ℂ) F) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  rw [PowerSeries.coeff_derivative, hN (n + 1) (le_trans hn (Nat.le_succ n)), zero_mul]

theorem IsPolySeries.iterate {F : ℂ⟦X⟧} (h : IsPolySeries F) (j : ℕ) :
    IsPolySeries ((⇑(d⁄dX ℂ))^[j] F) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ih.derivative

/-- Iterated formal differentiation is additive. -/
theorem iterate_powerSeriesDerivative_sub (F G : ℂ⟦X⟧) (j : ℕ) :
    (⇑(d⁄dX ℂ))^[j] (F - G) = (⇑(d⁄dX ℂ))^[j] F - (⇑(d⁄dX ℂ))^[j] G := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_sub]

/-! ## Realising a finite-support series inside the variable slot -/

/-- The differential polynomial `∑_{k<N} c k · Y₀^k`, involving only the variable slot. -/
def slotPoly (m N : ℕ) (c : ℕ → ℂ) : MvPolynomial (Fin (m + 2)) ℂ :=
  ∑ k ∈ Finset.range N, MvPolynomial.C (c k) * MvPolynomial.X 0 ^ k

theorem aeval_slotPoly {A : Type*} [CommRing A] [Algebra ℂ A] (g : Fin (m + 2) → A)
    (N : ℕ) (c : ℕ → ℂ) :
    aeval g (slotPoly m N c) = ∑ k ∈ Finset.range N, algebraMap ℂ A (c k) * g 0 ^ k := by
  rw [slotPoly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]

/-- A substitution fixing the variable slot fixes every variable-slot polynomial. -/
theorem aeval_slotPoly_self (sh : Fin (m + 2) → MvPolynomial (Fin (m + 2)) ℂ)
    (hsh : sh 0 = MvPolynomial.X 0) (N : ℕ) (c : ℕ → ℂ) :
    aeval sh (slotPoly m N c) = slotPoly m N c := by
  rw [aeval_slotPoly, hsh, slotPoly]
  rfl

/-- Evaluating a variable-slot polynomial on jets returns the corresponding truncated series. -/
theorem aeval_slotPoly_coeff (g : Fin (m + 2) → ℂ⟦X⟧) (hg : g 0 = PowerSeries.X)
    {F : ℂ⟦X⟧} {N : ℕ} (hF : ∀ n : ℕ, N ≤ n → PowerSeries.coeff n F = 0) :
    aeval g (slotPoly m N fun k => PowerSeries.coeff k F) = F := by
  classical
  rw [aeval_slotPoly, hg]
  refine PowerSeries.ext fun n => ?_
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range N,
      PowerSeries.coeff n ((algebraMap ℂ ℂ⟦X⟧) (PowerSeries.coeff k F) * PowerSeries.X ^ k)
        = if k = n then PowerSeries.coeff n F else 0 := by
    intro k _
    have hC : (algebraMap ℂ ℂ⟦X⟧) (PowerSeries.coeff k F) = PowerSeries.C (PowerSeries.coeff k F) :=
      rfl
    rw [hC, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases hk : n = k
    · subst hk; simp
    · rw [if_neg hk, if_neg (fun hc => hk hc.symm), mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hn : n < N
  · rw [Finset.sum_ite_eq' (Finset.range N) n (fun _ => PowerSeries.coeff n F),
      if_pos (Finset.mem_range.mpr hn)]
  · rw [Finset.sum_ite_eq' (Finset.range N) n (fun _ => PowerSeries.coeff n F),
      if_neg (fun hc => hn (Finset.mem_range.mp hc)), hF n (not_lt.mp hn)]

/-! ## The shift automorphism -/

/-- The substitution `Y₀ ↦ Y₀`, `Y_{j+1} ↦ Y_{j+1} + Qⱼ`. -/
def jetTranslate (Q : ℕ → MvPolynomial (Fin (m + 2)) ℂ) :
    Fin (m + 2) → MvPolynomial (Fin (m + 2)) ℂ :=
  Fin.cons (MvPolynomial.X 0) (fun j : Fin (m + 1) => MvPolynomial.X j.succ + Q (j : ℕ))

@[simp] theorem jetTranslate_zero (Q : ℕ → MvPolynomial (Fin (m + 2)) ℂ) :
    jetTranslate Q 0 = MvPolynomial.X 0 := rfl

@[simp] theorem jetTranslate_succ (Q : ℕ → MvPolynomial (Fin (m + 2)) ℂ) (j : Fin (m + 1)) :
    jetTranslate Q j.succ = MvPolynomial.X j.succ + Q (j : ℕ) := by
  simp [jetTranslate]

/-- Fixed by every substitution that fixes the variable slot. -/
def SlotOnly (Q : MvPolynomial (Fin (m + 2)) ℂ) : Prop :=
  ∀ sh : Fin (m + 2) → MvPolynomial (Fin (m + 2)) ℂ,
    sh 0 = MvPolynomial.X 0 → aeval sh Q = Q

theorem slotOnly_slotPoly (N : ℕ) (c : ℕ → ℂ) : SlotOnly (slotPoly m N c) :=
  fun sh hsh => aeval_slotPoly_self sh hsh N c

/-- **The shift substitution is injective.**  Its left inverse is the shift by `-Q`. -/
theorem aeval_jetTranslate_injective (Q : ℕ → MvPolynomial (Fin (m + 2)) ℂ)
    (hQ : ∀ j : ℕ, SlotOnly (Q j)) :
    Function.Injective (aeval (jetTranslate Q) : MvPolynomial (Fin (m + 2)) ℂ → _) := by
  set Q' : ℕ → MvPolynomial (Fin (m + 2)) ℂ := fun j => -(Q j) with hQ'
  have hcomp : (aeval (jetTranslate Q')).comp (aeval (jetTranslate Q)) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.id_apply]
    induction i using Fin.cases with
    | zero => rw [jetTranslate_zero, MvPolynomial.aeval_X, jetTranslate_zero]
    | succ j =>
        rw [jetTranslate_succ, map_add, MvPolynomial.aeval_X, jetTranslate_succ,
          hQ (j : ℕ) (jetTranslate Q') (jetTranslate_zero Q'), hQ']
        ring
  intro x y hxy
  have hx : (aeval (jetTranslate Q')) ((aeval (jetTranslate Q)) x) = x := by
    have := congrArg (fun φ => φ x) hcomp
    simpa using this
  have hy : (aeval (jetTranslate Q')) ((aeval (jetTranslate Q)) y) = y := by
    have := congrArg (fun φ => φ y) hcomp
    simpa using this
  rw [← hx, ← hy, hxy]

/-! ## The transfer -/

/-- **Transfer along a jet shift.**  If every jet of `f` is the corresponding jet of `g` plus a
variable-slot polynomial evaluated on the jets of `g`, then nonvanishing transports from `g` to
`f`. -/
theorem aeval_formalJets_ne_zero_of_jetTranslate {f g : ℂ⟦X⟧}
    (Q : ℕ → MvPolynomial (Fin (m + 2)) ℂ) (hQ : ∀ j : ℕ, SlotOnly (Q j))
    (hval : ∀ j : Fin (m + 1),
      formalJetsOver m g j.succ + aeval (formalJetsOver m g) (Q (j : ℕ))
        = formalJetsOver m f j.succ)
    (hg : ∀ P : MvPolynomial (Fin (m + 2)) ℂ, P ≠ 0 → aeval (formalJetsOver m g) P ≠ 0) :
    ∀ P : MvPolynomial (Fin (m + 2)) ℂ, P ≠ 0 → aeval (formalJetsOver m f) P ≠ 0 := by
  have hslots : (fun i => (aeval (formalJetsOver m g)) (jetTranslate Q i)) = formalJetsOver m f := by
    funext i
    induction i using Fin.cases with
    | zero =>
        rw [jetTranslate_zero, MvPolynomial.aeval_X, formalJetsOver_zero, formalJetsOver_zero]
    | succ j => rw [jetTranslate_succ, map_add, MvPolynomial.aeval_X, hval j]
  have hkey : (aeval (formalJetsOver m g)).comp (aeval (jetTranslate Q))
      = aeval (formalJetsOver m f) := by
    rw [MvPolynomial.comp_aeval, hslots]
  intro P hP
  have hshift : aeval (jetTranslate Q) P ≠ 0 := by
    intro hc
    refine hP (aeval_jetTranslate_injective Q hQ ?_)
    rw [hc, map_zero]
  have hval2 : aeval (formalJetsOver m f) P
      = aeval (formalJetsOver m g) (aeval (jetTranslate Q) P) := by
    rw [← hkey, AlgHom.comp_apply]
  rw [hval2]
  exact hg _ hshift

/-- **Hypertranscendence is unchanged by a polynomial shift.** -/
theorem aeval_formalJets_ne_zero_of_polySeries_sub {f g : ℂ⟦X⟧}
    (hdiff : IsPolySeries (f - g))
    (hg : ∀ P : MvPolynomial (Fin (m + 2)) ℂ, P ≠ 0 → aeval (formalJetsOver m g) P ≠ 0) :
    ∀ P : MvPolynomial (Fin (m + 2)) ℂ, P ≠ 0 → aeval (formalJetsOver m f) P ≠ 0 := by
  classical
  obtain ⟨N, hN⟩ := hdiff
  have hiter : ∀ j : ℕ, ∀ n : ℕ, N ≤ n →
      PowerSeries.coeff n ((⇑(d⁄dX ℂ))^[j] (f - g)) = 0 := by
    intro j
    induction j with
    | zero => intro n hn; simpa using hN n hn
    | succ j ih =>
        intro n hn
        rw [Function.iterate_succ_apply', PowerSeries.coeff_derivative,
          ih (n + 1) (le_trans hn (Nat.le_succ n)), zero_mul]
  refine aeval_formalJets_ne_zero_of_jetTranslate
    (fun j => slotPoly m N fun k => PowerSeries.coeff k ((⇑(d⁄dX ℂ))^[j] (f - g)))
    (fun j => slotOnly_slotPoly N _) ?_ hg
  intro j
  have hg0 : formalJetsOver m g 0 = PowerSeries.X := formalJetsOver_zero m g
  rw [aeval_slotPoly_coeff (formalJetsOver m g) hg0 (hiter (j : ℕ))]
  rw [iterate_powerSeriesDerivative_sub f g (j : ℕ), formalJetsOver_succ, formalJetsOver_succ]
  ring

end

end GaloisForLFunctions.HTGeometry
