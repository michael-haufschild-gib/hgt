import GaloisForLFunctions.RHTower.CompletedFluxGermRigidity

/-!
# Graded reality of the completed-flux Taylor sequence

Functional-equation reflection and Schwarz conjugation act differently on the single completed-flux
Taylor sequence: reflection multiplies order `n` by `(-1)^n`, while Schwarz conjugates its value.
Germ rigidity therefore turns the critical line into the fixed locus of one graded-reality law

`(-1)^n * c_n(ρ) = conj (c_n(ρ))` for every `n`.

This removes the two-base comparison from the constraint interface.  Every off-critical point has a
finite parity-phase defect: an even coefficient with nonzero imaginary part or an odd coefficient
with nonzero real part.  The quadratic Laguerre reader is the even order-two member, but its sign is
not asserted to detect every off-line zero.

The final theorem expands each coefficient into its fixed continued-prime and
archimedean/boundary terms.  It is an exact RH-equivalent source-coordinate interface, not a proof
of the source-side graded-reality law.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Schwarz reflection commutes with the complex derivative of `xi`. -/
theorem xi_deriv_conj (s : ℂ) :
    deriv xi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv xi s) := by
  have hfun : (starRingEnd ℂ) ∘ xi ∘ (starRingEnd ℂ) = xi := by
    funext z
    simp [Function.comp_apply, xi_conj]
  have hder : deriv xi =
      (starRingEnd ℂ) ∘ deriv xi ∘ (starRingEnd ℂ) := by
    calc
      deriv xi = deriv ((starRingEnd ℂ) ∘ xi ∘ (starRingEnd ℂ)) :=
        congrArg deriv hfun.symm
      _ = (starRingEnd ℂ) ∘ deriv xi ∘ (starRingEnd ℂ) := deriv_conj_conj
  simpa [Function.comp_apply] using congrFun hder ((starRingEnd ℂ) s)

/-- The completed logarithmic flux is Schwarz-equivariant. -/
theorem seamFluxCochain_conj (s : ℂ) :
    seamFluxCochain ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (seamFluxCochain s) := by
  rw [seamFluxCochain, seamFluxCochain, logDeriv_apply, logDeriv_apply,
    xi_deriv_conj, xi_conj]
  simp

/-- Schwarz equivariance survives the residue filling at a zero of `xi`. -/
theorem completedFluxGermAt_conj (ρ x : ℂ) :
    completedFluxGermAt ((starRingEnd ℂ) ρ) ((starRingEnd ℂ) x) =
      (starRingEnd ℂ) (completedFluxGermAt ρ x) := by
  by_cases hx : x = 0
  · subst x
    simp [xi_orderAt_conj]
  · have hcx : (starRingEnd ℂ) x ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hx
    rw [completedFluxGermAt, if_neg hcx, completedFluxGermAt, if_neg hx]
    rw [show (starRingEnd ℂ) ρ + (starRingEnd ℂ) x =
      (starRingEnd ℂ) (ρ + x) by simp, seamFluxCochain_conj]
    simp

/-- Iterated complex derivatives commute with Schwarz reflection. -/
theorem iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]

/-- Every completed-flux Taylor coefficient is Schwarz-equivariant in its base point. -/
theorem completedFluxTaylorCoeff_conj (ρ : ℂ) (n : ℕ) :
    completedFluxTaylorCoeff ((starRingEnd ℂ) ρ) n =
      (starRingEnd ℂ) (completedFluxTaylorCoeff ρ n) := by
  have hfun : completedFluxGermAt ((starRingEnd ℂ) ρ) =
      (starRingEnd ℂ) ∘ completedFluxGermAt ρ ∘ (starRingEnd ℂ) := by
    funext x
    simpa using completedFluxGermAt_conj ρ ((starRingEnd ℂ) x)
  rw [completedFluxTaylorCoeff, completedFluxTaylorCoeff, hfun,
    iteratedDeriv_conj_conj]
  simp [Function.comp_apply]

/-- Solved form of functional-equation parity for the completed-flux coefficient sequence. -/
theorem completedFluxTaylorCoeff_one_sub (ρ : ℂ) (n : ℕ) :
    completedFluxTaylorCoeff (1 - ρ) n =
      (-1 : ℂ) ^ n * completedFluxTaylorCoeff ρ n := by
  have h := completedFluxTaylorCoeff_reflection ρ n
  have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  calc
    completedFluxTaylorCoeff (1 - ρ) n =
        1 * completedFluxTaylorCoeff (1 - ρ) n := by ring
    _ = (((-1 : ℂ) ^ n) ^ 2) * completedFluxTaylorCoeff (1 - ρ) n := by rw [hs]
    _ = (-1 : ℂ) ^ n *
        ((-1 : ℂ) ^ n * completedFluxTaylorCoeff (1 - ρ) n) := by ring
    _ = (-1 : ℂ) ^ n * completedFluxTaylorCoeff ρ n := by rw [h]

/-- The one-base all-order constraint: even coefficients are real and odd coefficients are purely
imaginary, expressed without a parity case split. -/
def CompletedFluxGradedRealAt (ρ : ℂ) : Prop :=
  ∀ n : ℕ, (-1 : ℂ) ^ n * completedFluxTaylorCoeff ρ n =
    (starRingEnd ℂ) (completedFluxTaylorCoeff ρ n)

/-- **Single-germ critical-line reconstruction.**  The completed-flux Taylor sequence is graded
real at every order exactly on the critical line, including at zeros of `xi`. -/
theorem completedFluxGradedRealAt_iff (ρ : ℂ) :
    CompletedFluxGradedRealAt ρ ↔ ρ.re = 1 / 2 := by
  rw [← completedFluxTaylorCoeff_line_pair_all_eq_iff]
  constructor
  · intro h n
    rw [completedFluxTaylorCoeff_one_sub, completedFluxTaylorCoeff_conj]
    exact h n
  · intro h n
    rw [← completedFluxTaylorCoeff_one_sub, ← completedFluxTaylorCoeff_conj]
    exact h n

/-- Every off-critical point has a finite failure of the one-germ graded-reality constraint. -/
theorem exists_completedFlux_gradedReality_defect {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) :
    ∃ n : ℕ, (-1 : ℂ) ^ n * completedFluxTaylorCoeff ρ n ≠
      (starRingEnd ℂ) (completedFluxTaylorCoeff ρ n) := by
  by_contra h
  push Not at h
  exact hρ ((completedFluxGradedRealAt_iff ρ).mp h)

/-- **Finite parity-phase witness.**  At an off-critical point, some even coefficient is nonreal or
some odd coefficient has nonzero real part. -/
theorem exists_completedFlux_parityPhase_defect {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) :
    ∃ n : ℕ,
      (Even n ∧ (completedFluxTaylorCoeff ρ n).im ≠ 0) ∨
      (Odd n ∧ (completedFluxTaylorCoeff ρ n).re ≠ 0) := by
  obtain ⟨n, hn⟩ := exists_completedFlux_gradedReality_defect hρ
  rcases Nat.even_or_odd n with hneven | hnodd
  · refine ⟨n, Or.inl ⟨hneven, ?_⟩⟩
    rw [hneven.neg_one_pow, one_mul] at hn
    intro him
    apply hn
    exact (Complex.conj_eq_iff_im.mpr him).symm
  · refine ⟨n, Or.inr ⟨hnodd, ?_⟩⟩
    rw [hnodd.neg_one_pow, neg_one_mul] at hn
    intro hre
    apply hn
    apply Complex.ext
    · simp [hre]
    · simp

/-- The fixed prime-plus-archimedean version of the one-base graded-reality constraint. -/
def CompletedFluxSourceGradedRealAt (ρ : ℂ) : Prop :=
  ∀ n : ℕ,
    (-1 : ℂ) ^ n *
        (infinitePrimeFluxTaylorCoeff ρ n + archimedeanBoundaryFluxTaylorCoeff ρ n) =
      (starRingEnd ℂ)
        (infinitePrimeFluxTaylorCoeff ρ n + archimedeanBoundaryFluxTaylorCoeff ρ n)

/-- Inside the critical strip, the fixed continued-prime plus archimedean coefficient sequence is
graded real exactly on the critical line. -/
theorem completedFluxSourceGradedRealAt_iff {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    CompletedFluxSourceGradedRealAt ρ ↔ ρ.re = 1 / 2 := by
  rw [← completedFluxGradedRealAt_iff]
  constructor <;> intro h n
  · rw [completedFluxTaylorCoeff_eq_prime_add_archimedean hstrip]
    exact h n
  · rw [← completedFluxTaylorCoeff_eq_prime_add_archimedean hstrip]
    exact h n

/-- RH is equivalent to graded reality of the single residue-filled completed-flux germ at every
zero.  This is a zero-fed coordinate criterion; its purpose is to expose the exact all-order
constraint that an independent source theorem would have to force. -/
theorem rh_iff_forall_zero_completedFluxGradedRealAt :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, xi ρ = 0 → CompletedFluxGradedRealAt ρ := by
  constructor
  · intro hRH ρ hzero
    apply (completedFluxGradedRealAt_iff ρ).mpr
    have hright := rh_iff_xi_ne_zero_right.mp hRH
    have hle : ρ.re ≤ 1 / 2 := by
      by_contra h
      exact hright ρ (lt_of_not_ge h) hzero
    have hge : 1 / 2 ≤ ρ.re := by
      by_contra h
      have href : 1 / 2 < (1 - ρ).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hzref : xi (1 - ρ) = 0 := by rw [xi_one_sub, hzero]
      exact hright (1 - ρ) href hzref
    linarith
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hright hzero
    have hright' : 1 / 2 < ρ.re := mem_rightHalf.mp hright
    have hline := (completedFluxGradedRealAt_iff ρ).mp (h ρ hzero)
    linarith

/-- **Fixed-source RH interface.** RH is equivalent to graded reality, at every strip zero, of the
single order-independent coefficient sequence obtained by adding the continued Euler-prime and
archimedean/boundary germs.  Proving the right side directly from the source remains the open
constraint theorem; this equivalence does not supply that proof. -/
theorem rh_iff_forall_strip_zero_completedFluxSourceGradedRealAt :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → xi ρ = 0 →
        CompletedFluxSourceGradedRealAt ρ := by
  constructor
  · intro hRH ρ h0 h1 hzero
    have hgraded := (rh_iff_forall_zero_completedFluxGradedRealAt.mp hRH) ρ hzero
    have hline := (completedFluxGradedRealAt_iff ρ).mp hgraded
    exact (completedFluxSourceGradedRealAt_iff ⟨h0, h1⟩).mpr hline
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hright hzero
    have hright' : 1 / 2 < ρ.re := mem_rightHalf.mp hright
    by_cases h1 : ρ.re < 1
    · have hsource := h ρ (by linarith) h1 hzero
      have hline := (completedFluxSourceGradedRealAt_iff
        (ρ := ρ) ⟨by linarith, h1⟩).mp hsource
      linarith
    · exact absurd hzero (xi_ne_zero_of_one_le_re (not_lt.mp h1))

end

end RHTower
