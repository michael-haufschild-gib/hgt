import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure

/-!
# From a local algebraic differential equation to a global one

A differential relation for an analytic function is itself analytic, so it propagates from any
nonempty open subset to the whole connected domain by the identity theorem.  When the domain is
the complement of a single point — the situation for a function with one pole — multiplying the
relation by `(s − p)` extends it across the missing point, upgrading local differential
algebraicity to the global notion.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ## Analyticity of a jet relation -/

/-- The evaluation of a differential polynomial on the jets of an analytic function is analytic. -/
theorem analyticAt_jetEval {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval
      (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) P) z := by
  have hfz : AnalyticAt ℂ f z := hf z hz
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) (P + Q)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) P +
            MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) (P * MvPolynomial.X i)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) P *
            (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w) : Fin (n + 2) → ℂ) i := by
        funext w
        simp
      rw [heq]
      refine hP.mul ?_
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          exact analyticAt_id
      | succ j =>
          simp only [Fin.cons_succ]
          exact analyticAt_iteratedDeriv_of_analyticAt hfz (j : ℕ)

/-! ## Propagation across a connected domain -/

/-- **A local differential relation propagates.**  A relation valid on a nonempty open subset of a
preconnected domain of analyticity is valid on the whole domain. -/
theorem differentiallyAlgebraicOn_mono_of_isPreconnected {f : ℂ → ℂ} {U V : Set ℂ}
    (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hVo : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    (hDA : DifferentiallyAlgebraicOn f V) : DifferentiallyAlgebraicOn f U := by
  obtain ⟨n, P, hP0, hPv⟩ := hDA
  refine ⟨n, P, hP0, ?_⟩
  obtain ⟨z₀, hz₀V⟩ := hVne
  set E : ℂ → ℂ := fun z => MvPolynomial.eval
    (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P with hE
  have han : AnalyticOnNhd ℂ E U := fun z hz => analyticAt_jetEval hf n P hz
  letI : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in nhds z₀, E z = 0 := by
    filter_upwards [hVo.mem_nhds hz₀V] with z hz
    exact hPv z hz
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc (hVU hz₀V) hfreq

/-! ## Crossing a single missing point -/

theorem isPreconnected_compl_singleton (p : ℂ) : IsPreconnected ({p}ᶜ : Set ℂ) := by
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_
    (Set.countable_singleton p)).isConnected.isPreconnected
  rw [Complex.rank_real_complex]
  norm_num

/-- **Local differential algebraicity off one point is global differential algebraicity.**
Multiplying the propagated relation by `(s − p)` extends it across the missing point. -/
theorem differentiallyAlgebraic_of_on_compl_singleton {f : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticOnNhd ℂ f ({p}ᶜ : Set ℂ)) {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVU : V ⊆ ({p}ᶜ : Set ℂ)) (hDA : DifferentiallyAlgebraicOn f V) :
    DifferentiallyAlgebraic f := by
  obtain ⟨n, P, hP0, hPv⟩ := differentiallyAlgebraicOn_mono_of_isPreconnected
    (isPreconnected_compl_singleton p) hf hVo hVne hVU hDA
  refine ⟨n, (X 0 - C p) * P, ?_, ?_⟩
  · refine mul_ne_zero ?_ hP0
    intro h0
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin (n + 2)) 1)) h0
    have hne : ¬ ((0 : Fin (n + 2) →₀ ℕ) = Finsupp.single (0 : Fin (n + 2)) 1) := by
      intro h
      have h1 := congrArg (fun t => t (0 : Fin (n + 2))) h
      simp at h1
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_C, if_neg hne] at hcoeff
    simp at hcoeff
  · intro z
    rw [map_mul, map_sub, eval_X, eval_C, Fin.cons_zero]
    by_cases hz : z = p
    · rw [hz, sub_self, zero_mul]
    · rw [hPv z (by simpa using hz), mul_zero]

end

end GaloisForLFunctions.HTGeometry
