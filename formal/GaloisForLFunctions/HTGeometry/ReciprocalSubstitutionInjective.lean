import GaloisForLFunctions.HTGeometry.ReciprocalSubstitution
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets

/-!
# The reciprocal substitution kills nothing

The substitution `yⱼ ↦ Aⱼ/g^{j+1}` is tested on the digamma pair `ψ`, `1/ψ`: on the open set where
`ψ` is analytic and nonzero the substituted polynomial evaluates to `P(s, ψ, ψ′, …)·ψ^{-E}`, so a
vanishing substitution forces a differential relation for `ψ` there, which propagates off the poles
by the identity theorem and is then killed by Hölder's theorem.  Hence

`recipSub n P = 0 → P = 0`,

which is the missing half of the reciprocal closure of differential algebraicity.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ## Jets of an analytic function on an open set -/

theorem hasDerivAt_iteratedDeriv_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f z) z := by
  have h := (analyticOnNhd_iteratedDeriv hf k z hz).differentiableAt
  rw [iteratedDeriv_succ]
  exact h.hasDerivAt

/-! ## The regular and unit loci of digamma -/

/-- The complement of the pole set `−ℕ` of `ψ`. -/
def digammaOffPoles : Set ℂ := {z : ℂ | ∀ p : ℕ, z ≠ -(p : ℂ)}

theorem isOpen_digammaOffPoles : IsOpen digammaOffPoles := offPoles_isOpen

theorem isPreconnected_digammaOffPoles : IsPreconnected digammaOffPoles :=
  offPoles_isPreconnected

theorem analyticOnNhd_digamma_offPoles :
    AnalyticOnNhd ℂ Complex.digamma digammaOffPoles :=
  fun _ hz => analyticAt_digamma_of_offPoles hz

/-- The open set where `ψ` is analytic and invertible. -/
def digammaUnitSet : Set ℂ := {z : ℂ | (∀ p : ℕ, z ≠ -(p : ℂ)) ∧ Complex.digamma z ≠ 0}

theorem digammaUnitSet_subset : digammaUnitSet ⊆ digammaOffPoles := fun _ hz => hz.1

theorem isOpen_digammaUnitSet : IsOpen digammaUnitSet := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hpol : {w : ℂ | ∀ p : ℕ, w ≠ -(p : ℂ)} ∈ nhds z :=
    offPoles_isOpen.mem_nhds hz.1
  have hcont := (analyticAt_digamma_of_offPoles hz.1).continuousAt
  have hne : {w : ℂ | Complex.digamma w ≠ 0} ∈ nhds z := hcont.eventually_ne hz.2
  exact Filter.inter_mem hpol hne

/-- `ψ` is not identically zero off its poles, so its unit locus is nonempty. -/
theorem digammaUnitSet_nonempty : digammaUnitSet.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hzero : ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) → Complex.digamma z = 0 := by
    intro z hz
    by_contra h0
    have : z ∈ digammaUnitSet := ⟨hz, h0⟩
    rw [hempty] at this
    exact this
  have hP : (X (Fin.succ (0 : Fin 1)) : MvPolynomial (Fin 2) ℂ) = 0 := by
    refine digamma_jet_annihilator_eq_zero 0 _ ?_
    intro z hz
    rw [eval_X, Fin.cons_succ]
    simpa using hzero z hz
  have hne : (X (Fin.succ (0 : Fin 1)) : MvPolynomial (Fin 2) ℂ) ≠ 0 := X_ne_zero _
  exact hne hP

/-! ## Analyticity of the digamma jet evaluation -/

theorem analyticAt_digammaJetEval (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ}
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval
      (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w)) P) z := by
  have hf : AnalyticAt ℂ Complex.digamma z := analyticAt_digamma_of_offPoles hz
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w)) (P + Q)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w)) P +
            MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w)) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w))
            (P * MvPolynomial.X i)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w)) P *
            (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma w) :
              Fin (n + 2) → ℂ) i := by
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
          exact analyticAt_iteratedDeriv_of_analyticAt hf (j : ℕ)

/-! ## Propagation of a local digamma relation -/

theorem digamma_relation_propagates {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty) (hVreg : V ⊆ digammaOffPoles)
    (hrel : ∀ z ∈ V, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma z)) P = 0) :
    ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) → MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma z)) P = 0 := by
  let E : ℂ → ℂ := fun z => MvPolynomial.eval
    (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma z)) P
  obtain ⟨z₀, hz₀V⟩ := hVne
  have hz₀reg : z₀ ∈ digammaOffPoles := hVreg hz₀V
  have han : AnalyticOnNhd ℂ E digammaOffPoles := fun z hz => analyticAt_digammaJetEval n P hz
  letI : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in nhds z₀, E z = 0 := by
    filter_upwards [hVopen.mem_nhds hz₀V] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_digammaOffPoles hz₀reg hfreq
  intro z hz
  exact hEq (show z ∈ digammaOffPoles from hz)

/-! ## Injectivity of the reciprocal substitution -/

/-- **The reciprocal substitution is injective on differential polynomials.**  Testing on the pair
`ψ`, `1/ψ` turns a vanishing substitution into a differential relation for the digamma function,
which Hölder's theorem forbids. -/
theorem recipSub_eq_zero_iff (n : ℕ) {P : MvPolynomial (Fin (n + 2)) ℂ}
    (h : recipSub n P = 0) : P = 0 := by
  set ψ : ℂ → ℂ := Complex.digamma with hψ
  set g : ℂ → ℂ := fun w => (Complex.digamma w)⁻¹ with hg
  have hUopen : IsOpen digammaUnitSet := isOpen_digammaUnitSet
  have hψan : AnalyticOnNhd ℂ ψ digammaUnitSet := fun z hz =>
    analyticAt_digamma_of_offPoles hz.1
  have hgan : AnalyticOnNhd ℂ g digammaUnitSet := fun z hz =>
    (analyticAt_digamma_of_offPoles hz.1).inv hz.2
  have hrel : ∀ z ∈ digammaUnitSet, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) ψ z)) P = 0 := by
    intro z hz
    have hev := eval_recipSub n (g := g) (f := ψ) (U := digammaUnitSet) hUopen
      (fun k w hw => hasDerivAt_iteratedDeriv_of_analyticOnNhd hgan k hw)
      (fun k w hw => hasDerivAt_iteratedDeriv_of_analyticOnNhd hψan k hw)
      (fun w hw => mul_inv_cancel₀ hw.2) P hz
    rw [h] at hev
    simp only [map_zero] at hev
    have hgz : g z ≠ 0 := inv_ne_zero hz.2
    have hpow : g z ^ recipBound n P ≠ 0 := pow_ne_zero _ hgz
    exact (mul_eq_zero.mp hev.symm).resolve_right hpow
  refine digamma_jet_annihilator_eq_zero n P ?_
  exact digamma_relation_propagates hUopen digammaUnitSet_nonempty digammaUnitSet_subset hrel

/-! ## Reciprocal closure of differential algebraicity -/

/-- **Differential algebraicity is closed under reciprocals.**  If `f·g = 1` with both factors
analytic on an open set and `f` satisfies an algebraic differential equation there, then so does
`g`: substitute the reciprocal jet formula and clear the single denominator.  The substituted
polynomial is nonzero by `recipSub_eq_zero_iff`. -/
theorem differentiallyAlgebraicOn_of_mul_eq_one {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfan : AnalyticOnNhd ℂ f U) (hgan : AnalyticOnNhd ℂ g U)
    (hinv : ∀ z ∈ U, f z * g z = 1) (hDA : DifferentiallyAlgebraicOn f U) :
    DifferentiallyAlgebraicOn g U := by
  obtain ⟨n, P, hP0, hPv⟩ := hDA
  refine ⟨n + 1, recipSub n P, fun h0 => hP0 (recipSub_eq_zero_iff n h0), ?_⟩
  intro z hz
  have hev := eval_recipSub n (g := g) (f := f) (U := U) hU
    (fun k w hw => hasDerivAt_iteratedDeriv_of_analyticOnNhd hgan k hw)
    (fun k w hw => hasDerivAt_iteratedDeriv_of_analyticOnNhd hfan k hw)
    hinv P hz
  rw [hev, hPv z hz, zero_mul]

/-- **Differential algebraicity is closed under inverses of nonvanishing analytic functions.** -/
theorem differentiallyAlgebraicOn_inv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfan : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0)
    (hDA : DifferentiallyAlgebraicOn f U) :
    DifferentiallyAlgebraicOn (fun z => (f z)⁻¹) U :=
  differentiallyAlgebraicOn_of_mul_eq_one hU hfan (fun z hz => (hfan z hz).inv (hne z hz))
    (fun z hz => mul_inv_cancel₀ (hne z hz)) hDA

/-- **Hypertranscendence transfers to the reciprocal.**  If the reciprocal of a nonvanishing
analytic function satisfies no algebraic differential equation on an open set, neither does the
function itself. -/
theorem not_differentiallyAlgebraicOn_of_inv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfan : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0)
    (hinvDA : ¬ DifferentiallyAlgebraicOn (fun z => (f z)⁻¹) U) :
    ¬ DifferentiallyAlgebraicOn f U :=
  fun hDA => hinvDA (differentiallyAlgebraicOn_inv hU hfan hne hDA)

/-- **Reciprocal closure, global form.**  The reciprocal of a nonvanishing entire differentially
algebraic function is differentially algebraic. -/
theorem differentiallyAlgebraic_inv {f : ℂ → ℂ} (hfan : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∀ z : ℂ, f z ≠ 0) (hDA : DifferentiallyAlgebraic f) :
    DifferentiallyAlgebraic (fun z => (f z)⁻¹) := by
  obtain ⟨n, P, hP0, hPv⟩ := hDA
  have hDAon : DifferentiallyAlgebraicOn f Set.univ := ⟨n, P, hP0, fun z _ => hPv z⟩
  obtain ⟨m, Q, hQ0, hQv⟩ :=
    differentiallyAlgebraicOn_inv isOpen_univ hfan (fun z _ => hne z) hDAon
  exact ⟨m, Q, hQ0, fun z => hQv z (Set.mem_univ z)⟩

end

end GaloisForLFunctions.HTGeometry
