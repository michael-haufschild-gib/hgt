import GaloisForLFunctions.HTGeometry.FamilyJetChainRule
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets
import GaloisForLFunctions.HTGeometry.MeromorphicDifferentialField

/-!
# The jet polynomial ring realized by analytic functions

An analytic family on an open set realizes the full jet polynomial ring inside the ring of analytic
functions: a jet polynomial becomes the germ of its evaluation along the family.  The realization is
a ring homomorphism, it is injective exactly when the family is differentially independent, and it
carries the total jet derivation to differentiation.

Passing to the meromorphic fraction field turns this into a realization inside a differential field,
which is where linear independence of exponentials is proved.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem contDiffAt_of_analyticOnNhd {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w := fun w hw => (hf w hw).contDiffAt

/-- Evaluating a jet polynomial along an analytic family is analytic. -/
theorem analyticOnNhd_eval_fullJetVec {m : ℕ} {U : Set ℂ} {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U) (P : MvPolynomial (FullJetIndex m) ℂ) :
    AnalyticOnNhd ℂ (fun w => MvPolynomial.eval (fullJetVec sigma w) P) U := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact analyticOnNhd_const
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      rcases v with u | ⟨i, k⟩
      · simp only [fullJetVec_inl]
        exact hp.mul analyticOnNhd_id
      · simp only [fullJetVec_inr]
        exact hp.mul (analyticOnNhd_iteratedDeriv (hs i) k)

/-- **Independence localizes.**  For an analytic family on a connected domain, a differential
relation holding on a nonempty open subdomain holds on the whole domain, so independence on the
domain gives independence on every nonempty open subdomain. -/
theorem fullJet_independent_mono {m : ℕ} {U W : Set ℂ} (hUc : IsPreconnected U)
    {sigma : Fin m → ℂ → ℂ} (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U) (hWo : IsOpen W)
    (hWU : W ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ W)
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec sigma z) P = 0) → P = 0)
    (P : MvPolynomial (FullJetIndex m) ℂ)
    (hP : ∀ z ∈ W, MvPolynomial.eval (fullJetVec sigma z) P = 0) : P = 0 := by
  refine hind P fun z hz => ?_
  have hana : AnalyticOnNhd ℂ (fun w => MvPolynomial.eval (fullJetVec sigma w) P) U :=
    analyticOnNhd_eval_fullJetVec hs P
  have hev : (fun w => MvPolynomial.eval (fullJetVec sigma w) P) =ᶠ[nhds z₀] 0 := by
    filter_upwards [hWo.mem_nhds hz₀] with w hw using hP w hw
  exact hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc (hWU hz₀) hev hz

/-- Two analytic germs with representatives agreeing on the domain are equal. -/
theorem analyticSubring_eq_of_eqOn {U : Set ℂ} {a b : Bottcher.analyticSubring U} {f h : ℂ → ℂ}
    (ha : (a : Germ (𝓟 U) ℂ) = (f : Germ (𝓟 U) ℂ))
    (hb : (b : Germ (𝓟 U) ℂ) = (h : Germ (𝓟 U) ℂ))
    (heq : ∀ z ∈ U, f z = h z) : a = b := by
  apply Subtype.ext
  rw [ha, hb, Germ.coe_eq]
  exact eventually_principal.mpr heq

theorem analyticSubring_coe_mul {U : Set ℂ} {a b : Bottcher.analyticSubring U} {f h : ℂ → ℂ}
    (ha : (a : Germ (𝓟 U) ℂ) = (f : Germ (𝓟 U) ℂ))
    (hb : (b : Germ (𝓟 U) ℂ) = (h : Germ (𝓟 U) ℂ)) :
    ((a * b : Bottcher.analyticSubring U) : Germ (𝓟 U) ℂ)
      = ((fun w => f w * h w : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
  rw [MulMemClass.coe_mul, ha, hb, ← Germ.coe_mul]
  rfl

/-- The analytic germ of a function analytic on the domain. -/
def analyticFunGerm {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    Bottcher.analyticSubring U := ⟨(f : Germ (𝓟 U) ℂ), ⟨f, hf, rfl⟩⟩

@[simp] theorem analyticFunGerm_coe {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ((analyticFunGerm hf : Bottcher.analyticSubring U) : Germ (𝓟 U) ℂ)
      = (f : Germ (𝓟 U) ℂ) := rfl

/-- **The jet realization.**  A jet polynomial becomes the germ of its evaluation along the family. -/
def jetAnalyticHom {m : ℕ} {U : Set ℂ} {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U) :
    MvPolynomial (FullJetIndex m) ℂ →+* Bottcher.analyticSubring U :=
  ((Germ.coeRingHom (𝓟 U)).comp
      (RingHom.pi fun w : ℂ => (MvPolynomial.eval (fullJetVec sigma w)))).codRestrict
    (Bottcher.analyticSubring U)
    (fun P => ⟨fun w => MvPolynomial.eval (fullJetVec sigma w) P,
      analyticOnNhd_eval_fullJetVec hs P, rfl⟩)

@[simp] theorem jetAnalyticHom_coe {m : ℕ} {U : Set ℂ} {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U) (P : MvPolynomial (FullJetIndex m) ℂ) :
    ((jetAnalyticHom hs P : Bottcher.analyticSubring U) : Germ (𝓟 U) ℂ)
      = ((fun w => MvPolynomial.eval (fullJetVec sigma w) P : ℂ → ℂ) : Germ (𝓟 U) ℂ) := rfl

/-- **The realization is injective exactly for a differentially independent family.** -/
theorem jetAnalyticHom_injective {m : ℕ} {U : Set ℂ} {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U)
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec sigma z) P = 0) → P = 0) :
    Function.Injective (jetAnalyticHom hs) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine hind P fun z hz => ?_
  have hval := congrArg Subtype.val hP
  rw [jetAnalyticHom_coe, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq] at hval
  exact eventually_principal.mp hval z hz

/-- **The realization is differential.**  It carries the total jet derivation to differentiation. -/
theorem analyticSubringDeriv_jetAnalyticHom {m : ℕ} {U : Set ℂ} (hUo : IsOpen U)
    {sigma : Fin m → ℂ → ℂ} (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U)
    (P : MvPolynomial (FullJetIndex m) ℂ) :
    analyticSubringDeriv hUo (jetAnalyticHom hs P)
      = jetAnalyticHom hs (fullJetDerivation m P) := by
  apply Subtype.ext
  rw [analyticSubringDeriv_coe, jetAnalyticHom_coe, analyticGermDeriv_coe, jetAnalyticHom_coe,
    Germ.coe_eq]
  refine eventually_principal.mpr fun z hz => ?_
  exact deriv_eval_fullJetVec hUo (fun i => contDiffAt_of_analyticOnNhd (hs i)) hz P

end

end GaloisForLFunctions.HTGeometry
