import GaloisForLFunctions.HTGeometry.IntegerMonomialIndependence
import GaloisForLFunctions.HTGeometry.TranslateJetGenericity

/-!
# Translated jets with vanishing companions

At a translated zero the distinguished jet blows up and the companions take finite values.  Those
values may be zero, and the earlier data demanded they were not — a hypothesis that cannot be
established, and is genuinely false for some derivatives of the log-derivative.

With integer rates the demand disappears.  A companion vanishing to order `V` at the sampled point
simply has rate `−V`, supplied by the order-`V` factorization of its analytic germ.  What replaces
"the companion does not vanish" is "the companion has a known analytic order", which every nonzero
analytic germ has.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The integer rate vector: blow-up in the distinguished coordinate, minus the vanishing order in
the others. -/
noncomputable def integerTranslateJetRate {n : ℕ} (m : Fin n → ℕ) (k₀ : Fin n) (V : Fin n → ℕ) :
    Fin n → ℤ :=
  fun k => if k = k₀ then ((m k₀ : ℤ) + 1) else -(V k : ℤ)

/-- The vertical approach to a point, staying inside any set that contains an initial segment of the
vertical ray above it. -/
theorem exists_verticalApproach {S : Set ℂ} {ζ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hS : ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S) :
    ∃ u : ℕ → ℂ, (∀ j, u j ∈ S) ∧ (∀ j, u j ≠ ζ) ∧ (∀ j, 0 < (u j - ζ).im) ∧
      Tendsto u atTop (𝓝 ζ) ∧ Tendsto (fun j => u j - ζ) atTop (𝓝 0) := by
  classical
  set tr : ℕ → ℝ := fun j => (ε / 2) * (1 / ((j : ℝ) + 1)) with htr
  have htrpos : ∀ j, 0 < tr j := by
    intro j
    rw [htr]
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    positivity
  have htrlt : ∀ j, tr j < ε := by
    intro j
    have hle : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have : tr j ≤ ε / 2 := by
      rw [htr]
      nlinarith
    linarith
  have htr0 : Tendsto tr atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (ε / 2)
    simpa [htr] using h
  set u : ℕ → ℂ := fun j => ζ + ((tr j : ℝ) : ℂ) * Complex.I with hu
  have hulim : Tendsto u atTop (𝓝 ζ) := by
    have hc : Tendsto (fun j => ((tr j : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp htr0
    have hmul : Tendsto (fun j => ((tr j : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
      simpa using hc.mul_const Complex.I
    simpa [hu] using tendsto_const_nhds.add hmul
  have hdiff : ∀ j, u j - ζ = ((tr j : ℝ) : ℂ) * Complex.I := by
    intro j
    rw [hu]
    ring
  have huim : ∀ j, 0 < (u j - ζ).im := by
    intro j
    rw [hdiff j]
    simpa using htrpos j
  refine ⟨u, fun j => hS (tr j) (htrpos j) (htrlt j), ?_, huim, hulim, ?_⟩
  · intro j hcon
    have h0 : (u j - ζ).im = 0 := by rw [hcon]; simp
    exact absurd h0 (ne_of_gt (huim j))
  · have h := hulim.sub (tendsto_const_nhds (x := ζ))
    simpa using h

set_option maxHeartbeats 1000000 in
/-- **The blow-up datum at one translated zero.**  Approaching the zero vertically, the distinguished
jet blows up at rate `m k₀ + 1` with the factorial leading value, and every companion is renormalized
by its own vanishing order there. -/
theorem exists_translateJetBlowUp_at {n : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    {S : Set ℂ} {ζ : ℂ}
    (hS : ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hV : ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞)) :
    ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (c : Fin n → ℂ),
      (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
        (∀ k, c k ≠ 0) ∧
        ∀ k, Tendsto (fun j =>
            iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (u j + σ k) *
              t j ^ (integerTranslateJetRate m k₀ V k)) atTop (𝓝 (c k)) := by
  classical
  obtain ⟨p, hp⟩ := hzero
  obtain ⟨u, humem, hune, huim, hulim, htlim⟩ :=
    exists_verticalApproach (ε := 1) one_pos (fun y hy _ => hS y hy)
  have htne : ∀ j, u j - ζ ≠ 0 := fun j => sub_ne_zero.mpr (hune j)
  have hzeroim : (ζ + σ k₀).im = 0 := by
    rw [hp]
    simp
  have hupper : ∀ j, 0 < (u j + σ k₀).im := by
    intro j
    have h1 : (u j + σ k₀).im = (u j - ζ).im + (ζ + σ k₀).im := by
      simp only [Complex.add_im, Complex.sub_im]
      ring
    rw [h1, hzeroim, add_zero]
    exact huim j
  have hcomp : ∀ k, k ≠ k₀ → ∃ C : ℂ, C ≠ 0 ∧
      Tendsto (fun j => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (u j + σ k) *
        (u j - ζ) ^ (-(V k : ℤ))) atTop (𝓝 C) :=
    fun k hk => exists_tendsto_zpow_neg_of_analyticOrderAt (hfin k hk) (hV k hk) hulim hune
  refine ⟨u, fun j => u j - ζ,
    fun k => if hk : k = k₀ then -((-1 : ℂ) ^ (m k₀) * ((m k₀).factorial : ℂ))
      else (hcomp k hk).choose,
    humem, htne, hulim, htlim, ?_, ?_⟩
  · intro k
    dsimp only
    by_cases hk : k = k₀
    · rw [dif_pos hk]
      exact jetLeadingValue_ne_zero _
    · rw [dif_neg hk]
      exact (hcomp k hk).choose_spec.1
  · intro k
    dsimp only
    by_cases hk : k = k₀
    · subst hk
      rw [dif_pos rfl]
      have hrate : integerTranslateJetRate m k V k = ((m k + 1 : ℕ) : ℤ) := by
        rw [integerTranslateJetRate, if_pos rfl]
        push_cast
        ring
      rw [hrate]
      have hbase := tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative θ p (m k) (σ k)
        hupper (by rw [← hp]; exact hulim)
      refine hbase.congr fun j => ?_
      rw [zpow_natCast, hp]
    · rw [dif_neg hk]
      have hrate : integerTranslateJetRate m k₀ V k = -(V k : ℤ) := by
        rw [integerTranslateJetRate, if_neg hk]
      rw [hrate]
      exact (hcomp k hk).choose_spec.2

/-- **Blow-up data for translated jets, with companions allowed to vanish.** -/
theorem integerMultiBlowUpData_translateJets {n : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    {S Z : Set ℂ} (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hV : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞)) :
    IntegerMultiBlowUpData S
      (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) Z
      (integerTranslateJetRate m k₀ V) :=
  ⟨hZ, fun ζ hζ =>
    exists_translateJetBlowUp_at θ m σ k₀ V (hS ζ hζ) (hzero ζ hζ) (hfin ζ hζ) (hV ζ hζ)⟩

/-- **The translated jet box, with vanishing companions.**  Separation is now injectivity of the
integer order form, which sees the companions' vanishing orders. -/
theorem linearIndependent_restrict_expandedMonomialFamily_integerTranslateJets
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    {S Z : Set ℂ} (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hV : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞))
    {exponent : κ → (Fin n →₀ ℕ)}
    (hsep : Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetRate m k₀ V) (exponent a)) :
    LinearIndependent ℂ (fun c : κ × Fin (q + 1) =>
      Set.restrict S (expandedMonomialFamily
        (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k))
        exponent q c)) :=
  linearIndependent_restrict_expandedMonomialFamily_of_integerMultiBlowUp
    (integerMultiBlowUpData_translateJets θ m σ k₀ V hZ hS hzero hfin hV) hsep

end GaloisForLFunctions.HTGeometry
