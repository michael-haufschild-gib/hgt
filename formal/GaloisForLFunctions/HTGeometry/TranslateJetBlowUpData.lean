import GaloisForLFunctions.HTGeometry.IteratedPoleResidue

/-!
# Blow-up data for a family of translated jets

At a translated zero `ζ = ζ_p − σ k₀` exactly one member of the family
`w ↦ L^{(m k)}(w + σ k)` blows up: the one carrying the shift `σ k₀`.  The others take finite values
there, which depend on which zero was approached — so the leading values are *not* independent of the
point.  Only the **orders** are, and that is all the graded law asks for.

The rate vector is therefore `m k₀ + 1` in the distinguished coordinate and zero elsewhere, and the
order of a monomial is `e_{a,k₀} · (m k₀ + 1)`.  The box is decided precisely when the exponent
family separates in that one coordinate.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The rate vector of a translated jet family at the zeros of one shift. -/
noncomputable def translateJetRate {n : ℕ} (m : Fin n → ℕ) (k₀ : Fin n) : Fin n → ℕ :=
  fun k => if k = k₀ then m k₀ + 1 else 0

/-- The blow-up order of a monomial is its exponent in the distinguished coordinate, scaled. -/
theorem blowUpOrder_translateJetRate {n : ℕ} (m : Fin n → ℕ) (k₀ : Fin n) (e : Fin n →₀ ℕ) :
    blowUpOrder (translateJetRate m k₀) e = e k₀ * (m k₀ + 1) := by
  classical
  rw [blowUpOrder, Finsupp.sum]
  by_cases hk : k₀ ∈ e.support
  · rw [Finset.sum_eq_single k₀]
    · rw [translateJetRate, if_pos rfl]
    · intro b _ hb
      rw [translateJetRate, if_neg hb, mul_zero]
    · intro hcon
      exact absurd hk hcon
  · have hz : e k₀ = 0 := by
      by_contra hne
      exact hk (Finsupp.mem_support_iff.mpr hne)
    rw [hz, zero_mul]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbk : b ≠ k₀ := by
      intro hcon
      exact hk (hcon ▸ hb)
    rw [translateJetRate, if_neg hbk, mul_zero]

/-- **The translated jet family has blow-up data at the zeros of one shift.**  The distinguished jet
blows up at rate `m k₀ + 1` with the universal leading value; the others converge to their values at
the point, which are assumed finite and nonzero. -/
theorem multiBlowUpData_translateJets {n : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) {S Z : Set ℂ} (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hne : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (ζ + σ k) ≠ 0) :
    MultiBlowUpData S
      (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) Z
      (translateJetRate m k₀) := by
  refine ⟨hZ, ?_⟩
  intro ζ hζ
  obtain ⟨p, hp⟩ := hzero ζ hζ
  set tr : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with htr
  set u : ℕ → ℂ := fun j => ζ + ((tr j : ℝ) : ℂ) * Complex.I with hu
  have htr0 : Tendsto tr atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hulim : Tendsto u atTop (𝓝 ζ) := by
    have hc : Tendsto (fun j => ((tr j : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp htr0
    have hmul : Tendsto (fun j => ((tr j : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
      simpa using hc.mul_const Complex.I
    simpa [hu] using tendsto_const_nhds.add hmul
  have hupper : ∀ j, 0 < (u j + σ k₀).im := by
    intro j
    have heq : u j + σ k₀ = (movingCanonicalZero θ p : ℂ) + ((tr j : ℝ) : ℂ) * Complex.I := by
      rw [hu, hp]
      ring
    rw [heq]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    rw [htr]
    positivity
  have htlim : Tendsto (fun j => u j - ζ) atTop (𝓝 0) := by
    have := hulim.sub (tendsto_const_nhds (x := ζ))
    simpa using this
  refine ⟨u, fun j => u j - ζ,
    fun k => if k = k₀ then -((-1 : ℂ) ^ (m k₀) * ((m k₀).factorial : ℂ))
      else iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (ζ + σ k),
    fun j => hS ζ hζ (tr j) (by rw [htr]; positivity), hulim, htlim, ?_, ?_⟩
  · intro k
    dsimp only
    by_cases hk : k = k₀
    · rw [if_pos hk]
      exact jetLeadingValue_ne_zero _
    · rw [if_neg hk]
      exact hne ζ hζ k hk
  · intro k
    dsimp only
    simp only [translateJetRate]
    by_cases hk : k = k₀
    · subst hk
      rw [if_pos rfl, if_pos rfl]
      have hbase := tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative θ p (m k) (σ k)
        hupper (by rw [← hp]; exact hulim)
      refine hbase.congr fun j => ?_
      rw [hp]
    · rw [if_neg hk, if_neg hk]
      simp only [pow_zero, mul_one]
      exact ((hfin ζ hζ k hk).continuousAt.tendsto).comp hulim

/-- **The translated jet box is decided by exponent separation in one coordinate.** -/
theorem linearIndependent_restrict_expandedMonomialFamily_translateJets
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) {S Z : Set ℂ} (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hne : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (ζ + σ k) ≠ 0)
    {exponent : κ → (Fin n →₀ ℕ)}
    (hsep : Function.Injective fun a => exponent a k₀) :
    LinearIndependent ℂ (fun c : κ × Fin (q + 1) =>
      Set.restrict S (expandedMonomialFamily
        (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k))
        exponent q c)) := by
  refine linearIndependent_restrict_expandedMonomialFamily_of_multiBlowUp
    (multiBlowUpData_translateJets θ m σ k₀ hZ hS hzero hfin hne) ?_
  intro a b hab
  simp only [blowUpOrder_translateJetRate] at hab
  exact hsep (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hab)

end GaloisForLFunctions.HTGeometry
