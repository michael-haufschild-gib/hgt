import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries
import GaloisForLFunctions.HTGeometry.MultivariateEntireCommMonoid
import GaloisForLFunctions.HTGeometry.MultivariateEntireCauchyEstimate
import GaloisForLFunctions.HTGeometry.MultivariateJetCompositionLaw

/-!
# Vanishing jets survive multiplication and translation

An entire source all of whose mixed jets up to order `n` vanish at a point keeps that property
after multiplication by any entire source: the Leibniz rule sends every ordered coordinate
derivative of the product to a sum of terms each of which still carries a derivative of the
vanishing factor of order at most `n`.  Translation moves the point.

Together these say that a Poincaré summand `x ↦ ψ(γ,x)⁻¹ · G(x + γ)` has vanishing jets at `p`
whenever `G` has vanishing jets at `p + γ` — the automorphy factor cannot resurrect a jet it did
not have.  That is what turns "prescribe zero jets at the translated packet points" into
"the complement Poincaré terms contribute nothing to the packet".

* `partialDerivEntire_mul`, `partialDerivEntire_translate`;
* `orderedPartialJetEvalCLM_translate`;
* `AllJetsVanish`, `AllJetsVanish.mono`, `AllJetsVanish.partialDeriv`;
* `AllJetsVanish.mul_left`, `AllJetsVanish.translate`, `allJetsVanish_poincareTermEntire`;
* `AllJetsVanish.multiIndexJet`, `multiIndexJetEvalCLM_poincareTermEntire_eq_zero`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d : ℕ}

/-- **Leibniz for a coordinate derivative of entire sources.** -/
theorem partialDerivEntire_mul (v : Fin d → ℂ) (f g : MultivariateEntire d) :
    partialDerivEntire v (f * g)
      = partialDerivEntire v f * g + f * partialDerivEntire v g := by
  ext x
  have h := ((differentiable_multivariateEntire f x).hasFDerivAt).mul
    ((differentiable_multivariateEntire g x).hasFDerivAt)
  show fderiv ℂ ((f.1 : (Fin d → ℂ) → ℂ) * (g.1 : (Fin d → ℂ) → ℂ)) x v
      = fderiv ℂ (f.1 : (Fin d → ℂ) → ℂ) x v * g.1 x
        + f.1 x * fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) x v
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- A coordinate derivative commutes with translation. -/
theorem partialDerivEntire_translate (v : Fin d → ℂ) (f : MultivariateEntire d)
    (y : Fin d → ℂ) :
    partialDerivEntire v (multivariateEntireTranslate f y)
      = multivariateEntireTranslate (partialDerivEntire v f) y := by
  ext x
  show fderiv ℂ (fun z => f.1 (z + y)) x v = fderiv ℂ (f.1 : (Fin d → ℂ) → ℂ) (x + y) v
  rw [fderiv_comp_add_right]

/-- Ordered mixed jets of a translate are the jets at the translated point. -/
theorem orderedPartialJetEvalCLM_translate :
    ∀ {n : ℕ} (x y : Fin d → ℂ) (word : Fin n → Fin d) (f : MultivariateEntire d),
      orderedPartialJetEvalCLM x word (multivariateEntireTranslate f y)
        = orderedPartialJetEvalCLM (x + y) word f
  | 0, x, y, word, f => by
      rw [orderedPartialJetEvalCLM_eq_wordPartialDerivEntire,
        orderedPartialJetEvalCLM_eq_wordPartialDerivEntire]
      rfl
  | (n + 1), x, y, word, f => by
      rw [orderedPartialJetEvalCLM_succ_right, orderedPartialJetEvalCLM_succ_right,
        partialDerivEntire_translate]
      exact orderedPartialJetEvalCLM_translate x y (Fin.init word) _

/-- Every ordered mixed jet of `f` at `p` up to order `n` vanishes. -/
def AllJetsVanish (n : ℕ) (p : Fin d → ℂ) (f : MultivariateEntire d) : Prop :=
  ∀ k, k ≤ n → ∀ word : Fin k → Fin d, orderedPartialJetEvalCLM p word f = 0

theorem AllJetsVanish.mono {n n' : ℕ} (h : n' ≤ n) {p : Fin d → ℂ} {f : MultivariateEntire d}
    (hf : AllJetsVanish n p f) : AllJetsVanish n' p f :=
  fun k hk word => hf k (le_trans hk h) word

theorem AllJetsVanish.value {n : ℕ} {p : Fin d → ℂ} {f : MultivariateEntire d}
    (hf : AllJetsVanish n p f) : f.1 p = 0 := by
  have h := hf 0 (Nat.zero_le n) (fun i => i.elim0)
  rwa [orderedPartialJetEvalCLM_eq_wordPartialDerivEntire] at h

/-- Differentiating drops the vanishing order by one. -/
theorem AllJetsVanish.partialDeriv {n : ℕ} {p : Fin d → ℂ} {f : MultivariateEntire d}
    (hf : AllJetsVanish (n + 1) p f) (i : Fin d) :
    AllJetsVanish n p (partialDerivEntire (coordinateJetDirection i) f) := by
  intro k hk word
  have hsnoc := orderedPartialJetEvalCLM_succ_right (n := k) p (Fin.snoc word i) f
  rw [Fin.init_snoc, Fin.snoc_last] at hsnoc
  rw [← hsnoc]
  exact hf (k + 1) (by omega) _

/-- **Vanishing jets are preserved by multiplication.** -/
theorem AllJetsVanish.mul_left :
    ∀ (n : ℕ) {p : Fin d → ℂ} (h : MultivariateEntire d) {f : MultivariateEntire d},
      AllJetsVanish n p f → AllJetsVanish n p (h * f)
  | 0, p, h, f, hf => by
      intro k hk word
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rw [orderedPartialJetEvalCLM_eq_wordPartialDerivEntire]
      show h.1 p * f.1 p = 0
      rw [hf.value, mul_zero]
  | (n + 1), p, h, f, hf => by
      intro k hk word
      match k, word with
      | 0, word =>
          rw [orderedPartialJetEvalCLM_eq_wordPartialDerivEntire]
          show h.1 p * f.1 p = 0
          rw [hf.value, mul_zero]
      | (j + 1), word =>
          rw [orderedPartialJetEvalCLM_succ_right, partialDerivEntire_mul, map_add]
          have hj : j ≤ n := by omega
          have h1 := AllJetsVanish.mul_left n
            (partialDerivEntire (coordinateJetDirection (word (Fin.last j))) h)
            (hf.mono (by omega)) j hj (Fin.init word)
          have h2 := AllJetsVanish.mul_left n h
            (hf.partialDeriv (word (Fin.last j))) j hj (Fin.init word)
          rw [h1, h2, add_zero]

theorem AllJetsVanish.mul_right {n : ℕ} {p : Fin d → ℂ} {f : MultivariateEntire d}
    (hf : AllJetsVanish n p f) (h : MultivariateEntire d) : AllJetsVanish n p (f * h) := by
  rw [mul_comm]
  exact AllJetsVanish.mul_left n h hf

/-- **Vanishing jets translate.** -/
theorem AllJetsVanish.translate {n : ℕ} {p y : Fin d → ℂ} {f : MultivariateEntire d}
    (hf : AllJetsVanish n (p + y) f) : AllJetsVanish n p (multivariateEntireTranslate f y) := by
  intro k hk word
  rw [orderedPartialJetEvalCLM_translate]
  exact hf k hk word

/-- **A Poincaré summand inherits the vanishing of its seed at the translated point.** -/
theorem allJetsVanish_poincareTermEntire {n : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) {seed : MultivariateEntire d} {p : Fin d → ℂ} (γ : Γ)
    (hseed : AllJetsVanish n (p + γ.1) seed) :
    AllJetsVanish n p (poincareTermEntire ψ seed γ) := by
  have hfac : poincareTermEntire ψ seed γ
      = automorphicFactorInverseEntire ψ γ * multivariateEntireTranslate seed γ.1 := by
    ext x
    rfl
  rw [hfac]
  exact AllJetsVanish.mul_left n _ hseed.translate

/-- A multi-index jet below the vanishing order vanishes. -/
theorem AllJetsVanish.multiIndexJet {n : ℕ} {p : Fin d → ℂ} {f : MultivariateEntire d}
    (hf : AllJetsVanish n p f) {a : Fin d →₀ ℕ} (ha : Finsupp.degree a ≤ n) :
    multiIndexJetEvalCLM p a f = 0 := by
  rw [multiIndexJetEvalCLM]
  refine hf _ ?_ _
  have hd := degree_wordMultiplicity (multiIndexWord a)
  rw [wordMultiplicity_multiIndexWord] at hd
  rw [← hd]
  exact ha

/-- **The complement Poincaré terms contribute nothing to the packet.**  A seed whose jets vanish
at the translated packet point contributes a zero packet jet, whatever the automorphy factor. -/
theorem multiIndexJetEvalCLM_poincareTermEntire_eq_zero {n : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) {seed : MultivariateEntire d} {p : Fin d → ℂ} (γ : Γ)
    (hseed : AllJetsVanish n (p + γ.1) seed) {a : Fin d →₀ ℕ} (ha : Finsupp.degree a ≤ n) :
    multiIndexJetEvalCLM p a (poincareTermEntire ψ seed γ) = 0 :=
  (allJetsVanish_poincareTermEntire ψ γ hseed).multiIndexJet ha

end

end GaloisForLFunctions.HTGeometry
