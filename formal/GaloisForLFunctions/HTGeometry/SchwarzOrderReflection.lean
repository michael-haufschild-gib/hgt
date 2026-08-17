import GaloisForLFunctions.HTGeometry.AnalyticConjReflection
import GaloisForLFunctions.RHTower.GelfondSchneiderProof.AnalyticPart

/-!
# Schwarz reflection preserves the analytic order

A Schwarz-real entire function `F(conj z) = conj (F z)` has the same vanishing order at a point and
at its conjugate (`analyticOrderAt_conj`).  Equivalently its zero divisor is stable under
conjugation *with multiplicity* — the fact that makes the finite zero product on a disc centred on
the real axis itself Schwarz-real, and hence makes the zero-free cofactor of a boundary
factorization Schwarz-real too.

The proof goes through the jets: `iteratedDeriv_conj_of_schwarz` shows every jet of a Schwarz-real
function is Schwarz-equivariant, by induction on the order using mathlib's `deriv_conj_conj` (the
derivative of `conj ∘ f ∘ conj` is `conj ∘ deriv f ∘ conj`, which for a Schwarz-real `f` says
`deriv f` is Schwarz-real again).  The order comparison is then the jet characterization
`analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero` from the tree's Gelfond–Schneider analytic
layer, with the identically-vanishing case handled separately by `analyticOrderAt_eq_top`.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry


open GaloisForLFunctions.RHTower.GelfondSchneiderProof

/-- Every jet of a Schwarz-real function is Schwarz-equivariant. -/
theorem iteratedDeriv_conj_of_schwarz :
    ∀ (n : ℕ) {G : ℂ → ℂ},
      (∀ z : ℂ, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z)) →
      ∀ z : ℂ, iteratedDeriv n G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (iteratedDeriv n G z) := by
  intro n
  induction n with
  | zero => intro G hG z; simpa using hG z
  | succ n ih =>
      intro G hG z
      have hcomp : (starRingEnd ℂ) ∘ G ∘ (starRingEnd ℂ) = G := by
        funext u
        simp only [Function.comp_apply, hG u, Complex.conj_conj]
      have h := deriv_conj_conj (f := G)
      rw [hcomp] at h
      have hderiv : ∀ w : ℂ, deriv G ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv G w) := by
        intro w
        have hw := congrFun h w
        simp only [Function.comp_apply] at hw
        rw [hw, Complex.conj_conj]
      simp only [iteratedDeriv_succ']
      exact ih hderiv z

/-- **Schwarz reflection preserves the analytic order.** -/
theorem analyticOrderAt_conj {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
    (hFan : ∀ z : ℂ, AnalyticAt ℂ F z) (a : ℂ) :
    analyticOrderAt F ((starRingEnd ℂ) a) = analyticOrderAt F a := by
  have key : ∀ (G : ℂ → ℂ), (∀ z : ℂ, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z)) →
      (∀ z : ℂ, AnalyticAt ℂ G z) → ∀ b : ℂ,
        analyticOrderAt G b ≤ analyticOrderAt G ((starRingEnd ℂ) b) := by
    intro G hG hGan b
    rcases eq_or_ne (analyticOrderAt G ((starRingEnd ℂ) b)) ⊤ with htop | hfin
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
      rcases eq_or_ne (analyticOrderAt G b) ⊤ with htop' | hfin'
      · -- `G` vanishes near `b`, hence near `conj b`, contradicting finiteness there
        exfalso
        have hzero : ∀ᶠ z in 𝓝 b, G z = 0 := analyticOrderAt_eq_top.mp htop'
        have hmap : Filter.Tendsto (fun z : ℂ => (starRingEnd ℂ) z) (𝓝 ((starRingEnd ℂ) b))
            (𝓝 b) := by
          have hcont : Continuous (fun z : ℂ => (starRingEnd ℂ) z) := Complex.continuous_conj
          have hc := hcont.tendsto ((starRingEnd ℂ) b)
          simpa using hc
        have hzero' : ∀ᶠ z in 𝓝 ((starRingEnd ℂ) b), G z = 0 := by
          filter_upwards [hmap.eventually hzero] with z hz
          have hgz := hG z
          rw [hz] at hgz
          have : (starRingEnd ℂ) (G z) = 0 := hgz.symm
          simpa using this
        have := analyticOrderAt_eq_top.mpr hzero'
        rw [this] at hfin
        exact hfin rfl
      · -- both orders finite: compare jets
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin'
        rw [← hm, ← hn, Nat.cast_le]
        by_contra hcon
        push Not at hcon
        have hjets := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := n) G
          (hGan ((starRingEnd ℂ) b))).mpr hn.symm
        have hzero : ∀ k < m, deriv^[k] G b = 0 :=
          ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := m) G (hGan b)).mpr hm.symm).1
        have hconj : deriv^[n] G ((starRingEnd ℂ) b) = (starRingEnd ℂ) (deriv^[n] G b) := by
          have h := iteratedDeriv_conj_of_schwarz n hG b
          simp only [iteratedDeriv_eq_iterate] at h
          exact h
        have hnm : deriv^[n] G b = 0 := hzero n hcon
        rw [hnm, map_zero] at hconj
        exact hjets.2 hconj
  refine le_antisymm ?_ ?_
  · have h := key F hF hFan ((starRingEnd ℂ) a)
    simpa using h
  · exact key F hF hFan a


end GaloisForLFunctions.HTGeometry

end
