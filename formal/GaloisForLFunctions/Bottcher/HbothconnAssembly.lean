/-
# hbothconn from exactly two named Props: HoleFreeTip and SmoothPieceRigidity

The both-connected case of q62, reduced to its two remaining inputs.  `SmoothPieceRigidity` is the
P6 interface: a relatively open piece of `J_{c₁}` inside the modulus-one locus of one branch of a
separable analytic-coefficient root family is impossible (the classical smooth-piece Julia
rigidity, to be discharged by the Montel/Fatou epic).  Together with a `HoleFreeTip` (open
problem 04, answered on paper for `−3/4 < c₂ < c₁ < 0`; collar epic pending), it yields
`NoRelation` for the pair — the `hbothconn` input of `q62_phiMero_independence_conditional`.
The degenerate degree-`0` relation dies on the germ bridge: its lone coefficient function
vanishes on `U` while its analytic-ring element is nonzero.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.TipSmoothPiece
import GaloisForLFunctions.Bottcher.RelativeTranscendenceBridge

open Polynomial Set Metric Bornology Filter Topology

namespace Bottcher

/-- **The smooth-piece rigidity interface (P6).**  For nonexceptional parameters, no relatively
open piece of `J_{c₁}` lies inside the modulus-one locus of one branch of a continuous root family
of a separable analytic-coefficient fibre polynomial.  The full branch-family data is carried so
the discharge can upgrade continuity to analyticity via the implicit function theorem. -/
def SmoothPieceRigidity (c₁ c₂ : ℂ) : Prop :=
  ∀ (a : ℕ → ℂ → ℂ) (sT : Finset ℕ) (N : ℕ) (wfam : Fin N → ℂ → ℂ) (z₁ : ℂ) (ρ : ℝ)
    (k : Fin N) (Uop S : Set ℂ),
    sT ⊆ Finset.range (N + 1) → N ∈ sT → 1 ≤ N → 0 < ρ →
    (∀ i ∈ sT, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ) →
    a N z₁ ≠ 0 → (fibrePoly a sT z₁).Separable →
    (∀ k', ContinuousOn (wfam k') (Metric.ball z₁ ρ)) →
    (∀ z ∈ Metric.ball z₁ ρ, ∀ k' l, k' ≠ l → wfam k' z ≠ wfam l z) →
    (∀ z ∈ Metric.ball z₁ ρ, (fibrePoly a sT z).natDegree = N) →
    (∀ k', ∀ z ∈ Metric.ball z₁ ρ, ∑ i ∈ sT, a i z * (wfam k' z) ^ i = 0) →
    z₁ ∈ frontier (filledJulia c₁) →
    IsClosed S → S.Nonempty → S ⊆ frontier (filledJulia c₁) → S ⊆ Metric.ball z₁ ρ →
    S ⊆ (filledJulia c₂)ᶜ →
    IsOpen Uop → (Uop ∩ S).Nonempty → (∀ x ∈ Uop ∩ S, ‖wfam k x‖ = 1) → False

/-- **hbothconn, conditional on the two named Props.**  A `HoleFreeTip` plus `SmoothPieceRigidity`
give the bivariate no-relation for the pair — the both-connected input of
`q62_phiMero_independence_conditional`. -/
theorem noRelation_phiMero_of_holeFreeTip_of_rigidity {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (h1M : c₁ ∈ mandelbrot) (h2M : c₂ ∈ mandelbrot)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    {z₀ : ℂ} {r : ℝ} (htip : HoleFreeTip c₁ c₂ z₀ r)
    (hrig : SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  rcases Nat.lt_or_ge (bivarPoly Q s).natDegree 1 with hdeg0 | hpos
  · -- degree-0 degenerate relation: the lone coefficient function vanishes on `U`,
    -- contradicting its nonzero analytic-ring element
    exfalso
    have hdeg0' : (bivarPoly Q s).natDegree = 0 := by omega
    have hQzero : ∀ i ∈ s, i ≠ 0 → Q i = 0 := by
      intro i hi hi0
      have hcoeff : (bivarPoly Q s).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [bivarPoly, Polynomial.finsetSum_coeff] at hcoeff
      simp only [Polynomial.coeff_C_mul_X_pow] at hcoeff
      rw [Finset.sum_ite_eq] at hcoeff
      rw [if_pos hi] at hcoeff
      exact hcoeff
    obtain ⟨i₀, hi₀s, hi₀ne⟩ := hnt
    have hi₀0 : i₀ = 0 := by
      by_contra h
      apply hi₀ne
      rw [hQzero i₀ hi₀s h]
      simp
    rw [hi₀0] at hi₀ne hi₀s
    have hfun : ∀ z ∈ U, (Q 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) = 0 := by
      intro z hzU
      have h1 := hEqOn hzU
      simp only [Pi.zero_apply] at h1
      have h2 : ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i
          = (Q 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
        rw [Finset.sum_eq_single_of_mem 0 hi₀s]
        · simp
        · intro b hb hb0
          rw [hQzero b hb hb0]
          simp
      rw [h2] at h1
      exact h1
    apply hi₀ne
    have hval : ((Q 0).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) : analyticSubring U).val
        = ((0 : analyticSubring U) : Germ (Filter.principal U) ℂ) := by
      rw [eval₂_polyToAnalytic_val, ZeroMemClass.coe_zero, ← Filter.Germ.coe_zero,
        Filter.Germ.coe_eq]
      exact Filter.eventually_principal.mpr fun z hz => hfun z hz
    exact Subtype.ext hval
  · -- genuine bivariate relation: run the pigeonhole chain into the rigidity Prop
    obtain ⟨N, a, sT, wfam, z₁, ρ, k, Uop, S, hsupp, hN, hN1, hρ, haan, hlead, hsep,
      hwc, hwsep, hwdeg, hwrel, hz₁J, hScl, hSne, hSJ, hSball, hSK₂, hUop, hUopne, hmod1⟩ :=
      exists_relOpen_smooth_piece_of_holeFreeTip hUo hUc hUne hUinf h1M h2M hU₁ hU₂ hG
        htip Q s hpos hEqOn
    exact hrig a sT N wfam z₁ ρ k Uop S hsupp hN hN1 hρ haan hlead hsep hwc hwsep hwdeg
      hwrel hz₁J hScl hSne hSJ hSball hSK₂ hUop hUopne hmod1

end Bottcher
