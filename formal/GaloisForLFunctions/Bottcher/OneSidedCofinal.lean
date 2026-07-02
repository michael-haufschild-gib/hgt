/-
# The cofinal one-sided lane — the numerically-necessary weakening

`OneSidedAt` demands a connected punctured ball at EVERY small radius.  The consumer
(`holeFreeTip_of_oneSided`) only ever reads ONE radius below the `K₂`-clearance, so the
weakest sufficient input is connectivity at ARBITRARILY SMALL radii — `OneSidedAtCofinal`.

The weakening is not cosmetic: at `c = −0.9` (real, period-2 window) the β-fixed point has a
single access, yet `ball β ρ \ K` is DISCONNECTED for `ρ` in log-periodically recurring bands
(self-similar rim pockets pinched by the limbs of `K`; the multiplier `2β` is real, so the
Julia germ at `β` is log-periodic in scale; verified numerically at scales `0.096 → 0.003`,
stable in grid resolution and iteration depth — `computations/op136_beta_ball_connectivity/`).
So the ∀-form can FAIL at `β` while the cofinal form survives (clean bands dominate every
period).  All downstream consumers are rebuilt here on the cofinal form:

* `OneSidedAtCofinal`, `ExposedOneSidedCofinal` — the weakened Props, with implications from
  the strong forms.
* `holeFreeTip_of_oneSidedCofinal` — the tip certificate on the cofinal input.
* `q62_phiMero_independence_of_exposed_oneSidedCofinal`,
  `q62_phiMero_bothconnected_of_op6_cofinal` — the general and both-connected capstones.
* `realPair_exposedOneSidedCofinal_of_connected_beta` — real pairs: `β₁ ∈ ∂K₁` is proven
  (`betaFixed_mem_frontier_slice`), off-`K₂` and visibility are proven (`RealPairExposed`),
  so the exposure input shrinks to the bare connectivity clause at `β₁`.
* `q62_phiMero_realPair_of_connected_beta` — the real-pair capstone on that bare clause.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RealPairExposed

open Set Metric Bornology

namespace Bottcher

/-- **Cofinally one-sided boundary point**: `x` is on the Julia set and the punctured ball
`ball x ρ \ K` is connected for ARBITRARILY SMALL `ρ` — not necessarily for all small `ρ`.
The weakest input the tip certificate needs. -/
def OneSidedAtCofinal (c x : ℂ) : Prop :=
  x ∈ frontier (filledJulia c) ∧
    ∀ ε > 0, ∃ ρ, 0 < ρ ∧ ρ < ε ∧ IsConnected (Metric.ball x ρ \ filledJulia c)

/-- The strong (all-small-radii) form implies the cofinal form. -/
theorem OneSidedAt.cofinal {c x : ℂ} (h : OneSidedAt c x) : OneSidedAtCofinal c x := by
  obtain ⟨hfront, ρ₀, hρ₀, hconn⟩ := h
  refine ⟨hfront, fun ε hε => ?_⟩
  refine ⟨min ρ₀ (ε / 2), lt_min hρ₀ (by linarith), ?_,
    hconn _ (lt_min hρ₀ (by linarith)) (min_le_left _ _)⟩
  calc min ρ₀ (ε / 2) ≤ ε / 2 := min_le_right _ _
    _ < ε := by linarith

/-- **Cofinally-exposed one-sided point** — the open-problem-6 shape on the weakened
one-sidedness. -/
def ExposedOneSidedCofinal (c₁ c₂ : ℂ) : Prop :=
  ∃ x, OneSidedAtCofinal c₁ x ∧ x ∉ filledJulia c₂ ∧ VisibleFromInfinity c₁ c₂ x

theorem ExposedOneSided.cofinal {c₁ c₂ : ℂ} (h : ExposedOneSided c₁ c₂) :
    ExposedOneSidedCofinal c₁ c₂ := by
  obtain ⟨x, hos, hx2, hvis⟩ := h
  exact ⟨x, hos.cofinal, hx2, hvis⟩

/-- **The tip certificate from the cofinal form.**  The consumer only ever needs ONE radius
below the `K₂`-clearance `δ`, and the cofinal hypothesis supplies one. -/
theorem holeFreeTip_of_oneSidedCofinal {c₁ c₂ x : ℂ}
    (hos : OneSidedAtCofinal c₁ x) (hx2 : x ∉ filledJulia c₂)
    (hvis : VisibleFromInfinity c₁ c₂ x) :
    ∃ r > 0, HoleFreeTip c₁ c₂ x r := by
  obtain ⟨hfront, hconn⟩ := hos
  obtain ⟨W, hWconn, hWunbd, hWcompl, hxW⟩ := hvis
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl x hx2
  obtain ⟨r, hr, hrδ, hpunct⟩ := hconn δ hδ
  have hballδ : Metric.ball x r ⊆ (filledJulia c₂)ᶜ :=
    (Metric.ball_subset_ball hrδ.le).trans hδsub
  obtain ⟨w₀, hw₀ball, hw₀W⟩ :=
    mem_closure_iff.mp hxW _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hw₀notK₁ : w₀ ∉ filledJulia c₁ := fun h => hWcompl hw₀W (Or.inl h)
  have hw₀mem : w₀ ∈ Metric.ball x r \ filledJulia c₁ := ⟨hw₀ball, hw₀notK₁⟩
  set V : Set ℂ := (Metric.ball x r \ filledJulia c₁) ∪ W with hVdef
  have hVconn : IsPreconnected V :=
    hpunct.isPreconnected.union w₀ hw₀mem hw₀W hWconn
  have hVunbd : ¬ IsBounded V := fun hbd => hWunbd (hbd.subset subset_union_right)
  have hVcompl : V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ := by
    rintro z (⟨hzb, hzK₁⟩ | hzW)
    · rintro (h | h)
      · exact hzK₁ h
      · exact hballδ hzb h
    · exact hWcompl hzW
  refine ⟨r, hr, hr, hfront, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact hballδ hz1 hz2
  · intro q hq hqK₁
    exact ⟨V, Or.inl ⟨hq, hqK₁⟩, hVconn, hVunbd, hVcompl⟩

/-- **General q62 from a cofinally-exposed one-sided point** — as
`q62_phiMero_independence_of_exposed_oneSided`, on the weakened input. -/
theorem q62_phiMero_independence_of_exposed_oneSidedCofinal
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (hexp : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSidedCofinal c₁ c₂)
    (hrig : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine q62_phiMero_independence_of_monodromy_tip_rigidity hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hc₁0 hc₁2 hc₂0 hc₂2 hmono₁ hmono₂ ?_ hrig
  intro h1 h2
  obtain ⟨x, hos, hx2, hvis⟩ := hexp h1 h2
  obtain ⟨r, _, htip⟩ := holeFreeTip_of_oneSidedCofinal hos hx2 hvis
  exact ⟨x, r, htip⟩

/-- **Both-connected q62 from the cofinal exposure disjunction** — as
`q62_phiMero_bothconnected_of_op6`, on the weakened input. -/
theorem q62_phiMero_bothconnected_of_op6_cofinal
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hexp : ExposedOneSidedCofinal c₁ c₂ ∨ ExposedOneSidedCofinal c₂ c₁)
    (hrig12 : SmoothPieceRigidity c₁ c₂) (hrig21 : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  rcases hexp with hL | hR
  · exact q62_phiMero_independence_of_exposed_oneSidedCofinal hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      hc₁0 hc₁2 hc₂0 hc₂2 (fun h => absurd hc₁M h) (fun h => absurd hc₂M h)
      (fun _ _ => hL) (fun _ _ => hrig12)
  · exact noRelation_symm
      (q62_phiMero_independence_of_exposed_oneSidedCofinal hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁
        hc₂0 hc₂2 hc₁0 hc₁2 (fun h => absurd hc₂M h) (fun h => absurd hc₁M h)
        (fun _ _ => hR) (fun _ _ => hrig21))

/-- **Real pairs: the input shrinks to the bare connectivity clause.**  `β₁ ∈ ∂K₁` is proven
(`betaFixed_mem_frontier`), off-`K₂` and visibility are proven (`RealPairExposed`); what
remains is connectivity of the punctured ball at `β₁` for arbitrarily small radii. -/
theorem realPair_exposedOneSidedCofinal_of_connected_beta {c₁ c₂ : ℝ}
    (hc₁2 : -2 ≤ c₁) (hc₁4 : c₁ ≤ 1 / 4) (hc₂4 : c₂ ≤ 1 / 4)
    (hβ : betaFixed c₂ < betaFixed c₁)
    (hconn : ∀ ε > 0, ∃ ρ, 0 < ρ ∧ ρ < ε ∧
      IsConnected (Metric.ball (betaFixed c₁ : ℂ) ρ \ filledJulia (c₁ : ℂ))) :
    ExposedOneSidedCofinal (c₁ : ℂ) (c₂ : ℂ) :=
  ⟨(betaFixed c₁ : ℂ), ⟨betaFixed_mem_frontier_slice hc₁2 hc₁4, hconn⟩,
    not_mem_filledJulia_of_betaFixed_lt hc₂4 hβ,
    realPair_beta_visibleFromInfinity hc₁4 hc₂4 hβ⟩

/-- **Real-pair both-connected capstone on the bare clause.**  For real `−2 ≤ c₁ < c₂ ≤ 1/4`,
both nonexceptional: cofinal punctured-ball connectivity at `β₁` plus smooth-piece rigidity
(both orientations) give `NoRelation` for the Böttcher pair. -/
theorem q62_phiMero_realPair_of_connected_beta
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℝ} (hlt : c₁ < c₂) (hc₁2 : -2 ≤ c₁) (hc₂4 : c₂ ≤ 1 / 4)
    (hc₁0 : (c₁ : ℂ) ≠ 0) (hc₁m2 : (c₁ : ℂ) ≠ -2) (hc₂0 : (c₂ : ℂ) ≠ 0) (hc₂m2 : (c₂ : ℂ) ≠ -2)
    (hU₁ : U ⊆ escapeOpen (c₁ : ℂ)) (hU₂ : U ⊆ escapeOpen (c₂ : ℂ))
    (hconn : ∀ ε > 0, ∃ ρ, 0 < ρ ∧ ρ < ε ∧
      IsConnected (Metric.ball (betaFixed c₁ : ℂ) ρ \ filledJulia (c₁ : ℂ)))
    (hrig12 : SmoothPieceRigidity (c₁ : ℂ) (c₂ : ℂ))
    (hrig21 : SmoothPieceRigidity (c₂ : ℂ) (c₁ : ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero (c₁ : ℂ) hU₁) (phiMero (c₂ : ℂ) hU₂) := by
  have hc₁4 : c₁ ≤ 1 / 4 := hlt.le.trans hc₂4
  have hc₂2 : -2 ≤ c₂ := hc₁2.trans hlt.le
  exact q62_phiMero_bothconnected_of_op6_cofinal hUo hUc hUne hUinf
    (real_mem_mandelbrot hc₁2 hc₁4) (real_mem_mandelbrot hc₂2 hc₂4)
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (Or.inl (realPair_exposedOneSidedCofinal_of_connected_beta hc₁2 hc₁4 hc₂4
      (betaFixed_lt_betaFixed hlt hc₂4) hconn))
    hrig12 hrig21

end Bottcher
