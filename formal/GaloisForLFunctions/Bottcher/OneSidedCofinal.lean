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
import GaloisForLFunctions.Bottcher.GreenPullback

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

namespace Bottcher

/-- **Neighbourhood-cofinal one-sidedness**: arbitrarily small OPEN neighbourhoods of `x`
with connected puncture — the round-ball shape dropped.  Log-periodic rim pockets refute
cofinal BALLS at `β` for some real `c`; adapted neighbourhoods dodge them: the repelling
fixed-point transfer `V ↦ g(V)` (inverse branch at `β`) maps a connected puncture to a
connected puncture by the full invariance of `K`, and contracts to all scales — so this form
needs only ONE good neighbourhood inside the linearization domain. -/
def OneSidedAtCofinalNbhd (c x : ℂ) : Prop :=
  x ∈ frontier (filledJulia c) ∧
    ∀ ε > 0, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ Metric.ball x ε ∧
      IsConnected (V \ filledJulia c)

/-- The round-ball cofinal form implies the neighbourhood form. -/
theorem OneSidedAtCofinal.nbhd {c x : ℂ} (h : OneSidedAtCofinal c x) :
    OneSidedAtCofinalNbhd c x := by
  obtain ⟨hfront, hconn⟩ := h
  refine ⟨hfront, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ0, hρε, hpunct⟩ := hconn ε hε
  exact ⟨Metric.ball x ρ, Metric.isOpen_ball, Metric.mem_ball_self hρ0,
    Metric.ball_subset_ball hρε.le, hpunct⟩

/-- **The tip certificate from the neighbourhood-cofinal form.**  The consumer only needs a
round ball INSIDE the good neighbourhood: every escaped point of that ball joins the
neighbourhood's connected puncture, which joins the visibility channel. -/
theorem holeFreeTip_of_oneSidedCofinalNbhd {c₁ c₂ x : ℂ}
    (hos : OneSidedAtCofinalNbhd c₁ x) (hx2 : x ∉ filledJulia c₂)
    (hvis : VisibleFromInfinity c₁ c₂ x) :
    ∃ r > 0, HoleFreeTip c₁ c₂ x r := by
  obtain ⟨hfront, hconn⟩ := hos
  obtain ⟨W, hWconn, hWunbd, hWcompl, hxW⟩ := hvis
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl x hx2
  obtain ⟨V₀, hV₀o, hxV₀, hV₀sub, hpunct⟩ := hconn δ hδ
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hV₀o x hxV₀
  have hV₀K₂ : V₀ ⊆ (filledJulia c₂)ᶜ := hV₀sub.trans hδsub
  obtain ⟨w₀, hw₀ball, hw₀W⟩ :=
    mem_closure_iff.mp hxW _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hw₀notK₁ : w₀ ∉ filledJulia c₁ := fun h => hWcompl hw₀W (Or.inl h)
  have hw₀mem : w₀ ∈ V₀ \ filledJulia c₁ := ⟨hrball hw₀ball, hw₀notK₁⟩
  set V : Set ℂ := (V₀ \ filledJulia c₁) ∪ W with hVdef
  have hVconn : IsPreconnected V :=
    hpunct.isPreconnected.union w₀ hw₀mem hw₀W hWconn
  have hVunbd : ¬ IsBounded V := fun hbd => hWunbd (hbd.subset subset_union_right)
  have hVcompl : V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ := by
    rintro z (⟨hzb, hzK₁⟩ | hzW)
    · rintro (h | h)
      · exact hzK₁ h
      · exact hV₀K₂ hzb h
    · exact hWcompl hzW
  refine ⟨r, hr, hr, hfront, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact hV₀K₂ (hrball hz1) hz2
  · intro q hq hqK₁
    exact ⟨V, Or.inl ⟨hrball hq, hqK₁⟩, hVconn, hVunbd, hVcompl⟩

end Bottcher

namespace Bottcher

/-- **Neighbourhood-cofinally exposed one-sided point** — the open-problem-6 shape on the
neighbourhood-form one-sidedness. -/
def ExposedOneSidedCofinalNbhd (c₁ c₂ : ℂ) : Prop :=
  ∃ x, OneSidedAtCofinalNbhd c₁ x ∧ x ∉ filledJulia c₂ ∧ VisibleFromInfinity c₁ c₂ x

theorem ExposedOneSidedCofinal.nbhd {c₁ c₂ : ℂ} (h : ExposedOneSidedCofinal c₁ c₂) :
    ExposedOneSidedCofinalNbhd c₁ c₂ := by
  obtain ⟨x, hos, hx2, hvis⟩ := h
  exact ⟨x, hos.nbhd, hx2, hvis⟩

/-- **General q62 from a neighbourhood-cofinally exposed one-sided point.** -/
theorem q62_phiMero_independence_of_exposed_oneSidedCofinalNbhd
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
    (hexp : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSidedCofinalNbhd c₁ c₂)
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
  obtain ⟨r, _, htip⟩ := holeFreeTip_of_oneSidedCofinalNbhd hos hx2 hvis
  exact ⟨x, r, htip⟩

/-- **Both-connected q62 from the neighbourhood-cofinal exposure disjunction.** -/
theorem q62_phiMero_bothconnected_of_op6_cofinalNbhd
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hexp : ExposedOneSidedCofinalNbhd c₁ c₂ ∨ ExposedOneSidedCofinalNbhd c₂ c₁)
    (hrig12 : SmoothPieceRigidity c₁ c₂) (hrig21 : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  rcases hexp with hL | hR
  · exact q62_phiMero_independence_of_exposed_oneSidedCofinalNbhd hUo hUc hUne hUinf c₁ c₂
      hU₁ hU₂ hc₁0 hc₁2 hc₂0 hc₂2 (fun h => absurd hc₁M h) (fun h => absurd hc₂M h)
      (fun _ _ => hL) (fun _ _ => hrig12)
  · exact noRelation_symm
      (q62_phiMero_independence_of_exposed_oneSidedCofinalNbhd hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁
        hc₂0 hc₂2 hc₁0 hc₁2 (fun h => absurd hc₂M h) (fun h => absurd hc₁M h)
        (fun _ _ => hR) (fun _ _ => hrig21))

/-- **Real pairs on the neighbourhood clause**: what remains for the real-pair close is ONE
adapted open neighbourhood of `β₁` per scale with connected puncture — the round-ball form
(refuted numerically at some radii by log-periodic rim pockets) is no longer required. -/
theorem realPair_exposedOneSidedCofinalNbhd_of_connected_beta {c₁ c₂ : ℝ}
    (hc₁2 : -2 ≤ c₁) (hc₁4 : c₁ ≤ 1 / 4) (hc₂4 : c₂ ≤ 1 / 4)
    (hβ : betaFixed c₂ < betaFixed c₁)
    (hconn : ∀ ε > 0, ∃ V : Set ℂ, IsOpen V ∧ (betaFixed c₁ : ℂ) ∈ V ∧
      V ⊆ Metric.ball (betaFixed c₁ : ℂ) ε ∧
      IsConnected (V \ filledJulia (c₁ : ℂ))) :
    ExposedOneSidedCofinalNbhd (c₁ : ℂ) (c₂ : ℂ) :=
  ⟨(betaFixed c₁ : ℂ), ⟨betaFixed_mem_frontier_slice hc₁2 hc₁4, hconn⟩,
    not_mem_filledJulia_of_betaFixed_lt hc₂4 hβ,
    realPair_beta_visibleFromInfinity hc₁4 hc₂4 hβ⟩

/-- **Real-pair both-connected capstone on the neighbourhood clause.** -/
theorem q62_phiMero_realPair_of_connected_beta_nbhd
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℝ} (hlt : c₁ < c₂) (hc₁2 : -2 ≤ c₁) (hc₂4 : c₂ ≤ 1 / 4)
    (hc₁0 : (c₁ : ℂ) ≠ 0) (hc₁m2 : (c₁ : ℂ) ≠ -2) (hc₂0 : (c₂ : ℂ) ≠ 0) (hc₂m2 : (c₂ : ℂ) ≠ -2)
    (hU₁ : U ⊆ escapeOpen (c₁ : ℂ)) (hU₂ : U ⊆ escapeOpen (c₂ : ℂ))
    (hconn : ∀ ε > 0, ∃ V : Set ℂ, IsOpen V ∧ (betaFixed c₁ : ℂ) ∈ V ∧
      V ⊆ Metric.ball (betaFixed c₁ : ℂ) ε ∧
      IsConnected (V \ filledJulia (c₁ : ℂ)))
    (hrig12 : SmoothPieceRigidity (c₁ : ℂ) (c₂ : ℂ))
    (hrig21 : SmoothPieceRigidity (c₂ : ℂ) (c₁ : ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero (c₁ : ℂ) hU₁) (phiMero (c₂ : ℂ) hU₂) := by
  have hc₁4 : c₁ ≤ 1 / 4 := hlt.le.trans hc₂4
  have hc₂2 : -2 ≤ c₂ := hc₁2.trans hlt.le
  exact q62_phiMero_bothconnected_of_op6_cofinalNbhd hUo hUc hUne hUinf
    (real_mem_mandelbrot hc₁2 hc₁4) (real_mem_mandelbrot hc₂2 hc₂4)
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (Or.inl (realPair_exposedOneSidedCofinalNbhd_of_connected_beta hc₁2 hc₁4 hc₂4
      (betaFixed_lt_betaFixed hlt hc₂4) hconn))
    hrig12 hrig21

end Bottcher

namespace Bottcher

/-- **Puncture-connectivity pulls back along an inverse branch.**  If `g` is a right inverse
of `f_c` on `V` and `V ∖ K` is connected, then `g(V) ∖ K` is connected: by the FULL invariance
`f_c z ∈ K ⟺ z ∈ K`, the puncture of the image is the image of the puncture. -/
theorem connected_puncture_pullback {c : ℂ} {g : ℂ → ℂ} {V : Set ℂ}
    (hg : ContinuousOn g V) (hfg : ∀ w ∈ V, quadratic c (g w) = w)
    (hVconn : IsConnected (V \ filledJulia c)) :
    IsConnected (g '' V \ filledJulia c) := by
  have hset : g '' V \ filledJulia c = g '' (V \ filledJulia c) := by
    ext z
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hzK⟩
      refine ⟨w, ⟨hw, fun hwK => hzK ?_⟩, rfl⟩
      rw [← hfg w hw] at hwK
      exact (quadratic_mem_filledJulia_iff c (g w)).mp hwK
    · rintro ⟨w, ⟨hw, hwK⟩, rfl⟩
      refine ⟨⟨w, hw, rfl⟩, fun hzK => hwK ?_⟩
      rw [← hfg w hw]
      exact (quadratic_mem_filledJulia_iff c (g w)).mpr hzK
  rw [hset]
  exact hVconn.image g (hg.mono Set.sdiff_subset)

/-- **Cofinal one-sidedness from ONE base neighbourhood.**  Given a contracting inverse
branch `g` of `f_c` fixing the frontier point `β'` on `ball β' r₀`, a SINGLE open
neighbourhood `V₀ ∋ β'` inside the ball with connected puncture propagates to every scale:
`V_{n+1} := g(V_n)` stays open (`g` is an open map), keeps the connected puncture
(`connected_puncture_pullback`), and shrinks geometrically.  The residual real-pair clause is
therefore exactly the base datum `V₀`. -/
theorem oneSidedAtCofinalNbhd_of_base {c β' : ℂ} {g : ℂ → ℂ} {r₀ κ : ℝ}
    (hfront : β' ∈ frontier (filledJulia c))
    (_hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hr₀ : 0 < r₀)
    (hgc : ContinuousOn g (Metric.ball β' r₀))
    (hgopen : ∀ W ⊆ Metric.ball β' r₀, IsOpen W → IsOpen (g '' W))
    (hfg : ∀ w ∈ Metric.ball β' r₀, quadratic c (g w) = w)
    (hgβ : g β' = β')
    (hcontr : ∀ w ∈ Metric.ball β' r₀, ‖g w - β'‖ ≤ κ * ‖w - β'‖)
    {V₀ : Set ℂ} (hV₀o : IsOpen V₀) (hβV₀ : β' ∈ V₀) (hV₀sub : V₀ ⊆ Metric.ball β' r₀)
    (hV₀conn : IsConnected (V₀ \ filledJulia c)) :
    OneSidedAtCofinalNbhd c β' := by
  -- replace the contraction constant by a positive one
  set κ' : ℝ := max κ (1 / 2) with hκ'def
  have hκ'0 : (0:ℝ) < κ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hκ'1 : κ' < 1 := max_lt hκ1 (by norm_num)
  have hκκ' : κ ≤ κ' := le_max_left _ _
  have hcontr' : ∀ w ∈ Metric.ball β' r₀, ‖g w - β'‖ ≤ κ' * ‖w - β'‖ := by
    intro w hw
    calc ‖g w - β'‖ ≤ κ * ‖w - β'‖ := hcontr w hw
      _ ≤ κ' * ‖w - β'‖ := by
          apply mul_le_mul_of_nonneg_right hκκ' (norm_nonneg _)
  refine ⟨hfront, fun ε hε => ?_⟩
  -- the iterated images and their invariants
  have hstep : ∀ n : ℕ, IsOpen ((g^[n]) '' V₀) ∧ β' ∈ (g^[n]) '' V₀ ∧
      (g^[n]) '' V₀ ⊆ Metric.ball β' (κ' ^ n * r₀) ∧
      IsConnected ((g^[n]) '' V₀ \ filledJulia c) := by
    intro n
    induction n with
    | zero =>
        refine ⟨by simpa using hV₀o, by simpa using hβV₀, ?_, by simpa using hV₀conn⟩
        simpa using hV₀sub
    | succ m ih =>
        obtain ⟨iho, ihβ, ihsub, ihconn⟩ := ih
        have hpow0 : (0:ℝ) < κ' ^ m := by positivity
        have hsubball : (g^[m]) '' V₀ ⊆ Metric.ball β' r₀ := by
          intro z hz
          have h1 := ihsub hz
          rw [Metric.mem_ball] at h1 ⊢
          have h3 : κ' ^ m ≤ 1 := pow_le_one₀ (le_of_lt hκ'0) (le_of_lt hκ'1)
          nlinarith
        have himg : (g^[m + 1]) '' V₀ = g '' ((g^[m]) '' V₀) := by
          rw [Function.iterate_succ', Set.image_comp]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [himg]
          exact hgopen _ hsubball iho
        · rw [himg]
          exact ⟨β', ihβ, hgβ⟩
        · rw [himg]
          rintro z ⟨w, hw, rfl⟩
          have h1 := hcontr' w (hsubball hw)
          have h2 := ihsub hw
          rw [Metric.mem_ball, dist_eq_norm] at h2 ⊢
          calc ‖g w - β'‖ ≤ κ' * ‖w - β'‖ := h1
            _ < κ' * (κ' ^ m * r₀) := by
                apply mul_lt_mul_of_pos_left h2 hκ'0
            _ = κ' ^ (m + 1) * r₀ := by ring
        · rw [himg]
          exact connected_puncture_pullback (hgc.mono hsubball)
            (fun w hw => hfg w (hsubball hw)) ihconn
  -- choose the depth reaching scale ε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hr₀) hκ'1
  obtain ⟨ho, hβ, hsub, hconn⟩ := hstep n
  refine ⟨(g^[n]) '' V₀, ho, hβ, ?_, hconn⟩
  intro z hz
  have h1 := hsub hz
  rw [Metric.mem_ball] at h1 ⊢
  have h2 : κ' ^ n * r₀ < ε := (lt_div_iff₀ hr₀).mp hn
  linarith

end Bottcher

namespace Bottcher

/-- **The contracting inverse branch at a repelling fixed point of `f_c`.**  At a fixed point
`b` with `2‖b‖ > 1`, the inverse function theorem gives a right-inverse branch `g` fixing `b`
on a ball, open and continuous, and the quadratic factorization
`f z₁ − f z₂ = (z₁ − z₂)(z₁ + z₂)` makes it a contraction with ratio `2/(2‖b‖+1) < 1` — no
differentiability of the inverse is needed.  This is datum (a) of the
`oneSidedAtCofinalNbhd_of_base` reduction. -/
theorem exists_inverse_branch_at_repelling {c b : ℂ}
    (hfix : quadratic c b = b) (hb : 1 < 2 * ‖b‖) :
    ∃ (g : ℂ → ℂ) (r₀ κ : ℝ), 0 < r₀ ∧ 0 ≤ κ ∧ κ < 1 ∧
      ContinuousOn g (Metric.ball b r₀) ∧
      (∀ W ⊆ Metric.ball b r₀, IsOpen W → IsOpen (g '' W)) ∧
      (∀ w ∈ Metric.ball b r₀, quadratic c (g w) = w) ∧
      g b = b ∧
      (∀ w ∈ Metric.ball b r₀, ‖g w - b‖ ≤ κ * ‖w - b‖) := by
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hb
    norm_num at hb
  have hd : HasStrictDerivAt (quadratic c) (2 * b) b := by
    have h := hasStrictDerivAt_quadratic_iterate c 1 b
    simpa using h
  have hd0 : (2 : ℂ) * b ≠ 0 := mul_ne_zero two_ne_zero hb0
  obtain ⟨φ, hbsrc, hφeq⟩ := exists_openPartialHomeomorph_of_hasStrictDerivAt hd hd0
  have hφb : φ b = b := by rw [hφeq]; exact hfix
  have hbtgt : b ∈ φ.target := hφb ▸ φ.map_source hbsrc
  set g : ℂ → ℂ := ⇑φ.symm with hgdef
  have hgb : g b = b := by
    have h1 := φ.left_inv hbsrc
    rw [hφb] at h1
    exact h1
  -- the clearance radius and contraction ratio
  set ρ : ℝ := (2 * ‖b‖ - 1) / 2 with hρdef
  have hρ0 : (0:ℝ) < ρ := by rw [hρdef]; linarith
  set κ : ℝ := 2 / (2 * ‖b‖ + 1) with hκdef
  have hκ0 : (0:ℝ) < κ := by rw [hκdef]; positivity
  have hκ1 : κ < 1 := by
    rw [hκdef, div_lt_one (by linarith)]
    linarith
  -- image control by continuity of the branch at b
  have hgc : ContinuousAt g b := (φ.continuousOn_symm b hbtgt).continuousAt
    (φ.open_target.mem_nhds hbtgt)
  obtain ⟨r₁, hr₁0, hr₁⟩ := Metric.continuousAt_iff.mp hgc ρ hρ0
  obtain ⟨r₂, hr₂0, hr₂⟩ := Metric.isOpen_iff.mp φ.open_target b hbtgt
  set r₀ : ℝ := min r₁ r₂ with hr₀def
  have hr₀0 : (0:ℝ) < r₀ := lt_min hr₁0 hr₂0
  have hballtgt : Metric.ball b r₀ ⊆ φ.target :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hr₂
  have himgρ : ∀ w ∈ Metric.ball b r₀, ‖g w - b‖ < ρ := by
    intro w hw
    have h1 : dist w b < r₁ := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
    have h2 := hr₁ h1
    rw [dist_eq_norm] at h2
    rw [← hgb]
    exact h2
  have hrinv : ∀ w ∈ Metric.ball b r₀, quadratic c (g w) = w := by
    intro w hw
    have h1 := φ.right_inv (hballtgt hw)
    rw [hφeq] at h1
    exact h1
  refine ⟨g, r₀, κ, hr₀0, le_of_lt hκ0, hκ1, ?_, ?_, hrinv, hgb, ?_⟩
  · exact (φ.continuousOn_symm).mono hballtgt
  · intro W hWsub hWo
    exact φ.symm.isOpen_image_of_subset_source hWo (hWsub.trans hballtgt)
  · intro w hw
    -- the quadratic factorization estimate
    have h1 : w - b = (g w - b) * (g w + b) := by
      have h2 : quadratic c (g w) - quadratic c b = w - b := by
        rw [hrinv w hw, hfix]
      rw [quadratic_apply, quadratic_apply] at h2
      rw [← h2]
      ring
    have h3 : ‖g w + b‖ ≥ 2 * ‖b‖ - ρ := by
      have h4 : g w + b = 2 * b + (g w - b) := by ring
      rw [h4]
      calc ‖2 * b + (g w - b)‖ ≥ ‖(2 : ℂ) * b‖ - ‖g w - b‖ := by
            have := norm_add_le (2 * b + (g w - b)) (-(g w - b))
            simp only [add_neg_cancel_right, norm_neg] at this
            linarith
        _ ≥ 2 * ‖b‖ - ρ := by
            have h5 : ‖(2 : ℂ) * b‖ = 2 * ‖b‖ := by
              rw [norm_mul]
              norm_num
            rw [h5]
            linarith [le_of_lt (himgρ w hw)]
    have h6 : 2 * ‖b‖ - ρ = (2 * ‖b‖ + 1) / 2 := by rw [hρdef]; ring
    have h7 : ‖w - b‖ = ‖g w - b‖ * ‖g w + b‖ := by rw [h1, norm_mul]
    have h8 : (0:ℝ) < (2 * ‖b‖ + 1) / 2 := by linarith
    rw [hκdef]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < 2 * ‖b‖ + 1)]
    calc ‖g w - b‖ * (2 * ‖b‖ + 1) = ‖g w - b‖ * ((2 * ‖b‖ + 1) / 2) * 2 := by ring
      _ ≤ ‖g w - b‖ * ‖g w + b‖ * 2 := by
          have h9 : ‖g w - b‖ * ((2 * ‖b‖ + 1) / 2) ≤ ‖g w - b‖ * ‖g w + b‖ := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            rw [← h6]
            exact h3
          linarith
      _ = ‖w - b‖ * 2 := by rw [← h7]
      _ = 2 * ‖w - b‖ := by ring

end Bottcher

namespace Bottcher

/-- The fixed-point identity for `β` on the full real slice `c ≤ 1/4`. -/
theorem betaFixed_sq_quarter {c : ℝ} (hc4 : c ≤ 1 / 4) :
    betaFixed c ^ 2 + c = betaFixed c := by
  unfold betaFixed
  have h1 : Real.sqrt (1 - 4 * c) ^ 2 = 1 - 4 * c := Real.sq_sqrt (by linarith)
  nlinarith [h1]

/-- **The threshold radius for the single-neighbourhood reduction.**  At a repelling fixed
point there is a radius `r₀` such that ONE good open neighbourhood below it yields the full
neighbourhood-cofinal one-sidedness — the composition of the inverse-branch instantiation with
the transfer engine. -/
theorem exists_threshold_oneSidedAtCofinalNbhd {c b : ℂ}
    (hfront : b ∈ frontier (filledJulia c))
    (hfix : quadratic c b = b) (hb : 1 < 2 * ‖b‖) :
    ∃ r₀ > 0, ∀ V₀ : Set ℂ, IsOpen V₀ → b ∈ V₀ → V₀ ⊆ Metric.ball b r₀ →
      IsConnected (V₀ \ filledJulia c) → OneSidedAtCofinalNbhd c b := by
  obtain ⟨g, r₀, κ, hr₀, hκ0, hκ1, hgc, hgopen, hfg, hgb, hcontr⟩ :=
    exists_inverse_branch_at_repelling hfix hb
  exact ⟨r₀, hr₀, fun V₀ hV₀o hbV₀ hV₀sub hV₀conn =>
    oneSidedAtCofinalNbhd_of_base hfront hκ0 hκ1 hr₀ hgc hgopen hfg hgb hcontr
      hV₀o hbV₀ hV₀sub hV₀conn⟩

/-- **The real-pair clause at threshold scale.**  For real `−2 ≤ c < 1/4`, `β = betaFixed c`
is a repelling fixed point on the frontier, so the entire remaining content of the real-pair
both-connected close is ONE open neighbourhood of `β` below the threshold radius with
connected puncture. -/
theorem exists_threshold_realPair_beta {c : ℝ} (hc2 : -2 ≤ c) (hc4 : c < 1 / 4) :
    ∃ r₀ > 0, ∀ V₀ : Set ℂ, IsOpen V₀ → ((betaFixed c : ℝ) : ℂ) ∈ V₀ →
      V₀ ⊆ Metric.ball ((betaFixed c : ℝ) : ℂ) r₀ →
      IsConnected (V₀ \ filledJulia (c : ℂ)) →
      OneSidedAtCofinalNbhd (c : ℂ) ((betaFixed c : ℝ) : ℂ) := by
  have hfront : ((betaFixed c : ℝ) : ℂ) ∈ frontier (filledJulia (c : ℂ)) :=
    betaFixed_mem_frontier_slice hc2 (le_of_lt hc4)
  have hfix : quadratic (c : ℂ) ((betaFixed c : ℝ) : ℂ) = ((betaFixed c : ℝ) : ℂ) := by
    unfold quadratic
    have h1 := betaFixed_sq_quarter (le_of_lt hc4)
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h1
  have hβhalf : 1 / 2 < betaFixed c := by
    unfold betaFixed
    have h1 : (0:ℝ) < Real.sqrt (1 - 4 * c) := Real.sqrt_pos.mpr (by linarith)
    linarith
  have hb : 1 < 2 * ‖((betaFixed c : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  exact exists_threshold_oneSidedAtCofinalNbhd hfront hfix hb

end Bottcher
