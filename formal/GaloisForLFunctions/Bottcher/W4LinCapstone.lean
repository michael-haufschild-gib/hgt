/-
# Linear-gap both-disconnected q62 (task #139 capstone)

The consumer of `bottcher_towerDataG_linGapRoot`: for disconnected `c₁, c₂` with `‖c₁‖ ≥ 1000`,
`‖c₂‖ ≥ 2` and the LINEAR gap `(√(2‖c₂‖)+1)² ≤ ‖c₁‖/300` (i.e. `‖c₂‖ ≲ ‖c₁‖/600`), the two
Böttcher coordinates satisfy no algebraic relation over `ℂ(z)` on a common far domain —
UNCONDITIONALLY.  Both former interfaces are theorems: the far-band clause dissolved into the
green-superlevel glue (the overlap is the section image of a round sub-annulus), and the
chain-overlap clause is `chainOverlapsConnected_of_normalized` (certified fold window +
antipode kills, after renormalizing the slit center by a full turn when below `−3π/8`).

No measure theory enters.  Compare
`q62_phiMero_pair_far_general` (unconditional, quadratic gap `300·(max 2 ‖c₂‖)² ≤ ‖c₁‖`): the
linear gap covers second parameters up to `~‖c₁‖/600` instead of `~√(‖c₁‖/300)`.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.MixedTowerData
import GaloisForLFunctions.Bottcher.W4LinPack

open Set Filter

namespace Bottcher

/-- **Both-disconnected q62, linear norm gap** — unconditional. -/
theorem q62_phiMero_linGap {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc₂2 : (2:ℝ) ≤ ‖c₂‖)
    (hsgap : (Real.sqrt (2 * ‖c₂‖) + 1) ^ 2 ≤ ‖c₁‖ / 300) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  classical
  obtain ⟨Bmin, hBmin1, hspec⟩ :=
    bottcher_towerDataG_linGapRoot c₁ c₂ hc₁ hc1000 hc₂2 hsgap
  set FB : ℝ := bottcherFarBound c₂ hc₂ with hFBdef
  have hFB1 : 1 < FB := one_lt_bottcherFarBound c₂ hc₂
  set BU : ℝ := Bmin + FB + ‖c₁‖ + ‖c₂‖ + 2 with hBUdef
  have hBU1 : 1 < BU := by
    rw [hBUdef]
    have := norm_nonneg c₁
    have := norm_nonneg c₂
    linarith
  have hBU2 : BU < 2 * BU := by linarith
  set U : Set ℂ := annulusSet BU (2 * BU) with hUdef
  have hUo : IsOpen U := isOpen_annulusSet _ _
  have hUconn : IsConnected U := isConnected_annulus (by linarith) hBU2
  have hUne : U.Nonempty := hUconn.nonempty
  have hUinf : U.Infinite := by
    have h1 : (Set.Ioo BU (2 * BU)).Infinite := Set.Ioo_infinite hBU2
    have h2 : ((fun t : ℝ => (t : ℂ)) '' Set.Ioo BU (2 * BU)).Infinite :=
      h1.image (fun a _ b _ hab => by exact_mod_cast hab)
    apply h2.mono
    rintro z ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have htpos : (0:ℝ) < t := by linarith
    constructor <;> simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    · exact ht1
    · exact ht2
  have hUB : ∀ z ∈ U, Bmin < ‖z‖ := by
    rintro z ⟨h1, _⟩
    rw [hBUdef] at h1
    have := norm_nonneg c₁
    have := norm_nonneg c₂
    linarith
  have hUFB : ∀ z ∈ U, FB < ‖z‖ := by
    rintro z ⟨h1, _⟩
    rw [hBUdef] at h1
    have := norm_nonneg c₁
    have := norm_nonneg c₂
    linarith
  have hU₁ : U ⊆ escapeOpen c₁ := by
    rintro z ⟨h1, _⟩
    show max 2 ‖c₁‖ < ‖z‖
    rw [hBUdef] at h1
    have := norm_nonneg c₂
    apply max_lt
    · linarith
    · linarith
  have hU₂ : U ⊆ escapeOpen c₂ := by
    rintro z ⟨h1, _⟩
    show max 2 ‖c₂‖ < ‖z‖
    rw [hBUdef] at h1
    have := norm_nonneg c₁
    apply max_lt
    · linarith
    · linarith
  obtain ⟨a₁', a₂', ha₁', ha₂', hdata⟩ := hspec U hUo hUconn.isPreconnected hUne hUinf hUB
  have ha₁eq : a₁' = phiAnalytic c₁ hU₁ := Subtype.ext (by rw [← ha₁']; rfl)
  have ha₂eq : a₂' = phiAnalytic c₂ hU₂ := Subtype.ext (by rw [← ha₂']; rfl)
  have hGtr₂ : haveI := isDomain_analyticSubring U hUo hUconn.isPreconnected hUne
               haveI := (ratfuncToMero U hUo hUconn.isPreconnected hUne hUinf).toAlgebra
               Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    bottcher_transcendental_far c₂ hc₂ hUo hUconn.isPreconnected hUne hUinf hUFB
      (a₂ := phiAnalytic c₂ hU₂) rfl
  refine ⟨U, hUo, hUconn.isPreconnected, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUconn.isPreconnected hUne
  letI := (ratfuncToMero U hUo hUconn.isPreconnected hUne hUinf).toAlgebra
  have hF₁ : phiMero c₁ hU₁ ≠ 0 := phiMero_ne_zero hUo hUconn.isPreconnected hUne hU₁
  apply q62_disconnected_of_towerData hUo hUconn.isPreconnected hUne hUinf
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) hF₁ hGtr₂
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, GBExt, k, hk1, hdk, hFan, hFne, hae,
    hrad, hGB, hloops⟩ := hdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, GBExt, k, hk1, hdk, hFan, hFne, hae,
    ?_, ?_, hloops⟩
  · rw [hrad, ha₁eq]
  · rw [hGB, ha₂eq]

/-- **Both-disconnected q62, linear norm gap, swapped orientation** — by `noRelation_symm`. -/
theorem q62_phiMero_linGap_swapped {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc₁2 : (2:ℝ) ≤ ‖c₁‖)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖)
    (hsgap : (Real.sqrt (2 * ‖c₁‖) + 1) ^ 2 ≤ ‖c₂‖ / 300) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₂', hU₁', hNR⟩ :=
    q62_phiMero_linGap hc₂ hc1000 hc₁ hc₁2 hsgap
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁', hU₂', ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_symm hNR

end Bottcher
