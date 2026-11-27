import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodIsobaricParameters

/-! Conjugate self-duality descends through the inverse character twist.
At infinity, the shifted singleton summand lies inside the regular
algebraic weight multiset of the point. -/

noncomputable section

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

theorem isoLoc_single (D : D7) {a : ℕ} (π : D.naut.CG a)
    (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

/-- A cuspidal point parameter has the conjugate self-dual and regular
algebraic properties required by local–global compatibility. -/
theorem csd_ralg_of_hasParamX_single (D : D7) (i : D.nd.Loc) (x : D.nd.X i)
    (π : D.naut.CG D.R.r) (hx : HasParamX D.nd D.naut i x [⟨D.R.r, π, 1⟩])
    (hTw : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π)
    (hc : D.naut.csd D.naut.etaT)
    (hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)) :
    D.naut.csd π ∧ D.naut.ralg π := by
  obtain ⟨P, -, hB⟩ := hx
  have hp : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Part D.naut.CG) ∈
      twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
    List.mem_cons_self
  refine ⟨?_, (D.naut.ralg_def π).2 fun τ => ?_⟩
  · have h := D.naut.csd_tw _ _ hc (hB.1 _ hp).2.2
    rwa [hTw] at h
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (D.naut.infG_card D.naut.etaTinv τ)
  obtain ⟨k₀, hk₀⟩ := hz τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hW : (D.naut.infWt i τ).Nodup ∧
      ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    rw [D.nbc.embAV_inf i P]
    exact D.nbc.infW_alg _ _ τ
  have hle : (D.naut.infG π τ).map (· + s) ≤ D.naut.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ, ← D.naut.infG_tw π _ τ s hs]
    simp [isoInf, twistIso]
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle hW.1), fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  refine ⟨k - k₀, ?_⟩
  rw [Ranks.nV] at hk
  push_cast at hk hk₀ ⊢
  linear_combination hk - hk₀

end WindowedLandauTheory.NormalizedTypes
