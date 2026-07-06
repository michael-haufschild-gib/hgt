/-
The u-plane ladder packages the descended completed zeta function on simply
connected slit-plane regions.  The domain no longer needs to be convex: a
preconnected simply connected region inside the slit plane, with one nonzero
base value, supports the whole coherent dyadic Kummer tower exactly when
`xiDescent` has no zero there.
-/
import GaloisForLFunctions.RHTower.SquareLadder

namespace RHTower

open Complex Filter Set

/-- Levelwise dyadic roots force nonvanishing on any open preconnected region.
The obstruction argument is order-theoretic and does not need convexity. -/
theorem nonvanishing_of_exists_roots_all_two_powers_preconnected
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩpc : IsPreconnected Ω) (hz₀ : z₀ ∈ Ω)
    (hf : AnalyticOnNhd ℂ f Ω) (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧
      ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    ∀ s ∈ Ω, f s ≠ 0 := by
  intro ρ hρ hρ0
  have hord : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩpc hρ hev0
    exact hf0 (this hz₀)
  set m : ℕ := (analyticOrderAt f ρ).toNat with hmdef
  have hm : (m : ℕ∞) = analyticOrderAt f ρ := ENat.coe_toNat hord
  have hdvd : ∀ k : ℕ, 2 ^ k ∣ m := by
    intro k
    obtain ⟨g, hgan, hgpow⟩ := hroots k
    have hdvd' : ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt f ρ :=
      root_orders_dvd hΩo hgan hgpow hρ
    rw [← hm] at hdvd'
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd'
  have hm0 : m = 0 := by
    by_contra hm0
    have h2 : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd m)
    have h3 : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  have hne : analyticOrderAt f ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hf ρ hρ, hρ0⟩
  rw [← hm, hm0] at hne
  exact hne rfl

/-- Independent dyadic roots on an open simply connected preconnected region assemble
to one coherent tower.  Convexity is not part of the assembly mechanism. -/
theorem coherentTower_of_exists_roots_all_two_powers_preconnected
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩsc : IsSimplyConnected Ω) (hΩpc : IsPreconnected Ω)
    (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω) (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧
      ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    Nonempty (CoherentTower f Ω) := by
  have hnz : ∀ s ∈ Ω, f s ≠ 0 :=
    nonvanishing_of_exists_roots_all_two_powers_preconnected
      hΩo hΩpc hz₀ hf hf0 hroots
  exact (coherentTower_iff_nonvanishing hΩo hΩsc hΩpc hf hz₀ hf0).2 hnz

/-- On open simply connected preconnected regions, coherent towers are equivalent
to having analytic dyadic roots at every finite level. -/
theorem coherentTower_iff_exists_roots_all_two_powers_preconnected
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩsc : IsSimplyConnected Ω) (hΩpc : IsPreconnected Ω)
    (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω) (hf0 : f z₀ ≠ 0) :
    Nonempty (CoherentTower f Ω) ↔
      ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧
        ∀ s ∈ Ω, g s ^ (2 ^ k) = f s := by
  constructor
  · rintro ⟨T⟩ k
    exact ⟨T.level k, T.analytic k, T.pow_eq k⟩
  · exact coherentTower_of_exists_roots_all_two_powers_preconnected
      hΩo hΩsc hΩpc hz₀ hf hf0

/-- The descended function is analytic on every region contained in the slit plane. -/
theorem xiDescent_analyticOnNhd_of_subset_slitPlane {U : Set ℂ} (hU : U ⊆ slitPlane) :
    AnalyticOnNhd ℂ xiDescent U := by
  intro z hz
  exact xiDescent_analyticAt (hU hz)

/-- A simply connected zero-free slit-plane region carries an analytic `n`-th root
of `xiDescent`. -/
theorem xiDescent_root_of_nonvanishing_on {U : Set ℂ} (hUo : IsOpen U)
    (hUsc : IsSimplyConnected U) (hUsub : U ⊆ slitPlane) {n : ℕ} (hn : n ≠ 0)
    (hnz : ∀ z ∈ U, xiDescent z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z, g z ≠ 0) ∧
      ∀ z ∈ U, g z ^ n = xiDescent z := by
  exact U0KummerBranch.exists_analyticOnNhd_pow_eq hUo hUsc
    (xiDescent_analyticOnNhd_of_subset_slitPlane hUsub) hnz hn

/-- The dyadic level `k` root of `xiDescent` on a simply connected zero-free
slit-plane region. -/
theorem xiDescent_twoPower_root_of_nonvanishing_on {U : Set ℂ} (hUo : IsOpen U)
    (hUsc : IsSimplyConnected U) (hUsub : U ⊆ slitPlane) (k : ℕ)
    (hnz : ∀ z ∈ U, xiDescent z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z, g z ≠ 0) ∧
      ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z := by
  exact xiDescent_root_of_nonvanishing_on hUo hUsc hUsub
    (pow_ne_zero k two_ne_zero) hnz

/-- On any open simply connected preconnected slit-plane region with one nonzero
base value, the coherent u-plane ladder is equivalent to zero-freeness. -/
theorem xiDescent_coherentTower_iff_nonvanishing_on {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hz₀ : z₀ ∈ U) (hz₀nz : xiDescent z₀ ≠ 0) :
    Nonempty (CoherentTower xiDescent U) ↔ ∀ z ∈ U, xiDescent z ≠ 0 := by
  exact coherentTower_iff_nonvanishing hUo hUsc hUpc
    (xiDescent_analyticOnNhd_of_subset_slitPlane hUsub) hz₀ hz₀nz

/-- Zero-freeness on a slit-plane region gives the coherent dyadic u-plane ladder. -/
theorem xiDescent_coherentTower_of_nonvanishing_on {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hz₀ : z₀ ∈ U) (hz₀nz : xiDescent z₀ ≠ 0)
    (hnz : ∀ z ∈ U, xiDescent z ≠ 0) :
    Nonempty (CoherentTower xiDescent U) :=
  (xiDescent_coherentTower_iff_nonvanishing_on hUo hUsc hUpc hUsub hz₀ hz₀nz).2 hnz

/-- Independent dyadic roots of `xiDescent` on a simply connected slit-plane region
assemble into one coherent u-plane ladder. -/
theorem xiDescent_coherentTower_of_roots_all_two_powers_on {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hz₀ : z₀ ∈ U) (hz₀nz : xiDescent z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z) :
    Nonempty (CoherentTower xiDescent U) :=
  coherentTower_of_exists_roots_all_two_powers_preconnected hUo hUsc hUpc hz₀
    (xiDescent_analyticOnNhd_of_subset_slitPlane hUsub) hz₀nz hroots

/-- Coherence of the u-plane ladder is equivalent to independent dyadic roots at
all finite levels on the same simply connected slit-plane region. -/
theorem xiDescent_coherentTower_iff_roots_all_two_powers_on {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hz₀ : z₀ ∈ U) (hz₀nz : xiDescent z₀ ≠ 0) :
    Nonempty (CoherentTower xiDescent U) ↔
      ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g U ∧
        ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z := by
  exact coherentTower_iff_exists_roots_all_two_powers_preconnected hUo hUsc hUpc hz₀
    (xiDescent_analyticOnNhd_of_subset_slitPlane hUsub) hz₀nz

/-- On a simply connected slit-plane region, independent dyadic roots at every
finite level are equivalent to zero-freeness of `xiDescent`. -/
theorem xiDescent_roots_all_two_powers_iff_nonvanishing_on {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hz₀ : z₀ ∈ U) (hz₀nz : xiDescent z₀ ≠ 0) :
    (∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z) ↔
      ∀ z ∈ U, xiDescent z ≠ 0 := by
  constructor
  · exact nonvanishing_of_exists_roots_all_two_powers_preconnected hUo hUpc hz₀
      (xiDescent_analyticOnNhd_of_subset_slitPlane hUsub) hz₀nz
  · intro hnz k
    obtain ⟨g, hgan, _hgnz, hgpow⟩ :=
      xiDescent_twoPower_root_of_nonvanishing_on hUo hUsc hUsub k hnz
    exact ⟨g, hgan, hgpow⟩

/-- The positive real far-field point used as a u-plane anchor lies in the slit plane. -/
theorem xiDescent_far_anchor_mem_slitPlane : ((9 : ℂ) / 4) ∈ slitPlane := by
  norm_num [Complex.mem_slitPlane_iff]

/-- The positive real u-plane anchor is a nonzero value of the descended function. -/
theorem xiDescent_far_anchor_ne_zero : xiDescent ((9 : ℂ) / 4) ≠ 0 := by
  rw [show ((9 : ℂ) / 4) = ((2 : ℂ) - 1 / 2) ^ 2 from by norm_num,
    ← xi_eq_xiDescent]
  exact xi_two_ne_zero

/-- A simply connected slit-plane region containing the far-field anchor supports a
coherent u-plane ladder exactly when `xiDescent` has no zero in the region. -/
theorem xiDescent_coherentTower_iff_nonvanishing_on_far_anchor {U : Set ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hanchor : ((9 : ℂ) / 4) ∈ U) :
    Nonempty (CoherentTower xiDescent U) ↔ ∀ z ∈ U, xiDescent z ≠ 0 :=
  xiDescent_coherentTower_iff_nonvanishing_on hUo hUsc hUpc hUsub hanchor
    xiDescent_far_anchor_ne_zero

/-- On a far-anchored simply connected slit-plane region, coherent tower data are
equivalent to independent dyadic roots at every finite level. -/
theorem xiDescent_coherentTower_iff_roots_all_two_powers_on_far_anchor {U : Set ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hanchor : ((9 : ℂ) / 4) ∈ U) :
    Nonempty (CoherentTower xiDescent U) ↔
      ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g U ∧
        ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z :=
  xiDescent_coherentTower_iff_roots_all_two_powers_on hUo hUsc hUpc hUsub hanchor
    xiDescent_far_anchor_ne_zero

/-- On a far-anchored simply connected slit-plane region, all finite dyadic roots
exist exactly when `xiDescent` is zero-free on the region. -/
theorem xiDescent_roots_all_two_powers_iff_nonvanishing_on_far_anchor {U : Set ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hUsub : U ⊆ slitPlane) (hanchor : ((9 : ℂ) / 4) ∈ U) :
    (∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z) ↔
      ∀ z ∈ U, xiDescent z ≠ 0 :=
  xiDescent_roots_all_two_powers_iff_nonvanishing_on hUo hUsc hUpc hUsub hanchor
    xiDescent_far_anchor_ne_zero

/-- Under RH, every simply connected slit-plane region containing the far-field anchor
has a coherent u-plane ladder. -/
theorem xiDescent_coherentTower_of_RH_on_far_anchor {U : Set ℂ}
    (hRH : RiemannHypothesis) (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    (hUpc : IsPreconnected U) (hUsub : U ⊆ slitPlane)
    (hanchor : ((9 : ℂ) / 4) ∈ U) :
    Nonempty (CoherentTower xiDescent U) := by
  refine (xiDescent_coherentTower_iff_nonvanishing_on_far_anchor
    hUo hUsc hUpc hUsub hanchor).2 ?_
  intro z hz
  exact (rh_iff_xiDescent_ne_zero_slitPlane.mp hRH) z (hUsub hz)

/-- Under RH, all finite dyadic roots exist on every simply connected slit-plane
region containing the far-field anchor. -/
theorem xiDescent_roots_all_two_powers_of_RH_on_far_anchor {U : Set ℂ}
    (hRH : RiemannHypothesis) (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    (hUpc : IsPreconnected U) (hUsub : U ⊆ slitPlane)
    (hanchor : ((9 : ℂ) / 4) ∈ U) :
    ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, g z ^ (2 ^ k) = xiDescent z := by
  refine (xiDescent_roots_all_two_powers_iff_nonvanishing_on_far_anchor
    hUo hUsc hUpc hUsub hanchor).2 ?_
  intro z hz
  exact (rh_iff_xiDescent_ne_zero_slitPlane.mp hRH) z (hUsub hz)

end RHTower
