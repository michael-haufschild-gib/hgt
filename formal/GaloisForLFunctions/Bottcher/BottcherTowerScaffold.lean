/-
# Scaffold helpers for the Böttcher tower data

Generic bricks feeding the per-depth tower-data assembly: the open-image lemma for analytic maps
with nonvanishing derivative, the iterated section functional equation
`f^[m] (T w) = T (w^(2^m))`, and the arc square root `exists_arc_sqrt` — the crossing root on a
half-width sub-arc dodging the unique critical-value preimage (the slit recursion's step, with
the quantitative arc-width bound that keeps `d+1` nested slits alive).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SlitCrossing
import GaloisForLFunctions.Bottcher.SectionInverse

open Complex Set Filter Metric Topology

namespace Bottcher

/-- An analytic map with nonvanishing derivative is open (image version). -/
theorem isOpen_image_of_analytic_dne {A : Set ℂ} (hAo : IsOpen A) {f : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ f A) (hdne : ∀ w ∈ A, deriv f w ≠ 0) :
    IsOpen (f '' A) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨w₀, hw₀, rfl⟩
  have hfan : AnalyticAt ℂ f w₀ := han w₀ hw₀
  have hsd : HasStrictDerivAt f (deriv f w₀) w₀ := hfan.hasStrictDerivAt
  have hd0 : deriv f w₀ ≠ 0 := hdne w₀ hw₀
  set ι : ℂ → ℂ := hsd.localInverse _ _ _ hd0 with hιdef
  have hl : ∀ᶠ w in nhds w₀, ι (f w) = w := hsd.eventually_left_inverse hd0
  have hr : ∀ᶠ z in nhds (f w₀), f (ι z) = z := hsd.eventually_right_inverse hd0
  have hcont : ContinuousAt ι (f w₀) :=
    (hfan.analyticAt_localInverse hd0).continuousAt
  have hι₀ : ι (f w₀) = w₀ := hl.self_of_nhds
  have hev : ∀ᶠ z in nhds (f w₀), ι z ∈ A := by
    apply hcont.preimage_mem_nhds
    rw [hι₀]
    exact hAo.mem_nhds hw₀
  filter_upwards [hev, hr] with z hz1 hz2
  exact ⟨ι z, hz1, hz2⟩

/-- **Iterated section functional equation**: as long as the dyadic powers of `w` stay in the
annulus, `f^[m] (T w) = T (w^(2^m))`. -/
theorem TowerSection.iterate_fe {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    (m : ℕ) {w : ℂ} (hpow : ∀ i : ℕ, i ≤ m → w ^ (2 ^ i) ∈ annulusSet rlo rhi) :
    (quadratic c)^[m] (S.T w) = S.T (w ^ (2 ^ m)) := by
  induction m with
  | zero => simp
  | succ n ih =>
      have hpow' : ∀ i : ℕ, i ≤ n → w ^ (2 ^ i) ∈ annulusSet rlo rhi := fun i hi =>
        hpow i (Nat.le_succ_of_le hi)
      rw [Function.iterate_succ_apply', ih hpow']
      have hfe := S.fe (w ^ (2 ^ n)) (hpow n (Nat.le_succ n)) (by
        have h1 : (w ^ (2 ^ n)) ^ 2 = w ^ (2 ^ (n + 1)) := by
          rw [← pow_mul, pow_succ]
        rw [h1]
        exact hpow (n + 1) le_rfl)
      show quadratic c (S.T (w ^ 2 ^ n)) = S.T (w ^ 2 ^ (n + 1))
      unfold quadratic
      rw [← hfe]
      congr 1
      rw [← pow_mul, pow_succ]

/-- Unique log-lift into a width-`≤ 2π` argument window at fixed radius band. -/
theorem exp_lift_unique {r R α β : ℝ} (hβα : β ≤ α + 2 * Real.pi)
    {ξ₁ ξ₂ : ℂ} (h₁ : ξ₁ ∈ arcBox r R α β) (h₂ : ξ₂ ∈ arcBox r R α β)
    (h : Complex.exp ξ₁ = Complex.exp ξ₂) : ξ₁ = ξ₂ :=
  exp_injOn_arcBox r R α β hβα h₁ h₂ h

/-- **The arc square root.**  Injective analytic `P` on an arc annulus takes value `c` at most
once; some sub-arc of at least half the width misses that point, is simply connected, and carries
an analytic square root of `P − c`, injective, nonvanishing, with nonvanishing derivative. -/
theorem exists_arc_sqrt {P : ℂ → ℂ} {r R α β : ℝ} (hr : 0 < r) (hrR : r < R)
    (hαβ : α < β) (hβα : β ≤ α + 2 * Real.pi)
    (han : AnalyticOnNhd ℂ P (arcAnnulus r R α β))
    (hinj : Set.InjOn P (arcAnnulus r R α β))
    (hdne : ∀ v ∈ arcAnnulus r R α β, deriv P v ≠ 0) (c : ℂ) :
    ∃ α' β' : ℝ, α ≤ α' ∧ β' ≤ β ∧ α' < β' ∧ (β - α) / 4 ≤ β' - α' ∧
      ∃ σr : ℂ → ℂ, AnalyticOnNhd ℂ σr (arcAnnulus r R α' β') ∧
        (∀ v ∈ arcAnnulus r R α' β', σr v ^ 2 = P v - c) ∧
        (∀ v ∈ arcAnnulus r R α' β', σr v ≠ 0) ∧
        Set.InjOn σr (arcAnnulus r R α' β') ∧
        (∀ v ∈ arcAnnulus r R α' β', deriv σr v ≠ 0) := by
  classical
  -- the shared root construction on a sub-arc with no c-preimage
  have hmain : ∀ α' β' : ℝ, α ≤ α' → β' ≤ β → α' < β' →
      (∀ v ∈ arcAnnulus r R α' β', P v ≠ c) →
      ∃ σr : ℂ → ℂ, AnalyticOnNhd ℂ σr (arcAnnulus r R α' β') ∧
        (∀ v ∈ arcAnnulus r R α' β', σr v ^ 2 = P v - c) ∧
        (∀ v ∈ arcAnnulus r R α' β', σr v ≠ 0) ∧
        Set.InjOn σr (arcAnnulus r R α' β') ∧
        (∀ v ∈ arcAnnulus r R α' β', deriv σr v ≠ 0) := by
    intro α' β' hα' hβ' hαβ' hne
    have hsub : arcAnnulus r R α' β' ⊆ arcAnnulus r R α β := arcAnnulus_mono hα' hβ'
    have hWopen : IsOpen (arcAnnulus r R α' β') := isOpen_arcAnnulus r R α' β'
    have hWsc : IsSimplyConnected (arcAnnulus r R α' β') :=
      isSimplyConnected_arcAnnulus hr hrR hαβ' (by linarith)
    have hg_an : AnalyticOnNhd ℂ (fun v => P v - c) (arcAnnulus r R α' β') := fun v hv =>
      (han v (hsub hv)).sub analyticAt_const
    have hg_ne : ∀ v ∈ arcAnnulus r R α' β', P v - c ≠ 0 := fun v hv h =>
      hne v hv (sub_eq_zero.mp h)
    obtain ⟨s, hs_an, hs_sq⟩ := exists_analyticOnNhd_pow_eq hWsc hWopen hg_an hg_ne
      (by norm_num : 1 ≤ 2)
    have hs_ne : ∀ v ∈ arcAnnulus r R α' β', s v ≠ 0 := by
      intro v hv h
      have h1 := hs_sq v hv
      rw [h, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h1
      exact hg_ne v hv h1.symm
    refine ⟨s, hs_an, hs_sq, hs_ne, ?_, ?_⟩
    · intro v₁ h₁ v₂ h₂ heq
      have h3 : P v₁ = P v₂ := by
        have e1 := hs_sq v₁ h₁
        have e2 := hs_sq v₂ h₂
        have h4 : P v₁ - c = P v₂ - c := by rw [← e1, ← e2, heq]
        linear_combination h4
      exact hinj (hsub h₁) (hsub h₂) h3
    · intro v hv
      have hs_d : HasDerivAt s (deriv s v) v := (hs_an v hv).differentiableAt.hasDerivAt
      have hLd : HasDerivAt (fun x => s x ^ 2) (2 * s v * deriv s v) v := by
        have h4 := hs_d.pow 2
        have h5 : (2:ℕ) * s v ^ (2 - 1) * deriv s v = 2 * s v * deriv s v := by
          push_cast
          ring
        rwa [h5] at h4
      have hRd : HasDerivAt (fun x => P x - c) (deriv P v) v :=
        ((han v (hsub hv)).differentiableAt.hasDerivAt).sub_const c
      have hEqF : (fun x => s x ^ 2) =ᶠ[nhds v] (fun x => P x - c) := by
        filter_upwards [hWopen.mem_nhds hv] with z hz
        exact hs_sq z hz
      have h7 : HasDerivAt (fun x => P x - c) (2 * s v * deriv s v) v :=
        hLd.congr_of_eventuallyEq hEqF.symm
      have hEqD : deriv P v = 2 * s v * deriv s v := hRd.unique h7
      intro h0
      rw [h0, mul_zero] at hEqD
      exact hdne v (hsub hv) hEqD
  by_cases hzero : ∃ vz ∈ arcAnnulus r R α β, P vz = c
  · obtain ⟨vz, hvz, hPvz⟩ := hzero
    obtain ⟨ξ, hξbox, hξexp⟩ := hvz
    set θ : ℝ := ξ.im with hθdef
    have hθ1 : α < θ := hξbox.2.2.1
    have hθ2 : θ < β := hξbox.2.2.2
    -- pick the wider sub-arc
    have hpick : ∃ α' β' : ℝ, α ≤ α' ∧ β' ≤ β ∧ α' < β' ∧ (β - α) / 4 ≤ β' - α' ∧
        (θ ≤ α' ∨ β' ≤ θ) := by
      by_cases hcase : θ - α ≤ β - θ
      · refine ⟨θ, β, le_of_lt hθ1, le_refl β, ?_, ?_, Or.inl (le_refl θ)⟩ <;> linarith
      · refine ⟨α, θ, le_refl α, le_of_lt hθ2, ?_, ?_, Or.inr (le_refl θ)⟩ <;> linarith
    obtain ⟨α', β', hα', hβ', hαβ', hwidth, hside⟩ := hpick
    refine ⟨α', β', hα', hβ', hαβ', hwidth, ?_⟩
    apply hmain α' β' hα' hβ' hαβ'
    intro v hv h
    have hveq : v = vz := hinj (arcAnnulus_mono hα' hβ' hv) ⟨ξ, hξbox, hξexp⟩
      (by rw [h, hPvz])
    obtain ⟨ξ', hξ'box, hξ'exp⟩ := hv
    have hξ'boxfull : ξ' ∈ arcBox r R α β := by
      obtain ⟨h1, h2, h3, h4⟩ := hξ'box
      exact ⟨h1, h2, by linarith, by linarith⟩
    have hlift : ξ' = ξ := exp_lift_unique hβα hξ'boxfull hξbox (by rw [hξ'exp, hξexp, hveq])
    rcases hside with h5 | h5
    · have := hξ'box.2.2.1
      rw [hlift] at this
      linarith
    · have := hξ'box.2.2.2
      rw [hlift] at this
      linarith
  · refine ⟨α, β, le_refl α, le_refl β, hαβ, by linarith, ?_⟩
    apply hmain α β (le_refl α) (le_refl β) hαβ
    intro v hv h
    exact hzero ⟨v, hv, h⟩

end Bottcher
