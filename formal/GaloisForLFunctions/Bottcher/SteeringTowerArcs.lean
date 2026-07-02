/-
# Tower-section arcs as steerable injective arcs (B1b)

Bridges the abstract steering engine (`SteeringWindow`) to the concrete tower construction: a
tower-section circle `θ ↦ S.T(r·e^{iθ})` restricted to any angular window of width `< 2π` is a
continuous injective arc — exactly the `η` data that `exists_steering_window_margin` consumes.
The circle map is injective on short intervals (the exponential is injective modulo `2π`), and the
tower section `S.T` is injective on the annulus, so their composite is injective on the window.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SteeringWindow
import GaloisForLFunctions.Bottcher.SectionTower
import GaloisForLFunctions.Bottcher.SectionTowerStep

open Set Metric Topology Complex

namespace Bottcher

/-- `circleMap 0 r` is injective on any closed interval of length `< 2π` (for `r ≠ 0`): equal
images force the arguments to differ by an integer multiple of `2π`, impossible for a positive
gap below `2π`. -/
theorem circleMap_injOn_Icc_of_lt {r : ℝ} (hr : r ≠ 0) {α β : ℝ}
    (hlt : β - α < 2 * Real.pi) : InjOn (circleMap 0 r) (Icc α β) := by
  intro θ₁ h₁ θ₂ h₂ heq
  have hcexp : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) := by
    have e1 : circleMap 0 r θ₁ = r * Complex.exp (θ₁ * Complex.I) := by simp [circleMap]
    have e2 : circleMap 0 r θ₂ = r * Complex.exp (θ₂ * Complex.I) := by simp [circleMap]
    rw [e1, e2] at heq
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    exact mul_left_cancel₀ hrc heq
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hcexp
  have hn' : (θ₁ : ℂ) * Complex.I = ((θ₂ : ℂ) + n * (2 * Real.pi)) * Complex.I := by
    rw [hn]; ring
  have hII : Complex.I ≠ 0 := Complex.I_ne_zero
  have hcast : (θ₁ : ℂ) = (θ₂ : ℂ) + n * (2 * Real.pi) := mul_right_cancel₀ hII hn'
  have hreal : θ₁ = θ₂ + n * (2 * Real.pi) := by exact_mod_cast hcast
  -- the gap `θ₁ − θ₂ = n·2π` lies strictly in `(−2π, 2π)`, forcing `n = 0`
  have hgap : θ₁ - θ₂ = (n : ℝ) * (2 * Real.pi) := by linarith [hreal]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hb1 : θ₁ - θ₂ < 2 * Real.pi := by
    have : θ₁ - θ₂ ≤ β - α := by
      have := h₁.2; have := h₁.1; have := h₂.1; have := h₂.2; linarith
    linarith
  have hb2 : -(2 * Real.pi) < θ₁ - θ₂ := by
    have : α - β ≤ θ₁ - θ₂ := by
      have := h₁.1; have := h₂.2; linarith
    linarith
  have hn0 : n = 0 := by
    rw [hgap] at hb1 hb2
    have hlt1 : (n : ℝ) < 1 := by nlinarith [hb1, hpi]
    have hgt1 : (-1 : ℝ) < (n : ℝ) := by nlinarith [hb2, hpi]
    have : (-1 : ℤ) < n ∧ n < 1 := ⟨by exact_mod_cast hgt1, by exact_mod_cast hlt1⟩
    omega
  rw [hn0] at hreal; simpa using hreal

/-- **A tower-section circle arc is continuous and injective on a short angular window.**  For a
tower section `S` on the annulus `(rlo, rhi)`, a radius `r` inside it, and any closed angular
window `[α, β]` of width `< 2π`, the arc `θ ↦ S.T(r·e^{iθ})` is continuous and injective — the
concrete instance of the abstract `η` arcs the steering window consumes. -/
theorem TowerSection.arc_continuousOn_injOn {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hrpos : 0 < r) (hr1 : rlo < r) (hr2 : r < rhi) {α β : ℝ}
    (hlt : β - α < 2 * Real.pi) :
    ContinuousOn (fun θ => S.T (circleMap 0 r θ)) (Icc α β) ∧
      InjOn (fun θ => S.T (circleMap 0 r θ)) (Icc α β) := by
  have hmem : ∀ θ : ℝ, circleMap 0 r θ ∈ annulusSet rlo rhi :=
    circleMap_mem_annulusSet hrpos hr1 hr2
  constructor
  · have hTcont : ContinuousOn S.T (annulusSet rlo rhi) :=
      S.an.continuousOn
    exact (hTcont.comp_continuous (continuous_circleMap 0 r) hmem).continuousOn
  · intro θ₁ h₁ θ₂ h₂ heq
    have hcm : circleMap 0 r θ₁ = circleMap 0 r θ₂ :=
      S.inj (hmem θ₁) (hmem θ₂) heq
    exact circleMap_injOn_Icc_of_lt (ne_of_gt hrpos) hlt h₁ h₂ hcm

/-- **Steering a finite family of tower-section arcs past a Cantor target (concrete 02-A).**  For
finitely many tower sections `S i` at radii `r i`, a compact totally disconnected `K` (e.g. a
Cantor filled Julia set `K_{c₂}`), and a base angular window `(a, b)` of width `< 2π`, there is a
nondegenerate closed subwindow `[c', d'] ⊆ (a, b)` and a uniform margin `ε > 0` such that the whole
`ε`-tube around every arc `θ ↦ S_i.T(r_i·e^{iθ})`, `θ ∈ [c', d']`, misses `K`.  This is the
tower-level instantiation of `exists_steering_window_margin`: the arcs are continuous and injective
on the short window, so the abstract engine applies verbatim. -/
theorem exists_tower_steering_window {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    {K : Set ℂ} (hKcpt : IsCompact K) (hKne : K.Nonempty) (hKtd : IsTotallyDisconnected K)
    {cc : ι → ℂ} {rlo rhi : ι → ℝ} (S : ∀ i, TowerSection (cc i) (rlo i) (rhi i))
    {r : ι → ℝ} (hrpos : ∀ i ∈ s, 0 < r i) (hr1 : ∀ i ∈ s, rlo i < r i)
    (hr2 : ∀ i ∈ s, r i < rhi i)
    {a b : ℝ} (hab : a < b) (hwidth : b - a < 2 * Real.pi) :
    ∃ c' d' : ℝ, c' < d' ∧ Icc c' d' ⊆ Ioo a b ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ i ∈ s, ∀ t ∈ Icc c' d', ∀ z : ℂ,
        dist z ((S i).T (circleMap 0 (r i) t)) < ε → z ∉ K := by
  have harc : ∀ i ∈ s,
      ContinuousOn (fun θ => (S i).T (circleMap 0 (r i) θ)) (Icc a b) ∧
        InjOn (fun θ => (S i).T (circleMap 0 (r i) θ)) (Icc a b) := fun i hi =>
    (S i).arc_continuousOn_injOn (hrpos i hi) (hr1 i hi) (hr2 i hi) hwidth
  exact exists_steering_window_margin s hs hKcpt hKne hKtd hab
    (fun i θ => (S i).T (circleMap 0 (r i) θ))
    (fun i hi => (harc i hi).1) (fun i hi => (harc i hi).2)

end Bottcher
