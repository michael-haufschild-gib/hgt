import GaloisForLFunctions.HTGeometry.PoincareHopf.DivergenceForm

/-!
# The fundamental vanishing lemma of degree theory

Let `Ω` be a bounded open subset of `ℝⁿ`, `u` a `C²` map, and `W` a `C¹` field vanishing outside
the ball of radius `ρ`.  If `‖u x‖ > ρ` on the boundary of `Ω`, then

  `∫_Ω (div W) (u x) · det (Du x) dx = 0`.

The integrand is the divergence of the Piola field `V j = ∑ i, cof (Du)_{i j} · (W ∘ u) i`, and the
boundary condition makes the zero extension of `V` outside `Ω` a globally `C¹` compactly supported
field: near a boundary point of `Ω` the field already vanishes identically, because `‖u‖ > ρ` there
and hence on a whole neighbourhood.  So the integral is the total divergence of a compactly
supported field, which vanishes.

Every invariance property of the Brouwer degree is a corollary of this one lemma.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ}

/-- The zero extension of the Piola field outside `Ω`. -/
noncomputable def piolaFieldExt (u W : (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  if x ∈ Ω then piolaField u W x else 0

section

variable {u W : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {ρ : ℝ}

theorem piolaField_eq_zero_of_le (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0) {x : Fin n → ℝ}
    (hx : ρ ≤ ‖u x‖) : piolaField u W x = 0 := by
  funext j
  simp [piolaField, hWball _ hx]

theorem piolaFieldExt_eq_zero_of_lt (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0) {x : Fin n → ℝ}
    (hx : ρ < ‖u x‖) : piolaFieldExt u W Ω x = 0 := by
  by_cases h : x ∈ Ω
  · simp [piolaFieldExt, h, piolaField_eq_zero_of_le hWball hx.le]
  · simp [piolaFieldExt, h]

theorem piolaFieldExt_eq_zero_of_notMem_closure {x : Fin n → ℝ} (hx : x ∉ closure Ω) :
    piolaFieldExt u W Ω x = 0 := by
  have : x ∉ Ω := fun h => hx (subset_closure h)
  simp [piolaFieldExt, this]

/-- Away from `Ω` the extension vanishes on a whole neighbourhood. -/
theorem piolaFieldExt_eventuallyEq_zero (hu : ContDiff ℝ 2 u)
    (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0) (hΩ : IsOpen Ω)
    (hfront : ∀ x ∈ frontier Ω, ρ < ‖u x‖) {x : Fin n → ℝ} (hx : x ∉ Ω) :
    piolaFieldExt u W Ω =ᶠ[nhds x] 0 := by
  by_cases hcl : x ∈ closure Ω
  · -- boundary point: `‖u‖ > ρ` on a neighbourhood
    have hxf : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hcl, hx⟩
    have hlt : ρ < ‖u x‖ := hfront x hxf
    have hcont : Continuous fun z => ‖u z‖ := (hu.continuous).norm
    have hopen : IsOpen {z : Fin n → ℝ | ρ < ‖u z‖} := isOpen_lt continuous_const hcont
    filter_upwards [hopen.mem_nhds hlt] with z hz
    exact piolaFieldExt_eq_zero_of_lt hWball hz
  · have hopen : IsOpen (closure Ω)ᶜ := isClosed_closure.isOpen_compl
    filter_upwards [hopen.mem_nhds hcl] with z hz
    exact piolaFieldExt_eq_zero_of_notMem_closure hz

theorem contDiff_piolaFieldExt (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 1 W)
    (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0) (hΩ : IsOpen Ω)
    (hfront : ∀ x ∈ frontier Ω, ρ < ‖u x‖) :
    ContDiff ℝ 1 (piolaFieldExt u W Ω) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · have hev : piolaFieldExt u W Ω =ᶠ[nhds x] piolaField u W := by
      filter_upwards [hΩ.mem_nhds hx] with z hz
      simp [piolaFieldExt, hz]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((hasFDerivAt_piolaField hu hW x).differentiableAt).contDiffAt_of_contDiff ?_
  · exact (contDiffAt_const (c := (0 : Fin n → ℝ))).congr_of_eventuallyEq
      (piolaFieldExt_eventuallyEq_zero hu hWball hΩ hfront hx)

end

end GaloisForLFunctions.HTGeometry.PoincareHopf
