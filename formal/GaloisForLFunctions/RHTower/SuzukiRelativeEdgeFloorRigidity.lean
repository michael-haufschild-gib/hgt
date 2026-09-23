import GaloisForLFunctions.RHTower.SuzukiRelativeEdgeParityFloor

/-!
# The strict-floor edge collapse and the rigid parity incidence

Two consequences of the ground-mode edge bound complete the relative-edge correspondence.

If the even floor is strictly below the odd floor, the odd variational floor already forces the
ground defect to be at least the floor gap, so the edge bound is `g/(2(α_e - λ) + g)` with `g` the
gap, and this tends to `1` as the shift rises to the even floor: a strict even floor collapses the
relative edge completely.

At a tied floor the gap is zero and the argument survives only through the ground defect itself.
Its vanishing is not an accident of the quadratic value: for a positive semidefinite form, a vector
of zero energy is annihilated by the whole form.  So the defect vanishes exactly on the odd form
kernel, and avoiding collapse forces the even bottom space to sit inside the odd one.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-! ## `(257)`: a strict even floor collapses the edge -/

/-- The odd variational floor bounds the ground defect below by the floor gap. -/
theorem groundDefect_ge_floorGap {V : Type*} [NormedAddCommGroup V]
    {qo : V → ℝ} {αe αo : ℝ} (hfloor : ∀ f : V, αo * ‖f‖ ^ (2 : ℕ) ≤ qo f)
    {φ : V} (hφ : ‖φ‖ = 1) : αo - αe ≤ qo φ - αe := by
  have h := hfloor φ
  rw [hφ] at h
  simp at h
  linarith

/-- The ground-mode edge bound is monotone in the ground defect. -/
theorem edgeBound_mono {η₁ η₂ d : ℝ} (hη : 0 ≤ η₁) (hd : 0 < d) (hle : η₁ ≤ η₂) :
    η₁ / (2 * d + η₁) ≤ η₂ / (2 * d + η₂) := by
  have h1 : (0 : ℝ) < 2 * d + η₁ := by linarith
  have h2 : (0 : ℝ) < 2 * d + η₂ := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-- **`(257)`: the edge bound rises to one as the shift approaches a strict even floor.** -/
theorem tendsto_edgeFloorBound {g αe : ℝ} (hg : 0 < g) :
    Tendsto (fun lam : ℝ => g / (2 * (αe - lam) + g)) (𝓝[<] αe) (𝓝 1) := by
  have hcont : Continuous fun lam : ℝ => 2 * (αe - lam) + g :=
    (continuous_const.mul (continuous_const.sub continuous_id)).add continuous_const
  have hden : Tendsto (fun lam : ℝ => 2 * (αe - lam) + g) (𝓝 αe) (𝓝 g) := by
    have := hcont.tendsto αe
    simpa using this
  have hquot : Tendsto (fun lam : ℝ => g / (2 * (αe - lam) + g)) (𝓝 αe) (𝓝 (g / g)) :=
    tendsto_const_nhds.div hden hg.ne'
  rw [div_self hg.ne'] at hquot
  exact hquot.mono_left nhdsWithin_le_nhds

/-- **`(257)`, combined**: at a strict even floor the edge bound is the floor-gap expression. -/
theorem edge_ge_floorGap {r αe αo lam : ℝ} (hr : |r| < 1) (hgap : 0 < αo - αe)
    (hlam : lam < αe) {η : ℝ} (hη : αo - αe ≤ η)
    (hratio : 1 + η / (αe - lam) ≤ (1 + r) / (1 - r)) :
    (αo - αe) / (2 * (αe - lam) + (αo - αe)) ≤ r := by
  have hd : (0 : ℝ) < αe - lam := by linarith
  exact le_trans (edgeBound_mono hgap.le hd hη)
    (edge_ge_of_ground_test hr (le_trans hgap.le hη) hd hratio)

/-! ## `(258)`: the rigid incidence of the two bottom spaces -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **A vector of zero energy is annihilated by a positive semidefinite form.** -/
theorem psd_form_kernel_of_diag_eq_zero {b : V → V → ℝ}
    (hsymm : ∀ x y, b x y = b y x)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsmul : ∀ (c : ℝ) (x y : V), b (c • x) y = c * b x y)
    (hpsd : ∀ x, 0 ≤ b x x) {x : V} (hx : b x x = 0) (y : V) : b x y = 0 := by
  have h := sq_le_of_psd_bilinear hsymm hadd hsmul hpsd x y
  rw [hx, zero_mul] at h
  nlinarith [sq_nonneg (b x y)]

/-- **`(258)`: a ground mode outside the odd form kernel has a strictly positive defect**, so the
edge bound applies and the relative edge collapses. -/
theorem groundDefect_pos_of_not_formKernel {b : V → V → ℝ}
    (hsymm : ∀ x y, b x y = b y x)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsmul : ∀ (c : ℝ) (x y : V), b (c • x) y = c * b x y)
    (hpsd : ∀ x, 0 ≤ b x x) {x : V} (hx : ∃ y, b x y ≠ 0) : 0 < b x x := by
  rcases lt_or_eq_of_le (hpsd x) with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy⟩ := hx
    exact hy (psd_form_kernel_of_diag_eq_zero hsymm hadd hsmul hpsd h.symm y)

/-- **`(258)`, contrapositive form**: avoiding the pole-driven collapse forces the even bottom
space into the odd one. -/
theorem formKernel_of_groundDefect_eq_zero {b : V → V → ℝ}
    (hsymm : ∀ x y, b x y = b y x)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsmul : ∀ (c : ℝ) (x y : V), b (c • x) y = c * b x y)
    (hpsd : ∀ x, 0 ≤ b x x) {x : V} (hx : b x x = 0) : ∀ y, b x y = 0 :=
  psd_form_kernel_of_diag_eq_zero hsymm hadd hsmul hpsd hx

end RHTower
