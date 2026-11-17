import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSecondForm

/-!
# Recovering a contact point from its support plane

The support parametrization has height exactly equal to its support
function. If a point lies below all nearby support planes and touches one,
the first derivatives of the support gap fix both tangent components.
The orthogonal frame then determines the contact point uniquely.
-/

open Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.BonnetEnvelope
open GaloisForLFunctions.HTGeometry.GaussBonnet
open BonnetSupport BonnetSurface StereographicFrame BonnetSecondForm
noncomputable section

/-- The actual support surface has precisely the prescribed height along its Gauss normal. -/
theorem surface_support_height (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    inner ℝ (surface ρ p) (normal p) = ρ p := by
  obtain ⟨hn, hx, hy⟩ := normal_metric p
  have hxn : inner ℝ (tangentX p) (normal p) = 0 := (real_inner_comm _ _).trans hx
  have hyn : inner ℝ (tangentY p) (normal p) = 0 := (real_inner_comm _ _).trans hy
  simp only [surface, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    hn, hxn, hyn, mul_one, mul_zero, add_zero]

/-- A touching point under every support plane equals the actual support parametrization. -/
theorem contact_point_unique {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) (x : Space)
    (hbelow : ∀ q : ℝ × ℝ, inner ℝ x (normal q) ≤ ρ q)
    (htouch : inner ℝ x (normal p) = ρ p) : x = surface ρ p := by
  have hx : IsLocalMin (fun t : ℝ => ρ (t, p.2) - inner ℝ x (normal (t, p.2))) p.1 := by
    apply Eventually.of_forall
    intro t
    change ρ p - inner ℝ x (normal p) ≤ _
    rw [htouch, sub_self]
    exact sub_nonneg.mpr (hbelow (t, p.2))
  have hy : IsLocalMin (fun t : ℝ => ρ (p.1, t) - inner ℝ x (normal (p.1, t))) p.2 := by
    apply Eventually.of_forall
    intro t
    change ρ p - inner ℝ x (normal p) ≤ _
    rw [htouch, sub_self]
    exact sub_nonneg.mpr (hbelow (p.1, t))
  have hnx := normal_path (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)
  have hny := normal_path (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)
  have hdx := hx.hasDerivAt_eq_zero
    ((hasDerivAt_px hρ p.1 p.2).sub ((hasDerivAt_const p.1 x).inner ℝ hnx))
  have hdy := hy.hasDerivAt_eq_zero
    ((hasDerivAt_py hρ p.1 p.2).sub ((hasDerivAt_const p.2 x).inner ℝ hny))
  simp only [one_smul, zero_smul, add_zero, zero_add, id_eq, Prod.mk.eta,
    inner_zero_left] at hdx hdy
  have hex : inner ℝ x (tangentX p) = px ρ p := (sub_eq_zero.mp hdx).symm
  have hey : inner ℝ x (tangentY p) = py ρ p := (sub_eq_zero.mp hdy).symm
  have hres := frame_resolution p x
  rw [htouch, hex, hey] at hres
  rw [hres]
  simp only [surface, smul_add, mul_smul, add_assoc]

#print axioms surface_support_height
#print axioms contact_point_unique
end
end GaloisForLFunctions.HilbertMetric.Geometry.BonnetEnvelope
