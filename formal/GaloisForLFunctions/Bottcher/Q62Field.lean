/-
# Field-4 / Field-7 scaffolding: the Böttcher coordinates inside the meromorphic field `M`

Places the genuine Böttcher coordinate `φ_c` as an element of the carrier field `M = meroField U`,
for a common exterior region `U` on which both `φ_{c₁}` and `φ_{c₂}` are analytic. This is the bridge
from the analytic layer (`bottcherCoord`, analytic on `escapeOpen`) to the algebraic carrier
(`meroField`) the q62 statement is instantiated over: `φ_c` is the germ of the actual function, not a
formal symbol.
-/
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.Topology.Separation.Connected

open Filter Topology Set

namespace Bottcher

variable {U : Set ℂ}

/-- The Böttcher coordinate `φ_c` as an element of `analyticSubring U`, valid when `U ⊆ escapeOpen c`
(where `φ_c` is analytic and nowhere zero). The genuine function as a germ. -/
noncomputable def phiAnalytic (c : ℂ) (hU : U ⊆ escapeOpen c) : analyticSubring U :=
  ⟨Germ.coeRingHom (𝓟 U) (bottcherCoord c),
   ⟨bottcherCoord c, (analyticOnNhd_bottcherCoord_full c).mono hU, rfl⟩⟩

/-- The genuine Böttcher coordinate `φ_c` as an element of the meromorphic field `M = meroField U` —
the actual analytic function, embedded via the fraction-field map. This is the `φ c` the q62
instantiation feeds to `q62_independence`. -/
noncomputable def phiMero (c : ℂ) (hU : U ⊆ escapeOpen c) : meroField U :=
  algebraMap (analyticSubring U) (meroField U) (phiAnalytic c hU)

/-! ### A connected base `U` near `∞`

We need a connected open `U ⊆ escapeOpen c₁ ∩ escapeOpen c₂` to place both `φ_{c₁}, φ_{c₂}` in the
same field `M = meroField U`. We take `U` to be a *ball* deep in the common exterior: convexity makes
it connected (the full annular exterior `{‖z‖ > R}` connectedness is not in Mathlib, and a ball
suffices — the connected basin `Ω_c` propagates any germ relation to the global function by the
identity theorem). -/

/-- Real center of norm `3 + max ‖c₁‖ ‖c₂‖`, deep in the common exterior. -/
noncomputable def deepCenter (c₁ c₂ : ℂ) : ℂ := ((3 + max ‖c₁‖ ‖c₂‖ : ℝ) : ℂ)

/-- A unit ball around `deepCenter`, lying inside `escapeOpen c₁ ∩ escapeOpen c₂`. Convex ⟹
connected; the base `U` for placing both `φ_{c₁}, φ_{c₂}` in the same field `M = meroField U`. -/
noncomputable def deepBall (c₁ c₂ : ℂ) : Set ℂ := Metric.ball (deepCenter c₁ c₂) 1

theorem norm_deepCenter (c₁ c₂ : ℂ) : ‖deepCenter c₁ c₂‖ = 3 + max ‖c₁‖ ‖c₂‖ := by
  rw [deepCenter, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Every point of `deepBall` has norm `> 2 + max ‖c₁‖ ‖c₂‖`. -/
theorem deepBall_lt_norm {c₁ c₂ z : ℂ} (hz : z ∈ deepBall c₁ c₂) :
    2 + max ‖c₁‖ ‖c₂‖ < ‖z‖ := by
  rw [deepBall, Metric.mem_ball, Complex.dist_eq] at hz
  have h1 : ‖deepCenter c₁ c₂‖ - ‖z‖ ≤ ‖deepCenter c₁ c₂ - z‖ := norm_sub_norm_le _ _
  rw [norm_deepCenter, norm_sub_rev] at h1
  linarith

theorem deepBall_subset_escapeOpen_left (c₁ c₂ : ℂ) : deepBall c₁ c₂ ⊆ escapeOpen c₁ := by
  intro z hz
  simp only [escapeOpen, mem_setOf_eq]
  have h := deepBall_lt_norm hz
  have hm : max 2 ‖c₁‖ ≤ 2 + max ‖c₁‖ ‖c₂‖ := by
    have := le_max_left ‖c₁‖ ‖c₂‖; have := norm_nonneg c₁; have := norm_nonneg c₂
    apply max_le <;> linarith
  linarith

theorem deepBall_subset_escapeOpen_right (c₁ c₂ : ℂ) : deepBall c₁ c₂ ⊆ escapeOpen c₂ := by
  intro z hz
  simp only [escapeOpen, mem_setOf_eq]
  have h := deepBall_lt_norm hz
  have hm : max 2 ‖c₂‖ ≤ 2 + max ‖c₁‖ ‖c₂‖ := by
    have := le_max_right ‖c₁‖ ‖c₂‖; have := norm_nonneg c₁; have := norm_nonneg c₂
    apply max_le <;> linarith
  linarith

theorem isOpen_deepBall (c₁ c₂ : ℂ) : IsOpen (deepBall c₁ c₂) := Metric.isOpen_ball

theorem isPreconnected_deepBall (c₁ c₂ : ℂ) : IsPreconnected (deepBall c₁ c₂) :=
  (convex_ball _ _).isPreconnected

theorem deepBall_nonempty (c₁ c₂ : ℂ) : (deepBall c₁ c₂).Nonempty :=
  Metric.nonempty_ball.mpr one_pos

theorem deepBall_infinite (c₁ c₂ : ℂ) : (deepBall c₁ c₂).Infinite := by
  have hpc : IsPreconnected (deepBall c₁ c₂) := isPreconnected_deepBall c₁ c₂
  have hc : deepCenter c₁ c₂ ∈ deepBall c₁ c₂ := Metric.mem_ball_self one_pos
  have hc2 : deepCenter c₁ c₂ + 1 / 2 ∈ deepBall c₁ c₂ := by
    rw [deepBall, Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left]
    norm_num [Complex.norm_div, Complex.norm_ofNat]
  exact IsPreconnected.infinite_of_nontrivial hpc
    ⟨deepCenter c₁ c₂, hc, deepCenter c₁ c₂ + 1 / 2, hc2,
     by intro h; have h2 : (1 / 2 : ℂ) = 0 := (by linear_combination -h); norm_num at h2⟩

end Bottcher
