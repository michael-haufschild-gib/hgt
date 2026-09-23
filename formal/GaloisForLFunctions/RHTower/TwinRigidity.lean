import GaloisForLFunctions.RHTower.TwinFactorization
import GaloisForLFunctions.RHTower.WeldTowerFree
import GaloisForLFunctions.HTGeometry.LocalAnalyticQuotient

/-!
# Twin rigidity: every twin factorization of ξ is a square root dressed by a unit

A twin factorization of ξ on `Re s > ½` is a pair of analytic factors `a, d` with `a · d = ξ` and
equal vanishing orders at every right-half point.  Equal orders make the quotient `a / d` an
analytic nonvanishing function `q` on the half-plane; the half-plane is simply connected, so `q`
has an analytic square root `v`; and `g := d · v` satisfies `g² = d² q = d · a = ξ`, with
`a = g · v` and `d = g / v`.

Conversely, for any analytic square root `g` of ξ on the half-plane and any analytic nonvanishing
`v` there, `(g v, g / v)` is a twin factorization.

So twin factorizations are exactly the diagonal twin `(g, g)` dressed by units: the set of twins
is empty or a torsor under the group of analytic units of the half-plane.  The freedom to choose
non-diagonal twins carries no information beyond the existence of a square root, which is the
base rung of the multiplicity ladder.
-/

open Complex Filter Topology

namespace RHTower

/-- The open half-plane `Re s > ½` is simply connected. -/
theorem isSimplyConnected_rightHalf : IsSimplyConnected rightHalf :=
  isSimplyConnected_of_convex (convex_halfSpace_re_gt (1 / 2))
    ⟨1, show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num⟩

/-- The factors of a twin factorization have finite order at every right-half point. -/
theorem twin_analyticOrderAt_ne_top {a d : ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ a rightHalf) (hd : AnalyticOnNhd ℂ d rightHalf)
    (hprod : ∀ s ∈ rightHalf, a s * d s = xi s) {z : ℂ} (hz : z ∈ rightHalf) :
    analyticOrderAt a z ≠ ⊤ := by
  intro htop
  have hev : xi =ᶠ[𝓝 z] a * d := by
    filter_upwards [isOpen_rightHalf.mem_nhds hz] with s hs
    exact (hprod s hs).symm
  have h1 : analyticOrderAt xi z = analyticOrderAt a z + analyticOrderAt d z := by
    rw [analyticOrderAt_congr hev]
    exact analyticOrderAt_mul (ha z hz) (hd z hz)
  apply xi_order_ne_top z
  rw [h1, htop, top_add]

/-- **Twin rigidity.**  Every twin factorization `(a, d)` of ξ on the right half-plane is a
square root `g` of ξ dressed by an analytic unit `v`: `a = g v` and `g = d v`. -/
theorem twin_eq_sqrt_mul_unit {a d : ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ a rightHalf) (hd : AnalyticOnNhd ℂ d rightHalf)
    (hprod : ∀ s ∈ rightHalf, a s * d s = xi s)
    (hord : ∀ ρ ∈ rightHalf, analyticOrderAt a ρ = analyticOrderAt d ρ) :
    ∃ g v : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalf ∧ (∀ s ∈ rightHalf, g s ^ (2 : ℕ) = xi s) ∧
      AnalyticOnNhd ℂ v rightHalf ∧ (∀ s ∈ rightHalf, v s ≠ 0) ∧
      (∀ s ∈ rightHalf, a s = g s * v s) ∧ ∀ s ∈ rightHalf, g s = d s * v s := by
  have hfin : ∀ z ∈ rightHalf, analyticOrderAt a z ≠ ⊤ :=
    fun z hz => twin_analyticOrderAt_ne_top ha hd hprod hz
  obtain ⟨hq, hqne, hqeq⟩ :=
    GaloisForLFunctions.HTGeometry.localQuotientOn_analytic_nonvanishing_factorization
      ha hd hfin hord
  set q := GaloisForLFunctions.HTGeometry.localQuotientOn a d rightHalf with hqdef
  obtain ⟨v, hvdiff, hvsq⟩ := Bottcher.exists_differentiableOn_pow_eq isSimplyConnected_rightHalf
    isOpen_rightHalf (fun z hz => (hq z hz).differentiableWithinAt)
    (by
      rintro ⟨z, hz, hz0⟩
      exact hqne z hz hz0)
    (two_ne_zero : (2 : ℕ) ≠ 0)
  have hvan : AnalyticOnNhd ℂ v rightHalf := hvdiff.analyticOnNhd isOpen_rightHalf
  have hvne : ∀ s ∈ rightHalf, v s ≠ 0 := by
    intro s hs h0
    have h1 := hvsq s hs
    rw [h0, zero_pow two_ne_zero] at h1
    exact hqne s hs h1.symm
  refine ⟨fun s => d s * v s, v, hd.mul hvan, ?_, hvan, hvne, ?_, fun s _ => rfl⟩
  · intro s hs
    have h1 := hvsq s hs
    have h2 := hqeq s hs
    have h3 := hprod s hs
    calc (d s * v s) ^ (2 : ℕ) = d s * (v s ^ (2 : ℕ) * d s) := by ring
      _ = d s * (q s * d s) := by rw [h1]
      _ = d s * a s := by rw [← h2]
      _ = xi s := by rw [mul_comm]; exact h3
  · intro s hs
    have h1 := hvsq s hs
    have h2 := hqeq s hs
    calc a s = q s * d s := h2
      _ = v s ^ (2 : ℕ) * d s := by rw [h1]
      _ = d s * v s * v s := by ring

/-- **Twins from a square root and a unit.**  For any analytic square root `g` of ξ on the right
half-plane and any analytic nonvanishing `v` there, `(g v, g / v)` is a twin factorization. -/
theorem twinFactorization_of_sqrt_mul_unit {g v : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g rightHalf) (hgsq : ∀ s ∈ rightHalf, g s ^ (2 : ℕ) = xi s)
    (hv : AnalyticOnNhd ℂ v rightHalf) (hvne : ∀ s ∈ rightHalf, v s ≠ 0) :
    TwinFactorization := by
  have hvinv : AnalyticOnNhd ℂ (fun s => (v s)⁻¹) rightHalf := hv.inv hvne
  refine ⟨fun s => g s * v s, fun s => g s * (v s)⁻¹, hg.mul hv, hg.mul hvinv, ?_, ?_⟩
  · intro s hs
    have := hgsq s hs
    calc g s * v s * (g s * (v s)⁻¹) = g s ^ (2 : ℕ) * (v s * (v s)⁻¹) := by ring
      _ = xi s := by rw [mul_inv_cancel₀ (hvne s hs), mul_one, this]
  · intro ρ hρ
    have h1 : analyticOrderAt (fun s => g s * v s) ρ
        = analyticOrderAt g ρ + analyticOrderAt v ρ :=
      analyticOrderAt_mul (hg ρ hρ) (hv ρ hρ)
    have h2 : analyticOrderAt (fun s => g s * (v s)⁻¹) ρ
        = analyticOrderAt g ρ + analyticOrderAt (fun s => (v s)⁻¹) ρ :=
      analyticOrderAt_mul (hg ρ hρ) (hvinv ρ hρ)
    have hv0 : analyticOrderAt v ρ = 0 := (hv ρ hρ).analyticOrderAt_eq_zero.mpr (hvne ρ hρ)
    have hvi0 : analyticOrderAt (fun s => (v s)⁻¹) ρ = 0 :=
      (hvinv ρ hρ).analyticOrderAt_eq_zero.mpr (inv_ne_zero (hvne ρ hρ))
    rw [h1, h2, hv0, hvi0]

/-- **The twin set is the diagonal twin dressed by units.**  Twin factorizations exist iff ξ has
an analytic square root on the right half-plane, and every twin is `(g v, g / v)` for such a root
`g` and an analytic unit `v`. -/
theorem twinFactorization_iff_exists_sqrt :
    TwinFactorization ↔ ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ ∀ s ∈ rightHalf, g s ^ (2 : ℕ) = xi s := by
  rw [← rhLadder_one_iff_twinFactorization, rhLadder_one_iff_sqrt_rightHalf]

end RHTower
