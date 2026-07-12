import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# The completed logarithmic derivative is not holonomic at its zeros

The pole-based master engine excludes linear differential equations with polynomial
coefficients for any function whose derivatives blow up with nonvanishing leading Laurent
data along an injective sequence of poles.  The logarithmic derivative `ξ'/ξ` of the
completed zeta has a pole at every `ξ`-zero `ρ`, of the exact shape
`ξ'/ξ = m_ρ/(s-ρ) + analytic` with `m_ρ ≥ 1` the vanishing order — no simplicity of zeros is
needed.  Feeding these residues to the engine: given any injective sequence of `ξ`-zeros,
`ξ'/ξ` satisfies no linear differential equation with polynomial coefficients.

The zero sequence enters as an explicit hypothesis; its existence is the classical
infinitude of nontrivial zeros.  This is the holonomic rung of the hypertranscendence of the
completed constraint: the full algebraic-differential rung remains open, and cannot follow
from pole bookkeeping alone — a logarithmic derivative satisfies Riccati-type cancellations
(`u' + u²` has no double pole at a simple zero), so nonlinear relations require the
quantitative digamma input, not sharper Laurent data.
-/

noncomputable section

namespace RHTower

open Complex Filter Finset Topology GaloisForLFunctions

/-- The logarithmic derivative of the completed `xi`. -/
def xiLogDeriv (s : ℂ) : ℂ := deriv xi s / xi s

/-- At every zero `ρ` of `xi`, each iterated derivative of `ξ'/ξ` has a pole of exact order
`j+1` with leading coefficient `m_ρ · (-1)^j · j!`, where `m_ρ ≥ 1` is the vanishing order.
The residues never vanish, whatever the multiplicity. -/
theorem xiLogDeriv_iteratedDeriv_residue {ρ : ℂ} (hρ : xi ρ = 0) (j : ℕ) :
    Tendsto (fun s : ℂ => (s - ρ) ^ (j + 1) * iteratedDeriv j xiLogDeriv s)
      (𝓝[≠] ρ)
      (𝓝 (((analyticOrderAt xi ρ).toNat : ℂ) * ((-1) ^ j * (j.factorial : ℂ)))) := by
  set m : ℕ := (analyticOrderAt xi ρ).toNat with hm_def
  have hxiA : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  have hmord : analyticOrderAt xi ρ = (m : ℕ∞) := (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  obtain ⟨g, hg, hg0, hev⟩ := (hxiA.analyticOrderAt_eq_natCast).mp hmord
  have hgan : ∀ᶠ z in 𝓝 ρ, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev.and (hgan.and hgne))
  set U : Set ℂ := Metric.ball ρ r \ {ρ} with hU_def
  have hUopen : IsOpen U := Metric.isOpen_ball.sdiff isClosed_singleton
  have hUmem : ∀ s ∈ U, s ∈ Metric.ball ρ r ∧ s ≠ ρ := fun s hs => ⟨hs.1, hs.2⟩
  set G : ℂ → ℂ := fun t => (m : ℂ) + (t - ρ) * (deriv g t / g t) with hG_def
  have hGA : ∀ z ∈ Metric.ball ρ r, AnalyticAt ℂ G z := by
    intro z hz
    have hgz := (hball z hz).2.1
    have hgz0 := (hball z hz).2.2
    exact analyticAt_const.add
      (((analyticAt_id.sub analyticAt_const)).mul (hgz.deriv.div hgz hgz0))
  -- pointwise factorization of `ξ'/ξ` on the punctured ball
  have hpoint : ∀ t ∈ U, xiLogDeriv t = G t * (t + -ρ)⁻¹ := by
    intro t ht
    obtain ⟨htball, htne⟩ := hUmem t ht
    have hgt := (hball t htball).2.1
    have hgt0 := (hball t htball).2.2
    have htρ : t - ρ ≠ 0 := sub_ne_zero.mpr htne
    -- xi agrees with the local model on the ball, hence so does its derivative at `t`
    have hloc : ∀ z ∈ Metric.ball ρ r, xi z = (z - ρ) ^ m * g z := by
      intro z hz
      have := (hball z hz).1
      simpa [smul_eq_mul] using this
    have hevt : xi =ᶠ[𝓝 t] fun z => (z - ρ) ^ m * g z :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds htball) hloc
    have hgd : HasDerivAt g (deriv g t) t := hgt.differentiableAt.hasDerivAt
    have hpow : HasDerivAt (fun z : ℂ => (z - ρ) ^ m)
        ((m : ℂ) * (t - ρ) ^ (m - 1) * 1) t :=
      ((hasDerivAt_id t).sub_const ρ).pow m
    have hprod := hpow.mul hgd
    have hderiv : deriv xi t
        = (m : ℂ) * (t - ρ) ^ (m - 1) * 1 * g t + (t - ρ) ^ m * deriv g t := by
      rw [hevt.deriv_eq]
      exact hprod.deriv
    have hm1 : 1 ≤ m := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have : analyticOrderAt xi ρ = 0 := by
        rw [hmord, h0]
        rfl
      rcases analyticOrderAt_eq_zero.mp this with h | h
      · exact h hxiA
      · exact h hρ
    have hpowsplit : (t - ρ) ^ m = (t - ρ) ^ (m - 1) * (t - ρ) := by
      rw [← pow_succ]
      congr 1
      omega
    unfold xiLogDeriv
    rw [hderiv, hloc t htball, hG_def]
    have hpm : (t - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero _ htρ
    rw [show t + -ρ = t - ρ by ring]
    field_simp
    rw [hpowsplit]
    ring
  have hres := iteratedDeriv_residue_of_factor_add xiLogDeriv G (-ρ) U
    (fun s hs => by
      rw [show s + -ρ = s - ρ by ring]
      exact sub_ne_zero.mpr (hUmem s hs).2)
    (by
      rw [neg_neg]
      filter_upwards [inter_mem (mem_nhdsWithin_of_mem_nhds
        (Metric.ball_mem_nhds ρ hr)) self_mem_nhdsWithin] with s hs
      exact ⟨hs.1, hs.2⟩)
    (fun s hs n => ((hGA s (hUmem s hs).1).contDiffAt))
    (fun n => by
      rw [neg_neg]
      exact (hGA ρ (Metric.mem_ball_self hr)).contDiffAt)
    (fun s hs => Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) hpoint)
    j
  rw [neg_neg] at hres
  have hGρ : G ρ = (m : ℂ) := by
    rw [hG_def]
    simp
  rw [hGρ] at hres
  refine hres.congr' ?_
  filter_upwards with s
  rw [show s + -ρ = s - ρ by ring]

/-- **The completed logarithmic derivative is not holonomic**, given any injective sequence
of `xi` zeros: `ξ'/ξ` satisfies no linear differential equation with polynomial
coefficients.  The sequence hypothesis is the classical infinitude of nontrivial zeros;
multiplicities are arbitrary. -/
theorem xiLogDeriv_not_holonomic (p : ℕ → ℂ) (hp : Function.Injective p)
    (hz : ∀ k, xi (p k) = 0) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
      (∀ s : ℂ, ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j xiLogDeriv s = 0) →
      ∀ j ∈ range (n + 1), c j = 0 := by
  refine not_holonomic_master xiLogDeriv p hp 1
    (fun i k => ((analyticOrderAt xi (p k)).toNat : ℂ) * ((-1) ^ i * (i.factorial : ℂ)))
    (fun i k => ?_) (fun i k => ?_)
  · have hm1 : 1 ≤ (analyticOrderAt xi (p k)).toNat := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have : analyticOrderAt xi (p k) = 0 := by
        rw [(ENat.coe_toNat (xi_order_ne_top (p k))).symm, h0]
        rfl
      rcases analyticOrderAt_eq_zero.mp this with h | h
      · exact h (xi_analyticOnNhd_univ (p k) (Set.mem_univ (p k)))
      · exact h (hz k)
    have hmne : ((analyticOrderAt xi (p k)).toNat : ℂ) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hm1
    exact mul_ne_zero hmne
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast i.factorial_ne_zero))
  · exact xiLogDeriv_iteratedDeriv_residue (hz k) i

end RHTower
