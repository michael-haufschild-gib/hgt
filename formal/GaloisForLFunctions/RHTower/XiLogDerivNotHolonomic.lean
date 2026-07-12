import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Logarithmic derivatives are not holonomic at their zeros

The pole-based master engine excludes linear differential equations with polynomial
coefficients for any function whose derivatives blow up with nonvanishing leading Laurent
data along an injective sequence of poles.  A logarithmic derivative `f'/f` has a pole at
every zero `ρ` of `f`, of the exact shape `f'/f = m_ρ/(s-ρ) + analytic` with `m_ρ ≥ 1` the
vanishing order — no simplicity is needed, since the leading Laurent datum `m_ρ·(-1)^j·j!`
never vanishes.  This module proves the residue law for a general analytic zero and feeds it
to the engine twice:

* **`ζ'/ζ` is not holonomic, unconditionally**: the trivial zeros `-2, -4, …` supply the
  injective pole sequence, and "not identically zero nearby" follows from `ζ(2) ≠ 0` by the
  identity theorem on the punctured plane — no simplicity of trivial zeros enters.
* **`ξ'/ξ` is not holonomic given any injective sequence of `ξ`-zeros** — the hypothesis is
  the classical infinitude of nontrivial zeros.

This is the holonomic rung of the hypertranscendence of the (completed) constraint: the full
algebraic-differential rung cannot follow from pole bookkeeping alone — a logarithmic
derivative satisfies Riccati-type cancellations (`u' + u²` has no double pole at a simple
zero), so nonlinear relations require the quantitative digamma input, not sharper Laurent
data.
-/

noncomputable section

namespace RHTower

open Complex Filter Finset Topology GaloisForLFunctions

/-- At an isolated zero `ρ` of an analytic `f`, each iterated derivative of `f'/f` has a
pole of exact order `j+1` with leading coefficient `m_ρ·(-1)^j·j!`, where `m_ρ ≥ 1` is the
vanishing order.  The residues never vanish, whatever the multiplicity. -/
theorem logDeriv_iteratedDeriv_residue_of_zero {f : ℂ → ℂ} {ρ : ℂ}
    (hA : AnalyticAt ℂ f ρ) (hord : analyticOrderAt f ρ ≠ ⊤) (hρ : f ρ = 0) (j : ℕ) :
    Tendsto (fun s : ℂ => (s - ρ) ^ (j + 1)
        * iteratedDeriv j (fun t => deriv f t / f t) s)
      (𝓝[≠] ρ)
      (𝓝 (((analyticOrderAt f ρ).toNat : ℂ) * ((-1) ^ j * (j.factorial : ℂ)))) := by
  set m : ℕ := (analyticOrderAt f ρ).toNat with hm_def
  have hmord : analyticOrderAt f ρ = (m : ℕ∞) := (ENat.coe_toNat hord).symm
  obtain ⟨g, hg, hg0, hev⟩ := (hA.analyticOrderAt_eq_natCast).mp hmord
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
  have hpoint : ∀ t ∈ U, (fun t => deriv f t / f t) t = G t * (t + -ρ)⁻¹ := by
    intro t ht
    obtain ⟨htball, htne⟩ := hUmem t ht
    have hgt := (hball t htball).2.1
    have hgt0 := (hball t htball).2.2
    have htρ : t - ρ ≠ 0 := sub_ne_zero.mpr htne
    have hloc : ∀ z ∈ Metric.ball ρ r, f z = (z - ρ) ^ m * g z := by
      intro z hz
      have := (hball z hz).1
      simpa [smul_eq_mul] using this
    have hevt : f =ᶠ[𝓝 t] fun z => (z - ρ) ^ m * g z :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds htball) hloc
    have hgd : HasDerivAt g (deriv g t) t := hgt.differentiableAt.hasDerivAt
    have hpow : HasDerivAt (fun z : ℂ => (z - ρ) ^ m)
        ((m : ℂ) * (t - ρ) ^ (m - 1) * 1) t :=
      ((hasDerivAt_id t).sub_const ρ).pow m
    have hprod := hpow.mul hgd
    have hderiv : deriv f t
        = (m : ℂ) * (t - ρ) ^ (m - 1) * 1 * g t + (t - ρ) ^ m * deriv g t := by
      rw [hevt.deriv_eq]
      exact hprod.deriv
    have hm1 : 1 ≤ m := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have : analyticOrderAt f ρ = 0 := by
        rw [hmord, h0]
        rfl
      rcases analyticOrderAt_eq_zero.mp this with h | h
      · exact h hA
      · exact h hρ
    have hpowsplit : (t - ρ) ^ m = (t - ρ) ^ (m - 1) * (t - ρ) := by
      rw [← pow_succ]
      congr 1
      omega
    show deriv f t / f t = G t * (t + -ρ)⁻¹
    rw [hderiv, hloc t htball, hG_def]
    have hpm : (t - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero _ htρ
    rw [show t + -ρ = t - ρ by ring]
    field_simp
    rw [hpowsplit]
    ring
  have hres := iteratedDeriv_residue_of_factor_add (fun t => deriv f t / f t) G (-ρ) U
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

/-! ## The completed side: `ξ'/ξ` at a sequence of nontrivial zeros -/

/-- The logarithmic derivative of the completed `xi`. -/
def xiLogDeriv (s : ℂ) : ℂ := deriv xi s / xi s

/-- Residue law for `ξ'/ξ` at any `ξ`-zero, of arbitrary multiplicity. -/
theorem xiLogDeriv_iteratedDeriv_residue {ρ : ℂ} (hρ : xi ρ = 0) (j : ℕ) :
    Tendsto (fun s : ℂ => (s - ρ) ^ (j + 1) * iteratedDeriv j xiLogDeriv s)
      (𝓝[≠] ρ)
      (𝓝 (((analyticOrderAt xi ρ).toNat : ℂ) * ((-1) ^ j * (j.factorial : ℂ)))) := by
  unfold xiLogDeriv
  exact logDeriv_iteratedDeriv_residue_of_zero
    (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)) (xi_order_ne_top ρ) hρ j

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

/-! ## The uncompleted side: `ζ'/ζ` at the trivial zeros, unconditionally -/

/-- The logarithmic derivative of `ζ`. -/
def zetaLogDeriv (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

theorem trivialZero_ne_one (k : ℕ) : (-2 : ℂ) * ((k : ℂ) + 1) ≠ 1 := by
  intro h
  rw [show ((-2 : ℂ) * ((k : ℂ) + 1)) = (((-2 : ℝ) * ((k : ℝ) + 1) : ℝ) : ℂ) by
      push_cast; ring,
    show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num] at h
  have := Complex.ofReal_injective h
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem analyticAt_riemannZeta_trivialZero (k : ℕ) :
    AnalyticAt ℂ riemannZeta ((-2 : ℂ) * ((k : ℂ) + 1)) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds (trivialZero_ne_one k)] with z hz
  exact differentiableAt_riemannZeta hz

/-- `ζ` is not identically zero near a trivial zero: otherwise the identity theorem on the
punctured plane would force `ζ(2) = 0`. -/
theorem analyticOrderAt_riemannZeta_trivialZero_ne_top (k : ℕ) :
    analyticOrderAt riemannZeta ((-2 : ℂ) * ((k : ℂ) + 1)) ≠ ⊤ := by
  intro htop
  have hev := analyticOrderAt_eq_top.mp htop
  set U : Set ℂ := ({1} : Set ℂ)ᶜ with hU
  have hUopen : IsOpen U := isOpen_compl_singleton
  have hUconn : IsPreconnected U := by
    refine ((Set.countable_singleton (1 : ℂ)).isPathConnected_compl_of_one_lt_rank
      ?_).isConnected.isPreconnected
    rw [Complex.rank_real_complex]
    norm_num
  have hζan : AnalyticOnNhd ℂ riemannZeta U :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) hUopen
  have hmem : (-2 : ℂ) * ((k : ℂ) + 1) ∈ U :=
    Set.mem_compl_singleton_iff.mpr (trivialZero_ne_one k)
  have h2mem : (2 : ℂ) ∈ U := Set.mem_compl_singleton_iff.mpr (by norm_num)
  have hEq := hζan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hmem hev
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) (hEq h2mem)

/-- **The logarithmic derivative of `ζ` is not holonomic — unconditionally.**  The trivial
zeros supply the injective pole sequence; no simplicity input is needed, since the leading
Laurent datum `m_k·(-1)^j·j!` is nonvanishing for any vanishing order `m_k ≥ 1`. -/
theorem zetaLogDeriv_not_holonomic :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
      (∀ s : ℂ, ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j zetaLogDeriv s = 0) →
      ∀ j ∈ range (n + 1), c j = 0 := by
  have hinj : Function.Injective (fun k : ℕ => (-2 : ℂ) * ((k : ℂ) + 1)) := by
    intro a b hab
    simp only at hab
    have : ((a : ℂ)) = (b : ℂ) := by linear_combination (-(1 : ℂ) / 2) * hab
    exact_mod_cast this
  refine not_holonomic_master zetaLogDeriv _ hinj 1
    (fun i k => ((analyticOrderAt riemannZeta ((-2 : ℂ) * ((k : ℂ) + 1))).toNat : ℂ)
      * ((-1) ^ i * (i.factorial : ℂ)))
    (fun i k => ?_) (fun i k => ?_)
  · have hm1 : 1 ≤ (analyticOrderAt riemannZeta ((-2 : ℂ) * ((k : ℂ) + 1))).toNat := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have : analyticOrderAt riemannZeta ((-2 : ℂ) * ((k : ℂ) + 1)) = 0 := by
        rw [(ENat.coe_toNat (analyticOrderAt_riemannZeta_trivialZero_ne_top k)).symm, h0]
        rfl
      rcases analyticOrderAt_eq_zero.mp this with h | h
      · exact h (analyticAt_riemannZeta_trivialZero k)
      · exact h (riemannZeta_neg_two_mul_nat_add_one k)
    have hmne :
        ((analyticOrderAt riemannZeta ((-2 : ℂ) * ((k : ℂ) + 1))).toNat : ℂ) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hm1
    exact mul_ne_zero hmne
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast i.factorial_ne_zero))
  · have := logDeriv_iteratedDeriv_residue_of_zero (analyticAt_riemannZeta_trivialZero k)
      (analyticOrderAt_riemannZeta_trivialZero_ne_top k)
      (riemannZeta_neg_two_mul_nat_add_one k) i
    exact this

end RHTower
