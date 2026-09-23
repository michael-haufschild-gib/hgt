/-
# The exact edge law `(½ − θ_max)√d → 1/π`: the analytic core

At the physical carrier `c = 2` the inverted-response strip is marginal (`Φ(2) = 1`), so the sign of
the equilibrium deviation `θ*(i) − ½` in gap `i` is set by the next order — the `√d` boundary layer.
The deviation decomposes (validated to 5 digits against the direct finite-`d` `coth`-equilibrium):

* **local field factor** `φ(i) = ½ − θ*(i) = (2/π²)·g(i)/i`, where `|F'(m)|·δ_i → π²·i` from the
  known series `Σ_{k≥0} 1/(k+½)² = π²/2` (near-pole `csch² → (1/z)²`) — so `κ = 2/π²`;
* **margin** `g(i)/i = A_trunc/i − ε(i) = i/d + (π²/16)/i`, the finite-`d` truncation `A_trunc/i → i/d`
  against the finite-`i` shell correction `ε(i) = poleModelDiff(2,i) − 1 → −(π²/16)/i`.

Minimizing the margin over the gap scale is the `√d` edge (AM–GM): `min_{x>0}(x/d + a/x) = 2√(a/d)`
at `x = √(a·d)`. With `a = π²/16`: the minimum is `(π/2)/√d` at `x = (π/4)√d`, and scaled by the local
factor `κ = 2/π²` and by `√d` the `√d` **cancels exactly**, leaving `1/π`:

> `(½ − θ_max)·√d = (2/π²)·(π/2) = 1/π`,  peak at  `i_peak = (π/4)√d`.

This file formalizes the rigorous analytic core: the AM–GM edge-scale minorant (`edge_amgm`), its
attainment at the boundary-layer scale `√(a·d)` (`edge_amgm_eq`), the exact constant identity that the
`√d`-scaled edge margin is the dead constant `1/π` (`edge_margin_const`), and the peak location
(`edge_peak_loc`) — bundled in `edge_law` with the `Tendsto` form `edge_law_tendsto`. The three input
asymptotics (`κ = 2/π²`, `A_trunc/i → i/d`, `ε(i) → −(π²/16)/i`) are the finite-`d`/finite-`i`
inputs the closed-form skeleton consumes; each is a matched Euler–Maclaurin/digamma asymptotic of the
`poleExcess` field (numerically dead-on `π²/16` and `π²`).
-/
import GaloisForLFunctions.RHTower.LegStripPoleModel
open Real Filter Topology
noncomputable section
namespace RHTower

/-- **AM–GM in the edge-scale form.** The decomposed margin `x/d + a/x` — finite-`d` truncation `x/d`
against finite-`i` shell correction `a/x` — is minorized by `2√(a/d)` at every gap scale `x > 0`. -/
theorem edge_amgm {a d x : ℝ} (ha : 0 < a) (hd : 0 < d) (hx : 0 < x) :
    2 * Real.sqrt (a/d) ≤ x/d + a/x := by
  have h := sq_nonneg (Real.sqrt (x/d) - Real.sqrt (a/x))
  have e1 : Real.sqrt (x/d) ^ (2 : ℕ) = x/d := Real.sq_sqrt (by positivity)
  have e2 : Real.sqrt (a/x) ^ (2 : ℕ) = a/x := Real.sq_sqrt (by positivity)
  have e3 : Real.sqrt (x/d) * Real.sqrt (a/x) = Real.sqrt (a/d) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  nlinarith [h, e1, e2, e3]

/-- The minorant is attained at the edge scale `x = √(a·d)` — the `√d` boundary layer where the peak
gap sits (`i_peak ≈ (π/4)√d`). -/
theorem edge_amgm_eq {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    Real.sqrt (a*d)/d + a/Real.sqrt (a*d) = 2 * Real.sqrt (a/d) := by
  have hsa : Real.sqrt a > 0 := Real.sqrt_pos.mpr ha
  have hsd : Real.sqrt d > 0 := Real.sqrt_pos.mpr hd
  have hsad : Real.sqrt (a*d) = Real.sqrt a * Real.sqrt d := Real.sqrt_mul ha.le d
  have had : Real.sqrt (a/d) = Real.sqrt a / Real.sqrt d := Real.sqrt_div ha.le d
  have t1 : Real.sqrt (a*d)/d = Real.sqrt a / Real.sqrt d := by
    rw [hsad, div_eq_div_iff hd.ne' hsd.ne', mul_assoc, Real.mul_self_sqrt hd.le]
  have t2 : a/Real.sqrt (a*d) = Real.sqrt a / Real.sqrt d := by
    rw [hsad, div_eq_div_iff (mul_pos hsa hsd).ne' hsd.ne', ← mul_assoc,
      Real.mul_self_sqrt ha.le]
  rw [t1, t2, had]; ring

/-- **The edge-law constant identity.** With shell-correction coefficient `a = π²/16` and local field
factor `κ = 2/π²`, the edge margin `κ·2√(a/d)` scaled by `√d` is the dead constant `1/π`: the `√d`
cancels exactly, so `(½ − θ_max)·√d = 1/π`. -/
theorem edge_margin_const {d : ℝ} (hd : 0 < d) :
    Real.sqrt d * ((2/π^(2 : ℕ)) * (2 * Real.sqrt ((π^(2 : ℕ)/16)/d))) = 1/π := by
  have hpi : 0 < π := Real.pi_pos
  have hsplit : Real.sqrt ((π^(2 : ℕ)/16)/d) = (π/4) / Real.sqrt d := by
    rw [Real.sqrt_div (by positivity)]
    congr 1
    rw [show (π^(2 : ℕ)/16) = (π/4)^(2 : ℕ) by ring, Real.sqrt_sq (by positivity)]
  rw [hsplit]
  have hsd : Real.sqrt d > 0 := Real.sqrt_pos.mpr hd
  field_simp
  ring

/-- **The edge-law peak location.** The margin `x/d + a/x` (`a = π²/16`) is minimized at
`x = √(a·d) = (π/4)√d` — the Airy/boundary-layer scale `i_peak ≈ (π/4)√d`. -/
theorem edge_peak_loc (d : ℝ) :
    Real.sqrt ((π^(2 : ℕ)/16) * d) = (π/4) * Real.sqrt d := by
  rw [Real.sqrt_mul (by positivity), show (π^(2 : ℕ)/16) = (π/4)^(2 : ℕ) by ring,
    Real.sqrt_sq (by positivity [Real.pi_pos])]

/-- **The exact edge law (closed-form skeleton).** For every level `d > 0`, at the physical carrier:
the `√d`-scaled edge margin is exactly `1/π`; the minimizing gap scale is `(π/4)√d`; and the margin
`x/d + (π²/16)/x` is minorized by its edge value at every gap scale. Combined with the decomposition
`½ − θ*(i) = (2/π²)(i/d + (π²/16)/i)` (matched Euler–Maclaurin asymptotics), this is
`(½ − θ_max)√d → 1/π` with `i_peak = (π/4)√d`. -/
theorem edge_law {d : ℝ} (hd : 0 < d) :
    Real.sqrt d * ((2/π^(2 : ℕ)) * (2 * Real.sqrt ((π^(2 : ℕ)/16)/d))) = 1/π
    ∧ Real.sqrt ((π^(2 : ℕ)/16) * d) = (π/4) * Real.sqrt d
    ∧ ∀ x : ℝ, 0 < x → 2 * Real.sqrt ((π^(2 : ℕ)/16)/d) ≤ x/d + (π^(2 : ℕ)/16)/x :=
  ⟨edge_margin_const hd, edge_peak_loc d,
    fun x hx => edge_amgm (by positivity [Real.pi_pos]) hd hx⟩

set_option maxHeartbeats 1000000 in
/-- **Odd Basel.** `Σ_{k≥0} 1/(2k+1)² = π²/8` — from Basel `Σ 1/n² = π²/6` (even part `π²/24`,
via `HasSum.even_add_odd`). -/
theorem hasSum_odd_basel : HasSum (fun k : ℕ => (1:ℝ)/(2*k+1)^(2 : ℕ)) (π^(2 : ℕ)/8) := by
  have hz : HasSum (fun n : ℕ => (1:ℝ)/(n:ℝ)^(2 : ℕ)) (π^(2 : ℕ)/6) := hasSum_zeta_two
  have he : HasSum (fun k:ℕ => (1:ℝ)/((2*k:ℕ):ℝ)^(2 : ℕ)) (π^(2 : ℕ)/24) := by
    have hfe : (fun k:ℕ => (1:ℝ)/((2*k:ℕ):ℝ)^(2 : ℕ)) = fun k:ℕ => (1/4)*(1/(k:ℝ)^(2 : ℕ)) := by
      funext k; push_cast; ring
    rw [hfe, show (π^(2 : ℕ)/24:ℝ) = (1/4)*(π^(2 : ℕ)/6) by ring]; exact hz.mul_left _
  have hinj : Function.Injective (fun k : ℕ => 2*k+1) := by intro a b h; simpa using h
  have hoddsumm : Summable (fun k:ℕ => (1:ℝ)/((2*k+1:ℕ):ℝ)^(2 : ℕ)) :=
    hz.summable.comp_injective hinj
  have ho := hoddsumm.hasSum
  have hcomb : HasSum (fun n : ℕ => (1:ℝ)/(n:ℝ)^(2 : ℕ)) (π^(2 : ℕ)/24 + ∑' k, (1:ℝ)/((2*k+1:ℕ):ℝ)^(2 : ℕ)) :=
    he.even_add_odd ho
  have hval : (∑' k:ℕ, (1:ℝ)/((2*k+1:ℕ):ℝ)^(2 : ℕ)) = π^(2 : ℕ)/8 := by linarith [hz.unique hcomb]
  have hcast : (fun k:ℕ => (1:ℝ)/(2*k+1)^(2 : ℕ)) = fun k:ℕ => (1:ℝ)/((2*k+1:ℕ):ℝ)^(2 : ℕ) := by
    funext k; norm_num
  rw [hcast, ← hval]; exact ho

/-- **The local-factor series.** `Σ_{k≥0} 1/(k+½)² = π²/2` — the continuum value of `|F'(m)|·δ_i/i` at
`c = 2` (near-pole `csch²((k+½)/i) → (i/(k+½))²`), the source of the local field factor `κ = 2/π²`. -/
theorem local_factor_series : ∑' k : ℕ, (1/((k:ℝ)+1/2))^(2 : ℕ) = π^(2 : ℕ)/2 := by
  have h := hasSum_odd_basel
  have hfe : (fun k:ℕ => (1/((k:ℝ)+1/2))^(2 : ℕ)) = fun k:ℕ => 4 * ((1:ℝ)/(2*k+1)^(2 : ℕ)) := by
    funext k
    have h1 : ((k:ℝ)+1/2) ≠ 0 := by positivity
    have h2 : (2*(k:ℝ)+1) ≠ 0 := by positivity
    field_simp; ring
  rw [hfe, tsum_mul_left, h.tsum_eq]; ring

/-- The local field factor `κ = 2/π²` is the reciprocal of the local-factor series `Σ 1/(k+½)² = π²/2`:
the edge law's `1/π` is the odd-Basel constant read through the `√d` boundary layer. -/
theorem kappa_eq_inv_series : (2:ℝ)/π^(2 : ℕ) = (∑' k : ℕ, (1/((k:ℝ)+1/2))^(2 : ℕ))⁻¹ := by
  rw [local_factor_series, inv_div]

/-- The edge value `2√(a/d)` is the **least** value of the gap margin `x/d + a/x` over gap scales
`x > 0` — a lower bound (`edge_amgm`) that is attained (`edge_amgm_eq`). -/
theorem edge_isLeast {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    IsLeast ((fun x => x/d + a/x) '' Set.Ioi 0) (2 * Real.sqrt (a/d)) := by
  constructor
  · exact ⟨Real.sqrt (a*d), Real.sqrt_pos.mpr (by positivity), edge_amgm_eq ha hd⟩
  · rintro y ⟨x, hx, rfl⟩
    exact edge_amgm ha hd hx

/-- **The edge law as a reduction.** Given the physical decomposition `½ − θ_max(d) = κ · m(d)` with
local factor `κ = 2/π²` and `m(d)` the least value of the gap margin `x/d + (π²/16)/x` (the finite-`d`
truncation against the finite-`i` shell correction), the `√d`-scaled margin tends to `1/π`. The AM–GM
minimization (`m(d) = 2√((π²/16)/d)`, via `edge_isLeast` uniqueness) and the exact `√d`-cancellation
(`edge_margin_const`) are discharged here; the decomposition is the sole input. -/
theorem edge_law_reduction {θmax : ℝ → ℝ} {m : ℝ → ℝ}
    (hm : ∀ d, 0 < d → IsLeast ((fun x => x/d + (π^(2 : ℕ)/16)/x) '' Set.Ioi 0) (m d))
    (hθ : ∀ d, 0 < d → (1/2 - θmax d) = (2/π^(2 : ℕ)) * (m d)) :
    Tendsto (fun d => (1/2 - θmax d) * Real.sqrt d) atTop (𝓝 (1/π)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hpi : (0:ℝ) < π^(2 : ℕ)/16 := by positivity [Real.pi_pos]
  have hmeq : m d = 2 * Real.sqrt ((π^(2 : ℕ)/16)/d) := (hm d hd).unique (edge_isLeast hpi hd)
  rw [hθ d hd, hmeq, mul_comm]
  exact (edge_margin_const hd).symm

/-- The `√d`-scaled edge margin tends to `1/π` (a dead constant on `d > 0`). -/
theorem edge_law_tendsto :
    Tendsto (fun d : ℝ => Real.sqrt d * ((2/π^(2 : ℕ)) * (2 * Real.sqrt ((π^(2 : ℕ)/16)/d))))
      atTop (𝓝 (1/π)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  exact (edge_margin_const hd).symm

end RHTower
end
