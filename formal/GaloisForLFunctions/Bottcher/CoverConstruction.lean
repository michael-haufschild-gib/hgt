/-
# Toward the connected dyadic cover: local holomorphic Böttcher branches on the basin

The disconnected-case faithful field is the meromorphic function field of the **connected dyadic
cover** of the basin `Ω_c = ℂ ∖ K_c`, on which the multivalued `φ_c` becomes single-valued and the
deck group `μ_{2^∞}` acts (the `CoverMonodromy` algebra is the model). Over the escape region the
cover splits into disjoint sheets; it becomes connected only when continued down toward `J_c`, where
the dyadic monodromy glues the sheets.

This file builds the analytic raw material for that cover: at every basin point, since `G_c` is
harmonic there (`harmonicOnNhd_greenLimit_basin`), it is locally the real part of a holomorphic `F`
(the harmonic conjugate = the angle of `φ_c`), so `exp F` is a local single-valued branch of `φ_c`
past the escape region. The cover is assembled by gluing these local branches; the monodromy is the
`2πi·period` ambiguity of the conjugate around the Cantor cylinders.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import GaloisForLFunctions.Bottcher.Winding
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.OpenMapping

open Filter Topology Set Metric InnerProductSpace

namespace Bottcher

/-- **Local holomorphic Böttcher logarithm on the basin.** At any basin point `z ∉ K_c`, `G_c` is
harmonic, so on a ball it equals `Re F` for a holomorphic `F`; `exp F` is then a local single-valued
branch of `φ_c` (with `|exp F| = exp G_c = |φ_c|`) extending past the escape region. These local
branches are the sheets that glue — with `2πi·period` monodromy — into the connected dyadic cover. -/
theorem exists_local_greenConjugate_basin {c z : ℂ} (hz : z ∉ filledJulia c) :
    ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ AnalyticOnNhd ℂ F (ball z r) ∧
      EqOn (fun w => (F w).re) (greenLimit c) (ball z r) := by
  have hbo : IsOpen (filledJulia c)ᶜ := (isClosed_filledJulia c).isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hbo z hz
  have hharm : HarmonicOnNhd (greenLimit c) (ball z r) :=
    fun w hw => harmonicOnNhd_greenLimit_basin c w (hball hw)
  obtain ⟨F, hFan, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm
  exact ⟨r, F, hr, hFan, hFeq⟩

/-- The local branch `exp F` is **nowhere zero** and has modulus `exp(G_c) > 1` near `∞`-side levels:
`|exp F| = exp(Re F) = exp(G_c)`. So each sheet of the cover lands in `{|w| = exp(G_c)}`, the level
structure the deck group `μ_{2^∞}` rotates. -/
theorem norm_exp_greenConjugate {c : ℂ} {F : ℂ → ℂ} {w : ℂ}
    (hF : (F w).re = greenLimit c w) : ‖Complex.exp (F w)‖ = Real.exp (greenLimit c w) := by
  rw [Complex.norm_exp, hF]

/-- On the escape overlap, a local basin branch `exp F` has the **same modulus as the actual `φ_c`**:
`|exp F| = exp(G_c) = |φ_c|`. So each cover sheet agrees in modulus with `φ_c`; the sheets differ only
by the `μ_{2^∞}` phase — exactly the deck action. This ties the abstract `CoverMonodromy` sheets to
the genuine Böttcher coordinate. -/
theorem norm_exp_eq_norm_bottcher {c : ℂ} {F : ℂ → ℂ} {w : ℂ}
    (hF : (F w).re = greenLimit c w) (hw : w ∈ escapeOpen c) :
    ‖Complex.exp (F w)‖ = ‖bottcherCoord c w‖ := by
  rw [norm_exp_greenConjugate hF, ← greenLogNorm_eq_greenLimit_escape hw, greenLogNorm,
      Real.exp_log (norm_pos_iff.mpr (bottcherCoord_ne_zero c w))]

/-- **Deck cocycle: two local Böttcher branches differ by an imaginary constant.** On a connected
open overlap `U` of two local branches of `φ_c`, their green-conjugates `F₁, F₂` have the same real
part `G_c`, so `F₁ - F₂` is holomorphic with zero real part, hence a constant `a` with `Re a = 0`
(`AnalyticOnNhd.eq_const_of_re_eq_const` — open mapping). Thus `exp F₁ = exp a · exp F₂` with
`|exp a| = 1`: the two sheets differ by a unimodular factor — the `μ_{2^∞}` deck action. This is the
transition cocycle of the connected dyadic cover. -/
theorem greenConjugate_sub_imaginary_const {c : ℂ} {F₁ F₂ : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hF1 : AnalyticOnNhd ℂ F₁ U) (hF2 : AnalyticOnNhd ℂ F₂ U)
    (h1 : EqOn (fun w => (F₁ w).re) (greenLimit c) U)
    (h2 : EqOn (fun w => (F₂ w).re) (greenLimit c) U) :
    ∃ a : ℂ, a.re = 0 ∧ EqOn F₁ (fun w => F₂ w + a) U := by
  have hg : AnalyticOnNhd ℂ (fun w => F₁ w - F₂ w) U := hF1.sub hF2
  have hre : ∀ x ∈ U, (F₁ x - F₂ x).re = (0 : ℝ) := by
    intro z hz
    have e1 : (F₁ z).re = greenLimit c z := h1 hz
    have e2 : (F₂ z).re = greenLimit c z := h2 hz
    rw [Complex.sub_re, e1, e2, sub_self]
  obtain ⟨a, ha⟩ := AnalyticOnNhd.eq_const_of_re_eq_const hg hre hUo hUc
  refine ⟨a, ?_, fun w hw => ?_⟩
  · obtain ⟨z₀, hz₀⟩ := hUc.nonempty
    have e1 : (F₁ z₀).re = greenLimit c z₀ := h1 hz₀
    have e2 : (F₂ z₀).re = greenLimit c z₀ := h2 hz₀
    rw [← ha z₀ hz₀, Complex.sub_re, e1, e2, sub_self]
  · rw [← ha w hw]; ring

/-- **Functional equation at the green-conjugate level.** For a local branch's logarithm `F` (with
`Re F = G_c`), `Re F(f_c z) = 2·Re F(z)` — the Böttcher functional equation `φ_c(f_c z) = φ_c(z)²`
read off on the real part (`|·|`-level), via the scaling law `G_c∘f_c = 2 G_c`. Combined with the
deck cocycle, this gives `F(f_c z) = 2 F(z) + iθ`, so `exp F(f_c z) = (exp F z)²·(unimodular)`: the
dynamics `f_c` connects the cover's levels — the structure that makes the dyadic cover connected. -/
theorem greenConjugate_quadratic_re {c : ℂ} {F : ℂ → ℂ} {z : ℂ} (hz : z ∉ filledJulia c)
    (hFz : (F z).re = greenLimit c z)
    (hFfz : (F (quadratic c z)).re = greenLimit c (quadratic c z)) :
    (F (quadratic c z)).re = 2 * (F z).re := by
  rw [hFfz, greenLimit_quadratic_basin hz, hFz]

/-- **A local branch is a unimodular multiple of `φ_c`.** On a connected overlap `U ⊆ escapeOpen ∩
slitPlane`, a local green-conjugate `F` (`Re F = G_c`) and `bottcherLog` both have real part `G_c`,
so they differ by an imaginary constant `a` (cocycle). Hence `exp F = exp(a)·φ_c` with `|exp a| = 1`:
the cover sheet is `φ_c` up to a unimodular factor — confirming the sheets ARE the branches of the
genuine Böttcher coordinate (the `μ_{2^∞}` orbit), tying `CoverConstruction` to `bottcherCoord`. -/
theorem local_branch_eq_unimodular_bottcher {c : ℂ} {F : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U) (hUsub : U ⊆ escapeOpen c ∩ Complex.slitPlane)
    (hF : AnalyticOnNhd ℂ F U) (hFre : EqOn (fun w => (F w).re) (greenLimit c) U) :
    ∃ a : ℂ, a.re = 0 ∧
      EqOn (fun w => Complex.exp (F w)) (fun w => Complex.exp a * bottcherCoord c w) U := by
  have hblog_an : AnalyticOnNhd ℂ (bottcherLog c) U :=
    ((differentiableOn_bottcherLog c).analyticOnNhd
      ((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane)).mono hUsub
  have hblog_re : EqOn (fun w => (bottcherLog c w).re) (greenLimit c) U := by
    intro w hw
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime (hUsub hw).1
    exact bottcherLog_re hc hz2
  obtain ⟨a, ha0, ha⟩ := greenConjugate_sub_imaginary_const hUo hUc hF hblog_an hFre hblog_re
  refine ⟨a, ha0, fun w hw => ?_⟩
  simp only [ha hw, Complex.exp_add, bottcherCoord]
  ring

open Metric in
/-- **Local Böttcher branch on the basin.** At any basin point `z ∉ K_c`, there is a local
single-valued holomorphic branch `β = exp F` of `φ_c` on a ball: analytic, nowhere zero, with
`|β| = exp(G_c) = |φ_c|`. This is the Böttcher coordinate extended past the escape region (where the
series diverges), realized as a single-valued branch via the harmonic conjugate. The sheets of the
connected dyadic cover are these branches; gluing them (by the `μ_{2^∞}` cocycle) is the remaining
analysis-on-Riemann-surfaces step. -/
theorem exists_local_bottcherBranch_basin {c z : ℂ} (hz : z ∉ filledJulia c) :
    ∃ (r : ℝ) (β : ℂ → ℂ), 0 < r ∧ AnalyticOnNhd ℂ β (ball z r) ∧
      (∀ w ∈ ball z r, ‖β w‖ = Real.exp (greenLimit c w)) ∧ (∀ w ∈ ball z r, β w ≠ 0) := by
  obtain ⟨r, F, hr, hFan, hFre⟩ := exists_local_greenConjugate_basin hz
  refine ⟨r, fun w => Complex.exp (F w), hr, hFan.cexp, ?_, fun w _ => Complex.exp_ne_zero _⟩
  exact fun w hw => norm_exp_greenConjugate (hFre hw)

/-- **Iterated functional equation at the green-conjugate level.** `Re F(f_c^[n] z) = 2ⁿ·Re F(z)`
for a local branch logarithm `F` (`Re F = G_c`): the `n`-th iterate multiplies the level by `2ⁿ`, so
`exp F(f_c^[n] z) = (exp F z)^{2ⁿ}·(unimodular)` — the dyadic level tower (`φ_c^{2ⁿ} = φ_c∘f_c^[n]`)
realized on the cover, the structure the `μ_{2^∞}` deck group acts through. -/
theorem greenConjugate_iterate_re {c : ℂ} {F : ℂ → ℂ} {z : ℂ} (hz : z ∉ filledJulia c) (n : ℕ)
    (hFz : (F z).re = greenLimit c z)
    (hFnz : (F ((quadratic c)^[n] z)).re = greenLimit c ((quadratic c)^[n] z)) :
    (F ((quadratic c)^[n] z)).re = 2 ^ n * (F z).re := by
  rw [hFnz, greenLimit_iterate_basin hz n, hFz]

/-- **The deck group acts transitively on cover fibres.** Any two branches `v₁, v₂` of `φ_c` over the
same `z` (points of `bottcherPullbackSpace c n`) are related by a `2ⁿ`-th root of unity `ζ`:
`v₂ = ζ·v₁`. So the fibre is a single `μ_{2ⁿ}` deck orbit — transitivity, the key to the cover's
connectedness (a covering of a connected base with transitive monodromy has a connected total space). -/
theorem bottcherPullback_fiber_transitive {c : ℂ} {n : ℕ} {z v₁ v₂ : ℂ}
    (h₁ : (z, v₁) ∈ bottcherPullbackSpace c n) (h₂ : (z, v₂) ∈ bottcherPullbackSpace c n) :
    ∃ ζ : ℂ, ζ ^ (2 ^ n) = 1 ∧ v₂ = ζ * v₁ := by
  refine ⟨v₂ / v₁, bottcherPullback_fiber_deck h₂ h₁, ?_⟩
  rw [div_mul_cancel₀ _ h₁.2]

/-- `φ_c` is continuous on the escape region (analytic ⟹ continuous). -/
theorem continuousOn_bottcherCoord (c : ℂ) : ContinuousOn (bottcherCoord c) (escapeOpen c) :=
  (differentiableOn_bottcherCoord c).continuousOn

/-- **The Böttcher section into the common cover is continuous.** `s(z) = (z, φ_{c₁}(z), φ_{c₂}(z))`
is continuous on the common escape region; with `bottcher_mem_commonPullback` it is a continuous map
into the cover `commonPullback`, so its image (the principal sheet) is connected — a building block
for the connectedness of the total dyadic cover (with fibre transitivity supplying the cross-sheet
links). -/
theorem continuousOn_bottcherSection (c₁ c₂ : ℂ) :
    ContinuousOn (fun z => (z, bottcherCoord c₁ z, bottcherCoord c₂ z))
      (escapeOpen c₁ ∩ escapeOpen c₂) := by
  have h1 : ContinuousOn (bottcherCoord c₁) (escapeOpen c₁ ∩ escapeOpen c₂) :=
    (continuousOn_bottcherCoord c₁).mono inter_subset_left
  have h2 : ContinuousOn (bottcherCoord c₂) (escapeOpen c₁ ∩ escapeOpen c₂) :=
    (continuousOn_bottcherCoord c₂).mono inter_subset_right
  exact continuousOn_id.prodMk (h1.prodMk h2)

/-- `‖φ_c‖ = exp(G_c)` on the escape region. -/
theorem norm_bottcher_eq_exp_greenLimit {c w : ℂ} (hw : w ∈ escapeOpen c) :
    ‖bottcherCoord c w‖ = Real.exp (greenLimit c w) := by
  rw [← greenLogNorm_eq_greenLimit_escape hw, greenLogNorm,
      Real.exp_log (norm_pos_iff.mpr (bottcherCoord_ne_zero c w))]

/-- **The local branch realizes the dyadic level tower (modulus form).** For a local branch logarithm
`F` (`Re F = G_c`), `‖exp F(z)‖^{2ⁿ} = ‖φ_c(f_c^[n] z)‖`: the branch raised to `2ⁿ` matches the
single-valued `φ_c` at level `n` — the relation `v^{2ⁿ} = φ_c(f_c^[n] z)` defining the cover variety
`bottcherPullbackSpace`, here verified on the analytic branch (modulus), via the iterated scaling law. -/
theorem norm_exp_pow_eq_norm_bottcher_iterate {c : ℂ} {F : ℂ → ℂ} {z : ℂ} (hz : z ∉ filledJulia c)
    (n : ℕ) (hF : (F z).re = greenLimit c z)
    (hesc : (quadratic c)^[n] z ∈ escapeOpen c) :
    ‖Complex.exp (F z)‖ ^ (2 ^ n) = ‖bottcherCoord c ((quadratic c)^[n] z)‖ := by
  rw [norm_exp_greenConjugate hF, ← Real.exp_nat_mul, norm_bottcher_eq_exp_greenLimit hesc,
      greenLimit_iterate_basin hz n]
  congr 1; push_cast; ring

/-- **`f_c` doubles the Green level.** The map `f_c` sends the level set `{G_c = t}` (in the basin)
into `{G_c = 2t}`: the renormalization foliating `Ω_c` by levels, with the boundary `{G_c → 0} = J_c`
the natural boundary of `φ_c`. This level structure underlies both the dyadic cylinder/monodromy
(disconnected) and the natural-boundary rigidity (connected). -/
theorem mapsTo_greenLevel_quadratic (c : ℂ) (t : ℝ) :
    Set.MapsTo (quadratic c) {z | z ∉ filledJulia c ∧ greenLimit c z = t}
      {z | greenLimit c z = 2 * t} := by
  rintro z ⟨hz, hzt⟩
  rw [Set.mem_setOf_eq, greenLimit_quadratic_basin hz, hzt]

/-- **`f_c^[n]` multiplies the Green level by `2ⁿ`.** The `n`-th iterate sends `{G_c = t}` (in the
basin) into `{G_c = 2ⁿ t}`: the depth-`n` cylinder maps onto the critical collar, the `2ⁿ`-fold
covering whose monodromy is the order-`2ⁿ` dyadic multiplier. -/
theorem mapsTo_greenLevel_iterate (c : ℂ) (t : ℝ) (n : ℕ) :
    Set.MapsTo (quadratic c)^[n] {z | z ∉ filledJulia c ∧ greenLimit c z = t}
      {z | greenLimit c z = 2 ^ n * t} := by
  rintro z ⟨hz, hzt⟩
  rw [Set.mem_setOf_eq, greenLimit_iterate_basin hz n, hzt]

/-- **The local branch maps the basin into the exterior of the unit disk.** For a local branch
logarithm `F` (`Re F = G_c`) at a basin point, `1 < ‖exp F(z)‖` (since `G_c > 0` off `K_c`). So the
(multivalued) Böttcher coordinate sends `Ω_c` into `{|w| > 1}`, with the natural boundary `J_c`
mapping to the unit circle — the picture the natural-boundary rigidity (connected) and the dyadic
monodromy (disconnected) both rest on. -/
theorem one_lt_norm_localBranch {c : ℂ} {F : ℂ → ℂ} {z : ℂ} (hz : z ∉ filledJulia c)
    (hF : (F z).re = greenLimit c z) : 1 < ‖Complex.exp (F z)‖ := by
  rw [norm_exp_greenConjugate hF]
  exact Real.one_lt_exp_iff.mpr (greenLimit_pos_basin hz)

end Bottcher

namespace Bottcher

/-- **The cover fibre is exactly one `μ_{2ⁿ}`-orbit.** Over a basin point `z` (any `(z,v₀)` on the
cover), the full fibre `{v : (z,v) ∈ bottcherPullbackSpace}` equals the deck orbit `{ζ·v₀ : ζ^{2ⁿ}=1}`:
transitivity (`bottcherPullback_fiber_transitive`) gives `⊆`, deck-closure (`deckMap_mapsTo_bottcher`)
gives `⊇`. So the level-`n` cover is a `μ_{2ⁿ}`-torsor over each point — the unbranched degree-`2ⁿ`
covering structure whose transitive monodromy makes the connected total space connected (and hence its
function field a domain, the carrier `hDisc` needs). -/
theorem bottcherPullback_fiber_eq_orbit {c : ℂ} {n : ℕ} {z v₀ : ℂ}
    (h₀ : (z, v₀) ∈ bottcherPullbackSpace c n) (v : ℂ) :
    (z, v) ∈ bottcherPullbackSpace c n ↔ ∃ ζ : ℂ, ζ ^ (2 ^ n) = 1 ∧ v = ζ * v₀ := by
  constructor
  · intro hv
    exact bottcherPullback_fiber_transitive h₀ hv
  · rintro ⟨ζ, hζ, rfl⟩
    simpa [deckMap] using deckMap_mapsTo_bottcher (c := c) (n := n) hζ h₀

end Bottcher

namespace Bottcher

/-- **The deck action is free on the cover** (regular/Galois covering). If a `2ⁿ`-th root of unity `ζ`
fixes a cover point `(z,v)` — i.e. `ζ·v = v` with `v ≠ 0` — then `ζ = 1`. So `μ_{2ⁿ}` acts with trivial
stabilizers: the covering is regular. With `bottcherPullback_fiber_eq_orbit` (each fibre is one orbit)
this makes every fibre a **principal** `μ_{2ⁿ}`-torsor — the precise structure (free + transitive)
under which a transitive monodromy class connects all sheets into one connected total space. -/
theorem deckMap_free_on_cover {c : ℂ} {n : ℕ} {ζ z v : ℂ}
    (h : (z, v) ∈ bottcherPullbackSpace c n) (hfix : ζ * v = v) : ζ = 1 :=
  mul_right_cancel₀ h.2 (by rw [hfix, one_mul])

end Bottcher

namespace Bottcher

/-- **The local branch is a `2ⁿ`-th root of `φ_c∘f_c^[n]` (complex form).** Upgrading the modulus
relation `norm_exp_pow_eq_norm_bottcher_iterate` to the genuine complex equation: a local Böttcher
branch `exp F` on a connected `U ⊆ escapeOpen ∩ slitPlane` satisfies
`(exp F)^{2ⁿ} = exp b · (φ_c ∘ f_c^[n])` for a purely imaginary constant `b` (so the factor is
unimodular). This is the exact defining relation `v^{2ⁿ} = φ_c(f^[n]·)` of the cover variety
`bottcherPullbackSpace`, now on the analytic branch — the cover-variety equation the lift `hliftF`
must satisfy, here verified where `φ_c` is single-valued (the escape region); the genuine lift extends
this across `J_c` by analytic continuation. -/
theorem local_branch_pow_eq_bottcher_iterate {c : ℂ} {F : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U) (hUsub : U ⊆ escapeOpen c ∩ Complex.slitPlane)
    (hF : AnalyticOnNhd ℂ F U) (hFre : Set.EqOn (fun w => (F w).re) (greenLimit c) U) (n : ℕ) :
    ∃ b : ℂ, b.re = 0 ∧
      Set.EqOn (fun w => Complex.exp (F w) ^ (2 ^ n))
        (fun w => Complex.exp b * bottcherCoord c ((quadratic c)^[n] w)) U := by
  obtain ⟨a, ha0, ha⟩ := local_branch_eq_unimodular_bottcher hUo hUc hUsub hF hFre
  refine ⟨((2 ^ n : ℕ) : ℂ) * a, by rw [Complex.mul_re, ha0, Complex.natCast_im]; ring, fun w hw => ?_⟩
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime (hUsub hw).1
  have hexp : Complex.exp (F w) = Complex.exp a * bottcherCoord c w := ha hw
  simp only [hexp, mul_pow, ← Complex.exp_nat_mul, ← bottcherCoord_iterate hc hz2 n]

end Bottcher
namespace Bottcher

/-- **The cover fibre is the `μ_{2ⁿ}`-image of any point — the degree-`2ⁿ` regular covering.**
Restating `bottcherPullback_fiber_eq_orbit` as an explicit image: the fibre over `z` equals
`(· * v₀) '' {ζ | ζ^{2ⁿ}=1}`, the orbit of one point under the `2ⁿ`-th roots of unity. With
`deckMap_free_on_cover` (the action is free), this image is in bijection with `μ_{2ⁿ}`, so the fibre
has exactly `2ⁿ` points: the φ-pullback is an unbranched regular covering of the basin of degree `2ⁿ`.
This is the topological backbone whose connected total space (over the disconnected `K_c`, via the
transitive dyadic monodromy) is the carrier of the lift data `hliftF`. -/
theorem bottcherPullback_fiber_eq_rootsImage {c : ℂ} {n : ℕ} {z v₀ : ℂ}
    (h₀ : (z, v₀) ∈ bottcherPullbackSpace c n) :
    {v | (z, v) ∈ bottcherPullbackSpace c n} = (· * v₀) '' {ζ : ℂ | ζ ^ (2 ^ n) = 1} := by
  ext v
  rw [Set.mem_setOf_eq, bottcherPullback_fiber_eq_orbit h₀ v, Set.mem_image]
  constructor
  · rintro ⟨ζ, hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩
  · rintro ⟨ζ, hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩

end Bottcher

namespace Bottcher

/-- **The normalized Böttcher coordinate** `φ_c(z)/z = exp(Σₖ termₖ)` (`z ≠ 0`). Since `‖Σ‖ ≤ 2‖c‖/‖z‖²`
(`norm_bottcherLog_sub_log_le`), `φ_c(z)/z → exp 0 = 1` as `z → ∞`: `φ_c` is tangent to the identity at
`∞`, the normalization that makes it the *uniformizing* coordinate of the basin (a local
biholomorphism near `∞`), in which the cover lift `φ_{c₁} = w` is expressed. -/
theorem bottcherCoord_div_self {c z : ℂ} (hz : z ≠ 0) :
    bottcherCoord c z / z = Complex.exp (∑' k, bottcherLogTerm c z k) := by
  rw [bottcherCoord_eq_mul_exp hz, mul_comm, mul_div_assoc, div_self hz, mul_one]

end Bottcher

namespace Bottcher

/-- **The zero set of `d log φ_c` is forward-invariant.** From the self-similarity
`logDeriv φ_c (z) = z · logDeriv φ_c (f_c z)` and `z ≠ 0` on the escape set: `logDeriv φ_c` vanishes at
`z` iff it vanishes at `f_c z`. Since `f_c^[n] z → ∞` and `logDeriv φ_c ~ 1/w ≠ 0` near `∞`, no escape
point is a zero — so `dφ_c ≠ 0`, i.e. `φ_c` is a local biholomorphism on the escape set: the
uniformizing chart of the principal sheet (the `w`-coordinate of the cover). -/
theorem logDeriv_bottcherCoord_eq_zero_iff {c z : ℂ} (hz : z ∈ escapeOpen c) :
    logDeriv (bottcherCoord c) z = 0 ↔ logDeriv (bottcherCoord c) (quadratic c z) = 0 := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz2; linarith
  rw [logDeriv_bottcherCoord_self_similar hz, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hz0
    · exact h
  · intro h; right; exact h

end Bottcher

namespace Bottcher

/-- **Iterated forward-invariance of the `d log φ_c` zero set.** `logDeriv φ_c` vanishes at `z` iff it
vanishes at every iterate `f_c^[n] z`. Since `f_c^[n] z → ∞` (norm grows) and `logDeriv φ_c ~ 1/w` is
nonzero near `∞`, the right side fails for large `n` — so `logDeriv φ_c z ≠ 0` on the whole escape set,
giving the local injectivity of `φ_c` (nonzero derivative): the uniformizing chart of the cover's
principal sheet. -/
theorem logDeriv_bottcherCoord_iterate_eq_zero_iff {c z : ℂ} (hz : z ∈ escapeOpen c) (n : ℕ) :
    logDeriv (bottcherCoord c) z = 0 ↔ logDeriv (bottcherCoord c) ((quadratic c)^[n] z) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Function.iterate_succ', Function.comp_apply,
        logDeriv_bottcherCoord_eq_zero_iff (escapeOpen_iterate hz n)]

end Bottcher

namespace Bottcher

/-- **`d log φ_c = d(bottcherLog)`.** Since `φ_c = exp(bottcherLog c)`, the logarithmic derivative of
`φ_c` is just the ordinary derivative of its logarithm: `logDeriv φ_c z = deriv (bottcherLog c) z` on
the slit escape neighborhood. As `bottcherLog c = log z + Σ`, this is `1/z + deriv Σ`, which is `~ 1/z`
(nonzero) near `∞` — the explicit handle for `φ_c`'s local injectivity (the uniformizing chart). -/
theorem logDeriv_bottcherCoord_eq {c z : ℂ} (hz : z ∈ escapeOpen c ∩ Complex.slitPlane) :
    logDeriv (bottcherCoord c) z = deriv (bottcherLog c) z := by
  have hdiff : DifferentiableAt ℂ (bottcherLog c) z :=
    (differentiableOn_bottcherLog c).differentiableAt
      (((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane).mem_nhds hz)
  have hderiv : HasDerivAt (bottcherCoord c)
      (bottcherCoord c z * deriv (bottcherLog c) z) z := hdiff.hasDerivAt.cexp
  rw [logDeriv_apply, hderiv.deriv, mul_comm, mul_div_assoc,
      div_self (bottcherCoord_ne_zero c z), mul_one]

end Bottcher


namespace Bottcher

/-- **The deck transition constant is a `2ⁿ`-th root of unity.** If two cover branches differ by a
constant factor `ζ = exp a` (the unimodular cocycle of `greenConjugate_sub_imaginary_const`) and both
satisfy the cover relation `β^{2ⁿ} = φ_c∘f^[n]` at a point — so `(ζ·v)^{2ⁿ} = v^{2ⁿ}` with `v ≠ 0` —
then `ζ^{2ⁿ} = 1`. So the `U(1)`-cocycle of the branches is actually `μ_{2ⁿ}`-valued: this is exactly
what makes the dyadic cover a **finite** (degree-`2ⁿ`) regular covering, the structure
`CoverMonodromy`'s deck group acts through. -/
theorem deck_const_root_of_unity {ζ v : ℂ} {n : ℕ} (hv : v ≠ 0)
    (hpow : (ζ * v) ^ (2 ^ n) = v ^ (2 ^ n)) : ζ ^ (2 ^ n) = 1 := by
  rw [mul_pow] at hpow
  exact mul_right_cancel₀ (pow_ne_zero _ hv) (by rw [one_mul]; exact hpow)

end Bottcher

namespace Bottcher

/-- **The tower's defining relation: `g_{n+1} = g_n²`.** `φc∘f^[n+1] = (φc∘f^[n])²` on the escape set
(the Böttcher functional equation iterated). So `g_{n+1} = g_n²`: the level-`(n+1)` Kummer element is
the square of the level-`n` one, which is exactly what makes the cover an **iterated degree-2 tower**
(each level a square-root extension of the previous), and what makes the realized periods halve
(`pathInt_iterate_comp`). The structural backbone of the 2^∞ tower. -/
theorem bottcherCoord_iterate_succ {c z : ℂ} (hz : z ∈ escapeOpen c) (n : ℕ) :
    bottcherCoord c ((quadratic c)^[n + 1] z) = (bottcherCoord c ((quadratic c)^[n] z)) ^ 2 := by
  rw [Function.iterate_succ', Function.comp_apply]
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime (escapeOpen_iterate hz n)
  exact bottcherCoord_quadratic hc hz2

end Bottcher

namespace Bottcher

/-- **Winding-scaling: `g = φc^{2ⁿ}` winds `2ⁿ×` `φc`.** `logDeriv (φc^k) = k · logDeriv φc` on the
escape set. Integrated around a loop, `∮ d log(φc∘f^[n]) = ∮ d log(φc^{2ⁿ}) = 2ⁿ ∮ d log φc =
2ⁿ·(2πi/2ⁿ) = 2πi` (the realized dyadic period `pathInt_iterate_comp` gives `∮ d log φc = 2πi/2ⁿ`).
So `g` has winding `1` (odd) — exactly the input `not_square_of_odd_period` needs to conclude `g` is
not a square. The contour-wiring link between the verified period and the algebraic non-square. -/
theorem logDeriv_bottcherCoord_pow {c z : ℂ} (hz : z ∈ escapeOpen c) (k : ℕ) :
    logDeriv (fun w => (bottcherCoord c w) ^ k) z = (k : ℂ) * logDeriv (bottcherCoord c) z :=
  logDeriv_fun_pow ((differentiableOn_bottcherCoord c).differentiableAt
    ((isOpen_escapeOpen c).mem_nhds hz)) k

end Bottcher


namespace Bottcher

/-- **A square's winding is `2×`: `d log(h²) = 2·d log h`.** The "even half" of the argument-principle
bridge: integrated, `∮ d log(h²) = 2 ∮ d log h`, so any square `g = h²` of a single-valued analytic
`h` has *even* winding. Since `g = φc∘f^[n]` has winding `1` (odd) around the deep pullback loop (the
realized dyadic period `2πi/2ⁿ` × `2ⁿ`), `g` is not such a square — what `not_square_of_odd_period`
formalizes. The missing companion (`∮ d log h ∈ 2πiℤ` for single-valued nonzero `h`, the integer-winding
argument principle) is the one piece absent from current Mathlib. -/
theorem logDeriv_sq {h : ℂ → ℂ} {x : ℂ} (hd : DifferentiableAt ℂ h x) :
    logDeriv (fun w => (h w) ^ 2) x = 2 * logDeriv h x := by
  rw [logDeriv_fun_pow hd 2]; norm_num

end Bottcher

namespace Bottcher

/-- **Closed-loop fundamental theorem (argument-principle core).** If `I` is an antiderivative of the
logarithmic derivative `φ'/φ` of a nonvanishing differentiable path `φ` on `[a,b]`, then
`exp(I b − I a) = φ b / φ a`. Proof: `ψ = φ·exp(−I)` has derivative `0` (`ψ' = φ'·exp(−I) −
φ·(φ'/φ)·exp(−I) = 0`), so by the FTC `ψ b = ψ a`, i.e. `φ a·exp(−I a) = φ b·exp(−I b)`. For a
**closed loop** (`φ b = φ a`) this gives `exp(∮ d log φ) = exp(I b − I a) = 1` — exactly the
hypothesis the integer-winding lemma `winding_integer_of_exp_eq_one` consumes, hence (with the realized
odd period `2πi`) the per-level non-square `not_square_of_period_ftc`. Machine-checked, no axioms. -/
theorem exp_logDeriv_antiderivative {φ I : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ∀ t ∈ Set.Icc a b, φ t ≠ 0)
    (hdφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (deriv φ t) t)
    (hI : ∀ t ∈ Set.Icc a b, HasDerivAt I (deriv φ t / φ t) t) :
    Complex.exp (I b - I a) = φ b / φ a := by
  have hψd : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => φ s * Complex.exp (-(I s))) 0 t := by
    intro t ht
    have hne : φ t ≠ 0 := hφ t ht
    have h3 := (hdφ t ht).mul ((hI t ht).neg.cexp)
    convert h3 using 1
    field_simp
    ring
  have hψeq2 : φ a * Complex.exp (-(I a)) = φ b * Complex.exp (-(I b)) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hψd t (by rwa [Set.uIcc_of_le hab] at ht)) intervalIntegrable_const
    simp only [intervalIntegral.integral_zero] at h
    linear_combination h
  have ha := hφ a (Set.left_mem_Icc.mpr hab)
  have e2 : Complex.exp (I b) * Complex.exp (-(I b)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have e3 : Complex.exp (I b - I a) = Complex.exp (I b) * Complex.exp (-(I a)) := by
    rw [← Complex.exp_add, sub_eq_add_neg]
  rw [eq_div_iff ha, e3]
  linear_combination Complex.exp (I b) * hψeq2 + φ b * e2

end Bottcher

namespace Bottcher

/-- **Period-halving for a square (contour form).** The parametrized contour integral of `d log(h²)`
over a loop `γ` is `2·∮ d log h` — the integral analog of the pointwise `logDeriv_sq`. So if the
hypothetical single-valued square root `h` of `g` exists on a neighbourhood of the deep loop, the
period of `g = h²` is exactly twice the period of `h`. Combined with the realized **odd** period of `g`
(`circleIntegral_dlog_bottcher` = `2πi`, scaled by `pathInt_iterate_comp`) this gives `2πi = 2·ph`,
and the closed-loop FTC (`exp_logDeriv_antiderivative` ⟹ `exp ph = 1`) then triggers
`not_square_of_period_ftc` — the per-level non-square. Same proof shape as `pathInt_comp_quadratic`. -/
theorem pathInt_logDeriv_sq {h : ℂ → ℂ} {γ γ' : ℝ → ℂ}
    (hd : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), DifferentiableAt ℂ h (γ θ)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * γ' θ)
      = 2 * ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (γ θ) * γ' θ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hsq := logDeriv_sq (hd θ hθ)
  simp only
  rw [hsq]; ring

end Bottcher

namespace Bottcher

/-- **Argument principle for a closed loop: the winding number is an integer.** For a closed
(`φ(2π)=φ(0)`), nowhere-zero, differentiable path `φ` with `L` an antiderivative of its logarithmic
derivative `φ'/φ`, the total change `L(2π)−L(0) = ∮ d log φ` is an integer multiple of `2πi`. Proof:
the closed-loop FTC (`exp_logDeriv_antiderivative`) gives `exp(L(2π)−L(0)) = φ(2π)/φ(0) = 1`, and
`Complex.exp_eq_one_iff` reads off the integer. This is the genuine **integer winding number** — the
heart of the argument principle — realized for an arbitrary smooth loop, axiom-clean. Specialized to a
hypothetical single-valued root `h` of `φ_c^{2ⁿ}` on the deep loop (whose realized period is the odd
`2πi`), the even-vs-odd parity gives the per-level non-square. -/
theorem pathWinding_integer {φ L : ℝ → ℂ}
    (hclosed : φ (2 * Real.pi) = φ 0)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), φ t ≠ 0)
    (hdφ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt φ (deriv φ t) t)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt L (deriv φ t / φ t) t) :
    ∃ k : ℤ, L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hexp := exp_logDeriv_antiderivative hpi hφ hdφ hL
  rw [hclosed, div_self (hφ 0 (Set.left_mem_Icc.mpr hpi))] at hexp
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨k, hk⟩ := hexp
  exact ⟨k, by rw [hk]; ring⟩

end Bottcher

namespace Bottcher

/-- **Dyadic monodromy is nontrivial (no single-valued branch).** A closed, nowhere-zero,
differentiable path `φ` whose logarithmic-derivative period is the realized dyadic value `2πi/2ⁿ`
(`n ≥ 1`) cannot exist: `pathWinding_integer` forces that period into `2πiℤ`, but `2πi/2ⁿ = 2πi·k`
gives `1 = k·2ⁿ`, impossible for `n ≥ 1` (`2ⁿ ∣ 1`). This is exactly why the dyadic cover has
**nontrivial monodromy of order `2ⁿ`** at level `n`: the Böttcher coordinate `φ_c` pulled back to the
`n`-fold deep loop has period `2πi/2ⁿ` (`circleIntegral_dlog_bottcher` ÷ `pathInt_iterate_comp`
scaling), so no single-valued branch closes up — the sheets are genuinely permuted by `μ_{2ⁿ}`. The
obstruction certifying the carrier's deck order is unbounded. Axiom-clean. -/
theorem no_singlevalued_branch_of_dyadic_period {φ L : ℝ → ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hperiod : L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I / (2 ^ n))
    (hclosed : φ (2 * Real.pi) = φ 0)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), φ t ≠ 0)
    (hdφ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt φ (deriv φ t) t)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt L (deriv φ t / φ t) t) :
    False := by
  obtain ⟨k, hk⟩ := pathWinding_integer hclosed hφ hdφ hL
  rw [hperiod] at hk
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨by norm_num, hpi⟩, Complex.I_ne_zero⟩
  have h2n : ((2 : ℂ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [div_eq_iff h2n] at hk
  have h1 : (2 * (Real.pi : ℂ) * Complex.I) * 1
      = (2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * 2 ^ n) := by linear_combination hk
  have h2 := mul_left_cancel₀ hne h1
  have h3 : (1 : ℤ) = k * 2 ^ n := by exact_mod_cast h2
  have hdvd : (2 : ℤ) ^ n ∣ 1 := ⟨k, by rw [mul_comm]; exact h3⟩
  have hle := Int.le_of_dvd (by norm_num) hdvd
  have hge : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := by apply pow_le_pow_right₀ (by norm_num) hn
  omega

end Bottcher
