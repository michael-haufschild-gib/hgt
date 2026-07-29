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
import Mathlib.Topology.Covering.Basic
import GaloisForLFunctions.Bottcher.MeromorphicField

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
    rw [show (fun s => φ s * Complex.exp (-(I s))) =
        φ * fun s => Complex.exp (-(I s)) by
      funext s
      rfl]
    apply h3.congr_deriv
    field_simp [hne]
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

namespace Bottcher
open Set

/-- **Atomic analytic gluing.** Two local analytic branches `f₁` on `U₁`, `f₂` on `U₂` that **agree on
the overlap** `U₁∩U₂` glue to a single analytic function `U₁.piecewise f₁ f₂` on `U₁∪U₂`. (On `U₁` it
is `f₁`, on `U₂` it is `f₂` — well-defined and analytic by the agreement, using openness so each point
has a one-branch neighbourhood.) This is the inductive engine for assembling the local Böttcher branches
(`exists_local_bottcherBranch_basin`) into a single-valued lift on the connected dyadic cover: iterate
the glue along a chain of patches whose transition cocycle is trivialized on the cover. -/
theorem analyticOnNhd_glue {U₁ U₂ : Set ℂ} {f₁ f₂ : ℂ → ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hf₁ : AnalyticOnNhd ℂ f₁ U₁) (hf₂ : AnalyticOnNhd ℂ f₂ U₂)
    (hagree : EqOn f₁ f₂ (U₁ ∩ U₂)) :
    haveI := Classical.dec
    AnalyticOnNhd ℂ (U₁.piecewise f₁ f₂) (U₁ ∪ U₂) := by
  classical
  rintro z (hz | hz)
  · refine (hf₁ z hz).congr ?_
    filter_upwards [hU₁.mem_nhds hz] with w hw
    simp [Set.piecewise, hw]
  · refine (hf₂ z hz).congr ?_
    filter_upwards [hU₂.mem_nhds hz] with w hw
    by_cases hw1 : w ∈ U₁
    · simp [Set.piecewise, hw1, hagree ⟨hw1, hw⟩]
    · simp [Set.piecewise, hw1]

end Bottcher

namespace Bottcher
open Set

/-- **Gluing two green-conjugate branches across the cocycle.** The local Böttcher-logarithm branches
`F₁, F₂` differ by an **imaginary constant** `c` on their overlap (`greenConjugate_sub_imaginary_const`:
`F₁ = F₂ + c`). Adjusting `F₂` by `c` makes them agree, so `analyticOnNhd_glue` produces a single
analytic branch `F` on `U₁∪U₂` with `exp F` a single-valued Böttcher coordinate there. Iterating this
glue along a chain of patches around the cover annulus assembles the global single-valued lift `φ̃c =
exp F` — the genuine lift the disconnected case needs — the closing-up obstruction being exactly the
total period `2πi/2ⁿ` that the `2ⁿ`-fold cover unwinds (`no_singlevalued_branch_of_dyadic_period`). -/
theorem analyticOnNhd_glue_cocycle {U₁ U₂ : Set ℂ} {F₁ F₂ : ℂ → ℂ} {c : ℂ}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hF₁ : AnalyticOnNhd ℂ F₁ U₁) (hF₂ : AnalyticOnNhd ℂ F₂ U₂)
    (hcoc : EqOn F₁ (fun w => F₂ w + c) (U₁ ∩ U₂)) :
    haveI := Classical.dec
    AnalyticOnNhd ℂ (U₁.piecewise F₁ (fun w => F₂ w + c)) (U₁ ∪ U₂) :=
  analyticOnNhd_glue hU₁ hU₂ hF₁ (hF₂.add analyticOnNhd_const) hcoc

end Bottcher

namespace Bottcher
open Set

/-- **Multiplicative gluing of Böttcher branches (period-absorbing).** The local Böttcher branches
`β₁ = exp F₁`, `β₂ = exp F₂` are related on their overlap by a **unit constant** `u = exp c`
(`β₁ = u·β₂`, from the additive cocycle `F₁ = F₂ + c`). They glue to a single analytic `φ̃c` on
`U₁∪U₂`. The key over the additive version: `exp` **absorbs the `2πi`-period** — even where `F` jumps by
`2πi` between overlap components, `β = exp F` is unchanged (`exp(F+2πi)=exp F`), so the multiplicative
cocycle `u_i = exp(c_i)` is what must close up: `∏ u_i = exp(∑ c_i) = exp(period)`. Around the `2ⁿ`-fold
cover the period is `2πi` (`no_singlevalued_branch_of_dyadic_period`), so `∏ u_i = exp(2πi) = 1` and the
glued `φ̃c` is single-valued — the genuine lift, with the deck rotation scaling it by `ζ`. -/
theorem analyticOnNhd_glue_unit {U₁ U₂ : Set ℂ} {β₁ β₂ : ℂ → ℂ} {u : ℂ}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hβ₁ : AnalyticOnNhd ℂ β₁ U₁) (hβ₂ : AnalyticOnNhd ℂ β₂ U₂)
    (hcoc : EqOn β₁ (fun w => u * β₂ w) (U₁ ∩ U₂)) :
    haveI := Classical.dec
    AnalyticOnNhd ℂ (U₁.piecewise β₁ (fun w => u * β₂ w)) (U₁ ∪ U₂) :=
  analyticOnNhd_glue hU₁ hU₂ hβ₁ (analyticOnNhd_const.mul hβ₂) hcoc

end Bottcher

namespace Bottcher
open Set Complex

/-- **The deck scaling DERIVES from the lift's existence.** This is the analytic fact aesop cannot
synthesize — but it is not an independent input: once the single-valued green-conjugate `F = log φ̃c`
exists on the connected cover `U` and the deck `ρ` preserves the modulus (`Re(F∘ρ) = Re F`, since the
deck fixes the projection and `Re F = G_c∘p` is a projection-pullback), the ratio `φ̃c∘ρ / φ̃c = exp(F∘ρ
− F)` has constant real part `0`, so `F∘ρ − F` is an imaginary constant `a` (open mapping,
`AnalyticOnNhd.eq_const_of_re_eq_const`), giving `φ̃c∘ρ = ζ·φ̃c` with `ζ = exp a`, `|ζ| = 1`. So the
`hliftF` scaling `a₁∘g = ζ₀·a₁` reduces to the **existence** of the single-valued lift `φ̃c = exp F` on
the connected cover — the sole genuine remaining analytic input, the global gluing
(`analyticOnNhd_glue_unit`) where the period unwinds. -/
theorem scaling_from_modulus_preserved {U : Set ℂ} {F : ℂ → ℂ} {ρ : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hF : AnalyticOnNhd ℂ F U) (hρ : AnalyticOnNhd ℂ ρ U) (hmaps : Set.MapsTo ρ U U)
    (hmod : ∀ w ∈ U, (F (ρ w)).re = (F w).re) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ w ∈ U, Complex.exp (F (ρ w)) = ζ * Complex.exp (F w) := by
  have hcomp : AnalyticOnNhd ℂ (fun w => F (ρ w)) U := by
    intro w hw
    exact (hF (ρ w) (hmaps hw)).comp (hρ w hw)
  have hg : AnalyticOnNhd ℂ (fun w => F (ρ w) - F w) U := hcomp.sub hF
  have hre : ∀ x ∈ U, (F (ρ x) - F x).re = (0 : ℝ) := fun x hx => by
    rw [Complex.sub_re, hmod x hx, sub_self]
  obtain ⟨a, ha⟩ := AnalyticOnNhd.eq_const_of_re_eq_const hg hre hUo hUc
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  have ha0 : a.re = 0 := by
    have h1 : F (ρ z₀) - F z₀ = a := ha z₀ hz₀
    have h2 := hre z₀ hz₀
    rw [h1] at h2; exact h2
  refine ⟨Complex.exp a, by rw [Complex.norm_exp, ha0, Real.exp_zero], fun w hw => ?_⟩
  have hsub : F (ρ w) - F w = a := ha w hw
  rw [← Complex.exp_add]
  congr 1
  linear_combination hsub

end Bottcher

namespace Bottcher
open Set

/-- **Green-conjugate gluing step — extending the single-valued lift across two patches.** Two local
Böttcher-logarithm branches `F₁, F₂` (each with `Re F = G_c`, from `exists_local_greenConjugate_basin`)
on opens `U₁, U₂` with **connected** overlap glue to a single analytic `F` on `U₁∪U₂` still satisfying
`Re F = G_c`: they differ by an imaginary constant `a` on the overlap
(`greenConjugate_sub_imaginary_const`), and `F₂ + a` (with `Re a = 0`) agrees with `F₁` there, so
`analyticOnNhd_glue_cocycle` glues them while preserving the real part. **Iterating this along a chain
of patches around the cover assembles the global single-valued green-conjugate `F`** — hence the lift
`φ̃c = exp F` — the analytic input the disconnected discharge needs (feeding
`scaling_from_modulus_preserved`); the chain closes up because the accumulated cocycle is the period
`2πi`, absorbed by `exp` (`analyticOnNhd_glue_unit`). Axiom-clean. -/
theorem exists_greenConjugate_glue {c : ℂ} {U₁ U₂ : Set ℂ} {F₁ F₂ : ℂ → ℂ}
    (hU₁o : IsOpen U₁) (hU₂o : IsOpen U₂) (hovc : IsConnected (U₁ ∩ U₂))
    (hF₁ : AnalyticOnNhd ℂ F₁ U₁) (hF₂ : AnalyticOnNhd ℂ F₂ U₂)
    (h1 : EqOn (fun w => (F₁ w).re) (greenLimit c) U₁)
    (h2 : EqOn (fun w => (F₂ w).re) (greenLimit c) U₂) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (U₁ ∪ U₂) ∧
      EqOn (fun w => (F w).re) (greenLimit c) (U₁ ∪ U₂) := by
  classical
  obtain ⟨a, ha0, ha⟩ := greenConjugate_sub_imaginary_const (hU₁o.inter hU₂o) hovc
    (hF₁.mono inter_subset_left) (hF₂.mono inter_subset_right)
    (h1.mono inter_subset_left) (h2.mono inter_subset_right)
  refine ⟨U₁.piecewise F₁ (fun w => F₂ w + a),
    analyticOnNhd_glue_cocycle hU₁o hU₂o hF₁ hF₂ ha, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · simp only [Set.piecewise, if_pos hz]; exact h1 hz
  · by_cases hz1 : z ∈ U₁
    · simp only [Set.piecewise, if_pos hz1]; exact h1 hz1
    · simp only [Set.piecewise, if_neg hz1, Complex.add_re, ha0, add_zero]; exact h2 hz

end Bottcher

namespace Bottcher
open Filter Set

/-- **The whole `hscale` datum reduces to the green-conjugate's existence.** If the single-valued
green-conjugate `F` exists on the connected cover `U` (`Re F = G_c∘p`) and the deck `ρ` preserves the
modulus (`Re(F∘ρ) = Re F`), then the lift germ `a₁ = exp F` satisfies the germ-level deck scaling
`(a₁).compTendsto ρ = ζ·a₁` with `|ζ| = 1` — exactly the `hscale` hypothesis of `monoF_witness`/`hliftF`.
Chains `scaling_from_modulus_preserved` (open mapping ⟹ `exp(F∘ρ) = ζ·exp F`) with the germ-coe
naturality. So the entire monodromy-scaling input to the disconnected discharge bottoms out at the lone
analytic fact: **the global single-valued `F` exists on the connected cover** (assembled by iterating
`exists_greenConjugate_glue`). Everything else is mechanical and built. -/
theorem hscale_germ_of_greenConjugate {U : Set ℂ} {F : ℂ → ℂ} {ρ : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hF : AnalyticOnNhd ℂ F U) (hρ : AnalyticOnNhd ℂ ρ U) (hmaps : Set.MapsTo ρ U U)
    (hmod : ∀ w ∈ U, (F (ρ w)).re = (F w).re) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (↑(fun w => Complex.exp (F w)) : Germ (𝓟 U) ℂ).compTendsto ρ
          (tendsto_principal_principal.mpr hmaps)
        = (↑(fun _ : ℂ => ζ) : Germ (𝓟 U) ℂ) * ↑(fun w => Complex.exp (F w)) := by
  obtain ⟨ζ, hζ, hsc⟩ := scaling_from_modulus_preserved hUo hUc hF hρ hmaps hmod
  refine ⟨ζ, hζ, ?_⟩
  rw [Germ.coe_compTendsto, ← Germ.coe_mul]
  exact Germ.coe_eq.mpr (Filter.eventually_principal.mpr (fun w hw => hsc w hw))

end Bottcher

namespace Bottcher
open Set

/-- **Forward invariance of the filled Julia set (escape pulls back).** If an iterate `f^[n] z` escapes
(`∉ K_c`), then `z` itself escapes — `K_c` is forward-invariant
(`mem_filledJulia_iff_quadratic_mem`). So the domain `{z : f^[n] z ∈ escape}` lies in the basin, where
the green-conjugate continuation `F = 2⁻ⁿ·bottcherLog∘f^[n]` is defined. -/
theorem not_mem_filledJulia_of_iterate {c z : ℂ} (n : ℕ)
    (h : (quadratic c)^[n] z ∉ filledJulia c) : z ∉ filledJulia c := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    exact ih (fun hz => h ((mem_filledJulia_iff_quadratic_mem c _).mp hz))

/-- The iterate `f_c^[n] = (·²+c)^[n]` is entire (a polynomial map), analytic on all of `ℂ`. The
analytic backbone of the explicit green-conjugate continuation `F = 2⁻ⁿ·bottcherLog∘f^[n]`: on the deep
domain `{z : f^[n] z ∈ escape∩slitPlane}` it composes the analytic `bottcherLog` with the analytic
`f^[n]`, giving a single-valued `F` with `Re F = 2⁻ⁿ·G_c∘f^[n] = G_c` (`greenLimit_iterate_basin`) — the
genuine lift on each fundamental domain, the raw material the connected cover glues. -/
theorem analyticOnNhd_quadratic_iterate (c : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ ((quadratic c)^[n]) Set.univ := by
  have hq : AnalyticOnNhd ℂ (quadratic c) Set.univ :=
    fun w _ => (analyticAt_id.pow 2).add analyticAt_const
  induction n with
  | zero =>
      change AnalyticOnNhd ℂ (fun x : ℂ => x) Set.univ
      exact analyticOnNhd_id
  | succ n ih =>
    rw [Function.iterate_succ']
    intro z _
    exact (hq _ (Set.mem_univ _)).comp (ih z (Set.mem_univ _))

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit green-conjugate continuation `F = 2⁻ⁿ·bottcherLog∘f^[n]`.** On the deep domain
`{z : f^[n] z ∈ escape∩slitPlane}` (a fundamental domain), the genuine green-conjugate of `φ_c` is
realized in closed form: `F(z) = 2⁻ⁿ·bottcherLog(f^[n] z)` is single-valued analytic (composition of
the analytic `bottcherLog` with the entire `f^[n]`, scaled), and `Re F = 2⁻ⁿ·G_c(f^[n] z) = 2⁻ⁿ·2ⁿ·G_c
= G_c` by the iterated scaling law (`greenLimit_iterate_basin`). So `φ̃c = exp F` is the genuine
single-valued Böttcher lift on each of the `2ⁿ` fundamental domains — the explicit raw material that the
connected dyadic cover glues (via `exists_greenConjugate_glue`) into the global single-valued lift, with
the deck the order-`2ⁿ` permutation of these domains. This realizes the lift WITHOUT abstract gluing on
each domain; the remaining step is the global identification across the dyadic deck. Axiom-clean. -/
theorem exists_greenConjugate_explicit (c : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => ((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))
        {z : ℂ | (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane} ∧
      EqOn (fun z => (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)).re)
        (greenLimit c) {z : ℂ | (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane} := by
  have hbl : AnalyticOnNhd ℂ (bottcherLog c) (escapeOpen c ∩ Complex.slitPlane) :=
    (differentiableOn_bottcherLog c).analyticOnNhd
      ((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane)
  refine ⟨fun z hz => analyticAt_const.mul
    ((hbl _ hz).comp (analyticOnNhd_quadratic_iterate c n z (mem_univ _))), ?_⟩
  intro z hz
  have hesc : (quadratic c)^[n] z ∈ escapeOpen c := hz.1
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hesc
  have hnf : z ∉ filledJulia c := not_mem_filledJulia_of_iterate n (not_mem_filledJulia hc hz2)
  show (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)).re = greenLimit c z
  rw [Complex.re_ofReal_mul, bottcherLog_re hc hz2, greenLimit_iterate_basin hnf, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit lift has the genuine Böttcher modulus.** `|φ̃c| = |exp F| = exp(Re F) = exp(G_c)` on
the explicit-lift domain — confirming `φ̃c = exp(2⁻ⁿ·bottcherLog∘f^[n])` is the genuine Böttcher
coordinate continued (same modulus as `|φ_c| = exp G_c`), nowhere zero, landing on the level
`{|w| = exp G_c}` that the dyadic deck rotates. With `Re F = G_c` (`exists_greenConjugate_explicit`),
this pins the lift's modulus on every fundamental domain — the data the deck (a rotation preserving
`|·|`) acts through, and the input `scaling_from_modulus_preserved` consumes once the domains are glued
into the connected cover. -/
theorem norm_exp_greenConjugate_explicit (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane) :
    ‖Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))‖
      = Real.exp (greenLimit c z) := by
  rw [Complex.norm_exp]
  congr 1
  exact (exists_greenConjugate_explicit c n).2 hz

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit lift's derivative is the continued `d log φc`.** `F = 2⁻ⁿ·bottcherLog∘f^[n]` is
differentiable on its domain with `deriv F = 2⁻ⁿ·(deriv bottcherLog)(f^[n] z)·∏_{k<n} 2·f^[k] z`
(chain rule: `deriv_bottcherLog` × `hasStrictDerivAt_quadratic_iterate`). Since `deriv bottcherLog =
logDeriv φc` and `∏ 2·f^[k] z = 2ⁿ·∏ f^[k] z`, this is `(∏_{k<n} f^[k] z)·logDeriv φc(f^[n] z)` — which
on the escape region equals `logDeriv φc z` (`logDeriv_bottcherCoord_iterate`), so below escape `deriv F`
**is** the analytic continuation of `d log φc`. This is the concrete first step of continuing
`log φc = F` past the escape region toward the connected cover: the period `∮ deriv F` around a deep
loop is the deck cocycle (the `2πi/2ⁿ` monodromy multiplier), the data that glues the per-domain lifts.
Axiom-clean. -/
theorem hasDerivAt_greenConjugate_explicit (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane) :
    HasDerivAt (fun z => ((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))
      (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * (deriv (bottcherLog c) ((quadratic c)^[n] z)
        * (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z))) z := by
  have hbl : HasDerivAt (bottcherLog c) (deriv (bottcherLog c) ((quadratic c)^[n] z))
      ((quadratic c)^[n] z) :=
    ((differentiableOn_bottcherLog c).differentiableAt
      (((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane).mem_nhds hz)).hasDerivAt
  have hit : HasDerivAt ((quadratic c)^[n]) (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) z :=
    (hasStrictDerivAt_quadratic_iterate c n z).hasDerivAt
  exact (hbl.comp z hit).const_mul _

end Bottcher

namespace Bottcher
open Set Complex

/-- **`deriv F = logDeriv φc` on the escape overlap — the explicit lift IS the genuine `log φc`.** On
`escape∩slitPlane` (where both are defined), the explicit green-conjugate's derivative equals the
genuine logarithmic derivative `logDeriv φc`: combining `hasDerivAt_greenConjugate_explicit` (chain
rule), `logDeriv_bottcherCoord_iterate` (`logDeriv φc z = (∏_{k<n} f^[k] z)·logDeriv φc(f^[n] z)`), and
`logDeriv_bottcherCoord_eq`, the `2⁻ⁿ·∏ 2 = 1` cancellation gives `deriv F = logDeriv φc`. So
`F = 2⁻ⁿ·bottcherLog∘f^[n]` is a genuine analytic continuation of `log φc` (same `d log φc`), single-valued
below the escape region where `log φc` itself is undefined — the per-domain piece of the global green-
conjugate. Its period around a deep loop is therefore the deck cocycle `2πi/2ⁿ` (the project's computed
monodromy multiplier), the data assembling the connected cover. Axiom-clean. -/
theorem deriv_greenConjugate_explicit_eq (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hfz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane) :
    deriv (fun z => ((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)) z
      = logDeriv (bottcherCoord c) z := by
  rw [(hasDerivAt_greenConjugate_explicit c n hfz).deriv,
      logDeriv_bottcherCoord_iterate hz.1 n, logDeriv_bottcherCoord_eq hfz,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2n : ((2:ℂ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  push_cast
  field_simp

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit lift's period IS the genuine `d log φc` period.** Over a loop `γ` lying (with its
`n`-th iterate) in `escape∩slitPlane`, the contour integral of the explicit lift's `1`-form `deriv F`
equals that of `logDeriv φc` (`deriv_greenConjugate_explicit_eq` pointwise + `integral_congr`). So the
period of `φ̃c = exp F` around a deep pullback loop is the genuine `∮ d log φc` — which the project
computes as `2πi` over the base circle (`circleIntegral_dlog_bottcher`) and `2πi/2ⁿ` over the `n`-fold
pullback (`pathInt_iterate_comp`). This is the explicit **deck-cocycle value** `2πi/2ⁿ` on the continued
`F`: the monodromy multiplier `exp(2πi/2ⁿ) = ζ` of order `2ⁿ` by which `φ̃c` scales across the cover —
the bridge from the per-domain continuations to the connected-cover deck. Axiom-clean. -/
theorem pathInt_deriv_greenConjugate_explicit_eq (c : ℂ) (n : ℕ) {γ γ' : ℝ → ℂ}
    (hmem : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c ∩ Complex.slitPlane)
    (hmemn : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      (quadratic c)^[n] (γ θ) ∈ escapeOpen c ∩ Complex.slitPlane) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        deriv (fun z => ((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)) (γ θ) * γ' θ)
      = ∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ := by
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only
  rw [deriv_greenConjugate_explicit_eq c n (hmem θ hθ) (hmemn θ hθ)]

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit lift `φ̃c = exp F` is analytic on its domain.** Hence on each connected fundamental
domain it is a genuine element of `analyticSubring` — the carrier germ `a₁` that the disconnected
discharge consumes (`exp F` of the analytic `F = 2⁻ⁿ·bottcherLog∘f^[n]`, via `AnalyticAt.cexp`). -/
theorem analyticOnNhd_exp_greenConjugate_explicit (c : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ
        (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)))
        {z : ℂ | (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane} :=
  fun z hz => ((exists_greenConjugate_explicit c n).1 z hz).cexp

/-- **The explicit lift is nowhere zero** (`exp` never vanishes) — so its carrier germ `a₁ ≠ 0`, the
nonvanishing hypothesis `hF0` of the disconnected discharge, holds automatically. -/
theorem exp_greenConjugate_explicit_ne_zero (c : ℂ) (n : ℕ) (z : ℂ) :
    Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)) ≠ 0 :=
  Complex.exp_ne_zero _

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit lift satisfies the Böttcher functional equation, exactly.**
`φ̃c_{m+1}(z)² = φ̃c_m(f_c z)` where `φ̃c_n = exp(2⁻ⁿ·bottcherLog∘f^[n])` — pure `exp`-algebra
(`(exp a)² = exp(2a)`, `2·2⁻⁽ᵐ⁺¹⁾ = 2⁻ᵐ`, `f^[m+1] z = f^[m](f z)`), with no branch ambiguity (it lives
at the `exp` level where `bottcherCoord_quadratic` is exact). This is the conjugacy `φ̃c ∘ f_c = φ̃c²`
realized for the continued lift across levels — the dynamical engine of the dyadic monodromy: pulling
the lift back through `f_c` halves it, so the `2ⁿ` preimages of a base loop carry the `2ⁿ`-th-root
multipliers `ζ` of the deck. The exact level-relation that, combined with the cocycle period `2πi/2ⁿ`,
organizes the per-domain lifts into the connected-cover deck structure. Axiom-clean. -/
theorem exp_greenConjugate_explicit_sq (c : ℂ) (m : ℕ) (z : ℂ) :
    (Complex.exp (((((2:ℝ) ^ (m+1))⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m+1] z))) ^ 2
      = Complex.exp (((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] (quadratic c z))) := by
  rw [sq, ← Complex.exp_add, Function.iterate_succ_apply]
  congr 1
  push_cast
  ring

end Bottcher

namespace Bottcher
open Set Complex

/-- **The explicit lift is an exact `2ⁿ`-th root of the genuine Böttcher coordinate.**
`φ̃c_n(z)^{2ⁿ} = bottcherCoord c (f^[n] z)` — pure `exp`-algebra (`(exp a)^{2ⁿ} = exp(2ⁿ·a)`,
`2ⁿ·2⁻ⁿ = 1`, `bottcherCoord = exp∘bottcherLog`). So `φ̃c_n` is a genuine `2ⁿ`-th root of `φc∘f^[n] =
φc^{2ⁿ}`, i.e. the genuine Böttcher coordinate `φc` itself (at the right branch), exhibiting the
disconnected-case multivaluedness as the `2ⁿ`-valued root that the dyadic deck `μ_{2ⁿ}` permutes. This
is the exact algebraic bond between the explicit lift and `bottcherCoord` — the relation `q62`'s descent
uses to identify `φ̃c` with `phiMero`. Axiom-clean. -/
theorem exp_greenConjugate_explicit_pow (c : ℂ) (n : ℕ) (z : ℂ) :
    (Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))) ^ (2 ^ n)
      = bottcherCoord c ((quadratic c)^[n] z) := by
  rw [← Complex.exp_nat_mul, bottcherCoord]
  congr 1
  have h2n : ((2:ℂ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  push_cast
  field_simp

end Bottcher

namespace Bottcher
open Set

/-- **The deck is the value-rotation conjugated through the lift — reducing the deck to the lift's
invertibility.** If the lift `φ` (= `φ̃c`) has a right-inverse `ψ` on the value annulus `V`
(`φ∘ψ = id` on `V`, i.e. `φ` maps the cover biholomorphically onto `V`) and `ρ = ×ζ` is the value
rotation, then `g = ψ∘ρ∘φ` is a self-map of the cover with `φ∘g = ζ·φ` — exactly the deck scaling
`a₁∘g = ζ·a₁` that `monoF_witness` consumes. So the **entire genuine monodromy deck** (for every
depth, hence the unbounded order) reduces to a single analytic input: that the lift `φ̃c` is
**invertible** on the cover (the cover is biholomorphic to the value annulus via `φ̃c`) — the
uniformization of the dyadic cover. Combined with the explicit lift's verified properties
(`φ̃c^{2ⁿ}=bottcherCoord∘f^[n]`, `Re=G_c`, the conjugacy), this is the last analytic fact between the
built reduction and the discharged `hDisc`. Axiom-clean. -/
theorem deck_scaling_of_invertible_lift {U V : Set ℂ} {φ ψ ρ : ℂ → ℂ} {ζ : ℂ}
    (hinv : Set.EqOn (φ ∘ ψ) id V) (hρ : Set.EqOn ρ (fun w => ζ * w) V)
    (hφmaps : Set.MapsTo φ U V) (hρmaps : Set.MapsTo ρ V V) :
    Set.EqOn (φ ∘ (ψ ∘ ρ ∘ φ)) (fun z => ζ * φ z) U := by
  intro z hz
  have h1 := hinv (hρmaps (hφmaps hz))
  have h2 := hρ (hφmaps hz)
  simp only [Function.comp_apply, id_eq] at h1 h2 ⊢
  rw [h1, h2]

end Bottcher

namespace Bottcher
open Set Complex

/-- **The lift `φ̃c = exp F` is differentiable, with `deriv φ̃c = φ̃c·deriv F`.** From
`hasDerivAt_greenConjugate_explicit` via `HasDerivAt.cexp`. Since `φ̃c ≠ 0` everywhere and
`deriv F = d log φc` (`deriv_greenConjugate_explicit_eq`) is nonzero off the precritical orbit
(`logDeriv_bottcherCoord_eq_zero_iff`), the lift's derivative is nonzero there — so `φ̃c` is a **local
biholomorphism** away from critical points (inverse function theorem). This is the concrete first step
toward the global invertibility `deck_scaling_of_invertible_lift` needs: the lift is everywhere locally
invertible; the remaining analytic content is upgrading local to global (the uniformization of the
connected cover onto the value annulus). Axiom-clean. -/
theorem hasDerivAt_exp_greenConjugate_explicit (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane) :
    HasDerivAt (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)))
      (Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))
        * (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * (deriv (bottcherLog c) ((quadratic c)^[n] z)
          * (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z)))) z :=
  (hasDerivAt_greenConjugate_explicit c n hz).cexp

end Bottcher

namespace Bottcher
open Set Complex

/-- **Clean lift-derivative formula: `deriv φ̃c = φ̃c · logDeriv φc`** on the escape overlap. From the
chain-rule derivative (`hasDerivAt_exp_greenConjugate_explicit`) with the raw factor identified as
`logDeriv φc` (`deriv_greenConjugate_explicit_eq`). -/
theorem deriv_exp_greenConjugate_explicit (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hfz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane) :
    deriv (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))) z
      = Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))
        * logDeriv (bottcherCoord c) z := by
  rw [(hasDerivAt_exp_greenConjugate_explicit c n hfz).deriv]
  congr 1
  rw [← (hasDerivAt_greenConjugate_explicit c n hfz).deriv]
  exact deriv_greenConjugate_explicit_eq c n hz hfz

/-- **The lift is a local biholomorphism off critical points: `deriv φ̃c ≠ 0`** where `logDeriv φc ≠ 0`
(i.e. away from the precritical orbit, `logDeriv_bottcherCoord_eq_zero_iff`). Since `deriv φ̃c =
φ̃c·logDeriv φc` with `φ̃c ≠ 0`, the lift's derivative is nonzero there — so by the inverse function
theorem `φ̃c` is locally invertible, the local half of the cover biholomorphism
`deck_scaling_of_invertible_lift` needs. The remaining content is upgrading this everywhere-local
invertibility to a global biholomorphism onto the value annulus (the uniformization of the connected
dyadic cover). Axiom-clean. -/
theorem deriv_exp_greenConjugate_explicit_ne_zero (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hfz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hcrit : logDeriv (bottcherCoord c) z ≠ 0) :
    deriv (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))) z
      ≠ 0 := by
  rw [deriv_exp_greenConjugate_explicit c n hz hfz]
  exact mul_ne_zero (Complex.exp_ne_zero _) hcrit

end Bottcher

namespace Bottcher
open Set Complex

/-- **The lift has a local analytic inverse off critical points.** Where `logDeriv φc ≠ 0` (away from
the precritical orbit), `deriv φ̃c ≠ 0`, so by the analytic inverse function theorem
(`AnalyticAt.hasStrictDerivAt` → `HasStrictDerivAt.to_localInverse`) there is a local holomorphic inverse
`g` of `φ̃c` with `g'(φ̃c z) = (deriv φ̃c z)⁻¹`. This is the local section `ψ` that
`deck_scaling_of_invertible_lift` consumes — realized concretely. The remaining content is patching
these local inverses into a single global section on the value annulus (the uniformization upgrading
the local biholomorphisms to the global cover biholomorphism). Axiom-clean. -/
theorem exists_localInverse_exp_greenConjugate (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hfz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hcrit : logDeriv (bottcherCoord c) z ≠ 0) :
    ∃ g : ℂ → ℂ, HasStrictDerivAt g
      (deriv (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ)
        * bottcherLog c ((quadratic c)^[n] z))) z)⁻¹
      (Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))) :=
  ⟨_, (analyticOnNhd_exp_greenConjugate_explicit c n z hfz).hasStrictDerivAt.to_localInverse
    (deriv_exp_greenConjugate_explicit_ne_zero c n hz hfz hcrit)⟩

end Bottcher

namespace Bottcher
open Set Complex Filter

/-- **The lift is locally injective: a local left-inverse exists.** Near any point off the precritical
orbit, the local analytic inverse `g` of `φ̃c` satisfies `g(φ̃c x) = x` (`HasStrictDerivAt`'s
`eventually_left_inverse`). So `φ̃c` is injective on a neighbourhood — locally a biholomorphism. The
local sections agree where they overlap (the left-inverse is unique near `z`); the remaining content is
that the global obstruction to a single section over the value annulus is exactly the dyadic
monodromy, unwound by passing to the connected cover (the uniformization). Axiom-clean. -/
theorem exists_eventually_left_inverse_exp_greenConjugate (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hfz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hcrit : logDeriv (bottcherCoord c) z ≠ 0) :
    ∃ g : ℂ → ℂ, ∀ᶠ x in nhds z,
      g (Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] x))) = x :=
  ⟨_, (analyticOnNhd_exp_greenConjugate_explicit c n z hfz).hasStrictDerivAt.eventually_left_inverse
    (deriv_exp_greenConjugate_explicit_ne_zero c n hz hfz hcrit)⟩

end Bottcher

namespace Bottcher
open Set Complex Filter

/-- **The lift has a local section: `φ̃c∘g = id` near `φ̃c z`.** The right-inverse of the analytic local
inverse (`HasStrictDerivAt.eventually_right_inverse`) — so `φ̃c` maps a neighbourhood of `z`
homeomorphically onto a neighbourhood of the value `φ̃c z`, and `g` is a local **section** of `φ̃c`. This
is *exactly* the `hinv : φ∘ψ = id on V` hypothesis `deck_scaling_of_invertible_lift` consumes, realized
locally on the value side. With the left-inverse (`exists_eventually_left_inverse_...`), `φ̃c` is a local
biholomorphism in both directions. The lone remaining content is upgrading this local section to a
global one on the whole value annulus — the uniformization of the connected cover, whose obstruction is
precisely the dyadic monodromy. Axiom-clean. -/
theorem exists_eventually_right_inverse_exp_greenConjugate (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hfz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane)
    (hcrit : logDeriv (bottcherCoord c) z ≠ 0) :
    ∃ g : ℂ → ℂ, ∀ᶠ y in nhds (Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ)
        * bottcherLog c ((quadratic c)^[n] z))),
      Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] (g y))) = y :=
  ⟨_, (analyticOnNhd_exp_greenConjugate_explicit c n z hfz).hasStrictDerivAt.eventually_right_inverse
    (deriv_exp_greenConjugate_explicit_ne_zero c n hz hfz hcrit)⟩

end Bottcher

namespace Bottcher
open Set Complex

/-- **The lift lands in the value-annulus exterior `{|w|>1}`.** `|φ̃c z| = exp(G_c z) > 1` on the basin
(`greenLimit_pos_basin`: `G_c > 0` off `K_c`, reached via `not_mem_filledJulia_of_iterate`). So `φ̃c`
maps its domain into `{|w| > 1}` — the value region that is the **target** of the global cover
biholomorphism `φ̃c : U → V`. With `|φ̃c| = exp G_c` pinning the modulus to the green level, the lift's
image lies on the level annuli the deck `μ_{2ⁿ}` rotates. Confirms the lift takes values in the
value-annulus where `deck_scaling_of_invertible_lift`'s rotation `ρ` acts. Axiom-clean. -/
theorem one_lt_norm_exp_greenConjugate_explicit (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane) :
    1 < ‖Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))‖ := by
  rw [norm_exp_greenConjugate_explicit c n hz]
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz.1
  have hnf : z ∉ filledJulia c := not_mem_filledJulia_of_iterate n (not_mem_filledJulia hc hz2)
  exact Real.one_lt_exp_iff.mpr (greenLimit_pos_basin hnf)

end Bottcher

namespace Bottcher
open Set Filter

/-- **Global section ⟹ the germ-level `hscale` datum, in one step.** Combining
`deck_scaling_of_invertible_lift` (the section yields the function-level scaling `φ∘g = ζ·φ`) with the
germ-coercion (`Germ.coe_compTendsto`/`coe_mul`/`coe_eq`), the deck `g = ψ∘ρ∘φ` acts on the germ `↑φ`
by the scalar `ζ`: `(↑φ).compTendsto g = ↑ζ · ↑φ`. This is *exactly* the `hscale` shape
`monoF_witness`/`hliftF` consume, now derived directly from the **global-section** hypotheses
(`hinv : φ∘ψ = id on V`) rather than posited. So the reduction chain tightens to:
global section `ψ` of `φ̃c` ⟹ germ scaling ⟹ `monoF` ⟹ `q62_independence`. The sole remaining input
is the existence of that global section `ψ` — the uniformization of the dyadic cover. Axiom-clean. -/
theorem germ_scaling_of_section {U V : Set ℂ} {φ ψ ρ : ℂ → ℂ} {ζ : ℂ}
    (hinv : Set.EqOn (φ ∘ ψ) id V) (hρ : Set.EqOn ρ (fun w => ζ * w) V)
    (hφmaps : Set.MapsTo φ U V) (hρmaps : Set.MapsTo ρ V V)
    (hgmaps : Set.MapsTo (ψ ∘ ρ ∘ φ) U U) :
    (↑φ : Germ (𝓟 U) ℂ).compTendsto (ψ ∘ ρ ∘ φ) (tendsto_principal_principal.mpr hgmaps)
      = (↑(fun _ : ℂ => ζ) : Germ (𝓟 U) ℂ) * ↑φ := by
  rw [Germ.coe_compTendsto, ← Germ.coe_mul]
  refine Germ.coe_eq.mpr (Filter.eventually_principal.mpr (fun w hw => ?_))
  have := deck_scaling_of_invertible_lift hinv hρ hφmaps hρmaps hw
  simpa [Function.comp_apply, Pi.mul_apply] using this

end Bottcher

namespace Bottcher
open Set

/-- **At level `n=m=0` the cover is the genuine Böttcher graph.** `commonPullback c₁ c₂ 0 0` forces
`v₁ = φ_{c₁}(z)` and `v₂ = φ_{c₂}(z)` (no root branching, since `2⁰ = 1` and `f^[0] = id`). So the
formal cover coordinates `v1Germ, v2Germ` ARE the actual inverse Böttcher coordinates at this level.
This pins the location of the only genuine gap: the "formal product vs. connected Riemann-surface
function field" obstruction (named in `commonPullback`'s docstring) lives ENTIRELY in the `n ≥ 1`
root-branching — where the `2ⁿ`-fold cover is disconnected, so `coverGerm` (functions on the full
fibre) is not a domain — and NOT in the coordinates being abstract. At `n=0` the coordinates are
genuine but the deck has order `2⁰ = 1` (no monodromy); the genuine q62 needs both genuine coordinates
AND nontrivial monodromy, i.e. the connected `n ≥ 1` cover. Axiom-clean. -/
theorem commonPullback_zero_eq (c₁ c₂ : ℂ) :
    commonPullback c₁ c₂ 0 0 =
      {p : ℂ × ℂ × ℂ | p.2.1 = bottcherCoord c₁ p.1 ∧ p.2.1 ≠ 0 ∧
        p.2.2 = bottcherCoord c₂ p.1 ∧ p.2.2 ≠ 0} := by
  ext p
  simp only [commonPullback, Set.mem_setOf_eq, pow_zero, pow_one, Function.iterate_zero, id_eq]

end Bottcher

namespace Bottcher
open Complex

/-- **[Covering brick B] A nonzero strict derivative packages as an `OpenPartialHomeomorph`.** For
`f : ℂ → ℂ` with `HasStrictDerivAt f d z` and `d ≠ 0`, the inverse function theorem gives an open
partial homeomorphism `φ` with `z ∈ φ.source` and `φ = f` near `z`. This is the local-homeomorphism
datum that `IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph` consumes at each preimage point —
the enabling brick for assembling `IsCoveringMap (f_c^[n] : cylinder → collar)` (step 4 of the
`hDisc` roadmap). Via `HasStrictDerivAt.hasStrictFDerivAt_equiv` (the `unitsEquivAut` CLE of `d`) and
`HasStrictFDerivAt.toOpenPartialHomeomorph`. Axiom-clean. -/
theorem exists_openPartialHomeomorph_of_hasStrictDerivAt {f : ℂ → ℂ} {z d : ℂ}
    (hf : HasStrictDerivAt f d z) (hd : d ≠ 0) :
    ∃ φ : OpenPartialHomeomorph ℂ ℂ, z ∈ φ.source ∧ ⇑φ = f := by
  have hfd : HasStrictFDerivAt f
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd) : ℂ →L[ℂ] ℂ) z :=
    hf.hasStrictFDerivAt_equiv hd
  exact ⟨hfd.toOpenPartialHomeomorph f, hfd.mem_toOpenPartialHomeomorph_source,
    hfd.toOpenPartialHomeomorph_coe⟩

end Bottcher

namespace Bottcher
open Complex Polynomial

/-- **[Covering brick E — STEP 4 CORE] `f_c^[n]` is an honest covering map over the complement of its
critical values.** Assembled from the project's verified pieces via Mathlib's
`IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph`:
* `quadratic_iterate_isProperMap` ⟹ closed map;
* `quadratic_iterate_fiber_finite` ⟹ finite fibres (degree `2ⁿ`);
* at each preimage `e` of a non-critical value, `(f_c^[n])'(e) = ∏_{k<n} 2·f_c^[k](e) ≠ 0`
  (`quadratic_iterate_deriv_eq_zero_iff`, `quadratic_iterate_fiber_noncritical`), so brick B
  (`exists_openPartialHomeomorph_of_hasStrictDerivAt`) supplies the local chart.
This is the even-covering trivialization the `hDisc` roadmap (STATUS step 4) called for — the analytic
realization of the dyadic `w ↦ w^{2ⁿ}` cover, now an honest `IsCoveringMapOn` over
`(criticalValues)ᶜ`, with deck group `μ_{2ⁿ}` fixing `z` and scaling the `2ⁿ`-th-root coordinate
`v ≈ φ_{c₁}`. The branched-covering bridge from the dynamics to the monodromy automorphism `σ_n`.
Axiom-clean. -/
theorem isCoveringMapOn_quadratic_iterate (c : ℂ) (n : ℕ) :
    IsCoveringMapOn ((quadratic c)^[n])
      ((quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w})ᶜ := by
  apply (quadratic_iterate_isProperMap c n).isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro x _
    exact quadratic_iterate_fiber_finite c n x
  · intro e he
    have hfe : (quadratic c)^[n] e ∉
        (quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w} := he
    have hnc : ¬ (quadraticPolyIterate c n).derivative.IsRoot e :=
      quadratic_iterate_fiber_noncritical hfe rfl
    have hd : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] e) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      exact mul_ne_zero two_ne_zero
        (fun h0 => hnc ((quadratic_iterate_deriv_eq_zero_iff c n e).mpr
          ⟨k, Finset.mem_range.mp hk, h0⟩))
    obtain ⟨φ, he, hφ⟩ := exists_openPartialHomeomorph_of_hasStrictDerivAt
      (hasStrictDerivAt_quadratic_iterate c n e) hd
    exact ⟨φ, he, hφ.symm⟩

end Bottcher

namespace Bottcher
open Complex Polynomial

/-- **[Covering] The global branched covering on the subtype.** Restricting
`isCoveringMapOn_quadratic_iterate` to the preimage subtype yields an honest `IsCoveringMap`
(`IsCoveringMapOn.isCoveringMap_restrictPreimage`), so Mathlib's covering-monodromy machinery
(`IsCoveringMap.monodromy`, the homotopy-invariant fibre bijection) applies directly to
`f_c^[n] : (f_c^[n])⁻¹(criticalValuesᶜ) → criticalValuesᶜ`. This is the dynamical realization of the
order-`2ⁿ` deck action `μ_{2ⁿ}` (matching `isCoveringMap_dyadic` via the conjugacy
`φ_c∘f^[n]=φ_c^{2ⁿ}`), now as a genuine covering whose monodromy IS the continuation operator.
Axiom-clean. -/
theorem isCoveringMap_quadratic_iterate_restrict (c : ℂ) (n : ℕ) :
    IsCoveringMap
      (((quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w})ᶜ.restrictPreimage
        ((quadratic c)^[n])) :=
  (isCoveringMapOn_quadratic_iterate c n).isCoveringMap_restrictPreimage

end Bottcher

namespace Bottcher
open Complex

/-- **[Covering] Local `2ⁿ`-th root branch.** Away from `0`, `w ↦ w^k` (`k>0`) is a local
homeomorphism — its `OpenPartialHomeomorph` `φ` (brick B at `deriv = k·v₀^{k-1} ≠ 0`) has inverse
`φ.symm` the analytic `k`-th-root branch through `v₀`. This is the section-builder for the
**projection** covering `{(z,v) : v^{2ⁿ} = f_c^[n] z} → z`-plane (the structurally correct `σ_n`
carrier, whose deck `(z,v)↦(z,ζv)` fixes `z` and `φ_{c₂}`): a local trivialization sends `z` to
`(z, (φ.symm)(f_c^[n] z))`. Axiom-clean. -/
theorem exists_openPartialHomeomorph_npow {v₀ : ℂ} (hv₀ : v₀ ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ φ : OpenPartialHomeomorph ℂ ℂ, v₀ ∈ φ.source ∧ ⇑φ = (fun w => w ^ k) := by
  refine exists_openPartialHomeomorph_of_hasStrictDerivAt
    (f := fun w => w ^ k) (d := (k : ℂ) * v₀ ^ (k - 1)) (hasStrictDerivAt_pow k v₀) ?_
  exact mul_ne_zero (by exact_mod_cast hk.ne') (pow_ne_zero _ hv₀)

end Bottcher

namespace Bottcher
open Complex Polynomial

/-- **[Covering] The branch locus is finite.** The critical values of `f_c^[n]` — the set over which
`isCoveringMapOn_quadratic_iterate` is branched — form a FINITE set: the critical points are the roots
of the nonzero degree-`(2ⁿ-1)` polynomial `(f_c^[n])'` (`derivative ≠ 0` since `deg f_c^[n] = 2ⁿ > 0`
in char 0), hence finite, and so is their image. So `f_c^[n]` is an honest unbranched covering over the
**cofinite** base `(criticalValues)ᶜ` — a connected, dense open set carrying the full dyadic monodromy.
This pins that the covering's defect is supported on finitely many points (the precritical orbit's
image), exactly the branch locus of the `2ⁿ`-fold cover. Axiom-clean. -/
theorem criticalValues_finite (c : ℂ) (n : ℕ) :
    ((quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w}).Finite := by
  apply Set.Finite.image
  have hne : (quadraticPolyIterate c n).derivative ≠ 0 := by
    intro h
    have hdeg : (quadraticPolyIterate c n).natDegree = 0 :=
      by simpa using Polynomial.derivative_eq_zero.mp h
    rw [quadraticPolyIterate_natDegree] at hdeg
    exact absurd hdeg (by positivity)
  exact Polynomial.finite_setOf_isRoot hne

end Bottcher

namespace Bottcher
open Complex Filter

/-- **[Field carrier] The explicit lift `φ̃c` is a genuine element of the field carrier.** Since
`φ̃c = exp(2⁻ⁿ·bottcherLog∘f^[n])` is analytic on `D₀ = {z | f_c^[n] z ∈ escape ∩ slit}`
(`analyticOnNhd_exp_greenConjugate_explicit`), its germ on any `U ⊆ D₀` lies in `analyticSubring U` —
hence in `meroField U`, the FractionRing-of-domain field that `q62_independence_disconnected_of_lifts`
consumes. So the single-valued analytic continuation `φ̃c` (the deck-scaled coordinate, with
`φ̃c^{2ⁿ} = bottcherCoord∘f^[n]`) is realized as an honest field element — closing the gap between the
explicit lift and the planar `meroField` carrier. The remaining input is the deck self-map of `U`
(global section / the connected deck-invariant piece). Axiom-clean. -/
theorem exp_greenConjugate_explicit_mem_analyticSubring (c : ℂ) (n : ℕ) {U : Set ℂ}
    (hU : U ⊆ {z : ℂ | (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane}) :
    (Germ.coeRingHom (𝓟 U)
        (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))))
      ∈ analyticSubring U :=
  ⟨_, (analyticOnNhd_exp_greenConjugate_explicit c n).mono hU, rfl⟩

end Bottcher

namespace Bottcher
open Complex Filter

/-- **[Field carrier] The lift germ is a nonzero field element.** `φ̃c = exp(…) ≠ 0` pointwise, so on a
nonempty `U` its germ is `≠ 0` in `Germ (𝓟 U) ℂ` — hence a nonzero element of `analyticSubring U` and
of `meroField U` (the `F ≠ 0` datum of `q62_disconnected_both`). Axiom-clean. -/
theorem exp_greenConjugate_explicit_germ_ne_zero (c : ℂ) (n : ℕ) {U : Set ℂ} (hU : U.Nonempty) :
    (Germ.coeRingHom (𝓟 U)
        (fun z => Complex.exp (((((2:ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))))
      ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := hU
  have hev := Germ.coe_eq.mp (h.trans Germ.coe_zero.symm)
  exact Complex.exp_ne_zero _ (Filter.eventually_principal.mp hev x hx)

end Bottcher

namespace Bottcher
open Complex Set

/-- **[L1 — the `φ_{c₂}`-fixed half of the winding lemma] A closed loop inside the single-valued
domain of the lift has zero period.** If a `C¹` loop `γ` (closed: `γ(2π)=γ(0)`) lies, throughout
`[0,2π]`, in the domain `D_m = {z | f_c^[m] z ∈ escape ∩ slit}` where `φ̃c = exp(2⁻ᵐ·bottcherLog∘f^[m])`
is single-valued analytic, then `∮_γ d log φ̃c = 0`. Pure FTC: `deriv F` integrates to the endpoint
difference `F(γ(2π)) − F(γ(0)) = 0`. This is the asymmetry the disconnected proof turns on: the *same*
loop that produces the `2πi/2ⁿ` monodromy of `φ_{c₁}` (because it crosses fundamental domains of `φ̃c₁`)
fixes `φ_{c₂}` whenever it stays in one single-valued domain of `φ̃c₂` — i.e. is null-homotopic in the
*other* basin. The contrast with the nonzero `n`-fold pullback period (`pathInt_iterate_comp`) is exactly
"`σ_n` scales `φ_{c₁}`, fixes `φ_{c₂}`". Axiom-clean. -/
theorem pathInt_dlog_lift_closed_eq_zero (c : ℂ) (m : ℕ) {γ γ' : ℝ → ℂ}
    (hmem : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      (quadratic c)^[m] (γ θ) ∈ escapeOpen c ∩ Complex.slitPlane)
    (hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ)
    (hint : IntervalIntegrable
      (fun θ => deriv (fun z => ((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] z))
        (γ θ) * γ' θ) MeasureTheory.volume 0 (2 * Real.pi))
    (hclosed : γ (2 * Real.pi) = γ 0) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        deriv (fun z => ((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] z))
          (γ θ) * γ' θ) = 0 := by
  have hd : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun t => ((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] (γ t)))
        (deriv (fun z => ((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] z)) (γ θ)
          * γ' θ) θ := by
    intro θ hθ
    have hF := hasDerivAt_greenConjugate_explicit c m (hmem θ hθ)
    have hF' : HasDerivAt
        (fun z => ((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] z))
        (deriv (fun z => ((((2:ℝ) ^ m)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[m] z)) (γ θ))
        (γ θ) := by rw [hF.deriv]; exact hF
    exact hF'.comp θ (hderiv θ hθ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [hclosed, sub_self]

end Bottcher
