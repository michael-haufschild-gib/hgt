/-
# Böttcher tower — step 4: the disconnected-case branching structure (basin pullback)

The continuation skeleton (`MonodromyContinuation.lean`) realizes the dyadic monodromy multiplier
on the model covering `w ↦ w^{2ⁿ}`. Step 4 pulls this back along `φ_{c₁}` to the actual basin
`Ω_{c₁}`: the source of `φ_{c₁}`'s branching is that the critical point `0` ESCAPES (the
disconnected hypothesis), so the critical value sits at a positive Green level, below which `φ_c`
is multivalued. The loops carrying the dyadic monodromy encircle the precritical clusters at those
levels.

This file records the dynamical foundation of that branching. The full step 4 — the branched
covering `Ω_{c₁} ∖ (precritical orbit)`, `φ_{c₁}` single-valued on it, `φ_{c₂}`/`z` carried as
functions, and `σ_n` fixing `φ_{c₂}` (loop null-homotopic in the other basin) — is the major
remaining analytic build (the disconnected, Cantor-Julia-set covering structure).
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

open Complex Filter Topology Polynomial

namespace Bottcher

/-- **Critical orbit escapes (disconnected case).** When `c` is disconnected (`0 ∉ K_c`), some
iterate of the critical point `0` enters the escape region `escapeOpen c`. The dynamical source of
`φ_c`'s multivaluedness: the critical value lies at a positive Green level, below which `φ_c`
branches. -/
theorem disconnected_critical_escapes {c : ℂ} (hc : Disconnected c) :
    ∃ N, (quadratic c)^[N] 0 ∈ escapeOpen c := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨N, hN⟩ := exists_orbit_gt h0 (max 2 ‖c‖)
  exact ⟨N, hN⟩

/-- **Critical Green level is positive (disconnected case).** `G_c(0) > 0`. The critical value
`c = f_c(0)` then sits at level `G_c(c) = 2 G_c(0) > 0`; the branch locus of `φ_c` is the level set
`{G_c = G_c(0)}` and its `f_c`-preimages — the depth-`n` cylinders whose enclosing loops carry the
order-`2ⁿ` monodromy. -/
theorem disconnected_green_critical_pos {c : ℂ} (hc : Disconnected c) :
    0 < greenLimit c 0 :=
  greenLimit_pos_basin ((disconnected_iff_zero_not_mem c).mp hc)

/-- `g_n(z) → G_c(z)` on the whole basin `Ω_c` (not just the escape regime), via the pullback
representation: the orbit eventually enters the escape regime where convergence holds. -/
theorem greenApprox_tendsto_basin {c z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto (greenApprox c z) atTop (𝓝 (greenLimit c z)) := by
  obtain ⟨N, hNc, hN2, heq⟩ := greenLimit_eq_pullback hz
  rw [heq, ← tendsto_add_atTop_iff_nat N]
  have hrel : ∀ m, greenApprox c z (m + N)
      = (2 ^ N : ℝ)⁻¹ * greenApprox c ((quadratic c)^[N] z) m := by
    intro m; unfold greenApprox
    rw [Function.iterate_add_apply, pow_add]; field_simp
  simp_rw [hrel]
  exact (greenApprox_tendsto hNc hN2).const_mul _

/-- **Basin-wide functional equation** `G_c(f_c z) = 2·G_c(z)` on all of `Ω_c` (extending the
escape-regime version). Levels double under `f_c`: the branch locus `{G_c = G_c(0)}` and its
`f_c`-preimages `{G_c = G_c(0)/2ⁿ}` are the depth-`n` cylinder boundaries carrying the dyadic
monodromy. -/
theorem greenLimit_quadratic_basin {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenLimit c (quadratic c z) = 2 * greenLimit c z := by
  have hfz : quadratic c z ∉ filledJulia c := by
    rw [← mem_filledJulia_iff_quadratic_mem]; exact hz
  have h1 : Tendsto (fun n => greenApprox c (quadratic c z) n) atTop
      (𝓝 (greenLimit c (quadratic c z))) := greenApprox_tendsto_basin hfz
  have h2 : Tendsto (fun n => 2 * greenApprox c z (n + 1)) atTop (𝓝 (2 * greenLimit c z)) :=
    ((greenApprox_tendsto_basin hz).comp (tendsto_add_atTop_nat 1)).const_mul 2
  rw [funext (greenApprox_quadratic c z)] at h1
  exact tendsto_nhds_unique h1 h2

/-- The basin is forward-invariant: every iterate of a basin point stays in the basin. -/
theorem not_mem_filledJulia_iterate {c z : ℂ} (hz : z ∉ filledJulia c) (n : ℕ) :
    (quadratic c)^[n] z ∉ filledJulia c := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← mem_filledJulia_iff_quadratic_mem]; exact ih

/-- **Depth-`n` cylinder levels.** `G_c(f_c^[n] z) = 2ⁿ · G_c(z)` on the basin: the `n`-th iterate
multiplies the Green level by `2ⁿ`. So `f_c^[n]` maps the depth-`n` cylinder `{G_c(0)/2ⁿ < G_c <
G_c(0)/2ⁿ⁻¹}` onto the critical collar `{G_c(0) < G_c < 2 G_c(0)}` — the `2ⁿ`-fold covering whose
monodromy is the order-`2ⁿ` dyadic multiplier. -/
theorem greenLimit_iterate_basin {c z : ℂ} (hz : z ∉ filledJulia c) (n : ℕ) :
    greenLimit c ((quadratic c)^[n] z) = 2 ^ n * greenLimit c z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', greenLimit_quadratic_basin (not_mem_filledJulia_iterate hz n),
        ih, pow_succ]
    ring

/-- `f_c(z) = z²+c` has strict derivative `2z`. -/
theorem hasStrictDerivAt_quadratic (c z : ℂ) : HasStrictDerivAt (quadratic c) (2 * z) z := by
  have h : HasStrictDerivAt (quadratic c) ((2 : ℕ) * z ^ (2 - 1)) z :=
    (hasStrictDerivAt_pow 2 z).add_const c
  convert h using 1
  norm_num

/-- **`f_c` is a local homeomorphism off the critical point.** For `z ≠ 0` (`f_c'(z)=2z≠0`), `f_c`
maps neighbourhoods of `z` bijectively onto neighbourhoods of `f_c z` (`map (f_c) (𝓝 z) = 𝓝 (f_c z)`).
The local-triviality of the collar covering: `f_c^[n]: cylinder → collar` is `2ⁿ`-to-1 and a local
homeomorphism away from the precritical orbit `⋃ₖ f_c^{-k}{0}` (the critical points of `f_c^[n]`),
so off that discrete set it is an honest covering — the analytic realization of the dyadic covering
the `σ_n` skeleton acts on. -/
theorem quadratic_map_nhds {c z : ℂ} (hz : z ≠ 0) :
    Filter.map (quadratic c) (𝓝 z) = 𝓝 (quadratic c z) :=
  (hasStrictDerivAt_quadratic c z).map_nhds_eq (by simp [hz])

/-- `f_c` as a polynomial `X² + c`. -/
noncomputable def quadraticPoly (c : ℂ) : Polynomial ℂ := X ^ 2 + C c

theorem quadraticPoly_natDegree (c : ℂ) : (quadraticPoly c).natDegree = 2 := by
  unfold quadraticPoly; compute_degree!

/-- The `n`-fold composition `f_c^[n]` as a polynomial. -/
noncomputable def quadraticPolyIterate (c : ℂ) : ℕ → Polynomial ℂ
  | 0 => X
  | n + 1 => (quadraticPoly c).comp (quadraticPolyIterate c n)

/-- **Degree of the `n`-th iterate**: `deg(f_c^[n]) = 2ⁿ`. The `2ⁿ`-fold covering degree — `f_c^[n]`
attains each value `2ⁿ` times (with multiplicity), the algebraic source of the dyadic fibre. Off
the `2ⁿ−1` critical values (images of the precritical orbit), the `2ⁿ` preimages are distinct, so
`f_c^[n]` is `2ⁿ`-to-1 there — the sheet count of the collar covering. -/
theorem quadraticPolyIterate_natDegree (c : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n).natDegree = 2 ^ n := by
  induction n with
  | zero => simp [quadraticPolyIterate]
  | succ n ih =>
    rw [quadraticPolyIterate, Polynomial.natDegree_comp, quadraticPoly_natDegree, ih, pow_succ]
    ring

/-- The iterate polynomial evaluates to the dynamical iterate: `f_c^[n]` as a polynomial agrees
with the iterated map. -/
theorem quadraticPolyIterate_eval (c : ℂ) (n : ℕ) (z : ℂ) :
    (quadraticPolyIterate c n).eval z = (quadratic c)^[n] z := by
  induction n with
  | zero => simp [quadraticPolyIterate]
  | succ n ih =>
    rw [quadraticPolyIterate, Polynomial.eval_comp, ih, Function.iterate_succ_apply',
        quadratic, quadraticPoly]
    simp [pow_two]

/-- **The fibre of `f_c^[n]` is finite (discrete).** Every value `z` has finitely many `f_c^[n]`-
preimages — the roots of the nonzero degree-`2ⁿ` polynomial `f_c^[n] − z`. The discrete-fibre input
to the even-covering structure: a covering map has discrete fibres, and here each fibre has `≤ 2ⁿ`
points (exactly `2ⁿ` off the critical values). -/
theorem quadratic_iterate_fiber_finite (c : ℂ) (n : ℕ) (z : ℂ) :
    {w | (quadratic c)^[n] w = z}.Finite := by
  have hP : (quadraticPolyIterate c n - C z) ≠ 0 := by
    intro h
    have hd : (quadraticPolyIterate c n - C z).natDegree = 2 ^ n := by
      rw [natDegree_sub_C, quadraticPolyIterate_natDegree]
    rw [h, natDegree_zero] at hd
    exact pow_ne_zero n two_ne_zero hd.symm
  have heq : {w | (quadratic c)^[n] w = z} = {w | (quadraticPolyIterate c n - C z).IsRoot w} := by
    ext w
    simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_C, quadraticPolyIterate_eval,
      sub_eq_zero]
  rw [heq]
  exact Polynomial.finite_setOf_isRoot hP

/-- **Critical points of `f_c^[n]` are finite**: the roots of `(f_c^[n])'`, a nonzero polynomial of
degree `2ⁿ−1`. Off this finite set `f_c^[n]` is a local homeomorphism. -/
theorem quadratic_iterate_critical_finite (c : ℂ) (n : ℕ) :
    {w | (quadraticPolyIterate c n).derivative.IsRoot w}.Finite := by
  apply Polynomial.finite_setOf_isRoot
  intro h
  have hd := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
  rw [quadraticPolyIterate_natDegree] at hd
  exact pow_ne_zero n two_ne_zero hd

/-- **Critical values of `f_c^[n]` are finite** (images of the `≤2ⁿ−1` critical points). The
punctured base `collar ∖ criticalValues` is where `f_c^[n]` is an honest `2ⁿ`-fold covering. -/
theorem quadratic_iterate_criticalValues_finite (c : ℂ) (n : ℕ) :
    ((quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w}).Finite :=
  (quadratic_iterate_critical_finite c n).image _

/-- **`f_c^[n]` is a local homeomorphism off its critical points.** At any non-critical `w`
(`(f_c^[n])'(w) ≠ 0`), `f_c^[n]` maps neighbourhoods bijectively. With the discrete `2ⁿ`-point
fibres and finite critical values, this is the local-homeomorphism + sheet data of the even
covering `f_c^[n]: collar∖crit → base∖critValues`. -/
theorem quadratic_iterate_map_nhds {c : ℂ} {n : ℕ} {w : ℂ}
    (hw : ¬ (quadraticPolyIterate c n).derivative.IsRoot w) :
    Filter.map ((quadratic c)^[n]) (𝓝 w) = 𝓝 ((quadratic c)^[n] w) := by
  have hev : ((quadratic c)^[n]) = fun z => (quadraticPolyIterate c n).eval z := by
    funext z; exact (quadraticPolyIterate_eval c n z).symm
  rw [hev]
  have hd : HasStrictDerivAt (fun z => (quadraticPolyIterate c n).eval z)
      ((quadraticPolyIterate c n).derivative.eval w) w := Polynomial.hasStrictDerivAt _ _
  refine hd.map_nhds_eq ?_
  rwa [Polynomial.IsRoot.def] at hw

/-- **Chain-rule derivative of the iterate**: `(f_c^[n])'(w) = ∏_{k<n} 2·f_c^[k](w)`. -/
theorem hasStrictDerivAt_quadratic_iterate (c : ℂ) (n : ℕ) (w : ℂ) :
    HasStrictDerivAt ((quadratic c)^[n])
      (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] w) w := by
  induction n with
  | zero => simpa using hasStrictDerivAt_id w
  | succ n ih =>
    rw [Function.iterate_succ', Finset.prod_range_succ, mul_comm]
    exact (hasStrictDerivAt_quadratic c ((quadratic c)^[n] w)).comp w ih

/-- **Critical points of `f_c^[n]` = the precritical orbit** `⋃_{k<n} (f_c^[k])⁻¹{0}`: `(f_c^[n])'(w)
= 0 ↔ ∃ k<n, f_c^[k](w) = 0`. So the critical values (over which the collar covering is branched)
are the finite set `{f_c^[n](w) : ∃ k<n, f_c^[k](w)=0}` — the precritical part of the dynamics. -/
theorem quadratic_iterate_deriv_eq_zero_iff (c : ℂ) (n : ℕ) (w : ℂ) :
    (quadraticPolyIterate c n).derivative.eval w = 0 ↔ ∃ k < n, (quadratic c)^[k] w = 0 := by
  have hsd : HasStrictDerivAt (fun z => (quadraticPolyIterate c n).eval z)
      ((quadraticPolyIterate c n).derivative.eval w) w := Polynomial.hasStrictDerivAt _ _
  have hev : (fun z => (quadraticPolyIterate c n).eval z) = (quadratic c)^[n] := by
    funext z; exact quadraticPolyIterate_eval c n z
  rw [hev] at hsd
  have huniq := hsd.hasDerivAt.unique (hasStrictDerivAt_quadratic_iterate c n w).hasDerivAt
  rw [huniq, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, hk0⟩
    exact ⟨k, Finset.mem_range.mp hk, by simpa using hk0⟩
  · rintro ⟨k, hk, hk0⟩
    exact ⟨k, Finset.mem_range.mpr hk, by simp [hk0]⟩

/-- **`f_c^[n]` is a proper map** (a degree-`2ⁿ` polynomial; `|f_c^[n](z)| → ∞` as `|z| → ∞`).
Properness + the local-homeomorphism-off-critical-points (`quadratic_iterate_map_nhds`) + discrete
`2ⁿ`-point fibres are exactly the hypotheses of "proper local homeomorphism ⟹ covering map": over
each non-critical value the `2ⁿ` inverse branches are disjoint and cover the fibre, giving the
even-covering trivialization. This is the data that folds into `IsCoveringMapOn (f_c^[n]) (ℂ ∖
criticalValues)`. -/
theorem quadratic_iterate_isProperMap (c : ℂ) (n : ℕ) : IsProperMap ((quadratic c)^[n]) := by
  have hev : ((quadratic c)^[n]) = (quadraticPolyIterate c n).eval := by
    funext z; exact (quadraticPolyIterate_eval c n z).symm
  rw [hev]
  apply Polynomial.isProperMap_eval
  rw [← Polynomial.natDegree_pos_iff_degree_pos, quadraticPolyIterate_natDegree]
  positivity

/-- **`f_c^[n]` is surjective** (a nonconstant polynomial over `ℂ` attains every value, by the
fundamental theorem of algebra). So every base point has a nonempty fibre — the covering is onto;
combined with properness + local-homeo, `f_c^[n]: ℂ → ℂ` is a `2ⁿ`-fold branched covering, an
honest covering over `ℂ ∖ criticalValues`. -/
theorem quadratic_iterate_surjective (c : ℂ) (n : ℕ) :
    Function.Surjective ((quadratic c)^[n]) := by
  intro z
  have hdeg : 0 < (quadraticPolyIterate c n - C z).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, natDegree_sub_C, quadraticPolyIterate_natDegree]
    positivity
  obtain ⟨w, hw⟩ := Complex.exists_root hdeg
  refine ⟨w, ?_⟩
  rw [← quadraticPolyIterate_eval]
  have hroot : (quadraticPolyIterate c n - C z).eval w = 0 := hw
  rwa [eval_sub, eval_C, sub_eq_zero] at hroot

/-- Over a non-critical value, every preimage is a non-critical point (critical points map to
critical values). So `f_c^[n]` is unbranched over `ℂ ∖ criticalValues`. -/
theorem quadratic_iterate_fiber_noncritical {c : ℂ} {n : ℕ} {z : ℂ}
    (hz : z ∉ (quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w})
    {w : ℂ} (hw : (quadratic c)^[n] w = z) :
    ¬ (quadraticPolyIterate c n).derivative.IsRoot w :=
  fun hcrit => hz ⟨w, hcrit, hw⟩

/-- **`f_c^[n]` is a local homeomorphism at every preimage of a non-critical value** (`map_nhds`).
With finite fibres (`quadratic_iterate_fiber_finite`) and properness, this is the full local-homeo
data of the even covering `f_c^[n]: ℂ∖crit → ℂ∖critValues`: each of the `2ⁿ` preimages has a chart,
and the proper-map shrinking confines `f_c^[n]⁻¹(W)` to their disjoint union. -/
theorem quadratic_iterate_map_nhds_of_noncritical {c : ℂ} {n : ℕ} {z : ℂ}
    (hz : z ∉ (quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w})
    {w : ℂ} (hw : (quadratic c)^[n] w = z) :
    Filter.map ((quadratic c)^[n]) (nhds w) = nhds z := by
  rw [quadratic_iterate_map_nhds (quadratic_iterate_fiber_noncritical hz hw), hw]

/-- The base domain `{z | f_c^[n] z ≠ 0}` of the pullback covering is open (complement of the finite
`n`-fold preimage of `0`). This is the base of `{(z,v) : v^{2ⁿ} = f_c^[n] z} → z`-plane = the
pullback of `w↦w^{2ⁿ}` along `f_c^[n]`: the covering whose deck group `μ_{2ⁿ}` FIXES `z` and scales
the `2ⁿ`-th-root coordinate `v` (≈ `φ_{c₁}`), the structurally correct carrier of `σ_n`. -/
theorem quadratic_iterate_apply_ne_zero_isOpen (c : ℂ) (n : ℕ) :
    IsOpen {z | (quadratic c)^[n] z ≠ 0} :=
  (quadratic_iterate_fiber_finite c n 0).isClosed.isOpen_compl

/-- The pullback covering space `{(z,v) : v^{2ⁿ} = f_c^[n] z, v ≠ 0}` — total space of the pullback
of `w↦w^{2ⁿ}` along `f_c^[n]`. The coordinate `v` is the `2ⁿ`-th-root branch (≈ `φ_{c₁}`). -/
def pullbackSpace (c : ℂ) (n : ℕ) : Set (ℂ × ℂ) :=
  {p | p.2 ^ (2 ^ n) = (quadratic c)^[n] p.1 ∧ p.2 ≠ 0}

/-- The deck transformation `(z,v) ↦ (z, ζ·v)`. -/
def deckMap (ζ : ℂ) : ℂ × ℂ → ℂ × ℂ := fun p => (p.1, ζ * p.2)

@[simp] theorem deckMap_fst (ζ : ℂ) (p : ℂ × ℂ) : (deckMap ζ p).1 = p.1 := rfl
@[simp] theorem deckMap_snd (ζ : ℂ) (p : ℂ × ℂ) : (deckMap ζ p).2 = ζ * p.2 := rfl

/-- **The deck transformation acts on the pullback space**, FIXING the base coordinate `z` and
scaling the root coordinate `v` by a `2ⁿ`-th root of unity `ζ`. This is the geometric `σ_n`: it
fixes `z` (hence `K = ℂ(z)`) and scales `v ≈ φ_{c₁}` by `ζ` — exactly the `DyadicMonodromyTower`
shape, now over the z-plane (the structurally correct base, unlike the dynamics covering). -/
theorem deckMap_mapsTo {c : ℂ} {n : ℕ} {ζ : ℂ} (hζ : ζ ^ (2 ^ n) = 1) :
    Set.MapsTo (deckMap ζ) (pullbackSpace c n) (pullbackSpace c n) := by
  rintro ⟨z, v⟩ ⟨hv, hv0⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hζ
    exact one_ne_zero hζ.symm
  refine ⟨?_, ?_⟩
  · show (ζ * v) ^ (2 ^ n) = (quadratic c)^[n] z
    rw [mul_pow, hζ, one_mul]; exact hv
  · show ζ * v ≠ 0
    exact mul_ne_zero hζ0 hv0

/-- The deck transformations compose by multiplication of roots of unity: `D_ζ ∘ D_η = D_{ζη}`
(the `μ_{2ⁿ}`-action). -/
theorem deckMap_comp (ζ η : ℂ) : deckMap ζ ∘ deckMap η = deckMap (ζ * η) := by
  funext p
  simp only [deckMap, Function.comp_apply, Prod.mk.injEq, true_and, mul_assoc]

/-- **Fibers of the pullback covering are `μ_{2ⁿ}`-orbits (regular/Galois covering).** Two points
over the same `z` differ by a deck transformation `D_ζ` with `ζ` a `2ⁿ`-th root of unity — the deck
group `μ_{2ⁿ}` acts simply transitively on each fibre. Hence the covering's monodromy IS the deck
action `v ↦ ζ·v`, i.e. `σ_n(v) = ζ·v` with `v ≈ φ_{c₁}`: the `DyadicMonodromyTower` scaling, realized
geometrically over the z-plane (so `σ_n` fixes `z`, and `φ_{c₂}`/`z` are pulled back from the base). -/
theorem pullback_fiber_deck {c : ℂ} {n : ℕ} {z v₁ v₂ : ℂ}
    (h₁ : (z, v₁) ∈ pullbackSpace c n) (h₂ : (z, v₂) ∈ pullbackSpace c n) :
    (v₁ / v₂) ^ (2 ^ n) = 1 ∧ (z, v₁) = deckMap (v₁ / v₂) (z, v₂) := by
  obtain ⟨hv1, hv10⟩ := h₁
  obtain ⟨hv2, hv20⟩ := h₂
  have hne : (quadratic c)^[n] z ≠ 0 := by rw [← hv2]; exact pow_ne_zero _ hv20
  refine ⟨?_, ?_⟩
  · rw [div_pow, hv1, hv2, div_self hne]
  · simp only [deckMap, Prod.mk.injEq, true_and]
    rw [div_mul_cancel₀ _ hv20]

end Bottcher
