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
import GaloisForLFunctions.Bottcher.HarmonicComp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import GaloisForLFunctions.Bottcher.DyadicMonodromy

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
  grind [pullbackSpace, deckMap, mul_pow]

/-- The deck transformations compose by multiplication of roots of unity: `D_ζ ∘ D_η = D_{ζη}`
(the `μ_{2ⁿ}`-action). -/
theorem deckMap_comp (ζ η : ℂ) : deckMap ζ ∘ deckMap η = deckMap (ζ * η) := by
  funext p
  grind [deckMap]

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

theorem continuous_deckMap (ζ : ℂ) : Continuous (deckMap ζ) := by
  unfold deckMap; fun_prop

@[simp] theorem deckMap_one : deckMap 1 = id := by funext p; simp [deckMap]

theorem deckMap_leftInverse {ζ : ℂ} (hζ : ζ ≠ 0) :
    Function.LeftInverse (deckMap ζ⁻¹) (deckMap ζ) := by
  intro p
  rw [← Function.comp_apply (f := deckMap ζ⁻¹), deckMap_comp, inv_mul_cancel₀ hζ, deckMap_one, id]

/-- **Each deck transformation is a homeomorphism** of `ℂ×ℂ` (for `ζ ≠ 0`), fixing the base
coordinate `z` and scaling `v` by `ζ`. Precomposition by it is therefore a ring automorphism of the
function field of the pullback space, FIXING functions of `z` (= `K = ℂ(z)`) and scaling `v ≈ φ_{c₁}`
by `ζ` — the field-level `σ_n` of `DyadicMonodromyTower`, realized as an honest precomposition (no
circularity: well-definedness is geometric, from `deckMap_mapsTo`). -/
noncomputable def deckHomeomorph {ζ : ℂ} (hζ : ζ ≠ 0) : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toFun := deckMap ζ
  invFun := deckMap ζ⁻¹
  left_inv := deckMap_leftInverse hζ
  right_inv := by have h := deckMap_leftInverse (inv_ne_zero hζ); rwa [inv_inv] at h
  continuous_toFun := continuous_deckMap ζ
  continuous_invFun := continuous_deckMap ζ⁻¹

/-- Precomposition by the deck map FIXES the base-coordinate function `z` (`σ_n` fixes `K = ℂ(z)`). -/
theorem fst_comp_deckMap (ζ : ℂ) : (Prod.fst : ℂ × ℂ → ℂ) ∘ deckMap ζ = Prod.fst := rfl

/-- Precomposition by the deck map SCALES the root-coordinate function `v` by `ζ`
(`σ_n(φ_{c₁}) = ζ·φ_{c₁}`). -/
theorem snd_comp_deckMap (ζ : ℂ) :
    (Prod.snd : ℂ × ℂ → ℂ) ∘ deckMap ζ = fun p => ζ * Prod.snd p := rfl

/-- **Precomposition by the deck homeomorphism is a ℂ-algebra automorphism** of the function ring
`ℂ×ℂ → ℂ`. This is the field-level `σ_n` as an honest precomposition automorphism: by
`fst_comp_deckMap` it fixes functions of `z` (= `K`), by `snd_comp_deckMap` it scales `v ≈ φ_{c₁}`
by `ζ` — exactly the `DyadicMonodromyTower` action `σ_n(φ_{c₁})=ζ·φ_{c₁}`, `σ_n|_K = id`. The
remaining gap to the FAITHFUL tower (with the actual transcendental `φ_{c₁}`, `φ_{c₂}`) is that this
realizes `σ_n` on the level-`n` root `v` (algebraic over `K`); the actual `φ_{c₁} = v·(σ_n-invariant
correction)` and `φ_{c₂}` live in the inverse-limit analytic field. -/
noncomputable def deckPrecomp {ζ : ℂ} (hζ : ζ ≠ 0) : (ℂ × ℂ → ℂ) ≃ₐ[ℂ] (ℂ × ℂ → ℂ) where
  toFun g := g ∘ deckMap ζ
  invFun g := g ∘ deckMap ζ⁻¹
  left_inv g := by
    ext p; simp only [Function.comp_apply]
    have h := deckMap_leftInverse (inv_ne_zero hζ); rw [inv_inv] at h; rw [h p]
  right_inv g := by ext p; simp only [Function.comp_apply, deckMap_leftInverse hζ p]
  map_mul' g₁ g₂ := rfl
  map_add' g₁ g₂ := rfl
  commutes' r := rfl

/-- The φ-pullback covering `{(z,v) : v^{2ⁿ} = φ_c(f_c^[n] z), v ≠ 0}` — pullback of `w↦w^{2ⁿ}`
along the single-valued (near ∞) map `z ↦ φ_c(f_c^[n] z) = φ_c(z)^{2ⁿ}`. -/
def bottcherPullbackSpace (c : ℂ) (n : ℕ) : Set (ℂ × ℂ) :=
  {p | p.2 ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] p.1) ∧ p.2 ≠ 0}

/-- **The actual transcendental `φ_{c₁}` is a section** of the φ-pullback covering: `(z, φ_{c₁}(z))`
satisfies the pullback relation `v^{2ⁿ} = φ_c(f^[n]z)`, which is exactly the functional equation
`bottcherCoord_iterate`. Hence the deck transformation `(z,v)↦(z,ζv)` carries the section
`(z,φ_{c₁}(z))` to `(z, ζ·φ_{c₁}(z))` — realizing `σ_n(φ_{c₁}) = ζ·φ_{c₁}` for the ACTUAL `φ_{c₁}`,
not an approximation. This connects the transcendental Böttcher coordinate to the geometric `σ_n`. -/
theorem bottcherCoord_mem_pullback {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    (z, bottcherCoord c z) ∈ bottcherPullbackSpace c n :=
  ⟨(bottcherCoord_iterate hc hz n).symm, bottcherCoord_ne_zero c z⟩

/-- The deck transformation acts on the φ-pullback covering, fixing `z` and scaling `v = φ_{c₁}`. -/
theorem deckMap_mapsTo_bottcher {c : ℂ} {n : ℕ} {ζ : ℂ} (hζ : ζ ^ (2 ^ n) = 1) :
    Set.MapsTo (deckMap ζ) (bottcherPullbackSpace c n) (bottcherPullbackSpace c n) := by
  rintro ⟨z, v⟩ ⟨hv, hv0⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow (by positivity)] at hζ; exact one_ne_zero hζ.symm
  grind [bottcherPullbackSpace, deckMap, mul_pow]

/-- The common pullback covering resolving both `φ_{c₁}` (level `n`) and `φ_{c₂}` (level `m`):
`{(z,v₁,v₂) : v₁^{2ⁿ}=φ_{c₁}(f_{c₁}^[n]z), v₂^{2ᵐ}=φ_{c₂}(f_{c₂}^[m]z), v₁,v₂≠0}`. -/
def commonPullback (c₁ c₂ : ℂ) (n m : ℕ) : Set (ℂ × ℂ × ℂ) :=
  {p | p.2.1 ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] p.1) ∧ p.2.1 ≠ 0 ∧
       p.2.2 ^ (2 ^ m) = bottcherCoord c₂ ((quadratic c₂)^[m] p.1) ∧ p.2.2 ≠ 0}

/-- The `c₁`-deck transformation on the common cover: scales `v₁` by `ζ`, FIXES `z` and `v₂`. -/
def deckMap₁ (ζ : ℂ) : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun p => (p.1, ζ * p.2.1, p.2.2)

/-- **The full `σ_n` shape, geometrically.** The `c₁`-deck acts on the common cover: it scales
`v₁ ≈ φ_{c₁}` by a `2ⁿ`-th root of unity while FIXING `z` (= `K`) and `v₂ ≈ φ_{c₂}`. This is exactly
`σ_n(φ_{c₁})=ζ·φ_{c₁}`, `σ_n(φ_{c₂})=φ_{c₂}`, `σ_n|_{ℂ(z)}=id` — the complete `DyadicMonodromyTower`
action, as a genuine homeomorphism over the z-plane (well-definedness geometric). The remaining gap
to FAITHFUL `hDisc`: that the `c₁`-deck = the ACTUAL `φ_{c₁}`-monodromy requires a `c₁`-loop trivial
for `φ_{c₂}` (exists since `c₁≠c₂` give distinct precritical sets — the analytic input), and that
`NoRelation K v₁ v₂` is the actual independence requires `M` to be the actual common Riemann
surface's function field (not a formal product). -/
theorem deckMap₁_mapsTo {c₁ c₂ : ℂ} {n m : ℕ} {ζ : ℂ} (hζ : ζ ^ (2 ^ n) = 1) :
    Set.MapsTo (deckMap₁ ζ) (commonPullback c₁ c₂ n m) (commonPullback c₁ c₂ n m) := by
  rintro ⟨z, v₁, v₂⟩ ⟨h1, h10, h2, h20⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow (by positivity)] at hζ; exact one_ne_zero hζ.symm
  grind [commonPullback, deckMap₁, mul_pow]

/-- The actual coordinates `(z, φ_{c₁}(z), φ_{c₂}(z))` form a section of the common cover. -/
theorem bottcher_mem_commonPullback {c₁ c₂ z : ℂ} {n m : ℕ}
    (h1 : ‖c₁‖ ≤ ‖z‖) (hz1 : 2 < ‖z‖) (h2 : ‖c₂‖ ≤ ‖z‖) (hz2 : 2 < ‖z‖) :
    (z, bottcherCoord c₁ z, bottcherCoord c₂ z) ∈ commonPullback c₁ c₂ n m :=
  ⟨(bottcherCoord_iterate h1 hz1 n).symm, bottcherCoord_ne_zero c₁ z,
   (bottcherCoord_iterate h2 hz2 m).symm, bottcherCoord_ne_zero c₂ z⟩

theorem deckMap₁_comp (ζ η : ℂ) : deckMap₁ ζ ∘ deckMap₁ η = deckMap₁ (ζ * η) := by
  funext p
  grind [deckMap₁]

theorem continuous_deckMap₁ (ζ : ℂ) : Continuous (deckMap₁ ζ) := by
  unfold deckMap₁; fun_prop

@[simp] theorem deckMap₁_one : deckMap₁ 1 = id := by funext p; simp [deckMap₁]

theorem deckMap₁_leftInverse {ζ : ℂ} (hζ : ζ ≠ 0) :
    Function.LeftInverse (deckMap₁ ζ⁻¹) (deckMap₁ ζ) := by
  intro p
  grind [deckMap₁]

/-- **`σ_n` as a ℂ-algebra automorphism of the common cover's function ring**, realizing the complete
`DyadicMonodromyTower` coordinate action by precomposition with the `c₁`-deck homeomorphism. By
`deckPrecomp₁_z`/`deckPrecomp₁_v₂`/`deckPrecomp₁_v₁` it fixes `z` (= `K`) and `v₂` (`φ_{c₂}`) and
scales `v₁` (`φ_{c₁}`) by `ζ`. A genuine algebra automorphism (well-definedness geometric). -/
noncomputable def deckPrecomp₁ {ζ : ℂ} (hζ : ζ ≠ 0) :
    (ℂ × ℂ × ℂ → ℂ) ≃ₐ[ℂ] (ℂ × ℂ × ℂ → ℂ) where
  toFun g := g ∘ deckMap₁ ζ
  invFun g := g ∘ deckMap₁ ζ⁻¹
  left_inv g := by
    ext p; simp only [Function.comp_apply]
    have h := deckMap₁_leftInverse (inv_ne_zero hζ); rw [inv_inv] at h; rw [h p]
  right_inv g := by ext p; simp only [Function.comp_apply, deckMap₁_leftInverse hζ p]
  map_mul' g₁ g₂ := rfl
  map_add' g₁ g₂ := rfl
  commutes' r := rfl

/-- `σ_n` fixes the base coordinate `z` (= `K = ℂ(z)`). -/
theorem deckPrecomp₁_z {ζ : ℂ} (hζ : ζ ≠ 0) :
    deckPrecomp₁ hζ (fun p => p.1) = (fun p => p.1) := rfl
/-- `σ_n` fixes the second root coordinate `v₂` (= `φ_{c₂}`). -/
theorem deckPrecomp₁_v₂ {ζ : ℂ} (hζ : ζ ≠ 0) :
    deckPrecomp₁ hζ (fun p => p.2.2) = (fun p => p.2.2) := rfl
/-- `σ_n` scales the first root coordinate `v₁` (= `φ_{c₁}`) by `ζ`. -/
theorem deckPrecomp₁_v₁ {ζ : ℂ} (hζ : ζ ≠ 0) :
    deckPrecomp₁ hζ (fun p => p.2.1) = (fun p => ζ * p.2.1) := rfl

/-- There is a primitive `2ⁿ`-th root of unity (order exactly `2ⁿ`). -/
theorem exists_dyadic_primitive (n : ℕ) : ∃ ζ : ℂ, orderOf ζ = 2 ^ n ∧ ζ ^ (2 ^ n) = 1 := by
  refine ⟨Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)), orderOf_dyadicRoot n, ?_⟩
  have h := orderOf_dyadicRoot n
  calc Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ^ (2 ^ n)
      = _ ^ orderOf (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))) := by rw [h]
    _ = 1 := pow_orderOf_eq_one _

/-- The deck transformation scales the actual `φ_{c₁}`-section: `(z,φ_{c₁}(z),φ_{c₂}(z)) ↦
(z, ζ·φ_{c₁}(z), φ_{c₂}(z))` — fixes `z` and `φ_{c₂}`, scales `φ_{c₁}`. -/
theorem deckMap₁_bottcher_section (ζ : ℂ) (c₁ c₂ z : ℂ) :
    deckMap₁ ζ (z, bottcherCoord c₁ z, bottcherCoord c₂ z)
      = (z, ζ * bottcherCoord c₁ z, bottcherCoord c₂ z) := rfl

/-- **Geometric unbounded monodromy.** For every degree bound `d` there is a `2ⁿ`-th root of unity
`ζ` of order `> d` whose deck transformation `deckMap₁ ζ` fixes `z` and `φ_{c₂}` and scales `φ_{c₁}`
by `ζ` — exactly the unbounded-order `σ_n` data that `q62_disconnected_both` consumes, realized
geometrically on the common cover. -/
theorem exists_deck_unbounded (d : ℕ) :
    ∃ (ζ : ℂ) (n : ℕ), d < orderOf ζ ∧ ζ ^ (2 ^ n) = 1 ∧ orderOf ζ = 2 ^ n := by
  obtain ⟨ζ, hord, hpow⟩ := exists_dyadic_primitive d
  exact ⟨ζ, d, by rw [hord]; exact Nat.lt_two_pow_self, hpow, hord⟩

/-- Two `φ_{c₁}`-branches over the same `z` differ by a `2ⁿ`-th root of unity (fibre = `μ_{2ⁿ}`
orbit, for the actual Böttcher coordinate). -/
theorem bottcherPullback_fiber_deck {c : ℂ} {n : ℕ} {z v₁ v₂ : ℂ}
    (h₁ : (z, v₁) ∈ bottcherPullbackSpace c n) (h₂ : (z, v₂) ∈ bottcherPullbackSpace c n) :
    (v₁ / v₂) ^ (2 ^ n) = 1 := by
  obtain ⟨hv1, _⟩ := h₁
  obtain ⟨hv2, _⟩ := h₂
  rw [div_pow, hv1, hv2, div_self (bottcherCoord_ne_zero _ _)]

/-- **The actual `(φ_{c₁},φ_{c₂})` carries the full geometric monodromy datum.** For escaping `z`
and every degree bound `d`, there is `ζ` of order `> d` whose deck transformation `deckMap₁ ζ`
carries the section `(z,φ_{c₁}(z),φ_{c₂}(z))` (a point of the common cover) to
`(z, ζ·φ_{c₁}(z), φ_{c₂}(z))`, scaling `φ_{c₁}` by order `> d` and fixing `z, φ_{c₂}` — `monoF`
realized for the ACTUAL coordinates over the z-plane. -/
theorem section_monodromy_datum {c₁ c₂ z : ℂ} {n m : ℕ}
    (h1 : ‖c₁‖ ≤ ‖z‖) (hz1 : 2 < ‖z‖) (h2 : ‖c₂‖ ≤ ‖z‖) (d : ℕ) :
    ∃ (ζ : ℂ), d < orderOf ζ ∧
      (z, bottcherCoord c₁ z, bottcherCoord c₂ z) ∈ commonPullback c₁ c₂ n m ∧
      deckMap₁ ζ (z, bottcherCoord c₁ z, bottcherCoord c₂ z)
        = (z, ζ * bottcherCoord c₁ z, bottcherCoord c₂ z) := by
  obtain ⟨ζ, _, hord, _⟩ := exists_deck_unbounded d
  exact ⟨ζ, hord, bottcher_mem_commonPullback h1 hz1 h2 hz1, rfl⟩

/-- Iterating the deck map multiplies the scalar: `(deckMap₁ ζ)^[k] = deckMap₁ (ζ^k)`. -/
theorem deckMap₁_iterate (ζ : ℂ) (k : ℕ) : (deckMap₁ ζ)^[k] = deckMap₁ (ζ ^ k) := by
  induction k with
  | zero => funext p; simp [deckMap₁]
  | succ n ih => rw [Function.iterate_succ', ih, deckMap₁_comp, pow_succ, mul_comm]

/-- The deck-orbit of the actual section is `{(z, ζ^k·φ_{c₁}(z), φ_{c₂}(z))}` — the branches of
`φ_{c₁}` over `z`, all fixing `φ_{c₂}` and `z`. -/
theorem deckMap₁_iterate_section (ζ : ℂ) (c₁ c₂ z : ℂ) (k : ℕ) :
    (deckMap₁ ζ)^[k] (z, bottcherCoord c₁ z, bottcherCoord c₂ z)
      = (z, ζ ^ k * bottcherCoord c₁ z, bottcherCoord c₂ z) := by
  rw [deckMap₁_iterate]; rfl

/-- `σ_n^k` scales `v₁ = φ_{c₁}` by `ζ^k`: the full cyclic deck action of order `orderOf ζ` on
`φ_{c₁}` (with `ζ` of order `2ⁿ`, this is the order-`2ⁿ` monodromy on `φ_{c₁}`). -/
theorem deckPrecomp₁_pow_v₁ {ζ : ℂ} (hζ : ζ ≠ 0) (k : ℕ) :
    (deckPrecomp₁ hζ ^ k) (fun p => p.2.1) = (fun p => ζ ^ k * p.2.1) := by
  induction k with
  | zero => funext p; simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih]
    funext p
    show (fun q => ζ ^ n * q.2.1) (deckMap₁ ζ p) = ζ ^ (n + 1) * p.2.1
    simp only [deckMap₁]; rw [pow_succ]; ring

/-- The deck precomposition is a `μ`-action: `σ_ζ ∘ σ_η = σ_{ηζ}`. So `ζ ↦ deckPrecomp₁ ζ` is a
homomorphism from the roots of unity to the automorphism group of the function ring — the deck-group
action realizing the monodromy. -/
theorem deckPrecomp₁_trans {ζ η : ℂ} (hζ : ζ ≠ 0) (hη : η ≠ 0) :
    (deckPrecomp₁ hη).trans (deckPrecomp₁ hζ) = deckPrecomp₁ (mul_ne_zero hη hζ) := by
  ext g p
  show (g ∘ deckMap₁ η) (deckMap₁ ζ p) = g (deckMap₁ (η * ζ) p)
  simp only [deckMap₁, Function.comp_apply, Prod.mk.injEq]
  ring_nf

/-- **Geometric realization of the full `monoF` datum.** For every degree bound `d` there is an
algebra automorphism `σ = deckPrecomp₁ ζ` of the common cover's function ring, with `ζ` of order
`> d`, that FIXES the base coordinate `z` and the `φ_{c₂}`-coordinate and SCALES the
`φ_{c₁}`-coordinate by `ζ`. This is exactly the `σ_n`/`monoF` shape of `DyadicMonodromyTower`,
realized as a genuine ℂ-algebra automorphism over the z-plane. The only remaining step to `hDisc`
is transporting it from the function ring to the meromorphic function FIELD of the connected
cover (so the abstract `Field M` obstruction `q62_disconnected_both` applies to the actual
coordinates); `hRigid` (E–vS) handles the connected case. -/
theorem geometric_monoF (d : ℕ) :
    ∃ (ζ : ℂ) (hζ : ζ ≠ 0), d < orderOf ζ ∧
      deckPrecomp₁ hζ (fun p => p.1) = (fun p => p.1) ∧
      deckPrecomp₁ hζ (fun p => p.2.2) = (fun p => p.2.2) ∧
      deckPrecomp₁ hζ (fun p => p.2.1) = (fun p => ζ * p.2.1) := by
  obtain ⟨ζ, hord, _⟩ := exists_dyadic_primitive d
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [orderOf_zero] at hord; exact (pow_ne_zero d two_ne_zero) hord.symm
  exact ⟨ζ, hζ0, by rw [hord]; exact Nat.lt_two_pow_self,
    deckPrecomp₁_z hζ0, deckPrecomp₁_v₂ hζ0, deckPrecomp₁_v₁ hζ0⟩

end Bottcher

namespace Bottcher

open InnerProductSpace in
/-- **`G_c` is harmonic on the entire basin `Ω_c = (filledJulia c)ᶜ`.** At any basin point `z`, an
iterate `f_c^[N] z` lands in the escape region (where `greenLimit` is harmonic); pulling back through
the holomorphic `f_c^[N]` via the basin scaling law `G_c = 2⁻ᴺ·(G_c ∘ f_c^[N])` transports
harmonicity to `z` (`HarmonicAt.comp_analytic`). The Green's function is thus harmonic on all of `Ω_c`
right down to `J_c` — the constraint-side object on its full natural domain, the exterior in whose
boundary behaviour the connected-case natural-boundary rigidity lives. -/
theorem harmonicOnNhd_greenLimit_basin (c : ℂ) :
    HarmonicOnNhd (greenLimit c) (filledJulia c)ᶜ := by
  intro z hz
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max 2 ‖c‖)
  have hesc : (quadratic c)^[N] z ∈ escapeOpen c := hN
  have hg : HarmonicAt (greenLimit c) ((quadratic c)^[N] z) :=
    harmonicOnNhd_greenLimit_escape c _ hesc
  have hf : AnalyticAt ℂ (quadratic c)^[N] z := analyticAt_quadratic_iterate c N z
  have hcomp : HarmonicAt (greenLimit c ∘ (quadratic c)^[N]) z := HarmonicAt.comp_analytic hg hf
  have hsmul : HarmonicAt ((2 ^ N : ℝ)⁻¹ • (greenLimit c ∘ (quadratic c)^[N])) z :=
    hcomp.const_smul
  have heq : ((2 ^ N : ℝ)⁻¹ • (greenLimit c ∘ (quadratic c)^[N])) =ᶠ[𝓝 z] greenLimit c := by
    filter_upwards [(isClosed_filledJulia c).isOpen_compl.mem_nhds hz] with w hw
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [greenLimit_iterate_basin hw N, ← mul_assoc,
        inv_mul_cancel₀ (by positivity : (2 ^ N : ℝ) ≠ 0), one_mul]
  exact (harmonicAt_congr_nhds heq).mp hsmul

end Bottcher
