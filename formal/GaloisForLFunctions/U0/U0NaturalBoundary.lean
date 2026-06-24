/-
# Natural boundary of u₀ at the unit circle

The function `u₀(z) = ∑_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}` has the unit circle `{|z|=1}` as
a natural boundary — it cannot be analytically continued across any arc of the unit circle.

## Proof strategy

Substituting `w = 1/z`, the companion series is `U₀(w) = u₀(1/w) = ∑_{n≥0} 2^{-(n+1)} w^{2^{n+1}-1}`.
- The exponents `2^{n+1}-1` satisfy `lim_{n→∞} λ_{n+1}/λ_n = 2 > 1`, so the series has
  **Hadamard gaps** (Ostrowski–Hadamard gap theorem).
- Every point on the unit circle `|w|=1` is a singular point of U₀.
- Equivalently, every point on the unit circle `|z|=1` is a singular point of u₀.

In Lean: stated with the genuine *analytic-continuation* predicate `ContinuesAcross` (NOT `¬AnalyticAt`
of the junk-extended tsum, which is trivially true for the wrong reason — see the ⚠ note below).
`u0_natural_boundary` is **proven modulo a single leaf lemma** `seed_singularity` — ∃ one boundary
point of non-continuation (the genuine analytic core, Mathlib-missing; far weaker than the full
Ostrowski–Hadamard gap theorem, which asserts *every* point fails). Everything else is proven here:
convergence/divergence (radius = 1), the Mahler-equation propagation `continues_sq`, closedness
`isClosed_singular`, dyadic-root density `dense_dyadic_roots`, the root induction and the closure.
-/
import GaloisForLFunctions.U0.U0Series
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.RingTheory.Algebraic.Basic

open Complex Filter Topology U0

namespace U0NaturalBoundary

/-! ## Radius of convergence of U₀ = 1 -/

/-- The companion series U₀(w) = u₀(1/w) converges absolutely for |w| < 1. -/
theorem U0_summable_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (2 : ℝ) ^ (-(n + 1 : ℤ)))
  · exact summable_two_zpow_neg
  · intro n
    rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_two]
    have hw1 : ‖w‖ ≤ 1 := le_of_lt hw
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    have hexp : (0 : ℤ) ≤ 2 ^ (n + 1) - 1 := by
      have h : (1 : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast Nat.one_le_two_pow
      linarith
    have hwpow : ‖w‖ ^ (2 ^ (n + 1) - 1 : ℤ) ≤ 1 := by
      lift (2 ^ (n + 1) - 1 : ℤ) to ℕ using hexp with m hm
      rw [zpow_natCast]
      exact pow_le_one₀ hw0 hw1
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(↑n + 1 : ℤ)) := zpow_nonneg (by norm_num) _
    linarith [mul_le_mul_of_nonneg_left hwpow h2]

/-! ## The single irreducible analytic core

⚠ **Correctness note (junk-extension trap).** `∑'` is `0` wherever the series diverges, so the
*literal* tsum function jumps to `0` across `‖·‖=1` and is trivially non-`AnalyticAt` there — for the
WRONG reason (a discontinuous junk extension, which an *algebraic* function would share). That trivial
statement does **not** encode a natural boundary and does **not** imply transcendence. The genuine
content is *analytic continuation from the domain of convergence*, captured by `ContinuesAcross`:
an analytic `g` near `z₀` agreeing with the function on the convergence-side neighborhood. Junk values
off the domain cannot satisfy this, so it carries real content. -/

/-- `f` continues analytically across `z₀` from the domain `D`: some `g` analytic at `z₀` agrees with
`f` on a `D`-side neighborhood of `z₀`. Its negation, for every boundary point, is a *genuine* natural
boundary (unlike `¬ AnalyticAt` of a junk-extended tsum). -/
def ContinuesAcross (f : ℂ → ℂ) (D : Set ℂ) (z₀ : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ ∀ᶠ w in nhdsWithin z₀ D, g w = f w

/-- The exterior `{z | 1 < ‖z‖}`, the genuine domain of convergence of `u₀`. -/
def Ext : Set ℂ := {z : ℂ | 1 < ‖z‖}

theorem isOpen_Ext : IsOpen Ext := isOpen_lt continuous_const continuous_norm

theorem ne_zero_of_Ext {z : ℂ} (hz : z ∈ Ext) : z ≠ 0 := by
  intro h; rw [h] at hz; simp only [Ext, Set.mem_setOf_eq, norm_zero] at hz; linarith

/-- Each term `2^{-(n+1)}·z^{-(2^{n+1}-1)}` is holomorphic on the exterior (`z ≠ 0` there). -/
theorem term_differentiableOn_Ext (n : ℕ) : DifferentiableOn ℂ
    (fun z : ℂ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))) Ext :=
  DifferentiableOn.const_mul
    (DifferentiableOn.zpow differentiableOn_id (Or.inl (fun x hx => ne_zero_of_Ext hx))) _

/-- **u₀ is holomorphic on the exterior `Ext` (PROVEN).** Weierstrass M-test: each term is
holomorphic on `Ext` and bounded there by the summable `2^{-(n+1)}` (`norm_u0_term_le`). -/
theorem u0_differentiableOn_Ext : DifferentiableOn ℂ u0 Ext :=
  differentiableOn_tsum_of_summable_norm summable_two_zpow_neg
    term_differentiableOn_Ext isOpen_Ext
    (fun n w hw => norm_u0_term_le (le_of_lt hw) n)

/-- **u₀ is analytic on the exterior `Ext` (PROVEN).** The analytic realization underlying the
natural-boundary statement: on `Ext`, `u₀` is the genuine convergent sum, not a junk extension. -/
theorem u0_analyticOnNhd_Ext : AnalyticOnNhd ℂ u0 Ext :=
  u0_differentiableOn_Ext.analyticOnNhd isOpen_Ext

/-- **Propagation by the Mahler functional equation (step 3, PROVEN).**
If `u₀` continues analytically across `z₀ ≠ 0`, it continues across `z₀²`.

The continuation `g` of `u₀` near `z₀` is pushed to a continuation of `u₀` near `z₀²` via the local
analytic inverse `s` of `z ↦ z²` (`analyticAt_localInverse`, valid since `z₀ ≠ 0`): set
`h(v) = 2·s(v)·g(s(v)) − 1`. On the exterior side, `s(v) ∈ Ext`, `g(s v) = u₀(s v)`, `(s v)² = v`, and
the functional equation `2·(s v)·u₀(s v) = 1 + u₀((s v)²)` give `h(v) = u₀(v)`. This is the step the
generic Ostrowski–Hadamard proof lacks — it is special to series with a Mahler equation. -/
theorem continues_sq {z₀ : ℂ} (hz0 : z₀ ≠ 0) (h : ContinuesAcross u0 Ext z₀) :
    ContinuesAcross u0 Ext (z₀ ^ 2) := by
  obtain ⟨g, hg_an, hg_eq⟩ := h
  have hf : AnalyticAt ℂ (fun z : ℂ => z ^ 2) z₀ := by fun_prop
  have hfderiv : deriv (fun z : ℂ => z ^ 2) z₀ ≠ 0 := by
    rw [show deriv (fun z : ℂ => z ^ 2) z₀ = 2 * z₀ from by simp]; simp [hz0]
  set s := hf.hasStrictDerivAt.localInverse _ _ _ hfderiv with hs_def
  have hs_an : AnalyticAt ℂ s (z₀ ^ 2) := hf.analyticAt_localInverse hfderiv
  have hs_pt : s (z₀ ^ 2) = z₀ := by
    have := (hf.hasStrictDerivAt.eventually_left_inverse hfderiv).self_of_nhds
    simpa [hs_def] using this
  have hs_rinv : ∀ᶠ v in nhds (z₀ ^ 2), (s v) ^ 2 = v :=
    hf.hasStrictDerivAt.eventually_right_inverse hfderiv
  refine ⟨fun v => 2 * s v * g (s v) - 1, ?_, ?_⟩
  · have hgs : AnalyticAt ℂ (fun v => g (s v)) (z₀ ^ 2) := by
      have hg' : AnalyticAt ℂ g (s (z₀ ^ 2)) := by rw [hs_pt]; exact hg_an
      exact hg'.comp hs_an
    exact (((analyticAt_const.mul hs_an).mul hgs).sub analyticAt_const)
  · have ha : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), (s v) ^ 2 = v := hs_rinv.filter_mono nhdsWithin_le_nhds
    have hv_ext : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), v ∈ Ext := self_mem_nhdsWithin
    have hb : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), s v ∈ Ext := by
      filter_upwards [ha, hv_ext] with v hva hvb
      have hvn : 1 < ‖v‖ := hvb
      rw [← hva, norm_pow] at hvn
      have hsn : 0 ≤ ‖s v‖ := norm_nonneg _
      show 1 < ‖s v‖
      nlinarith [hvn, hsn]
    have hc : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), g (s v) = u0 (s v) := by
      have htends : Tendsto s (𝓝[Ext] (z₀ ^ 2)) (𝓝[Ext] z₀) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, hb⟩
        have hcont : Tendsto s (𝓝 (z₀ ^ 2)) (𝓝 z₀) := by
          have := hs_an.continuousAt; rw [ContinuousAt, hs_pt] at this; exact this
        exact hcont.mono_left nhdsWithin_le_nhds
      exact htends.eventually hg_eq
    filter_upwards [ha, hb, hc] with v hva hvb hvc
    have hsv1 : 1 ≤ ‖s v‖ := le_of_lt hvb
    have hfe := functional_equation hsv1
    show 2 * s v * g (s v) - 1 = u0 v
    rw [hva] at hfe
    rw [hvc, hfe]; ring

/-- **Singularity spreads to square roots (contrapositive of `continues_sq`).**
If `u₀` does not continue across `z₀² (z₀ ≠ 0)`, it does not continue across `z₀`. -/
theorem not_continues_of_sq {z₀ : ℂ} (hz0 : z₀ ≠ 0)
    (h : ¬ ContinuesAcross u0 Ext (z₀ ^ 2)) : ¬ ContinuesAcross u0 Ext z₀ :=
  fun hc => h (continues_sq hz0 hc)

/-- **The set of continuation points is open (step 5, PROVEN).**
If `u₀` continues across `z₀` via `g`, the *same* `g` witnesses continuation across every nearby `z`
(`g` is analytic on a neighborhood, and the agreement set `W ∩ Ext` is an `Ext`-neighborhood of each
`z ∈ W`). Hence the singular set is closed. -/
theorem isOpen_continues : IsOpen {z : ℂ | ContinuesAcross u0 Ext z} := by
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨g, hg_an, hg_eq⟩
  obtain ⟨W, hWopen, hz₀W, hWsub⟩ := mem_nhdsWithin.mp hg_eq
  have hWnhds : W ∈ 𝓝 z₀ := hWopen.mem_nhds hz₀W
  have hAnhds : {z | AnalyticAt ℂ g z} ∈ 𝓝 z₀ := (isOpen_analyticAt ℂ g).mem_nhds hg_an
  filter_upwards [hWnhds, hAnhds] with z hzW hzAn
  exact ⟨g, hzAn, mem_nhdsWithin.mpr ⟨W, hWopen, hzW, hWsub⟩⟩

/-- The singular set `{z | ¬ ContinuesAcross u0 Ext z}` is closed. -/
theorem isClosed_singular : IsClosed {z : ℂ | ¬ ContinuesAcross u0 Ext z} :=
  isOpen_continues.isClosed_compl

/-- **Seed singularity (step 2 — the one genuine irreducible analytic core).**
`u₀` fails to continue across **some** unit-circle point.

What is already in place (PROVEN above): `u0_analyticOnNhd_Ext` (u₀ analytic on the exterior, the
genuine convergent realization), and the radius bracket — convergence on `Ext` plus the
doubly-exponential divergence `U0term_norm_tendsto_atTop` for `‖·‖>1`.

The remaining gap is the **gluing-to-larger-radius** step: assuming `u₀` continues across *every*
boundary point, compactness of the circle yields finitely many continuations that agree with `u₀` on
the connected exterior overlaps (identity theorem) and so glue to one function analytic on
`{‖z‖ > 1−δ}`; its companion power series (in `1/z`) then has radius `> 1` (`HasFPowerSeriesOnBall`),
whose terms must `→0` past `‖·‖=1` — contradicting `U0term_norm_tendsto_atTop`. This `∃`-of-a-boundary-
singularity is the lone Mathlib-missing input; it is *far* weaker than the full Ostrowski–Hadamard gap
theorem (which asserts *every* point fails), but the sheaf-gluing of analytic continuations has no
ready Mathlib API, so it is isolated here. -/
theorem seed_singularity : ∃ z₁ : ℂ, ‖z₁‖ = 1 ∧ ¬ ContinuesAcross u0 Ext z₁ := by
  sorry

/-- Lipschitz-type bound on the imaginary axis: `‖exp(aI) − exp(bI)‖ ≤ 2·|a−b|` for `|a−b| ≤ 1`.
(`exp(aI) − exp(bI) = exp(bI)·(exp((a−b)I) − 1)` and `‖exp(x) − 1‖ ≤ 2‖x‖` for `‖x‖ ≤ 1`.) -/
private theorem norm_exp_imI_sub (a b : ℝ) (h : |a - b| ≤ 1) :
    ‖Complex.exp (a * I) - Complex.exp (b * I)‖ ≤ 2 * |a - b| := by
  have factor : Complex.exp (a * I) - Complex.exp (b * I)
      = Complex.exp (b * I) * (Complex.exp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2 <;> push_cast <;> ring
  rw [factor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnorm : ‖((a - b : ℝ) : ℂ) * I‖ = |a - b| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hkey := norm_exp_sub_one_le (x := ((a - b : ℝ) : ℂ) * I) (by rw [hnorm]; exact h)
  rwa [hnorm] at hkey

/-- **Density of dyadic roots (step 4, PROVEN).** The `2ⁿ`-th roots of a unit-circle point `z₁` are
dense in the unit circle. For target `w = exp(α I)` and tolerance `ε`, pick `n` with `2π/2ⁿ < ε` and
`k = round((2ⁿα − arg z₁)/2π)`; then `exp(((arg z₁)+2πk)/2ⁿ · I)` is a `2ⁿ`-th root of `z₁` within
`2π/2ⁿ` of `w` (argument error `≤ π/2ⁿ`, exp Lipschitz). -/
theorem dense_dyadic_roots (z₁ : ℂ) (hz₁ : ‖z₁‖ = 1) :
    Metric.sphere (0 : ℂ) 1 ⊆ closure {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = z₁} := by
  intro w hw
  rw [mem_sphere_zero_iff_norm] at hw
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (max (2 * Real.pi / ε) (2 * Real.pi)) (by norm_num : (1:ℝ) < 2)
  have h2n_pos : (0:ℝ) < 2 ^ n := by positivity
  set θ₁ := z₁.arg
  set α := w.arg
  set t : ℝ := (2 ^ n * α - θ₁) / (2 * Real.pi) with ht
  set k : ℤ := round t with hk
  set β : ℝ := (θ₁ + 2 * Real.pi * k) / 2 ^ n with hβ
  have hz₁eq : Complex.exp ((θ₁:ℂ) * I) = z₁ := by
    simpa [hz₁] using norm_mul_exp_arg_mul_I z₁
  have hweq : w = Complex.exp ((α:ℂ) * I) := by
    have := norm_mul_exp_arg_mul_I w; rw [hw] at this; simpa using this.symm
  refine ⟨Complex.exp ((β:ℂ) * I), ?_, ?_⟩
  · refine ⟨n, ?_⟩
    rw [← Complex.exp_nat_mul]
    have hβ2 : (2 ^ n : ℕ) * ((β:ℂ) * I) = ((θ₁ : ℂ) + 2 * Real.pi * (k:ℂ)) * I := by
      push_cast [hβ]; field_simp
    rw [hβ2, show ((θ₁ : ℂ) + 2 * Real.pi * (k:ℂ)) * I = (θ₁:ℂ) * I + (k : ℂ) * (2 * Real.pi * I)
        by ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hz₁eq]
  · rw [dist_eq_norm, hweq]
    have habs : |α - β| ≤ Real.pi / 2 ^ n := by
      have hαβ : α - β = (2 * Real.pi / 2 ^ n) * (t - k) := by rw [hβ, ht]; field_simp; ring
      rw [hαβ, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / 2 ^ n)]
      calc 2 * Real.pi / 2 ^ n * |t - (k:ℝ)|
          ≤ 2 * Real.pi / 2 ^ n * (1/2) :=
            mul_le_mul_of_nonneg_left (by rw [hk]; exact abs_sub_round t) (by positivity)
        _ = Real.pi / 2 ^ n := by ring
    have hpi_le : Real.pi / 2 ^ n ≤ 1 := by
      rw [div_le_one h2n_pos]
      have h2 : 2 * Real.pi ≤ 2 ^ n := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
      linarith [Real.pi_pos]
    have hle1 : |α - β| ≤ 1 := le_trans habs hpi_le
    have hbound := norm_exp_imI_sub α β hle1
    have hπ : 2 * (Real.pi / 2 ^ n) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ h2n_pos]
      have h2πε : 2 * Real.pi / ε < 2 ^ n := lt_of_le_of_lt (le_max_left _ _) hn
      rw [div_lt_iff₀ hε, mul_comm] at h2πε
      linarith [h2πε]
    have hfin : 2 * |α - β| < ε := by
      calc 2 * |α - β| ≤ 2 * (Real.pi / 2 ^ n) := by linarith [habs]
        _ < ε := hπ
    linarith [hbound]

/-- **Natural boundary of u₀ — ASSEMBLED from the two leaf inputs (genuine form).**

`u₀` (analytic on the exterior `Ext`) continues across **no** point of the unit circle. This — not the
junk `¬AnalyticAt` form — is the real content equivalent to "u₀ transcendental over ℂ(z)".

**This theorem is fully proven modulo the two named leaf sorries** `seed_singularity` (step 2, the
genuine analytic core) and `dense_dyadic_roots` (step 4, elementary). The connective tissue —
propagation (`continues_sq`, step 3), the root induction, closedness (`isClosed_singular`, step 5),
and the closed-⊇-dense closure — is all proven here.

**Proof blueprint — softer than the generic Ostrowski–Hadamard gap theorem because it uses the Mahler
functional equation `(2/w)·U₀(w) = 1 + U₀(w²)` that this specific series satisfies:**

1. *Radius of convergence exactly 1.* `U0_summable_lt_one` + `U0term_norm_tendsto_atTop`. [PROVEN]
2. *Seed singularity.* `seed_singularity`. [leaf sorry — the genuine analytic core]
3. *Propagation.* `continues_sq` / `not_continues_of_sq`. [PROVEN]
4. *Density.* `dense_dyadic_roots`. [PROVEN]
5. *Close up.* `isClosed_singular` + `closure_minimal`. [PROVEN]

So on the analytic side the three-card independence result reduces to step 2 alone (step 4 being
routine). -/
theorem u0_natural_boundary :
    ∀ z₀ : ℂ, ‖z₀‖ = 1 → ¬ ContinuesAcross u0 Ext z₀ := by
  obtain ⟨z₁, hz₁norm, hz₁sing⟩ := seed_singularity
  -- every 2ⁿ-th root of the seed is singular (induction via `not_continues_of_sq`)
  have hroots : ∀ (n : ℕ) (z : ℂ), z ^ (2 ^ n) = z₁ → ¬ ContinuesAcross u0 Ext z := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [pow_zero, pow_one] at hz
      rw [hz]; exact hz₁sing
    | succ m ih =>
      intro z hz
      have hexp : 2 ^ (m + 1) ≠ 0 := by positivity
      have hznorm : ‖z‖ = 1 := by
        have h1 : ‖z‖ ^ (2 ^ (m + 1)) = 1 := by rw [← norm_pow, hz, hz₁norm]
        rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
        · exact absurd h1 (by have := pow_lt_one₀ (norm_nonneg z) hlt hexp; linarith)
        · exact heq
        · exact absurd h1 (by have := one_lt_pow₀ hgt hexp; linarith)
      have hz0 : z ≠ 0 := by intro h; rw [h] at hznorm; simp at hznorm
      apply not_continues_of_sq hz0
      apply ih (z ^ 2)
      rw [← pow_mul, show 2 * 2 ^ m = 2 ^ (m + 1) from by rw [pow_succ]; ring]
      exact hz
  have hRootsSub : {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = z₁} ⊆
      {z : ℂ | ¬ ContinuesAcross u0 Ext z} := by
    rintro z ⟨n, hn⟩; exact hroots n z hn
  -- the seed's roots are dense in the circle; the singular set is closed ⊇ them ⟹ ⊇ circle
  intro z₀ hz₀
  have hz₀sphere : z₀ ∈ Metric.sphere (0 : ℂ) 1 := by rwa [mem_sphere_zero_iff_norm]
  exact (closure_minimal hRootsSub isClosed_singular)
    (dense_dyadic_roots z₁ hz₁norm hz₀sphere)

/-- The companion series equals `u₀ ∘ (·⁻¹)` as tsums: `(w⁻¹)^{-(2^{n+1}-1)} = w^{2^{n+1}-1}`.
Pure algebra; underlies the `w ↦ 1/w` bridge between the u₀-side and U₀-side boundary statements. -/
theorem u0_inv_eq_companion (w : ℂ) :
    u0 w⁻¹ = ∑' n : ℕ, (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ) := by
  simp only [u0]; congr 1; ext n; congr 1
  rw [inv_zpow, zpow_neg, inv_inv]

end U0NaturalBoundary
