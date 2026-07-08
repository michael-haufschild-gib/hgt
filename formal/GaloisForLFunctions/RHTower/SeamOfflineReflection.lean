/-
The holomorphic-symmetry ramification engine, and the wall it meets at the off-line quadrant.

The functional equation forces even vanishing order at its fixed point `1/2`
(`analyticOrderAt_even_of_reflection`, the affine reflection `s ↦ 2c − s`).  This module lifts
that mechanism from affine reflections to **any analytic self-symmetry**, and records exactly why
it cannot be aimed off the critical line without new input.

* **The engine.**  If `f ∘ τ = f` near a fixed point `c = τ c` of an analytic map `τ`, then the
  multiplier `λ = τ'(c)` satisfies `λ ^ ord_c f = 1` (`multiplier_pow_analyticOrderAt_eq_one`).
  Reading `λ` as a root of unity: `λ = −1` forces `ord_c f` even
  (`even_analyticOrderAt_of_symmetry_neg_one`); a primitive `n`-th root forces `n ∣ ord_c f`
  (`dvd_analyticOrderAt_of_symmetry_primitiveRoot`) — the full `RHLadder`-rung divisibility from a
  single symmetry.  This is the local model the parity program needs: "reflection across a
  biholomorphic preimage of a line" is exactly an analytic `τ` with `τ'(c) = −1`, no longer
  required to be the global affine `s ↦ 1 − s`.  The proof is derivative-limit + order-peel; no
  argument principle.

* **The wall.**  Two symmetry centers generate a translation
  (`two_center_symmetry_periodic`): an entire reflection whose center `b/2` is *off* `1/2` would
  make `f` periodic with the nonzero period `1 − b`.  For `f = xi` this is the whole obstruction —
  the completed zeta is not periodic, so its only entire reflection symmetry is the functional
  equation, fixed at `1/2` on the critical line.  Off-line, the engine has nothing entire to run
  on.

* **What is left open, precisely.**  A symmetry family that *is* functorial under the
  FE `s ↦ 1 − s` and Schwarz conjugation `s ↦ s̄` produces, by
  `QuadrantRamifiedCover.quadrant_ram_forced_equal`, one order value on the whole
  `V₄`-orbit `{ρ, 1−ρ, ρ̄, 1−ρ̄}`, hence a charge divisible by `4`, blind at rungs `k ≤ 2`
  (`quadrant_ram_charge_blind`).  So an off-line detector must run the engine on a `τ` that is
  **not** `FE`/conjugation-functorial — a correspondence living on a cover and consuming the Euler
  structure (the only constraint that separates `xi` from the Davenport–Heilbronn and Révész
  functions, which share `xi`'s reflection type yet carry simple off-line zeros).  The engine is
  built and waiting; the cover is the open object.
-/
import GaloisForLFunctions.RHTower.ReflectionParity
import GaloisForLFunctions.RHTower.QuadrantRamifiedCover

open Complex Filter Topology

namespace RHTower

/-! ### §1 The engine: an analytic symmetry constrains the multiplier by the vanishing order -/

/-- **The multiplier law.**  If an analytic map `τ` fixes `c` and `f ∘ τ = f` on a neighbourhood
of `c`, then the multiplier `τ'(c)` is a `(ord_c f)`-th root of unity: `(τ'(c)) ^ ord_c f = 1`.

Mechanism: peel `f = (·−c)^m · h` with `h c ≠ 0`; then near `c`, `f(τ s) = f s` reads
`h s = (slope τ c s)^m · h(τ s)`, and the difference quotient `slope τ c s → τ'(c)` as `s → c`, so
`h c = (τ'(c))^m · h c`, whence `(τ'(c))^m = 1`.  No argument principle; the affine reflection
lemma is the special case `τ s = 2c − s`, `τ'(c) = −1`. -/
theorem multiplier_pow_analyticOrderAt_eq_one {f τ : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hsym : ∀ᶠ s in 𝓝 c, f (τ s) = f s) (hne : analyticOrderAt f c ≠ ⊤) :
    (deriv τ c) ^ (analyticOrderAt f c).toNat = 1 := by
  set m : ℕ := (analyticOrderAt f c).toNat with hm_def
  have hcoe : analyticOrderAt f c = (m : ℕ∞) := (ENat.coe_toNat hne).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ := exists_peel isOpen_univ hf (Set.mem_univ c) hcoe
  set lam : ℂ := deriv τ c with hlam
  have hderiv : HasDerivAt τ lam c := hτ.differentiableAt.hasDerivAt
  have hslope : Tendsto (slope τ c) (𝓝[≠] c) (𝓝 lam) := hasDerivAt_iff_tendsto_slope.mp hderiv
  have key : ∀ᶠ s in 𝓝[≠] c, h s = (slope τ c s) ^ m * h (τ s) := by
    have hsym' : ∀ᶠ s in 𝓝[≠] c, f (τ s) = f s := hsym.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsym'] with s hs hsyms
    have hsc : s - c ≠ 0 := sub_ne_zero.mpr hs
    have hsl : slope τ c s * (s - c) = τ s - c := by
      rw [slope_def_field, hfix, div_mul_cancel₀ _ hsc]
    have e1 : f s = (s - c) ^ m * h s := hfact s (Set.mem_univ s)
    have e2 : f (τ s) = (τ s - c) ^ m * h (τ s) := hfact (τ s) (Set.mem_univ _)
    have hpow : ((s - c : ℂ)) ^ m ≠ 0 := pow_ne_zero m hsc
    have hcancel : (s - c) ^ m * ((slope τ c s) ^ m * h (τ s)) = (s - c) ^ m * h s := by
      have hchain : (slope τ c s) ^ m * (s - c) ^ m * h (τ s) = (s - c) ^ m * h s := by
        calc (slope τ c s) ^ m * (s - c) ^ m * h (τ s)
            = (τ s - c) ^ m * h (τ s) := by rw [← mul_pow, hsl]
          _ = f (τ s) := e2.symm
          _ = f s := hsyms
          _ = (s - c) ^ m * h s := e1
      rw [← hchain]; ring
    exact (mul_left_cancel₀ hpow hcancel).symm
  have hlim_lhs : Tendsto h (𝓝[≠] c) (𝓝 (h c)) :=
    ((hhan c (Set.mem_univ c)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have htau : Tendsto τ (𝓝[≠] c) (𝓝 c) := by
    have h0 := hτ.continuousAt.tendsto
    rw [hfix] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hhtau : Tendsto (fun s => h (τ s)) (𝓝[≠] c) (𝓝 (h c)) :=
    ((hhan c (Set.mem_univ c)).continuousAt.tendsto).comp htau
  have hrhs : Tendsto (fun s => (slope τ c s) ^ m * h (τ s)) (𝓝[≠] c) (𝓝 (lam ^ m * h c)) :=
    (hslope.pow m).mul hhtau
  have huniq : h c = lam ^ m * h c := tendsto_nhds_unique (hlim_lhs.congr' key) hrhs
  have : lam ^ m * h c = 1 * h c := by rw [one_mul]; exact huniq.symm
  exact mul_right_cancel₀ hh0 this

/-- **A `−1` multiplier forces even order.**  If `f ∘ τ = f` near a fixed point `c` of `τ` with
`τ'(c) = −1`, the vanishing order of `f` at `c` is even.  Generalizes
`analyticOrderAt_even_of_reflection` from the affine reflection `2c − s` to any analytic `τ`. -/
theorem even_analyticOrderAt_of_symmetry_neg_one {f τ : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hderiv : deriv τ c = -1)
    (hsym : ∀ᶠ s in 𝓝 c, f (τ s) = f s) (hne : analyticOrderAt f c ≠ ⊤) :
    Even (analyticOrderAt f c).toNat := by
  have h1 : (deriv τ c) ^ (analyticOrderAt f c).toNat = 1 :=
    multiplier_pow_analyticOrderAt_eq_one hf hτ hfix hsym hne
  rw [hderiv] at h1
  rcases Nat.even_or_odd (analyticOrderAt f c).toNat with he | ho
  · exact he
  · exfalso; rw [ho.neg_one_pow] at h1; norm_num at h1

/-- **A primitive `n`-th root multiplier forces `n ∣ order`.**  If `f ∘ τ = f` near a fixed point
`c` and the multiplier `τ'(c)` is a primitive `n`-th root of unity, then `n ∣ ord_c f` — a single
analytic symmetry forces the whole `RHLadder`-style divisibility clause at `c`.  (`n = 2` recovers
even order; `n = 2^k` is the rung-`k` clause.) -/
theorem dvd_analyticOrderAt_of_symmetry_primitiveRoot {f τ : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hroot : IsPrimitiveRoot (deriv τ c) n)
    (hsym : ∀ᶠ s in 𝓝 c, f (τ s) = f s) (hne : analyticOrderAt f c ≠ ⊤) :
    n ∣ (analyticOrderAt f c).toNat := by
  have h1 : (deriv τ c) ^ (analyticOrderAt f c).toNat = 1 :=
    multiplier_pow_analyticOrderAt_eq_one hf hτ hfix hsym hne
  exact (hroot.pow_eq_one_iff_dvd _).mp h1

/-- **A `−1`-symmetry at a zero forces non-simplicity.**  If `f(c) = 0` and `f` has a `−1`-multiplier
analytic symmetry fixing `c`, then the vanishing order at `c` is at least `2`: the zero is not
simple.  Contrapositive: a *simple* zero admits no analytic self-symmetry with multiplier `−1`.  This
is the exact tension the parity program lives on — an off-line detector would force the (conjecturally
simple) off-line zeros to be double. -/
theorem order_ge_two_of_zero_symmetry_neg_one {f τ : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hderiv : deriv τ c = -1) (hsym : ∀ᶠ s in 𝓝 c, f (τ s) = f s)
    (hne : analyticOrderAt f c ≠ ⊤) (hzero : f c = 0) :
    2 ≤ (analyticOrderAt f c).toNat := by
  have heven := even_analyticOrderAt_of_symmetry_neg_one hf hτ hfix hderiv hsym hne
  have hord_ne : analyticOrderAt f c ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hf c (Set.mem_univ c), hzero⟩
  have hpos : (analyticOrderAt f c).toNat ≠ 0 := by
    intro h0
    apply hord_ne
    have hc := ENat.coe_toNat hne
    rw [h0] at hc; simpa using hc.symm
  rcases heven with ⟨k, hk⟩
  omega

/-! ### §2 The ξ engine and the recovered base case -/

/-- **The general ξ parity engine.**  Any analytic symmetry `τ` of the completed zeta fixing `ρ`
with multiplier `−1` forces even vanishing order at `ρ` — for `ρ` anywhere, on or off the line.
The functional equation `s ↦ 1 − s` (fixed point `1/2`, derivative `−1`) is the special case that
recovers `xi_central_order_even`; the content of the parity program is to find such a `τ` with an
*off-line* fixed point. -/
theorem xi_even_order_of_analytic_symmetry {τ : ℂ → ℂ} {ρ : ℂ}
    (hτ : AnalyticAt ℂ τ ρ) (hfix : τ ρ = ρ) (hderiv : deriv τ ρ = -1)
    (hsym : ∀ᶠ s in 𝓝 ρ, xi (τ s) = xi s) :
    Even (analyticOrderAt xi ρ).toNat :=
  even_analyticOrderAt_of_symmetry_neg_one xi_analyticOnNhd_univ hτ hfix hderiv hsym
    (xi_orderAt_ne_top ρ)

/-- The functional equation is the `c = 1/2` instance of the engine: its multiplier is `−1`, so it
recovers even central order.  Confirms the general engine subsumes the affine reflection lemma. -/
theorem xi_central_order_even_via_engine : Even (analyticOrderAt xi (1 / 2 : ℂ)).toNat := by
  refine xi_even_order_of_analytic_symmetry (τ := fun s => 1 - s) ?_ ?_ ?_ ?_
  · exact (analyticAt_const.sub analyticAt_id)
  · norm_num
  · rw [deriv_const_sub]; simp
  · filter_upwards with s using xi_one_sub s

/-! ### §3 The wall: two centers force periodicity, and ξ has only the FE center -/

/-- **Two symmetry centers generate a translation.**  If `f` is symmetric under both the reflection
`s ↦ b − s` and the functional-equation reflection `s ↦ 1 − s`, then `f` is periodic with period
`1 − b`.  An entire reflection whose center `b/2` differs from `1/2` therefore forces a *nonzero*
period; the completed zeta admits no such period, so its only entire reflection symmetry is the
functional equation, fixed on the critical line at `1/2`.  Off-line entire reflections do not
exist — the engine of §1 must be run on a non-entire (cover) symmetry to reach the open region. -/
theorem two_center_symmetry_periodic {f : ℂ → ℂ} {b : ℂ}
    (hb : ∀ s, f (b - s) = f s) (hFE : ∀ s, f (1 - s) = f s) (s : ℂ) :
    f (s + (1 - b)) = f s := by
  have h1 : f (1 - (b - s)) = f (b - s) := hFE (b - s)
  rw [hb s] at h1
  have h2 : (1 - (b - s) : ℂ) = s + (1 - b) := by ring
  rw [h2] at h1
  exact h1

/-- **The only entire reflection symmetry of ξ is the functional equation.**  Given that the
completed zeta has no nonzero period (`hap` — the standard fact that `xi` is not periodic, its
super-exponential real-axis growth exceeding any exponential type), any entire reflection
`s ↦ b − s` under which `xi` is invariant has `b = 1`: it is the functional equation `s ↦ 1 − s`,
whose fixed point `b/2 = 1/2` lies on the critical line.  Hence the reflection engine of §1, run on
`xi`'s own entire symmetries, reaches only `1/2` — off-line it has no entire `τ` to run on, and a
detector must descend to a cover (the open object). -/
theorem xi_entire_reflection_center_eq_half {b : ℂ}
    (hap : ∀ ω : ℂ, ω ≠ 0 → ¬ (∀ s, xi (s + ω) = xi s))
    (hb : ∀ s, xi (b - s) = xi s) : b = 1 := by
  by_contra hb1
  have hper : ∀ s, xi (s + (1 - b)) = xi s :=
    fun s => two_center_symmetry_periodic hb xi_one_sub s
  have hω : (1 - b : ℂ) ≠ 0 := fun h => hb1 (by rw [sub_eq_zero] at h; exact h.symm)
  exact hap (1 - b) hω hper

end RHTower
