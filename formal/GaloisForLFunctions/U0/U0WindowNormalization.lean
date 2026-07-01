/-
# Window relations — general-degree normalization (separability removal)

Removes the `hleadw`/`hsepw` inputs from the circle-window theorems: an arbitrary function-level
nondegenerate relation is normalized to a separable one internally.  Plan (worklog 2026-07-01):
minimal function-level degree by `Nat.find`; gcd dichotomy in `K₀[Y]`, `K₀ := FractionRing` of the
function subring `R₀ = Φ(ℂ[z][W])`; Bézout certificates specialize pointwise (coprime case →
separability at a good point → the windowed engine); `IsLocalization.integerNormalization` clears
denominators (proper-gcd case → smaller relation → contradicts minimality).

This file builds the ring-theoretic layer:
* `analytic_domain_of_preconnected` — the domain property on any open preconnected set;
* `coeffFun`/`Φring` — the coefficient-function ring hom `ℂ[z][W] →+* (↥D → ℂ)` for a window
  function `φ`, and the `IsDomain` instance on its range.
-/
import GaloisForLFunctions.U0.U0PhiCircleWindow

open Complex Filter Topology Metric Set Polynomial
open U0 U0NaturalBoundary U0Transcendence U0PhiCard

namespace U0WindowNormalization

/-- **Analytic domain property on any open preconnected set** (generalizes
`U0Transcendence.analytic_domain` from `Ext`). -/
theorem analytic_domain_of_preconnected {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U)
    (hgh : ∀ z ∈ U, g z * h z = 0) :
    (∀ z ∈ U, g z = 0) ∨ (∀ z ∈ U, h z = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨z₁, hz₁E, hgz₁⟩, ⟨z₂, hz₂E, hhz₂⟩⟩ := hcon
  have hgne : ∀ᶠ z in 𝓝 z₁, g z ≠ 0 := (hg z₁ hz₁E).continuousAt.eventually_ne hgz₁
  have hU_nhds : U ∈ 𝓝 z₁ := hUo.mem_nhds hz₁E
  have hzero_near : ∀ᶠ z in 𝓝 z₁, h z = 0 := by
    filter_upwards [hgne, hU_nhds] with z hgz hzE
    rcases mul_eq_zero.mp (hgh z hzE) with h1 | h2
    · exact absurd h1 hgz
    · exact h2
  have hfreq : ∃ᶠ z in 𝓝[≠] z₁, h z = 0 :=
    (hzero_near.filter_mono nhdsWithin_le_nhds).frequently
  have hEqOn := hh.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₁E hfreq
  exact hhz₂ (hEqOn hz₂E)

variable {Ω : Set ℂ} {φ : ℂ → ℂ} {D : Set ℂ}

/-- The coefficient-function of an abstract polynomial `p ∈ ℂ[z][W]` along the window function
`φ`: `z ↦ p(z, φ z)`. -/
noncomputable def coeffFun (φ : ℂ → ℂ) (p : Polynomial (Polynomial ℂ)) : ℂ → ℂ :=
  fun z => p.eval₂ (evalRingHom z) (φ z)

theorem coeffFun_analytic (hφ : AnalyticOnNhd ℂ φ Ω) (p : Polynomial (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (coeffFun φ p) Ω :=
  eval_phi_analytic hφ p

/-- The coefficient-function ring hom into functions on `↥D`. -/
noncomputable def Φring (φ : ℂ → ℂ) (D : Set ℂ) :
    Polynomial (Polynomial ℂ) →+* (↥D → ℂ) :=
  Pi.ringHom fun z => (eval₂RingHom (evalRingHom (z : ℂ)) (φ (z : ℂ)))

@[simp] theorem Φring_apply (φ : ℂ → ℂ) (D : Set ℂ) (p : Polynomial (Polynomial ℂ)) (z : ↥D) :
    Φring φ D p z = coeffFun φ p (z : ℂ) := rfl

/-- The window coefficient ring `R₀ = Φ(ℂ[z][W]) ⊆ (↥D → ℂ)`. -/
noncomputable def R₀ (φ : ℂ → ℂ) (D : Set ℂ) : Subring (↥D → ℂ) :=
  (Φring φ D).range

/-- Vanishing transfer: an element of `R₀` that is zero as a subring element vanishes at every
point of `D`. -/
theorem R₀_zero_iff {φ : ℂ → ℂ} {D : Set ℂ} (a : R₀ φ D) :
    a = 0 ↔ ∀ z : ↥D, (a : ↥D → ℂ) z = 0 := by
  constructor
  · intro h z; rw [h]; rfl
  · intro h
    apply Subtype.ext
    funext z
    exact h z

/-- **`R₀` is an integral domain** when `D ⊆ Ω` is open, preconnected and nonempty: coefficient
functions extend analytically to `Ω`, and the domain property splits a vanishing product. -/
theorem R₀_noZeroDivisors (hφ : AnalyticOnNhd ℂ φ Ω) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDΩ : D ⊆ Ω) :
    ∀ a b : R₀ φ D, a * b = 0 → a = 0 ∨ b = 0 := by
  rintro ⟨a, pa, rfl⟩ ⟨b, pb, rfl⟩ hab
  have hfun : ∀ z ∈ D, coeffFun φ pa z * coeffFun φ pb z = 0 := by
    intro z hz
    have := congrArg (Subtype.val) hab
    have h2 := congrFun this ⟨z, hz⟩
    simpa using h2
  have hga : AnalyticOnNhd ℂ (coeffFun φ pa) D := (coeffFun_analytic hφ pa).mono hDΩ
  have hgb : AnalyticOnNhd ℂ (coeffFun φ pb) D := (coeffFun_analytic hφ pb).mono hDΩ
  rcases analytic_domain_of_preconnected hDo hDc hga hgb hfun with h | h
  · left
    apply Subtype.ext
    funext z
    exact h (z : ℂ) z.2
  · right
    apply Subtype.ext
    funext z
    exact h (z : ℂ) z.2

end U0WindowNormalization

/-!
## Remaining build plan (increments; see worklog 2026-07-01)

3a. `relation_propagates`: V-relation → D-relation (identity theorem, as in
    `u0_windowed_relation_false`).  `RelSet φ D d`: function-level degree-`d` relations with
    abstract coefficient witnesses and ≢0 leading function; membership from a nondegenerate `P`
    via max-support truncation (`Finset.sum_subset`).  Minimal `dmin ≥ 1` via `Nat.find`.
3b. `Q : Polynomial ↥(R₀ φ D)` from the minimal witness; `IsDomain ↥R₀` instance
    (`R₀_noZeroDivisors` + Nontrivial from `D.Nonempty`); `K₀ := FractionRing ↥R₀`;
    `q̄ := Q.map (algebraMap _ K₀)`; `(dmin : K₀) ≠ 0` manually (evaluate at a point).
3c. Dichotomy on `g := EuclideanDomain.gcd q̄ (derivative q̄)`:
    - `natDegree g = 0`: Bézout (`EuclideanDomain.gcd_eq_gcd_ab`), scale by `c⁻¹`, clear
      denominators (`IsLocalization.integerNormalization`), push through `Polynomial.map`
      injectivity to `U₁*Q + V₁*(derivative Q) = C s` in `↥R₀[Y]`, `s ≠ 0`.  Pick `w ∈ D` with
      `(s * leadingCoeff Q) w ≠ 0` (domain + `R₀_zero_iff`); specialize with
      `ev_w := (Pi.evalRingHom _ w).comp (R₀ φ D).subtype`; coprime specialization ⟹ Separable;
      feed `U0PhiCircleWindow.u0_windowed_relation_false` with `a i := coeffFun φ (b i)`,
      `V := D`.
    - `1 ≤ natDegree g ≤ dmin − 1` (`gcd_dvd_right` + `natDegree_le_of_dvd`): factor
      `g₁ * h₁ = C (b_g*b_h) * Q` in `↥R₀[Y]` (integerNormalization + map injectivity); apply
      `Polynomial.map ev_z` pointwise and evaluate at `u0 z`: product of two analytic functions
      ≡ 0 on D ⟹ `analytic_domain_of_preconnected` ⟹ a `RelSet` member of degree in
      `[1, dmin−1]` (abstract lifts of `g₁`/`h₁` coefficients by range choice) — contradicts
      minimality.
4.  Wrappers: `u0_windowed_no_relation_nondegenerate` (general `Ω, φ`) and the `phiFour`
    instance without separability inputs; register in `FullyProvenNewTargets`.
-/

namespace U0WindowNormalization

variable {Ω : Set ℂ} {φ : ℂ → ℂ}

/-- **Relation propagation V → D** (identity theorem on the preconnected window piece). -/
theorem relation_propagates (hDc : IsPreconnected (Ω ∩ Ext))
    (hφ : AnalyticOnNhd ℂ φ Ω) (P : (Polynomial (Polynomial ℂ))[X])
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty) (hVD : V ⊆ Ω ∩ Ext)
    (hrel : ∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (φ z)) (u0 z) = 0) :
    ∀ z ∈ Ω ∩ Ext, ∑ k ∈ Finset.range (P.natDegree + 1),
      coeffFun φ (P.coeff k) z * u0 z ^ k = 0 := by
  set G : ℂ → ℂ := fun z => ∑ k ∈ Finset.range (P.natDegree + 1),
    coeffFun φ (P.coeff k) z * u0 z ^ k with hG
  have hGan : AnalyticOnNhd ℂ G (Ω ∩ Ext) := by
    intro z hz
    have h1 : AnalyticAt ℂ (∑ k ∈ Finset.range (P.natDegree + 1),
        fun z => coeffFun φ (P.coeff k) z * u0 z ^ k) z :=
      Finset.analyticAt_sum _ (fun k _ =>
        ((coeffFun_analytic hφ (P.coeff k)) z hz.1).mul ((u0_analyticOnNhd_Ext z hz.2).pow _))
    have h2 : (∑ k ∈ Finset.range (P.natDegree + 1),
        fun z => coeffFun φ (P.coeff k) z * u0 z ^ k) = G := by
      funext y; rw [hG]; simp
    rwa [h2] at h1
  have hGV : ∀ z ∈ V, G z = 0 := by
    intro z hz
    have h0 := hrel z hz
    rw [eval₂_eq_sum_range] at h0
    rw [hG]
    simpa [coeffFun] using h0
  obtain ⟨v₀, hv₀⟩ := hVne
  have hev : G =ᶠ[nhds v₀] 0 :=
    Filter.eventuallyEq_of_mem (hVo.mem_nhds hv₀) (fun z hz => hGV z hz)
  have hzero : Set.EqOn G 0 (Ω ∩ Ext) :=
    hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hVD hv₀) hev
  intro z hz
  simpa [hG] using hzero hz

/-- **Function-level relation set**: degree-`d` relations between `u₀` and the window function,
with abstract polynomial coefficient witnesses and a leading coefficient function not identically
zero on `D`. -/
def RelSet (φ : ℂ → ℂ) (D : Set ℂ) (d : ℕ) : Prop :=
  ∃ b : Fin (d + 1) → Polynomial (Polynomial ℂ),
    (∃ z ∈ D, coeffFun φ (b (Fin.last d)) z ≠ 0) ∧
    ∀ z ∈ D, ∑ i : Fin (d + 1), coeffFun φ (b i) z * u0 z ^ (i : ℕ) = 0

/-- **A nondegenerate relation yields a `RelSet` member of positive degree** (max-support
truncation). -/
theorem relSet_of_nondegenerate {D : Set ℂ}
    (P : (Polynomial (Polynomial ℂ))[X]) {i₀ : ℕ} (hi₀ : 1 ≤ i₀)
    (hnondeg : ∃ z ∈ D, coeffFun φ (P.coeff i₀) z ≠ 0)
    (hrelD : ∀ z ∈ D, ∑ k ∈ Finset.range (P.natDegree + 1),
      coeffFun φ (P.coeff k) z * u0 z ^ k = 0) :
    ∃ d, 1 ≤ d ∧ RelSet φ D d := by
  classical
  set n := P.natDegree with hn
  set Pk : ℕ → Prop := fun k => ∃ z ∈ D, coeffFun φ (P.coeff k) z ≠ 0 with hPk
  have hi₀n : i₀ ≤ n := by
    by_contra hgt
    push Not at hgt
    have hzero : P.coeff i₀ = 0 := coeff_eq_zero_of_natDegree_lt hgt
    obtain ⟨z, _, hz⟩ := hnondeg
    apply hz
    rw [hzero]
    simp [coeffFun]
  set d := Nat.findGreatest Pk n with hd
  have hdi₀ : i₀ ≤ d := Nat.le_findGreatest hi₀n hnondeg
  have hd1 : 1 ≤ d := le_trans hi₀ hdi₀
  have hdn : d ≤ n := Nat.findGreatest_le n
  have hPd : Pk d := Nat.findGreatest_spec (m := i₀) hi₀n hnondeg
  have hvanish : ∀ k, d < k → k ≤ n → ∀ z ∈ D, coeffFun φ (P.coeff k) z = 0 := by
    intro k hk hkn z hz
    by_contra hne
    exact Nat.findGreatest_is_greatest hk hkn ⟨z, hz, hne⟩
  refine ⟨d, hd1, fun i => P.coeff (i : ℕ), ?_, ?_⟩
  · simpa [Fin.val_last] using hPd
  · intro z hz
    have hconv : (∑ i : Fin (d + 1), coeffFun φ (P.coeff (i : ℕ)) z * u0 z ^ (i : ℕ))
        = ∑ k ∈ Finset.range (d + 1), coeffFun φ (P.coeff k) z * u0 z ^ k :=
      Fin.sum_univ_eq_sum_range (fun k => coeffFun φ (P.coeff k) z * u0 z ^ k) (d + 1)
    rw [hconv]
    rw [Finset.sum_subset (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hdn))) ?_]
    · exact hrelD z hz
    · intro k hk hknot
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkd : d + 1 ≤ k := by
        by_contra hlt
        push Not at hlt
        exact hknot (Finset.mem_range.mpr hlt)
      rw [hvanish k (Nat.lt_of_succ_le hkd) (Nat.lt_succ_iff.mp hklt) z hz, zero_mul]

end U0WindowNormalization

namespace U0WindowNormalization

/-- Coefficient of a `Fin`-indexed coefficient sum, in range. -/
theorem finSum_coeff {R : Type*} [CommRing R] {d : ℕ} (r : Fin (d + 1) → R) (k : ℕ) (hk : k ≤ d) :
    (∑ i : Fin (d + 1), C (r i) * X ^ (i : ℕ)).coeff k = r ⟨k, Nat.lt_succ_of_le hk⟩ := by
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (d + 1))]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hi
    rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
    intro h
    exact hi (Fin.ext (by simpa using h.symm))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Coefficient of a `Fin`-indexed coefficient sum, above range. -/
theorem finSum_coeff_gt {R : Type*} [CommRing R] {d : ℕ} (r : Fin (d + 1) → R) (k : ℕ)
    (hk : d < k) :
    (∑ i : Fin (d + 1), C (r i) * X ^ (i : ℕ)).coeff k = 0 := by
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
  intro h
  have := i.isLt
  omega

/-- Mapping a `Fin`-indexed coefficient sum through a ring hom. -/
theorem map_finSum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (r : Fin (d + 1) → R) :
    (∑ i : Fin (d + 1), C (r i) * X ^ (i : ℕ)).map f
      = ∑ i : Fin (d + 1), C (f (r i)) * X ^ (i : ℕ) := by
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

/-- Evaluating a `Fin`-indexed coefficient sum. -/
theorem eval_finSum {S : Type*} [CommRing S] {d : ℕ} (c : Fin (d + 1) → S) (x : S) :
    (∑ i : Fin (d + 1), C (c i) * X ^ (i : ℕ)).eval x
      = ∑ i : Fin (d + 1), c i * x ^ (i : ℕ) := by
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

end U0WindowNormalization
