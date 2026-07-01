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

namespace U0WindowNormalization

set_option maxHeartbeats 1000000 in
/-- **No function-level relation of any positive degree** (separability-free master).  If the
window data is in place (`Ω` open preconnected touching the circle at `z₁`, `Ω ∩ Ext`
preconnected, `φ` analytic on `Ω`), then `RelSet φ (Ω ∩ Ext) d` is impossible for every `d ≥ 1`:
a minimal-degree member is normalized internally — Bézout certificate when the fraction-field gcd
is trivial (specializing to a separable instance for the windowed engine), gcd factorization plus
the analytic domain property otherwise (contradicting minimality). -/
theorem relSet_false {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hDc : IsPreconnected (Ω ∩ Ext))
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Ω)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) (hz₁norm : ‖z₁‖ = 1)
    (hex : ∃ d, 1 ≤ d ∧ RelSet φ (Ω ∩ Ext) d) : False := by
  classical
  set D : Set ℂ := Ω ∩ Ext with hD
  have hDo : IsOpen D := hΩo.inter isOpen_Ext
  have hDΩ : D ⊆ Ω := Set.inter_subset_left
  -- D is nonempty: points just outside the circle near z₁
  have hDne : D.Nonempty := by
    obtain ⟨ρ, hρpos, hballΩ⟩ := Metric.isOpen_iff.mp hΩo z₁ hz₁
    set ρ' : ℝ := min ρ 1 with hρ'
    have hρ'pos : 0 < ρ' := lt_min hρpos one_pos
    refine ⟨((1 : ℝ) + ρ' / 2) • z₁, hballΩ ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm,
        show ((1 : ℝ) + ρ' / 2) • z₁ - z₁ = (ρ' / 2) • z₁ by module,
        norm_smul, Real.norm_eq_abs, hz₁norm, mul_one, abs_of_pos (by linarith)]
      have : ρ' ≤ ρ := min_le_left _ _
      linarith
    · show (1 : ℝ) < ‖((1 : ℝ) + ρ' / 2) • z₁‖
      rw [norm_smul, Real.norm_eq_abs, hz₁norm, mul_one, abs_of_pos (by linarith)]
      linarith
  -- minimal degree
  set PP : ℕ → Prop := fun n => 1 ≤ n ∧ RelSet φ D n with hPP
  have hPPex : ∃ n, PP n := hex
  have hspec := Nat.find_spec hPPex
  have hmin : ∀ e, PP e → Nat.find hPPex ≤ e := fun e he => Nat.find_le he
  revert hspec hmin
  generalize Nat.find hPPex = dmin
  intro hspec hmin
  obtain ⟨hdmin1, bmin, hbl, hbrel⟩ := hspec
  -- the coefficient ring and its fraction field
  haveI hNT : Nontrivial ↥(R₀ φ D) := by
    refine ⟨1, 0, fun h => ?_⟩
    obtain ⟨z₀, hz₀⟩ := hDne
    have := congrFun (congrArg Subtype.val h) ⟨z₀, hz₀⟩
    simpa using this
  haveI : NoZeroDivisors ↥(R₀ φ D) :=
    ⟨fun {a b} hab => R₀_noZeroDivisors hφ hDo hDc hDΩ a b hab⟩
  haveI : IsDomain ↥(R₀ φ D) := NoZeroDivisors.to_isDomain _
  set K : Type := FractionRing ↥(R₀ φ D) with hK
  set alg : ↥(R₀ φ D) →+* K := algebraMap ↥(R₀ φ D) K with halg
  have halg_inj : Function.Injective alg := IsFractionRing.injective ↥(R₀ φ D) K
  have hmap_inj : Function.Injective (Polynomial.map alg) := Polynomial.map_injective alg halg_inj
  -- the coefficient elements and the polynomial Q
  set r : Fin (dmin + 1) → ↥(R₀ φ D) :=
    fun i => ⟨Φring φ D (bmin i), RingHom.mem_range_self _ _⟩ with hr
  set Q : Polynomial ↥(R₀ φ D) := ∑ i : Fin (dmin + 1), C (r i) * X ^ (i : ℕ) with hQ
  have hrlast_ne : r (Fin.last dmin) ≠ 0 := by
    intro h
    obtain ⟨z, hz, hne⟩ := hbl
    apply hne
    have := (R₀_zero_iff (r (Fin.last dmin))).mp h ⟨z, hz⟩
    simpa [hr] using this
  have hQcoeff : ∀ k (hk : k ≤ dmin), Q.coeff k = r ⟨k, Nat.lt_succ_of_le hk⟩ :=
    fun k hk => finSum_coeff r k hk
  have hQcoeff_top : Q.coeff dmin = r (Fin.last dmin) := by
    rw [hQcoeff dmin le_rfl]; rfl
  have hQdeg : Q.natDegree = dmin := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hQcoeff_top]; exact hrlast_ne))
    refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    exact finSum_coeff_gt r m hm
  have hQne : Q ≠ 0 := fun h => hrlast_ne (by rw [← hQcoeff_top, h, coeff_zero])
  -- push to the fraction field
  set qb : K[X] := Q.map alg with hqb
  have hqbne : qb ≠ 0 := fun h => hQne (hmap_inj (by simpa [hqb] using h))
  have hqbdeg : qb.natDegree = dmin := by
    rw [hqb, natDegree_map_eq_of_injective halg_inj, hQdeg]
  set qb' : K[X] := derivative qb with hqb'
  have hdmin_ne : (dmin : ↥(R₀ φ D)) ≠ 0 := by
    intro h
    obtain ⟨z₀, hz₀⟩ := hDne
    have := (R₀_zero_iff _).mp h ⟨z₀, hz₀⟩
    have hcast : ((dmin : ↥(R₀ φ D)) : ↥D → ℂ) ⟨z₀, hz₀⟩ = (dmin : ℂ) := by
      simp
    rw [hcast] at this
    exact Nat.cast_ne_zero.mpr (by omega) this
  have hqb'_coeff : qb'.coeff (dmin - 1) = alg (r (Fin.last dmin)) * (dmin : K) := by
    rw [hqb', coeff_derivative]
    have h1 : dmin - 1 + 1 = dmin := by omega
    rw [h1, hqb, coeff_map, hQcoeff_top]
    have h2 : ((dmin - 1 : ℕ) : K) + 1 = ((dmin : ℕ) : K) := by
      rw [← Nat.cast_succ]
      congr 1
      omega
    rw [h2]
  have hqb'ne : qb' ≠ 0 := by
    intro h
    have := hqb'_coeff
    rw [h, coeff_zero] at this
    have hK1 : alg (r (Fin.last dmin)) ≠ 0 := fun hh => hrlast_ne (halg_inj (by simpa using hh))
    have hK2 : (dmin : K) ≠ 0 := by
      intro hh
      apply hdmin_ne
      apply halg_inj
      rw [map_natCast, hh, map_zero]
    exact (mul_ne_zero hK1 hK2) this.symm
  have hqb'deg : qb'.natDegree = dmin - 1 := by
    refine le_antisymm (le_trans (natDegree_derivative_le qb) (by rw [hqbdeg])) ?_
    refine le_natDegree_of_ne_zero ?_
    rw [hqb'_coeff]
    refine mul_ne_zero (fun hh => hrlast_ne (halg_inj (by simpa using hh))) ?_
    intro hh
    apply hdmin_ne
    apply halg_inj
    rw [map_natCast, hh, map_zero]
  -- the gcd dichotomy
  set g : K[X] := EuclideanDomain.gcd qb qb' with hg
  have hgne : g ≠ 0 := by
    intro h
    exact hqbne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgdeg_le : g.natDegree ≤ dmin - 1 := by
    calc g.natDegree ≤ qb'.natDegree :=
      natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right qb qb') hqb'ne
    _ = dmin - 1 := hqb'deg
  by_cases hg0 : g.natDegree = 0
  · -- CASE A: coprime — Bézout, clear denominators, specialize, feed the engine
    obtain ⟨c, hgC⟩ := natDegree_eq_zero.mp hg0
    have hcne : c ≠ 0 := fun h => hgne (by rw [← hgC, h, map_zero])
    have hBez : C c = qb * EuclideanDomain.gcdA qb qb' + qb' * EuclideanDomain.gcdB qb qb' := by
      rw [hgC]; exact EuclideanDomain.gcd_eq_gcd_ab qb qb'
    set A : K[X] := EuclideanDomain.gcdA qb qb' with hA
    set B : K[X] := EuclideanDomain.gcdB qb qb' with hB
    obtain ⟨sA, hsAmem, hA₁⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(R₀ φ D)) A
    obtain ⟨sB, hsBmem, hB₁⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(R₀ φ D)) B
    set A₁ := IsLocalization.integerNormalization (nonZeroDivisors ↥(R₀ φ D)) A with hA₁d
    set B₁ := IsLocalization.integerNormalization (nonZeroDivisors ↥(R₀ φ D)) B with hB₁d
    have hA₁' : A₁.map alg = C (alg sA) * A := by
      rw [hA₁d, hA₁, ← algebraMap_smul K sA A, smul_eq_C_mul]
    have hB₁' : B₁.map alg = C (alg sB) * B := by
      rw [hB₁d, hB₁, ← algebraMap_smul K sB B, smul_eq_C_mul]
    obtain ⟨⟨cn, cd⟩, hcmk⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ↥(R₀ φ D)) c
    have hcd : c * alg (cd : ↥(R₀ φ D)) = alg cn := by
      rw [← hcmk]
      exact IsLocalization.mk'_spec K cn cd
    have hsAne : sA ≠ 0 := nonZeroDivisors.ne_zero hsAmem
    have hsBne : sB ≠ 0 := nonZeroDivisors.ne_zero hsBmem
    have hcdne : (cd : ↥(R₀ φ D)) ≠ 0 := nonZeroDivisors.ne_zero cd.2
    have hcnne : cn ≠ 0 := by
      intro h
      rw [h, map_zero] at hcd
      exact (mul_ne_zero hcne (fun hh => hcdne (halg_inj (by simpa using hh)))) hcd
    set s : ↥(R₀ φ D) := sA * sB * cn with hs
    have hsne : s ≠ 0 := mul_ne_zero (mul_ne_zero hsAne hsBne) hcnne
    -- the cleared Bézout identity over R₀
    have hderiv_map : (derivative Q).map alg = qb' := by
      rw [hqb', hqb, derivative_map]
    have hkey : (C ((cd : ↥(R₀ φ D)) * sB) * A₁) * Q
        + (C ((cd : ↥(R₀ φ D)) * sA) * B₁) * derivative Q = C s := by
      apply hmap_inj
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_C, hA₁', hB₁', ← hqb, hderiv_map]
      simp only [map_mul]
      have hcdC : C c * C (alg (cd : ↥(R₀ φ D))) = C (alg cn) := by
        rw [← map_mul C, hcd]
      linear_combination (-(C (alg (cd : ↥(R₀ φ D))) * C (alg sA) * C (alg sB))) * hBez
        + (C (alg sA) * C (alg sB)) * hcdC
    -- pick a good specialization point
    have hprod_ne : s * r (Fin.last dmin) ≠ 0 := mul_ne_zero hsne hrlast_ne
    have hgood : ∃ w : ↥D, (s : ↥D → ℂ) w * ((r (Fin.last dmin) : ↥D → ℂ)) w ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hprod_ne
      exact (R₀_zero_iff _).mpr fun w => by
        have := hall w
        simpa using this
    obtain ⟨w, hw_ne⟩ := hgood
    have hsw : (s : ↥D → ℂ) w ≠ 0 := fun h => hw_ne (by rw [h, zero_mul])
    have hlw : ((r (Fin.last dmin) : ↥D → ℂ)) w ≠ 0 := fun h => hw_ne (by rw [h, mul_zero])
    set ev : ↥(R₀ φ D) →+* ℂ := (Pi.evalRingHom (fun _ : ↥D => ℂ) w).comp (R₀ φ D).subtype
      with hev
    -- specialize the Bézout identity
    have hkeyw := congrArg (Polynomial.map ev) hkey
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hkeyw
    have hsep : (Q.map ev).Separable := by
      unfold Polynomial.Separable
      refine ⟨C ((ev s)⁻¹) * ((C ((cd : ↥(R₀ φ D)) * sB) * A₁).map ev),
        C ((ev s)⁻¹) * ((C ((cd : ↥(R₀ φ D)) * sA) * B₁).map ev), ?_⟩
      have hevs : ev s ≠ 0 := hsw
      have hder : (derivative Q).map ev = derivative (Q.map ev) := by
        rw [derivative_map]
      rw [← hder]
      calc C (ev s)⁻¹ * ((C ((cd : ↥(R₀ φ D)) * sB) * A₁).map ev) * (Q.map ev)
            + C (ev s)⁻¹ * ((C ((cd : ↥(R₀ φ D)) * sA) * B₁).map ev) * ((derivative Q).map ev)
          = C (ev s)⁻¹ * (((C ((cd : ↥(R₀ φ D)) * sB) * A₁).map ev) * (Q.map ev)
            + ((C ((cd : ↥(R₀ φ D)) * sA) * B₁).map ev) * ((derivative Q).map ev)) := by ring
        _ = C (ev s)⁻¹ * C (ev s) := by rw [hkeyw]
        _ = 1 := by rw [← map_mul C, inv_mul_cancel₀ hevs, map_one]
    -- feed the windowed engine
    have hQmap : Q.map ev = ∑ i : Fin (dmin + 1), C (coeffFun φ (bmin i) (w : ℂ)) * X ^ (i : ℕ) := by
      rw [hQ, map_finSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    refine U0PhiCircleWindow.u0_windowed_relation_false hΩo hΩc hDc hdmin1
      (fun i => coeffFun φ (bmin i)) (fun i => coeffFun_analytic hφ (bmin i))
      (w := (w : ℂ)) (hDΩ w.2) ?_ ?_ hz₁ hz₁norm hDo hDne (Set.Subset.refl D) hbrel
    · show coeffFun φ (bmin (Fin.last dmin)) (w : ℂ) ≠ 0
      simpa [hr] using hlw
    · rw [← hQmap]
      exact hsep
  · -- CASE B: proper gcd — factor, clear denominators, split analytically, contradict minimality
    have hg1 : 1 ≤ g.natDegree := Nat.one_le_iff_ne_zero.mpr hg0
    obtain ⟨h, hgh⟩ := EuclideanDomain.gcd_dvd_left qb qb'
    have hhne : h ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hgh
      exact hqbne hgh
    have hdegsum : g.natDegree + h.natDegree = dmin := by
      have := natDegree_mul hgne hhne
      rw [← hgh, hqbdeg] at this
      omega
    have hh1 : 1 ≤ h.natDegree := by omega
    have hhlt : h.natDegree ≤ dmin - 1 := by omega
    obtain ⟨sG, hsGmem, hG₁spec⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(R₀ φ D)) g
    obtain ⟨sH, hsHmem, hH₁spec⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(R₀ φ D)) h
    set G₁ := IsLocalization.integerNormalization (nonZeroDivisors ↥(R₀ φ D)) g with hG₁d
    set H₁ := IsLocalization.integerNormalization (nonZeroDivisors ↥(R₀ φ D)) h with hH₁d
    have hG₁' : G₁.map alg = C (alg sG) * g := by
      rw [hG₁d, hG₁spec, ← algebraMap_smul K sG g, smul_eq_C_mul]
    have hH₁' : H₁.map alg = C (alg sH) * h := by
      rw [hH₁d, hH₁spec, ← algebraMap_smul K sH h, smul_eq_C_mul]
    have hsGne : sG ≠ 0 := nonZeroDivisors.ne_zero hsGmem
    have hsHne : sH ≠ 0 := nonZeroDivisors.ne_zero hsHmem
    have halgsG : alg sG ≠ 0 := fun hh => hsGne (halg_inj (by simpa using hh))
    have halgsH : alg sH ≠ 0 := fun hh => hsHne (halg_inj (by simpa using hh))
    -- the cleared factorization over R₀
    have hfac : G₁ * H₁ = C (sG * sH) * Q := by
      apply hmap_inj
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, hG₁', hH₁', ← hqb]
      simp only [map_mul]
      linear_combination (C (alg sG) * C (alg sH)) * hgh.symm
    -- degrees of the cleared factors
    have hG₁deg : G₁.natDegree = g.natDegree := by
      rw [← natDegree_map_eq_of_injective halg_inj G₁, hG₁', natDegree_C_mul halgsG]
    have hH₁deg : H₁.natDegree = h.natDegree := by
      rw [← natDegree_map_eq_of_injective halg_inj H₁, hH₁', natDegree_C_mul halgsH]
    have hG₁ne : G₁ ≠ 0 := by
      intro hh
      have := hG₁'
      rw [hh, Polynomial.map_zero] at this
      exact hgne ((mul_eq_zero.mp this.symm).resolve_left (fun hc => halgsG (by
        simpa using congrArg (fun p => Polynomial.coeff p 0) hc)))
    have hH₁ne : H₁ ≠ 0 := by
      intro hh
      have := hH₁'
      rw [hh, Polynomial.map_zero] at this
      exact hhne ((mul_eq_zero.mp this.symm).resolve_left (fun hc => halgsH (by
        simpa using congrArg (fun p => Polynomial.coeff p 0) hc)))
    -- abstract lifts of the factor coefficients
    have hlift : ∀ a : ↥(R₀ φ D), ∃ p : Polynomial (Polynomial ℂ), Φring φ D p = (a : ↥D → ℂ) :=
      fun a => a.2
    choose liftG hliftG using fun k => hlift (G₁.coeff k)
    choose liftH hliftH using fun k => hlift (H₁.coeff k)
    -- the factor value functions
    set Gf : ℂ → ℂ := fun z => ∑ k ∈ Finset.range (G₁.natDegree + 1),
      coeffFun φ (liftG k) z * u0 z ^ k with hGf
    set Hf : ℂ → ℂ := fun z => ∑ k ∈ Finset.range (H₁.natDegree + 1),
      coeffFun φ (liftH k) z * u0 z ^ k with hHf
    -- pointwise: the factors multiply to (unit)·(relation) = 0
    have hGfHf : ∀ z ∈ D, Gf z * Hf z = 0 := by
      intro z hz
      set evz : ↥(R₀ φ D) →+* ℂ :=
        (Pi.evalRingHom (fun _ : ↥D => ℂ) ⟨z, hz⟩).comp (R₀ φ D).subtype with hevz
      have hfacz := congrArg (fun p => Polynomial.eval₂ evz (u0 z) p) hfac
      simp only [eval₂_mul, eval₂_C] at hfacz
      have hQz : Polynomial.eval₂ evz (u0 z) Q = 0 := by
        rw [eval₂_eq_eval_map, hQ, map_finSum, eval_finSum]
        have : ∀ i : Fin (dmin + 1), evz (r i) = coeffFun φ (bmin i) z := fun i => rfl
        simp only [this]
        exact hbrel z hz
      have hGz : Polynomial.eval₂ evz (u0 z) G₁ = Gf z := by
        rw [eval₂_eq_sum_range, hGf]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : evz (G₁.coeff k) = coeffFun φ (liftG k) z := by
          have h2 := congrFun (hliftG k) ⟨z, hz⟩
          simpa [hevz] using h2.symm
        rw [this]
      have hHz : Polynomial.eval₂ evz (u0 z) H₁ = Hf z := by
        rw [eval₂_eq_sum_range, hHf]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : evz (H₁.coeff k) = coeffFun φ (liftH k) z := by
          have h2 := congrFun (hliftH k) ⟨z, hz⟩
          simpa [hevz] using h2.symm
        rw [this]
      rw [hGz, hHz, hQz, mul_zero] at hfacz
      exact hfacz
    -- analyticity of the factor functions on D
    have hGfan : AnalyticOnNhd ℂ Gf D := by
      intro z hz
      have h1 : AnalyticAt ℂ (∑ k ∈ Finset.range (G₁.natDegree + 1),
          fun z => coeffFun φ (liftG k) z * u0 z ^ k) z :=
        Finset.analyticAt_sum _ (fun k _ =>
          ((coeffFun_analytic hφ (liftG k)) z (hDΩ hz)).mul
            ((u0_analyticOnNhd_Ext z hz.2).pow _))
      have h2 : (∑ k ∈ Finset.range (G₁.natDegree + 1),
          fun z => coeffFun φ (liftG k) z * u0 z ^ k) = Gf := by
        funext y; rw [hGf]; simp
      rwa [h2] at h1
    have hHfan : AnalyticOnNhd ℂ Hf D := by
      intro z hz
      have h1 : AnalyticAt ℂ (∑ k ∈ Finset.range (H₁.natDegree + 1),
          fun z => coeffFun φ (liftH k) z * u0 z ^ k) z :=
        Finset.analyticAt_sum _ (fun k _ =>
          ((coeffFun_analytic hφ (liftH k)) z (hDΩ hz)).mul
            ((u0_analyticOnNhd_Ext z hz.2).pow _))
      have h2 : (∑ k ∈ Finset.range (H₁.natDegree + 1),
          fun z => coeffFun φ (liftH k) z * u0 z ^ k) = Hf := by
        funext y; rw [hHf]; simp
      rwa [h2] at h1
    -- split, and in either branch produce a smaller RelSet member
    have hsplit := analytic_domain_of_preconnected hDo hDc hGfan hHfan hGfHf
    have hcontr : ∀ (e : ℕ) (F₁ : Polynomial ↥(R₀ φ D)) (lift : ℕ → Polynomial (Polynomial ℂ)),
        (∀ k, Φring φ D (lift k) = ((F₁.coeff k : ↥(R₀ φ D)) : ↥D → ℂ)) →
        F₁ ≠ 0 → F₁.natDegree = e → 1 ≤ e → e ≤ dmin - 1 →
        (∀ z ∈ D, ∑ k ∈ Finset.range (e + 1), coeffFun φ (lift k) z * u0 z ^ k = 0) →
        False := by
      intro e F₁ lift hliftF hF₁ne hF₁deg he1 helt hFzero
      have hPPe : PP e := by
        refine ⟨he1, fun i => lift (i : ℕ), ?_, ?_⟩
        · -- leading coefficient function is not identically zero
          have hlc : F₁.coeff e ≠ 0 := by
            rw [← hF₁deg]
            exact leadingCoeff_ne_zero.mpr hF₁ne
          by_contra hall
          push Not at hall
          apply hlc
          refine (R₀_zero_iff _).mpr fun w => ?_
          have h2 := congrFun (hliftF e) w
          have h3 := hall (w : ℂ) w.2
          rw [Fin.val_last] at h3
          rw [← h2]
          exact h3
        · intro z hz
          have hconv : (∑ i : Fin (e + 1), coeffFun φ (lift (i : ℕ)) z * u0 z ^ (i : ℕ))
              = ∑ k ∈ Finset.range (e + 1), coeffFun φ (lift k) z * u0 z ^ k :=
            Fin.sum_univ_eq_sum_range (fun k => coeffFun φ (lift k) z * u0 z ^ k) (e + 1)
          rw [hconv]
          exact hFzero z hz
      have := hmin e hPPe
      omega
    rcases hsplit with hGzero | hHzero
    · refine hcontr g.natDegree G₁ liftG hliftG hG₁ne hG₁deg hg1 (by omega) ?_
      rw [← hG₁deg]
      exact fun z hz => by simpa [hGf] using hGzero z hz
    · refine hcontr h.natDegree H₁ liftH hliftH hH₁ne hH₁deg hh1 hhlt ?_
      rw [← hH₁deg]
      exact fun z hz => by simpa [hHf] using hHzero z hz

end U0WindowNormalization
