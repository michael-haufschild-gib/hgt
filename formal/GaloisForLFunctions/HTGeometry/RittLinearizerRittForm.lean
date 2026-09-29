import GaloisForLFunctions.HTGeometry.RittMeromorphicGermFrame
import GaloisForLFunctions.HTGeometry.RittSubstitutionFixed

/-!
# Ritt's first-order form for a differentially algebraic linearizer

Let `R` have degree at least two and a fixed point `0` whose multiplier `λ` is nonzero and not a
root
of unity, and let `κ` be an analytic linearizer, `κ(R(z)) = λ·κ(z)`, with `κ(0) = 0`, `κ'(0) ≠ 0`.
If `κ` satisfies an algebraic differential equation near `0`, then

`κ'(z)^N = A(z)·κ(z)^j`

near `0` for some `N ≥ 1`, `j ∈ ℤ` and a nonzero rational `A` — Ritt's first-order form.

The proof: Ritt's implication gives the cocycle `R'^N·B = λ^{N+j}·B(R)`; then `H = (κ')^N·B·κ^j` is
invariant under composition with `R`, because `κ'(R)·R' = λκ'` and `κ(R) = λκ`, so `H` is a
constant.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem ofMero_pow {f : ℂ → ℂ} (hf : MeromorphicAt f 0) (n : ℕ) :
    ofMero f hf ^ n = ofMero (f ^ n) (hf.pow n) := by
  induction n with
  | zero => rw [pow_zero, ← ofMero_one, ofMero_eq_iff]; exact Eventually.of_forall fun z => by simp
  | succ n ih =>
      rw [pow_succ, ih, ofMero_mul, ofMero_eq_iff]
      exact Eventually.of_forall fun z => by simp [pow_succ]

theorem ofMero_zpow {f : ℂ → ℂ} (hf : MeromorphicAt f 0) (n : ℤ) :
    ofMero f hf ^ n = ofMero (f ^ n) (hf.zpow n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, ofMero_pow, ofMero_eq_iff]
    exact Eventually.of_forall fun z => by simp
  · rw [zpow_neg, zpow_natCast, ofMero_pow, ofMero_inv, ofMero_eq_iff]
    exact Eventually.of_forall fun z => by simp

variable {R : RatFunc ℂ}

/-- **Ritt's first-order form for a differentially algebraic linearizer.** -/
theorem rittForm_of_differentiallyAlgebraicOn_linearizer (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (hfix : IsLinearizableFixedPoint R) {κ : ℂ → ℂ}
    (hκ : AnalyticAt ℂ κ 0) (hκ' : deriv κ 0 ≠ 0)
    (hfe : ∀ᶠ z in 𝓝 (0 : ℂ), κ (ratValue R z) = ratValue (ratFuncDeriv R) 0 * κ z)
    {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) (hDA : DifferentiallyAlgebraicOn κ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ j : ℤ, ∃ A : RatFunc ℂ, A ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv κ z ^ N = ratValue A z * κ z ^ j := by
  set lam := ratValue (ratFuncDeriv R) 0 with hlamdef
  have hlam0 : lam ≠ 0 := hfix.mult_ne_zero
  obtain ⟨N, hN, j, B, hB, hcoc⟩ :=
    ratCocycle_of_differentiallyAlgebraicOn_linearizer hR hd hfix hκ hκ' hlam0 hfe hU hDA
  set Fr := hfix.frame hR with hFr
  set τ := ofMero κ hκ.meromorphicAt with hτdef
  set dτ := ofMero (deriv κ) hκ.deriv.meromorphicAt with hdτdef
  have hτ0 : τ ≠ 0 := ofMero_ne_zero_of_deriv_ne_zero hκ hκ'
  have hdτ0 : dτ ≠ 0 := ofMero_ne_zero_of_ne_zero hκ.deriv hκ'
  have hdτeq : meroDeriv τ = dτ := meroDeriv_ofMero _
  have hR' : ratFuncDeriv R ≠ 0 := ratFuncDeriv_ne_zero_of_nonconst' hR
  set r := algebraMap (RatFunc ℂ) MeroGerm (ratFuncDeriv R) with hrdef
  have hr0 : r ≠ 0 := (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) MeroGerm).injective).mpr hR'
  set l := algebraMap (RatFunc ℂ) MeroGerm (RatFunc.C lam) with hldef
  have hl0 : l ≠ 0 := by
    rw [hldef]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) MeroGerm).injective).mpr (by simpa using hlam0)
  -- the shift of the linearizer and of its derivative
  have hστ : hfix.pull τ = l * τ := by
    rw [hτdef, hfix.pull_ofMero, hldef, algebraMap_ratFunc_meroGerm, ofMero_mul, ofMero_eq_iff]
    filter_upwards [nhdsWithin_le_nhds hfe] with z hz
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [hz, ratValue_C]
  have hσdτ : r * hfix.pull dτ = l * dτ := by
    have h := hfix.meroDeriv_pull τ
    rw [hστ, meroDeriv_mul, hdτeq, hldef, meroDeriv_algebraMap, ratFuncDeriv_C, map_zero,
      mul_zero, add_zero] at h
    rw [← hrdef, ← hldef] at h
    exact h.symm
  -- the cocycle, read in the germ field
  have hcocL : r ^ N * algebraMap (RatFunc ℂ) MeroGerm B
      = l ^ ((N : ℤ) + j) * hfix.pull (algebraMap (RatFunc ℂ) MeroGerm B) := by
    have h := congrArg (algebraMap (RatFunc ℂ) MeroGerm) hcoc
    rw [map_mul, map_pow, map_mul, ← hfix.pull_algebraMap hR] at h
    rw [h, hldef, ← map_zpow₀, ← RatFunc.algebraMap_eq_C, ← map_zpow₀]
  -- the invariant
  set bB := algebraMap (RatFunc ℂ) MeroGerm B with hbB
  have hbB0 : bB ≠ 0 := (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) MeroGerm).injective).mpr hB
  set H := dτ ^ N * bB * τ ^ j with hH
  have hσH : hfix.pull H = H := by
    have hpdτ : hfix.pull dτ = l * dτ / r := by rw [eq_div_iff hr0, ← hσdτ]; ring
    have hpB : hfix.pull bB = r ^ N * bB / l ^ ((N : ℤ) + j) := by
      rw [eq_div_iff (zpow_ne_zero _ hl0), hcocL]; ring
    rw [hH, map_mul, map_mul, map_pow, map_zpow₀, hpdτ, hpB, hστ, div_pow, mul_pow, mul_zpow,
      zpow_add₀ hl0, zpow_natCast]
    field_simp
  obtain ⟨a, ha⟩ := hfix.pull_fixed H hσH
  have hψa : ratFuncSubstitutionAlgHom R hR a = a := by
    apply (algebraMap (RatFunc ℂ) MeroGerm).injective
    rw [← hfix.pull_algebraMap hR, ha, hσH]
  obtain ⟨c, hc⟩ := eq_C_of_substitution_fixed hR hd hψa
  have hH0 : H ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hdτ0) hbB0) (zpow_ne_zero _ hτ0)
  refine ⟨N, hN, -j, RatFunc.C c * B⁻¹, ?_, ?_⟩
  · refine mul_ne_zero ?_ (inv_ne_zero hB)
    intro hc0
    apply hH0
    rw [← ha, hc, hc0, map_zero]
  · have hkey : dτ ^ N = algebraMap (RatFunc ℂ) MeroGerm (RatFunc.C c * B⁻¹) * τ ^ (-j) := by
      rw [map_mul, map_inv₀, ← hc, ha, ← hbB, hH, zpow_neg]
      field_simp
    rw [hdτdef, hτdef, ofMero_pow, ofMero_zpow, algebraMap_ratFunc_meroGerm, ofMero_mul,
      ofMero_eq_iff] at hkey
    exact hkey.mono fun z hz => by simpa using hz

end

end GaloisForLFunctions.HTGeometry
