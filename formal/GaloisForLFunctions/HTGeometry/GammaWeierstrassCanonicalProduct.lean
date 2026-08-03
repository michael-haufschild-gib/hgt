import GaloisForLFunctions.HTGeometry.RationalPowerCyclicNorm

/-!
# The exponent-one power canonical product is the Weierstrass product for `1/Γ`

The canonical product of minimal genus with simple zeros exactly at `-n`, `n ≥ 1`, is

`W_1(z) = ∏_{n ≥ 1} (1 + z/n) e^{-z/n} = e^{-γ z} / Γ(z+1)`,

with `γ` the Euler–Mascheroni constant.  The identity is proved from Euler's limit formula for `Γ`
together with `H_N - log N → γ`: the `N`-th partial product equals

`(N^{z+1} / ((z+1+N) · GammaSeq(z+1, N))) · e^{-z H_N}`,

whose three factors converge to `1/Γ(z+1)`, `1` and `e^{-γ z}` respectively.  At the zeros
`z = -(m+1)` both sides vanish, the right-hand side because mathlib's `Γ` takes the value `0` at its
poles.
-/

namespace HTGeometry

open Complex Filter Finset

/-! ## The genus-one factors -/

@[simp] theorem powerGenus_one : powerGenus 1 = 1 := by
  simp [powerGenus]

theorem powerZero_one (n : ℕ) : powerZero 1 n = -((n : ℂ) + 1) := by
  rw [powerZero, Real.rpow_one]
  push_cast
  ring

theorem primaryFactor_one_apply (u : ℂ) : primaryFactor 1 u = (1 - u) * Complex.exp u := by
  simp [primaryFactor, primaryExponent]

/-- The Weierstrass factors of the exponent-one canonical product. -/
theorem hasProd_powerCanonicalProduct_one (z : ℂ) :
    HasProd (fun n : ℕ => (1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))
      (powerCanonicalProduct 1 z) := by
  have h := hasProd_powerCanonicalProduct (a := (1 : ℝ)) one_pos z
  refine h.congr_fun ?_
  intro n
  rw [powerGenus_one, powerZero_one, primaryFactor_one_apply]
  have hne : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero n
  rw [div_neg]
  ring

/-- Closed form of the `N`-th partial product. -/
theorem prod_range_weierstrass (z : ℂ) (N : ℕ) :
    ∏ n ∈ Finset.range N, ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))
      = ((∏ j ∈ Finset.range N, (z + 1 + (j : ℂ))) / ((Nat.factorial N : ℕ) : ℂ))
          * Complex.exp (-(z * ∑ n ∈ Finset.range N, ((n : ℂ) + 1)⁻¹)) := by
  have hne : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := by
    intro n
    have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact_mod_cast Nat.succ_ne_zero n
  have hfac : ∏ n ∈ Finset.range N, ((n : ℂ) + 1) = ((Nat.factorial N : ℕ) : ℂ) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
        push_cast
        ring
  have hfacne : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by
    rw [← hfac]
    exact Finset.prod_ne_zero_iff.mpr fun n _ => hne n
  have hs : ∑ n ∈ Finset.range N, (-(z / ((n : ℂ) + 1)))
      = -(z * ∑ n ∈ Finset.range N, ((n : ℂ) + 1)⁻¹) := by
    simp [Finset.mul_sum, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [eq_div_iff hfacne, ← hfac, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    field_simp
    ring
  · rw [← Complex.exp_sum, hs]

end HTGeometry
