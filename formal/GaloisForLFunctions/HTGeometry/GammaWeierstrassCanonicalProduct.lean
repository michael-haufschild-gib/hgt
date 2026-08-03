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

/-! ## Euler's limit and the Weierstrass identity -/

theorem harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℂ) = ∑ n ∈ Finset.range N, ((n : ℂ) + 1)⁻¹ := by
  simp [harmonic]

/-- The partial product against Euler's Gamma sequence, in closed form. -/
theorem prod_range_mul_gammaSeq (z : ℂ) (hz : ∀ m : ℕ, z + 1 + (m : ℂ) ≠ 0)
    {N : ℕ} (hN : N ≠ 0) :
    (∏ n ∈ Finset.range N, ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))))
        * Complex.GammaSeq (z + 1) N
      = Complex.exp (-(z * (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ))))
          * ((N : ℂ) / ((N : ℂ) + (z + 1))) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hA : (∏ j ∈ Finset.range N, (z + 1 + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hz j
  have hF : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hD : z + 1 + (N : ℂ) ≠ 0 := hz N
  have hGS : Complex.GammaSeq (z + 1) N
      = (N : ℂ) ^ (z + 1) * ((Nat.factorial N : ℕ) : ℂ)
          / ∏ j ∈ Finset.range (N + 1), (z + 1 + (j : ℂ)) := rfl
  have hsplit : ∏ j ∈ Finset.range (N + 1), (z + 1 + (j : ℂ))
      = (∏ j ∈ Finset.range N, (z + 1 + (j : ℂ))) * (z + 1 + (N : ℂ)) :=
    Finset.prod_range_succ _ _
  have hpow : (N : ℂ) ^ (z + 1) = Complex.exp (((Real.log N : ℝ) : ℂ) * z) * (N : ℂ) := by
    rw [Complex.cpow_add _ _ hNC, Complex.cpow_one, Complex.cpow_def_of_ne_zero hNC]
    congr 2
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity)]
  have hne2 : ((N : ℂ) + (z + 1)) ≠ 0 := by
    rw [show ((N : ℂ) + (z + 1)) = z + 1 + (N : ℂ) from by ring]
    exact hD
  rw [prod_range_weierstrass, ← harmonic_cast_eq, hGS, hsplit, hpow]
  field_simp
  have hE : Complex.exp (-(z * ((harmonic N : ℚ) : ℂ)) + z * ((Real.log N : ℝ) : ℂ))
      = Complex.exp (-(z * (((harmonic N : ℚ) : ℂ) - ((Real.log N : ℝ) : ℂ)))) := by
    congr 1
    ring
  rw [← Complex.exp_add, hE, show ((N : ℂ) + (z + 1)) = z + 1 + (N : ℂ) from by ring]
  ring

/-- **Weierstrass form of the exponent-one canonical product**, away from its zeros. -/
theorem powerCanonicalProduct_one_mul_Gamma (z : ℂ) (hz : ∀ m : ℕ, z + 1 + (m : ℂ) ≠ 0) :
    powerCanonicalProduct 1 z * Complex.Gamma (z + 1)
      = Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * z)) := by
  have hP : Filter.Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N,
        ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))))
      Filter.atTop (nhds (powerCanonicalProduct 1 z)) :=
    (hasProd_powerCanonicalProduct_one z).tendsto_prod_nat
  have hL : Filter.Tendsto
      (fun N : ℕ => (∏ n ∈ Finset.range N,
        ((1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))))
          * Complex.GammaSeq (z + 1) N)
      Filter.atTop (nhds (powerCanonicalProduct 1 z * Complex.Gamma (z + 1))) :=
    hP.mul (Complex.GammaSeq_tendsto_Gamma (z + 1))
  have hEM : Filter.Tendsto
      (fun N : ℕ => (((harmonic N : ℚ) : ℝ) - Real.log N : ℝ)) Filter.atTop
      (nhds Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hEMC : Filter.Tendsto
      (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log N : ℝ) : ℂ)) Filter.atTop
      (nhds ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hEM
  have hexp : Filter.Tendsto
      (fun N : ℕ => Complex.exp (-(z * ((((harmonic N : ℚ) : ℝ) - Real.log N : ℝ) : ℂ))))
      Filter.atTop (nhds (Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * z)))) := by
    have h1 : Filter.Tendsto
        (fun N : ℕ => -(z * ((((harmonic N : ℚ) : ℝ) - Real.log N : ℝ) : ℂ))) Filter.atTop
        (nhds (-(z * ((Real.eulerMascheroniConstant : ℝ) : ℂ)))) :=
      (hEMC.const_mul z).neg
    have h2 := (Complex.continuous_exp.tendsto _).comp h1
    rw [show (-((Real.eulerMascheroniConstant : ℂ) * z))
      = -(z * ((Real.eulerMascheroniConstant : ℝ) : ℂ)) from by ring]
    exact h2
  have hdiv : Filter.Tendsto (fun N : ℕ => (N : ℂ) / ((N : ℂ) + (z + 1)))
      Filter.atTop (nhds 1) := tendsto_natCast_div_add_atTop (z + 1)
  have hR : Filter.Tendsto
      (fun N : ℕ => Complex.exp (-(z * ((((harmonic N : ℚ) : ℝ) - Real.log N : ℝ) : ℂ)))
        * ((N : ℂ) / ((N : ℂ) + (z + 1)))) Filter.atTop
      (nhds (Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * z)))) := by
    simpa using hexp.mul hdiv
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [Filter.eventually_ne_atTop 0] with N hN
  rw [prod_range_mul_gammaSeq z hz hN]
  push_cast
  ring_nf

/-- The exponent-one canonical product vanishes at every negative integer. -/
theorem powerCanonicalProduct_one_eq_zero (m : ℕ) :
    powerCanonicalProduct 1 (-((m : ℂ) + 1)) = 0 := by
  set z : ℂ := -((m : ℂ) + 1) with hzdef
  have hmne : ((m : ℂ) + 1) ≠ 0 := by
    have h : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact_mod_cast Nat.succ_ne_zero m
  have hfactor : (1 + z / ((m : ℂ) + 1)) * Complex.exp (-(z / ((m : ℂ) + 1))) = 0 := by
    have hd : z / ((m : ℂ) + 1) = -1 := by
      rw [hzdef]
      field_simp
    rw [hd]
    ring
  have hP := (hasProd_powerCanonicalProduct_one z).tendsto_prod_nat
  refine tendsto_nhds_unique hP ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (m + 1)] with N hN
  symm
  refine Finset.prod_eq_zero (Finset.mem_range.mpr (by omega)) hfactor

/-- **Weierstrass form of the exponent-one canonical product.**  `W_1(z) = e^{-γ z}/Γ(z+1)`, with
`γ` the Euler–Mascheroni constant, at every complex point. -/
theorem powerCanonicalProduct_one_eq (z : ℂ) :
    powerCanonicalProduct 1 z
      = Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * z)) * (Complex.Gamma (z + 1))⁻¹ := by
  by_cases hz : ∀ m : ℕ, z + 1 + (m : ℂ) ≠ 0
  · have hΓ : Complex.Gamma (z + 1) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m => ?_
      intro h
      exact hz m (by rw [h]; ring)
    have hmul := powerCanonicalProduct_one_mul_Gamma z hz
    field_simp at hmul ⊢
    linear_combination hmul
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, z + 1 + (m : ℂ) = 0 := by
      by_contra hcon
      exact hz fun m h => hcon ⟨m, h⟩
    have hzval : z = -((m : ℂ) + 1) := by linear_combination hm
    have hΓ : Complex.Gamma (z + 1) = 0 := by
      have hshift : z + 1 = -(m : ℂ) := by rw [hzval]; ring
      rw [hshift, Complex.Gamma_neg_nat_eq_zero]
    rw [hΓ, inv_zero, mul_zero, hzval]
    exact powerCanonicalProduct_one_eq_zero m

end HTGeometry

