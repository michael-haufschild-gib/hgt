import GaloisForLFunctions.HTGeometry.RationalPowerHypertranscendenceTransfer

/-!
# Even-exponent power canonical products are differentially algebraic

For an even integer `p = 2m` the canonical product with zeros `-n^p` becomes elementary after the
substitution `z = -w^p`: the `2m`-th roots of unity pair off, and each pair assembles an Euler sine
product.  Concretely

`W_{2m}(-w^{2m}) = ∏_{k<m} sinc(α^k w)`,  `sinc(c) = ∏_{n ≥ 1}(1 - c²/n²) = sin(π c)/(π c)`,

where `α` is a primitive `2m`-th root of unity.  Each factor satisfies the algebraic differential
equation `(π c y)² + (y + c y')² = 1` coming from `sin² + cos² = 1`, so the right-hand side is
differentially algebraic; descent along `z ↦ -z^{2m}` then makes `W_{2m}` itself differentially
algebraic.

This is the even half of the integer-exponent dichotomy.  The odd half is genuinely different: for
odd `p` the roots of unity admit no pairing and no elementary closed form appears.
-/

namespace HTGeometry

open GaloisForLFunctions

/-! ## The Euler sine product as a canonical product -/

/-- The square zero sequence `n ↦ (n+1)²`. -/
noncomputable def sqZero (n : ℕ) : ℂ := ((n : ℂ) + 1) ^ 2

theorem sqZero_ne_zero (n : ℕ) : sqZero n ≠ 0 := by
  have h : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero n
  exact pow_ne_zero _ h

theorem norm_sqZero (n : ℕ) : ‖sqZero n‖ = ((n : ℝ) + 1) ^ 2 := by
  have h : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    push_cast
    ring
  rw [sqZero, norm_pow, h]

theorem sqZero_summable : Summable (fun n : ℕ => 1 / ‖sqZero n‖ ^ (0 + 1)) := by
  have hrw : (fun n : ℕ => 1 / ‖sqZero n‖ ^ (0 + 1))
      = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    funext n
    rw [norm_sqZero]
    ring
  rw [hrw]
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    refine h.congr fun n => ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).mpr hsum
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

/-- The Euler sine product `sinc(c) = ∏_{n ≥ 1} (1 - c²/n²)`. -/
noncomputable def sincProduct (c : ℂ) : ℂ := canonicalProduct 0 sqZero (c ^ 2)

theorem primaryFactor_zero_apply (z : ℂ) : primaryFactor 0 z = 1 - z := by
  simp [primaryFactor]

theorem hasProd_sincProduct (c : ℂ) :
    HasProd (fun n : ℕ => 1 - c ^ 2 / ((n : ℂ) + 1) ^ 2) (sincProduct c) := by
  have h := (canonicalProduct_hasProdLocallyUniformlyOn 0 sqZero sqZero_ne_zero
    sqZero_summable).hasProd (Set.mem_univ (c ^ 2))
  refine h.congr_fun ?_
  intro n
  rw [primaryFactor_zero_apply, sqZero]

/-- The Euler sine product is entire. -/
theorem analyticOnNhd_sincProduct : AnalyticOnNhd ℂ sincProduct Set.univ := by
  intro c _
  have houter : AnalyticAt ℂ (canonicalProduct 0 sqZero) (c ^ 2) :=
    canonicalProduct_analytic 0 sqZero sqZero_ne_zero sqZero_summable (c ^ 2) (Set.mem_univ _)
  have hinner : AnalyticAt ℂ (fun x : ℂ => x ^ 2) c := by fun_prop
  exact AnalyticAt.comp (f := fun x : ℂ => x ^ 2) houter hinner

/-- Euler's product formula: `π c · sinc(c) = sin(π c)`, valid at every complex point. -/
theorem pi_mul_sincProduct (c : ℂ) :
    (Real.pi : ℂ) * c * sincProduct c = Complex.sin ((Real.pi : ℂ) * c) := by
  have h1 : Filter.Tendsto
      (fun n : ℕ => (Real.pi : ℂ) * c * ∏ j ∈ Finset.range n, (1 - c ^ 2 / ((j : ℂ) + 1) ^ 2))
      Filter.atTop (nhds ((Real.pi : ℂ) * c * sincProduct c)) :=
    ((hasProd_sincProduct c).tendsto_prod_nat).const_mul _
  exact tendsto_nhds_unique h1 (Complex.tendsto_euler_sin_prod c)

/-- The Euler sine product satisfies the algebraic differential equation
`(π c y)² + (y + c y')² = 1`. -/
theorem sincProduct_ade (c : ℂ) :
    ((Real.pi : ℂ) * c * sincProduct c) ^ 2
      + (sincProduct c + c * deriv sincProduct c) ^ 2 = 1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : HasDerivAt sincProduct (deriv sincProduct c) c :=
    (analyticOnNhd_sincProduct c (Set.mem_univ c)).differentiableAt.hasDerivAt
  have hlin : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x) (Real.pi : ℂ) c := by
    have h := (hasDerivAt_id c).const_mul (Real.pi : ℂ)
    rw [mul_one] at h
    exact h
  have hleft : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x * sincProduct x)
      ((Real.pi : ℂ) * sincProduct c + (Real.pi : ℂ) * c * deriv sincProduct c) c :=
    hlin.mul hd
  have hright : HasDerivAt (fun x : ℂ => Complex.sin ((Real.pi : ℂ) * x))
      ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * c)) c := by
    have h := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * c)).comp c hlin
    rw [show (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * c)
      = Complex.cos ((Real.pi : ℂ) * c) * (Real.pi : ℂ) by ring]
    exact h
  have heq : (fun x : ℂ => (Real.pi : ℂ) * x * sincProduct x)
      = fun x : ℂ => Complex.sin ((Real.pi : ℂ) * x) := funext pi_mul_sincProduct
  have hderiv : (Real.pi : ℂ) * sincProduct c + (Real.pi : ℂ) * c * deriv sincProduct c
      = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * c) := by
    rw [heq] at hleft
    exact hleft.unique hright
  have hcos : sincProduct c + c * deriv sincProduct c
      = Complex.cos ((Real.pi : ℂ) * c) :=
    mul_left_cancel₀ hpi (by linear_combination hderiv)
  rw [pi_mul_sincProduct, hcos]
  exact Complex.sin_sq_add_cos_sq _

/-- The Euler sine product is differentially algebraic. -/
theorem differentiallyAlgebraic_sincProduct : DifferentiallyAlgebraic sincProduct := by
  classical
  refine ⟨1, (MvPolynomial.C (Real.pi : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1) ^ 2
      + (MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2) ^ 2 - 1, ?_, ?_⟩
  · intro hzero
    have h := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : ℂ))) hzero
    simp at h
  · intro z
    have h0 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) sincProduct z) : Fin 3 → ℂ) 0
        = z := rfl
    have h1 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) sincProduct z) : Fin 3 → ℂ) 1
        = sincProduct z := by
      rw [show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    have h2 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) sincProduct z) : Fin 3 → ℂ) 2
        = deriv sincProduct z := by
      rw [show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_one]
    simp only [map_sub, map_add, map_pow, map_mul, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, h0, h1, h2]
    rw [sincProduct_ade z]
    ring

/-! ## The even-exponent factorization -/

/-- Root-of-unity factorisation of `1 - X^m`. -/
theorem one_sub_pow_eq_prod_primitiveRoot {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (X : ℂ) :
    1 - X ^ m = ∏ k ∈ Finset.range m, (1 - ζ ^ k * X) := by
  have h := prod_one_add_primitiveRoot_pow_mul hm hζ (-X)
  rw [neg_neg] at h
  rw [← h]
  exact Finset.prod_congr rfl fun k _ => by ring

/-- The `n`-th factor of an even-exponent power canonical product, evaluated at `-w^{2m}`. -/
theorem powerZero_even_apply {m : ℕ} (n : ℕ) :
    powerZero ((2 * m : ℕ) : ℝ) n = -(((n : ℂ) + 1) ^ (2 * m)) := by
  have hbase : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hreal : (((n : ℝ) + 1) ^ (((2 * m : ℕ) : ℝ))) = ((n : ℝ) + 1) ^ (2 * m : ℕ) :=
    Real.rpow_natCast _ _
  rw [powerZero, hreal]
  push_cast
  ring

/-- **Even-exponent sine factorisation.**  For `p = 2m` the canonical product with zeros `-n^p`,
evaluated at `-w^p`, is the product of `m` Euler sine products at the rotated points `α^k w`. -/
theorem powerCanonicalProduct_even_eq_prod_sinc {m : ℕ} (hm : 0 < m) {α : ℂ}
    (hα : IsPrimitiveRoot α (2 * m)) (w : ℂ) :
    powerCanonicalProduct ((2 * m : ℕ) : ℝ) (-(w ^ (2 * m)))
      = ∏ k ∈ Finset.range m, sincProduct (α ^ k * w) := by
  have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this
  have hgenus : powerGenus ((2 * m : ℕ) : ℝ) = 0 := by
    rw [powerGenus_natCast]
    exact Nat.div_eq_of_lt (by omega)
  have hζ : IsPrimitiveRoot (α ^ 2) m :=
    IsPrimitiveRoot.pow (n := 2 * m) (a := 2) (b := m) (by omega) hα rfl
  have h1 : HasProd (fun n : ℕ => 1 - w ^ (2 * m) / ((n : ℂ) + 1) ^ (2 * m))
      (powerCanonicalProduct ((2 * m : ℕ) : ℝ) (-(w ^ (2 * m)))) := by
    have h := hasProd_powerCanonicalProduct hpos (-(w ^ (2 * m)))
    refine h.congr_fun ?_
    intro n
    rw [hgenus, primaryFactor_zero_apply, powerZero_even_apply, neg_div_neg_eq]
  have h2 : HasProd
      (fun n : ℕ => ∏ k ∈ Finset.range m, (1 - (α ^ k * w) ^ 2 / ((n : ℂ) + 1) ^ 2))
      (∏ k ∈ Finset.range m, sincProduct (α ^ k * w)) :=
    hasProd_prod fun k _ => hasProd_sincProduct (α ^ k * w)
  have hfac : ∀ n : ℕ, 1 - w ^ (2 * m) / ((n : ℂ) + 1) ^ (2 * m)
      = ∏ k ∈ Finset.range m, (1 - (α ^ k * w) ^ 2 / ((n : ℂ) + 1) ^ 2) := by
    intro n
    have hX : w ^ (2 * m) / ((n : ℂ) + 1) ^ (2 * m)
        = (w ^ 2 / ((n : ℂ) + 1) ^ 2) ^ m := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm 2 m]
    rw [hX, one_sub_pow_eq_prod_primitiveRoot hm hζ (w ^ 2 / ((n : ℂ) + 1) ^ 2)]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hpow : (α ^ 2) ^ k = (α ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hpow, mul_pow]
    ring
  have h1' : HasProd
      (fun n : ℕ => ∏ k ∈ Finset.range m, (1 - (α ^ k * w) ^ 2 / ((n : ℂ) + 1) ^ 2))
      (powerCanonicalProduct ((2 * m : ℕ) : ℝ) (-(w ^ (2 * m)))) := by
    simpa only [hfac] using h1
  exact h1'.unique h2

/-- **Even half of the integer dichotomy.**  For every even positive integer `p`, the canonical
product with zeros `-n^p` is differentially algebraic. -/
theorem differentiallyAlgebraic_powerCanonicalProduct_even {m : ℕ} (hm : 0 < m) :
    DifferentiallyAlgebraic (powerCanonicalProduct ((2 * m : ℕ) : ℝ)) := by
  classical
  have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this
  obtain ⟨α, hα⟩ : ∃ α : ℂ, IsPrimitiveRoot α (2 * m) :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℕ)),
      Complex.isPrimitiveRoot_exp (2 * m) (by omega)⟩
  have hαne : α ≠ 0 := hα.ne_zero (by omega)
  have hAfac : ∀ k ∈ Finset.range m,
      AnalyticOnNhd ℂ (fun w : ℂ => sincProduct (α ^ k * w)) Set.univ := by
    intro k _ w _
    exact (analyticOnNhd_sincProduct (α ^ k * w) (Set.mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)
  have hDAfac : ∀ k ∈ Finset.range m,
      DifferentiallyAlgebraic (fun w : ℂ => sincProduct (α ^ k * w)) :=
    fun k _ => differentiallyAlgebraic_sincProduct.comp_const_mul_uncond (pow_ne_zero k hαne)
  have hDAprod : DifferentiallyAlgebraic
      (fun w : ℂ => ∏ k ∈ Finset.range m, sincProduct (α ^ k * w)) :=
    differentiallyAlgebraic_finsetProd (Finset.range m) _ hAfac hDAfac
  have heq : (fun w : ℂ =>
        powerCanonicalProduct ((2 * m : ℕ) : ℝ) ((-1 : ℂ) * w ^ (2 * m)))
      = fun w : ℂ => ∏ k ∈ Finset.range m, sincProduct (α ^ k * w) := by
    funext w
    rw [show ((-1 : ℂ) * w ^ (2 * m)) = -(w ^ (2 * m)) by ring]
    exact powerCanonicalProduct_even_eq_prod_sinc hm hα w
  have hcomp : DifferentiallyAlgebraic
      (fun w : ℂ => powerCanonicalProduct ((2 * m : ℕ) : ℝ) ((-1 : ℂ) * w ^ (2 * m))) := by
    rw [heq]; exact hDAprod
  exact differentiallyAlgebraic_of_comp_const_mul_pow
    (analyticOnNhd_powerCanonicalProduct hpos) (by norm_num) (by omega) hcomp

/-- The even half of the dichotomy in parity form. -/
theorem differentiallyAlgebraic_powerCanonicalProduct_of_even {p : ℕ} (hp : 0 < p)
    (hpe : Even p) : DifferentiallyAlgebraic (powerCanonicalProduct (p : ℝ)) := by
  obtain ⟨m, hm⟩ := hpe
  have hpm : p = 2 * m := by omega
  have hmpos : 0 < m := by omega
  subst hpm
  exact differentiallyAlgebraic_powerCanonicalProduct_even hmpos

end HTGeometry

