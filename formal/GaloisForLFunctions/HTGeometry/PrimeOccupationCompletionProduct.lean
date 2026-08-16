import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA

/-!
# The all-prime occupation product and its even-temperature collapse

At temperature `r` the occupation modes of a prime packet contribute the zeros `n^r` for the
positive integers `n` built from the packet.  Cofinal completion of the packet replaces those by
all positive integers, so the completed product is the canonical product with zeros `n^r`:

`Φ_r(x) = ∏_{n ≥ 1} (1 - x / n^r)`.

For even `r` the `r`-th roots of unity pair off and the product becomes a finite product of Euler
sine products, hence differentially algebraic.  At `r = 2` the collapse is completely explicit:
`π c · Φ_2(c²) = sin(π c)`, and `Φ_2` solves the second-order linear equation
`4 x y'' + 6 y' + π² y = 0`.
-/

namespace HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The completed occupation product at temperature `r`: the entire function with simple zeros at
the `r`-th powers of the positive integers. -/
def occupationProduct (r : ℕ) (x : ℂ) : ℂ := powerCanonicalProduct (r : ℝ) (-x)

theorem powerZero_natCast_apply {r : ℕ} (n : ℕ) :
    powerZero ((r : ℕ) : ℝ) n = -(((n : ℂ) + 1) ^ r) := by
  have hreal : (((n : ℝ) + 1) ^ ((r : ℕ) : ℝ)) = ((n : ℝ) + 1) ^ (r : ℕ) :=
    Real.rpow_natCast _ _
  rw [powerZero, hreal]
  push_cast
  ring

theorem powerGenus_eq_zero_of_two_le {r : ℕ} (hr : 2 ≤ r) : powerGenus ((r : ℕ) : ℝ) = 0 := by
  rw [powerGenus_natCast]
  exact Nat.div_eq_of_lt (by omega)

/-- **The completed product.**  For `r ≥ 2` the occupation product is the convergent product of
the factors `1 - x/n^r` over the positive integers. -/
theorem hasProd_occupationProduct {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    HasProd (fun n : ℕ => 1 - x / ((n : ℂ) + 1) ^ r) (occupationProduct r x) := by
  have hpos : (0 : ℝ) < ((r : ℕ) : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have h := hasProd_powerCanonicalProduct hpos (-x)
  refine h.congr_fun fun n => ?_
  rw [powerGenus_eq_zero_of_two_le hr, primaryFactor_zero_apply, powerZero_natCast_apply,
    neg_div_neg_eq]

theorem analyticOnNhd_occupationProduct {r : ℕ} (hr : 2 ≤ r) :
    AnalyticOnNhd ℂ (occupationProduct r) Set.univ := by
  have hpos : (0 : ℝ) < ((r : ℕ) : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  intro x _
  exact (analyticOnNhd_powerCanonicalProduct hpos (-x) (Set.mem_univ _)).comp
    (analyticAt_id.neg)

/-- **Even-temperature collapse.**  At even temperature the completed occupation product is
differentially algebraic, although every finite packet is hypertranscendental. -/
theorem differentiallyAlgebraic_occupationProduct_of_even {r : ℕ} (hr : 2 ≤ r) (hre : Even r) :
    DifferentiallyAlgebraic (occupationProduct r) := by
  have hbase : DifferentiallyAlgebraic (powerCanonicalProduct ((r : ℕ) : ℝ)) :=
    differentiallyAlgebraic_powerCanonicalProduct_of_even (by omega) hre
  have hneg : (-1 : ℂ) ≠ 0 := by norm_num
  have h := hbase.comp_const_mul_uncond hneg
  have heq : (fun z : ℂ => powerCanonicalProduct ((r : ℕ) : ℝ) ((-1 : ℂ) * z))
      = occupationProduct r := by
    funext x
    rw [occupationProduct]
    congr 1
    ring
  rwa [heq] at h

/-! ## Temperature two: the explicit sine collapse -/

/-- **The sine collapse at temperature two.**  The completed occupation product at `r = 2`
evaluated at a square is the Euler sinc product. -/
theorem occupationProduct_two_sq (c : ℂ) : occupationProduct 2 (c ^ 2) = sincProduct c := by
  have h1 := hasProd_occupationProduct (r := 2) (by norm_num) (c ^ 2)
  have h2 := hasProd_sincProduct c
  exact h1.unique h2

/-- **Euler's product at temperature two.**  `π c · Φ₂(c²) = sin(π c)`. -/
theorem pi_mul_occupationProduct_two (c : ℂ) :
    (Real.pi : ℂ) * c * occupationProduct 2 (c ^ 2) = Complex.sin ((Real.pi : ℂ) * c) := by
  rw [occupationProduct_two_sq]
  exact pi_mul_sincProduct c

end

end HTGeometry
