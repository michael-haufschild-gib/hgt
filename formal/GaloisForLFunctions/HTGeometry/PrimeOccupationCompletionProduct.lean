import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

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

open GaloisForLFunctions Complex Filter Topology

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

/-! ## The second-order law at temperature two -/

/-- **The second-order law behind a sine square law.**  An entire function whose value at a square
is the normalized sine solves `4 x y'' + 6 y' + π² y = 0`. -/
theorem ode_of_sin_square_law {Φ : ℂ → ℂ} (hA : AnalyticOnNhd ℂ Φ Set.univ)
    (hs : ∀ c : ℂ, (Real.pi : ℂ) * c * Φ (c ^ 2) = Complex.sin ((Real.pi : ℂ) * c)) (x : ℂ) :
    4 * x * deriv (deriv Φ) x + 6 * deriv Φ x + (Real.pi : ℂ) ^ 2 * Φ x = 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hA1 : AnalyticOnNhd ℂ (deriv Φ) Set.univ := hA.deriv
  have hA2 : AnalyticOnNhd ℂ (deriv (deriv Φ)) Set.univ := hA1.deriv
  have hdiff : ∀ z : ℂ, HasDerivAt Φ (deriv Φ z) z := fun z =>
    ((hA z (Set.mem_univ _)).differentiableAt).hasDerivAt
  have hdiff1 : ∀ z : ℂ, HasDerivAt (deriv Φ) (deriv (deriv Φ) z) z := fun z =>
    ((hA1 z (Set.mem_univ _)).differentiableAt).hasDerivAt
  have hlin : ∀ c : ℂ, HasDerivAt (fun c : ℂ => (Real.pi : ℂ) * c) (Real.pi : ℂ) c := by
    intro c
    simpa using (hasDerivAt_id c).const_mul ((Real.pi : ℂ))
  have hsq : ∀ c : ℂ, HasDerivAt (fun c : ℂ => c ^ 2) (2 * c) c := by
    intro c
    simpa using hasDerivAt_pow 2 c
  have hcompΦ : ∀ c : ℂ, HasDerivAt (fun c : ℂ => Φ (c ^ 2)) (deriv Φ (c ^ 2) * (2 * c)) c := by
    intro c
    simpa [Function.comp_def] using HasDerivAt.comp c (hdiff (c ^ 2)) (hsq c)
  have hcompΦ1 : ∀ c : ℂ,
      HasDerivAt (fun c : ℂ => deriv Φ (c ^ 2)) (deriv (deriv Φ) (c ^ 2) * (2 * c)) c := by
    intro c
    simpa [Function.comp_def] using HasDerivAt.comp c (hdiff1 (c ^ 2)) (hsq c)
  have hG : ∀ c : ℂ, c * Φ (c ^ 2) = Complex.sin ((Real.pi : ℂ) * c) / (Real.pi : ℂ) := by
    intro c
    rw [eq_div_iff hpi]
    linear_combination hs c
  have hfun : (fun c : ℂ => c * Φ (c ^ 2))
      = fun c : ℂ => Complex.sin ((Real.pi : ℂ) * c) / (Real.pi : ℂ) := funext hG
  have he1 : ∀ c : ℂ, HasDerivAt (fun c : ℂ => Complex.sin ((Real.pi : ℂ) * c) / (Real.pi : ℂ))
      (Complex.cos ((Real.pi : ℂ) * c)) c := by
    intro c
    have h := ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * c)).comp c (hlin c)).div_const
      ((Real.pi : ℂ))
    rwa [mul_div_assoc, div_self hpi, mul_one] at h
  have hd1 : ∀ c : ℂ, HasDerivAt (fun c : ℂ => c * Φ (c ^ 2))
      (1 * Φ (c ^ 2) + c * (deriv Φ (c ^ 2) * (2 * c))) c := by
    intro c
    exact (hasDerivAt_id c).mul (hcompΦ c)
  have hclean : ∀ c : ℂ, Φ (c ^ 2) + 2 * c ^ 2 * deriv Φ (c ^ 2)
      = Complex.cos ((Real.pi : ℂ) * c) := by
    intro c
    have h1 : (1 : ℂ) * Φ (c ^ 2) + c * (deriv Φ (c ^ 2) * (2 * c))
        = Complex.cos ((Real.pi : ℂ) * c) := by
      rw [← (hd1 c).deriv, ← (he1 c).deriv, hfun]
    linear_combination h1
  have hfun2 : (fun c : ℂ => Φ (c ^ 2) + 2 * c ^ 2 * deriv Φ (c ^ 2))
      = fun c : ℂ => Complex.cos ((Real.pi : ℂ) * c) := funext hclean
  have he2 : ∀ c : ℂ, HasDerivAt (fun c : ℂ => Complex.cos ((Real.pi : ℂ) * c))
      (-Complex.sin ((Real.pi : ℂ) * c) * (Real.pi : ℂ)) c := by
    intro c
    simpa [Function.comp_def] using
      HasDerivAt.comp c (Complex.hasDerivAt_cos ((Real.pi : ℂ) * c)) (hlin c)
  have hd2 : ∀ c : ℂ, HasDerivAt (fun c : ℂ => Φ (c ^ 2) + 2 * c ^ 2 * deriv Φ (c ^ 2))
      (deriv Φ (c ^ 2) * (2 * c)
        + (2 * (2 * c) * deriv Φ (c ^ 2)
          + 2 * c ^ 2 * (deriv (deriv Φ) (c ^ 2) * (2 * c)))) c := by
    intro c
    exact (hcompΦ c).add (((hsq c).const_mul (2 : ℂ)).mul (hcompΦ1 c))
  have hder2 : ∀ c : ℂ, deriv Φ (c ^ 2) * (2 * c)
      + (2 * (2 * c) * deriv Φ (c ^ 2)
        + 2 * c ^ 2 * (deriv (deriv Φ) (c ^ 2) * (2 * c)))
      = -Complex.sin ((Real.pi : ℂ) * c) * (Real.pi : ℂ) := by
    intro c
    rw [← (hd2 c).deriv, ← (he2 c).deriv, hfun2]
  have hsquare : ∀ c : ℂ, c * (4 * c ^ 2 * deriv (deriv Φ) (c ^ 2) + 6 * deriv Φ (c ^ 2)
      + (Real.pi : ℂ) ^ 2 * Φ (c ^ 2)) = 0 := by
    intro c
    linear_combination hder2 c + (Real.pi : ℂ) * hs c
  have hEoff : ∀ y : ℂ, y ≠ 0 →
      4 * y * deriv (deriv Φ) y + 6 * deriv Φ y + (Real.pi : ℂ) ^ 2 * Φ y = 0 := by
    intro y hy
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) y (n := 2) (by norm_num)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hc
      exact hy (by rw [← hc]; norm_num)
    have h := hsquare c
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hc0
    · rw [hc] at h0
      linear_combination h0
  have hEcont : Continuous (fun y : ℂ => 4 * y * deriv (deriv Φ) y + 6 * deriv Φ y
      + (Real.pi : ℂ) ^ 2 * Φ y) := by
    have c0 : Continuous Φ := by
      rw [← continuousOn_univ]
      exact hA.continuousOn
    have c1 : Continuous (deriv Φ) := by
      rw [← continuousOn_univ]
      exact hA1.continuousOn
    have c2 : Continuous (deriv (deriv Φ)) := by
      rw [← continuousOn_univ]
      exact hA2.continuousOn
    fun_prop
  have hall : (fun y : ℂ => 4 * y * deriv (deriv Φ) y + 6 * deriv Φ y
      + (Real.pi : ℂ) ^ 2 * Φ y) = fun _ : ℂ => 0 :=
    Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hEcont continuous_const
      (fun y hy => hEoff y (by simpa using hy))
  exact congrFun hall x

/-- **The second-order law at temperature two.** -/
theorem occupationProduct_two_ode (x : ℂ) :
    4 * x * deriv (deriv (occupationProduct 2)) x + 6 * deriv (occupationProduct 2) x
      + (Real.pi : ℂ) ^ 2 * occupationProduct 2 x = 0 :=
  ode_of_sin_square_law (analyticOnNhd_occupationProduct (by norm_num))
    pi_mul_occupationProduct_two x

/-! ## The Euler jet of a finite prime packet -/

/-- Reciprocal `k`-th powers as a multiplicative arithmetic weight. -/
def natPowInvHom (k : ℕ) : ℕ →* ℂ where
  toFun n := (((n : ℂ)) ^ k)⁻¹
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, mul_pow, mul_inv]

@[simp]
theorem natPowInvHom_apply (k n : ℕ) : natPowInvHom k n = (((n : ℂ)) ^ k)⁻¹ := rfl

theorem summable_natPowInvHom {k : ℕ} (hk : 2 ≤ k) : Summable (natPowInvHom k) := by
  rw [← summable_norm_iff]
  have hnorm : ∀ n : ℕ, ‖natPowInvHom k n‖ = 1 / ((n : ℝ)) ^ k := by
    intro n
    rw [natPowInvHom_apply, norm_inv, norm_pow, Complex.norm_natCast, one_div]
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ k) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  exact hbase.congr fun n => (hnorm n).symm

/-- **The occupation divisor sum of a finite prime packet.**  The sum of `n^{-k}` over the positive
integers built from the primes below `N`. -/
def smoothZetaSum (N k : ℕ) : ℂ := ∑' n : Nat.smoothNumbers N, (((n : ℕ) : ℂ) ^ k)⁻¹

/-- **The Euler factorization of the packet sum.**  The occupation divisor sum of a packet is the
finite Euler product over its primes. -/
theorem prod_primesBelow_eq_smoothZetaSum {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 - (((p : ℕ) : ℂ) ^ k)⁻¹)⁻¹ = smoothZetaSum N k :=
  EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers (summable_natPowInvHom hk) N

theorem tsum_natPowInvHom_eq_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    ∑' n : ℕ, (((n : ℂ)) ^ k)⁻¹ = riemannZeta (k : ℂ) := by
  have hre : 1 < ((k : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < k)
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  refine tsum_congr fun n => ?_
  rw [Complex.cpow_natCast, one_div]

/-- **Cofinal completion of the packet sum.**  As the packet exhausts the primes, the occupation
divisor sum converges to the zeta value. -/
theorem tendsto_smoothZetaSum {k : ℕ} (hk : 2 ≤ k) :
    Filter.Tendsto (fun N : ℕ => smoothZetaSum N k) Filter.atTop
      (nhds (riemannZeta (k : ℂ))) := by
  rw [← tsum_natPowInvHom_eq_riemannZeta hk]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt
    (f := fun n : ℕ => (((n : ℂ)) ^ k)⁻¹) (summable_natPowInvHom hk)
    (by simp [zero_pow (by omega : k ≠ 0)]) hε
  refine ⟨N₀, fun N hN => ?_⟩
  have h := hN₀ N hN
  rw [Complex.dist_eq, smoothZetaSum]
  rw [← norm_neg]
  simpa only [neg_sub] using h

/-- **The Euler boundary jet.**  The finite Euler product over the primes of a packet, at every
logarithmic level `m`, converges to the corresponding zeta value. -/
theorem tendsto_prod_primesBelow_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, (1 - (((p : ℕ) : ℂ) ^ k)⁻¹)⁻¹)
      Filter.atTop (nhds (riemannZeta (k : ℂ))) := by
  refine (tendsto_smoothZetaSum hk).congr fun N => ?_
  exact (prod_primesBelow_eq_smoothZetaSum hk N).symm

/-! ## The occupation product of a finite prime packet -/

/-- The centred factor of the completed occupation product. -/
def occFull (r : ℕ) (x : ℂ) (m : ℕ) : ℂ := if m = 0 then 0 else -(x / (m : ℂ) ^ r)

/-- The centred factor of the occupation product of the packet of primes below `N`. -/
def occSmooth (N r : ℕ) (x : ℂ) (m : ℕ) : ℂ :=
  if m ∈ Nat.smoothNumbers N then -(x / (m : ℂ) ^ r) else 0

theorem norm_occFull {r : ℕ} (x : ℂ) (m : ℕ) :
    ‖occFull r x m‖ = if m = 0 then 0 else ‖x‖ / ((m : ℝ)) ^ r := by
  rw [occFull]
  by_cases h : m = 0
  · simp [h]
  · rw [if_neg h, if_neg h, norm_neg, norm_div, norm_pow, Complex.norm_natCast]

theorem summable_norm_occFull {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    Summable (fun m : ℕ => ‖occFull r x m‖) := by
  have hbase : Summable (fun m : ℕ => ‖x‖ / ((m : ℝ)) ^ r) := by
    have h : Summable (fun m : ℕ => 1 / ((m : ℝ)) ^ r) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    have := h.mul_left ‖x‖
    refine this.congr fun m => ?_
    rw [mul_one_div]
  refine hbase.of_nonneg_of_le (fun m => norm_nonneg _) fun m => ?_
  rw [norm_occFull]
  by_cases h : m = 0
  · simp [h]
    positivity
  · rw [if_neg h]


theorem norm_occSmooth_le {N r : ℕ} (x : ℂ) (m : ℕ) :
    ‖occSmooth N r x m‖ ≤ ‖occFull r x m‖ := by
  rw [occSmooth, occFull]
  by_cases h : m ∈ Nat.smoothNumbers N
  · have h0 : m ≠ 0 := h.1
    rw [if_pos h, if_neg h0]
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

theorem summable_norm_occSmooth {N r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    Summable (fun m : ℕ => ‖occSmooth N r x m‖) :=
  (summable_norm_occFull hr x).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => norm_occSmooth_le x m)

/-- The occupation product of the packet of primes below `N`. -/
def smoothOccupationProduct (N r : ℕ) (x : ℂ) : ℂ := ∏' m : ℕ, (1 + occSmooth N r x m)

theorem hasProd_occFull {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    HasProd (fun m : ℕ => 1 + occFull r x m) (occupationProduct r x) := by
  have hinj : Function.Injective (fun n : ℕ => n + 1) := fun a b h => by simpa using h
  have hout : ∀ m ∉ Set.range (fun n : ℕ => n + 1), (1 : ℂ) + occFull r x m = 1 := by
    intro m hm
    have hm0 : m = 0 := by
      by_contra h
      refine hm ⟨m - 1, ?_⟩
      show m - 1 + 1 = m
      omega
    rw [hm0, occFull, if_pos rfl, add_zero]
  refine (hinj.hasProd_iff hout).mp ?_
  have hbase := hasProd_occupationProduct hr x
  refine hbase.congr_fun fun n => ?_
  have hne : (n + 1 : ℕ) ≠ 0 := by omega
  simp only [Function.comp_apply, occFull, if_neg hne]
  push_cast
  ring

theorem occupationProduct_eq_tprod {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    occupationProduct r x = ∏' m : ℕ, (1 + occFull r x m) := (hasProd_occFull hr x).tprod_eq.symm

/-- **Cofinal completion of the occupation product.**  As the prime packet exhausts the primes,
its occupation product converges to the completed product. -/
theorem tendsto_smoothOccupationProduct {r : ℕ} (hr : 2 ≤ r) (x : ℂ) :
    Tendsto (fun N : ℕ => smoothOccupationProduct N r x) atTop
      (nhds (occupationProduct r x)) := by
  classical
  set w : ℕ → ℝ := fun m => ‖occFull r x m‖ with hwdef
  have hw : Summable w := summable_norm_occFull hr x
  have hw0 : w 0 = 0 := by rw [hwdef]; simp [occFull]
  have hwnn : ∀ m, 0 ≤ w m := fun m => norm_nonneg _
  set M : ℝ := ∑' m : ℕ, w m with hMdef
  have hkey : ∀ N : ℕ, ‖occupationProduct r x - smoothOccupationProduct N r x‖
      ≤ (∑' m : ℕ, ‖occFull r x m - occSmooth N r x m‖) * Real.exp (2 * M) := by
    intro N
    have hb := GaloisForLFunctions.HTGeometry.norm_tprod_one_add_sub_tprod_one_add_le (occFull r x) (occSmooth N r x)
      (summable_norm_occFull hr x) (summable_norm_occSmooth hr x)
    rw [← occupationProduct_eq_tprod hr x] at hb
    refine hb.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun m => norm_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    have hsum : ∑' m : ℕ, (‖occFull r x m‖ + ‖occSmooth N r x m‖)
        ≤ ∑' m : ℕ, (2 * w m) := by
      refine Summable.tsum_le_tsum (fun m => ?_) ((summable_norm_occFull hr x).add
        (summable_norm_occSmooth hr x)) (hw.mul_left 2)
      have hle := norm_occSmooth_le (N := N) (r := r) x m
      rw [hwdef]
      linarith
    rw [tsum_mul_left] at hsum
    rw [hMdef]
    linarith
  have hdiff : ∀ N : ℕ, ∑' m : ℕ, ‖occFull r x m - occSmooth N r x m‖
      = ∑' m : ℕ, w m - ∑' m : Nat.smoothNumbers N, w m := by
    intro N
    have hpt : ∀ m : ℕ, ‖occFull r x m - occSmooth N r x m‖
        = (Nat.smoothNumbers N)ᶜ.indicator w m := by
      intro m
      by_cases h : m ∈ Nat.smoothNumbers N
      · have h0 : m ≠ 0 := h.1
        rw [occSmooth, if_pos h, occFull, if_neg h0, sub_self, norm_zero,
          Set.indicator_of_notMem (by simpa using h)]
      · rw [occSmooth, if_neg h, sub_zero, Set.indicator_of_mem (by simpa using h), hwdef]
    rw [tsum_congr hpt, ← tsum_subtype]
    have hsplit : (∑' m : Nat.smoothNumbers N, w m) + (∑' m : ↥((Nat.smoothNumbers N)ᶜ), w m)
        = ∑' m : ℕ, w m :=
      Summable.tsum_add_tsum_compl (hw.subtype _) (hw.subtype _)
    linarith
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hEpos : (0 : ℝ) < Real.exp (2 * M) := Real.exp_pos _
  obtain ⟨N₀, hN₀⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt (f := w) hw hw0
    (show (0 : ℝ) < ε / Real.exp (2 * M) by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := hN₀ N hN
  have h2 := hkey N
  rw [hdiff N] at h2
  rw [Complex.dist_eq]
  have h3 : ∑' m : ℕ, w m - ∑' m : Nat.smoothNumbers N, w m < ε / Real.exp (2 * M) :=
    lt_of_abs_lt (by simpa [Real.norm_eq_abs] using h1)
  calc ‖smoothOccupationProduct N r x - occupationProduct r x‖
      = ‖occupationProduct r x - smoothOccupationProduct N r x‖ := norm_sub_rev _ _
    _ ≤ (∑' m : ℕ, w m - ∑' m : Nat.smoothNumbers N, w m) * Real.exp (2 * M) := h2
    _ < (ε / Real.exp (2 * M)) * Real.exp (2 * M) := by
        exact mul_lt_mul_of_pos_right h3 hEpos
    _ = ε := by field_simp

/-! ## Unique factorization of the occupation monoid -/

/-- **Occupation vectors are exactly the prime-supported exponent functions.** -/
def occupationEquivPrimeSupported :
    (Nat.Primes →₀ ℕ) ≃ {f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p} where
  toFun ν := ⟨Finsupp.extendDomain ν, by
    intro p hp
    exact Finsupp.support_extendDomain_subset (P := fun n => Nat.Prime n) ν hp⟩
  invFun f := Finsupp.subtypeDomain (fun n => Nat.Prime n) (f : ℕ →₀ ℕ)
  left_inv ν := Finsupp.subtypeDomain_extendDomain ν
  right_inv f := Subtype.ext (Finsupp.extendDomain_subtypeDomain (f : ℕ →₀ ℕ) f.2)

/-- **Unique factorization.**  The occupation monoid of the primes is the positive integers. -/
def occupationEquivPNat : (Nat.Primes →₀ ℕ) ≃ ℕ+ :=
  occupationEquivPrimeSupported.trans Nat.factorizationEquiv.symm

theorem occupationEquivPNat_coe (ν : Nat.Primes →₀ ℕ) :
    ((occupationEquivPNat ν : ℕ+) : ℕ)
      = (Finsupp.extendDomain (P := fun n => Nat.Prime n) ν).prod fun n k => n ^ k := by
  rw [occupationEquivPNat, Equiv.trans_apply]
  exact Nat.factorizationEquiv_symm_apply_coe (occupationEquivPrimeSupported ν)

theorem occupationEquivPNat_ne_zero (ν : Nat.Primes →₀ ℕ) :
    ((occupationEquivPNat ν : ℕ+) : ℕ) ≠ 0 := (occupationEquivPNat ν).ne_zero

end

end HTGeometry
