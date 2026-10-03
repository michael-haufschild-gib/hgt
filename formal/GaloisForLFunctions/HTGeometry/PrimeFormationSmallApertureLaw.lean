import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.HTGeometry.PrimePoissonFormationFrame

/-!
# The small-aperture limit of the prime formation law

The prime formation law is `μ_d(p) = u_d(p)/U_d` with `u_d(p) = 8d log(p) p^{-(1+2d)}` and
`U_d = Σ_p u_d(p)`.  As `d → 0+` the law, read in the logarithmic coordinate `y = d log p`,
converges to the exponential law `2e^{-2y} dy`:

`μ_d{p : a ≤ d log p ≤ b} → 2 ∫_a^b e^{-2y} dy`  for `0 < a < b`.

The mechanism is Abel summation against the Chebyshev function `θ` with the weight
`f(t) = t^{-(1+2d)}`.  The prime number theorem `θ(t) ~ t` turns the window sum
`Σ_{X < p ≤ Y} log(p) p^{-(1+2d)}` into `∫_X^Y t^{-(1+2d)} dt = (X^{-2d} - Y^{-2d})/(2d)` up to
`ε` times the same kernel mass, uniformly in `d`.  With `X = e^{a/d}`, `Y = e^{b/d}` this gives
`(e^{-2a} - e^{-2b})/(2d)`, and the same estimate on `(T₀, ∞)` gives `d Σ_p log(p) p^{-(1+2d)} → 1/2`,
i.e. `U_d → 4`.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ϑw" => RHTower.primeLogWeight_primeRpowAbelSummation

/-! ## The uniform window estimate -/

/-- The aperture window sum `Σ_{X < n ≤ Y} n^{-(1+2d)} log n` over primes `n`. -/
def apertureWindowSum (d X Y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, (k : ℝ) ^ (-(1 + 2 * d)) * ϑw k

/-- `∫_X^Y t^{-(1+2d)} dt = (X^{-2d} - Y^{-2d})/(2d)`. -/
theorem integral_Ioc_rpow_aperture {d X Y : ℝ} (hd : 0 < d) (hX : 0 < X) (hXY : X ≤ Y) :
    ∫ t in Ioc X Y, t ^ (-(1 + 2 * d)) = (X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d) := by
  rw [← intervalIntegral.integral_of_le hXY, integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
  · rw [show -(1 + 2 * d) + 1 = -2 * d by ring]
    field_simp
    ring
  · rw [uIcc_of_le hXY]
    exact fun h => absurd h.1 (not_le.2 hX)

theorem integrableOn_Ioc_rpow_aperture {d X Y : ℝ} (c : ℝ) (hX : 0 < X) :
    IntegrableOn (fun t : ℝ => c * t ^ (-(1 + 2 * d))) (Ioc X Y) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  exact continuousOn_const.mul
    (continuousOn_id.rpow_const fun t ht => Or.inl (by simp only [id]; linarith [ht.1]))

/-- **The uniform window estimate.**  For every `ε > 0` there is `T₀` such that for all
`d > 0` and `T₀ ≤ X ≤ Y`,
`|Σ_{X<p≤Y} log(p) p^{-(1+2d)} - (X^{-2d}-Y^{-2d})/(2d)|
  ≤ ε (X^{-2d} + Y^{-2d} + (1+2d)(X^{-2d}-Y^{-2d})/(2d))`. -/
theorem abs_apertureWindowSum_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ d : ℝ, 0 < d → ∀ X Y : ℝ, T₀ ≤ X → X ≤ Y →
      |apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)| ≤
        ε * (X ^ (-2 * d) + Y ^ (-2 * d) +
          (1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d))) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (chebyshev_asymptotic.isLittleO.bound hε)
  refine ⟨max T 1, le_max_right _ _, fun d hd X Y hX hXY => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hθ : ∀ t, X ≤ t → |Chebyshev.theta t - t| ≤ ε * t := fun t ht => by
    have h := hT t (le_trans (le_max_left _ _) (hX.trans ht))
    simpa [Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)] using h
  set r : ℝ := -(1 + 2 * d) with hr
  have hr1 : r + 1 = -2 * d := by rw [hr]; ring
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => s ^ r) (r * t ^ (r - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hgcont : ContinuousOn (fun t : ℝ => r * t ^ (r - 1)) (Icc X Y) :=
    continuousOn_const.mul
      (continuousOn_id.rpow_const fun t ht => Or.inl (by simp only [id]; linarith [ht.1]))
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) ϑw (f := fun s : ℝ => s ^ r)
    (a := X) (b := Y) hX0.le hXY
    (fun t ht => (hderiv t (by linarith [ht.1])).differentiableAt)
    (hgcont.integrableOn_Icc.congr_fun (fun t ht => (hderiv t (by linarith [ht.1])).deriv.symm)
      measurableSet_Icc)
  simp only [RHTower.sum_primeLogWeight_eq_theta] at habel
  -- the integral against `θ`, split into the kernel mass and the PNT error
  have hθint : IntegrableOn Chebyshev.theta (Icc X Y) :=
    (Chebyshev.theta_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hgθ : IntegrableOn (fun t => r * t ^ (r - 1) * Chebyshev.theta t) (Ioc X Y) :=
    (hθint.continuousOn_mul hgcont isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hgt : IntegrableOn (fun t : ℝ => r * t ^ (r - 1) * t) (Ioc X Y) :=
    ((hgcont.mul continuousOn_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hkernel : ∀ t ∈ Ioc X Y, r * t ^ (r - 1) * t = r * t ^ r := fun t ht => by
    rw [Real.rpow_sub_one (by linarith [ht.1] : t ≠ 0)]
    field_simp [(by linarith [ht.1] : t ≠ 0)]
  have hI : ∫ t in Ioc X Y, deriv (fun s : ℝ => s ^ r) t * Chebyshev.theta t =
      r * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)) +
        ∫ t in Ioc X Y, r * t ^ (r - 1) * (Chebyshev.theta t - t) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t => r * t ^ (r - 1) * t +
      r * t ^ (r - 1) * (Chebyshev.theta t - t)) fun t ht => by
        simp only
        rw [(hderiv t (by linarith [ht.1])).deriv]
        ring]
    rw [integral_add hgt (hgθ.sub hgt |>.congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioc), setIntegral_congr_fun measurableSet_Ioc hkernel, integral_const_mul,
      integral_Ioc_rpow_aperture hd hX0 hXY]
  have hE3 : |∫ t in Ioc X Y, r * t ^ (r - 1) * (Chebyshev.theta t - t)| ≤
      ε * ((1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d))) := by
    have hbound : ∫ t in Ioc X Y, (ε * (1 + 2 * d)) * t ^ r =
        ε * ((1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d))) := by
      rw [integral_const_mul, integral_Ioc_rpow_aperture hd hX0 hXY]
      ring
    rw [← hbound, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (integrableOn_Ioc_rpow_aperture _ hX0) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := by linarith [ht.1]
    have htr : 0 < t ^ (r - 1) := Real.rpow_pos_of_pos ht0 _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_neg (by rw [hr]; linarith : r < 0), abs_of_pos htr]
    calc -r * t ^ (r - 1) * |Chebyshev.theta t - t| ≤ -r * t ^ (r - 1) * (ε * t) := by
          have hnr : 0 < -r := by rw [hr]; linarith
          exact mul_le_mul_of_nonneg_left (hθ t ht.1.le) (mul_pos hnr htr).le
      _ = ε * (1 + 2 * d) * (r * t ^ (r - 1) * t) / r := by
          field_simp [(by rw [hr]; linarith : r ≠ 0)]
          rw [hr]
          ring
      _ = ε * (1 + 2 * d) * t ^ r := by
          rw [hkernel t ht]
          field_simp [(by rw [hr]; linarith : r ≠ 0)]
  -- the two endpoint terms
  have hend : ∀ Z : ℝ, X ≤ Z → |Z ^ r * (Chebyshev.theta Z - Z)| ≤ ε * Z ^ (-2 * d) := fun Z hZ => by
    have hZ0 : 0 < Z := by linarith
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hZ0 _), ← hr1, Real.rpow_add_one hZ0.ne']
    calc Z ^ r * |Chebyshev.theta Z - Z| ≤ Z ^ r * (ε * Z) :=
          mul_le_mul_of_nonneg_left (hθ Z hZ) (Real.rpow_pos_of_pos hZ0 _).le
      _ = ε * (Z ^ r * Z) := by ring
  have hpow : ∀ Z : ℝ, 0 < Z → Z ^ r * Z = Z ^ (-2 * d) := fun Z hZ => by
    rw [← hr1, Real.rpow_add_one hZ.ne']
  have hsum : apertureWindowSum d X Y = Y ^ r * Chebyshev.theta Y - X ^ r * Chebyshev.theta X -
      ∫ t in Ioc X Y, deriv (fun s : ℝ => s ^ r) t * Chebyshev.theta t := habel
  have h1 := abs_le.1 (hend Y hXY)
  have h2 := abs_le.1 (hend X le_rfl)
  have h3 := abs_le.1 hE3
  have hd2 : (2 * d) ≠ 0 := by positivity
  have hmain : apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d) =
      Y ^ r * (Chebyshev.theta Y - Y) - X ^ r * (Chebyshev.theta X - X) -
        ∫ t in Ioc X Y, r * t ^ (r - 1) * (Chebyshev.theta t - t) := by
    rw [hsum, hI]
    have hY := hpow Y hY0
    have hX' := hpow X hX0
    have hrr : r * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)) =
        -(1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)) := by rw [hr]
    have hsplit : ∀ Z : ℝ, Z ^ r * Chebyshev.theta Z = Z ^ r * Z + Z ^ r * (Chebyshev.theta Z - Z) :=
      fun Z => by ring
    rw [hsplit Y, hsplit X, hY, hX', hrr]
    field_simp
    ring
  rw [hmain, abs_le]
  constructor <;> nlinarith

/-- Multiplied by `d`, the window estimate is uniform: for `0 < d ≤ 1/3` and `T₀ ≤ X ≤ Y`,
`|d Σ_{X<p≤Y} log(p) p^{-(1+2d)} - (X^{-2d}-Y^{-2d})/2| ≤ 2ε`. -/
theorem abs_mul_apertureWindowSum_sub_le {ε T₀ : ℝ} (hε : 0 < ε) (hT₀ : 1 ≤ T₀)
    (hwin : ∀ d : ℝ, 0 < d → ∀ X Y : ℝ, T₀ ≤ X → X ≤ Y →
      |apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)| ≤
        ε * (X ^ (-2 * d) + Y ^ (-2 * d) +
          (1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d))))
    {d X Y : ℝ} (hd : 0 < d) (hd3 : d ≤ 1 / 3) (hX : T₀ ≤ X) (hXY : X ≤ Y) :
    |d * apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / 2| ≤ 2 * ε := by
  have h := hwin d hd X Y hX hXY
  have hX1 : 1 ≤ X := hT₀.trans hX
  have hu1 : X ^ (-2 * d) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  have hv1 : Y ^ (-2 * d) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hX1.trans hXY) (by linarith)
  have hv0 : 0 < Y ^ (-2 * d) := Real.rpow_pos_of_pos (by linarith) _
  have hvu : Y ^ (-2 * d) ≤ X ^ (-2 * d) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hXY (by linarith)
  have hkey : d * apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / 2 =
      d * (apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)) := by
    field_simp
  have hmass : d * (ε * (X ^ (-2 * d) + Y ^ (-2 * d) +
      (1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)))) =
      ε * (d * X ^ (-2 * d) + d * Y ^ (-2 * d) +
        (1 + 2 * d) * (X ^ (-2 * d) - Y ^ (-2 * d)) / 2) := by
    field_simp
  rw [hkey, abs_mul, abs_of_pos hd]
  calc d * |apertureWindowSum d X Y - (X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)|
      ≤ d * (ε * (X ^ (-2 * d) + Y ^ (-2 * d) +
          (1 + 2 * d) * ((X ^ (-2 * d) - Y ^ (-2 * d)) / (2 * d)))) :=
        mul_le_mul_of_nonneg_left h hd.le
    _ = ε * (d * X ^ (-2 * d) + d * Y ^ (-2 * d) +
          (1 + 2 * d) * (X ^ (-2 * d) - Y ^ (-2 * d)) / 2) := hmass
    _ ≤ ε * 2 := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        nlinarith
    _ = 2 * ε := by ring

/-! ## The aperture current -/

/-- The aperture Dirichlet term `n^{-(1+2d)} log n` on primes, `0` elsewhere. -/
def apertureDirichletTerm (d : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 + 2 * d)) * ϑw n

theorem primeLogWeight_primeRpowAbelSummation_nonneg (n : ℕ) : 0 ≤ ϑw n := by
  unfold RHTower.primeLogWeight_primeRpowAbelSummation
  split_ifs
  · exact Real.log_natCast_nonneg n
  · exact le_rfl

theorem apertureDirichletTerm_nonneg (d : ℝ) (n : ℕ) : 0 ≤ apertureDirichletTerm d n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (primeLogWeight_primeRpowAbelSummation_nonneg n)

theorem apertureDirichletTerm_le {d : ℝ} (hd : 0 ≤ d) (n : ℕ) : apertureDirichletTerm d n ≤ ϑw n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [apertureDirichletTerm, RHTower.primeLogWeight_primeRpowAbelSummation, Nat.not_prime_zero]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_le_of_le_one_left (primeLogWeight_primeRpowAbelSummation_nonneg n)
      (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))

theorem apertureDirichletTerm_prime (d : ℝ) (p : Nat.Primes) :
    apertureDirichletTerm d p = Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)) := by
  rw [apertureDirichletTerm, RHTower.primeLogWeight_primeRpowAbelSummation, if_pos p.property, mul_comm]

theorem apertureDirichletTerm_eq_zero_of_not_mem {d : ℝ} {n : ℕ}
    (hn : n ∉ Set.range ((↑) : Nat.Primes → ℕ)) : apertureDirichletTerm d n = 0 := by
  have : ¬ n.Prime := fun h => hn ⟨⟨n, h⟩, rfl⟩
  simp [apertureDirichletTerm, RHTower.primeLogWeight_primeRpowAbelSummation, this]

/-- The Stokes prime term `u_d(p)` is `8d` times the aperture term. -/
theorem stokesPrimeTerm_eq_apertureDirichletTerm {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d p = 8 * d * apertureDirichletTerm d p := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, xiMassPrimeSquareEulerWeight_eq,
    abs_of_pos hd, apertureDirichletTerm_prime]

theorem summable_apertureDirichletTerm {d : ℝ} (hd : 0 < d) : Summable (apertureDirichletTerm d) := by
  have hs := summable_gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d
  have h8 : (8 * d) ≠ 0 := by positivity
  have hcomp : Summable (apertureDirichletTerm d ∘ ((↑) : Nat.Primes → ℕ)) := by
    refine (hs.div_const (8 * d)).congr fun p => ?_
    simp only [Function.comp, stokesPrimeTerm_eq_apertureDirichletTerm hd]
    field_simp
  exact (Function.Injective.summable_iff Subtype.val_injective
    fun n hn => apertureDirichletTerm_eq_zero_of_not_mem hn).1 hcomp

/-- `U_d = 8d Σ_n n^{-(1+2d)} log n`. -/
theorem apertureCurrent_eq {d : ℝ} (hd : 0 < d) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d = 8 * d * ∑' n, apertureDirichletTerm d n := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent]
  simp_rw [stokesPrimeTerm_eq_apertureDirichletTerm hd]
  rw [tsum_mul_left]
  congr 1
  exact Function.Injective.tsum_eq Subtype.val_injective (f := apertureDirichletTerm d) fun n hn => by
    by_contra h
    exact hn (apertureDirichletTerm_eq_zero_of_not_mem h)

theorem apertureWindowSum_natCast (d : ℝ) {N₀ N : ℕ} (h : N₀ ≤ N) (T : ℝ) (hT : ⌊T⌋₊ = N₀) :
    apertureWindowSum d T N =
      ∑ k ∈ Finset.range (N + 1), apertureDirichletTerm d k - ∑ k ∈ Finset.range (N₀ + 1), apertureDirichletTerm d k := by
  rw [apertureWindowSum, hT, Nat.floor_natCast, ← Finset.Ico_add_one_add_one_eq_Ioc,
    Finset.sum_Ico_eq_sub _ (by omega)]
  rfl

/-- **The aperture current is asymptotically `4`:** `d Σ_p log(p) p^{-(1+2d)} → 1/2`. -/
theorem tendsto_mul_tsum_apertureDirichletTerm :
    Tendsto (fun d => d * ∑' n, apertureDirichletTerm d n) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀1, hT₀⟩ := abs_apertureWindowSum_sub_le (ε := ε / 8) (by positivity)
  set N₀ := ⌊T₀⌋₊ with hN₀
  set C₀ := ∑ k ∈ Finset.range (N₀ + 1), ϑw k
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun k _ => primeLogWeight_primeRpowAbelSummation_nonneg k
  have hcont : Tendsto (fun d : ℝ => T₀ ^ (-2 * d)) (𝓝 0) (𝓝 1) := by
    have h : Continuous fun d : ℝ => T₀ ^ (-2 * d) :=
      (Real.continuous_const_rpow (by linarith : T₀ ≠ 0)).comp (continuous_const_mul (-2))
    simpa using h.tendsto 0
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhds_nhds.1 hcont (ε / 4) (by positivity)
  refine ⟨min (min δ₁ (1 / 3)) (ε / (4 * (C₀ + 1))), by positivity, fun d hd hdist => ?_⟩
  have hd0 : 0 < d := hd
  rw [Real.dist_eq, sub_zero, abs_of_pos hd0] at hdist
  have hdδ : d < δ₁ := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_left _ _))
  have hd3 : d ≤ 1 / 3 := (lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_right _ _))).le
  have hdC : d < ε / (4 * (C₀ + 1)) := lt_of_lt_of_le hdist (min_le_right _ _)
  -- the tail of the current on `(T₀, ∞)`
  set u := T₀ ^ (-2 * d)
  set tail := ∑' n, apertureDirichletTerm d n - ∑ k ∈ Finset.range (N₀ + 1), apertureDirichletTerm d k
  have htail : |d * tail - u / 2| ≤ 2 * (ε / 8) := by
    have hlim : Tendsto (fun N : ℕ => |d * (∑ k ∈ Finset.range (N + 1), apertureDirichletTerm d k -
        ∑ k ∈ Finset.range (N₀ + 1), apertureDirichletTerm d k) - (u - (N : ℝ) ^ (-2 * d)) / 2|)
        atTop (𝓝 (|d * tail - (u - 0) / 2|)) := by
      have hS := ((summable_apertureDirichletTerm hd0).tendsto_sum_tsum_nat.comp (tendsto_add_atTop_nat 1))
      have hv : Tendsto (fun N : ℕ => (N : ℝ) ^ (-2 * d)) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < 2 * d)).comp
          tendsto_natCast_atTop_atTop
        simpa only [Function.comp_def, neg_mul] using h
      exact (((hS.sub_const _).const_mul d).sub ((tendsto_const_nhds.sub hv).div_const 2)).abs
    rw [sub_zero] at hlim
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨max N₀ ⌈T₀⌉₊, fun N hN => ?_⟩)
    have hN₀N : N₀ ≤ N := (le_max_left _ _).trans hN
    have hTN : T₀ ≤ (N : ℝ) := Nat.ceil_le.1 ((le_max_right _ _).trans hN)
    rw [← apertureWindowSum_natCast d hN₀N T₀ hN₀.symm]
    exact abs_mul_apertureWindowSum_sub_le (by positivity) hT₀1 hT₀ hd0 hd3 le_rfl hTN
  -- the head on `[0, T₀]`
  have hhead0 : 0 ≤ d * ∑ k ∈ Finset.range (N₀ + 1), apertureDirichletTerm d k :=
    mul_nonneg hd0.le (Finset.sum_nonneg fun k _ => apertureDirichletTerm_nonneg d k)
  have hhead : d * ∑ k ∈ Finset.range (N₀ + 1), apertureDirichletTerm d k ≤ d * C₀ :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => apertureDirichletTerm_le hd0.le k) hd0.le
  have hdC' : d * C₀ ≤ ε / 4 := by
    have h1 : d * (C₀ + 1) < ε / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hdC
      linarith
    nlinarith
  have hu : |u - 1| < ε / 4 := by
    have h := hδ₁' (x := d) (by rw [Real.dist_eq, sub_zero, abs_of_pos hd0]; exact hdδ)
    rwa [Real.dist_eq] at h
  rw [Real.dist_eq]
  have hsplit : d * ∑' n, apertureDirichletTerm d n - 1 / 2 =
      d * ∑ k ∈ Finset.range (N₀ + 1), apertureDirichletTerm d k + (d * tail - u / 2) + (u - 1) / 2 := by
    simp only [tail]
    ring
  rw [hsplit]
  have h1 := abs_le.1 htail
  have h2 := abs_lt.1 hu
  rw [abs_lt]
  constructor <;> linarith

/-- **The Stokes current converges:** `U_d → 4` as `d → 0+`. -/
theorem tendsto_apertureCurrent :
    Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (𝓝[>] 0) (𝓝 4) := by
  have h := tendsto_mul_tsum_apertureDirichletTerm.const_mul 8
  rw [show (8 : ℝ) * (1 / 2) = 4 by norm_num] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun d hd => ?_)
  rw [apertureCurrent_eq hd]
  ring

/-! ## Window masses -/

/-- The `μ_d`-mass of the logarithmic window `a < d log p ≤ b`. -/
def primeFormationWindowMass (d a b : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Set.indicator {p : Nat.Primes | a < d * Real.log p ∧ d * Real.log p ≤ b}
    (primeFormationLaw d) p

/-- The `μ_d`-mass of the closed logarithmic window `a ≤ d log p ≤ b`. -/
def primeFormationClosedWindowMass (d a b : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Set.indicator {p : Nat.Primes | a ≤ d * Real.log p ∧ d * Real.log p ≤ b}
    (primeFormationLaw d) p

theorem primeFormationLaw_eq_apertureDirichletTerm {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    primeFormationLaw d p =
      8 * d * apertureDirichletTerm d p / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [primeFormationLaw, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd,
    stokesPrimeTerm_eq_apertureDirichletTerm hd]

theorem mem_window_iff {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (n : ℕ) :
    (a < d * Real.log n ∧ d * Real.log n ≤ b) ↔
      n ∈ Finset.Ioc ⌊Real.exp (a / d)⌋₊ ⌊Real.exp (b / d)⌋₊ := by
  rw [Finset.mem_Ioc, Nat.floor_lt (Real.exp_pos _).le, Nat.le_floor_iff (Real.exp_pos _).le]
  constructor
  · rintro ⟨h1, h2⟩
    have hn : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at h1; linarith
      · exact_mod_cast hn
    refine ⟨(Real.lt_log_iff_exp_lt hn).1 ?_, (Real.log_le_iff_le_exp hn).1 ?_⟩
    · rw [div_lt_iff₀ hd]; linarith
    · rw [le_div_iff₀ hd]; linarith
  · rintro ⟨h1, h2⟩
    have hn : (0 : ℝ) < n := (Real.exp_pos _).trans h1
    have h1' := (Real.lt_log_iff_exp_lt hn).2 h1
    have h2' := (Real.log_le_iff_le_exp hn).2 h2
    rw [div_lt_iff₀ hd] at h1'
    rw [le_div_iff₀ hd] at h2'
    constructor <;> linarith

/-- The half-open window mass is a normalized aperture window sum. -/
theorem primeFormationWindowMass_eq {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) :
    primeFormationWindowMass d a b =
      8 * (d * apertureWindowSum d (Real.exp (a / d)) (Real.exp (b / d))) /
        (8 * (d * ∑' n, apertureDirichletTerm d n)) := by
  set G : ℕ → ℝ := fun n => if a < d * Real.log n ∧ d * Real.log n ≤ b then apertureDirichletTerm d n else 0
  have hU := apertureCurrent_eq hd
  have hcomp : ∀ p : Nat.Primes, Set.indicator
      {p : Nat.Primes | a < d * Real.log p ∧ d * Real.log p ≤ b} (primeFormationLaw d) p =
      8 * d / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d * G p := fun p => by
    simp only [Set.indicator_apply, Set.mem_setOf_eq, G]
    split_ifs
    · rw [primeFormationLaw_eq_apertureDirichletTerm hd]
      ring
    · ring
  have htr : ∑' p : Nat.Primes, G p = ∑' n, G n :=
    Function.Injective.tsum_eq Nat.Primes.coe_nat_injective (f := G) fun n hn => by
      by_contra h
      apply hn
      simp only [G]
      split_ifs <;> simp [apertureDirichletTerm_eq_zero_of_not_mem h]
  rw [primeFormationWindowMass, tsum_congr hcomp, tsum_mul_left, htr,
    tsum_eq_sum (s := Finset.Ioc ⌊Real.exp (a / d)⌋₊ ⌊Real.exp (b / d)⌋₊) fun n hn => by
      simp only [G]
      rw [if_neg fun h => hn ((mem_window_iff hd ha n).1 h)]]
  have hsum : ∑ n ∈ Finset.Ioc ⌊Real.exp (a / d)⌋₊ ⌊Real.exp (b / d)⌋₊, G n =
      apertureWindowSum d (Real.exp (a / d)) (Real.exp (b / d)) :=
    Finset.sum_congr rfl fun n hn => by
      simp only [G]
      rw [if_pos ((mem_window_iff hd ha n).2 hn)]
      rfl
  rw [hsum, hU]
  ring

/-- `2 ∫_a^b e^{-2y} dy = e^{-2a} - e^{-2b}`. -/
theorem two_mul_integral_exp_neg_two (a b : ℝ) :
    2 * ∫ y in a..b, Real.exp (-2 * y) = Real.exp (-2 * a) - Real.exp (-2 * b) := by
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.exp y) (by norm_num : (-2 : ℝ) ≠ 0),
    integral_exp, smul_eq_mul]
  ring

/-- The aperture window sum on `(e^{a/d}, e^{b/d}]` converges after multiplication by `d`. -/
theorem tendsto_mul_apertureWindowSum_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun d => d * apertureWindowSum d (Real.exp (a / d)) (Real.exp (b / d))) (𝓝[>] 0)
      (𝓝 ((Real.exp (-2 * a) - Real.exp (-2 * b)) / 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀1, hT₀⟩ := abs_apertureWindowSum_sub_le (ε := ε / 4) (by positivity)
  have hX : Tendsto (fun d : ℝ => Real.exp (a / d)) (𝓝[>] 0) atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    exact (tendsto_inv_nhdsGT_zero.const_mul_atTop ha).congr fun d => (div_eq_mul_inv a d).symm
  have h3 : ∀ᶠ d : ℝ in 𝓝[>] 0, d < 1 / 3 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num))
  filter_upwards [hX.eventually_ge_atTop T₀, h3, self_mem_nhdsWithin] with d hXd hd3 hd0
  have hd0' : (0 : ℝ) < d := hd0
  have hexp : ∀ c : ℝ, Real.exp (c / d) ^ (-2 * d) = Real.exp (-2 * c) := fun c => by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hXY : Real.exp (a / d) ≤ Real.exp (b / d) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right hab hd0'.le)
  have h := abs_mul_apertureWindowSum_sub_le (by positivity) hT₀1 hT₀ hd0' hd3.le hXd hXY
  rw [hexp, hexp] at h
  rw [Real.dist_eq]
  linarith

/-- **(PCOB.27) The small-aperture law, half-open windows.**  For `0 < a ≤ b`,
`μ_d{p : a < d log p ≤ b} → 2 ∫_a^b e^{-2y} dy` as `d → 0+`. -/
theorem tendsto_primeFormationWindowMass {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun d => primeFormationWindowMass d a b) (𝓝[>] 0)
      (𝓝 (2 * ∫ y in a..b, Real.exp (-2 * y))) := by
  rw [two_mul_integral_exp_neg_two]
  have h := ((tendsto_mul_apertureWindowSum_exp ha hab).const_mul 8).div
    (tendsto_mul_tsum_apertureDirichletTerm.const_mul 8) (by norm_num)
  rw [show 8 * ((Real.exp (-2 * a) - Real.exp (-2 * b)) / 2) / (8 * (1 / 2)) =
    Real.exp (-2 * a) - Real.exp (-2 * b) by ring] at h
  exact h.congr' (eventually_nhdsWithin_of_forall fun d hd =>
    (primeFormationWindowMass_eq hd ha.le).symm)

theorem summable_primeFormationLaw_indicator {d : ℝ} (hd : 0 < d) (s : Set Nat.Primes) :
    Summable (s.indicator (primeFormationLaw d)) :=
  (hasSum_primeFormationLaw hd).summable.indicator s

theorem primeFormationLaw_nonneg' {d : ℝ} (hd : 0 < d) : 0 ≤ primeFormationLaw d :=
  fun p => (primeFormationLaw_pos hd p).le

/-- **(PCOB.27) The small-aperture law.**  For `0 < a ≤ b`,
`μ_d{p : a ≤ d log p ≤ b} → 2 ∫_a^b e^{-2y} dy` as `d → 0+`. -/
theorem tendsto_primeFormationClosedWindowMass {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun d => primeFormationClosedWindowMass d a b) (𝓝[>] 0)
      (𝓝 (2 * ∫ y in a..b, Real.exp (-2 * y))) := by
  have hmono : ∀ {d a' : ℝ}, 0 < d → a' ≤ a →
      primeFormationWindowMass d a b ≤ primeFormationClosedWindowMass d a b ∧
        (a' < a → primeFormationClosedWindowMass d a b ≤ primeFormationWindowMass d a' b) :=
    fun {d a'} hd ha' => by
      refine ⟨Summable.tsum_le_tsum (Set.indicator_le_indicator_of_subset
          (fun p hp => ⟨hp.1.le, hp.2⟩) (primeFormationLaw_nonneg' hd))
          (summable_primeFormationLaw_indicator hd _) (summable_primeFormationLaw_indicator hd _),
        fun hlt => Summable.tsum_le_tsum (Set.indicator_le_indicator_of_subset
          (fun p hp => ⟨lt_of_lt_of_le hlt hp.1, hp.2⟩) (primeFormationLaw_nonneg' hd))
          (summable_primeFormationLaw_indicator hd _) (summable_primeFormationLaw_indicator hd _)⟩
  rw [two_mul_integral_exp_neg_two]
  have hlow := tendsto_primeFormationWindowMass ha hab
  rw [two_mul_integral_exp_neg_two] at hlow
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [(tendsto_order.1 hlow).1 c hc, self_mem_nhdsWithin] with d hd hd0
    exact lt_of_lt_of_le hd (hmono hd0 le_rfl).1
  · have hcont : Tendsto (fun a' : ℝ => Real.exp (-2 * a') - Real.exp (-2 * b)) (𝓝 a)
        (𝓝 (Real.exp (-2 * a) - Real.exp (-2 * b))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
        continuous_const).tendsto a
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 ((tendsto_order.1 hcont).2 c hc)
    set a' := a - min (δ / 2) (a / 2)
    have ha'pos : 0 < a' := by
      have := min_le_right (δ / 2) (a / 2)
      simp only [a']; linarith
    have ha'lt : a' < a := by
      have : 0 < min (δ / 2) (a / 2) := by positivity
      simp only [a']; linarith
    have hdist : dist a' a < δ := by
      rw [Real.dist_eq, abs_lt]
      have := min_le_left (δ / 2) (a / 2)
      have : 0 < min (δ / 2) (a / 2) := by positivity
      constructor <;> simp only [a'] <;> linarith
    have hup := tendsto_primeFormationWindowMass ha'pos (ha'lt.le.trans hab)
    rw [two_mul_integral_exp_neg_two] at hup
    filter_upwards [(tendsto_order.1 hup).2 c (hδ' hdist), self_mem_nhdsWithin] with d hd hd0
    exact lt_of_le_of_lt ((hmono hd0 ha'lt.le).2 ha'lt) hd

end GaloisForLFunctions.HTGeometry
