import GaloisForLFunctions.PrimeTorusTheory.PrimeCharactersAreLacunary

/-!
# The natural boundary of the hull

Haar-almost every torus point has a fibre holomorphic and zero-free on `Re s > ½`. This is sharp at every point of the line.

**Theorem** (`ae_natural_boundary`). For almost every `x`, the fibre extends to a zero-free analytic `F` on `Re s > ½`, and `F` has no analytic continuation across any point of `Re s = ½`.

**Mechanism.** Write `F = exp W`, `W = P + h`, with `P = Σ_p x_p p^{−s}` and `h = Σ_p (−log(1 − z_p) − z_p)`, `z_p = x_p p^{−s}`. The series `P` converges on `Re s > ½` by the almost-sure square-root cancellation. The series `h` is the sum of a part bounded in `L²` uniformly up to the line, namely `Σ_p z_p²/2`, and a uniformly bounded part (`lintegral_hullRem_le`).

A continuation `H` across a point of the line does not vanish at some `½ + iq`, `q` rational, nearby. There `W' = H'/H` is bounded on a half-disc, so `W` stays bounded along the ray `σ + iq`, `σ ↓ ½`. Zygmund's theorem on the torus (`measure_bounded_prime_sums_eq_zero`) says this happens only on a null set, for each `q`.

So over a typical point the hull ends exactly at the critical line. The Liouville point is the opposite extreme: whether its fibre even reaches the line is RH.
-/

open MeasureTheory Filter Topology Metric

namespace GaloisForLFunctions.PrimeTorusTheory

open ArithmeticCorrelationGeometry

noncomputable section

/-- The Euler variable `z_p = x_p p^{−s}`. -/
def eulerVar (s : ℂ) (x : GaugeTorus) (p : ℕ) : ℂ := powCoeff s p * twist x p

theorem norm_eulerVar {p : ℕ} (hp : p.Prime) (s : ℂ) (x : GaugeTorus) :
    ‖eulerVar s x p‖ = (p : ℝ) ^ (-s.re) := by
  unfold eulerVar powCoeff
  rw [norm_mul, norm_twist, mul_one, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]

theorem norm_eulerVar_sq {p : ℕ} (hp : p.Prime) (s : ℂ) (x : GaugeTorus) :
    ‖eulerVar s x p‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
  unfold eulerVar
  rw [norm_mul, norm_twist, mul_one, norm_powCoeff_sq hp.pos]

theorem norm_eulerVar_le_half {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    ‖eulerVar s x p‖ ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := by
  rw [norm_eulerVar hp]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)

theorem norm_eulerVar_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    ‖eulerVar s x p‖ ≤ 3 / 4 := by
  refine (norm_eulerVar_le_half hp hs x).trans ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (4 / 3 : ℝ) ≤ √(p : ℝ) := Real.le_sqrt' (by norm_num) |>.mpr (by norm_num; linarith)
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by linarith) (by norm_num)]
  norm_num
  linarith

/-- The local remainder `−log(1 − z) − z`. -/
def localRem (s : ℂ) (x : GaugeTorus) (p : ℕ) : ℂ :=
  -Complex.log (1 - eulerVar s x p) - eulerVar s x p

/-- The cubic remainder `−log(1 − z) − z − z²/2`. -/
def cubicRem (s : ℂ) (x : GaugeTorus) (p : ℕ) : ℂ := localRem s x p - eulerVar s x p ^ 2 / 2

theorem norm_localRem_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    ‖localRem s x p‖ ≤ 2 * (p : ℝ) ^ (-(2 * s.re)) := by
  set z := eulerVar s x p with hz
  have hle := norm_eulerVar_le hp hs x
  have h1 := Complex.norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
  rw [norm_neg] at h1
  have h2 : localRem s x p = -(Complex.log (1 + -z) - -z) := by
    unfold localRem
    rw [← hz, ← sub_eq_add_neg]
    ring
  rw [h2, norm_neg, ← norm_eulerVar_sq hp s x, ← hz]
  refine h1.trans ?_
  have h3 : (1 - ‖z‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [sq_nonneg ‖z‖]

theorem norm_cubicRem_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    ‖cubicRem s x p‖ ≤ 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
  set z := eulerVar s x p with hz
  have hle := norm_eulerVar_le hp hs x
  have h1 := Complex.norm_log_sub_logTaylor_le 2 (z := -z) (by rw [norm_neg]; linarith)
  rw [norm_neg] at h1
  have hT : Complex.logTaylor (2 + 1) (-z) = -z - z ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [hT] at h1
  have h2 : cubicRem s x p = -(Complex.log (1 + -z) - (-z - z ^ 2 / 2)) := by
    unfold cubicRem localRem
    rw [← hz, ← sub_eq_add_neg]
    ring
  rw [h2, norm_neg]
  refine h1.trans ?_
  have h3 : (1 - ‖z‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h4 : ‖z‖ ^ 3 ≤ (p : ℝ) ^ (-(3 / 2) : ℝ) := by
    have h5 := pow_le_pow_left₀ (norm_nonneg _) (norm_eulerVar_le_half hp hs x) 3
    rwa [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2) : ℝ)) 3,
      ← Real.rpow_mul (by positivity), show (-(1 / 2) : ℝ) * ((3 : ℕ) : ℝ) = -(3 / 2) by norm_num] at h5
  have h6 : ‖z‖ ^ (2 + 1) * (1 - ‖z‖)⁻¹ / (((2 : ℕ) : ℝ) + 1) ≤ 2 * ‖z‖ ^ 3 := by
    push_cast
    have h7 : 0 ≤ ‖z‖ ^ 3 := by positivity
    norm_num
    nlinarith
  linarith

theorem summable_primes_rpow {r : ℝ} (hr : r < -1) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ r := Nat.Primes.summable_rpow.mpr hr

theorem summable_localRem {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    Summable fun p : Nat.Primes => localRem s x p :=
  Summable.of_norm_bounded ((summable_primes_rpow (r := -(2 * s.re)) (by linarith)).mul_left 2)
    fun p => norm_localRem_le p.2 hs x

theorem summable_cubicRem {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    Summable fun p : Nat.Primes => cubicRem s x p :=
  Summable.of_norm_bounded ((summable_primes_rpow (r := -(3 / 2)) (by norm_num)).mul_left 2)
    fun p => norm_cubicRem_le p.2 hs x

theorem summable_quad {s : ℂ} (hs : 1 / 2 < s.re) (x : GaugeTorus) :
    Summable fun p : Nat.Primes => eulerVar s x p ^ 2 / 2 := by
  refine Summable.of_norm_bounded (summable_primes_rpow (r := -(2 * s.re)) (by linarith)) fun p => ?_
  rw [norm_div, norm_pow, norm_eulerVar_sq p.2]
  simp only [Complex.norm_ofNat]
  have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by positivity
  linarith

/-- The sum of the local remainders. -/
def hullRem (s : ℂ) (x : GaugeTorus) : ℂ := ∑' p : Nat.Primes, localRem s x p

theorem differentiableOn_localRem (x : GaugeTorus) {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ (fun s => localRem s x p) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have hz : DifferentiableAt ℂ (fun s => eulerVar s x p) s := by
    unfold eulerVar powCoeff
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hp.ne_zero))).mul_const _
  have hsl : 1 - eulerVar s x p ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]
    refine Complex.mem_slitPlane_of_norm_lt_one ?_
    rw [norm_neg]
    linarith [norm_eulerVar_le hp hs x]
  exact (((differentiableAt_const _).sub hz).clog hsl).neg.sub hz

/-- The remainder is analytic in `s` on the half-plane. -/
theorem analyticOnNhd_hullRem (x : GaugeTorus) : AnalyticOnNhd ℂ (fun s => hullRem s x) rightHalf := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  set η : ℝ := (s.re - 1 / 2) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set U : Set ℂ := {w | 1 / 2 + η < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUs : U ⊆ {w : ℂ | 1 / 2 < w.re} := fun w hw => by
    have : 1 / 2 + η < w.re := hw
    show 1 / 2 < w.re
    linarith
  have hd : DifferentiableOn ℂ (fun w => ∑' p : Nat.Primes, localRem w x p) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_primes_rpow (r := -(1 + 2 * η)) (by linarith)).mul_left 2)
      (fun p => (differentiableOn_localRem x p.2).mono hUs) hUo fun p w hw => ?_
    have hw' : 1 / 2 + η < w.re := hw
    refine (norm_localRem_le p.2 (hUs hw) x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)
  exact hd.analyticAt (hUo.mem_nhds (by show 1 / 2 + η < s.re; rw [hη]; linarith))

/-- The remainder is continuous on the torus. -/
theorem continuous_hullRem {s : ℂ} (hs : 1 / 2 < s.re) : Continuous (hullRem s) := by
  refine continuous_tsum (fun p => ?_)
    ((summable_primes_rpow (r := -(2 * s.re)) (by linarith)).mul_left 2)
    fun p x => norm_localRem_le p.2 hs x
  have hz : Continuous fun x => eulerVar s x p := continuous_const.mul (continuous_twist _)
  have hsl : ∀ x, 1 - eulerVar s x p ∈ Complex.slitPlane := fun x => by
    rw [sub_eq_add_neg]
    refine Complex.mem_slitPlane_of_norm_lt_one ?_
    rw [norm_neg]
    linarith [norm_eulerVar_le p.2 hs x]
  exact ((continuous_const.sub hz).clog hsl).neg.sub hz

/-! ### The square integral of the remainder -/

/-- The quadratic part `Σ_p z_p²/2`. -/
def quadPart (s : ℂ) (x : GaugeTorus) : ℂ := ∑' p : Nat.Primes, eulerVar s x p ^ 2 / 2

/-- The constant `Σ_p p^{−2}`. -/
def primeSqSum : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)

/-- The quadratic part is bounded in `L²`, uniformly up to the line: the squares of primes are distinct integers. -/
theorem lintegral_quadPart_le {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫⁻ x, ENNReal.ofReal (‖quadPart s x‖ ^ 2) ∂gaugeHaar ≤ ENNReal.ofReal (primeSqSum / 4) := by
  have hinj : ∀ N : ℕ, Set.InjOn (fun p : ℕ => p * p) (N.primesBelow : Set ℕ) := fun N a _ b _ h =>
    Nat.mul_self_inj.mp h
  refine lintegral_normSq_limit_le (s := fun N => N.primesBelow.image fun p => p * p)
    (a := fun n => (1 / 2 : ℂ) * (n : ℂ) ^ (-s)) (fun N n hn => ?_) (fun N => ?_)
    (Eventually.of_forall fun x => ?_)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have := (Nat.mem_primesBelow.mp hp).2.ne_zero
    exact Nat.mul_ne_zero this this
  · rw [Finset.sum_image (hinj N)]
    have hterm : ∀ p ∈ N.primesBelow, ‖(1 / 2 : ℂ) * (((p * p : ℕ) : ℂ)) ^ (-s)‖ ^ 2 ≤
        (1 / 4) * (p : ℝ) ^ (-2 : ℝ) := by
      intro p hp
      have hp' := (Nat.mem_primesBelow.mp hp).2
      rw [natCast_cpow_neg_mul hp'.ne_zero hp'.ne_zero, norm_mul, norm_mul, mul_pow, mul_pow]
      have h1 : ‖(p : ℂ) ^ (-s)‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := norm_powCoeff_sq hp'.pos s
      have h2 : (p : ℝ) ^ (-(2 * s.re)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp'.one_lt.le) (by linarith)
      have h3 : ((p : ℝ) ^ (-1 : ℝ)) ^ 2 = (p : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      have h4 : (0 : ℝ) ≤ (p : ℝ) ^ (-(2 * s.re)) := by positivity
      have h5 : ((p : ℝ) ^ (-(2 * s.re))) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
        rw [← h3]
        exact pow_le_pow_left₀ h4 h2 2
      have h6 : ‖(1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := by norm_num
      rw [h6, h1]
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have h7 := sum_primesBelow_le_tsum (g := fun p : ℕ => (p : ℝ) ^ (-2 : ℝ))
      (fun p => by positivity) (summable_primes_rpow (by norm_num)) N
    unfold primeSqSum
    linarith
  · refine (tendsto_sum_primesBelow (g := fun p : ℕ => eulerVar s x p ^ 2 / 2) (summable_quad hs x)).congr
      fun N => ?_
    unfold twistSum
    rw [Finset.sum_image (hinj N)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := (Nat.mem_primesBelow.mp hp).2
    show eulerVar s x p ^ 2 / 2 = (1 / 2 : ℂ) * ((p * p : ℕ) : ℂ) ^ (-s) * twist x (p * p)
    rw [natCast_cpow_neg_mul hp'.ne_zero hp'.ne_zero, twist_mul x hp'.ne_zero hp'.ne_zero]
    unfold eulerVar powCoeff
    ring

/-- **The remainder is bounded in `L²`, uniformly up to the line.** -/
theorem lintegral_hullRem_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re →
    ∫⁻ x, ENNReal.ofReal (‖hullRem s x‖ ^ 2) ∂gaugeHaar ≤ ENNReal.ofReal C := by
  set c : ℝ := ∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) with hc
  have hsc : Summable fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
    (summable_primes_rpow (by norm_num)).mul_left 2
  have hB : 0 ≤ primeSqSum := tsum_nonneg fun p => by positivity
  refine ⟨2 * (primeSqSum / 4) + 2 * c ^ 2, by positivity, fun s hs => ?_⟩
  have hpt : ∀ x, ‖hullRem s x‖ ^ 2 ≤ 2 * ‖quadPart s x‖ ^ 2 + 2 * c ^ 2 := by
    intro x
    have h1 : hullRem s x = quadPart s x + ∑' p : Nat.Primes, cubicRem s x p := by
      unfold quadPart
      rw [← Summable.tsum_add (summable_quad hs x) (summable_cubicRem hs x)]
      unfold hullRem cubicRem
      exact tsum_congr fun p => by ring
    have h2 : ‖∑' p : Nat.Primes, cubicRem s x p‖ ≤ c :=
      tsum_of_norm_bounded hsc.hasSum fun p => norm_cubicRem_le p.2 hs x
    have h3 := norm_add_le (quadPart s x) (∑' p : Nat.Primes, cubicRem s x p)
    rw [← h1] at h3
    have h4 := pow_le_pow_left₀ (norm_nonneg _) (h3.trans (add_le_add_right h2 _)) 2
    nlinarith [sq_nonneg (‖quadPart s x‖ - c)]
  have htwo : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    ∫⁻ x, ENNReal.ofReal (‖hullRem s x‖ ^ 2) ∂gaugeHaar
        ≤ ∫⁻ x, (ENNReal.ofReal 2 * ENNReal.ofReal (‖quadPart s x‖ ^ 2) + ENNReal.ofReal (2 * c ^ 2)) ∂gaugeHaar := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (‖quadPart s x‖ ^ 2) ∂gaugeHaar + ENNReal.ofReal (2 * c ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ htwo, lintegral_const,
            measure_univ, mul_one]
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (primeSqSum / 4) + ENNReal.ofReal (2 * c ^ 2) := by
          gcongr
          exact lintegral_quadPart_le hs
    _ = ENNReal.ofReal (2 * (primeSqSum / 4) + 2 * c ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-! ### The Euler product -/

/-- The twist as a monoid-with-zero homomorphism. -/
def twistHom (x : GaugeTorus) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else twist x n
  map_zero' := by simp
  map_one' := by simp [twist_one]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp [hm, hn, twist_mul x hm hn]

theorem twistHom_apply (x : GaugeTorus) (n : ℕ) :
    twistHom x n = if n = 0 then 0 else twist x n := rfl

theorem norm_twistHom_le (x : GaugeTorus) (n : ℕ) : ‖twistHom x n‖ ≤ 1 := by
  rw [twistHom_apply]
  split_ifs
  · simp
  · exact (norm_twist x n).le

theorem gaugeFibre_eq_tsum (x : GaugeTorus) {s : ℂ} (hs0 : s ≠ 0) :
    gaugeFibre x s = ∑' n, twistedHom (twistHom x) hs0 n := by
  unfold gaugeFibre LSeries
  refine tsum_congr fun n => ?_
  rw [twistedHom_apply, twistHom_apply]
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, if_neg hn, div_eq_mul_inv, ← Complex.cpow_neg]

/-- On `Re s > 1` the fibre is the exponential of the prime sum and the remainder. -/
theorem exp_tsum_eq_gaugeFibre (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp ((∑' p : Nat.Primes, eulerVar s x p) + hullRem s x) = gaugeFibre x s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hhalf : 1 / 2 < s.re := by linarith
  have h := EulerProduct.exp_tsum_primes_log_eq_tsum (f := twistedHom (twistHom x) hs0)
    (summable_norm_twistedHom (norm_twistHom_le x) hs hs0)
  have hz : Summable fun p : Nat.Primes => eulerVar s x p :=
    Summable.of_norm_bounded (summable_primes_rpow (r := -s.re) (by linarith))
      fun p => (norm_eulerVar p.2 s x).le
  rw [gaugeFibre_eq_tsum x hs0, ← h]
  congr 1
  unfold hullRem
  rw [← Summable.tsum_add hz (summable_localRem hhalf x)]
  refine tsum_congr fun p => ?_
  rw [twistedHom_apply, twistHom_apply, if_neg p.2.ne_zero]
  unfold localRem eulerVar powCoeff
  rw [mul_comm (twist x p)]
  ring

/-! ### The prime sums converge -/

/-- For almost every torus point the prime sum converges on `Re s > ½` to an analytic function. -/
theorem ae_exists_primeLimit :
    ∀ᵐ x ∂gaugeHaar, ∃ P : ℂ → ℂ, AnalyticOnNhd ℂ P rightHalf ∧
      ∀ s ∈ rightHalf, Tendsto (fun N => primeSum N s x) atTop (𝓝 (P s)) := by
  classical
  set a : ℕ → ℂ := fun n => if n.Prime then 1 else 0 with ha
  have h1 := ae_exists_norm_gaugePartialSum_le a (fun n => by
    simp only [ha]
    split_ifs <;> simp)
  filter_upwards [h1] with x hx
  obtain ⟨C, hC0, hC⟩ := hx
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N, (a (n + 1) * twist x (n + 1)) = gaugePartialSum a N x := by
    intro N
    unfold gaugePartialSum twistSum
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n => a n * twist x n) 0 N 1]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hbound : ∀ ε : ℝ, 0 < ε → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, (a (n + 1) * twist x (n + 1))‖ ≤ C' * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    intro ε hε
    refine ⟨C * (2 / ε + 1) ^ 2, by positivity, fun N => ?_⟩
    rw [hsum]
    refine (hC N).trans ?_
    have := sqrt_log_sq_le hε N
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hC0
  obtain ⟨P, hPa, hP⟩ := exists_analytic_of_squareRoot hbound
  refine ⟨P, hPa, fun s hs => ?_⟩
  have h3 : ∀ N : ℕ, ∑ n ∈ Finset.range N, (a (n + 1) * twist x (n + 1)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      primeSum (N + 1) s x := by
    intro N
    unfold primeSum twistSum Nat.primesBelow
    rw [Finset.sum_filter, Finset.sum_range_succ', if_neg Nat.not_prime_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : (n + 1).Prime
    · simp only [ha, if_pos hp, powCoeff]
      push_cast
      ring
    · simp only [ha, if_neg hp]
      ring
  have h4 : Tendsto (fun N => primeSum (N + 1) s x) atTop (𝓝 (P s)) := (hP s hs).congr h3
  exact (tendsto_add_atTop_iff_nat 1).mp h4

/-- The value of the prime sum, where it converges. -/
def primeLim (s : ℂ) (x : GaugeTorus) : ℂ := limUnder atTop fun N => primeSum N s x

/-- The point `½ + 1/(j+1) + iτ` of the horizontal ray ending at `½ + iτ`. -/
def rayPoint (τ : ℝ) (j : ℕ) : ℂ := ⟨1 / 2 + 1 / ((j : ℝ) + 1), τ⟩

theorem half_lt_rayPoint_re (τ : ℝ) (j : ℕ) : 1 / 2 < (rayPoint τ j).re := by
  show 1 / 2 < 1 / 2 + 1 / ((j : ℝ) + 1)
  have : 0 < 1 / ((j : ℝ) + 1) := by positivity
  linarith

/-- **Rays are unbounded.** For almost every point, the logarithm of the fibre is unbounded along every horizontal ray ending at a rational point of the line. -/
theorem ae_ray_unbounded :
    ∀ᵐ x ∂gaugeHaar, ∀ (q : ℚ) (M J : ℕ), ¬ ∀ j, J ≤ j →
      ‖primeLim (rayPoint q j) x + hullRem (rayPoint q j) x‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := lintegral_hullRem_le
  simp only [ae_all_iff]
  intro q M J
  rw [ae_iff]
  simp only [not_not]
  refine measure_bounded_prime_sums_eq_zero (s := rayPoint q) (fun j => half_lt_rayPoint_re _ j) ?_
    (g := fun j x => primeLim (rayPoint q j) x) (e := fun j x => hullRem (rayPoint q j) x) (fun j => ?_)
    (fun j => (continuous_hullRem (half_lt_rayPoint_re _ j)).aemeasurable) hC0
    (fun j => hC _ (half_lt_rayPoint_re _ j)) (M : ℝ) J
  · have h1 : Tendsto (fun j : ℕ => (1 / 2 : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 / 2 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h1
    exact h1
  · filter_upwards [ae_exists_primeLimit] with x hx
    obtain ⟨P, -, hP⟩ := hx
    have h2 := hP _ (half_lt_rayPoint_re (q : ℝ) j)
    unfold primeLim
    rw [h2.limUnder_eq]
    exact h2

/-! ### The boundary -/

/-- **The natural boundary of the hull.** For almost every torus point, the fibre extends to a zero-free analytic function on `Re s > ½`, with no analytic continuation across any point of `Re s = ½`. -/
theorem ae_natural_boundary :
    ∀ᵐ x ∂gaugeHaar, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
      (∀ s, 1 < s.re → F s = gaugeFibre x s) ∧ (∀ s ∈ rightHalf, F s ≠ 0) ∧
      ∀ (τ₀ r : ℝ) (H : ℂ → ℂ), 0 < r → AnalyticOnNhd ℂ H (ball (⟨1 / 2, τ₀⟩ : ℂ) r) →
        ¬ ∀ s ∈ ball (⟨1 / 2, τ₀⟩ : ℂ) r, s ∈ rightHalf → H s = F s := by
  filter_upwards [ae_exists_primeLimit, ae_ray_unbounded] with x hx hray
  obtain ⟨P, hPa, hP⟩ := hx
  set W : ℂ → ℂ := fun s => P s + hullRem s x with hW
  have hWa : AnalyticOnNhd ℂ W rightHalf := hPa.add (analyticOnNhd_hullRem x)
  refine ⟨fun s => Complex.exp (W s), fun s hs => (hWa s hs).cexp, fun s hs => ?_,
    fun s _ => Complex.exp_ne_zero _, ?_⟩
  · have hmem : s ∈ rightHalf := by
      show 1 / 2 < s.re
      linarith
    have hz : Summable fun p : Nat.Primes => eulerVar s x p :=
      Summable.of_norm_bounded (summable_primes_rpow (r := -s.re) (by linarith))
        fun p => (norm_eulerVar p.2 s x).le
    have h1 : P s = ∑' p : Nat.Primes, eulerVar s x p :=
      tendsto_nhds_unique (hP s hmem) (tendsto_sum_primesBelow (g := eulerVar s x) hz)
    simp only [hW]
    rw [h1]
    exact exp_tsum_eq_gaugeFibre x hs
  intro τ₀ r H hr hH hEq
  set z₀ : ℂ := ⟨1 / 2, τ₀⟩ with hz₀
  -- A rational point of the line where the continuation does not vanish.
  have hne : ∃ q : ℚ, (⟨1 / 2, (q : ℝ)⟩ : ℂ) ∈ ball z₀ r ∧ H ⟨1 / 2, (q : ℝ)⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hfreq : ∃ᶠ z in 𝓝[≠] z₀, H z = 0 := by
      intro hev
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
      obtain ⟨ε, hε, hball⟩ := hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show τ₀ < τ₀ + min ε r by
        have := lt_min hε hr
        linarith)
      have hdist : dist (⟨1 / 2, (q : ℝ)⟩ : ℂ) z₀ < min ε r := by
        rw [Complex.dist_of_re_eq (z := (⟨1 / 2, (q : ℝ)⟩ : ℂ)) (w := z₀) rfl, Real.dist_eq]
        show |(q : ℝ) - τ₀| < min ε r
        rw [abs_of_pos (sub_pos.mpr hq1)]
        linarith
      have hne' : (⟨1 / 2, (q : ℝ)⟩ : ℂ) ≠ z₀ := fun h => by
        have := congrArg Complex.im h
        simp only [hz₀] at this
        linarith
      exact hball _ (mem_ball.mpr (hdist.trans_le (min_le_left _ _))) hne'
        (hcon q (mem_ball.mpr (hdist.trans_le (min_le_right _ _))))
    have hzero := hH.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball z₀ r).isPreconnected (mem_ball_self hr) hfreq
    have hw : (⟨1 / 2 + r / 2, τ₀⟩ : ℂ) ∈ ball z₀ r := by
      rw [mem_ball, Complex.dist_of_im_eq (z := (⟨1 / 2 + r / 2, τ₀⟩ : ℂ)) (w := z₀) rfl, Real.dist_eq]
      show |1 / 2 + r / 2 - 1 / 2| < r
      rw [show (1 / 2 + r / 2 - 1 / 2 : ℝ) = r / 2 by ring, abs_of_pos (by positivity)]
      linarith
    have hw' : (⟨1 / 2 + r / 2, τ₀⟩ : ℂ) ∈ rightHalf := by
      show 1 / 2 < 1 / 2 + r / 2
      linarith
    have h1 := hEq _ hw hw'
    rw [hzero hw] at h1
    exact Complex.exp_ne_zero _ h1.symm
  obtain ⟨q, hqB, hq0⟩ := hne
  set z₁ : ℂ := ⟨1 / 2, (q : ℝ)⟩ with hz₁
  -- The logarithmic derivative of the continuation is bounded near `z₁`.
  set G : ℂ → ℂ := fun z => deriv H z / H z with hG
  have hGc : ContinuousAt G z₁ :=
    (hH z₁ hqB).deriv.continuousAt.div (hH z₁ hqB).continuousAt hq0
  set K : ℝ := ‖G z₁‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  have hev : ∀ᶠ z in 𝓝 z₁, ‖G z‖ < K ∧ z ∈ ball z₀ r :=
    (hGc.norm.tendsto.eventually (gt_mem_nhds (lt_add_one ‖G z₁‖))).and (isOpen_ball.mem_nhds hqB)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- So the logarithm `W` is Lipschitz on a half-disc.
  set D : Set ℂ := ball z₁ ρ ∩ rightHalf with hD
  have hDo : IsOpen D := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hDc : Convex ℝ D := (convex_ball _ _).inter (convex_halfSpace_re_gt _)
  have hderiv : ∀ z ∈ D, ‖deriv W z‖ ≤ K := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h1 : HasDerivAt (fun s => Complex.exp (W s)) (Complex.exp (W z) * deriv W z) z :=
      (hWa z hz2).differentiableAt.hasDerivAt.cexp
    have h2 : H =ᶠ[𝓝 z] fun s => Complex.exp (W s) := by
      filter_upwards [hDo.mem_nhds ⟨hz1, hz2⟩] with w hw
      exact hEq w (hball w hw.1).2 hw.2
    have h3 : deriv H z = Complex.exp (W z) * deriv W z := by
      rw [h2.deriv_eq]
      exact h1.deriv
    have h4 : H z = Complex.exp (W z) := h2.self_of_nhds
    have h5 : G z = deriv W z := by
      simp only [hG]
      rw [h3, h4]
      exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
    rw [← h5]
    exact (hball z hz1).1.le
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hρ
  have hraymem : ∀ j, J ≤ j → rayPoint q j ∈ D := by
    intro j hj
    refine ⟨?_, half_lt_rayPoint_re _ j⟩
    rw [mem_ball, Complex.dist_of_im_eq (z := rayPoint q j) (w := z₁) rfl, Real.dist_eq]
    have h1 : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := Nat.one_div_le_one_div hj
    have h2 : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    show |1 / 2 + 1 / ((j : ℝ) + 1) - 1 / 2| < ρ
    rw [show (1 / 2 + 1 / ((j : ℝ) + 1) - 1 / 2 : ℝ) = 1 / ((j : ℝ) + 1) by ring, abs_of_pos h2]
    linarith
  obtain ⟨M, hM⟩ := exists_nat_ge (‖W (rayPoint q J)‖ + K * (2 * ρ))
  refine hray q M J fun j hj => ?_
  have h1 := hDc.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hWa z hz.2).differentiableAt) hderiv (hraymem J le_rfl) (hraymem j hj)
  have h2 : ‖rayPoint q j - rayPoint q J‖ ≤ 2 * ρ := by
    have h3 := mem_ball.mp (hraymem j hj).1
    have h4 := mem_ball.mp (hraymem J le_rfl).1
    rw [← dist_eq_norm]
    have h5 := dist_triangle_right (rayPoint q j) (rayPoint q J) z₁
    linarith
  have h6 : W (rayPoint q j) = primeLim (rayPoint q j) x + hullRem (rayPoint q j) x := by
    simp only [hW]
    unfold primeLim
    rw [(hP _ (half_lt_rayPoint_re _ j)).limUnder_eq]
  rw [← h6]
  have h7 : ‖W (rayPoint q j)‖ ≤ ‖W (rayPoint q J)‖ + ‖W (rayPoint q j) - W (rayPoint q J)‖ := by
    have := norm_add_le (W (rayPoint q J)) (W (rayPoint q j) - W (rayPoint q J))
    rwa [add_sub_cancel] at this
  have h8 : K * ‖rayPoint q j - rayPoint q J‖ ≤ K * (2 * ρ) :=
    mul_le_mul_of_nonneg_left h2 hK0.le
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
