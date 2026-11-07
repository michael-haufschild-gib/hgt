import GaloisForLFunctions.PrimeTorusTheory.PrimeCharactersAreLacunary

/-!
# The logarithm of a fibre

For a point `u` of the torus, unimodular on the primes, write `z_p = u(p) p^{−s}`. On `Re s > 1` the fibre of a completely multiplicative `u` is

`L_u(s) = exp(Σ_p z_p + h_u(s))`, `h_u(s) = Σ_p (−log(1 − z_p) − z_p)` (`exp_tsum_eq_tsum`).

The remainder converges absolutely on `Re s > ½`: `|−log(1 − z) − z| ≤ 2|z|²`, and after the quadratic term `≤ 2|z|³` (`norm_localRem_le`, `norm_cubicRem_le`). So `h_u` is analytic on `Re s > ½` (`analyticOnNhd_hullRem`), and whether the fibre continues to `Re s > ½` is a question about the prime sum `Σ_p z_p` alone.
-/

open Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

variable {u : ℕ → ℂ}

/-- The Euler variable `z_p = u(p) p^{−s}`. -/
def eulerVar (s : ℂ) (u : ℕ → ℂ) (p : ℕ) : ℂ := powCoeff s p * u p

theorem norm_eulerVar (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖eulerVar s u p‖ = (p : ℝ) ^ (-s.re) := by
  unfold eulerVar powCoeff
  rw [norm_mul, hu p hp, mul_one, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]

theorem norm_eulerVar_sq (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖eulerVar s u p‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
  unfold eulerVar
  rw [norm_mul, hu p hp, mul_one, norm_powCoeff_sq hp.pos]

theorem norm_eulerVar_le_half (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 < s.re) : ‖eulerVar s u p‖ ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := by
  rw [norm_eulerVar hu hp]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)

theorem norm_eulerVar_le (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 < s.re) : ‖eulerVar s u p‖ ≤ 3 / 4 := by
  refine (norm_eulerVar_le_half hu hp hs).trans ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (4 / 3 : ℝ) ≤ √(p : ℝ) := Real.le_sqrt' (by norm_num) |>.mpr (by norm_num; linarith)
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by linarith) (by norm_num)]
  norm_num
  linarith

/-- The local remainder `−log(1 − z) − z`. -/
def localRem (s : ℂ) (u : ℕ → ℂ) (p : ℕ) : ℂ :=
  -Complex.log (1 - eulerVar s u p) - eulerVar s u p

/-- The cubic remainder `−log(1 − z) − z − z²/2`. -/
def cubicRem (s : ℂ) (u : ℕ → ℂ) (p : ℕ) : ℂ := localRem s u p - eulerVar s u p ^ 2 / 2

theorem norm_localRem_le (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 < s.re) : ‖localRem s u p‖ ≤ 2 * (p : ℝ) ^ (-(2 * s.re)) := by
  set z := eulerVar s u p with hz
  have hle := norm_eulerVar_le hu hp hs
  have h1 := Complex.norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
  rw [norm_neg] at h1
  have h2 : localRem s u p = -(Complex.log (1 + -z) - -z) := by
    unfold localRem
    rw [← hz, ← sub_eq_add_neg]
    ring
  rw [h2, norm_neg, ← norm_eulerVar_sq hu hp s, ← hz]
  refine h1.trans ?_
  have h3 : (1 - ‖z‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [sq_nonneg ‖z‖]

theorem norm_cubicRem_le (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 < s.re) : ‖cubicRem s u p‖ ≤ 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
  set z := eulerVar s u p with hz
  have hle := norm_eulerVar_le hu hp hs
  have h1 := Complex.norm_log_sub_logTaylor_le 2 (z := -z) (by rw [norm_neg]; linarith)
  rw [norm_neg] at h1
  have hT : Complex.logTaylor (2 + 1) (-z) = -z - z ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [hT] at h1
  have h2 : cubicRem s u p = -(Complex.log (1 + -z) - (-z - z ^ 2 / 2)) := by
    unfold cubicRem localRem
    rw [← hz, ← sub_eq_add_neg]
    ring
  rw [h2, norm_neg]
  refine h1.trans ?_
  have h3 : (1 - ‖z‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h4 : ‖z‖ ^ 3 ≤ (p : ℝ) ^ (-(3 / 2) : ℝ) := by
    have h5 := pow_le_pow_left₀ (norm_nonneg _) (norm_eulerVar_le_half hu hp hs) 3
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

theorem summable_eulerVar (hu : ∀ p, p.Prime → ‖u p‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => eulerVar s u p :=
  Summable.of_norm_bounded (summable_primes_rpow (r := -s.re) (by linarith))
    fun p => (norm_eulerVar hu p.2 s).le

theorem summable_localRem (hu : ∀ p, p.Prime → ‖u p‖ = 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun p : Nat.Primes => localRem s u p :=
  Summable.of_norm_bounded ((summable_primes_rpow (r := -(2 * s.re)) (by linarith)).mul_left 2)
    fun p => norm_localRem_le hu p.2 hs

theorem summable_cubicRem (hu : ∀ p, p.Prime → ‖u p‖ = 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun p : Nat.Primes => cubicRem s u p :=
  Summable.of_norm_bounded ((summable_primes_rpow (r := -(3 / 2)) (by norm_num)).mul_left 2)
    fun p => norm_cubicRem_le hu p.2 hs

theorem summable_quad (hu : ∀ p, p.Prime → ‖u p‖ = 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun p : Nat.Primes => eulerVar s u p ^ 2 / 2 := by
  refine Summable.of_norm_bounded (summable_primes_rpow (r := -(2 * s.re)) (by linarith)) fun p => ?_
  rw [norm_div, norm_pow, norm_eulerVar_sq hu p.2]
  simp only [Complex.norm_ofNat]
  have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by positivity
  linarith

/-- The sum of the local remainders. -/
def hullRem (s : ℂ) (u : ℕ → ℂ) : ℂ := ∑' p : Nat.Primes, localRem s u p

theorem differentiableOn_localRem (hu : ∀ p, p.Prime → ‖u p‖ = 1) {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ (fun s => localRem s u p) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have hz : DifferentiableAt ℂ (fun s => eulerVar s u p) s := by
    unfold eulerVar powCoeff
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hp.ne_zero))).mul_const _
  have hsl : 1 - eulerVar s u p ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]
    refine Complex.mem_slitPlane_of_norm_lt_one ?_
    rw [norm_neg]
    linarith [norm_eulerVar_le hu hp hs]
  exact (((differentiableAt_const _).sub hz).clog hsl).neg.sub hz

/-- The remainder is analytic in `s` on the half-plane. -/
theorem analyticOnNhd_hullRem (hu : ∀ p, p.Prime → ‖u p‖ = 1) :
    AnalyticOnNhd ℂ (fun s => hullRem s u) rightHalf := by
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
  have hd : DifferentiableOn ℂ (fun w => ∑' p : Nat.Primes, localRem w u p) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_primes_rpow (r := -(1 + 2 * η)) (by linarith)).mul_left 2)
      (fun p => (differentiableOn_localRem hu p.2).mono hUs) hUo fun p w hw => ?_
    have hw' : 1 / 2 + η < w.re := hw
    refine (norm_localRem_le hu p.2 (hUs hw)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)
  exact hd.analyticAt (hUo.mem_nhds (by show 1 / 2 + η < s.re; rw [hη]; linarith))

/-- **The logarithm of a fibre.** For `f` completely multiplicative, bounded by `1` and unimodular on the primes, `Σ_n f(n) n^{−s} = exp(Σ_p z_p + h_f(s))` on `Re s > 1`. -/
theorem exp_tsum_eq_tsum {f : ℕ →*₀ ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hu : ∀ p, p.Prime → ‖f p‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp ((∑' p : Nat.Primes, eulerVar s f p) + hullRem s f) = ∑' n, f n * (n : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hhalf : 1 / 2 < s.re := by linarith
  have h := EulerProduct.exp_tsum_primes_log_eq_tsum (f := twistedHom f hs0)
    (summable_norm_twistedHom hf hs hs0)
  rw [show (∑' n, f n * (n : ℂ) ^ (-s)) = ∑' n, twistedHom f hs0 n from
    tsum_congr fun n => (twistedHom_apply f hs0 n).symm, ← h]
  congr 1
  unfold hullRem
  rw [← Summable.tsum_add (summable_eulerVar hu hs) (summable_localRem hu hhalf)]
  refine tsum_congr fun p => ?_
  rw [twistedHom_apply]
  unfold localRem eulerVar powCoeff
  rw [mul_comm (f p)]
  ring

end

end GaloisForLFunctions.PrimeTorusTheory
