import GaloisForLFunctions.SurfaceOfSpecZ.ConfigurationsNeedAnAttainedTopAtFinitelyManyFrobenii

/-!
# Very smooth degrees need an attained top

`ConfigurationsNeedAnAttainedTopAtFinitelyManyFrobenii` blinds the degrees of a finite set of
primes. The obstruction is not finite generation: it persists when every prime eventually takes
part. Call `d ≥ 1` *very smooth* if every prime factor `p` of `d` satisfies `p⁴ ≤ log d`. For the
spline of order `o ≥ 3` and `0 < Θ ≤ ½` there is a tempered configuration without real zeros,
with `sup Re ρ = ½ + Θ` not attained, such that `(−1)^{o+1} 2 Re S(log d) ≥ −1` at every very
smooth `d` (`exists_zeroConfig_verySmooth_signed_nonattained`); from below for the cubic spline
(`exists_zeroConfig_verySmooth_bddBelow_nonattained`). With attainment they do decide: they contain
the `2ᵃ3ᵇ` beyond `log = 81` (`onLine_of_bddBelow_verySmooth_of_max`). The very smooth integers up to
`x` number `x^{o(1)}`; the primes, with power-saving gaps, need no attainment
(`TheGapMethodIterates`).

**Construction.** Level `k` is the pair `½ ± x_k + 2πiM_k` at a zero of `B̂`, `x_k = Θ(1 − 2^{−k−1})`,
on the windows `U_0 = 0`, `U_k = V^{2^k}`. The height `M_k ≥ 2^{k+1}` is a simultaneous Dirichlet
return of `log j` for all `j ≤ U_{k+1}^{1/4}` to precision `1/Q_k`, `Q_k ≥ 8πU_{k+1}/log 2`, so
`e^{2πiM_k log d}` is within `¼` of `1` at every very smooth `d` with `log d ≤ U_{k+1}`
(`norm_exp_smoothHeight_sub_one_le`). Every level `j ≥ k` is then in phase on the window `k`, so no
weight ceiling is needed (`neg_one_le_tsum_of_resonant`). With `U_{k+1}^{1/4} = U_k^{1/2}` generators,
`log M_k = O(U_k^{1/2} log U_k)`, and the weight `2|c_k| ≥ 2x_k^{2(o+1)}/(7M_k)^{2(o+1)}` overtakes
the earlier levels within the window once `log V = K(o, Θ)/Θ` (`eight_le_smoothWt_mul_exp`).
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### Dominance when every later level is in phase -/

/-- **Dominance without ceilings.** If level `k` carries at least half its weight, every later level
is nonnegative, the weights sum to at most `1`, and for `k ≥ 1` level `k` outweighs the earlier
ones by `8` at `λ`, then the tower sum at `λ` is at least `−1`. -/
theorem neg_one_le_tsum_of_resonant {Θ : ℝ} {x w a b : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hxΘ : ∀ j, x j ≤ Θ) (hxm : Monotone x) (hw : ∀ j, 0 ≤ w j) (hws : Summable w)
    (hw1 : ∑' j, w j ≤ 1) (ha : ∀ j, |a j| ≤ w j) (hb : ∀ j, |b j| ≤ w j) {lam : ℝ}
    (hlam : 0 ≤ lam) {k : ℕ} (hak : w k / 2 ≤ a k) (hpos : ∀ j, k < j → 0 ≤ a j)
    (hlo : ∀ n, k = n + 1 → 8 ≤ w (n + 1) * Real.exp ((x (n + 1) - x n) * lam)) :
    -1 ≤ ∑' j, (Real.exp (x j * lam) * a j + Real.exp (-(x j * lam)) * b j) := by
  set f : ℕ → ℝ := fun j => Real.exp (x j * lam) * a j with hf
  set g : ℕ → ℝ := fun j => Real.exp (-(x j * lam)) * b j with hg
  have hfb : ∀ j, |f j| ≤ Real.exp (Θ * lam) * w j := by
    intro j
    show |Real.exp (x j * lam) * a j| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxΘ j) hlam)) (ha j)
      (abs_nonneg _) (Real.exp_pos _).le
  have hgb : ∀ j, |g j| ≤ w j := by
    intro j
    show |Real.exp (-(x j * lam)) * b j| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-(x j * lam)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := mul_nonneg (hx0 j) hlam; linarith)
    calc Real.exp (-(x j * lam)) * |b j| ≤ 1 * w j :=
          mul_le_mul h1 (hb j) (abs_nonneg _) zero_le_one
      _ = w j := one_mul _
  have hfs : Summable f :=
    Summable.of_norm_bounded (hws.mul_left _) fun j => by rw [Real.norm_eq_abs]; exact hfb j
  have hgs : Summable g :=
    Summable.of_norm_bounded hws fun j => by rw [Real.norm_eq_abs]; exact hgb j
  have hg1 : -1 ≤ ∑' j, g j := by
    have : ∑' j, -w j ≤ ∑' j, g j :=
      Summable.tsum_le_tsum (fun j => neg_le_of_abs_le (hgb j)) hws.neg hgs
    rw [tsum_neg] at this
    linarith
  have hsplit := Summable.sum_add_tsum_nat_add (k + 1) hfs
  have htail : 0 ≤ ∑' j, f (j + (k + 1)) := tsum_nonneg fun j =>
    mul_nonneg (Real.exp_pos _).le (hpos _ (by omega))
  have hhead : 0 ≤ ∑ j ∈ Finset.range (k + 1), f j := by
    rw [Finset.sum_range_succ]
    rcases k with _ | n
    · simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact mul_nonneg (Real.exp_pos _).le (le_trans (by linarith [hw 0]) hak)
    · have hE := Real.exp_pos (x n * lam)
      -- the earlier levels are at least `−e^{x_n λ}`
      have hlow : -Real.exp (x n * lam) ≤ ∑ j ∈ Finset.range (n + 1), f j := by
        have h1 : ∀ j ∈ Finset.range (n + 1), -(Real.exp (x n * lam) * w j) ≤ f j := by
          intro j hj
          have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hex : Real.exp (x j * lam) ≤ Real.exp (x n * lam) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxm hjn) hlam)
          have haj := (abs_le.mp (ha j)).1
          show -(Real.exp (x n * lam) * w j) ≤ Real.exp (x j * lam) * a j
          calc -(Real.exp (x n * lam) * w j) ≤ -(Real.exp (x j * lam) * w j) :=
                neg_le_neg (mul_le_mul_of_nonneg_right hex (hw j))
            _ = Real.exp (x j * lam) * -w j := by ring
            _ ≤ Real.exp (x j * lam) * a j :=
                mul_le_mul_of_nonneg_left haj (Real.exp_pos _).le
        have h2 : ∑ j ∈ Finset.range (n + 1), w j ≤ 1 :=
          le_trans (hws.sum_le_tsum _ fun j _ => hw j) hw1
        have h3 := Finset.sum_le_sum h1
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h3
        have h4 := mul_le_mul_of_nonneg_left h2 hE.le
        linarith
      have htop : 4 * Real.exp (x n * lam) ≤ f (n + 1) := by
        have h8 := hlo n rfl
        have hE2 := Real.exp_pos ((x (n + 1) - x n) * lam)
        have e : Real.exp (x (n + 1) * lam) =
            Real.exp (x n * lam) * Real.exp ((x (n + 1) - x n) * lam) := by
          rw [← Real.exp_add]; ring_nf
        show 4 * Real.exp (x n * lam) ≤ Real.exp (x (n + 1) * lam) * a (n + 1)
        rw [e]
        calc 4 * Real.exp (x n * lam) = Real.exp (x n * lam) * 8 / 2 := by ring
          _ ≤ Real.exp (x n * lam) * (w (n + 1) * Real.exp ((x (n + 1) - x n) * lam)) / 2 := by
              gcongr
          _ = Real.exp (x n * lam) * Real.exp ((x (n + 1) - x n) * lam) * (w (n + 1) / 2) := by
              ring
          _ ≤ Real.exp (x n * lam) * Real.exp ((x (n + 1) - x n) * lam) * a (n + 1) :=
              mul_le_mul_of_nonneg_left hak (by positivity)
      linarith
  rw [hfs.tsum_add hgs, ← hsplit]
  linarith

namespace SmoothTower

open SplineTower

variable (o : ℕ) (Θ V : ℝ)

/-- The generators at level `k`: the integers `j < ⌊U_{k+1}^{1/4}⌋ + 1`. -/
def gens (k : ℕ) : ℕ := ⌊Real.sqrt (Real.sqrt (win V (k + 1)))⌋₊ + 1

/-- The least height `2^{k+1} + 2(o + 1)`. -/
def baseHeight (k : ℕ) : ℕ := 2 ^ (k + 1) + 2 * (o + 1)

theorem exists_smoothHeight (k : ℕ) : ∃ M : ℕ, baseHeight o k ≤ M ∧
    M ≤ 2 * baseHeight o k + (2 * baseHeight o k * prec V k) ^ gens V k ∧
    ∀ i : Fin (gens V k), ∃ z : ℤ, |(M : ℝ) * Real.log (i : ℕ) - z| ≤ 1 / (prec V k : ℝ) :=
  exists_resonant_ge (fun i : Fin (gens V k) => Real.log (i : ℕ))
    (by unfold baseHeight; exact le_add_left (by omega)) (by unfold prec; omega)

/-- The heights `M_k`, resonant with `log j` for every `j < gens k`. -/
def smoothHeight (k : ℕ) : ℕ := Classical.choose (exists_smoothHeight o V k)

theorem smoothHeight_spec (k : ℕ) : baseHeight o k ≤ smoothHeight o V k ∧
    smoothHeight o V k ≤ 2 * baseHeight o k + (2 * baseHeight o k * prec V k) ^ gens V k ∧
    ∀ i : Fin (gens V k), ∃ z : ℤ,
      |(smoothHeight o V k : ℝ) * Real.log (i : ℕ) - z| ≤ 1 / (prec V k : ℝ) :=
  Classical.choose_spec (exists_smoothHeight o V k)

/-- The coefficient `c_k = sinc(2πM_k − ix_k)^{2(o+1)}`. -/
def smoothCoef (k : ℕ) : ℂ := sincC (splinePoint (smoothHeight o V k) (depth Θ k)) ^ (2 * (o + 1))

/-- The weight `2|c_k|`. -/
def smoothWt (k : ℕ) : ℝ := 2 * ‖smoothCoef o Θ V k‖

/-- The points `½ ± x_k + 2πiM_k`. -/
def smoothPt : ℕ × Bool → ℂ
  | (k, true) => (1 / 2 : ℂ) + (depth Θ k : ℂ) + ((2 * Real.pi * smoothHeight o V k : ℝ) : ℂ) * I
  | (k, false) => (1 / 2 : ℂ) - (depth Θ k : ℂ) + ((2 * Real.pi * smoothHeight o V k : ℝ) : ℂ) * I

variable {o Θ V}

/-! ### Heights and weights -/

theorem two_mul_le_smoothHeight (k : ℕ) : 2 * (o + 1) ≤ smoothHeight o V k :=
  le_trans (Nat.le_add_left _ _) (smoothHeight_spec o V k).1

theorem two_pow_le_smoothHeight (k : ℕ) : 2 ^ (k + 1) ≤ smoothHeight o V k :=
  le_trans (Nat.le_add_right _ _) (smoothHeight_spec o V k).1

theorem k_le_smoothHeight (k : ℕ) : k ≤ smoothHeight o V k :=
  le_trans ((Nat.lt_two_pow_self (n := k)).le.trans (Nat.pow_le_pow_right (by norm_num) k.le_succ))
    (two_pow_le_smoothHeight k)

theorem smoothWt_nonneg (k : ℕ) : 0 ≤ smoothWt o Θ V k := by unfold smoothWt; positivity

/-- **The weights decay geometrically:** `2|c_k| ≤ 2/M_k² ≤ 2^{−k−1}`. -/
theorem smoothWt_le (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) :
    smoothWt o Θ V k ≤ (1 / 2) ^ (k + 1) := by
  have hM1 : 1 ≤ smoothHeight o V k := by have := two_mul_le_smoothHeight (o := o) (V := V) k; omega
  have h := norm_sincPow_le hM1 (depth_nonneg hΘ k) ((depth_lt hΘ k).le.trans hΘ2) (o + 1)
  have hm1 : (1 : ℝ) ≤ (smoothHeight o V k : ℝ) := by exact_mod_cast hM1
  have hm2 : (2 : ℝ) ^ (k + 1) ≤ (smoothHeight o V k : ℝ) := by
    exact_mod_cast two_pow_le_smoothHeight (o := o) (V := V) k
  set m : ℝ := (smoothHeight o V k : ℝ)
  have hp : m ^ 2 ≤ m ^ (2 * (o + 1)) := pow_le_pow_right₀ hm1 (by omega)
  have hq : ((2 : ℝ) ^ (k + 1)) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm2 2
  have h2k : (2 : ℝ) ≤ 2 ^ (k + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  unfold smoothWt smoothCoef
  calc 2 * ‖sincC (splinePoint (smoothHeight o V k) (depth Θ k)) ^ (2 * (o + 1))‖
      ≤ 2 * (1 / m ^ (2 * (o + 1))) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2 * (1 / ((2 : ℝ) ^ (k + 1)) ^ 2) := by
        gcongr
        exact hq.trans hp
    _ = (1 / 2) ^ (k + 1) * (2 / 2 ^ (k + 1)) := by
        rw [one_div_pow]; field_simp
    _ ≤ (1 / 2) ^ (k + 1) * 1 := by
        gcongr
        rw [div_le_one hpos]; exact h2k
    _ = (1 / 2) ^ (k + 1) := mul_one _

theorem summable_smoothWt (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : Summable (smoothWt o Θ V) :=
  Summable.of_nonneg_of_le smoothWt_nonneg (smoothWt_le hΘ hΘ2)
    ((summable_geometric_two).mul_right (1 / 2) |>.congr fun k => by rw [pow_succ])

theorem tsum_smoothWt_le (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ∑' k, smoothWt o Θ V k ≤ 1 := by
  have hg : Summable fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1) :=
    (summable_geometric_two).mul_right (1 / 2) |>.congr fun k => by rw [pow_succ]
  have h1 : ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_two]; norm_num
  calc ∑' k, smoothWt o Θ V k ≤ ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) :=
        Summable.tsum_le_tsum (smoothWt_le hΘ hΘ2) (summable_smoothWt hΘ hΘ2) hg
    _ = 1 := h1

/-- The weight from below: `2|c_k| ≥ 2(Θ/2)^{2(o+1)}/(7M_k)^{2(o+1)}`. -/
theorem smoothWt_ge (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) :
    2 * (Θ / 2) ^ (2 * (o + 1)) / (7 * (smoothHeight o V k : ℝ)) ^ (2 * (o + 1)) ≤
      smoothWt o Θ V k := by
  have hM1 : 1 ≤ smoothHeight o V k := by have := two_mul_le_smoothHeight (o := o) (V := V) k; omega
  have h1 := le_norm_sincPow hM1 (depth_nonneg hΘ k) ((depth_lt hΘ k).le.trans hΘ2) (o + 1)
  have h2 : (Θ / 2) ^ (2 * (o + 1)) / (7 * (smoothHeight o V k : ℝ)) ^ (2 * (o + 1)) ≤
      depth Θ k ^ (2 * (o + 1)) / (7 * (smoothHeight o V k : ℝ)) ^ (2 * (o + 1)) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (half_le_depth hΘ k) _)
      (by positivity)
  unfold smoothWt smoothCoef
  rw [mul_div_assoc]
  linarith

/-! ### Resonance at the very smooth degrees -/

/-- Every prime factor `p` with `p⁴ ≤ U_{k+1}` is a generator of level `k`. -/
theorem lt_gens_of_pow_four_le {k p : ℕ} (h4 : (p : ℝ) ^ 4 ≤ win V (k + 1)) : p < gens V k := by
  have hs1 : (p : ℝ) ^ 2 ≤ Real.sqrt (win V (k + 1)) :=
    Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact h4)
  have hs2 : (p : ℝ) ≤ Real.sqrt (Real.sqrt (win V (k + 1))) := Real.le_sqrt_of_sq_le hs1
  have := Nat.le_floor hs2
  unfold gens; omega

/-- **Resonance at the very smooth degrees.** If every prime factor `p` of `d ≠ 0` has
`p⁴ ≤ log d ≤ U_{k+1}`, then `e^{2πiM_k log d}` is within `¼` of `1`. -/
theorem norm_exp_smoothHeight_sub_one_le (hV : 1 ≤ V) (k : ℕ) {d : ℕ}
    (hsm : ∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) (hU : Real.log d ≤ win V (k + 1)) :
    ‖cexp (((2 * Real.pi * smoothHeight o V k * Real.log d : ℝ) : ℂ) * I) - 1‖ ≤ 1 / 4 := by
  obtain ⟨-, -, hres⟩ := smoothHeight_spec o V k
  choose z hz using hres
  set M : ℝ := (smoothHeight o V k : ℝ)
  set Q : ℝ := (prec V k : ℝ)
  set U : ℝ := win V (k + 1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU1 : 1 ≤ U := one_le_win_succ hV k
  have hQ : 8 * Real.pi * U / Real.log 2 ≤ Q := by
    simp only [Q, prec]; push_cast
    linarith [Nat.le_ceil (8 * Real.pi * U / Real.log 2)]
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hgen : ∀ p ∈ d.primeFactors, p < gens V k := fun p hp =>
    lt_gens_of_pow_four_le ((hsm p hp).trans hU)
  have hlog : Real.log d = ∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  -- integer parts and errors of `M log p`
  set zz : ℕ → ℤ := fun p => if h : p < gens V k then z ⟨p, h⟩ else 0
  set ε : ℕ → ℝ := fun p => M * Real.log p - zz p with hε
  have hεb : ∀ p ∈ d.primeFactors, |ε p| ≤ 1 / Q := by
    intro p hp
    have h := hgen p hp
    have := hz ⟨p, h⟩
    simp only [ε, zz, dif_pos h]
    exact this
  have hsplit : 2 * Real.pi * M * Real.log d =
      2 * Real.pi * ∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * ε p +
        ((∑ p ∈ d.primeFactors, (d.factorization p : ℤ) * zz p : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hlog]; simp only [hε]; push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hsplit]
  have hexp : cexp (((2 * Real.pi * ∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * ε p +
      ((∑ p ∈ d.primeFactors, (d.factorization p : ℤ) * zz p : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) *
        I) = cexp (((2 * Real.pi * ∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * ε p : ℝ) : ℂ) *
        I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have : ((((∑ p ∈ d.primeFactors, (d.factorization p : ℤ) * zz p : ℤ) : ℝ) * (2 * Real.pi) :
        ℝ) : ℂ) * I = ((∑ p ∈ d.primeFactors, (d.factorization p : ℤ) * zz p : ℤ) : ℂ) *
        (2 * Real.pi * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  refine (norm_exp_I_sub_one_le _).trans ?_
  -- `2π Σ t_p / Q ≤ ¼`, as `Σ t_p log 2 ≤ log d ≤ U`
  have hsum : (∑ p ∈ d.primeFactors, (d.factorization p : ℝ)) * Real.log 2 ≤ U := by
    have : (∑ p ∈ d.primeFactors, (d.factorization p : ℝ)) * Real.log 2 ≤
        ∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * Real.log p := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact Real.log_le_log (by norm_num)
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
    rw [← hlog] at this
    linarith
  have he : |∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * ε p| ≤
      (∑ p ∈ d.primeFactors, (d.factorization p : ℝ)) * (1 / Q) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hεb p hp) (Nat.cast_nonneg _)
  have hA0 : 0 ≤ ∑ p ∈ d.primeFactors, (d.factorization p : ℝ) :=
    Finset.sum_nonneg fun p _ => Nat.cast_nonneg _
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc 2 * Real.pi * |∑ p ∈ d.primeFactors, (d.factorization p : ℝ) * ε p|
      ≤ 2 * Real.pi * ((∑ p ∈ d.primeFactors, (d.factorization p : ℝ)) * (1 / Q)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 / 4 := by
        rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ hQ0]
        rw [div_le_iff₀ hl2] at hQ
        nlinarith [Real.pi_pos]

/-! ### The takeover -/

/-- The constant `K = 8(2 + 2(o+1) log(2/Θ)) + 304 · 2(o+1)`; the windows use `log V = K/Θ`. -/
def smoothK (o : ℕ) (Θ : ℝ) : ℝ :=
  8 * (2 + 2 * (o + 1) * Real.log (2 / Θ)) + 304 * (2 * (o + 1))

/-- The base `V = e^{K/Θ}` of the windows. -/
def smoothV (o : ℕ) (Θ : ℝ) : ℝ := Real.exp (smoothK o Θ / Θ)

theorem log_two_div_nonneg {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : 0 ≤ Real.log (2 / Θ) :=
  Real.log_nonneg (by rw [le_div_iff₀ hΘ]; linarith)

theorem le_smoothK (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : 304 * (2 * ((o : ℝ) + 1)) ≤ smoothK o Θ := by
  have hL := log_two_div_nonneg hΘ hΘ2
  unfold smoothK
  have : 0 ≤ 2 * ((o : ℝ) + 1) * Real.log (2 / Θ) := by positivity
  linarith

theorem le_smoothV (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : 1000 ≤ smoothV o Θ := by
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  have hK : 600 ≤ smoothK o Θ := by have := le_smoothK (o := o) hΘ hΘ2; nlinarith
  have hKΘ : 2 * smoothK o Θ ≤ smoothK o Θ / Θ := by
    rw [le_div_iff₀ hΘ]; nlinarith
  unfold smoothV
  have := Real.add_one_le_exp (smoothK o Θ / Θ)
  linarith

/-- `log s ≤ 2√s` and `(log s)² ≤ 4s` for `s ≥ 1`. -/
theorem log_le_two_sqrt {s : ℝ} (hs : 1 ≤ s) : Real.log s ≤ 2 * Real.sqrt s := by
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by linarith)
  have h1 := Real.log_le_sub_one_of_pos hs0
  rw [Real.log_sqrt (by linarith)] at h1
  linarith

/-- **The exponent budget.** With `ℓ = log s = 2^n log V`, `Θ log V = K`, `s ≥ 1`:
`c + 19 N s ℓ ≤ Θ s²/2^{n+2}`, `c = 2 + N log(2/Θ)`, `N = 2(o+1)`. -/
theorem budget {Θ s : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (hs : 1 ≤ s) (n : ℕ)
    (hℓ : Real.log s = 2 ^ n * Real.log (smoothV o Θ)) :
    (2 + 2 * (o + 1) * Real.log (2 / Θ)) + 19 * (2 * (o + 1)) * s * Real.log s ≤
      Θ * s ^ 2 / 2 ^ (n + 2) := by
  have hKN := le_smoothK (o := o) hΘ hΘ2
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 * ((o : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hN]
  rw [← hN] at hKN
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 + N * Real.log (2 / Θ) := ⟨_, rfl⟩
  rw [← hc]
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; have := log_two_div_nonneg hΘ hΘ2; positivity
  have hℓ0 : 0 ≤ Real.log s := Real.log_nonneg hs
  have hsq := Real.sqrt_nonneg s
  have hss := Real.mul_self_sqrt (show 0 ≤ s by linarith)
  have hℓ2 : Real.log s ≤ 2 * Real.sqrt s := log_le_two_sqrt hs
  have hsqs : Real.sqrt s ≤ s := by
    have h1 : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs
    nlinarith
  have hℓs : Real.log s ≤ 2 * s ^ 2 := by nlinarith
  have hℓsq : Real.log s ^ 2 ≤ 4 * s := by nlinarith
  have hLV : Real.log (smoothV o Θ) = smoothK o Θ / Θ := by unfold smoothV; rw [Real.log_exp]
  have hK : smoothK o Θ = 8 * c + 304 * N := by rw [hc, hN]; unfold smoothK; ring
  have h1 : (c + 19 * N * s * Real.log s) * (4 * Real.log s) ≤ smoothK o Θ * s ^ 2 := by
    have e1 : 4 * c * Real.log s ≤ 8 * c * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hℓs (by positivity : (0 : ℝ) ≤ 4 * c)
      linarith
    have e2 : 76 * N * s * Real.log s ^ 2 ≤ 304 * N * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hℓsq (by positivity : (0 : ℝ) ≤ 76 * N * s)
      linarith
    have expand : (c + 19 * N * s * Real.log s) * (4 * Real.log s) =
        4 * c * Real.log s + 76 * N * s * Real.log s ^ 2 := by ring
    rw [expand, hK]
    linarith
  have h2pos : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have hL0 : 0 < Real.log (smoothV o Θ) := by
    rw [hLV]; exact div_pos (by nlinarith) hΘ
  have h4 : 2 ^ (n + 2) * Real.log (smoothV o Θ) = 4 * Real.log s := by
    rw [hℓ, pow_add]; ring
  have hΘL : Θ * Real.log (smoothV o Θ) = smoothK o Θ := by rw [hLV]; field_simp
  have key : (c + 19 * N * s * Real.log s) * 2 ^ (n + 2) * Real.log (smoothV o Θ) ≤
      Θ * s ^ 2 * Real.log (smoothV o Θ) := by
    calc (c + 19 * N * s * Real.log s) * 2 ^ (n + 2) * Real.log (smoothV o Θ)
        = (c + 19 * N * s * Real.log s) * (4 * Real.log s) := by rw [mul_assoc, h4]
      _ ≤ smoothK o Θ * s ^ 2 := h1
      _ = Θ * s ^ 2 * Real.log (smoothV o Θ) := by rw [← hΘL]; ring
  rw [le_div_iff₀ h2pos]
  exact le_of_mul_le_mul_right key hL0

/-- **The takeover.** With `V = e^{K/Θ}`, level `n + 1` outweighs the earlier levels by `8` from the
start of its window: `2|c_{n+1}| e^{(x_{n+1} − x_n)U_{n+1}} ≥ 8`. -/
theorem eight_le_smoothWt_mul_exp (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (n : ℕ) :
    8 ≤ smoothWt o Θ (smoothV o Θ) (n + 1) *
      Real.exp ((depth Θ (n + 1) - depth Θ n) * win (smoothV o Θ) (n + 1)) := by
  set V := smoothV o Θ with hVdef
  have hV := le_smoothV (o := o) hΘ hΘ2
  rw [← hVdef] at hV
  have hV1 : 1 ≤ V := by linarith
  set s := V ^ 2 ^ n with hs
  have hsV : V ≤ s := by
    calc V = V ^ 1 := (pow_one V).symm
      _ ≤ V ^ 2 ^ n := pow_le_pow_right₀ hV1 (Nat.one_le_two_pow)
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 ≤ s := by linarith
  set N : ℕ := 2 * (o + 1) with hN
  have hNR : (N : ℝ) = 2 * ((o : ℝ) + 1) := by rw [hN]; push_cast; ring
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  have hNs : (N : ℝ) ≤ s := by
    have h1 := le_smoothK (o := o) hΘ hΘ2
    have hK0 : 0 ≤ smoothK o Θ := le_trans (by positivity) h1
    have h3 : smoothK o Θ ≤ smoothK o Θ / Θ := by
      rw [le_div_iff₀ hΘ]; nlinarith
    have hNV : (N : ℝ) ≤ V := by
      rw [hNR, hVdef]
      unfold smoothV
      linarith [Real.add_one_le_exp (smoothK o Θ / Θ)]
    linarith
  -- the least height, the precision and the number of generators
  have h2s : (2 : ℝ) ^ (n + 2) ≤ s := by
    have := two_pow_mul_le_pow (le_refl (1 : ℝ)) (by linarith : 8 * 1 ≤ V) n
    rw [mul_one] at this; exact this
  have hA : (baseHeight o (n + 1) : ℝ) ≤ 2 * s := by
    unfold baseHeight; push_cast
    rw [show n + 1 + 1 = n + 2 by ring]
    have : (2 : ℝ) * ((o : ℝ) + 1) = N := hNR.symm
    linarith
  have hQ := prec_succ_le hV1 n
  rw [← hs] at hQ
  have hwin2 : win V (n + 1 + 1) = (s ^ 2) ^ 2 := by
    rw [win_succ, hs, ← pow_mul, ← pow_mul]; congr 1; ring
  have hg : (gens V (n + 1) : ℝ) ≤ s + 1 := by
    unfold gens; push_cast
    rw [hwin2, Real.sqrt_sq (by positivity), Real.sqrt_sq hs0]
    linarith [Nat.floor_le hs0]
  -- `M ≤ 2(2AQ)^{g+1}` and `2AQ ≤ s⁶`
  have hA1 : (1 : ℝ) ≤ (baseHeight o (n + 1) : ℝ) := by
    have h : 1 ≤ baseHeight o (n + 1) := by unfold baseHeight; exact le_add_left (by omega)
    exact_mod_cast h
  have hQ1 : (1 : ℝ) ≤ (prec V (n + 1) : ℝ) := by
    have h : 1 ≤ prec V (n + 1) := by unfold prec; omega
    exact_mod_cast h
  have hM1 : (1 : ℝ) ≤ (smoothHeight o V (n + 1) : ℝ) := by
    have h : 1 ≤ smoothHeight o V (n + 1) := by
      have := two_mul_le_smoothHeight (o := o) (V := V) (n + 1); omega
    exact_mod_cast h
  have hspec : (smoothHeight o V (n + 1) : ℝ) ≤ 2 * (baseHeight o (n + 1) : ℝ) +
      (2 * (baseHeight o (n + 1) : ℝ) * (prec V (n + 1) : ℝ)) ^ gens V (n + 1) := by
    exact_mod_cast (smoothHeight_spec o V (n + 1)).2.1
  set A : ℝ := (baseHeight o (n + 1) : ℝ)
  set Q : ℝ := (prec V (n + 1) : ℝ)
  set g : ℕ := gens V (n + 1)
  set M : ℝ := (smoothHeight o V (n + 1) : ℝ)
  have hMle : M ≤ 2 * (2 * A * Q) ^ (g + 1) := by
    have h : M ≤ 2 * A + (2 * A * Q) ^ g := hspec
    set y : ℝ := 2 * A * Q
    have hy1 : 1 ≤ y := by nlinarith
    have h1 : 2 * A ≤ y ^ (g + 1) := le_trans (by nlinarith) (le_self_pow₀ hy1 (by omega))
    have h2 : y ^ g ≤ y ^ (g + 1) := pow_le_pow_right₀ hy1 (by omega)
    linarith
  have h2AQ : 2 * A * Q ≤ s ^ 6 := by
    have h156 : (156 : ℝ) ≤ s := by linarith
    calc 2 * A * Q ≤ 2 * (2 * s) * (39 * (s ^ 4)) :=
          mul_le_mul (by linarith) hQ (by linarith) (by positivity)
      _ = 156 * s ^ 5 := by ring
      _ ≤ s * s ^ 5 := mul_le_mul_of_nonneg_right h156 (by positivity)
      _ = s ^ 6 := by ring
  -- `7M ≤ s^{6g+7} ≤ e^{19 s log s}`
  have h7M : 7 * M ≤ Real.exp (19 * s * Real.log s) := by
    have h14 : (14 : ℝ) ≤ s := by linarith
    have hpow : (2 * A * Q) ^ (g + 1) ≤ (s ^ 6) ^ (g + 1) :=
      pow_le_pow_left₀ (by nlinarith) h2AQ _
    have h1 : 7 * M ≤ s ^ (6 * g + 7) := by
      have e : s ^ (6 * g + 7) = s * (s ^ 6) ^ (g + 1) := by
        rw [show 6 * g + 7 = 1 + 6 * (g + 1) by ring, pow_add, pow_one, pow_mul]
      rw [e]
      have : 0 ≤ (s ^ 6) ^ (g + 1) := by positivity
      nlinarith
    have h2 : s ^ (6 * g + 7) = Real.exp ((6 * g + 7 : ℕ) * Real.log s) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have h3 : ((6 * g + 7 : ℕ) : ℝ) * Real.log s ≤ 19 * s * Real.log s := by
      have hl := Real.log_nonneg hs1
      have : ((6 * g + 7 : ℕ) : ℝ) ≤ 19 * s := by push_cast; nlinarith
      exact mul_le_mul_of_nonneg_right this hl
    rw [h2] at h1
    exact h1.trans (Real.exp_le_exp.mpr h3)
  -- the window exponent
  have hdelta : (depth Θ (n + 1) - depth Θ n) * win V (n + 1) = Θ * s ^ 2 / 2 ^ (n + 2) := by
    rw [depth_succ_sub, win_succ, hs, ← pow_mul, ← pow_succ, one_div_pow]; ring
  rw [hdelta]
  have hℓ : Real.log s = 2 ^ n * Real.log V := by
    rw [hs, Real.log_pow]; push_cast; ring
  have hbud := budget (o := o) hΘ hΘ2 hs1 n hℓ
  rw [← hNR] at hbud
  have hwt := smoothWt_ge (o := o) (V := V) hΘ hΘ2 (n + 1)
  set c : ℝ := 2 + (N : ℝ) * Real.log (2 / Θ)
  set E : ℝ := Real.exp (Θ * s ^ 2 / 2 ^ (n + 2))
  set F : ℝ := Real.exp ((N : ℝ) * (19 * s * Real.log s))
  have hF : (7 * M) ^ N ≤ F := by
    have := pow_le_pow_left₀ (by linarith) h7M N
    rwa [← Real.exp_nat_mul] at this
  have hFpos : 0 < F := Real.exp_pos _
  have hcF : Real.exp c * F ≤ E := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : c + (N : ℝ) * (19 * s * Real.log s) = c + 19 * (N : ℝ) * s * Real.log s := by ring
    rw [this]; exact hbud
  have hec : Real.exp c = Real.exp 2 * (2 / Θ) ^ N := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hΘN : (Θ / 2) ^ N * (2 / Θ) ^ N = 1 := by
    rw [← mul_pow]; field_simp; simp
  have hMpos : 0 < (7 * M) ^ N := by positivity
  calc (8 : ℝ) ≤ 2 * Real.exp 2 := by linarith
    _ = 2 * (Θ / 2) ^ N * Real.exp c := by rw [hec]; linear_combination (-2 * Real.exp 2) * hΘN
    _ = 2 * (Θ / 2) ^ N * (Real.exp c * F) / F := by field_simp
    _ ≤ 2 * (Θ / 2) ^ N * E / F := by gcongr
    _ ≤ 2 * (Θ / 2) ^ N * E / (7 * M) ^ N := by gcongr
    _ = 2 * (Θ / 2) ^ N / (7 * M) ^ N * E := by ring
    _ ≤ smoothWt o Θ V (n + 1) * E := mul_le_mul_of_nonneg_right hwt (Real.exp_pos _).le

/-! ### The configuration -/

theorem smoothPt_true_re (k : ℕ) : (smoothPt o Θ V (k, true)).re = 1 / 2 + depth Θ k := by
  simp [smoothPt]

theorem smoothPt_false_re (k : ℕ) : (smoothPt o Θ V (k, false)).re = 1 / 2 - depth Θ k := by
  simp [smoothPt]

theorem smoothPt_im (kb : ℕ × Bool) :
    (smoothPt o Θ V kb).im = 2 * Real.pi * smoothHeight o V kb.1 := by
  rcases kb with ⟨k, _ | _⟩ <;> simp [smoothPt]

theorem smoothPt_injective (hΘ : 0 < Θ) : Function.Injective (smoothPt o Θ V) := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  have hre := congrArg Complex.re h
  have hd := (strictMono_depth hΘ).injective
  have h0 := depth_pos hΘ k
  have h0' := depth_pos hΘ k'
  cases b <;> cases b'
  · rw [smoothPt_false_re, smoothPt_false_re] at hre
    rw [hd (by linarith : depth Θ k = depth Θ k')]
  · rw [smoothPt_false_re, smoothPt_true_re] at hre; linarith
  · rw [smoothPt_true_re, smoothPt_false_re] at hre; linarith
  · rw [smoothPt_true_re, smoothPt_true_re] at hre
    rw [hd (by linarith : depth Θ k = depth Θ k')]

theorem reflect_smoothPt (k : ℕ) (b : Bool) :
    reflect (smoothPt o Θ V (k, b)) = smoothPt o Θ V (k, !b) := by
  apply Complex.ext <;> cases b <;> simp [reflect, smoothPt] <;> ring

variable (o V)

/-- **The configuration** `{½ ± x_k + 2πiM_k}` with multiplicity one. -/
def smoothConfig (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range (smoothPt o Θ V)
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨⟨k, b⟩, rfl⟩
    have h0 := depth_nonneg hΘ k
    have h1 := (depth_lt hΘ k).le
    cases b
    · rw [smoothPt_false_re]; constructor <;> linarith
    · rw [smoothPt_true_re]; constructor <;> linarith
  reflect_mem := by
    rintro ρ ⟨⟨k, b⟩, rfl⟩
    exact ⟨(k, !b), (reflect_smoothPt (o := o) (V := V) k b).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    refine (((Set.finite_Iic ⌊T₂⌋₊).prod (Set.finite_univ (α := Bool))).image
      (smoothPt o Θ V)).subset ?_
    rintro ρ ⟨⟨⟨k, b⟩, rfl⟩, -, hT⟩
    refine ⟨(k, b), ⟨Set.mem_Iic.mpr ?_, Set.mem_univ _⟩, rfl⟩
    rw [smoothPt_im] at hT
    have hk : (k : ℝ) ≤ smoothHeight o V k := by exact_mod_cast k_le_smoothHeight k
    have hM0 : (0 : ℝ) ≤ smoothHeight o V k := Nat.cast_nonneg _
    have : (k : ℝ) ≤ T₂ := by nlinarith [Real.pi_gt_three]
    exact Nat.le_floor this

variable {o V}

theorem gammaOf_smoothPt_true (k : ℕ) :
    gammaOf (smoothPt o Θ V (k, true)) = splinePoint (smoothHeight o V k) (depth Θ k) := by
  apply Complex.ext <;> simp [gammaOf, smoothPt, splinePoint, Complex.div_I]

theorem gammaOf_smoothPt_false (k : ℕ) :
    gammaOf (smoothPt o Θ V (k, false)) = conj (splinePoint (smoothHeight o V k) (depth Θ k)) := by
  apply Complex.ext <;> simp [gammaOf, smoothPt, splinePoint, Complex.div_I]

theorem normSq_gammaOf_smoothPt_ge (kb : ℕ × Bool) :
    (kb.1 : ℝ) ^ 2 ≤ Complex.normSq (gammaOf (smoothPt o Θ V kb)) := by
  have hre : (gammaOf (smoothPt o Θ V kb)).re = 2 * Real.pi * smoothHeight o V kb.1 := by
    rcases kb with ⟨k, _ | _⟩
    · rw [gammaOf_smoothPt_false, Complex.conj_re, splinePoint_re]
    · rw [gammaOf_smoothPt_true, splinePoint_re]
  rw [Complex.normSq_apply, hre]
  have hk : (kb.1 : ℝ) ≤ smoothHeight o V kb.1 := by exact_mod_cast k_le_smoothHeight kb.1
  have h0 : (0 : ℝ) ≤ kb.1 := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ smoothHeight o V kb.1 := Nat.cast_nonneg _
  have h1 : (kb.1 : ℝ) ≤ 2 * Real.pi * smoothHeight o V kb.1 := by nlinarith [Real.pi_gt_three]
  have h2 := mul_le_mul h1 h1 h0 (h0.trans h1)
  nlinarith [mul_self_nonneg (gammaOf (smoothPt o Θ V kb)).im]

theorem temperedConfig_smoothConfig (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (smoothConfig o V hΘ hΘ2) := by
  unfold TemperedConfig
  set e := Equiv.ofInjective (smoothPt o Θ V) (smoothPt_injective hΘ)
  show Summable fun ρ : Set.range (smoothPt o Θ V) =>
    ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  have hg : Summable fun kb : ℕ × Bool => 1 / (1 + (kb.1 : ℝ) ^ 2) := by
    refine (summable_prod_of_nonneg (fun kb => by positivity)).mpr ⟨fun k => ?_, ?_⟩
    · exact (hasSum_fintype _).summable
    · have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
        simpa [Nat.cast_add, Nat.cast_one] using this
      refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => by positivity)
        (fun k => ?_) (h1.mul_left 4)
      rw [tsum_fintype, Fintype.sum_bool]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h : 1 / (1 + (k : ℝ) ^ 2) ≤ 2 / ((k : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
      have h' : 2 / ((k : ℝ) + 1) ^ 2 = 2 * (1 / ((k : ℝ) + 1) ^ 2) := by ring
      simp only
      linarith
  simp only [Function.comp_def, e, Equiv.ofInjective_apply, Nat.cast_one]
  refine Summable.of_nonneg_of_le (fun kb => div_nonneg zero_le_one
    (by linarith [Complex.normSq_nonneg (gammaOf (smoothPt o Θ V kb))])) (fun kb => ?_) hg
  exact one_div_le_one_div_of_le (by positivity)
    (by linarith [normSq_gammaOf_smoothPt_ge (o := o) (Θ := Θ) (V := V) kb])

/-- **The traces of the tower.** `2 Re S(u) = Σ_k (e^{x_k u} 2 Re(c_k e^{iγ_k u}) +
e^{−x_k u} 2 Re(c̄_k e^{iγ_k u}))`, `γ_k = 2πM_k`. -/
theorem two_re_lagStructure_smoothConfig (ho : 3 ≤ o) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (smoothConfig o V hΘ hΘ2) (boxSpline 1 o) u).re =
      ∑' k, (Real.exp (depth Θ k * u) * (2 * (smoothCoef o Θ V k *
          cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I)).re) +
        Real.exp (-(depth Θ k * u)) * (2 * (conj (smoothCoef o Θ V k) *
          cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I)).re)) := by
  set Z := smoothConfig o V hΘ hΘ2
  have hb3 := contDiff_two_boxSpline ho
  have hbs := boxSpline_support (r := 1) one_pos o
  have hs := summable_lagStructure Z (temperedConfig_smoothConfig hΘ hΘ2) hb3 hbs u
  set e := Equiv.ofInjective (smoothPt o Θ V) (smoothPt_injective hΘ)
  set F : ℕ × Bool → ℂ := fun kb => paperFT (EF.weilTest (boxSpline 1 o) (boxSpline 1 o))
    (gammaOf (smoothPt o Θ V kb)) * cexp (I * gammaOf (smoothPt o Θ V kb) * u) with hF
  have hcomp : ∀ kb, ((Z.mult (e kb) : ℂ) * paperFT (EF.weilTest (boxSpline 1 o) (boxSpline 1 o))
      (gammaOf (e kb)) * cexp (I * gammaOf (e kb) * u)) = F kb := by
    intro kb
    simp only [Z, smoothConfig, e, Equiv.ofInjective_apply, Nat.cast_one, one_mul, hF]
  have hS : HasSum F (lagStructure Z (boxSpline 1 o) u) := by
    have h1 := ((e.hasSum_iff).mpr hs.hasSum)
    simp only [Function.comp_def, hcomp] at h1
    exact h1
  set g : ℕ → ℂ := fun k => smoothCoef o Θ V k * (Real.exp (depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I) +
    conj (smoothCoef o Θ V k) * (Real.exp (-(depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I) with hg
  have hfib : ∀ k, HasSum (fun b : Bool => F (k, b)) (g k) := by
    intro k
    have h := hasSum_fintype (fun b : Bool => F (k, b))
    rw [Fintype.sum_bool] at h
    convert h using 1
    simp only [hF, hg, gammaOf_smoothPt_true, gammaOf_smoothPt_false, paperFT_weilTest_spline ho,
      sincC_conj, map_pow, I_mul_splinePoint, I_mul_conj_splinePoint, Complex.exp_add,
      ← Complex.ofReal_exp, smoothCoef]
    ring
  have hG : HasSum g (lagStructure Z (boxSpline 1 o) u) := hS.prod_fiberwise hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simp only [Complex.reCLM_apply] at hre
  rw [← hre.tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [hg, Complex.add_re]
  rw [show smoothCoef o Θ V k * (Real.exp (depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I) =
      (Real.exp (depth Θ k * u) : ℂ) * (smoothCoef o Θ V k *
        cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I)) by ring,
    show conj (smoothCoef o Θ V k) * (Real.exp (-(depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I) =
      (Real.exp (-(depth Θ k * u)) : ℂ) * (conj (smoothCoef o Θ V k) *
        cexp (((2 * Real.pi * smoothHeight o V k * u : ℝ) : ℂ) * I)) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

end SmoothTower

open SplineTower SmoothTower in
/-- **Very smooth degrees need an attained top.** For the spline of order `o ≥ 3` and `0 < Θ ≤ ½`
there is a tempered zero configuration without real zeros whose real parts have the supremum
`½ + Θ`, not attained, with `(−1)^{o+1} 2 Re S(log d) ≥ −1` at every `d ≥ 1` whose prime factors
satisfy `p⁴ ≤ log d`. -/
theorem exists_zeroConfig_verySmooth_signed_nonattained {o : ℕ} (ho : 3 ≤ o) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ d : ℕ, d ≠ 0 → (∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) →
        -1 ≤ (-1) ^ (o + 1) * (2 * (lagStructure Z (boxSpline 1 o) (Real.log d)).re) := by
  set V : ℝ := smoothV o Θ with hVdef
  have hV := le_smoothV (o := o) hΘ hΘ2
  rw [← hVdef] at hV
  have hV1 : 1 ≤ V := by linarith
  refine ⟨smoothConfig o V hΘ hΘ2, temperedConfig_smoothConfig hΘ hΘ2, ?_, ?_, ?_,
    fun d hd hsm => ?_⟩
  · rintro ρ ⟨kb, rfl⟩
    rw [smoothPt_im]
    have := two_mul_le_smoothHeight (o := o) (V := V) kb.1
    have hM : (0 : ℝ) < smoothHeight o V kb.1 := by
      exact_mod_cast (by omega : 0 < smoothHeight o V kb.1)
    positivity
  · rintro ρ ⟨⟨k, b⟩, rfl⟩
    have h1 := depth_lt hΘ k
    have h0 := depth_nonneg hΘ k
    cases b
    · rw [smoothPt_false_re]; linarith
    · rw [smoothPt_true_re]; linarith
  · intro β hβ
    obtain ⟨k, hk⟩ := exists_depth_gt hΘ (show β - 1 / 2 < Θ by linarith)
    exact ⟨smoothPt o Θ V (k, true), ⟨(k, true), rfl⟩, by rw [smoothPt_true_re]; linarith⟩
  · set lam := Real.log d with hlam
    have hlam0 : 0 ≤ lam := Real.log_natCast_nonneg d
    rw [two_re_lagStructure_smoothConfig ho hΘ hΘ2, ← tsum_mul_left]
    obtain ⟨k, hkl, hku⟩ := exists_window (monotone_win hV1) (by rw [win_zero]; exact hlam0)
      (exists_le_win (by linarith) lam)
    set σ : ℝ := (-1) ^ (o + 1)
    have hσ : |σ| = 1 := by simp [σ]
    -- level `j` is in phase on `[0, U_{j+1}]`
    have hph : ∀ j, lam ≤ win V (j + 1) → smoothWt o Θ V j / 2 ≤
        σ * (2 * (smoothCoef o Θ V j *
          cexp (((2 * Real.pi * smoothHeight o V j * lam : ℝ) : ℂ) * I)).re) := by
      intro j hj
      have hres := norm_exp_smoothHeight_sub_one_le (o := o) hV1 j hsm hj
      have h := re_sincPow_mul_exp_ge (k := o + 1) (by omega)
        (two_mul_le_smoothHeight (o := o) (V := V) j)
        (depth_nonneg hΘ j) ((depth_lt hΘ j).le.trans hΘ2) hres
      unfold smoothWt smoothCoef
      simp only [σ]
      linarith
    have hnorm : ∀ j (c : ℂ), |σ * (2 * (c *
        cexp (((2 * Real.pi * smoothHeight o V j * lam : ℝ) : ℂ) * I)).re)| ≤ 2 * ‖c‖ := by
      intro j c
      rw [abs_mul, hσ, one_mul, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hterm : ∀ j, σ * (Real.exp (depth Θ j * lam) * (2 * (smoothCoef o Θ V j *
        cexp (((2 * Real.pi * smoothHeight o V j * lam : ℝ) : ℂ) * I)).re) +
        Real.exp (-(depth Θ j * lam)) * (2 * (conj (smoothCoef o Θ V j) *
          cexp (((2 * Real.pi * smoothHeight o V j * lam : ℝ) : ℂ) * I)).re)) =
        Real.exp (depth Θ j * lam) * (σ * (2 * (smoothCoef o Θ V j *
          cexp (((2 * Real.pi * smoothHeight o V j * lam : ℝ) : ℂ) * I)).re)) +
        Real.exp (-(depth Θ j * lam)) * (σ * (2 * (conj (smoothCoef o Θ V j) *
          cexp (((2 * Real.pi * smoothHeight o V j * lam : ℝ) : ℂ) * I)).re)) := fun j => by ring
    simp only [hterm]
    refine neg_one_le_tsum_of_resonant (Θ := Θ) (x := depth Θ) (w := smoothWt o Θ V)
      (fun j => depth_nonneg hΘ j) (fun j => (depth_lt hΘ j).le) (strictMono_depth hΘ).monotone
      smoothWt_nonneg (summable_smoothWt hΘ hΘ2) (tsum_smoothWt_le hΘ hΘ2) (fun j => hnorm j _)
      (fun j => ?_) hlam0 (hph k hku) (fun j hj => ?_) ?_
    · have h := hnorm j (conj (smoothCoef o Θ V j))
      rwa [Complex.norm_conj] at h
    · exact le_trans (by have := smoothWt_nonneg (o := o) (Θ := Θ) (V := V) j; linarith)
        (hph j (hku.trans (monotone_win hV1 (by omega))))
    · rintro n rfl
      have h8 := eight_le_smoothWt_mul_exp (o := o) hΘ hΘ2 n
      rw [← hVdef] at h8
      refine h8.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (smoothWt_nonneg _))
      exact mul_le_mul_of_nonneg_left hkl
        (by have := (strictMono_depth hΘ).monotone (Nat.le_succ n); linarith)

/-- **Very smooth degrees need an attained top** (cubic spline, from below): a lower bound on the
spline traces at the degrees `d` with `p⁴ ≤ log d` for every prime `p ∣ d` does not put the zeros of
a tempered configuration on the line without attainment. -/
theorem exists_zeroConfig_verySmooth_bddBelow_nonattained {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ d : ℕ, d ≠ 0 → (∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) →
        -1 ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := exists_zeroConfig_verySmooth_signed_nonattained le_rfl hΘ hΘ2
  refine ⟨Z, h1, h2, h3, h4, fun d hd hsm => ?_⟩
  have := h5 d hd hsm
  norm_num at this
  linarith

/-! ### Attained tops are sampled -/

/-- The degrees `2ᵃ3ᵇ` with `log(2ᵃ3ᵇ) ≥ 81` are very smooth. -/
theorem verySmooth_two_pow_mul_three_pow {a b : ℕ}
    (h81 : 81 ≤ Real.log ((2 ^ a * 3 ^ b : ℕ) : ℝ)) :
    ∀ p ∈ Nat.primeFactors (2 ^ a * 3 ^ b), ((p : ℕ) : ℝ) ^ 4 ≤
      Real.log ((2 ^ a * 3 ^ b : ℕ) : ℝ) := by
  intro p hp
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
  have h23 : p = 2 ∨ p = 3 := by
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h))
  rcases h23 with rfl | rfl
  · have : ((2 : ℕ) : ℝ) ^ 4 ≤ 81 := by norm_num
    linarith
  · have : ((3 : ℕ) : ℝ) ^ 4 ≤ 81 := by norm_num
    linarith

theorem log_two_pow_mul_three_pow (a b : ℕ) :
    Real.log ((2 ^ a * 3 ^ b : ℕ) : ℝ) = a * Real.log 2 + b * Real.log 3 := by
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- **From the very smooth degrees to two Frobenii.** At width `w`, a lower bound at the very smooth
degrees is a lower bound at every `2ᵃ3ᵇ`: beyond `log = 81` these are very smooth, and below it
`|2 Re S(u)| ≤ E e^{81|w|}`. -/
theorem bddBelow_twoThree_of_bddBelow_verySmooth {Z : ZeroConfig} (hZ : TemperedConfig Z) {w : ℝ}
    (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + w) {K : ℝ}
    (hK : ∀ d : ℕ, d ≠ 0 → (∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) (m n : ℕ) :
    -(|K| + (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp (81 * |w|)) ≤
      2 * (lagStructure Z (boxSpline 1 3) (m * Real.log 2 + n * Real.log 3)).re := by
  have hE : 0 ≤ ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = m * Real.log 2 + n * Real.log 3 := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 ≤ u := by
    rw [hu]
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    positivity
  have hEe : 0 ≤ (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp (81 * |w|) :=
    mul_nonneg hE (Real.exp_pos _).le
  rcases le_or_gt 81 u with h81 | h81
  · have hlog := log_two_pow_mul_three_pow m n
    have hd : (2 ^ m * 3 ^ n : ℕ) ≠ 0 := by positivity
    have h := hK _ hd (verySmooth_two_pow_mul_three_pow (by rw [hlog, ← hu]; exact h81))
    rw [hlog, ← hu] at h
    have := le_abs_self K
    linarith
  · have hb := abs_two_re_lagStructure_le_exp_of_width hZ hwid hu0
    have hexp : Real.exp (w * u) ≤ Real.exp (81 * |w|) := by
      refine Real.exp_le_exp.mpr ?_
      calc w * u ≤ |w| * u := mul_le_mul_of_nonneg_right (le_abs_self w) hu0
        _ ≤ |w| * 81 := mul_le_mul_of_nonneg_left h81.le (abs_nonneg w)
        _ = 81 * |w| := mul_comm _ _
    have h1 := mul_le_mul_of_nonneg_left hexp hE
    have h2 := (abs_le.mp hb).1
    have := abs_nonneg K
    linarith

/-- **The very smooth degrees sample every attained top.** A lower bound on the spline traces at the
degrees `d` with `p⁴ ≤ log d` for every prime `p ∣ d` puts every zero of a tempered configuration
without real zeros on the line, provided `sup Re ρ` is attained (`TwoFrobeniiSuffice`). -/
theorem onLine_of_bddBelow_verySmooth_of_max (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ d : ℕ, d ≠ 0 → (∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + (ρ₀.re - 1 / 2) := fun ρ hρ => by
    have := hmax ρ hρ; linarith
  refine onLine_of_bddBelow_twoPrimes_of_max Nat.prime_two Nat.prime_three (by norm_num) Z hZ
    hnoreal hρ₀ hmax fun m n => ?_
  simp only [Nat.cast_ofNat]
  exact bddBelow_twoThree_of_bddBelow_verySmooth hZ hwid hK m n

/-! ### For `ζ`: the Stepanov bound at the very smooth degrees -/

theorem re_le_of_mem_zetaZeroConfig' {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ρ.re ≤ 1 / 2 + 1 / 2 := by
  have := (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
    hρ).2.2
  linarith

/-- **A Stepanov bound at the very smooth degrees gives the abscissa law.** -/
theorem asymptoticAbscissaLaw_of_bddBelow_verySmooth {K : ℝ}
    (hK : ∀ d : ℕ, d ≠ 0 → (∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log d)).re) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_bddBelow_twoPrimes Nat.prime_two Nat.prime_three (by norm_num)
    fun m n => ?_
  simp only [Nat.cast_ofNat]
  exact bddBelow_twoThree_of_bddBelow_verySmooth temperedConfig_zetaZeroConfig
    (fun _ hρ => re_le_of_mem_zetaZeroConfig' hρ) hK m n

/-- **RH is the approach to the line plus a Stepanov bound at the very smooth degrees.** Although
every prime eventually divides a very smooth degree, these degrees give only the abscissa law. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_bddBelow_verySmooth :
    RiemannHypothesis ↔ _root_.RHTower.BacklundConverse.ZerosApproachLine ∧ ∃ K : ℝ,
      ∀ d : ℕ, d ≠ 0 → (∀ p ∈ d.primeFactors, (p : ℝ) ^ 4 ≤ Real.log d) →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log d)).re := by
  rw [_root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw]
  refine ⟨fun ⟨hZ, hA⟩ => ⟨hZ, ?_⟩, fun ⟨hZ, K, hK⟩ =>
    ⟨hZ, asymptoticAbscissaLaw_of_bddBelow_verySmooth hK⟩⟩
  have hRH :=
    _root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZ, hA⟩
  exact ⟨_, fun d _ _ =>
    neg_le_of_abs_le (abs_two_re_lagStructure_le_of_RH hRH (Real.log_natCast_nonneg d))⟩

end GaloisForLFunctions.SurfaceOfSpecZ
