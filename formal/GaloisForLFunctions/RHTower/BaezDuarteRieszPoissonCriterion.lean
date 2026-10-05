import GaloisForLFunctions.RHTower.RieszFunctionMellinCriterion
import GaloisForLFunctions.RHTower.BaezDuarteWaveletCriterion
import GaloisForLFunctions.RHTower.MobiusRHDecayMoment
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionExactOrder

/-!
# The Báez--Duarte criterion through the Riesz series

The Báez--Duarte coefficients
`c_k = Σ_{j ≤ k} (-1)^j C(k,j)/ζ(2j+2) = Σ_n μ(n) n^{-2}(1 - n^{-2})^k` are the Taylor data of
the Riesz series under Poissonization:
`R(x) = Σ_n μ(n) n^{-2} e^{-x/n²} = e^{-x} Σ_k c_k x^k / k!`, since
`Σ_k e^{-x} x^k (1 - u)^k / k! = e^{-xu}`.  Poisson averages preserve power decay:
`Σ_k e^{-x} x^k/k! · (k+1)^{-β} ≤ 2x^{-β}` for `0 ≤ β ≤ 1`, from `t^{-β} ≤ 1 + t^{-1}` and
`Σ_k e^{-x} x^k / (k+1)! = (1 - e^{-x})/x`.  So `c_k = O(k^{-β})` gives `R(x) = O(x^{-β})`, and the
Mellin continuation of `R` puts every zeta zero at `Re ρ ≤ 2 - 2β`.

With `β = 3/4 - ε` this is the converse half of the Báez--Duarte criterion; the forward half
(RH ⇒ `c_k = O(k^{-3/4+ε})`) is the weighted-moment scale law, so RH holds if and only if
`c_{k+1} = O(k^{-3/4+ε})` for every `ε > 0`.
-/

open Filter

namespace RHTower

noncomputable section

/-! ## The real Báez--Duarte coefficients -/

/-- The real summand `μ(n) n^{-2} (1 - n^{-2})^k`. -/
def bdRealTerm (k n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * ((n : ℝ) ^ 2)⁻¹ * (1 - ((n : ℝ) ^ 2)⁻¹) ^ k

/-- The real Báez--Duarte coefficient `c_k = Σ_n μ(n) n^{-2} (1 - n^{-2})^k`. -/
def bdReal (k : ℕ) : ℝ := ∑' n : ℕ, bdRealTerm k n

theorem inv_natCast_sq_le_one (n : ℕ) : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)

theorem abs_bdRealTerm_le (k n : ℕ) : |bdRealTerm k n| ≤ ((n : ℝ) ^ 2)⁻¹ := by
  unfold bdRealTerm
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hu0 : 0 ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
  have hu1 := inv_natCast_sq_le_one n
  have hpow : |(1 - ((n : ℝ) ^ 2)⁻¹) ^ k| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [abs_mul, abs_mul, abs_of_nonneg hu0]
  calc |(ArithmeticFunction.moebius n : ℝ)| * ((n : ℝ) ^ 2)⁻¹ * |(1 - ((n : ℝ) ^ 2)⁻¹) ^ k|
      ≤ 1 * ((n : ℝ) ^ 2)⁻¹ * 1 := by gcongr
    _ = ((n : ℝ) ^ 2)⁻¹ := by ring

theorem summable_bdRealTerm (k : ℕ) : Summable (bdRealTerm k) :=
  Summable.of_norm_bounded summable_natCast_sq_inv fun n => by
    rw [Real.norm_eq_abs]; exact abs_bdRealTerm_le k n

theorem abs_bdReal_le (k : ℕ) : |bdReal k| ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
  unfold bdReal
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_bdRealTerm k).norm).trans ?_
  exact (summable_bdRealTerm k).norm.tsum_le_tsum (fun n => by
    rw [Real.norm_eq_abs]; exact abs_bdRealTerm_le k n) summable_natCast_sq_inv

/-- The corpus coefficient `bdCoeff k` is the real coefficient `c_k`. -/
theorem bdCoeff_eq_ofReal_bdReal (k : ℕ) : bdCoeff k = ((bdReal k : ℝ) : ℂ) := by
  rw [bdCoeff_eq_tsum, bdReal, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  simp [bdMobiusTerm, bdRealTerm]

theorem norm_bdCoeff_eq_abs_bdReal (k : ℕ) : ‖bdCoeff k‖ = |bdReal k| := by
  rw [bdCoeff_eq_ofReal_bdReal, Complex.norm_real, Real.norm_eq_abs]

/-! ## Poissonization -/

/-- The Poisson weight `e^{-x} x^k / k!`. -/
def poissonProbWeight (x : ℝ) (k : ℕ) : ℝ := Real.exp (-x) * (x ^ k / (k.factorial : ℝ))

theorem poissonProbWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ poissonProbWeight x k := by
  unfold poissonProbWeight; positivity

theorem summable_poissonProbWeight (x : ℝ) : Summable (poissonProbWeight x) :=
  (Real.summable_pow_div_factorial x).mul_left _

theorem tsum_poissonProbWeight_mul_pow (x u : ℝ) :
    ∑' k : ℕ, poissonProbWeight x k * u ^ k = Real.exp (-(x * (1 - u))) := by
  have h : ∀ k : ℕ, poissonProbWeight x k * u ^ k =
      Real.exp (-x) * ((x * u) ^ k / (k.factorial : ℝ)) := fun k => by
    unfold poissonProbWeight; rw [mul_pow]; ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_pow_div_factorial_eq_exp, ← Real.exp_add]
  ring_nf

theorem tsum_poissonProbWeight (x : ℝ) : ∑' k : ℕ, poissonProbWeight x k = 1 := by
  have := tsum_poissonProbWeight_mul_pow x 1
  simp only [one_pow, mul_one, sub_self, mul_zero, neg_zero, Real.exp_zero] at this
  exact this

theorem summable_norm_poissonProbWeight (x : ℝ) : Summable fun k => ‖poissonProbWeight x k‖ := by
  refine ((Real.summable_pow_div_factorial |x|).mul_left (Real.exp (-x))).congr fun k => ?_
  unfold poissonProbWeight
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (k.factorial : ℝ))]

/-- **Poissonization.**  The Riesz series is the Poisson transform of the Báez--Duarte
coefficients: `R(x) = e^{-x} Σ_k c_k x^k / k!`, because
`Σ_k e^{-x} x^k (1 - u)^k / k! = e^{-xu}`. -/
theorem rieszSeries_eq_tsum_poissonProbWeight_mul_bdReal (x : ℝ) :
    rieszSeries x = ∑' k : ℕ, poissonProbWeight x k * bdReal k := by
  set D : ℕ → ℕ → ℝ := fun k n => poissonProbWeight x k * bdRealTerm k n with hD
  have hmaj : Summable fun p : ℕ × ℕ => ‖poissonProbWeight x p.1‖ * ((p.2 : ℝ) ^ 2)⁻¹ :=
    summable_mul_of_summable_norm (f := fun k => ‖poissonProbWeight x k‖)
      (g := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) (by simpa using summable_norm_poissonProbWeight x)
      (by simp)
  have hsum : Summable (Function.uncurry D) := by
    refine Summable.of_norm_bounded hmaj fun p => ?_
    simp only [Function.uncurry, hD, norm_mul, Real.norm_eq_abs (bdRealTerm _ _)]
    exact mul_le_mul_of_nonneg_left (abs_bdRealTerm_le _ _) (norm_nonneg _)
  have hswap := hsum.tsum_comm
  have hinner_k : ∀ n : ℕ, ∑' k : ℕ, D k n = rieszTerm x n := by
    intro n
    have h : ∀ k : ℕ, D k n = ((ArithmeticFunction.moebius n : ℝ) * ((n : ℝ) ^ 2)⁻¹) *
        (poissonProbWeight x k * (1 - ((n : ℝ) ^ 2)⁻¹) ^ k) := fun k => by
      simp only [hD, bdRealTerm]; ring
    simp_rw [h]
    rw [tsum_mul_left, tsum_poissonProbWeight_mul_pow, rieszTerm, rieszExpWeight]
    ring_nf
  have hinner_n : ∀ k : ℕ, ∑' n : ℕ, D k n = poissonProbWeight x k * bdReal k := by
    intro k
    simp only [hD]
    rw [tsum_mul_left, bdReal]
  rw [rieszSeries]
  simp_rw [← hinner_k]
  rw [hswap]
  exact tsum_congr hinner_n

/-! ## Poisson averages of powers -/

theorem tsum_poissonProbWeight_div_succ {x : ℝ} (hx : 0 < x) :
    ∑' k : ℕ, poissonProbWeight x k / ((k : ℝ) + 1) = (1 - Real.exp (-x)) / x := by
  have hs := Real.summable_pow_div_factorial x
  have h0 := hs.tsum_eq_zero_add
  rw [tsum_pow_div_factorial_eq_exp] at h0
  have hk : ∀ k : ℕ, x ^ (k + 1) / ((k + 1).factorial : ℝ) =
      x * (x ^ k / (k.factorial : ℝ) / ((k : ℝ) + 1)) := fun k => by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  simp_rw [hk] at h0
  rw [tsum_mul_left] at h0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h0
  have hT : ∑' k : ℕ, x ^ k / (k.factorial : ℝ) / ((k : ℝ) + 1) = (Real.exp x - 1) / x := by
    rw [eq_div_iff hx.ne']; linarith
  have hw : ∀ k : ℕ, poissonProbWeight x k / ((k : ℝ) + 1) =
      Real.exp (-x) * (x ^ k / (k.factorial : ℝ) / ((k : ℝ) + 1)) := fun k => by
    unfold poissonProbWeight; ring
  simp_rw [hw]
  rw [tsum_mul_left, hT, mul_div_assoc', mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    mul_one]

theorem rpow_neg_succ_le {x β : ℝ} (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (k : ℕ) :
    ((k : ℝ) + 1) ^ (-β) ≤ x ^ (-β) * (1 + x / ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set t : ℝ := ((k : ℝ) + 1) / x with ht
  have ht0 : 0 < t := div_pos hk hx
  have hkt : (k : ℝ) + 1 = x * t := by rw [ht]; field_simp
  have htb : t ^ (-β) ≤ 1 + x / ((k : ℝ) + 1) := by
    have hinv : x / ((k : ℝ) + 1) = t⁻¹ := by rw [ht, inv_div]
    rw [hinv]
    rcases le_or_gt 1 t with h1 | h1
    · have := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith : -β ≤ 0)
      have : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
      linarith
    · have h2 : t ^ (-β) ≤ t ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 h1.le (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith
  calc ((k : ℝ) + 1) ^ (-β) = (x * t) ^ (-β) := by rw [hkt]
    _ = x ^ (-β) * t ^ (-β) := Real.mul_rpow hx.le ht0.le
    _ ≤ x ^ (-β) * (1 + x / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left htb (Real.rpow_nonneg hx.le _)

/-- **Poisson averages preserve power decay.**  `Σ_k e^{-x} x^k/k! · (k+1)^{-β} ≤ 2 x^{-β}` for
`x > 0`, `0 ≤ β ≤ 1`. -/
theorem tsum_poissonProbWeight_mul_rpow_le {x β : ℝ} (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∑' k : ℕ, poissonProbWeight x k * ((k : ℝ) + 1) ^ (-β) ≤ 2 * x ^ (-β) := by
  have hw0 := poissonProbWeight_nonneg hx.le
  have hS := summable_poissonProbWeight x
  have hS1 : Summable fun k : ℕ => poissonProbWeight x k / ((k : ℝ) + 1) :=
    hS.of_nonneg_of_le (fun k => div_nonneg (hw0 k) (by positivity)) fun k =>
      div_le_self (hw0 k) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hR : Summable fun k : ℕ => poissonProbWeight x k * (x ^ (-β) * (1 + x / ((k : ℝ) + 1))) := by
    have : Summable fun k : ℕ => x ^ (-β) * (poissonProbWeight x k + x * (poissonProbWeight x k /
        ((k : ℝ) + 1))) := ((hS.add (hS1.mul_left x)).mul_left _)
    refine this.congr fun k => ?_
    ring
  have hL : Summable fun k : ℕ => poissonProbWeight x k * ((k : ℝ) + 1) ^ (-β) :=
    hS.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (Real.rpow_nonneg (by positivity) _))
      fun k => mul_le_of_le_one_right (hw0 k) (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (by linarith))
  calc ∑' k : ℕ, poissonProbWeight x k * ((k : ℝ) + 1) ^ (-β)
      ≤ ∑' k : ℕ, poissonProbWeight x k * (x ^ (-β) * (1 + x / ((k : ℝ) + 1))) :=
        hL.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
          (rpow_neg_succ_le hx hβ0 hβ1 k) (hw0 k)) hR
    _ = x ^ (-β) * (∑' k : ℕ, poissonProbWeight x k +
          x * ∑' k : ℕ, poissonProbWeight x k / ((k : ℝ) + 1)) := by
        rw [← tsum_mul_left, ← hS.tsum_add (hS1.mul_left x), ← tsum_mul_left]
        refine tsum_congr fun k => ?_
        ring
    _ = x ^ (-β) * (1 + (1 - Real.exp (-x))) := by
        rw [tsum_poissonProbWeight, tsum_poissonProbWeight_div_succ hx]; field_simp
    _ ≤ 2 * x ^ (-β) := by
        have := Real.exp_pos (-x)
        have := Real.rpow_nonneg hx.le (-β)
        nlinarith

/-! ## Báez--Duarte decay controls the Riesz series -/

/-- **Coefficient decay passes to the Riesz series.**  If `|c_k| ≤ C (k+1)^{-β}` for all `k`,
`0 ≤ β ≤ 1`, then `|R(x)| ≤ 2C x^{-β}` for all `x > 0`. -/
theorem abs_rieszSeries_le_of_bdReal_le {C β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hc : ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (-β)) {x : ℝ} (hx : 0 < x) :
    |rieszSeries x| ≤ 2 * C * x ^ (-β) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hc 0)
    simpa using this
  have hw0 := poissonProbWeight_nonneg hx.le
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  have hsumA : Summable fun k : ℕ => |poissonProbWeight x k * bdReal k| := by
    refine ((summable_poissonProbWeight x).mul_right Z).of_nonneg_of_le (fun k => abs_nonneg _)
      fun k => ?_
    rw [abs_mul, abs_of_nonneg (hw0 k)]
    exact mul_le_mul_of_nonneg_left (abs_bdReal_le k) (hw0 k)
  have hsumB : Summable fun k : ℕ => poissonProbWeight x k * (C * ((k : ℝ) + 1) ^ (-β)) := by
    refine ((summable_poissonProbWeight x).mul_right C).of_nonneg_of_le
      (fun k => mul_nonneg (hw0 k) (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)))
      fun k => ?_
    rw [mul_comm C]
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hC
    exact mul_le_of_le_one_right (hw0 k) (Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (by linarith))
  rw [rieszSeries_eq_tsum_poissonProbWeight_mul_bdReal, ← Real.norm_eq_abs]
  calc ‖∑' k : ℕ, poissonProbWeight x k * bdReal k‖
      ≤ ∑' k : ℕ, |poissonProbWeight x k * bdReal k| := by
        refine (norm_tsum_le_tsum_norm ?_).trans_eq rfl
        simpa only [Real.norm_eq_abs] using hsumA
    _ ≤ ∑' k : ℕ, poissonProbWeight x k * (C * ((k : ℝ) + 1) ^ (-β)) :=
        hsumA.tsum_le_tsum (fun k => by
          rw [abs_mul, abs_of_nonneg (hw0 k)]
          exact mul_le_mul_of_nonneg_left (hc k) (hw0 k)) hsumB
    _ = C * ∑' k : ℕ, poissonProbWeight x k * ((k : ℝ) + 1) ^ (-β) := by
        rw [← tsum_mul_left]; refine tsum_congr fun k => ?_; ring
    _ ≤ C * (2 * x ^ (-β)) :=
        mul_le_mul_of_nonneg_left (tsum_poissonProbWeight_mul_rpow_le hx hβ0 hβ1) hC
    _ = 2 * C * x ^ (-β) := by ring

/-- **Báez--Duarte decay pushes zeta zeros left.**  If `|c_k| ≤ C (k+1)^{-β}` for all `k`,
`0 ≤ β ≤ 1`, then every zeta zero has `Re ρ ≤ 2 - 2β`. -/
theorem zetaZeroAbscissa_le_of_bdReal_le {C β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hc : ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (-β)) :
    zetaZeroAbscissa ≤ 2 - 2 * β := by
  by_contra hcon
  obtain ⟨ρ, hzero, hρ⟩ := exists_zetaZero_lt_re (not_le.mp hcon)
  exact riemannZeta_ne_zero_of_rieszSeries_le (β := β) (C := 2 * C) (X := 1)
    (fun x hx => abs_rieszSeries_le_of_bdReal_le hβ0 hβ1 hc (by linarith)) hρ hzero

/-- Shifted coefficient bounds `|c_{k+1}| ≤ C k^{-β}` (`k ≥ 1`) become bounds on every `c_j`. -/
theorem exists_abs_bdReal_le_of_shifted {C β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : ∀ k : ℕ, 1 ≤ k → ‖bdCoeff (k + 1)‖ ≤ C * (k : ℝ) ^ (-β)) :
    ∃ C' : ℝ, ∀ j : ℕ, |bdReal j| ≤ C' * ((j : ℝ) + 1) ^ (-β) := by
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (h 1 le_rfl)
    simpa using this
  refine ⟨max (3 * C) (2 * Z), fun j => ?_⟩
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rcases lt_or_ge j 2 with hj | hj
  · have hpow : (1 / 2 : ℝ) ≤ ((j : ℝ) + 1) ^ (-β) := by
      have hj' : (j : ℝ) + 1 ≤ 2 := by
        have : (j : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hj
        linarith
      calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (-β) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ ((j : ℝ) + 1) ^ (-β) :=
            Real.rpow_le_rpow_of_nonpos hj1 hj' (by linarith)
    calc |bdReal j| ≤ Z := abs_bdReal_le j
      _ = 2 * Z * (1 / 2) := by ring
      _ ≤ max (3 * C) (2 * Z) * ((j : ℝ) + 1) ^ (-β) :=
          mul_le_mul (le_max_right _ _) hpow (by norm_num) (le_trans (by positivity)
            (le_max_right _ _))
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : 1 ≤ k := by omega
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hbd := h k hk
    rw [norm_bdCoeff_eq_abs_bdReal] at hbd
    have hcmp : (k : ℝ) ^ (-β) ≤ 3 * (((k + 1 : ℕ) : ℝ) + 1) ^ (-β) := by
      push_cast
      have h3 : ((k : ℝ) + 1 + 1) / 3 ≤ k := by linarith
      calc (k : ℝ) ^ (-β) ≤ (((k : ℝ) + 1 + 1) / 3) ^ (-β) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith)
        _ = 3 ^ β * ((k : ℝ) + 1 + 1) ^ (-β) := by
            rw [Real.div_rpow (by positivity) (by norm_num),
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
            field_simp
        _ ≤ 3 * ((k : ℝ) + 1 + 1) ^ (-β) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
            calc (3 : ℝ) ^ β ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
              _ = 3 := Real.rpow_one 3
    calc |bdReal (k + 1)| ≤ C * (k : ℝ) ^ (-β) := hbd
      _ ≤ C * (3 * (((k + 1 : ℕ) : ℝ) + 1) ^ (-β)) := mul_le_mul_of_nonneg_left hcmp hC
      _ = 3 * C * (((k + 1 : ℕ) : ℝ) + 1) ^ (-β) := by ring
      _ ≤ max (3 * C) (2 * Z) * (((k + 1 : ℕ) : ℝ) + 1) ^ (-β) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)

/-- **The converse Báez--Duarte criterion.**  If `c_{k+1} = O(k^{-3/4+ε})` for every `ε > 0`,
the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_bdCoeff_decay
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖bdCoeff (k + 1)‖ ≤ C * (k : ℝ) ^ (-(3 : ℝ) / 4 + ε)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_zetaZeroAbscissa_eq_half
    (le_antisymm ?_ half_le_zetaZeroAbscissa)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C, hC⟩ := h δ hδ0
  have hC' : ∀ k : ℕ, 1 ≤ k → ‖bdCoeff (k + 1)‖ ≤ C * (k : ℝ) ^ (-(3 / 4 - δ)) := by
    intro k hk
    rw [show -(3 / 4 - δ) = -(3 : ℝ) / 4 + δ by ring]
    exact hC k hk
  obtain ⟨C', hC''⟩ := exists_abs_bdReal_le_of_shifted (β := 3 / 4 - δ) (by linarith)
    (by linarith) hC'
  have := zetaZeroAbscissa_le_of_bdReal_le (by linarith) (by linarith) hC''
  linarith

/-- **The Báez--Duarte criterion.**  The Riemann hypothesis holds if and only if
`c_{k+1} = O(k^{-3/4+ε})` for every `ε > 0`, where `c_k = Σ_{j ≤ k} (-1)^j C(k,j)/ζ(2j+2)`. -/
theorem riemannHypothesis_iff_bdCoeff_decay :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖bdCoeff (k + 1)‖ ≤ C * (k : ℝ) ^ (-(3 : ℝ) / 4 + ε) := by
  constructor
  · intro hRH
    exact bdCoeff_decay_of_weightedMoments fun α hα0 hα =>
      weightedMertensMoment_of_riemannHypothesis hRH hα0 hα
  · intro h
    refine riemannHypothesis_of_bdCoeff_decay fun ε hε => ?_
    obtain ⟨C, _, hC⟩ := h ε hε
    exact ⟨C, hC⟩

end

end RHTower
