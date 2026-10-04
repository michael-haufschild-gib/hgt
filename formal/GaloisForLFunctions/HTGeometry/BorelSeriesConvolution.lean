import GaloisForLFunctions.HTGeometry.OddEvenFactorialSeriesCalculus
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus

/-!
# Borel series and their Volterra convolutions

For coefficients with a geometric bound `|a_n| ≤ M R^n` the Borel series
`B_a(t) = Σ_n a_n t^n/n!` converges absolutely at every real clock, is differentiable with
`B_a' = B_{a(·+1)}`, and the Volterra convolution of two Borel series is the Borel series of the
shifted Cauchy product:

```text
∫_0^t B_a(t-s) B_b(s) ds = Σ_{n ≥ 0} (Σ_{i+j=n} a_i b_j) t^{n+1}/(n+1)! .
```

The proof is the Beta integral `∫_0^t s^p/p! (t-s)^q/q! ds = t^{p+q+1}/(p+q+1)!`, dominated
termwise integration over `ℕ × ℕ`, and regrouping along antidiagonals.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The divided power `t^n/n!`. -/
def dividedPowerFn (n : ℕ) (t : ℝ) : ℝ := t ^ n / (n.factorial : ℝ)

theorem continuous_dividedPowerFn (n : ℕ) : Continuous (dividedPowerFn n) := by
  unfold dividedPowerFn; fun_prop

theorem hasDerivAt_dividedPowerFn_succ (n : ℕ) (t : ℝ) :
    HasDerivAt (dividedPowerFn (n + 1)) (dividedPowerFn n t) t := by
  have h := (hasDerivAt_pow (n + 1) t).div_const ((n + 1).factorial : ℝ)
  have e : ((n + 1 : ℕ) : ℝ) * t ^ (n + 1 - 1) / ((n + 1).factorial : ℝ) = dividedPowerFn n t := by
    unfold dividedPowerFn
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [e] at h
  exact h

theorem dividedPowerFn_zero_left (n : ℕ) : dividedPowerFn n 0 = if n = 0 then 1 else 0 := by
  unfold dividedPowerFn
  rcases n with _ | n <;> simp

theorem abs_dividedPowerFn (n : ℕ) (t : ℝ) : |dividedPowerFn n t| = dividedPowerFn n |t| := by
  unfold dividedPowerFn
  rw [abs_div, abs_pow, Nat.abs_cast]

/-- **Beta integral.**  `∫_0^t s^p/p! (t-s)^q/q! ds = t^{p+q+1}/(p+q+1)!`. -/
theorem integral_dividedPowerFn_mul (p q : ℕ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, dividedPowerFn p s * dividedPowerFn q (t - s) =
      dividedPowerFn (p + q + 1) t := by
  induction q generalizing p with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun x _ => hasDerivAt_dividedPowerFn_succ p x)
      ((continuous_dividedPowerFn p).intervalIntegrable 0 t)
    have h0 : dividedPowerFn (p + 1) 0 = 0 := by unfold dividedPowerFn; simp
    rw [h0, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [dividedPowerFn]
  | succ q ih =>
    have hu : ∀ x, HasDerivAt (fun s => dividedPowerFn (q + 1) (t - s))
        (-dividedPowerFn q (t - x)) x := by
      intro x
      have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) x := (hasDerivAt_id' x).const_sub t
      have h := (hasDerivAt_dividedPowerFn_succ q (t - x)).comp x h2
      rw [mul_neg_one] at h
      exact h
    have hcont := continuous_dividedPowerFn
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := 0) (b := t)
      (u := fun s => dividedPowerFn (q + 1) (t - s)) (v := dividedPowerFn (p + 1))
      (u' := fun s => -dividedPowerFn q (t - s)) (v' := dividedPowerFn p)
      ((hcont (q + 1)).comp (continuous_const.sub continuous_id)).continuousOn
      (hcont (p + 1)).continuousOn (fun x _ => hu x)
      (fun x _ => hasDerivAt_dividedPowerFn_succ p x)
      (((hcont q).comp (continuous_const.sub continuous_id)).neg.intervalIntegrable 0 t)
      ((hcont p).intervalIntegrable 0 t)
    have h0 : ∀ n, dividedPowerFn (n + 1) 0 = 0 := fun n => by unfold dividedPowerFn; simp
    simp only [sub_self, h0, mul_zero, zero_mul, sub_zero] at h
    have hneg : (∫ x in (0 : ℝ)..t, -dividedPowerFn q (t - x) * dividedPowerFn (p + 1) x) =
        -∫ x in (0 : ℝ)..t, dividedPowerFn (p + 1) x * dividedPowerFn q (t - x) := by
      rw [← intervalIntegral.integral_neg]
      congr 1; funext x; ring
    have h' : (∫ x in (0 : ℝ)..t, dividedPowerFn (q + 1) (t - x) * dividedPowerFn p x) =
        ∫ x in (0 : ℝ)..t, dividedPowerFn (p + 1) x * dividedPowerFn q (t - x) := by
      linarith [h, hneg]
    calc (∫ s in (0 : ℝ)..t, dividedPowerFn p s * dividedPowerFn (q + 1) (t - s)) =
        ∫ s in (0 : ℝ)..t, dividedPowerFn (q + 1) (t - s) * dividedPowerFn p s := by
          congr 1; funext s; ring
      _ = ∫ s in (0 : ℝ)..t, dividedPowerFn (p + 1) s * dividedPowerFn q (t - s) := h'
      _ = dividedPowerFn (p + q + 1 + 1) t := by
          rw [ih (p + 1)]; congr 1; ring

/-! ## Borel series -/

/-- The Borel series `Σ_n a_n t^n/n!`. -/
def borelSeries (a : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, a n * dividedPowerFn n t

theorem norm_borelTerm_le {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    {t T : ℝ} (ht : |t| ≤ T) (n : ℕ) :
    ‖a n * dividedPowerFn n t‖ ≤ M * dividedPowerFn n (R * T) := by
  have hM : 0 ≤ M * R ^ n := (abs_nonneg _).trans (ha n)
  rw [Real.norm_eq_abs, abs_mul, abs_dividedPowerFn]
  unfold dividedPowerFn
  rw [mul_pow, mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right
    (by exact_mod_cast Nat.factorial_pos n), ← mul_assoc]
  exact mul_le_mul (ha n) (pow_le_pow_left₀ (abs_nonneg t) ht n) (by positivity) hM

theorem summable_dividedPowerFn (x : ℝ) : Summable (fun n => dividedPowerFn n x) := by
  unfold dividedPowerFn
  exact Real.summable_pow_div_factorial x

theorem summable_borelTerm {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (t : ℝ) : Summable (fun n => a n * dividedPowerFn n t) :=
  ((summable_dividedPowerFn (R * |t|)).mul_left M).of_norm_bounded
    fun n => norm_borelTerm_le ha le_rfl n

/-- `B_a' = B_{a(·+1)}`. -/
theorem hasDerivAt_borelSeries {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (t : ℝ) :
    HasDerivAt (borelSeries a) (borelSeries (fun n => a (n + 1)) t) t := by
  set T := |t| + 1
  have hsplit : borelSeries a = fun y => a 0 + ∑' n : ℕ, a (n + 1) * dividedPowerFn (n + 1) y := by
    funext y
    unfold borelSeries
    rw [(summable_borelTerm ha y).tsum_eq_zero_add]
    simp [dividedPowerFn]
  rw [hsplit]
  have ha' := ha.shift
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      HasDerivAt (fun y => a (n + 1) * dividedPowerFn (n + 1) y)
        (a (n + 1) * dividedPowerFn n y) y :=
    fun n y _ => (hasDerivAt_dividedPowerFn_succ n y).const_mul (a (n + 1))
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      ‖a (n + 1) * dividedPowerFn n y‖ ≤ M * R * dividedPowerFn n (R * T) := by
    intro n y hy
    have hy' : |y| ≤ T := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy; exact hy.le
    exact norm_borelTerm_le ha' hy' n
  have hs0 : Summable (fun n : ℕ => a (n + 1) * dividedPowerFn (n + 1) (0 : ℝ)) := by
    simp [dividedPowerFn]
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_dividedPowerFn (R * T)).mul_left (M * R)) Metric.isOpen_ball
    (convex_ball (0 : ℝ) T).isPreconnected hderiv hbound (Metric.mem_ball_self (by positivity))
    hs0 (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; simp only [T]; linarith)
  exact h.const_add (a 0)

theorem continuous_borelSeries {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R) :
    Continuous (borelSeries a) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_borelSeries ha t).continuousAt

theorem borelSeries_zero (a : ℕ → ℝ) : borelSeries a 0 = a 0 := by
  unfold borelSeries
  rw [tsum_eq_single 0]
  · simp [dividedPowerFn]
  · intro n hn; simp [dividedPowerFn, hn]

/-! ## Volterra convolution -/

/-- Shifted Cauchy-product coefficients: `c_0 = 0`, `c_{n+1} = Σ_{i+j=n} a_i b_j`. -/
def borelConvCoeff (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2

theorem geometricCoeffBound_borelConvCoeff {a b : ℕ → ℝ} {M M' R : ℝ}
    (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R) (hR : 0 < R) :
    GeometricCoeffBound (borelConvCoeff a b) (M * M' / (2 * R)) (2 * R) := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  have hM' : 0 ≤ M' := by have := (abs_nonneg _).trans (hb 0); simpa using this
  intro n
  rcases n with _ | n
  · simp [borelConvCoeff]; positivity
  · simp only [borelConvCoeff]
    have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal n, |a ij.1 * b ij.2| ≤ M * M' * R ^ n := by
      intro ij hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      rw [abs_mul]
      calc |a ij.1| * |b ij.2| ≤ (M * R ^ ij.1) * (M' * R ^ ij.2) :=
            mul_le_mul (ha _) (hb _) (abs_nonneg _) (by positivity)
        _ = M * M' * R ^ n := by rw [← hij, pow_add]; ring
    calc |∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2| ≤
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, |a ij.1 * b ij.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, M * M' * R ^ n := Finset.sum_le_sum hterm
      _ = (n + 1) * (M * M' * R ^ n) := by
          rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring
      _ ≤ 2 ^ n * (M * M' * R ^ n) := by
          gcongr
          have h := Nat.lt_two_pow_self (n := n)
          exact_mod_cast h
      _ = M * M' / (2 * R) * (2 * R) ^ (n + 1) := by
          field_simp; ring

/-- **Volterra convolution of Borel series.**
`∫_0^t B_a(t-s) B_b(s) ds = B_{c}(t)` with `c` the shifted Cauchy product. -/
theorem volterraConv_borelSeries {a b : ℕ → ℝ} {M M' R : ℝ} (ha : GeometricCoeffBound a M R)
    (hb : GeometricCoeffBound b M' R) (hR : 0 < R) (t : ℝ) :
    volterraConv (borelSeries a) (borelSeries b) t = borelSeries (borelConvCoeff a b) t := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  have hM' : 0 ≤ M' := by have := (abs_nonneg _).trans (hb 0); simpa using this
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = |t| := ⟨_, rfl⟩
  -- termwise integration over `ℕ × ℕ`
  set F : ℕ × ℕ → ℝ → ℝ := fun ij s =>
    a ij.1 * dividedPowerFn ij.1 (t - s) * (b ij.2 * dividedPowerFn ij.2 s) with hF
  have hbound_s : ∀ ij : ℕ × ℕ, ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖F ij s‖ ≤ M * dividedPowerFn ij.1 (R * T) * (M' * dividedPowerFn ij.2 (R * T)) := by
    intro ij s hs
    have hs' : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
    have h1 : |t - s| ≤ T := by
      rcases le_total 0 t with h | h
      · rw [Set.uIcc_of_le h] at hs'; rw [abs_le]; rw [hT, abs_of_nonneg h]
        constructor <;> linarith [hs'.1, hs'.2]
      · rw [Set.uIcc_of_ge h] at hs'; rw [abs_le]; rw [hT, abs_of_nonpos h]
        constructor <;> linarith [hs'.1, hs'.2]
    have h2 : |s| ≤ T := by
      rcases le_total 0 t with h | h
      · rw [Set.uIcc_of_le h] at hs'; rw [abs_le]; rw [hT, abs_of_nonneg h]
        constructor <;> linarith [hs'.1, hs'.2]
      · rw [Set.uIcc_of_ge h] at hs'; rw [abs_le]; rw [hT, abs_of_nonpos h]
        constructor <;> linarith [hs'.1, hs'.2]
    simp only [hF, norm_mul]
    have e1 := norm_borelTerm_le ha h1 ij.1
    have e2 := norm_borelTerm_le hb h2 ij.2
    rw [norm_mul] at e1 e2
    exact mul_le_mul e1 e2 (by positivity) ((by positivity : (0 : ℝ) ≤ _).trans e1)
  have hsumB : Summable (fun ij : ℕ × ℕ =>
      M * dividedPowerFn ij.1 (R * T) * (M' * dividedPowerFn ij.2 (R * T))) := by
    have h1 := (summable_dividedPowerFn (R * T)).mul_left M
    have h2 := (summable_dividedPowerFn (R * T)).mul_left M'
    have hT0 : 0 ≤ T := hT ▸ abs_nonneg t
    have hdp : ∀ n, 0 ≤ dividedPowerFn n (R * T) := fun n =>
      div_nonneg (pow_nonneg (mul_nonneg hR.le hT0) _) (by positivity)
    exact h1.mul_of_nonneg h2 (fun i => mul_nonneg hM (hdp i)) (fun j => mul_nonneg hM' (hdp j))
  have hhas := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (f := fun s => borelSeries a (t - s) * borelSeries b s) (μ := volume) (a := 0) (b := t)
    (fun ij _ => M * dividedPowerFn ij.1 (R * T) * (M' * dividedPowerFn ij.2 (R * T)))
    (fun ij => ((((continuous_dividedPowerFn ij.1).comp (continuous_const.sub continuous_id)).const_smul
      (a ij.1)).mul ((continuous_dividedPowerFn ij.2).const_smul (b ij.2))).aestronglyMeasurable)
    (fun ij => Eventually.of_forall fun s hs => hbound_s ij s hs)
    (Eventually.of_forall fun s _ => hsumB)
    intervalIntegrable_const
    (Eventually.of_forall fun s hs => by
      have h1 := (summable_borelTerm ha (t - s)).hasSum
      have h2 := (summable_borelTerm hb s).hasSum
      have hprod : Summable (fun ij : ℕ × ℕ =>
          a ij.1 * dividedPowerFn ij.1 (t - s) * (b ij.2 * dividedPowerFn ij.2 s)) :=
        Summable.of_norm_bounded hsumB fun ij => hbound_s ij s hs
      exact h1.mul h2 hprod)
  -- evaluate each termwise integral by the Beta integral
  have hterm : ∀ ij : ℕ × ℕ, (∫ s in (0 : ℝ)..t, F ij s) =
      a ij.1 * b ij.2 * dividedPowerFn (ij.1 + ij.2 + 1) t := by
    intro ij
    have hβ := integral_dividedPowerFn_mul ij.2 ij.1 t
    rw [show ij.2 + ij.1 + 1 = ij.1 + ij.2 + 1 by ring] at hβ
    rw [← hβ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hF]; ring
  simp_rw [hterm] at hhas
  -- regroup along antidiagonals
  set g : ℕ × ℕ → ℝ := fun ij => a ij.1 * b ij.2 * dividedPowerFn (ij.1 + ij.2 + 1) t
  have hsig : HasSum (fun n : ℕ => borelConvCoeff a b (n + 1) * dividedPowerFn (n + 1) t)
      (volterraConv (borelSeries a) (borelSeries b) t) := by
    have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := g)).2 hhas
    refine he.sigma fun n => ?_
    have hfin := hasSum_fintype (fun x : (Finset.HasAntidiagonal.antidiagonal n) =>
      (g ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨n, x⟩)
    convert hfin using 1
    simp only [borelConvCoeff, Finset.sum_mul, Function.comp_apply,
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, g]
    rw [← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx := Finset.HasAntidiagonal.mem_antidiagonal.1 x.2
    rw [hx]
  have hc := geometricCoeffBound_borelConvCoeff ha hb hR
  have hB : HasSum (fun n : ℕ => borelConvCoeff a b (n + 1) * dividedPowerFn (n + 1) t)
      (borelSeries (borelConvCoeff a b) t) := by
    have h := (summable_borelTerm hc t).hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    have e : (∑ i ∈ Finset.range 1, borelConvCoeff a b i * dividedPowerFn i t) = 0 := by
      simp [borelConvCoeff]
    rw [e, sub_zero] at h
    exact h
  exact hsig.unique hB

/-! ## Odd factorial series -/

/-- Odd-series convolution coefficients: `C_0 = 0`, `C_{m+1} = Σ_{p+q=m} a_p b_q`. -/
def oddConvCoeff (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal m, a pq.1 * b pq.2

theorem oddConvCoeff_eq_borelConvCoeff (a b : ℕ → ℝ) (m : ℕ) :
    oddConvCoeff a b m = borelConvCoeff a b m := by
  rcases m with _ | m <;> rfl

theorem oddFactorialSeries_eq_tsum_dividedPowerFn (a : ℕ → ℝ) (t : ℝ) :
    oddFactorialSeries a t = ∑' j, a j * dividedPowerFn (2 * j + 1) t := by
  unfold oddFactorialSeries dividedPowerFn
  refine tsum_congr fun j => ?_
  ring

/-- **Volterra convolution of odd factorial series.**
`∫_0^t O_a(t-s) O_b(s) ds = Σ_{m} (Σ_{p+q=m} a_p b_q) t^{2m+3}/(2m+3)! = O_C(t)`. -/
theorem volterraConv_oddFactorialSeries {a b : ℕ → ℝ} {M M' R : ℝ}
    (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R) (hR : 0 < R) (t : ℝ) :
    volterraConv (oddFactorialSeries a) (oddFactorialSeries b) t =
      oddFactorialSeries (oddConvCoeff a b) t := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  have hM' : 0 ≤ M' := by have := (abs_nonneg _).trans (hb 0); simpa using this
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = |t| := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ abs_nonneg t
  set F : ℕ × ℕ → ℝ → ℝ := fun ij s =>
    a ij.1 * dividedPowerFn (2 * ij.1 + 1) (t - s) * (b ij.2 * dividedPowerFn (2 * ij.2 + 1) s)
    with hF
  set Bd : ℕ × ℕ → ℝ := fun ij =>
    M * R ^ ij.1 * T ^ (2 * ij.1 + 1) / ((2 * ij.1 + 1).factorial : ℝ) *
      (M' * R ^ ij.2 * T ^ (2 * ij.2 + 1) / ((2 * ij.2 + 1).factorial : ℝ)) with hBd
  have hbound_s : ∀ ij : ℕ × ℕ, ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖F ij s‖ ≤ Bd ij := by
    intro ij s hs
    have hs' : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
    have h1 : |t - s| ≤ T := by
      rcases le_total 0 t with h | h
      · rw [Set.uIcc_of_le h] at hs'; rw [abs_le, hT, abs_of_nonneg h]
        constructor <;> linarith [hs'.1, hs'.2]
      · rw [Set.uIcc_of_ge h] at hs'; rw [abs_le, hT, abs_of_nonpos h]
        constructor <;> linarith [hs'.1, hs'.2]
    have h2 : |s| ≤ T := by
      rcases le_total 0 t with h | h
      · rw [Set.uIcc_of_le h] at hs'; rw [abs_le, hT, abs_of_nonneg h]
        constructor <;> linarith [hs'.1, hs'.2]
      · rw [Set.uIcc_of_ge h] at hs'; rw [abs_le, hT, abs_of_nonpos h]
        constructor <;> linarith [hs'.1, hs'.2]
    have e1 := norm_oddEvenFactorialTerm_le ha h1 ij.1 1
    have e2 := norm_oddEvenFactorialTerm_le hb h2 ij.2 1
    have hd : ∀ k (x : ℝ), a k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) =
        a k * dividedPowerFn (2 * k + 1) x := fun k x => by unfold dividedPowerFn; ring
    have hd' : ∀ k (x : ℝ), b k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) =
        b k * dividedPowerFn (2 * k + 1) x := fun k x => by unfold dividedPowerFn; ring
    rw [hd] at e1
    rw [hd'] at e2
    simp only [hF, hBd, norm_mul] at e1 e2 ⊢
    exact mul_le_mul e1 e2 (by positivity) ((by positivity : (0 : ℝ) ≤ _).trans e1)
  have hsumB : Summable Bd := by
    have h1 := summable_geometric_div_factorial (M := M) hR.le hT0 1
    have h2 := summable_geometric_div_factorial (M := M') hR.le hT0 1
    exact h1.mul_of_nonneg h2 (fun i => by positivity) (fun j => by positivity)
  have hhas := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (f := fun s => oddFactorialSeries a (t - s) * oddFactorialSeries b s) (μ := volume)
    (a := 0) (b := t) (fun ij _ => Bd ij)
    (fun ij => ((((continuous_dividedPowerFn _).comp (continuous_const.sub continuous_id)).const_smul
      (a ij.1)).mul ((continuous_dividedPowerFn _).const_smul (b ij.2))).aestronglyMeasurable)
    (fun ij => Eventually.of_forall fun s hs => hbound_s ij s hs)
    (Eventually.of_forall fun s _ => hsumB)
    intervalIntegrable_const
    (Eventually.of_forall fun s hs => by
      have h1 : HasSum (fun i => a i * dividedPowerFn (2 * i + 1) (t - s))
          (oddFactorialSeries a (t - s)) := by
        rw [oddFactorialSeries_eq_tsum_dividedPowerFn]
        refine Summable.hasSum ?_
        refine (summable_oddFactorialSeries_term hR.le ha (t - s)).congr fun i => ?_
        unfold dividedPowerFn; ring
      have h2 : HasSum (fun j => b j * dividedPowerFn (2 * j + 1) s) (oddFactorialSeries b s) := by
        rw [oddFactorialSeries_eq_tsum_dividedPowerFn]
        refine Summable.hasSum ?_
        refine (summable_oddFactorialSeries_term hR.le hb s).congr fun j => ?_
        unfold dividedPowerFn; ring
      have hprod : Summable (fun ij : ℕ × ℕ => F ij s) :=
        Summable.of_norm_bounded hsumB fun ij => hbound_s ij s hs
      exact h1.mul h2 hprod)
  have hterm : ∀ ij : ℕ × ℕ, (∫ s in (0 : ℝ)..t, F ij s) =
      a ij.1 * b ij.2 * dividedPowerFn (2 * (ij.1 + ij.2) + 3) t := by
    intro ij
    have hβ := integral_dividedPowerFn_mul (2 * ij.2 + 1) (2 * ij.1 + 1) t
    rw [show 2 * ij.2 + 1 + (2 * ij.1 + 1) + 1 = 2 * (ij.1 + ij.2) + 3 by ring] at hβ
    rw [← hβ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hF]; ring
  simp_rw [hterm] at hhas
  set g : ℕ × ℕ → ℝ := fun ij => a ij.1 * b ij.2 * dividedPowerFn (2 * (ij.1 + ij.2) + 3) t
  have hsig : HasSum (fun m : ℕ => oddConvCoeff a b (m + 1) * dividedPowerFn (2 * m + 3) t)
      (volterraConv (oddFactorialSeries a) (oddFactorialSeries b) t) := by
    have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := g)).2 hhas
    refine he.sigma fun m => ?_
    have hfin := hasSum_fintype (fun x : (Finset.HasAntidiagonal.antidiagonal m) =>
      (g ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨m, x⟩)
    convert hfin using 1
    simp only [oddConvCoeff, Finset.sum_mul, Function.comp_apply,
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, g]
    rw [← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal m)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx := Finset.HasAntidiagonal.mem_antidiagonal.1 x.2
    rw [hx]
  have hc : GeometricCoeffBound (oddConvCoeff a b) (M * M' / (2 * R)) (2 * R) := by
    intro m
    rw [oddConvCoeff_eq_borelConvCoeff]
    exact geometricCoeffBound_borelConvCoeff ha hb hR m
  have hB : HasSum (fun m : ℕ => oddConvCoeff a b (m + 1) * dividedPowerFn (2 * m + 3) t)
      (oddFactorialSeries (oddConvCoeff a b) t) := by
    have h := (summable_oddFactorialSeries_term (by linarith : (0 : ℝ) ≤ 2 * R) hc t).hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    have e : (∑ i ∈ Finset.range 1, oddConvCoeff a b i * t ^ (2 * i + 1) /
        ((2 * i + 1).factorial : ℝ)) = 0 := by
      simp [oddConvCoeff]
    rw [e, sub_zero] at h
    refine h.congr_fun fun m => ?_
    unfold dividedPowerFn
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
    ring
  exact hsig.unique hB

end GaloisForLFunctions.HTGeometry
