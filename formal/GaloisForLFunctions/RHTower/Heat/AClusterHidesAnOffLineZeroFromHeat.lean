import GaloisForLFunctions.RHTower.XiSliceHeatCoshCountermodel
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.RootRadiusHeatCone

/-!
# A central cluster hides an off-line zero from heat `≍ δ²/m`

Let `F(z) = (z − t₀)^m ((z − t₀)² + δ²) √2 sin(L(z − t₀)/2 + π/4)`: a zero of multiplicity `m` at the
centre `t₀`, one off-line pair `t₀ ± iδ`, and real zeros spaced `2π/L` (the density of `Ξ` at height
`t` when `L = log t`).  Its slice at `t₀` is

  `g(x) = F(t₀ + ix) F(t₀ − ix) = x^{2m} (δ² − x²)² cosh(Lx)`        (`clusterModel`),

which vanishes at `x = δ`.

**Theorem** (`hasSum_clusterModelHeat`).  For every `L ≥ 0` and every heat `λ` with
`64δ² ≤ λ(m + 2)`, the heated slice `H(x) = E[g(x + √λ Z)]` has a power series at `0` with
nonnegative coefficients.

With `L = log t` and `m ≍ log t` (a multiplicity the local count `≤ 40 log(180t)` allows), the model
is heat-positive at rate `κ = λL ≍ δ²` although it carries an off-line zero of depth `δ`.  Against
detection at every `κ ≤ δ²/200` for `ξ` (`re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic`), the
order `δ²` cannot be improved by any argument that the model also satisfies; a linear rate needs a
bound on the number of zeros within `O(δ)` of `½ + it`.

Proof.  With `p(x) = x^{2m}(δ² − x²)²` and `Q = e^{(λ/2)∂²} p`, the Gaussian tilt gives
`H(x) = ½ e^{λL²/2} (e^{Lx} Q(x + λL) + e^{−Lx} Q(x − λL))` (`clusterModelHeat_eq`).  `p` is the
expansion of `y^m (y − δ²)²`, whose roots lie in the disc `|y| ≤ δ²`, so `Q` has nonnegative
coefficients once `32δ² ≤ (λ/2)(m + 2)` (`coeffNonneg_forwardPolyHeat_expand_of_discFactors`).  Then
`Q(x + λL)` and `e^{Lx}Q(x + λL)` have nonnegative coefficients, `Q` is even, and `H` is the even
part of `e^{Lx}Q(x + λL)` up to a positive factor.
-/

open Polynomial MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticLocalDivisorGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The cluster head `y^m (y − δ²)²` in the variable `y = x²`. -/
def clusterHead (m : ℕ) (δ : ℝ) : ℝ[X] := X ^ m * (X - C (δ ^ 2)) ^ 2

/-- The cluster model slice `x^{2m}(δ² − x²)² cosh(Lx)`. -/
def clusterModel (m : ℕ) (δ L x : ℝ) : ℝ := x ^ (2 * m) * (δ ^ 2 - x ^ 2) ^ 2 * Real.cosh (L * x)

/-- The heated cluster model: the Gaussian average with variance `λ`. -/
def clusterModelHeat (m : ℕ) (δ L lam x : ℝ) : ℝ :=
  ∫ u : ℝ, gaussDensity (lam / 2) u * clusterModel m δ L (x + u)

theorem clusterModel_offset (m : ℕ) (δ L : ℝ) : clusterModel m δ L δ = 0 := by
  simp [clusterModel]

theorem eval_expand_clusterHead (m : ℕ) (δ y : ℝ) :
    (expand ℝ 2 (clusterHead m δ)).eval y = y ^ (2 * m) * (δ ^ 2 - y ^ 2) ^ 2 := by
  rw [expand_eval]
  simp only [clusterHead, eval_mul, eval_pow, eval_X, eval_sub, eval_C]
  rw [pow_mul]
  ring

/-! ## Gaussian averages of polynomials -/

/-- Taylor expansion of a real polynomial around `c`. -/
theorem eval_add_eq_sum_hasseDeriv (P : ℝ[X]) (c v : ℝ) :
    P.eval (c + v) = ∑ j ∈ Finset.range (P.natDegree + 1), (hasseDeriv j P).eval c * v ^ j := by
  rw [show c + v = v + c by ring, ← taylor_eval, eval_eq_sum_range' (n := P.natDegree + 1)
    (by rw [natDegree_taylor]; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [taylor_coeff]

/-- `E[P(c + U)] = (e^{s∂²}P)(c)` for `U` with density `gaussDensity s`, `s > 0`. -/
theorem integrable_and_integral_gaussDensity_mul_eval_add {s : ℝ} (hs : 0 < s) (P : ℝ[X]) (c : ℝ) :
    Integrable (fun v : ℝ => gaussDensity s v * P.eval (c + v)) ∧
      ∫ v : ℝ, gaussDensity s v * P.eval (c + v) = (forwardPolyHeat s P).eval c := by
  set N := P.natDegree + 1
  have hexp : (fun v : ℝ => gaussDensity s v * P.eval (c + v)) =
      fun v => ∑ j ∈ Finset.range N, (hasseDeriv j P).eval c * (gaussDensity s v * v ^ j) := by
    funext v
    rw [eval_add_eq_sum_hasseDeriv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : Integrable (fun v : ℝ => gaussDensity s v * P.eval (c + v)) := by
    rw [hexp]
    exact integrable_finsetSum _ fun j _ => (integrable_gaussDensity_mul_pow hs j).const_mul _
  refine ⟨hint, ?_⟩
  rw [hexp, integral_finsetSum _ (fun j _ => (integrable_gaussDensity_mul_pow hs j).const_mul _)]
  simp_rw [integral_const_mul]
  let f : ℕ → ℝ := fun j => (hasseDeriv j P).eval c * ∫ v : ℝ, gaussDensity s v * v ^ j
  have hc0 : ∀ j, N ≤ j → f j = 0 := by
    intro j hj
    dsimp only [f]
    rw [hasseDeriv_eq_zero_of_lt_natDegree _ _ (by omega), eval_zero, zero_mul]
  have hext : ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range (2 * N), f j := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    exact hc0 j hj
  change ∑ j ∈ Finset.range N, f j = (forwardPolyHeat s P).eval c
  rw [hext, sum_range_two_mul]
  unfold forwardPolyHeat
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hodd : f (2 * m + 1) = 0 := by
    dsimp only [f]
    rw [integral_gaussDensity_mul_pow_odd s m, mul_zero]
  rw [hodd, add_zero]
  dsimp only [f]
  rw [integral_gaussDensity_mul_pow_even hs m, eval_mul, eval_C]
  have hfac := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := 2 * m)) P
  rw [LinearMap.smul_apply] at hfac
  rw [← hfac, eval_smul, nsmul_eq_mul]
  have hf2 : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-! ## Head repair -/

/-- **The heated cluster head is coefficient-positive.**  If `32δ² ≤ s(m + 2)` then
`e^{s∂²}(x^{2m}(δ² − x²)²)` has nonnegative coefficients. -/
theorem coeffNonneg_forwardPolyHeat_clusterHead {m : ℕ} {δ s : ℝ} (hs : 0 < s)
    (hsN : 32 * δ ^ 2 ≤ s * (m + 2)) :
    CoeffNonneg (forwardPolyHeat s (expand ℝ 2 (clusterHead m δ))) := by
  set Lst : List ℝ[X] := List.replicate m (X - C 0) ++ [X - C (δ ^ 2), X - C (δ ^ 2)] with hLst
  have hprod : Lst.prod = clusterHead m δ := by
    simp only [hLst, List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil, C_0,
      sub_zero, clusterHead]
    ring
  have hdisc : ∀ F ∈ Lst, DiscFactor (δ ^ 2) F := by
    intro F hF
    rw [hLst, List.mem_append, List.mem_replicate] at hF
    rcases hF with ⟨-, rfl⟩ | hF
    · exact DiscFactor.lin 0 (by rw [abs_zero]; positivity)
    · have hF' : F = X - C (δ ^ 2) := by simpa using hF
      rw [hF']
      exact DiscFactor.lin (δ ^ 2) (le_of_eq (abs_of_nonneg (sq_nonneg δ)))
  have hdeg : (Lst.prod).natDegree = m + 2 := by
    rw [hprod, clusterHead, (monic_X_pow m).natDegree_mul ((monic_X_sub_C _).pow 2),
      natDegree_X_pow, natDegree_pow, natDegree_X_sub_C]
  have h := coeffNonneg_forwardPolyHeat_expand_of_discFactors (sq_nonneg δ) hs hdisc
    (by rw [hdeg]; push_cast; linarith)
  rwa [hprod] at h

/-! ## Taylor shifts and exponential factors keep nonnegative coefficients -/

theorem coeffNonneg_X_add_C_pow {κ : ℝ} (hκ : 0 ≤ κ) (e : ℕ) : CoeffNonneg ((X + C κ) ^ e) := by
  induction e with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ e ih =>
    rw [pow_succ]
    refine ih.mul fun n => ?_
    rw [coeff_add, coeff_X, coeff_C]
    split_ifs <;> linarith

/-- A Taylor shift to a point `κ ≥ 0` keeps nonnegative coefficients. -/
theorem CoeffNonneg.taylor {P : ℝ[X]} (hP : CoeffNonneg P) {κ : ℝ} (hκ : 0 ≤ κ) :
    CoeffNonneg (taylor κ P) := by
  rw [taylor_apply, comp_eq_sum_left]
  exact CoeffNonneg.sum _ fun e _ => CoeffNonneg.C_mul (coeffNonneg_X_add_C_pow hκ e) (hP e)

/-- The coefficients of `e^{Lx} R(x)` for a polynomial `R`. -/
def expMulCoeff (L : ℝ) (R : ℝ[X]) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (R.natDegree + 1),
    if j ≤ n then R.coeff j * (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0

theorem hasSum_exp_mul_eval (L : ℝ) (R : ℝ[X]) (x : ℝ) :
    HasSum (fun n : ℕ => expMulCoeff L R n * x ^ n) (Real.exp (L * x) * R.eval x) := by
  have hj : ∀ j : ℕ, HasSum (fun n : ℕ => (if j ≤ n then (L ^ (n - j) / ((n - j).factorial : ℝ))
      else 0) * x ^ n) (x ^ j * Real.exp (L * x)) := by
    intro j
    have hexp : HasSum (fun m : ℕ => (L * x) ^ m / (m.factorial : ℝ)) (Real.exp (L * x)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (L * x)
    have h := hexp.mul_left (x ^ j)
    have hinj : Function.Injective (fun m : ℕ => m + j) := fun a b h => by simpa using h
    have hzero : ∀ n ∉ Set.range (fun m : ℕ => m + j),
        (if j ≤ n then (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0) * x ^ n = 0 := by
      intro n hn
      have : ¬ j ≤ n := fun hjn => hn ⟨n - j, by simp only; omega⟩
      rw [if_neg this, zero_mul]
    rw [← hinj.hasSum_iff hzero]
    refine h.congr_fun fun m => ?_
    simp only [Function.comp_def, show j ≤ m + j from Nat.le_add_left j m, if_true,
      Nat.add_sub_cancel, mul_pow, pow_add]
    ring
  have hall : HasSum (fun n : ℕ => ∑ j ∈ Finset.range (R.natDegree + 1), R.coeff j *
      ((if j ≤ n then (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0) * x ^ n))
      (∑ j ∈ Finset.range (R.natDegree + 1), R.coeff j * (x ^ j * Real.exp (L * x))) :=
    hasSum_sum fun j _ => (hj j).mul_left (R.coeff j)
  have hval : Real.exp (L * x) * R.eval x
      = ∑ j ∈ Finset.range (R.natDegree + 1), R.coeff j * (x ^ j * Real.exp (L * x)) := by
    rw [eval_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hval]
  refine hall.congr_fun fun n => ?_
  simp only [expMulCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem expMulCoeff_nonneg {L : ℝ} (hL : 0 ≤ L) {R : ℝ[X]} (hR : CoeffNonneg R) (n : ℕ) :
    0 ≤ expMulCoeff L R n :=
  Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (hR j) (by positivity)
    · exact le_rfl

/-! ## The heated cluster model -/

/-- **Gaussian tilt.**  `E[e^{LU} P(x + U)] = e^{λL²/2} (e^{(λ/2)∂²}P)(x + λL)` for `U` of variance
`λ`. -/
theorem integrable_and_integral_gaussDensity_tilt_poly {lam : ℝ} (hlam : 0 < lam) (P : ℝ[X])
    (L x : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * (Real.exp (L * u) * P.eval (x + u)))
      ∧ ∫ u : ℝ, gaussDensity (lam / 2) u * (Real.exp (L * u) * P.eval (x + u))
        = Real.exp (lam * L ^ 2 / 2) * (forwardPolyHeat (lam / 2) P).eval (x + lam * L) := by
  have ht : 0 < lam / 2 := by positivity
  obtain ⟨hint, hval⟩ := integrable_and_integral_gaussDensity_mul_eval_add ht P (x + lam * L)
  have hpt : ∀ u : ℝ, gaussDensity (lam / 2) u * (Real.exp (L * u) * P.eval (x + u))
      = Real.exp (lam * L ^ 2 / 2) * (gaussDensity (lam / 2) (u - lam * L)
        * P.eval (x + lam * L + (u - lam * L))) := by
    intro u
    have e : gaussDensity (lam / 2) u * Real.exp (L * u)
        = Real.exp (lam * L ^ 2 / 2) * gaussDensity (lam / 2) (u - lam * L) := by
      unfold gaussDensity
      have hexp : -(u ^ 2 / (4 * (lam / 2))) + L * u
          = lam * L ^ 2 / 2 + -((u - lam * L) ^ 2 / (4 * (lam / 2))) := by
        field_simp; ring
      calc (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (4 * (lam / 2))))
            * Real.exp (L * u)
          = (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ))
            * Real.exp (-(u ^ 2 / (4 * (lam / 2))) + L * u) := by rw [mul_assoc, ← Real.exp_add]
        _ = (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ))
            * Real.exp (lam * L ^ 2 / 2 + -((u - lam * L) ^ 2 / (4 * (lam / 2)))) := by rw [hexp]
        _ = _ := by rw [Real.exp_add]; ring
    rw [show x + lam * L + (u - lam * L) = x + u by ring, ← mul_assoc, e]
    ring
  have hfun : (fun u : ℝ => gaussDensity (lam / 2) u * (Real.exp (L * u) * P.eval (x + u)))
      = fun u => Real.exp (lam * L ^ 2 / 2) * ((fun v => gaussDensity (lam / 2) v
        * P.eval (x + lam * L + v)) (u - lam * L)) := funext hpt
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint.comp_sub_right _).const_mul _
  · rw [hfun, integral_const_mul, integral_sub_right_eq_self
      (fun v => gaussDensity (lam / 2) v * P.eval (x + lam * L + v)), hval]

/-- The heat of an even polynomial `P(x²)` is even. -/
theorem eval_neg_forwardPolyHeat_expand {s : ℝ} (hs : 0 < s) (q : ℝ[X]) (c : ℝ) :
    (forwardPolyHeat s (expand ℝ 2 q)).eval (-c) = (forwardPolyHeat s (expand ℝ 2 q)).eval c := by
  rw [← (integrable_and_integral_gaussDensity_mul_eval_add hs _ (-c)).2,
    ← (integrable_and_integral_gaussDensity_mul_eval_add hs _ c).2,
    ← integral_neg_eq_self (fun v => gaussDensity s v * (expand ℝ 2 q).eval (-c + v))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [gaussDensity_neg, expand_eval]
  congr 2
  ring

/-- **Closed form of the heated cluster model.**  With `κ = λL` and `Q = e^{(λ/2)∂²}p`,
`H(x) = ½ e^{λL²/2} (e^{Lx} Q(x + κ) + e^{−Lx} Q(x − κ))`. -/
theorem clusterModelHeat_eq {lam : ℝ} (hlam : 0 < lam) (m : ℕ) (δ L x : ℝ) :
    clusterModelHeat m δ L lam x = Real.exp (lam * L ^ 2 / 2) / 2 *
      (Real.exp (L * x) * (forwardPolyHeat (lam / 2) (expand ℝ 2 (clusterHead m δ))).eval
          (x + lam * L)
        + Real.exp (-(L * x)) * (forwardPolyHeat (lam / 2) (expand ℝ 2 (clusterHead m δ))).eval
          (x - lam * L)) := by
  set P := expand ℝ 2 (clusterHead m δ) with hP
  obtain ⟨h1, v1⟩ := integrable_and_integral_gaussDensity_tilt_poly hlam P L x
  obtain ⟨h2, v2⟩ := integrable_and_integral_gaussDensity_tilt_poly hlam P (-L) x
  have hpt : ∀ u : ℝ, gaussDensity (lam / 2) u * clusterModel m δ L (x + u)
      = Real.exp (L * x) / 2 * (gaussDensity (lam / 2) u * (Real.exp (L * u) * P.eval (x + u)))
        + Real.exp (-(L * x)) / 2 * (gaussDensity (lam / 2) u
          * (Real.exp (-L * u) * P.eval (x + u))) := by
    intro u
    rw [hP, eval_expand_clusterHead]
    unfold clusterModel
    rw [Real.cosh_eq, show L * (x + u) = L * x + L * u by ring, Real.exp_add,
      show -(L * x + L * u) = -(L * x) + -L * u by ring, Real.exp_add]
    ring
  unfold clusterModelHeat
  rw [show (fun u : ℝ => gaussDensity (lam / 2) u * clusterModel m δ L (x + u))
      = fun u => Real.exp (L * x) / 2 * (gaussDensity (lam / 2) u
        * (Real.exp (L * u) * P.eval (x + u)))
        + Real.exp (-(L * x)) / 2 * (gaussDensity (lam / 2) u
          * (Real.exp (-L * u) * P.eval (x + u))) from funext hpt,
    integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul, v1, v2]
  rw [show (-L) ^ 2 = L ^ 2 by ring, show x + lam * -L = x - lam * L by ring]
  ring

/-- **A central cluster hides an off-line zero.**  For `λ > 0`, `L ≥ 0` and `64δ² ≤ λ(m + 2)`, the
heated cluster model has a power series at `0` with nonnegative coefficients, although
`clusterModel m δ L δ = 0`. -/
theorem hasSum_clusterModelHeat {m : ℕ} {δ L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hheat : 64 * δ ^ 2 ≤ lam * (m + 2)) :
    ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧
      ∀ x : ℝ, HasSum (fun n : ℕ => a n * x ^ n) (clusterModelHeat m δ L lam x) := by
  have hs : 0 < lam / 2 := by positivity
  set Q := forwardPolyHeat (lam / 2) (expand ℝ 2 (clusterHead m δ)) with hQ
  have hQ0 : CoeffNonneg Q := coeffNonneg_forwardPolyHeat_clusterHead hs (by linarith)
  set κ := lam * L with hκdef
  have hκ : 0 ≤ κ := mul_nonneg hlam.le hL
  set R := taylor κ Q with hR
  have hR0 : CoeffNonneg R := CoeffNonneg.taylor hQ0 hκ
  set c := expMulCoeff L R with hc
  have hc0 : ∀ n, 0 ≤ c n := expMulCoeff_nonneg hL hR0
  refine ⟨fun n => Real.exp (lam * L ^ 2 / 2) / 2 * (c n + (-1) ^ n * c n), fun n => ?_,
    fun x => ?_⟩
  · have h1 : 0 ≤ c n + (-1) ^ n * c n := by
      rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> linarith [hc0 n]
    positivity
  · have h1 := hasSum_exp_mul_eval L R x
    have h2 := hasSum_exp_mul_eval L R (-x)
    rw [clusterModelHeat_eq hlam]
    rw [hR, taylor_eval] at h1 h2
    have e : Real.exp (L * -x) * Q.eval (-x + κ)
        = Real.exp (-(L * x)) * Q.eval (x - lam * L) := by
      rw [show L * -x = -(L * x) by ring, show -x + κ = -(x - lam * L) by rw [hκdef]; ring, hQ,
        eval_neg_forwardPolyHeat_expand hs]
    rw [e] at h2
    refine ((h1.add h2).mul_left (Real.exp (lam * L ^ 2 / 2) / 2)).congr_fun fun n => ?_
    rw [neg_pow]
    ring

end

end RHTower.DeBruijn
