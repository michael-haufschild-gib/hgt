import GaloisForLFunctions.HTGeometry.PolynomialInverseEval
import GaloisForLFunctions.HTGeometry.GammaMonomialHalfPlaneLimit
import GaloisForLFunctions.HTGeometry.GammaMonomialDigammaSum
import GaloisForLFunctions.HTGeometry.InverseSeriesLadder

/-!
# The transseries of a balanced gamma monomial

A gamma monomial with real nonnegative shifts, vanishing degree and vanishing first moment has an
asymptotic expansion in `1/s` to every order on a right half plane, with coefficients given by the
forced ladder of `InverseSeriesLadder`.

The induction runs one step of `norm_le_of_deriv_decay` per order: the residual of the differential
equation is a polynomial divisible by `X^{N+3}`, the tail of the digamma expansion is
`O(‖s‖^{-(N+3)})`, and the product of the logarithmic derivative with the previous error is
`O(‖s‖^{-2})·O(‖s‖^{-(N+1)})`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Polynomial

noncomputable section

/-- The ladder moments of a real shift vector. -/
def gammaLadderCoeff {r : ℕ} (lam : Fin r → ℝ) (g : Fin r → ℤ) : ℕ → ℂ :=
  balancedLadderCoeff (fun i => ((lam i : ℝ) : ℂ)) g

/-- The truncated transseries of a balanced gamma monomial. -/
def gammaExpPoly {r : ℕ} (lam : Fin r → ℝ) (g : Fin r → ℤ) (N : ℕ) : Polynomial ℂ :=
  inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) N

theorem gammaExpPoly_eq {r : ℕ} (lam : Fin r → ℝ) (g : Fin r → ℤ) (N : ℕ) :
    gammaExpPoly lam g N = inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) N := rfl

theorem eval_lamPoly_inv (D : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (lamPoly D N).eval z⁻¹ = -∑ m ∈ Finset.range (N + 1), D m / z ^ (m + 1) := by
  rw [lamPoly, Polynomial.eval_neg, Polynomial.eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    inv_pow, div_eq_mul_inv]

theorem eval_zero_expPoly (D : ℕ → ℂ) (N : ℕ) : (inverseSeriesLadderExpPoly D N).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_zero_expPoly]

/-- The gamma monomial tends to `1` along every horizontal ray in the half plane. -/
theorem exists_tendsto_gammaMonomial_ray {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, (g i : ℝ) * lam i = 0) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ s : ℂ, R₀ < s.re →
      Tendsto (fun x : ℝ => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g (s + (x : ℂ)))
        atTop (nhds 1) := by
  obtain ⟨A, R₀, hA0, hR₀, hb⟩ := exists_norm_gammaMonomial_sub_one_le lam hlam g hdeg hmom
  refine ⟨R₀, hR₀, fun s hs => ?_⟩
  have hsre : 0 < s.re := by linarith
  have hray : ∀ x : ℝ, 0 ≤ x → R₀ < (s + (x : ℂ)).re := by
    intro x hx
    have hre : (s + (x : ℂ)).re = s.re + x := by simp
    rw [hre]; linarith
  have hnormtop : Tendsto (fun x : ℝ => ‖s + (x : ℂ)‖) atTop atTop :=
    tendsto_norm_shift_ray (le_of_lt hsre)
  have hmaj : Tendsto (fun x : ℝ => A * (‖s + (x : ℂ)‖)⁻¹) atTop (nhds 0) := by
    have h := hnormtop.inv_tendsto_atTop
    have h2 : Tendsto (fun x : ℝ => (‖s + (x : ℂ)‖)⁻¹) atTop (nhds 0) := by
      refine h.congr fun x => ?_
      rw [Pi.inv_apply]
    simpa using h2.const_mul A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have := hb (s + (x : ℂ)) (hray x hx)
  rw [div_eq_mul_inv] at this
  exact this

/-- **The transseries of a balanced gamma monomial, to every order.** -/
theorem exists_norm_gammaMonomial_expansion {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, (g i : ℝ) * lam i = 0) (N : ℕ) :
    ∃ A R₀ : ℝ, 0 ≤ A ∧ 1 ≤ R₀ ∧ ∀ s : ℂ, R₀ < s.re →
      ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - (gammaExpPoly lam g N).eval s⁻¹‖
        ≤ A / ‖s‖ ^ (N + 1) := by
  have hmomC : ∑ i, ((g i : ℤ) : ℂ) * ((lam i : ℝ) : ℂ) = 0 := by
    have hcast : ((∑ i, (g i : ℝ) * lam i : ℝ) : ℂ) = 0 := by rw [hmom]; simp
    rw [← hcast]
    push_cast
    ring
  have hD0 : gammaLadderCoeff lam g 0 = 0 :=
    balancedLadderCoeff_zero _ g hdeg hmomC
  have hsumre : (∑ j, |(((lam j : ℝ) : ℂ)).re|) = ∑ j, |lam j| :=
    Finset.sum_congr rfl fun j _ => by simp
  induction N with
  | zero =>
      obtain ⟨A, R₀, hA0, hR₀, hb⟩ := exists_norm_gammaMonomial_sub_one_le lam hlam g hdeg hmom
      refine ⟨A, R₀, hA0, hR₀, fun s hs => ?_⟩
      have hev : (gammaExpPoly lam g 0).eval s⁻¹ = 1 := by
        rw [gammaExpPoly, inverseSeriesLadderExpPoly]
        simp
      rw [hev]
      simpa using hb s hs
  | succ N ih =>
      obtain ⟨AN, RN, hAN0, hRN, hIH⟩ := ih
      obtain ⟨RM, hRM, hMray⟩ := exists_tendsto_gammaMonomial_ray lam hlam g hdeg hmom
      obtain ⟨K, RL, hK0, hRL, hLb⟩ :=
        exists_norm_logDeriv_gammaMonomial_expansion (fun i => ((lam i : ℝ) : ℂ)) g hdeg (N + 2)
      obtain ⟨K1, RL1, hK10, hRL1, hL1b⟩ :=
        exists_norm_logDeriv_gammaMonomial_expansion (fun i => ((lam i : ℝ) : ℂ)) g hdeg 1
      have hdvd : (X : ℂ[X]) ^ (N + 3) ∣ resPoly (gammaLadderCoeff lam g) (N + 1) := by
        have h := X_pow_dvd_resPoly (gammaLadderCoeff lam g) hD0 (N + 1)
        rwa [show N + 1 + 2 = N + 3 from by omega] at h
      obtain ⟨Cres, hCres0, hResb⟩ := exists_norm_polyEval_div_pow_le_of_dvd hdvd 0
      set B : ℝ := ∑ j ∈ Finset.range ((inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).natDegree + 1),
        ‖(inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).coeff j‖ with hBdef
      have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
      set cN : ℂ := expLadderCoeffOf (gammaLadderCoeff lam g)
        (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) N) N with hcNdef
      set S : ℝ := ∑ j, |lam j| with hSdef
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
      set R₀ : ℝ := max (max (max RN RM) (max RL RL1)) (max (S + 1) 2) with hR₀def
      have hR₀1 : (1 : ℝ) ≤ R₀ :=
        le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hRNle : RN ≤ R₀ :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
      have hRMle : RM ≤ R₀ :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
      have hRLle : RL ≤ R₀ :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
      have hRL1le : RL1 ≤ R₀ :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
      have hSle : S + 1 ≤ R₀ := le_trans (le_max_left _ _) (le_max_right _ _)
      have h2le : (2 : ℝ) ≤ R₀ := le_trans (le_max_right _ _) (le_max_right _ _)
      have hnormlt : ∀ z : ℂ, R₀ < z.re → R₀ < ‖z‖ := by
        intro z hz
        have h1 := Complex.abs_re_le_norm z
        have h2 : z.re ≤ |z.re| := le_abs_self _
        linarith
      have hSlt : ∀ z : ℂ, R₀ < z.re → (∑ j, |(((lam j : ℝ) : ℂ)).re|) < z.re := by
        intro z hz
        rw [hsumre]
        linarith
      have hzne : ∀ z : ℂ, R₀ < z.re → z ≠ 0 := by
        intro z hz hcon
        rw [hcon] at hz
        simp only [Complex.zero_re] at hz
        linarith
      -- the truncation splits off the new coefficient
      have hPsplit : ∀ z : ℂ, (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹
          = (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) N).eval z⁻¹ + cN * (z⁻¹) ^ (N + 1) := by
        intro z
        rw [hcNdef, inverseSeriesLadderExpPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
      -- analyticity
      have hana : ∀ z : ℂ, R₀ < z.re → AnalyticAt ℂ
          (fun w : ℂ => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g w
            - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval w⁻¹) z := by
        intro z hz
        exact (analyticAt_gammaMonomial_of_gt_sum_abs _ g (hSlt z hz)).sub
          (analyticAt_polyEval_inv _ (hzne z hz))
      -- the logarithmic derivative is small
      have hLnorm : ∀ z : ℂ, R₀ < z.re →
          ‖∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ))‖ ≤ K1 / ‖z‖ ^ (2 : ℕ) := by
        intro z hz
        have hb := hL1b z (by linarith) (le_of_lt (lt_of_le_of_lt hRL1le (hnormlt z hz)))
        have hsum : ∑ m ∈ Finset.range 1,
            balancedLadderCoeff (fun i => ((lam i : ℝ) : ℂ)) g m / z ^ (m + 1) = 0 := by
          rw [Finset.sum_range_one]
          have : balancedLadderCoeff (fun i => ((lam i : ℝ) : ℂ)) g 0 = 0 := hD0
          rw [this]
          simp
        rw [hsum, add_zero] at hb
        exact hb
      -- the tail of the digamma expansion
      have hLtail : ∀ z : ℂ, R₀ < z.re →
          ‖(∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
            - (lamPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹‖ ≤ K / ‖z‖ ^ (N + 3) := by
        intro z hz
        have hb := hLb z (by linarith) (le_of_lt (lt_of_le_of_lt hRLle (hnormlt z hz)))
        rw [eval_lamPoly_inv, sub_neg_eq_add]
        rw [show N + 1 + 1 = N + 2 from by omega]
        rwa [show N + 2 + 1 = N + 3 from by omega] at hb
      -- the truncation is bounded
      have hPnorm : ∀ z : ℂ, R₀ < z.re →
          ‖(inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹‖ ≤ B := by
        intro z hz
        have := norm_polyEval_inv_le (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1))
          (by linarith [hnormlt z hz] : (1:ℝ) ≤ ‖z‖)
        rw [hBdef]
        exact this
      -- the residual is small
      have hRes : ∀ z : ℂ, R₀ < z.re →
          ‖(resPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹‖ ≤ Cres / ‖z‖ ^ (N + 3) := by
        intro z hz
        have hzn : (2:ℝ) ≤ ‖z‖ := by linarith [hnormlt z hz]
        have hzpos : (0:ℝ) < ‖z‖ := by linarith
        have hu : ‖z⁻¹‖ ≤ 1 / 2 := by
          rw [norm_inv, inv_le_iff_one_le_mul₀ hzpos]
          linarith
        have h := hResb z⁻¹ hu
        simp only [pow_zero, div_one] at h
        rw [norm_inv] at h
        rw [inv_pow] at h
        rw [div_eq_mul_inv]
        exact h
      -- the previous error is small
      have hfbound : ∀ z : ℂ, R₀ < z.re →
          ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
            - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹‖
            ≤ (AN + ‖cN‖) / ‖z‖ ^ (N + 1) := by
        intro z hz
        have hzpos : (0:ℝ) < ‖z‖ := by linarith [hnormlt z hz]
        have hih := hIH z (by linarith)
        rw [gammaExpPoly_eq] at hih
        rw [hPsplit z]
        have hsplit : gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
            - ((inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) N).eval z⁻¹ + cN * (z⁻¹) ^ (N + 1))
            = (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
                - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) N).eval z⁻¹) - cN * (z⁻¹) ^ (N + 1) := by
          ring
        rw [hsplit]
        refine le_trans (norm_sub_le _ _) ?_
        have hcn : ‖cN * (z⁻¹) ^ (N + 1)‖ = ‖cN‖ / ‖z‖ ^ (N + 1) := by
          rw [norm_mul, norm_pow, norm_inv, inv_pow, div_eq_mul_inv]
        rw [hcn]
        have hadd : AN / ‖z‖ ^ (N + 1) + ‖cN‖ / ‖z‖ ^ (N + 1) = (AN + ‖cN‖) / ‖z‖ ^ (N + 1) := by
          ring
        linarith [hih]
      -- the derivative bound
      have hderivb : ∀ z : ℂ, R₀ < z.re →
          ‖deriv (fun w : ℂ => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g w
              - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval w⁻¹) z‖
            ≤ (K1 * (AN + ‖cN‖) + K * B + Cres) / ‖z‖ ^ (N + 1 + 2) := by
        intro z hz
        have hzpos : (0:ℝ) < ‖z‖ := by linarith [hnormlt z hz]
        have hMd : HasDerivAt (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g)
            ((∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z) z := by
          have hd := (analyticAt_gammaMonomial_of_gt_sum_abs _ g (hSlt z hz)).differentiableAt
          have h := hd.hasDerivAt
          rwa [deriv_gammaMonomial _ g (hSlt z hz)] at h
        have hPd := hasDerivAt_polyEval_inv (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)) (hzne z hz)
        have hfd0 := hMd.sub hPd
        have hfun : (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g
              - fun w : ℂ => (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval w⁻¹)
            = fun w : ℂ => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g w
              - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval w⁻¹ := by
          funext w
          rfl
        rw [hfun] at hfd0
        rw [hfd0.deriv]
        have hid : (∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
            - (derivative (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1))).eval z⁻¹ * (-(z ^ (2 : ℕ))⁻¹)
            = (∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
                * (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
                  - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹)
              + ((∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
                  - (lamPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹)
                * (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹
              + (resPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹ := by
          rw [resPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_X]
          ring
        rw [hid]
        have hpowsplit : ‖z‖ ^ (N + 1 + 2) = ‖z‖ ^ (2 : ℕ) * ‖z‖ ^ (N + 1) := by ring
        have ha : ‖(∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
              * (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
                - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹)‖
            ≤ K1 * (AN + ‖cN‖) / ‖z‖ ^ (N + 1 + 2) := by
          rw [norm_mul]
          have hmul := mul_le_mul (hLnorm z hz) (hfbound z hz) (norm_nonneg _)
            (by positivity : (0:ℝ) ≤ K1 / ‖z‖ ^ (2 : ℕ))
          refine le_trans hmul (le_of_eq ?_)
          rw [hpowsplit]
          field_simp
        have hb2 : ‖((∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
                - (lamPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹)
              * (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹‖
            ≤ K * B / ‖z‖ ^ (N + 1 + 2) := by
          rw [norm_mul]
          have hmul := mul_le_mul (hLtail z hz) (hPnorm z hz) (norm_nonneg _)
            (by positivity : (0:ℝ) ≤ K / ‖z‖ ^ (N + 3))
          refine le_trans hmul (le_of_eq ?_)
          rw [div_mul_eq_mul_div]
        have hc2 : ‖(resPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹‖
            ≤ Cres / ‖z‖ ^ (N + 1 + 2) := hRes z hz
        have hsum : K1 * (AN + ‖cN‖) / ‖z‖ ^ (N + 1 + 2) + K * B / ‖z‖ ^ (N + 1 + 2)
            + Cres / ‖z‖ ^ (N + 1 + 2)
            = (K1 * (AN + ‖cN‖) + K * B + Cres) / ‖z‖ ^ (N + 1 + 2) := by ring
        have htri2 := norm_add_le
          ((∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
            * (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z
              - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹))
          (((∑ k, ((g k : ℤ) : ℂ) * Complex.digamma (z + ((lam k : ℝ) : ℂ)))
              - (lamPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹)
            * (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval z⁻¹)
        refine le_trans (norm_add_le _ _) ?_
        linarith [ha, hb2, hc2, htri2]
      -- the ray limit
      have hlim : ∀ s : ℂ, R₀ < s.re → Tendsto (fun x : ℝ =>
          gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g (s + (x : ℂ))
            - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval (s + (x : ℂ))⁻¹)
          atTop (nhds 0) := by
        intro s hs
        have h1 := hMray s (by linarith)
        have h2 := tendsto_polyEval_inv_ray (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1))
          (show 0 < s.re by linarith)
        rw [eval_zero_expPoly] at h2
        have h3 := h1.sub h2
        simpa using h3
      have hAtot : (0:ℝ) ≤ K1 * (AN + ‖cN‖) + K * B + Cres := by
        have h1 : (0:ℝ) ≤ K1 * (AN + ‖cN‖) :=
          mul_nonneg hK10 (by linarith [norm_nonneg cN])
        have h2 : (0:ℝ) ≤ K * B := mul_nonneg hK0 hB0
        linarith
      have hfinal := norm_le_of_deriv_decay (R₀ := R₀)
        (A := K1 * (AN + ‖cN‖) + K * B + Cres) (k := N + 1)
        (f := fun w : ℂ => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g w
          - (inverseSeriesLadderExpPoly (gammaLadderCoeff lam g) (N + 1)).eval w⁻¹)
        (by linarith) hAtot hana hderivb hlim
      refine ⟨2 ^ (N + 1 + 2) * (K1 * (AN + ‖cN‖) + K * B + Cres), R₀,
        mul_nonneg (by positivity) hAtot, hR₀1, fun s hs => ?_⟩
      rw [gammaExpPoly_eq]
      exact hfinal s hs

end

end GaloisForLFunctions.HTGeometry
