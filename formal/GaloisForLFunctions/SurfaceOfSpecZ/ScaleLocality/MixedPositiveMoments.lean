import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailIsolation

/-!
# Mixed linear and quadratic costs of positive deletion

A shift costs at most the smaller of its support radius and its Gaussian
moment exponent. Summing these costs permits separate treatment of low
and high ordinates. The resulting leakage estimate survives infinite
deletion without replacing the mixed cost by total square cost.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Cumulant bound using support for large shifts and variance for small shifts. -/
def mixedMomentCost (l : List (ℝ × ℝ)) (s : ℝ) : ℝ :=
  (l.map fun p => min |p.2 * s| (s ^ 2 * p.2 ^ 2 / 2)).sum

theorem mixedMomentCost_neg (l : List (ℝ × ℝ)) (s : ℝ) :
    mixedMomentCost l (-s) = mixedMomentCost l s := by
  simp only [mixedMomentCost, mul_neg, abs_neg, neg_sq]

theorem mixedMomentCost_append (l m : List (ℝ × ℝ)) (s : ℝ) :
    mixedMomentCost (l ++ m) s = mixedMomentCost l s + mixedMomentCost m s := by
  simp [mixedMomentCost]

theorem mixedMomentCost_filterPrefix (a h : ℕ → ℝ) (N : ℕ) (s : ℝ) :
    mixedMomentCost (filterPrefix a h N) s =
      ∑ i ∈ Finset.range N, min |h i * s| (s ^ 2 * h i ^ 2 / 2) := by
  induction N with
  | zero => simp [filterPrefix, mixedMomentCost]
  | succ N ih =>
      simp only [filterPrefix, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, mixedMomentCost_append, Finset.sum_range_succ] at *
      rw [ih]
      simp [mixedMomentCost]

/-- A positive probability average is bounded by the exponential of its support radius. -/
theorem quartet_mgf_le_linear (a h s : ℝ) :
    (Real.cosh (h * s) + Real.cosh (h * a)) / (1 + Real.cosh (h * a)) ≤
      Real.exp |h * s| := by
  have hcosh : Real.cosh (h * s) ≤ Real.exp |h * s| := by
    rw [Real.cosh_eq]
    have h₁ := Real.exp_le_exp.mpr (le_abs_self (h * s))
    have h₂ := Real.exp_le_exp.mpr (neg_le_abs (h * s))
    linarith only [h₁, h₂]
  have he := Real.one_le_exp (abs_nonneg (h * s))
  have hd : 0 < 1 + Real.cosh (h * a) := by linarith [Real.cosh_pos (h * a)]
  apply (div_le_iff₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_right he (Real.cosh_pos (h * a)).le
  nlinarith only [hcosh, hh]

theorem quartet_mgf_le_mixed (a h s : ℝ) :
    (Real.cosh (h * s) + Real.cosh (h * a)) / (1 + Real.cosh (h * a)) ≤
      Real.exp (min |h * s| (s ^ 2 * h ^ 2 / 2)) := by
  rcases le_total |h * s| (s ^ 2 * h ^ 2 / 2) with hh | hh
  · rw [min_eq_left hh]
    exact quartet_mgf_le_linear a h s
  · rw [min_eq_right hh]
    exact quartet_mgf_le a h s

/-- Mixed costs add under composition of positive averages. -/
theorem tailAverage_exp_le_mixed (l : List (ℝ × ℝ)) (s t : ℝ) :
    tailAverage l (fun u => Real.exp (s * u)) t ≤
      Real.exp (mixedMomentCost l s) * Real.exp (s * t) := by
  induction l generalizing t with
  | nil => simp [tailAverage, mixedMomentCost]
  | cons p l ih =>
      calc tailAverage (p :: l) (fun u => Real.exp (s * u)) t =
          quartetAverage p.1 p.2 (tailAverage l (fun u => Real.exp (s * u))) t := rfl
        _ ≤ quartetAverage p.1 p.2
            (fun u => Real.exp (mixedMomentCost l s) * Real.exp (s * u)) t :=
          quartetAverage_mono _ _ ih t
        _ = Real.exp (mixedMomentCost l s) *
            quartetAverage p.1 p.2 (fun u => Real.exp (s * u)) t := quartetAverage_mul _ _ _ _ _
        _ ≤ Real.exp (mixedMomentCost l s) *
            (Real.exp (min |p.2 * s| (s ^ 2 * p.2 ^ 2 / 2)) * Real.exp (s * t)) := by
          rw [quartetAverage_exp]
          gcongr
          exact quartet_mgf_le_mixed _ _ _
        _ = Real.exp (mixedMomentCost (p :: l) s) * Real.exp (s * t) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          simp only [mixedMomentCost, List.map_cons, List.sum_cons]
          ring

/-- Local ceilings pay the mixed exponential moment rather than the Gaussian upper bound. -/
theorem tailAverage_local_ceiling_mixed (l : List (ℝ × ℝ)) {f : ℝ → ℝ}
    {K C D q L : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hglobal : ∀ u, f u ≤ C * Real.exp (D * |u|))
    (hlocal : ∀ u, |u| ≤ L → f u ≤ K) :
    tailAverage l f 0 ≤ K + 2 * C * Real.exp (-q * L + mixedMomentCost l (D + q)) := by
  let E : ℝ := C * Real.exp (-q * L)
  have hE : 0 ≤ E := mul_nonneg hC (Real.exp_pos _).le
  have hp : ∀ u, f u ≤ K + E *
      (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) := by
    intro u
    by_cases hu : |u| ≤ L
    · exact (hlocal u hu).trans (le_add_of_nonneg_right (by positivity))
    · have hLu : L ≤ |u| := (lt_of_not_ge hu).le
      have he : Real.exp (D * |u|) ≤
          Real.exp (-q * L) * Real.exp ((D + q) * |u|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hLu hq])
      have habs : Real.exp ((D + q) * |u|) ≤
          Real.exp ((D + q) * u) + Real.exp (-(D + q) * u) := by
        rcases le_total 0 u with hu0 | hu0
        · rw [abs_of_nonneg hu0]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos hu0, mul_neg, ← neg_mul]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
      calc f u ≤ C * Real.exp (D * |u|) := hglobal u
        _ ≤ E * Real.exp ((D + q) * |u|) := by
          dsimp only [E]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left he hC
        _ ≤ E * (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) :=
          mul_le_mul_of_nonneg_left habs hE
        _ ≤ K + E * (Real.exp ((D + q) * u) + Real.exp (-(D + q) * u)) :=
          le_add_of_nonneg_left hK
  have hm := tailAverage_mono l hp 0
  rw [tailAverage_add, tailAverage_const, tailAverage_mul, tailAverage_add] at hm
  have hplus := tailAverage_exp_le_mixed l (D + q) 0
  have hminus := tailAverage_exp_le_mixed l (-(D + q)) 0
  simp only [mul_zero, Real.exp_zero, mul_one, mixedMomentCost_neg] at hplus hminus
  calc tailAverage l f 0 ≤ K + E *
        (tailAverage l (fun u => Real.exp ((D + q) * u)) 0 +
          tailAverage l (fun u => Real.exp (-(D + q) * u)) 0) := hm
    _ ≤ K + E * (2 * Real.exp (mixedMomentCost l (D + q))) := by
      gcongr
      linarith only [hplus, hminus]
    _ = _ := by dsimp only [E]; rw [Real.exp_add]; ring

theorem tailAverage_local_floor_mixed (l : List (ℝ × ℝ)) {f : ℝ → ℝ}
    {K C D q L : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hglobal : ∀ u, -C * Real.exp (D * |u|) ≤ f u)
    (hlocal : ∀ u, |u| ≤ L → -K ≤ f u) :
    -K - 2 * C * Real.exp (-q * L + mixedMomentCost l (D + q)) ≤ tailAverage l f 0 := by
  have hh := tailAverage_local_ceiling_mixed l hK hC hq
    (f := fun u => (-1 : ℝ) * f u)
    (fun u => by linarith only [hglobal u])
    (fun u hu => by linarith only [hlocal u hu])
  rw [tailAverage_mul] at hh
  linarith only [hh]

/-- Uniform mixed moment bounds control leakage after infinitely many positive deletions. -/
theorem infinite_tail_translated_mixed_floor {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (c w : ι → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D)
    {K q L t B : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hcost : ∀ N, mixedMomentCost (filterPrefix a h N) (D + q) ≤ B)
    (hlocal : ∀ u, |u - t| ≤ L → -K ≤ ∑' i, (c i * Complex.exp (w i * u)).re) :
    -K - 2 * (∑' i, ‖c i‖) * Real.exp (D * |t| - q * L + B) ≤
      ∑' i, (c i * (∏' n, quartetFactor (a n) (h n) (w i)) *
        Complex.exp (w i * t)).re := by
  let A : ℝ := ∑' i, ‖c i‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hglobal (u : ℝ) : -(A * Real.exp (D * |t|)) * Real.exp (D * |u|) ≤
      ∑' i, (c i * Complex.exp (w i * ((t + u : ℝ) : ℂ))).re := by
    have hb := abs_cexp_series_le c w hc hw (t + u)
    have he : Real.exp (D * |t + u|) ≤ Real.exp (D * |t|) * Real.exp (D * |u|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have habs : |t + u| ≤ |t| + |u| := by
        simpa only [Real.norm_eq_abs] using norm_add_le t u
      nlinarith only [mul_le_mul_of_nonneg_left habs hD]
    have hh := mul_le_mul_of_nonneg_left he hA
    have hn := neg_abs_le (∑' i, (c i * Complex.exp (w i * ((t + u : ℝ) : ℂ))).re)
    dsimp only [A] at hh ⊢
    nlinarith only [hb, hh, hn]
  apply ge_of_tendsto (tendsto_tailAverage_series a h hsq c w hc hw t)
  apply Filter.Eventually.of_forall
  intro N
  have hf := tailAverage_local_floor_mixed (filterPrefix a h N) hK
    (mul_nonneg hA (Real.exp_pos _).le) hq hglobal
    (fun u hu => hlocal (t + u) (by simpa only [add_sub_cancel_left] using hu))
  rw [tailAverage_translate (filterPrefix a h N)
    (fun u : ℝ => ∑' i, (c i * Complex.exp (w i * u)).re) t 0, add_zero] at hf
  have he : Real.exp (-q * L + mixedMomentCost (filterPrefix a h N) (D + q)) ≤
      Real.exp (-q * L + B) :=
    Real.exp_le_exp.mpr (add_le_add le_rfl (hcost N))
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2 * (A * Real.exp (D * |t|)) by positivity)
  have hexp : Real.exp (D * |t| - q * L + B) =
      Real.exp (D * |t|) * Real.exp (-q * L + B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  dsimp only [A] at hm hf
  nlinarith only [hm, hf]

#print axioms tailAverage_local_floor_mixed
#print axioms infinite_tail_translated_mixed_floor

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
