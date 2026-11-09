import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedConvolutionBounds

/-!
# Infinite complex deletion

Square-summable shifts give pointwise multiplier convergence. Summable
variation costs dominate every filtered mode on a vertical strip, allowing
the infinite product to pass through an absolutely convergent trace.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Finite multiplier of the signed convolution. -/
def signedTailFactor : List (ℝ × ℝ) → ℂ → ℂ
  | [], _ => 1
  | (a, h) :: l, w => signedDeletionFactor a h w * signedTailFactor l w

theorem signedTailFactor_append (l r : List (ℝ × ℝ)) (w : ℂ) :
    signedTailFactor (l ++ r) w = signedTailFactor l w * signedTailFactor r w := by
  induction l with
  | nil => simp [signedTailFactor]
  | cons p l ih => simp only [List.cons_append, signedTailFactor, ih, mul_assoc]

theorem signedTailFactor_filterPrefix (a h : ℕ → ℝ) (w : ℂ) (N : ℕ) :
    signedTailFactor (filterPrefix a h N) w =
      ∏ i ∈ Finset.range N, signedDeletionFactor (a i) (h i) w := by
  induction N with
  | zero => simp [filterPrefix, signedTailFactor]
  | succ N ih =>
      simp only [filterPrefix, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, signedTailFactor_append, signedTailFactor, mul_one,
        Finset.prod_range_succ] at *
      rw [ih]

theorem signedVariationCost_append (l r : List (ℝ × ℝ)) :
    signedVariationCost (l ++ r) = signedVariationCost l + signedVariationCost r := by
  simp [signedVariationCost]

theorem signedVariationCost_filterPrefix (a h : ℕ → ℝ) (N : ℕ) :
    signedVariationCost (filterPrefix a h N) =
      ∑ i ∈ Finset.range N, 3 / 2 * (h i * a i) ^ 2 := by
  induction N with
  | zero => simp [filterPrefix, signedVariationCost]
  | succ N ih =>
      simp only [filterPrefix, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, signedVariationCost_append, Finset.sum_range_succ] at *
      rw [ih]
      simp [signedVariationCost]

/-- All fixed exponents have convergent signed deletion products. -/
theorem multipliable_signedDeletionFactor (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    Multipliable fun i => signedDeletionFactor (a i) (h i) w := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_small_shift h hsq w)
  have hs : Summable fun i => ‖signedDeletionFactor (a i) (h i) w - 1‖ := by
    apply (summable_nat_add_iff N).mp
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _
      (((summable_nat_add_iff N).mpr hsq).mul_right (2 / 3 * ‖w‖ ^ 2))
    intro i
    convert norm_signedDeletionFactor_sub_one_le (a (i + N)) (h (i + N)) w
      (hN (i + N) (Nat.le_add_left N i)) using 1 <;> ring
  have he : (fun i => 1 + (signedDeletionFactor (a i) (h i) w - 1)) =
      fun i => signedDeletionFactor (a i) (h i) w := by funext i; ring
  simpa only [he] using multipliable_one_add_of_summable hs

theorem tendsto_signedTailFactor (a h : ℕ → ℝ) (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    Tendsto (fun N => signedTailFactor (filterPrefix a h N) w) atTop
      (𝓝 (∏' i, signedDeletionFactor (a i) (h i) w)) := by
  simpa only [signedTailFactor_filterPrefix] using
    (multipliable_signedDeletionFactor a h hsq w).hasProd.tendsto_prod_nat

/-- A sufficiently late signed tail preserves any chosen exponent. -/
theorem exists_nonzero_signed_tail_multiplier (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    ∃ N : ℕ, (∏' i : ℕ, signedDeletionFactor (a (i + N)) (h (i + N)) w) ≠ 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_small_shift h hsq w)
  exact ⟨N, (multipliable_signedDeletionFactor_ne_zero
    (fun i => a (i + N)) (fun i => h (i + N)) w
    ((summable_nat_add_iff N).mpr hsq) (fun i => hN (i + N) (Nat.le_add_left N i))).2⟩

/-- The assigned phase annihilates its exponent in the infinite product. -/
theorem tprod_signedDeletionFactor_root (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (n : ℕ) {γ : ℝ}
    (hphase : h n * γ = 2 * Real.pi / 3) :
    (∏' i, signedDeletionFactor (a i) (h i) ((a n : ℂ) + (γ : ℂ) * I)) = 0 := by
  have he : (fun _ : ℕ => (0 : ℂ)) =ᶠ[atTop]
      (fun N => signedTailFactor (filterPrefix a h N) ((a n : ℂ) + (γ : ℂ) * I)) := by
    filter_upwards [eventually_gt_atTop n] with N hN
    rw [signedTailFactor_filterPrefix]
    symm
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hN)
      (signedDeletionFactor_root (a n) (h n) γ hphase)
  exact tendsto_nhds_unique (tendsto_signedTailFactor a h hsq _)
    (tendsto_const_nhds.congr' he)

/-- The absolute coefficient moment bounds the complex multiplier. -/
theorem norm_signedDeletionFactor_le (a h : ℝ) (w : ℂ) :
    ‖signedDeletionFactor a h w‖ ≤ Real.exp (3 / 2 * (h * a) ^ 2 + w.re ^ 2 * h ^ 2 / 2) := by
  have hc : ‖Complex.cosh ((h : ℂ) * w)‖ ≤ Real.cosh (h * w.re) := by
    rw [Complex.cosh, norm_div, norm_ofNat, Real.cosh_eq]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      norm_add_le (Complex.exp ((h : ℂ) * w)) (Complex.exp (-((h : ℂ) * w)))
  have hm : ‖signedDeletionFactor a h w‖ ≤ signedVariationMoment a h w.re := by
    unfold signedDeletionFactor signedVariationMoment
    rw [norm_div]
    exact div_le_div_of_nonneg_right
      ((norm_add_le _ _).trans (add_le_add_right hc _)) (norm_nonneg _)
  exact (hm.trans (signedVariationMoment_le a h w.re)).trans
    (Real.exp_le_exp.mpr (add_le_add_left (min_le_right _ _) _))

theorem norm_signedTailFactor_le (l : List (ℝ × ℝ)) (w : ℂ) :
    ‖signedTailFactor l w‖ ≤
      Real.exp (signedVariationCost l + w.re ^ 2 * squareCost l / 2) := by
  induction l with
  | nil => simp [signedTailFactor, signedVariationCost, squareCost]
  | cons p l ih =>
      rw [signedTailFactor, norm_mul]
      calc
        _ ≤ Real.exp (3 / 2 * (p.2 * p.1) ^ 2 + w.re ^ 2 * p.2 ^ 2 / 2) *
            Real.exp (signedVariationCost l + w.re ^ 2 * squareCost l / 2) :=
          mul_le_mul (norm_signedDeletionFactor_le p.1 p.2 w) ih (norm_nonneg _)
            (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          simp only [signedVariationCost, squareCost, List.map_cons, List.sum_cons]
          ring

/-- Signed convolution commutes with every absolutely convergent complex series. -/
theorem signedAverage_tsum {ι : Type*} (a h : ℝ) (F : ι → ℝ → ℂ)
    (hF : ∀ u, Summable fun i => F i u) (t : ℝ) :
    Summable (fun i => signedAverage a h (F i) t) ∧
      signedAverage a h (fun u => ∑' i, F i u) t = ∑' i, signedAverage a h (F i) t := by
  have hleft := (hF (t - h)).div_const 2
  have hmid := (hF t).mul_left (signedDeletionCenter (h * a))
  have hright := (hF (t + h)).div_const 2
  refine ⟨((hleft.add hmid).add hright).div_const _, ?_⟩
  unfold signedAverage
  rw [tsum_div_const, (hleft.add hmid).tsum_add hright, hleft.tsum_add hmid,
    tsum_div_const, tsum_mul_left, tsum_div_const]

theorem signedTailAverage_tsum {ι : Type*} (l : List (ℝ × ℝ)) (F : ι → ℝ → ℂ)
    (hF : ∀ u, Summable fun i => F i u) (t : ℝ) :
    Summable (fun i => signedTailAverage l (F i) t) ∧
      signedTailAverage l (fun u => ∑' i, F i u) t = ∑' i, signedTailAverage l (F i) t := by
  induction l generalizing t with
  | nil => exact ⟨hF t, rfl⟩
  | cons p l ih =>
      have hq := signedAverage_tsum p.1 p.2 (fun i => signedTailAverage l (F i))
        (fun u => (ih u).1) t
      refine ⟨hq.1, ?_⟩
      change signedAverage p.1 p.2 (signedTailAverage l (fun u => ∑' i, F i u)) t = _
      rw [show signedTailAverage l (fun u => ∑' i, F i u) =
        fun u => ∑' i, signedTailAverage l (F i) u from funext fun u => (ih u).2]
      exact hq.2

theorem signedTailAverage_cexp (l : List (ℝ × ℝ)) (c w : ℂ) (t : ℝ) :
    signedTailAverage l (fun u => c * Complex.exp (w * u)) t =
      c * signedTailFactor l w * Complex.exp (w * t) := by
  induction l generalizing c t with
  | nil => simp [signedTailAverage, signedTailFactor]
  | cons p l ih =>
      rw [signedTailAverage, show signedTailAverage l (fun u => c * Complex.exp (w * u)) =
        (fun u : ℝ => c * signedTailFactor l w * Complex.exp (w * u)) from funext (ih c),
        signedAverage_cexp, signedTailFactor]
      ring

theorem signedTailAverage_translate (l : List (ℝ × ℝ)) (f : ℝ → ℂ) (s t : ℝ) :
    signedTailAverage l (fun u => f (s + u)) t = signedTailAverage l f (s + t) := by
  induction l generalizing t with
  | nil => rfl
  | cons p l ih =>
      simp only [signedTailAverage, signedAverage, ih, add_assoc, add_sub_assoc]

/-- Exponentials in a vertical strip have a common real envelope. -/
theorem norm_cexp_le_strip {w : ℂ} {D : ℝ} (hw : |w.re| ≤ D) (t : ℝ) :
    ‖Complex.exp (w * t)‖ ≤ Real.exp (D * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc w.re * t ≤ |w.re * t| := le_abs_self _
    _ = |w.re| * |t| := abs_mul _ _
    _ ≤ D * |t| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)

theorem summable_complex_cexp {ι : Type*} (c w : ι → ℂ) {D : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) (t : ℝ) :
    Summable fun i => c i * Complex.exp (w i * t) := by
  apply Summable.of_norm_bounded (hc.mul_right (Real.exp (D * |t|)))
  intro i
  by_cases hi : c i = 0
  · simp [hi]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_le_strip (hw i hi) t) (norm_nonneg _)

theorem norm_complex_cexp_series_le {ι : Type*} (c w : ι → ℂ) {D : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) (t : ℝ) :
    ‖∑' i, c i * Complex.exp (w i * t)‖ ≤ (∑' i, ‖c i‖) * Real.exp (D * |t|) := by
  have hs := summable_complex_cexp c w hc hw t
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  rw [← tsum_mul_right]
  apply Summable.tsum_le_tsum _ hs.norm (hc.mul_right _)
  intro i
  by_cases hi : c i = 0
  · simp [hi]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_le_strip (hw i hi) t) (norm_nonneg _)

theorem signedVariationCost_filterPrefix_le (a h : ℕ → ℝ)
    (hv : Summable fun i => 3 / 2 * (h i * a i) ^ 2) (N : ℕ) :
    signedVariationCost (filterPrefix a h N) ≤ ∑' i, 3 / 2 * (h i * a i) ^ 2 := by
  rw [signedVariationCost_filterPrefix]
  exact Summable.sum_le_tsum (Finset.range N) (fun i _ => by positivity) hv

/-- A summable variation cost bounds every prefix independently of its length. -/
theorem norm_signed_filtered_mode_le (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (hv : Summable fun i => 3 / 2 * (h i * a i) ^ 2)
    (c w : ℂ) {D : ℝ} (hw : |w.re| ≤ D) (t : ℝ) (N : ℕ) :
    ‖c * signedTailFactor (filterPrefix a h N) w * Complex.exp (w * t)‖ ≤
      ‖c‖ * (Real.exp ((∑' i, 3 / 2 * (h i * a i) ^ 2) +
        D ^ 2 * (∑' i, h i ^ 2) / 2) * Real.exp (D * |t|)) := by
  have hsqD : w.re ^ 2 ≤ D ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg w.re) hw
  have hm : ‖signedTailFactor (filterPrefix a h N) w‖ ≤
      Real.exp ((∑' i, 3 / 2 * (h i * a i) ^ 2) + D ^ 2 * (∑' i, h i ^ 2) / 2) := by
    apply (norm_signedTailFactor_le _ _).trans
    apply Real.exp_le_exp.mpr
    exact add_le_add (signedVariationCost_filterPrefix_le a h hv N)
      (div_le_div_of_nonneg_right
        (mul_le_mul hsqD (squareCost_filterPrefix_le a h hsq N)
          (squareCost_nonneg _) (sq_nonneg _)) (by norm_num))
  rw [norm_mul, norm_mul, ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
    (norm_cexp_le_strip hw t) (norm_nonneg _) (by positivity)

/-- Signed convolutions converge on every absolutely convergent strip spectrum. -/
theorem tendsto_signedTailAverage_series {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (hv : Summable fun i => 3 / 2 * (h i * a i) ^ 2)
    (c w : ι → ℂ) {D : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) (t : ℝ) :
    Tendsto (fun N => signedTailAverage (filterPrefix a h N)
      (fun u => ∑' i, c i * Complex.exp (w i * u)) t) atTop
      (𝓝 (∑' i, c i * (∏' n, signedDeletionFactor (a n) (h n) (w i)) *
        Complex.exp (w i * t))) := by
  have he (N : ℕ) : signedTailAverage (filterPrefix a h N)
      (fun u => ∑' i, c i * Complex.exp (w i * u)) t =
      ∑' i, c i * signedTailFactor (filterPrefix a h N) (w i) * Complex.exp (w i * t) := by
    rw [(signedTailAverage_tsum _ _ (summable_complex_cexp c w hc hw) t).2]
    simp only [signedTailAverage_cexp]
  simp_rw [he]
  apply tendsto_tsum_of_dominated_convergence
    (hc.mul_right (Real.exp ((∑' i, 3 / 2 * (h i * a i) ^ 2) +
      D ^ 2 * (∑' i, h i ^ 2) / 2) * Real.exp (D * |t|)))
  · intro i
    exact (tendsto_const_nhds.mul (tendsto_signedTailFactor a h hsq (w i))).mul tendsto_const_nhds
  · apply Filter.Eventually.of_forall
    intro N i
    by_cases hi : c i = 0
    · simp [hi]
    exact norm_signed_filtered_mode_le a h hsq hv (c i) (w i) (hw i hi) t N

/-- Local norm control passes through infinitely many genuinely complex deletions. -/
theorem infinite_signed_tail_translated_norm {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (hv : Summable fun i => 3 / 2 * (h i * a i) ^ 2)
    (c w : ι → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D)
    {K q L t B : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hcost : ∀ N, mixedMomentCost (filterPrefix a h N) (D + q) ≤ B)
    (hlocal : ∀ u, |u - t| ≤ L → ‖∑' i, c i * Complex.exp (w i * u)‖ ≤ K) :
    ‖∑' i, c i * (∏' n, signedDeletionFactor (a n) (h n) (w i)) *
      Complex.exp (w i * t)‖ ≤
      Real.exp (∑' i, 3 / 2 * (h i * a i) ^ 2) *
        (K + 2 * (∑' i, ‖c i‖) * Real.exp (D * |t| - q * L + B)) := by
  let A : ℝ := ∑' i, ‖c i‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hglobal (u : ℝ) : ‖∑' i, c i * Complex.exp (w i * ((t + u : ℝ) : ℂ))‖ ≤
      (A * Real.exp (D * |t|)) * Real.exp (D * |u|) := by
    apply (norm_complex_cexp_series_le c w hc hw (t + u)).trans
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have habs : |t + u| ≤ |t| + |u| := by
      simpa only [Real.norm_eq_abs] using norm_add_le t u
    nlinarith only [mul_le_mul_of_nonneg_left habs hD]
  apply le_of_tendsto (tendsto_signedTailAverage_series a h hsq hv c w hc hw t).norm
  apply Filter.Eventually.of_forall
  intro N
  have hf := signedTailAverage_local_norm (filterPrefix a h N) hK
    (mul_nonneg hA (Real.exp_pos _).le) hq hglobal
    (fun u hu => hlocal (t + u) (by simpa only [add_sub_cancel_left] using hu))
  rw [signedTailAverage_translate (filterPrefix a h N)
    (fun u : ℝ => ∑' i, c i * Complex.exp (w i * u)) t 0, add_zero] at hf
  apply hf.trans
  apply mul_le_mul
    (Real.exp_le_exp.mpr (signedVariationCost_filterPrefix_le a h hv N))
      _ (by positivity) (Real.exp_pos _).le
  apply add_le_add_left
  have he : Real.exp (D * |t| - q * L + B) =
      Real.exp (D * |t|) * Real.exp (-q * L + B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (add_le_add_left (hcost N) (-q * L)))
    (show 0 ≤ 2 * (A * Real.exp (D * |t|)) by positivity)
  convert hm using 1 <;> dsimp only [A] <;> ring

#print axioms tprod_signedDeletionFactor_root
#print axioms norm_signedTailFactor_le
#print axioms tendsto_signedTailAverage_series
#print axioms infinite_signed_tail_translated_norm

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
