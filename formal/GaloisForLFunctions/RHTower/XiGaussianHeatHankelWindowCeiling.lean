import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLargeTimeDetection

/-!
# The small-time ceiling of the heat Hankel window

Let `u` be an upper off-line heat frequency.  For a level `Λ ≥ Re u` let `K_Λ` be the monic
polynomial vanishing at every heat frequency of real part `≤ Λ` other than `u, ū`, and put
`P = K_Λ · ((X − ū) + t (X − u))` with `|t| = 1` (`heatLevelPairTest`).  The frequencies of real
part `≤ Λ` other than `u, ū` see nothing.  With the right phase of `t` the pair `u, ū` contributes
`−4 (Im u)² e^{-a Re u} |K_Λ(u)|²`.  Every frequency above `Λ` contributes at most
`8 (1 + R)² |K_Λ(u)|² e^{-a Re w} (C₀(1 + |w|))^{2k} (1 + |w|)²`, where `k = deg K_Λ`.  Comparing
with the summable weights `1/(1 + |w|) ≤ 1/|z|²` through the elementary bound
`e^{-aW} (C(1 + W))^M ≤ η` for `W ≥ Λ` (`exp_mul_pow_le_of_level`) gives:

**Theorem** (`exists_heatHankel_re_neg_of_level`).  There are `C, η > 0` depending only on `u`
such that for every `a ∈ (0, 1]`, level `Λ ≥ max(Re u, 0)` and `k ≥ deg K_Λ` with
`2k + 3 ≤ a (1 + Λ)` and `(2k + 3) log(C (1 + Λ)) + log(1/η) ≤ a Λ`, some nonzero polynomial of
degree `≤ k + 1` has `Re H_a(P, P) < 0`.

The zero count `#{|γ| ≤ S} ≤ 20 (S + 1)(A + log(S + 6))` bounds `deg K_Λ` by
`≍ √Λ log Λ`.  The level `Λ = s²`, `s = T⁴ log²(1/a)/a`, meets both conditions for a fixed large
`T` (`heatLevel_core`), with `deg K_Λ ≍ log³(1/a)/a`.  Hence:

**Theorem** (`exists_heatHankel_re_neg_small_time`).  Without RH there are `D` and `a₀ > 0` such
that for every `a ∈ (0, a₀]` some nonzero polynomial of degree `≤ D log³(1/a)/a` has
`Re H_a(P, P) < 0`.  Equivalently, some `Δ_M(a) ≤ 0` with `M ≤ D log³(1/a)/a + 1`
(`exists_heatMomentDet_nonpos_small_time`).

Together with the window `Δ_N(a) > 0` for `aN ≤ κ` (`heatMomentDet_pos_of_mul_le`), the largest
`a` at which all `Δ_M`, `M ≤ N`, are positive is pinned between `κ/N` and `≍ log³N/N` unless RH
holds.  So RH is equivalent to the window being super-polylogarithmic at arbitrarily small heat
times (`riemannHypothesis_iff_superPolylog_window`).
-/
open Complex Polynomial
open GaloisForLFunctions.HTGeometry (leadingMatrix)

namespace RHTower

noncomputable section

/-! ## An exponential–polynomial threshold -/

/-- If `M ≤ a (1 + Λ)` and `M log(C(1 + Λ)) + log(1/η) ≤ a Λ`, then
`e^{-aW} (C (1 + W))^M ≤ η` for every `W ≥ Λ`. -/
theorem exp_mul_pow_le_of_level {a C η Λ : ℝ} {M : ℕ} (hC : 0 < C) (hη : 0 < η) (hΛ : 0 ≤ Λ)
    (h1 : (M : ℝ) ≤ a * (1 + Λ))
    (h2 : M * Real.log (C * (1 + Λ)) + Real.log (1 / η) ≤ a * Λ) {W : ℝ} (hW : Λ ≤ W) :
    Real.exp (-(a * W)) * (C * (1 + W)) ^ M ≤ η := by
  have hW0 : 0 ≤ W := hΛ.trans hW
  have hCW : 0 < C * (1 + W) := by positivity
  have hCΛ : 0 < C * (1 + Λ) := by positivity
  have hq : 0 < (1 + W) / (1 + Λ) := by positivity
  have hsplit : Real.log (C * (1 + W)) =
      Real.log (C * (1 + Λ)) + Real.log ((1 + W) / (1 + Λ)) := by
    rw [← Real.log_mul hCΛ.ne' hq.ne']
    congr 1
    field_simp
  have hlogq : Real.log ((1 + W) / (1 + Λ)) ≤ (W - Λ) / (1 + Λ) := by
    have h := Real.log_le_sub_one_of_pos hq
    have he : (1 + W) / (1 + Λ) - 1 = (W - Λ) / (1 + Λ) := by
      field_simp
      ring
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hkey : (M : ℝ) * ((W - Λ) / (1 + Λ)) ≤ a * (W - Λ) := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    have : 0 ≤ W - Λ := by linarith
    nlinarith
  have hlogη : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
  have hMlog := mul_le_mul_of_nonneg_left hlogq hM0
  rw [← Real.exp_log hη, ← Real.exp_log (pow_pos hCW M), ← Real.exp_add, Real.exp_le_exp,
    Real.log_pow, hsplit, mul_add]
  linarith

/-! ## The level pair test -/

open Classical in
/-- The heat frequencies of real part `≤ Λ` other than `u, ū`. -/
def heatLevelRoots (Λ : ℝ) (u : ℂ) : Finset ℂ :=
  (heatFrequenciesBelow Λ).filter fun v => v ≠ u ∧ v ≠ (starRingEnd ℂ) u

/-- The level pair test `K_Λ · ((X − ū) + t (X − u))`. -/
def heatLevelPairTest (Λ : ℝ) (u t : ℂ) : ℂ[X] :=
  heatRootPoly (heatLevelRoots Λ u) * ((X - C ((starRingEnd ℂ) u)) + C t * (X - C u))

theorem mem_heatLevelRoots {Λ : ℝ} {u v : ℂ} :
    v ∈ heatLevelRoots Λ u ↔
      v ∈ heatFrequenciesBelow Λ ∧ v ≠ u ∧ v ≠ (starRingEnd ℂ) u := by
  classical
  unfold heatLevelRoots
  rw [Finset.mem_filter]

theorem conj_mem_heatLevelRoots {Λ : ℝ} {u v : ℂ} (hv : v ∈ heatLevelRoots Λ u) :
    (starRingEnd ℂ) v ∈ heatLevelRoots Λ u := by
  rw [mem_heatLevelRoots] at hv ⊢
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨conj_mem_heatFrequenciesBelow h1, fun h => h3 ?_, fun h => h2 ?_⟩
  · rw [← h, Complex.conj_conj]
  · simpa using congrArg (starRingEnd ℂ) h

theorem eval_heatLevelRoots_ne_zero (Λ : ℝ) (u : ℂ) :
    (heatRootPoly (heatLevelRoots Λ u)).eval u ≠ 0 :=
  eval_heatRootPoly_ne_zero fun h => (mem_heatLevelRoots.1 h).2.1 rfl

theorem eval_heatLevelRoots_conj (Λ : ℝ) (u w : ℂ) :
    (heatRootPoly (heatLevelRoots Λ u)).eval ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) ((heatRootPoly (heatLevelRoots Λ u)).eval w) :=
  eval_heatRootPoly_conj (fun _ hv => conj_mem_heatLevelRoots hv) w

/-- The pair value `e^{-au} P(u) \overline{P(ū)} = e^{-au} K(u)² (u − ū)² t̄`. -/
theorem heatHankelTermAt_heatLevelPairTest (a Λ : ℝ) (u t : ℂ) :
    heatHankelTermAt a (heatLevelPairTest Λ u t) (heatLevelPairTest Λ u t) u =
      Complex.exp (-(a : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2 *
        (u - (starRingEnd ℂ) u) ^ 2 * (starRingEnd ℂ) t := by
  have hK := eval_heatLevelRoots_conj Λ u u
  simp only [heatHankelTermAt, heatLevelPairTest, eval_mul, eval_add, eval_sub, eval_X, eval_C,
    hK, map_mul, map_sub, Complex.conj_conj, sub_self, mul_zero, add_zero, zero_add]
  ring

/-- With the phase `t = c/|c|`, `c = e^{-au} K(u)²`, the pair value is `−4 (Im u)² |c|`. -/
theorem heatHankelTermAt_heatLevelPairTest_phase (a Λ : ℝ) (u : ℂ) :
    let c := Complex.exp (-(a : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2
    heatHankelTermAt a (heatLevelPairTest Λ u (c / (‖c‖ : ℂ)))
        (heatLevelPairTest Λ u (c / (‖c‖ : ℂ))) u =
      -(((4 * u.im ^ 2 * ‖c‖ : ℝ)) : ℂ) := by
  intro c
  have hc : c ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (pow_ne_zero _ (eval_heatLevelRoots_ne_zero Λ u))
  have hnc : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc
  rw [heatHankelTermAt_heatLevelPairTest, map_div₀, Complex.conj_ofReal, Complex.sub_conj]
  have hcc : c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc Complex.exp (-(a : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2 *
          (((2 * u.im : ℝ) : ℂ) * I) ^ 2 * ((starRingEnd ℂ) c / (‖c‖ : ℂ))
      = (c * (starRingEnd ℂ) c) / (‖c‖ : ℂ) * (((2 * u.im : ℝ) : ℂ) * I) ^ 2 := by ring
    _ = -(((4 * u.im ^ 2 * ‖c‖ : ℝ)) : ℂ) := by
        rw [hcc]
        field_simp
        push_cast
        ring_nf
        rw [I_sq]
        ring

theorem norm_level_phase (a Λ : ℝ) (u : ℂ) :
    let c := Complex.exp (-(a : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2
    ‖c / (‖c‖ : ℂ)‖ = 1 := by
  intro c
  have hc : c ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (pow_ne_zero _ (eval_heatLevelRoots_ne_zero Λ u))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 hc)]

theorem norm_level_coefficient (a Λ : ℝ) (u : ℂ) :
    ‖Complex.exp (-(a : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2‖ =
      Real.exp (-(a * u.re)) * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 := by
  rw [norm_mul, Complex.norm_exp, norm_pow]
  congr 2
  simp

theorem natDegree_heatLevelPairTest_le (Λ : ℝ) (u t : ℂ) :
    (heatLevelPairTest Λ u t).natDegree ≤ (heatLevelRoots Λ u).card + 1 := by
  unfold heatLevelPairTest heatRootPoly
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · rw [natDegree_prod_of_monic _ _ fun v _ => monic_X_sub_C v]
    simp
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_X_sub_C]
    · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_sub_C])

theorem heatLevelPairTest_ne_zero (Λ : ℝ) {u : ℂ} (hu : 0 < u.im) (t : ℂ) :
    heatLevelPairTest Λ u t ≠ 0 := by
  intro h
  have := congrArg (fun P => P.eval u) h
  simp only [heatLevelPairTest, eval_mul, eval_add, eval_sub, eval_X, eval_C, sub_self, mul_zero,
    add_zero, eval_zero] at this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact eval_heatLevelRoots_ne_zero Λ u h1
  · rw [Complex.sub_conj] at h1
    have : (2 * u.im : ℝ) = 0 := by
      have := congrArg Complex.im h1
      simpa using this
    linarith

/-! ## The tail beyond the level -/

/-- Tail bound: above the level the pair test is controlled by `K_Λ(u)`. -/
theorem heatHankelTail_heatLevelPairTest_le {a Λ R d : ℝ} {u t : ℂ} (ht : ‖t‖ = 1) (hd : 0 < d)
    (hR : ‖u‖ ≤ R) (hsep : ∀ v ∈ heatLevelRoots Λ u, ‖v‖ < 2 * R + 2 → d ≤ ‖u - v‖)
    (q : XiZeroCopy) :
    heatHankelTail a Λ (heatLevelPairTest Λ u t) q ≤
      (if Λ < (xiHeatFrequency q).re then
        8 * (1 + R) ^ 2 * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 *
          (Real.exp (-(a * (xiHeatFrequency q).re)) *
            (((2 + (2 * R + 3) / d) * (1 + ‖xiHeatFrequency q‖)) ^
                (2 * (heatLevelRoots Λ u).card) * (1 + ‖xiHeatFrequency q‖) ^ 2))
        else 0) := by
  set S := heatLevelRoots Λ u
  set C₀ := 2 + (2 * R + 3) / d
  set w := xiHeatFrequency q
  have hR0 : 0 ≤ R := (norm_nonneg u).trans hR
  have hC₀ : 0 ≤ C₀ := by positivity
  have hroot : ∀ z : ℂ, ‖(heatRootPoly S).eval z‖ ≤
      (C₀ * (1 + ‖z‖)) ^ S.card * ‖(heatRootPoly S).eval u‖ := fun z =>
    norm_eval_heatRootPoly_le fun v hv => norm_sub_le_of_far_or_sep hd hR (hsep v hv)
  have hlin : ∀ z : ℂ, ‖(X - C ((starRingEnd ℂ) u) + C t * (X - C u) : ℂ[X]).eval z‖ ≤
      2 * (1 + R) * (1 + ‖z‖) := fun z => by
    simp only [eval_add, eval_sub, eval_mul, eval_X, eval_C]
    have h1 : ‖z - (starRingEnd ℂ) u‖ ≤ ‖z‖ + R := by
      calc ‖z - (starRingEnd ℂ) u‖ ≤ ‖z‖ + ‖(starRingEnd ℂ) u‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + R := by rw [Complex.norm_conj]; linarith
    have h2 : ‖t * (z - u)‖ ≤ ‖z‖ + R := by
      rw [norm_mul, ht, one_mul]
      calc ‖z - u‖ ≤ ‖z‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + R := by linarith
    calc ‖z - (starRingEnd ℂ) u + t * (z - u)‖ ≤ ‖z - (starRingEnd ℂ) u‖ + ‖t * (z - u)‖ :=
          norm_add_le _ _
      _ ≤ 2 * (‖z‖ + R) := by linarith
      _ ≤ 2 * (1 + R) * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
  have hP : ∀ z : ℂ, ‖(heatLevelPairTest Λ u t).eval z‖ ^ 2 ≤
      (C₀ * (1 + ‖z‖)) ^ (2 * S.card) * ‖(heatRootPoly S).eval u‖ ^ 2 *
        (4 * (1 + R) ^ 2 * (1 + ‖z‖) ^ 2) := fun z => by
    rw [heatLevelPairTest, eval_mul, norm_mul, mul_pow]
    have hk := hroot z
    have hl := hlin z
    have hk2 := pow_le_pow_left₀ (norm_nonneg _) hk 2
    have hl2 := pow_le_pow_left₀ (norm_nonneg _) hl 2
    calc ‖(heatRootPoly S).eval z‖ ^ 2 *
          ‖(X - C ((starRingEnd ℂ) u) + C t * (X - C u) : ℂ[X]).eval z‖ ^ 2
        ≤ ((C₀ * (1 + ‖z‖)) ^ S.card * ‖(heatRootPoly S).eval u‖) ^ 2 *
            (2 * (1 + R) * (1 + ‖z‖)) ^ 2 :=
          mul_le_mul hk2 hl2 (by positivity) (by positivity)
      _ = (C₀ * (1 + ‖z‖)) ^ (2 * S.card) * ‖(heatRootPoly S).eval u‖ ^ 2 *
            (4 * (1 + R) ^ 2 * (1 + ‖z‖) ^ 2) := by ring
  unfold heatHankelTail
  split_ifs with hlt
  · have h1 := hP w
    have h2 := hP ((starRingEnd ℂ) w)
    rw [Complex.norm_conj] at h2
    have he := (Real.exp_pos (-(a * w.re))).le
    calc Real.exp (-(a * w.re)) * (‖(heatLevelPairTest Λ u t).eval w‖ ^ 2 +
          ‖(heatLevelPairTest Λ u t).eval ((starRingEnd ℂ) w)‖ ^ 2)
        ≤ Real.exp (-(a * w.re)) * (2 * ((C₀ * (1 + ‖w‖)) ^ (2 * S.card) *
            ‖(heatRootPoly S).eval u‖ ^ 2 * (4 * (1 + R) ^ 2 * (1 + ‖w‖) ^ 2))) := by
          gcongr
          linarith
      _ = 8 * (1 + R) ^ 2 * ‖(heatRootPoly S).eval u‖ ^ 2 *
            (Real.exp (-(a * w.re)) * ((C₀ * (1 + ‖w‖)) ^ (2 * S.card) * (1 + ‖w‖) ^ 2)) := by
          ring
  · exact le_rfl

/-! ## Negativity at a level -/

theorem summable_inv_one_add_norm_xiHeatFrequency :
    Summable fun q : XiZeroCopy => 1 / (1 + ‖xiHeatFrequency q‖) := by
  refine xiSpectralPoint_inv_sq_summable.of_nonneg_of_le (fun _ => by positivity) fun q => ?_
  have hz : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
  have hn : ‖xiHeatFrequency q‖ = ‖xiSpectralPoint q‖ ^ 2 := by rw [xiHeatFrequency, norm_pow]
  rw [hn]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Above the level, `e^{-aW} (C₀(1 + |w|))^{2j} (1 + |w|)² ≤ η / (1 + |w|)`. -/
theorem exp_mul_level_weight_le {a Λ C₀ η : ℝ} {j k : ℕ} (hC₀ : 1 ≤ C₀) (hη : 0 < η)
    (hΛ : 0 ≤ Λ) (hjk : j ≤ k) (h1 : ((2 * k + 3 : ℕ) : ℝ) ≤ a * (1 + Λ))
    (h2 : ((2 * k + 3 : ℕ) : ℝ) * Real.log (2 * C₀ * (1 + Λ)) + Real.log (1 / η) ≤ a * Λ)
    {q : XiZeroCopy} (hq : Λ < (xiHeatFrequency q).re) :
    Real.exp (-(a * (xiHeatFrequency q).re)) *
        ((C₀ * (1 + ‖xiHeatFrequency q‖)) ^ (2 * j) * (1 + ‖xiHeatFrequency q‖) ^ 2) ≤
      η * (1 / (1 + ‖xiHeatFrequency q‖)) := by
  set w := xiHeatFrequency q
  set W := w.re
  have hW0 : 0 ≤ W := hΛ.trans hq.le
  have hnw : ‖w‖ ≤ W + 1 / 2 := norm_xiHeatFrequency_le_re q
  have hn1 : 0 < 1 + ‖w‖ := by positivity
  have hb : 1 + ‖w‖ ≤ 2 * (1 + W) := by linarith
  have hB1 : 1 ≤ 2 * C₀ * (1 + W) := by nlinarith
  have hlevel := exp_mul_pow_le_of_level (C := 2 * C₀) (M := 2 * k + 3) (by positivity) hη hΛ h1
    h2 hq.le
  have hpow1 : (C₀ * (1 + ‖w‖)) ^ (2 * j) ≤ (2 * C₀ * (1 + W)) ^ (2 * j) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hpow2 : (1 + ‖w‖) ^ 3 ≤ (2 * C₀ * (1 + W)) ^ 3 :=
    pow_le_pow_left₀ hn1.le (by nlinarith) _
  have hpow3 : (2 * C₀ * (1 + W)) ^ (2 * j + 3) ≤ (2 * C₀ * (1 + W)) ^ (2 * k + 3) :=
    pow_le_pow_right₀ hB1 (by omega)
  have he := Real.exp_pos (-(a * W))
  rw [mul_one_div, le_div_iff₀ hn1]
  calc Real.exp (-(a * W)) * ((C₀ * (1 + ‖w‖)) ^ (2 * j) * (1 + ‖w‖) ^ 2) * (1 + ‖w‖)
      = Real.exp (-(a * W)) * ((C₀ * (1 + ‖w‖)) ^ (2 * j) * (1 + ‖w‖) ^ 3) := by ring
    _ ≤ Real.exp (-(a * W)) * ((2 * C₀ * (1 + W)) ^ (2 * j) * (2 * C₀ * (1 + W)) ^ 3) := by
        gcongr
    _ = Real.exp (-(a * W)) * (2 * C₀ * (1 + W)) ^ (2 * j + 3) := by rw [pow_add]
    _ ≤ Real.exp (-(a * W)) * (2 * C₀ * (1 + W)) ^ (2 * k + 3) := by gcongr
    _ ≤ η := hlevel

/-- **Negativity at a level.**  For an upper off-line frequency `u` there are `C, η > 0` such that
for every `a ∈ (0, 1]`, every level `Λ ≥ max(Re u, 0)` and every `k ≥ #(roots of K_Λ)` with
`2k + 3 ≤ a (1 + Λ)` and `(2k + 3) log(C (1 + Λ)) + log(1/η) ≤ a Λ`, some nonzero polynomial of
degree `≤ k + 1` has `Re H_a(P, P) < 0`. -/
theorem exists_heatHankel_re_neg_of_level {u : ℂ} (hu : u ∈ xiUpperFrequencies) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ a Λ : ℝ, 0 < a → a ≤ 1 → u.re ≤ Λ → 0 ≤ Λ → ∀ k : ℕ,
      (heatLevelRoots Λ u).card ≤ k →
      ((2 * k + 3 : ℕ) : ℝ) ≤ a * (1 + Λ) →
      ((2 * k + 3 : ℕ) : ℝ) * Real.log (C * (1 + Λ)) + Real.log (1 / η) ≤ a * Λ →
      ∃ P : ℂ[X], P ≠ 0 ∧ P.natDegree ≤ k + 1 ∧ (heatHankel a P P).re < 0 := by
  obtain ⟨q₀, hq₀, hupos⟩ := hu
  set R := ‖u‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg u
  obtain ⟨d, hd, hdsep⟩ := exists_pos_le_norm_sub {u} (heatFrequenciesBelow (2 * R + 2))
  set C₀ := 2 + (2 * R + 3) / d with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ (2 * R + 3) / d := by positivity
    linarith
  set S₁ := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) with hS₁
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun _ => by positivity
  set η := u.im ^ 2 * Real.exp (-|u.re|) / ((1 + R) ^ 2 * (S₁ + 1)) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨2 * C₀, η, by positivity, hη0, fun a Λ ha ha1 huΛ hΛ k hk h1 h2 => ?_⟩
  set c := Complex.exp (-(a : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2 with hc
  set P := heatLevelPairTest Λ u (c / (‖c‖ : ℂ)) with hP
  refine ⟨P, heatLevelPairTest_ne_zero Λ hupos _,
    (natDegree_heatLevelPairTest_le Λ u _).trans (by omega), ?_⟩
  have hsep : ∀ v ∈ heatLevelRoots Λ u, ‖v‖ < 2 * R + 2 → d ≤ ‖u - v‖ := by
    intro v hv hvR
    obtain ⟨hvB, hvu, hvu'⟩ := mem_heatLevelRoots.1 hv
    obtain ⟨q, rfl, -⟩ := mem_heatFrequenciesBelow.1 hvB
    exact hdsep u (Finset.mem_singleton_self u) _
      (mem_heatFrequenciesBelow.2 ⟨q, rfl, (Complex.re_le_norm _).trans hvR.le⟩) hvu hvu'
  set Ω : ℝ := 4 * u.im ^ 2 * ‖c‖ with hΩ
  have hval : heatHankelTermAt a P P u = -((Ω : ℝ) : ℂ) :=
    heatHankelTermAt_heatLevelPairTest_phase a Λ u
  have hlow : ∀ q : XiZeroCopy, (xiHeatFrequency q).re ≤ Λ →
      (∀ _i : Unit, xiHeatFrequency q ≠ u ∧ xiHeatFrequency q ≠ (starRingEnd ℂ) u) →
      ∀ _i : Unit, P.eval (xiHeatFrequency q) = 0 ∧
        P.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0 := by
    intro q hle hne _
    have hmem : xiHeatFrequency q ∈ heatLevelRoots Λ u :=
      mem_heatLevelRoots.2 ⟨mem_heatFrequenciesBelow.2 ⟨q, rfl, hle⟩, (hne ()).1, (hne ()).2⟩
    have hK0 := eval_heatRootPoly_eq_zero hmem
    have hK0' := eval_heatRootPoly_eq_zero (conj_mem_heatLevelRoots hmem)
    simp only [hP, heatLevelPairTest, eval_mul, hK0, hK0', zero_mul, true_and]
  have hsum := re_heatHankel_sum_le ha (fun _ : Unit => P) (fun _ => u) (fun _ => q₀)
    (fun _ => Ω) (fun _ => hq₀) (fun _ => hupos) (Function.injective_of_subsingleton _)
    (fun _ => huΛ) hlow (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun _ => hval)
    (fun _ => by positivity) (fun _ => 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, norm_one, one_pow, one_mul,
    Fintype.card_unit, Nat.cast_one] at hsum
  have hKu := norm_pos_iff.2 (eval_heatLevelRoots_ne_zero Λ u)
  have hpt : ∀ q, heatHankelTail a Λ P q ≤
      8 * (1 + R) ^ 2 * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 *
        (η * (1 / (1 + ‖xiHeatFrequency q‖))) := by
    intro q
    refine (heatHankelTail_heatLevelPairTest_le (norm_level_phase a Λ u) hd le_rfl hsep q).trans ?_
    split_ifs with hlt
    · exact mul_le_mul_of_nonneg_left (exp_mul_level_weight_le hC₀1 hη0 hΛ hk h1 h2 hlt)
        (by positivity)
    · positivity
  have htail : ∑' q, heatHankelTail a Λ P q ≤
      8 * (1 + R) ^ 2 * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 * (η * S₁) := by
    calc ∑' q, heatHankelTail a Λ P q
        ≤ ∑' q, 8 * (1 + R) ^ 2 * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 *
            (η * (1 / (1 + ‖xiHeatFrequency q‖))) :=
          Summable.tsum_le_tsum hpt (summable_heatHankelTail ha Λ P)
            ((summable_inv_one_add_norm_xiHeatFrequency.mul_left η).mul_left _)
      _ = 8 * (1 + R) ^ 2 * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 * (η * S₁) := by
          rw [tsum_mul_left, tsum_mul_left]
  have hcn : ‖c‖ = Real.exp (-(a * u.re)) * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 :=
    norm_level_coefficient a Λ u
  have hexp : Real.exp (-|u.re|) ≤ Real.exp (-(a * u.re)) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    calc a * u.re ≤ a * |u.re| := mul_le_mul_of_nonneg_left (le_abs_self _) ha.le
      _ ≤ 1 * |u.re| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
      _ = |u.re| := one_mul _
  have hηS : η * ((1 + R) ^ 2 * S₁) < u.im ^ 2 * Real.exp (-|u.re|) := by
    have hden : 0 < (1 + R) ^ 2 * (S₁ + 1) := by positivity
    have hnum : 0 < u.im ^ 2 * Real.exp (-|u.re|) := by positivity
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [mul_pos hnum (by positivity : (0 : ℝ) < (1 + R) ^ 2)]
  have hK2 : 0 < ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 := by positivity
  have hkey : 4 * (1 + R) ^ 2 * (η * S₁) * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 < Ω := by
    rw [hΩ, hcn]
    have := mul_lt_mul_of_pos_right hηS hK2
    nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ u.im ^ 2 *
      ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2)]
  linarith

/-! ## Counting the roots and choosing the level -/

/-- The count envelope `20 (s + 2)(|A| + log(s + 7))`. -/
def heatLevelCount (A s : ℝ) : ℝ := 20 * (s + 2) * (|A| + Real.log (s + 7))

/-- The algebraic core of the level choice, in the variables `L = log(1/a) ≥ 1`, `ia = 1/a ≥ 1`
and `T ≥ 1`, with `B = T⁴`, `s = B L² ia`. -/
theorem heatLevel_core {A C η L ia T a : ℝ} (hC : 0 < C) (ha : 0 < a) (haia : a * ia = 1)
    (hL1 : 1 ≤ L) (hia1 : 1 ≤ ia) (hT1 : 1 ≤ T)
    (hlogs : Real.log (T ^ 4 * L ^ 2 * ia) ≤ Real.log (T ^ 4) + 3 * L)
    (hTbig : (120 * (|A| + Real.log 8 + 3 + 4) + 5) * (|Real.log C| + Real.log 2 + 6 + 8) +
      |Real.log (1 / η)| + (120 * (|A| + Real.log 8 + 3 + 4) + 5) + 1 ≤ T) :
    ((2 * ⌈heatLevelCount A (T ^ 4 * L ^ 2 * ia)⌉₊ + 3 : ℕ) : ℝ) ≤
        a * (1 + (T ^ 4 * L ^ 2 * ia) ^ 2) ∧
      ((2 * ⌈heatLevelCount A (T ^ 4 * L ^ 2 * ia)⌉₊ + 3 : ℕ) : ℝ) *
          Real.log (C * (1 + (T ^ 4 * L ^ 2 * ia) ^ 2)) + Real.log (1 / η) ≤
        a * (T ^ 4 * L ^ 2 * ia) ^ 2 ∧
      ((⌈heatLevelCount A (T ^ 4 * L ^ 2 * ia)⌉₊ + 1 : ℕ) : ℝ) ≤
        (60 * (|A| + Real.log 8 + 3 + Real.log (T ^ 4)) * T ^ 4 + 2) * L ^ 3 * ia := by
  obtain ⟨B, hB⟩ : ∃ B, B = T ^ 4 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = B * L ^ 2 * ia := ⟨_, rfl⟩
  rw [← hB, ← hs]
  rw [← hB, ← hs] at hlogs
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = |A| + Real.log 8 + 3 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = |Real.log C| + Real.log 2 + 6 := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c, c = |Real.log (1 / η)| := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ m, m = 120 * (c₁ + 4) + 5 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ m, m = M₁ * (c₂ + 8) + c₃ := ⟨_, rfl⟩
  rw [← hc₁, ← hc₂, ← hc₃, ← hM₁, ← hM] at hTbig
  rw [show |A| + Real.log 8 + 3 = c₁ from hc₁.symm]
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; exact abs_nonneg _
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hT0 : 0 < T := by linarith
  have hB1 : 1 ≤ B := hB ▸ one_le_pow₀ hT1
  have hB0 : 0 < B := by linarith
  have hlogB : Real.log B ≤ 4 * T := by
    rw [hB, Real.log_pow]
    push_cast
    linarith [Real.log_le_self hT0.le]
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hL0 : 0 < L := by linarith
  have hia0 : 0 < ia := by linarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB1 hL2) hia1
  have hs0 : 0 < s := by linarith
  -- the count envelope
  have hlogs7 : Real.log (s + 7) ≤ Real.log 8 + Real.log B + 3 * L := by
    calc Real.log (s + 7) ≤ Real.log (8 * s) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 8 + Real.log s := Real.log_mul (by norm_num) hs0.ne'
      _ ≤ Real.log 8 + Real.log B + 3 * L := by linarith
  obtain ⟨K, hK⟩ : ∃ K, K = heatLevelCount A s := ⟨_, rfl⟩
  rw [← hK]
  have hlogs70 : 0 ≤ Real.log (s + 7) := Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ K := by rw [hK, heatLevelCount]; positivity
  have hX : |A| + Real.log (s + 7) ≤ (c₁ + Real.log B) * L := by
    have h0 : 0 ≤ |A| + Real.log 8 + Real.log B := by positivity
    have h1 : |A| + Real.log 8 + Real.log B ≤ (|A| + Real.log 8 + Real.log B) * L :=
      le_mul_of_one_le_right h0 hL1
    rw [hc₁]
    linarith
  have hKle : K ≤ 60 * (c₁ + Real.log B) * B * L ^ 3 * ia := by
    have hX0 : 0 ≤ |A| + Real.log (s + 7) := by positivity
    calc K = 20 * (s + 2) * (|A| + Real.log (s + 7)) := by rw [hK, heatLevelCount]
      _ ≤ 20 * (3 * s) * ((c₁ + Real.log B) * L) :=
          mul_le_mul (by linarith) hX hX0 (by positivity)
      _ = 60 * (c₁ + Real.log B) * B * L ^ 3 * ia := by rw [hs]; ring
  have hceil : (⌈K⌉₊ : ℝ) ≤ K + 1 := (Nat.ceil_lt_add_one hK0).le
  obtain ⟨D₁, hD₁⟩ : ∃ d, d = c₁ + Real.log B := ⟨_, rfl⟩
  rw [← hD₁] at hKle
  rw [← hD₁]
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁]; positivity
  have hD₁T : D₁ ≤ (c₁ + 4) * T := by
    have := le_mul_of_one_le_right hc₁0 hT1
    rw [hD₁]
    linarith
  have hDB : 120 * D₁ * B + 5 ≤ M₁ * T ^ 5 := by
    have h1 : 120 * D₁ * B ≤ 120 * ((c₁ + 4) * T) * T ^ 4 := by
      rw [hB]
      have := mul_le_mul_of_nonneg_right hD₁T (by positivity : (0 : ℝ) ≤ T ^ 4)
      linarith
    have hT5 : 1 ≤ T ^ 5 := one_le_pow₀ hT1
    rw [hM₁]
    linarith
  have hcount : ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) ≤ (120 * D₁ * B + 5) * (L ^ 3 * ia) := by
    push_cast
    have h3 : 1 ≤ L ^ 3 * ia := one_le_mul_of_one_le_of_one_le hL3 hia1
    have hD : 0 ≤ 120 * D₁ * B := by positivity
    have h5 : (5 : ℝ) ≤ 5 * (L ^ 3 * ia) := by linarith
    have hK2 : 2 * K ≤ 120 * D₁ * B * (L ^ 3 * ia) := by linarith
    linarith
  have haΛ : a * s ^ 2 = B ^ 2 * (L ^ 4 * ia) := by
    rw [hs]
    have : a * (B * L ^ 2 * ia) ^ 2 = B ^ 2 * (L ^ 4 * ia) * (a * ia) := by ring
    rw [this, haia, mul_one]
  have hB2 : B ^ 2 = T ^ 8 := by rw [hB]; ring
  have hTM₁ : M₁ ≤ T := by linarith
  have hTM : M ≤ T := by linarith
  have hpowT : M₁ * T ^ 5 ≤ T ^ 8 := by
    have : M₁ * T ^ 5 ≤ T * T ^ 5 := mul_le_mul_of_nonneg_right hTM₁ (by positivity)
    have h2 : T * T ^ 5 ≤ T ^ 8 := by
      have : T ^ 8 = T ^ 2 * (T * T ^ 5) := by ring
      rw [this]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hT1)
    linarith
  have hpowT' : M * T ^ 6 ≤ T ^ 8 := by
    have : M * T ^ 6 ≤ T * T ^ 6 := mul_le_mul_of_nonneg_right hTM (by positivity)
    have h2 : T * T ^ 6 ≤ T ^ 8 := by
      have : T ^ 8 = T * (T * T ^ 6) := by ring
      rw [this]
      exact le_mul_of_one_le_left (by positivity) hT1
    nlinarith
  have hL34 : L ^ 3 * ia ≤ L ^ 4 * ia := by
    have : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hia0.le
  refine ⟨?_, ?_, ?_⟩
  · calc ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) ≤ (120 * D₁ * B + 5) * (L ^ 3 * ia) := hcount
      _ ≤ T ^ 8 * (L ^ 3 * ia) :=
          mul_le_mul_of_nonneg_right (hDB.trans hpowT) (by positivity)
      _ ≤ T ^ 8 * (L ^ 4 * ia) := mul_le_mul_of_nonneg_left hL34 (by positivity)
      _ = B ^ 2 * (L ^ 4 * ia) := by rw [hB2]
      _ = a * s ^ 2 := haΛ.symm
      _ ≤ a * (1 + s ^ 2) := by linarith
  · obtain ⟨E₁, hE₁⟩ : ∃ e, e = |Real.log C| + Real.log 2 + 2 * Real.log B + 6 := ⟨_, rfl⟩
    have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; positivity
    have hE₁T : E₁ ≤ (c₂ + 8) * T := by
      have := le_mul_of_one_le_right hc₂0 hT1
      rw [hE₁]
      linarith [hc₂, hlogB]
    have hlogC : Real.log (C * (1 + s ^ 2)) ≤ E₁ * L := by
      rw [Real.log_mul hC.ne' (by positivity)]
      have h2s : 1 + s ^ 2 ≤ 2 * s ^ 2 := by
        have : 1 ≤ s ^ 2 := one_le_pow₀ hs1
        linarith
      have hl : Real.log (1 + s ^ 2) ≤ Real.log 2 + 2 * Real.log s := by
        calc Real.log (1 + s ^ 2) ≤ Real.log (2 * s ^ 2) := Real.log_le_log (by positivity) h2s
          _ = Real.log 2 + 2 * Real.log s := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      have h0 : 0 ≤ |Real.log C| + Real.log 2 + 2 * Real.log B := by positivity
      have hpart : |Real.log C| + Real.log 2 + 2 * Real.log B ≤
          (|Real.log C| + Real.log 2 + 2 * Real.log B) * L := le_mul_of_one_le_right h0 hL1
      rw [hE₁]
      linarith [le_abs_self (Real.log C)]
    have hk0 : (0 : ℝ) ≤ ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : 1 ≤ L ^ 4 * ia := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hia1
    have hc3 : Real.log (1 / η) ≤ c₃ * (L ^ 4 * ia) := by
      have := le_abs_self (Real.log (1 / η))
      rw [← hc₃] at this
      have := le_mul_of_one_le_right hc₃0 h4
      linarith
    have hprod : ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) * Real.log (C * (1 + s ^ 2)) ≤
        (120 * D₁ * B + 5) * E₁ * (L ^ 4 * ia) := by
      calc ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) * Real.log (C * (1 + s ^ 2))
          ≤ ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) * (E₁ * L) := mul_le_mul_of_nonneg_left hlogC hk0
        _ ≤ ((120 * D₁ * B + 5) * (L ^ 3 * ia)) * (E₁ * L) :=
            mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = (120 * D₁ * B + 5) * E₁ * (L ^ 4 * ia) := by ring
    have hcoef : (120 * D₁ * B + 5) * E₁ + c₃ ≤ M * T ^ 6 := by
      have h1 : (120 * D₁ * B + 5) * E₁ ≤ (M₁ * T ^ 5) * ((c₂ + 8) * T) :=
        mul_le_mul hDB hE₁T hE₁0 (by positivity)
      have h2 : c₃ ≤ c₃ * T ^ 6 := le_mul_of_one_le_right hc₃0 (one_le_pow₀ hT1)
      rw [hM]
      linarith
    calc ((2 * ⌈K⌉₊ + 3 : ℕ) : ℝ) * Real.log (C * (1 + s ^ 2)) + Real.log (1 / η)
        ≤ ((120 * D₁ * B + 5) * E₁ + c₃) * (L ^ 4 * ia) := by linarith
      _ ≤ (M * T ^ 6) * (L ^ 4 * ia) := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ T ^ 8 * (L ^ 4 * ia) := mul_le_mul_of_nonneg_right hpowT' (by positivity)
      _ = a * s ^ 2 := by rw [haΛ, hB2]
  · have h : ((⌈K⌉₊ + 1 : ℕ) : ℝ) ≤ K + 2 := by push_cast; linarith
    have h3 : 1 ≤ L ^ 3 * ia := one_le_mul_of_one_le_of_one_le hL3 hia1
    have hD : 0 ≤ 60 * D₁ * B := by positivity
    have h2 : (2 : ℝ) ≤ 2 * (L ^ 3 * ia) := by linarith
    have hK' : K ≤ 60 * D₁ * B * (L ^ 3 * ia) := by linarith
    have : (60 * D₁ * B + 2) * L ^ 3 * ia = 60 * D₁ * B * (L ^ 3 * ia) + 2 * (L ^ 3 * ia) := by
      ring
    rw [this]
    linarith

/-! ## The ceiling -/

/-- An upper off-line frequency exists without RH. -/
theorem exists_mem_xiUpperFrequencies_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ u, u ∈ xiUpperFrequencies := by
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at hRH
  push Not at hRH
  obtain ⟨q, hq⟩ := hRH
  have hw := (xiHeatFrequency_im_ne_zero_iff q).2 hq
  rcases lt_or_gt_of_ne hw with h | h
  · refine ⟨_, xiZeroCopyLineConjEquiv q, rfl, ?_⟩
    rw [xiHeatFrequency_lineConj, Complex.conj_im]
    linarith
  · exact ⟨_, q, rfl, h⟩

/-- `#{heat frequencies of real part ≤ Λ} ≤ 20 (√(Λ+1) + 1)(|A| + log(√(Λ+1) + 6))`. -/
theorem card_heatFrequenciesBelow_le_log (Λ : ℝ) :
    ((heatFrequenciesBelow Λ).card : ℝ) ≤ 20 * (Real.sqrt (Λ + 1) + 1) *
      (|xiLineTwoLogDerivConstant| + Real.log (Real.sqrt (Λ + 1) + 6)) := by
  classical
  have h2 : (heatFrequenciesBelow Λ).card ≤ (xiCopiesBelow (Real.sqrt (Λ + 1))).card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  have h3 := card_xiCopiesBelow_le_log (Real.sqrt_nonneg (Λ + 1))
  have hp : 0 ≤ 20 * (Real.sqrt (Λ + 1) + 1) := by positivity
  have h4 : 20 * (Real.sqrt (Λ + 1) + 1) *
        (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (Λ + 1) + 6)) ≤
      20 * (Real.sqrt (Λ + 1) + 1) *
        (|xiLineTwoLogDerivConstant| + Real.log (Real.sqrt (Λ + 1) + 6)) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self xiLineTwoLogDerivConstant]) hp
  calc ((heatFrequenciesBelow Λ).card : ℝ) ≤ (xiCopiesBelow (Real.sqrt (Λ + 1))).card := by
        exact_mod_cast h2
    _ ≤ _ := h3
    _ ≤ _ := h4

/-- **Admissible levels.**  For `C > 0` and `η, U` there are `D` and `a₀ > 0` such that for every
`a ∈ (0, a₀]` some level `Λ ≥ max(U, 0)` and `k ≥ #{heat frequencies of real part ≤ Λ}` satisfy
`2k + 3 ≤ a (1 + Λ)`, `(2k + 3) log(C (1 + Λ)) + log(1/η) ≤ a Λ` and
`k + 1 ≤ D log³(1/a)/a`. -/
theorem exists_heatLevel {C : ℝ} (hC : 0 < C) (η U : ℝ) :
    ∃ D a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∃ Λ : ℝ, U ≤ Λ ∧ 0 ≤ Λ ∧ ∃ k : ℕ, (heatFrequenciesBelow Λ).card ≤ k ∧
        ((2 * k + 3 : ℕ) : ℝ) ≤ a * (1 + Λ) ∧
        ((2 * k + 3 : ℕ) : ℝ) * Real.log (C * (1 + Λ)) + Real.log (1 / η) ≤ a * Λ ∧
        ((k : ℝ) + 1) ≤ D * Real.log (1 / a) ^ 3 / a := by
  obtain ⟨A, hA⟩ : ∃ A, A = xiLineTwoLogDerivConstant := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = (120 * (|A| + Real.log 8 + 3 + 4) + 5) *
      (|Real.log C| + Real.log 2 + 6 + 8) + |Real.log (1 / η)| +
      (120 * (|A| + Real.log 8 + 3 + 4) + 5) + 1 := ⟨_, rfl⟩
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT1 : 1 ≤ T := by
    have : 0 ≤ (120 * (|A| + Real.log 8 + 3 + 4) + 5) * (|Real.log C| + Real.log 2 + 6 + 8) +
        |Real.log (1 / η)| + (120 * (|A| + Real.log 8 + 3 + 4) + 5) := by positivity
    rw [hT]
    linarith
  refine ⟨60 * (|A| + Real.log 8 + 3 + Real.log (T ^ 4)) * T ^ 4 + 2,
    min (Real.exp (-1)) (1 / (1 + |U|)), lt_min (Real.exp_pos _) (by positivity),
    fun a ha haa₀ => ?_⟩
  obtain ⟨ia, hia⟩ : ∃ x, x = 1 / a := ⟨_, rfl⟩
  have hia0 : 0 < ia := by rw [hia]; positivity
  have haia : a * ia = 1 := by rw [hia]; field_simp
  have hae : a ≤ Real.exp (-1) := haa₀.trans (min_le_left _ _)
  have ha1 : a ≤ 1 := hae.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hiaU : 1 + |U| ≤ ia := by
    have h := haa₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    rw [hia, le_div_iff₀ ha]
    linarith
  have hia1 : 1 ≤ ia := by linarith [abs_nonneg U]
  obtain ⟨L, hL⟩ : ∃ x, x = Real.log ia := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    have h : Real.exp 1 ≤ ia := by
      rw [hia, le_div_iff₀ ha]
      calc Real.exp 1 * a ≤ Real.exp 1 * Real.exp (-1) :=
            mul_le_mul_of_nonneg_left hae (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ L := hL ▸ Real.log_le_log (Real.exp_pos 1) h
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hlogs : Real.log (T ^ 4 * L ^ 2 * ia) ≤ Real.log (T ^ 4) + 3 * L := by
    rw [Real.log_mul (by positivity) hia0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow L, ← hL]
    have := Real.log_le_self hL0.le
    push_cast
    linarith
  obtain ⟨h1, h2, h3⟩ := heatLevel_core (A := A) (η := η) hC ha haia hL1 hia1 hT1 hlogs
    (le_of_eq hT.symm)
  obtain ⟨s, hs⟩ : ∃ x, x = T ^ 4 * L ^ 2 * ia := ⟨_, rfl⟩
  rw [← hs] at h1 h2 h3
  have hs1 : ia ≤ s := by
    rw [hs]
    exact le_mul_of_one_le_left hia0.le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT1) (one_le_pow₀ hL1))
  have hs1' : 1 ≤ s := hia1.trans hs1
  have hs0 : 0 ≤ s := by linarith
  have hss : s ≤ s ^ 2 := le_self_pow₀ hs1' (by norm_num)
  have huΛ : U ≤ s ^ 2 := by linarith [le_abs_self U]
  -- the root count
  have hcard : (heatFrequenciesBelow (s ^ 2)).card ≤ ⌈heatLevelCount A s⌉₊ := by
    have hsq : Real.sqrt (s ^ 2 + 1) ≤ s + 1 :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hsq0 : 0 ≤ Real.sqrt (s ^ 2 + 1) := Real.sqrt_nonneg _
    have hlog : Real.log (Real.sqrt (s ^ 2 + 1) + 6) ≤ Real.log (s + 7) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (Real.sqrt (s ^ 2 + 1) + 6) := Real.log_nonneg (by linarith)
    have hc := card_heatFrequenciesBelow_le_log (s ^ 2)
    rw [← hA] at hc
    have hmono : 20 * (Real.sqrt (s ^ 2 + 1) + 1) *
          (|A| + Real.log (Real.sqrt (s ^ 2 + 1) + 6)) ≤
        heatLevelCount A s := by
      rw [heatLevelCount]
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    exact_mod_cast hc.trans (hmono.trans (Nat.le_ceil _))
  refine ⟨s ^ 2, huΛ, by positivity, ⌈heatLevelCount A s⌉₊, hcard, h1, h2, ?_⟩
  calc ((⌈heatLevelCount A s⌉₊ : ℕ) + 1 : ℝ) = ((⌈heatLevelCount A s⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (60 * (|A| + Real.log 8 + 3 + Real.log (T ^ 4)) * T ^ 4 + 2) * L ^ 3 * ia := h3
    _ = (60 * (|A| + Real.log 8 + 3 + Real.log (T ^ 4)) * T ^ 4 + 2) *
          Real.log (1 / a) ^ 3 / a := by rw [hL, hia]; ring

/-- **Small-time ceiling of the heat Hankel window.**  Without RH there are `D` and `a₀ > 0` such
that for every heat time `a ∈ (0, a₀]` some nonzero polynomial of degree
`≤ D log³(1/a) / a` has `Re H_a(P, P) < 0`. -/
theorem exists_heatHankel_re_neg_small_time (hRH : ¬ RiemannHypothesis) :
    ∃ D a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∃ P : ℂ[X], P ≠ 0 ∧ (P.natDegree : ℝ) ≤ D * Real.log (1 / a) ^ 3 / a ∧
        (heatHankel a P P).re < 0 := by
  obtain ⟨u, hu⟩ := exists_mem_xiUpperFrequencies_of_not_riemannHypothesis hRH
  obtain ⟨C, η, hC, hη, hlevel⟩ := exists_heatHankel_re_neg_of_level hu
  obtain ⟨D, a₀, ha₀, hΛ⟩ := exists_heatLevel hC η u.re
  refine ⟨D, min a₀ 1, lt_min ha₀ one_pos, fun a ha haa₀ => ?_⟩
  obtain ⟨Λ, huΛ, hΛ0, k, hk, h1, h2, h3⟩ := hΛ a ha (haa₀.trans (min_le_left _ _))
  have hcard : (heatLevelRoots Λ u).card ≤ k := (Finset.card_filter_le _ _).trans hk
  obtain ⟨P, hP0, hPdeg, hneg⟩ :=
    hlevel a Λ ha (haa₀.trans (min_le_right _ _)) huΛ hΛ0 k hcard h1 h2
  refine ⟨P, hP0, ?_, hneg⟩
  calc (P.natDegree : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hPdeg
    _ ≤ D * Real.log (1 / a) ^ 3 / a := h3

/-- **The determinant form of the ceiling.**  Without RH there are `D` and `a₀ > 0` such that for
every `a ∈ (0, a₀]` some leading heat Hankel determinant `Δ_M(a)` with
`M ≤ D log³(1/a)/a + 1` is `≤ 0`. -/
theorem exists_heatMomentDet_nonpos_small_time (hRH : ¬ RiemannHypothesis) :
    ∃ D a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∃ M : ℕ, (M : ℝ) ≤ D * Real.log (1 / a) ^ 3 / a + 1 ∧
        (leadingMatrix (heatMomentArray a) M).det ≤ 0 := by
  obtain ⟨D, a₀, ha₀, h⟩ := exists_heatHankel_re_neg_small_time hRH
  refine ⟨D, a₀, ha₀, fun a ha haa₀ => ?_⟩
  obtain ⟨P, -, hPdeg, hneg⟩ := h a ha haa₀
  by_contra hall
  push Not at hall
  refine hneg.not_ge (heatHankel_re_nonneg_of_det_pos ha (N := P.natDegree + 1)
    (fun k hk => hall k ?_) (Nat.lt_succ_self _))
  have : (k : ℝ) ≤ P.natDegree + 1 := by exact_mod_cast hk
  linarith

/-- **RH as a super-polylogarithmic window.**  RH holds iff for every `D` and every `a₀ > 0` there
is a heat time `a ∈ (0, a₀]` at which every leading heat Hankel determinant `Δ_M(a)` with
`M ≤ D log³(1/a)/a + 1` is positive. -/
theorem riemannHypothesis_iff_superPolylog_window :
    RiemannHypothesis ↔ ∀ D a₀ : ℝ, 0 < a₀ → ∃ a : ℝ, 0 < a ∧ a ≤ a₀ ∧
      ∀ M : ℕ, (M : ℝ) ≤ D * Real.log (1 / a) ^ 3 / a + 1 →
        0 < (leadingMatrix (heatMomentArray a) M).det := by
  constructor
  · intro hRH D a₀ ha₀
    exact ⟨a₀, ha₀, le_rfl, fun M _ => (riemannHypothesis_iff_heatMomentDet_pos ha₀).1 hRH M⟩
  · intro h
    by_contra hRH
    obtain ⟨D, a₀, ha₀, hneg⟩ := exists_heatMomentDet_nonpos_small_time hRH
    obtain ⟨a, ha, haa₀, hpos⟩ := h D a₀ ha₀
    obtain ⟨M, hM, hdet⟩ := hneg a ha haa₀
    exact (hpos M hM).not_ge hdet

end

end RHTower
