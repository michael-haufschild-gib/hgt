import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# Super-Gaussian Taylor decay: arbitrarily wide Newton plateaux

A transcendental entire function whose Taylor coefficients decay faster than every Gaussian,

```text
∀ A > 0, ∃ C_A, ‖a n‖ ≤ C_A exp(-A n²),                                    (SG)
```

has arbitrarily wide *plateaux* of the logarithmic Newton envelope: intervals of `log r` on which a
single Taylor monomial dominates the whole series.  This file proves that existence statement.

The mechanism is a comparison of two convex scales.  `(SG)` bounds the maximum term by
`log μ(r) ≤ log C_A + (log r)²/(4A)`, and the lower growth law
`ν(r)·log(s/r) ≤ log μ(s) − log μ(r)` (already owned by `MaximumTermCentralIndex`) turns that into
`ν(e^T) ≤ D/T + T/A`: the central index grows more slowly than *every* fixed linear rate in `log r`.
A monotone integer function that grows more slowly than `T/A` must be constant on some interval of
length `≍ A`, and a constancy interval of the central index is exactly a plateau.

* `SuperGaussianCoeffs` — the hypothesis `(SG)`.
* `entireCoeffs_of_superGaussian` — `(SG)` already forces entireness.
* `log_maxTerm_le_of_superGaussian` — the quadratic maximum-term bound.
* `centralIndex_le_of_superGaussian` — `ν(e^T) ≤ D/T + T/A` for every `A`.
* `exists_wide_plateau` — **Theorem 1 (1)**: plateaux of arbitrary width at arbitrarily high index.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **Super-Gaussian Taylor decay** `(SG)`: the coefficients decay faster than every Gaussian. -/
def SuperGaussianCoeffs (a : ℕ → ℂ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a n‖ ≤ C * Real.exp (-(A * (n : ℝ) ^ 2))

variable {a : ℕ → ℂ}

/-- A positive radius turns a power into an exponential. -/
theorem pow_eq_exp_mul_log {r : ℝ} (hr : 0 < r) (n : ℕ) :
    r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
  rw [Real.exp_nat_mul, Real.exp_log hr]

/-- `(SG)` already implies the decay hypothesis defining entire Taylor coefficients. -/
theorem entireCoeffs_of_superGaussian (hSG : SuperGaussianCoeffs a) : EntireCoeffs a := by
  intro r hr
  obtain ⟨C, hC, hbound⟩ := hSG 1 one_pos
  have hg : Tendsto (fun n : ℕ => C * Real.exp (-(n : ℝ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := by
      exact Filter.tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun n => term_nonneg a hr n) ?_ hg
  filter_upwards [eventually_ge_atTop (Nat.ceil (Real.log r) + 1)] with n hn
  have hlogle : Real.log r ≤ (n : ℝ) - 1 := by
    have h1 : Real.log r ≤ (Nat.ceil (Real.log r) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.log r) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := le_trans (Nat.le_add_left 1 _) hn
    exact_mod_cast this
  calc ‖a n‖ * r ^ n
      ≤ (C * Real.exp (-(1 * (n : ℝ) ^ 2))) * Real.exp ((n : ℝ) * Real.log r) := by
        rw [pow_eq_exp_mul_log hr n]
        exact mul_le_mul_of_nonneg_right (hbound n) (Real.exp_pos _).le
    _ = C * Real.exp (-((n : ℝ) ^ 2) + (n : ℝ) * Real.log r) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ C * Real.exp (-(n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
        nlinarith [hn1, hlogle]

/-- **The quadratic maximum-term bound.**  Gaussian decay at rate `A` caps the maximum term by
`C·exp((log r)²/(4A))`: completing the square in `n·log r − A n²`. -/
theorem maxTerm_le_of_superGaussian {A : ℝ} (hA : 0 < A)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ n : ℕ, ‖a n‖ ≤ C * Real.exp (-(A * (n : ℝ) ^ 2)))
    {r : ℝ} (hr : 0 < r) :
    maxTerm a r ≤ C * Real.exp (Real.log r ^ 2 / (4 * A)) := by
  refine ciSup_le fun n => ?_
  have hsq : -(A * (n : ℝ) ^ 2) + (n : ℝ) * Real.log r ≤ Real.log r ^ 2 / (4 * A) := by
    have hkey : (0 : ℝ) ≤ (2 * A * (n : ℝ) - Real.log r) ^ 2 := sq_nonneg _
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hkey]
  calc ‖a n‖ * r ^ n
      ≤ (C * Real.exp (-(A * (n : ℝ) ^ 2))) * Real.exp ((n : ℝ) * Real.log r) := by
        rw [pow_eq_exp_mul_log hr n]
        exact mul_le_mul_of_nonneg_right (hbound n) (Real.exp_pos _).le
    _ = C * Real.exp (-(A * (n : ℝ) ^ 2) + (n : ℝ) * Real.log r) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (Real.log r ^ 2 / (4 * A)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq) hC.le

/-- The maximum term dominates every single term, in logarithmic form. -/
theorem log_maxTerm_ge (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Real.log ‖a n₀‖ + (n₀ : ℝ) * Real.log r ≤ Real.log (maxTerm a r) := by
  have hterm : (0 : ℝ) < ‖a n₀‖ * r ^ n₀ := mul_pos (norm_pos_iff.mpr hn₀) (pow_pos hr _)
  have hle := term_le_maxTerm ha hr n₀
  have hlog := Real.log_le_log hterm hle
  rwa [Real.log_mul (norm_ne_zero_iff.mpr hn₀) (by positivity), Real.log_pow] at hlog

/-- **Sublinear central index.**  Under `(SG)` the central index at radius `e^T` is bounded by
`D/T + T/A` for every `A > 0`: it grows more slowly than every fixed linear rate in `log r`. -/
theorem centralIndex_le_of_superGaussian (hSG : SuperGaussianCoeffs a)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {A : ℝ} (hA : 0 < A) :
    ∃ D : ℝ, ∀ T : ℝ, 0 < T →
      (centralIndex a (Real.exp T) : ℝ) ≤ D / T + T / A := by
  classical
  obtain ⟨C, hC, hbound⟩ := hSG A hA
  have ha : EntireCoeffs a := entireCoeffs_of_superGaussian hSG
  refine ⟨Real.log C - Real.log ‖a n₀‖, fun T hT => ?_⟩
  set r : ℝ := Real.exp T with hrdef
  have hr : 0 < r := Real.exp_pos T
  have hr2 : 0 < r ^ 2 := by positivity
  have hrle : r ≤ r ^ 2 := by
    have h1 : (1 : ℝ) ≤ r := Real.one_le_exp hT.le
    nlinarith
  have hlogr : Real.log r = T := Real.log_exp T
  have hlogr2 : Real.log (r ^ 2) = 2 * T := by
    rw [Real.log_pow, hlogr]; push_cast; ring
  -- lower growth law with `s = r²`
  have hgrow := centralIndex_mul_log_le_log_maxTerm_sub ha hr hrle hn₀
  have hdiv : Real.log (r ^ 2 / r) = T := by
    rw [show r ^ 2 / r = r by field_simp, hlogr]
  rw [hdiv] at hgrow
  -- upper bound for `log μ(r²)`
  have hup : Real.log (maxTerm a (r ^ 2)) ≤ Real.log C + (2 * T) ^ 2 / (4 * A) := by
    obtain ⟨_, _, hpos⟩ := exists_maxTerm_eq ha hr2 hn₀
    have h := maxTerm_le_of_superGaussian hA hC hbound hr2
    have := Real.log_le_log hpos h
    rwa [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp, hlogr2] at this
  -- lower bound for `log μ(r)`
  have hlow : Real.log ‖a n₀‖ + (n₀ : ℝ) * T ≤ Real.log (maxTerm a r) := by
    have := log_maxTerm_ge ha hr hn₀
    rwa [hlogr] at this
  have hn₀nonneg : (0 : ℝ) ≤ (n₀ : ℝ) * T := by positivity
  have hstep : (centralIndex a r : ℝ) * T
      ≤ (Real.log C - Real.log ‖a n₀‖) + (2 * T) ^ 2 / (4 * A) := by
    linarith
  have hTne : T ≠ 0 := ne_of_gt hT
  have hAne : A ≠ 0 := ne_of_gt hA
  have h4 : (2 * T) ^ 2 / (4 * A) = T ^ 2 / A := by
    have h : (2 * T) ^ 2 = 4 * T ^ 2 := by ring
    rw [h, mul_div_mul_left _ _ (by norm_num : (4:ℝ) ≠ 0)]
  rw [h4] at hstep
  have hexp : (Real.log C - Real.log ‖a n₀‖ + T ^ 2 / A) / T
      = (Real.log C - Real.log ‖a n₀‖) / T + T / A := by
    rw [add_div]; congr 1; field_simp
  rw [← hexp, le_div_iff₀ hT]
  linarith


/-! ## The central index escapes to infinity -/

/-- Beyond an explicit radius the central index passes every index carrying a nonzero
coefficient: otherwise the `n₁`-th term would stay below a fixed finite sum of lower terms. -/
theorem exists_radius_le_centralIndex (ha : EntireCoeffs a) {n₁ : ℕ} (hn₁ : a n₁ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → n₁ ≤ centralIndex a r := by
  classical
  set M : ℝ := ∑ m ∈ Finset.range n₁, ‖a m‖ with hM
  have hMnonneg : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn₁pos : 0 < ‖a n₁‖ := norm_pos_iff.mpr hn₁
  refine ⟨max 1 (M / ‖a n₁‖ + 1), by positivity, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hrM : M / ‖a n₁‖ + 1 ≤ r := le_trans (le_max_right _ _) hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  by_contra hcon
  push_neg at hcon
  set ν := centralIndex a r with hν
  have hpos1 : 1 ≤ n₁ := by omega
  have h1 : ‖a n₁‖ * r ^ n₁ ≤ ‖a ν‖ * r ^ ν := by
    rw [hν, term_centralIndex_eq ha hrpos hn₁]
    exact term_le_maxTerm ha hrpos n₁
  have h2 : ‖a ν‖ ≤ M := by
    rw [hM]
    exact Finset.single_le_sum (f := fun m => ‖a m‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.mpr hcon)
  have h3 : r ^ ν ≤ r ^ (n₁ - 1) := pow_le_pow_right₀ hr1 (by omega)
  have hsplit : r ^ n₁ = r ^ (n₁ - 1) * r := by
    conv_lhs => rw [show n₁ = (n₁ - 1) + 1 by omega]
    rw [pow_succ]
  have hpowpos : (0 : ℝ) < r ^ (n₁ - 1) := pow_pos hrpos _
  have hchain : ‖a n₁‖ * (r ^ (n₁ - 1) * r) ≤ M * r ^ (n₁ - 1) := by
    calc ‖a n₁‖ * (r ^ (n₁ - 1) * r) = ‖a n₁‖ * r ^ n₁ := by rw [hsplit]
      _ ≤ ‖a ν‖ * r ^ ν := h1
      _ ≤ M * r ^ (n₁ - 1) := by
          exact mul_le_mul h2 h3 (pow_nonneg hrpos.le _) hMnonneg
  have hfinal : ‖a n₁‖ * r ≤ M :=
    le_of_mul_le_mul_right
      (by nlinarith [hchain] : (‖a n₁‖ * r) * r ^ (n₁ - 1) ≤ M * r ^ (n₁ - 1)) hpowpos
  have : M / ‖a n₁‖ + 1 ≤ M / ‖a n₁‖ := by
    calc M / ‖a n₁‖ + 1 ≤ r := hrM
      _ ≤ M / ‖a n₁‖ := by rw [le_div_iff₀ hn₁pos]; linarith [hfinal]
  linarith

/-! ## Pigeonhole: a monotone sublinear central index has a wide constancy interval -/

/-- If the central index strictly increases across every one of `K` consecutive steps of width
`B`, it has gained at least `K`. -/
theorem add_le_centralIndex_of_strict (T B : ℝ) :
    ∀ K : ℕ,
      (∀ k : ℕ, k < K → centralIndex a (Real.exp (T + (k : ℝ) * B))
        < centralIndex a (Real.exp (T + ((k : ℝ) + 1) * B))) →
      centralIndex a (Real.exp T) + K ≤ centralIndex a (Real.exp (T + (K : ℝ) * B)) := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
      intro hstrict
      have hprev : centralIndex a (Real.exp T) + K
          ≤ centralIndex a (Real.exp (T + (K : ℝ) * B)) :=
        ih fun k hk => hstrict k (by omega)
      have hlast := hstrict K (by omega)
      have hcast : ((K : ℝ) + 1) * B = ((K + 1 : ℕ) : ℝ) * B := by push_cast; ring
      rw [hcast] at hlast
      omega

/-- **Theorem 1 (1): arbitrarily wide Newton plateaux.**  A super-Gaussian coefficient sequence with
infinitely many nonzero entries has, for every prescribed width `B` and every prescribed index
bound `N`, a plateau of width `B` carried by an index at least `N`: the central index is constant
on `[e^T, e^{T+B}]` and is at least `N` there. -/
theorem exists_wide_plateau (hSG : SuperGaussianCoeffs a)
    (htrans : ∀ N : ℕ, ∃ n, N ≤ n ∧ a n ≠ 0) {B : ℝ} (hB : 0 < B) (N : ℕ) (T₀ : ℝ) :
    ∃ (n : ℕ) (T : ℝ), N ≤ n ∧ T₀ ≤ T ∧ 0 < T ∧
      centralIndex a (Real.exp T) = n ∧ centralIndex a (Real.exp (T + B)) = n := by
  classical
  have ha : EntireCoeffs a := entireCoeffs_of_superGaussian hSG
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  obtain ⟨n₁, hn₁N, hn₁⟩ := htrans N
  obtain ⟨R, hRpos, hR⟩ := exists_radius_le_centralIndex ha hn₁
  obtain ⟨D, hD⟩ := centralIndex_le_of_superGaussian hSG hn₀ (by linarith : (0:ℝ) < 4 * B)
  -- choose the base height
  set T : ℝ := max (max (max 1 (Real.log R + 1)) (2 * B * |D| + B / 2 + 1)) T₀ with hTdef
  have hT1 : (1 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hTR : Real.log R + 1 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hTbig : 2 * B * |D| + B / 2 + 1 ≤ T :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hT₀ : T₀ ≤ T := le_max_right _ _
  have hRle : R ≤ Real.exp T := by
    have : Real.log R < T := by linarith
    calc R = Real.exp (Real.log R) := (Real.exp_log hRpos).symm
      _ ≤ Real.exp T := Real.exp_le_exp.mpr this.le
  set K : ℕ := Nat.ceil (T / B) with hKdef
  have hKge : T / B ≤ (K : ℝ) := Nat.le_ceil _
  have hKlt : (K : ℝ) < T / B + 1 := Nat.ceil_lt_add_one (by positivity)
  -- either some step is flat, or the central index gains `K`
  by_cases hflat : ∃ k : ℕ, k < K ∧ centralIndex a (Real.exp (T + (k : ℝ) * B))
      = centralIndex a (Real.exp (T + ((k : ℝ) + 1) * B))
  · obtain ⟨k, hkK, hk⟩ := hflat
    have hkB : (0 : ℝ) ≤ (k : ℝ) * B := by positivity
    refine ⟨centralIndex a (Real.exp (T + (k : ℝ) * B)), T + (k : ℝ) * B, ?_,
      by linarith, by linarith, rfl, ?_⟩
    · have hmono : centralIndex a (Real.exp T) ≤ centralIndex a (Real.exp (T + (k : ℝ) * B)) :=
        centralIndex_mono ha (Real.exp_pos T)
          (Real.exp_le_exp.mpr (by linarith : T ≤ T + (k : ℝ) * B)) hn₀
      exact le_trans hn₁N (le_trans (hR _ hRle) hmono)
    · rw [show T + (k : ℝ) * B + B = T + ((k : ℝ) + 1) * B by ring]
      exact hk.symm
  · push_neg at hflat
    exfalso
    have hstrict : ∀ k : ℕ, k < K → centralIndex a (Real.exp (T + (k : ℝ) * B))
        < centralIndex a (Real.exp (T + ((k : ℝ) + 1) * B)) := by
      intro k hk
      refine lt_of_le_of_ne ?_ (hflat k hk)
      exact centralIndex_mono ha (Real.exp_pos _)
        (Real.exp_le_exp.mpr (by nlinarith : T + (k : ℝ) * B ≤ T + ((k : ℝ) + 1) * B)) hn₀
    have hgain := add_le_centralIndex_of_strict (a := a) T B K hstrict
    have hKle : (K : ℝ) ≤ (centralIndex a (Real.exp (T + (K : ℝ) * B)) : ℝ) := by
      have : (K : ℕ) ≤ centralIndex a (Real.exp (T + (K : ℝ) * B)) := by omega
      exact_mod_cast this
    -- the sublinear bound at height `T + K B`
    have hKBnonneg : (0 : ℝ) ≤ (K : ℝ) * B := by positivity
    have hSpos : 0 < T + (K : ℝ) * B := by linarith
    have hbound := hD (T + (K : ℝ) * B) hSpos
    have hKB : (K : ℝ) * B ≤ T + B := by
      have hTBc : T / B * B = T := by field_simp
      nlinarith [hKlt, hB, hTBc]
    have hDdiv : D / (T + (K : ℝ) * B) ≤ |D| := by
      rcases le_total D 0 with hDneg | hDpos
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg hDneg hSpos.le) (abs_nonneg D)
      · rw [div_le_iff₀ hSpos]
        calc D = D * 1 := (mul_one D).symm
          _ ≤ |D| * (T + (K : ℝ) * B) := by
              refine mul_le_mul (le_abs_self D) (by linarith) zero_le_one (abs_nonneg D)
    have hsecond : (T + (K : ℝ) * B) / (4 * B) ≤ T / (2 * B) + 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : T / (2 * B) * (4 * B) = 2 * T := by field_simp; ring
      nlinarith [hKB, hB, h1]
    have hTB : T / B ≤ |D| + T / (2 * B) + 1 / 4 := by
      calc T / B ≤ (K : ℝ) := hKge
        _ ≤ (centralIndex a (Real.exp (T + (K : ℝ) * B)) : ℝ) := hKle
        _ ≤ D / (T + (K : ℝ) * B) + (T + (K : ℝ) * B) / (4 * B) := hbound
        _ ≤ |D| + (T / (2 * B) + 1 / 4) := by linarith
        _ = |D| + T / (2 * B) + 1 / 4 := by ring
    have hhalf : T / (2 * B) ≤ |D| + 1 / 4 := by
      have hTBval : T / B = 2 * (T / (2 * B)) := by field_simp
      rw [hTBval] at hTB
      linarith
    have : T ≤ 2 * B * |D| + B / 2 := by
      rw [div_le_iff₀ (by positivity)] at hhalf
      nlinarith [hhalf, hB]
    linarith

end GaloisForLFunctions.HTGeometry
