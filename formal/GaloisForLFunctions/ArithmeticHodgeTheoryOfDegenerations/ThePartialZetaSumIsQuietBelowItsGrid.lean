import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkIsBlindToTheLowZeros
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockIsQuietBelowTheGrid
import GaloisForLFunctions.RHTower.TruncatedPoissonSummation

/-!
# The partial zeta sum is quiet below its grid

The partial sum `Σ_{k≤M} k^{−w}` approximates `ζ(w) + M^{1−w}/(1−w)` with error `O(M^{−Re w})`
uniformly up to the height `|Im w| ≤ πM`, the grid of the sum: there the phase `(Im w/2π) log k`
of the tail moves by at most `½` per step, so the tail beyond `M` has no stationary point.

* **Truncated Poisson below the grid** (`norm_sum_Ioc_cexp_sub_integral_le`): for `|τ| ≤ πM`,
  `|Σ_{M<k≤B} k^{−iτ} − ∫_M^B u^{−iτ} du| ≤ 7` for every `B ≥ M`; the two dual integrals of the
  truncated Poisson formula have phase derivative `≥ π` (first-derivative test).
* **With the amplitude** (`norm_sum_Ioc_cpow_sub_integral_le`): for `Re w ≥ 0`, `|Im w| ≤ πM`,
  `|Σ_{M<k≤B} k^{−w} − ∫_M^B u^{−w} du| ≤ 8 M^{−Re w}` (summation by parts on unit intervals).
* **The strip error** (`norm_zetaStripError_le_grid`): `|E(w, M)| ≤ 9 M^{−Re w}` for
  `0 < Re w`, `w ≠ 1`, `|Im w| ≤ πM`, uniformly in the height (Titchmarsh's Theorem 4.11).
* **The conductor polynomial at a zero below its grid**
  (`norm_conductorDirichlet_sub_horizonTerm_le_grid`): if `ζ(1 − s) = 0`, `0 < Re s < 1`,
  `N ≥ 2e` and `|Im s| ≤ π⌊N/e⌋`, then `|D_e(s;N) − [e = 1]N^s/s| ≤ 24 e³ N^{Re s − 1}`.

Euler–Maclaurin gives the same bound only up to the height `N^{1−ε}`
(`TheBulkIsBlindBelowTheResolutionHeight`); the grid `π⌊N/e⌋` is linear in `N`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Complex intervalIntegral
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence

/-! ### Truncated Poisson below the grid -/

/-- The unit exponential `u^{−iτ} = e^{−iτ log u}`. -/
def unitPhase (τ u : ℝ) : ℂ := Complex.exp (((-(τ * Real.log u) : ℝ) : ℂ) * I)

theorem norm_unitPhase (τ u : ℝ) : ‖unitPhase τ u‖ = 1 := by
  unfold unitPhase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem conj_unitPhase (τ u : ℝ) : conj (unitPhase τ u) = unitPhase (-τ) u := by
  unfold unitPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem continuousOn_unitPhase (τ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (unitPhase τ) (Set.uIcc a b) := by
  have hne : ∀ u ∈ Set.uIcc a b, u ≠ 0 := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu
    have : 0 < u := by linarith [hu.1]
    exact this.ne'
  unfold unitPhase
  refine ContinuousOn.cexp (ContinuousOn.mul ?_ continuousOn_const)
  exact Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_const.mul (Real.continuousOn_log.mono fun u hu => hne u hu)).neg)

/-- The two dual integrals of the truncated Poisson formula: phase derivative `≥ π`. -/
theorem norm_integral_dual_le {f f' f'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Set.Icc a b)) (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f'' x)
    (hK : ∀ x ∈ Set.Icc a b, |f' x| ≤ 1 / 2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖∫ t in a..b, Complex.exp (((2 * Real.pi * (f t + σ * t) : ℝ) : ℂ) * I)‖ ≤ 3 / Real.pi := by
  have h := HTGeometry.norm_integral_mul_exp_le_of_monotone_phase (g := fun _ => (1 : ℂ))
    (g' := fun _ => 0) (Θ := fun t => 2 * Real.pi * (f t + σ * t))
    (Θ' := fun t => 2 * Real.pi * (f' t + σ)) (Θ'' := fun t => 2 * Real.pi * f'' t)
    (lam := Real.pi) (G := 1) (V := 0) hab Real.pi_pos
    (fun x _ => hasDerivAt_const x 1) continuousOn_const
    (fun x hx => (((hf x hx).add ((hasDerivAt_id' x).const_mul σ)).const_mul
      (2 * Real.pi)).congr_deriv (by ring))
    (fun x hx => ((hf' x hx).add_const σ).const_mul (2 * Real.pi))
    (continuousOn_const.mul hf''c)
    (fun x hx => mul_nonneg (by positivity) (hpos x hx))
    (fun x hx => by
      have hk := abs_le.mp (hK x hx)
      have hp := Real.pi_pos
      rcases hσ with rfl | rfl
      · rw [abs_of_pos (by nlinarith)]; nlinarith
      · rw [abs_of_neg (by nlinarith)]; nlinarith)
    (fun x _ => by simp) (by simp)
  simp only [one_mul, norm_one] at h
  linarith

/-- The integer interval `(M, B]` is the image of the natural one. -/
theorem Ioc_int_eq_map (M B : ℕ) :
    Finset.Ioc (M : ℤ) (B : ℤ) = (Finset.Ioc M B).map Nat.castEmbedding := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_map, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨m.toNat, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    exact ⟨by omega, by omega⟩

/-- **Truncated Poisson below the grid, positive frequency**: for `0 < τ ≤ πM`,
`|Σ_{M<k≤B} k^{−iτ} − ∫_M^B u^{−iτ}| ≤ 5 + 6/π`. -/
theorem norm_sum_Ioc_unitPhase_sub_integral_le_of_pos {M B : ℕ} (hM : 1 ≤ M) (hMB : M ≤ B)
    {τ : ℝ} (hτ0 : 0 < τ) (hτM : τ ≤ Real.pi * M) :
    ‖∑ k ∈ Finset.Ioc M B, unitPhase τ k - ∫ u in (M : ℝ)..B, unitPhase τ u‖ ≤
      5 + 6 / Real.pi := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hp := Real.pi_pos
  set f : ℝ → ℝ := fun t => -(τ / (2 * Real.pi)) * Real.log t with hfdef
  set f' : ℝ → ℝ := fun t => -(τ / (2 * Real.pi)) * t⁻¹ with hf'def
  set f'' : ℝ → ℝ := fun t => τ / (2 * Real.pi) * (t ^ 2)⁻¹ with hf''def
  have hpos_of : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((B : ℤ) : ℝ), 0 < x := fun x hx => by
    push_cast at hx; linarith [hx.1]
  have hf : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((B : ℤ) : ℝ), HasDerivAt f (f' x) x := fun x hx =>
    (Real.hasDerivAt_log (hpos_of x hx).ne').const_mul _
  have hf' : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((B : ℤ) : ℝ), HasDerivAt f' (f'' x) x := fun x hx =>
    ((hasDerivAt_inv (hpos_of x hx).ne').const_mul _).congr_deriv (by simp only [hf''def]; ring)
  have hf''c : ContinuousOn f'' (Set.Icc ((M : ℤ) : ℝ) ((B : ℤ) : ℝ)) :=
    continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_of x hx).ne')
  have hpos : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((B : ℤ) : ℝ), 0 ≤ f'' x := fun x hx => by
    simp only [hf''def]; positivity
  have hK' : ∀ x ∈ Set.Icc ((M : ℤ) : ℝ) ((B : ℤ) : ℝ), |f' x| ≤ 1 / 2 := fun x hx => by
    have hx0 := hpos_of x hx
    have hxM : (M : ℝ) ≤ x := by push_cast at hx; exact hx.1
    simp only [hf'def]
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < τ / (2 * Real.pi)),
      abs_of_pos (inv_pos.mpr hx0)]
    have e : τ / (2 * Real.pi) * x⁻¹ = τ / (2 * Real.pi * x) := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hP := RHTower.norm_sum_sub_truncatedPoisson_le (A := (M : ℤ)) (B := (B : ℤ))
    (by exact_mod_cast hMB) hf hf' hf''c hpos hK' (K := 1) (by norm_num) le_rfl
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_mul, Int.cast_natCast] at hP
  have hexp : ∀ t : ℝ, Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I) = unitPhase τ t := by
    intro t
    unfold unitPhase
    congr 3
    simp only [hfdef]
    field_simp
  simp only [hexp] at hP
  rw [Ioc_int_eq_map, Finset.sum_map] at hP
  simp only [Nat.castEmbedding_apply, Int.cast_natCast] at hP
  have hMBR : (M : ℝ) ≤ B := by exact_mod_cast hMB
  have hpos' : ∀ x ∈ Set.Icc (M : ℝ) B, 0 < x := fun x hx => by linarith [hx.1]
  have hplus := norm_integral_dual_le (f := f) (f' := f') (f'' := f'') hMBR
    (fun x hx => hf x (by push_cast; exact hx)) (fun x hx => hf' x (by push_cast; exact hx))
    (by simpa using hf''c) (fun x hx => hpos x (by push_cast; exact hx))
    (fun x hx => hK' x (by push_cast; exact hx)) (σ := 1) (Or.inl rfl)
  have hminus := norm_integral_dual_le (f := f) (f' := f') (f'' := f'') hMBR
    (fun x hx => hf x (by push_cast; exact hx)) (fun x hx => hf' x (by push_cast; exact hx))
    (by simpa using hf''c) (fun x hx => hpos x (by push_cast; exact hx))
    (fun x hx => hK' x (by push_cast; exact hx)) (σ := -1) (Or.inr rfl)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hplus hminus
  set S := ∑ k ∈ Finset.Ioc M B, unitPhase τ k
  set I₀ := ∫ u in (M : ℝ)..B, unitPhase τ u
  set Iplus := ∫ t in (M : ℝ)..B, Complex.exp (((2 * Real.pi * (f t + t) : ℝ) : ℂ) * I)
  set Iminus := ∫ t in (M : ℝ)..B, Complex.exp (((2 * Real.pi * (f t - t) : ℝ) : ℂ) * I)
  have : S - I₀ = (S - (I₀ + (Iplus + Iminus))) + Iplus + Iminus := by ring
  rw [this]
  calc ‖(S - (I₀ + (Iplus + Iminus))) + Iplus + Iminus‖ ≤ ‖S - (I₀ + (Iplus + Iminus))‖ + ‖Iplus‖ + ‖Iminus‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 5 + 3 / Real.pi + 3 / Real.pi := by gcongr
    _ = 5 + 6 / Real.pi := by ring

/-- **Truncated Poisson below the grid**: for `|τ| ≤ πM` and `B ≥ M`,
`|Σ_{M<k≤B} k^{−iτ} − ∫_M^B u^{−iτ} du| ≤ 7`. -/
theorem norm_sum_Ioc_unitPhase_sub_integral_le {M B : ℕ} (hM : 1 ≤ M) (hMB : M ≤ B) {τ : ℝ}
    (hτ : |τ| ≤ Real.pi * M) :
    ‖∑ k ∈ Finset.Ioc M B, unitPhase τ k - ∫ u in (M : ℝ)..B, unitPhase τ u‖ ≤ 7 := by
  have h6 : 6 / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · have h := norm_sum_Ioc_unitPhase_sub_integral_le_of_pos hM hMB (τ := -τ) (by linarith)
      (by rw [abs_of_neg hneg] at hτ; linarith)
    have e : ∑ k ∈ Finset.Ioc M B, unitPhase τ k - ∫ u in (M : ℝ)..B, unitPhase τ u =
        conj (∑ k ∈ Finset.Ioc M B, unitPhase (-τ) k - ∫ u in (M : ℝ)..B, unitPhase (-τ) u) := by
      rw [map_sub, map_sum, ← intervalIntegral.intervalIntegral_conj]
      simp only [conj_unitPhase, neg_neg]
    rw [e, RCLike.norm_conj]
    linarith
  · have h1 : ∀ u : ℝ, unitPhase 0 u = 1 := fun u => by simp [unitPhase]
    simp only [h1, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
      intervalIntegral.integral_const]
    rw [Nat.cast_sub hMB]
    simp
  · have h := norm_sum_Ioc_unitPhase_sub_integral_le_of_pos hM hMB hpos
      (by rw [abs_of_pos hpos] at hτ; exact hτ)
    linarith

/-! ### With the amplitude -/

/-- `u^{−w} = u^{−Re w} e^{−i Im w log u}` for `u > 0`. -/
theorem ofReal_cpow_neg_eq {u : ℝ} (hu : 0 < u) (w : ℂ) :
    ((u : ℝ) : ℂ) ^ (-w) = ((u ^ (-w.re) : ℝ) : ℂ) * unitPhase w.im u := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hu.ne'), ← Complex.ofReal_log hu.le,
    Real.rpow_def_of_pos hu, Complex.ofReal_exp, unitPhase, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- `Σ_{M<k≤M+K} f(k) = Σ_{j<K} f(M + j + 1)`. -/
theorem sum_Ioc_add_eq_sum_range (f : ℕ → ℂ) (M K : ℕ) :
    ∑ k ∈ Finset.Ioc M (M + K), f k = ∑ j ∈ range K, f (M + j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show M + (K + 1) = M + K + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_range_succ]

/-- **The tail with its amplitude below the grid**: for `Re w ≥ 0`, `|Im w| ≤ πM`, `B ≥ M`,
`|Σ_{M<k≤B} k^{−w} − ∫_M^B u^{−w} du| ≤ 8 M^{−Re w}`. -/
theorem norm_sum_Ioc_cpow_sub_integral_le {M B : ℕ} (hM : 1 ≤ M) (hMB : M ≤ B) {w : ℂ}
    (hσ : 0 ≤ w.re) (hτ : |w.im| ≤ Real.pi * M) :
    ‖∑ k ∈ Finset.Ioc M B, ((k : ℝ) : ℂ) ^ (-w) - ∫ u in (M : ℝ)..B, ((u : ℝ) : ℂ) ^ (-w)‖ ≤
      8 * (M : ℝ) ^ (-w.re) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hpt : ∀ j : ℕ, (0 : ℝ) < ((M + j : ℕ) : ℝ) := fun j => by
    have : 1 ≤ M + j := by omega
    exact_mod_cast this
  have hstep : ∀ j : ℕ, ((M + j : ℕ) : ℝ) ≤ ((M + (j + 1) : ℕ) : ℝ) := fun j => by
    push_cast; linarith
  set a : ℕ → ℝ := fun j => ((M + j : ℕ) : ℝ) ^ (-w.re) with ha
  have ha_anti : ∀ j, a (j + 1) ≤ a j := fun j => by
    simp only [ha]
    exact Real.rpow_le_rpow_of_nonpos (hpt j) (hstep j) (by linarith)
  have ha0 : ∀ j, 0 ≤ a j := fun j => by
    simp only [ha]; exact (Real.rpow_pos_of_pos (hpt j) _).le
  set F : ℝ → ℂ := fun u => ((u : ℝ) : ℂ) ^ (-w) with hF
  set z : ℝ → ℂ := unitPhase w.im with hz
  have hFz : ∀ u : ℝ, 0 < u → F u = ((u ^ (-w.re) : ℝ) : ℂ) * z u := fun u hu =>
    ofReal_cpow_neg_eq hu w
  have hFint : ∀ j : ℕ, IntervalIntegrable F volume ((M + j : ℕ) : ℝ) ((M + (j + 1) : ℕ) : ℝ) := by
    intro j
    refine ContinuousOn.intervalIntegrable fun u hu => ?_
    rw [Set.uIcc_of_le (hstep j)] at hu
    have hu0 : 0 < u := lt_of_lt_of_le (hpt j) hu.1
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hu0.ne')).continuousWithinAt
  have hzint : ∀ j : ℕ, IntervalIntegrable z volume ((M + j : ℕ) : ℝ) ((M + (j + 1) : ℕ) : ℝ) :=
    fun j => (continuousOn_unitPhase _ (hpt j) (hstep j)).intervalIntegrable
  -- the integral over adjacent unit intervals
  have hadj : ∀ G : ℝ → ℂ,
      (∀ j : ℕ, IntervalIntegrable G volume ((M + j : ℕ) : ℝ) ((M + (j + 1) : ℕ) : ℝ)) →
      ∀ K : ℕ, ∫ u in (M : ℝ)..((M + K : ℕ) : ℝ), G u =
        ∑ j ∈ range K, ∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), G u := by
    intro G hG K
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j : ℕ => ((M + j : ℕ) : ℝ)) (f := G) (μ := volume) (n := K) (fun j _ => hG j)
    simp only [add_zero] at h
    exact h.symm
  -- one unit interval: the amplitude frozen at the right end, plus a monotone error
  have hpiece : ∀ j : ℕ, ‖(∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), F u) -
      ((a (j + 1) : ℝ) : ℂ) * ∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), z u‖ ≤
      a j - a (j + 1) := by
    intro j
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hFint j) ((hzint j).const_mul _)]
    have hle : ∀ u ∈ Set.uIoc ((M + j : ℕ) : ℝ) ((M + (j + 1) : ℕ) : ℝ),
        ‖F u - ((a (j + 1) : ℝ) : ℂ) * z u‖ ≤ a j - a (j + 1) := by
      intro u hu
      rw [Set.uIoc_of_le (hstep j)] at hu
      have hu0 : 0 < u := lt_trans (hpt j) hu.1
      rw [hFz u hu0, ← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, hz, norm_unitPhase, mul_one]
      have h1 : u ^ (-w.re) ≤ a j := by
        simp only [ha]
        exact Real.rpow_le_rpow_of_nonpos (hpt j) hu.1.le (by linarith)
      have h2 : a (j + 1) ≤ u ^ (-w.re) := by
        simp only [ha]
        exact Real.rpow_le_rpow_of_nonpos hu0 hu.2 (by linarith)
      rw [abs_of_nonneg (by linarith)]
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hle
    have hlen : ((M + (j + 1) : ℕ) : ℝ) - ((M + j : ℕ) : ℝ) = 1 := by push_cast; ring
    rw [hlen, abs_one, mul_one] at this
    exact this
  -- partial sums of the unit increments are bounded by the truncated Poisson formula
  set e : ℕ → ℂ := fun j => z ((M + (j + 1) : ℕ) : ℝ) -
    ∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), z u with he
  have hpart : ∀ k : ℕ, ‖∑ j ∈ range (k + 1), e j‖ ≤ 7 := by
    intro k
    have hsumz : ∑ j ∈ range (k + 1), z ((M + (j + 1) : ℕ) : ℝ) =
        ∑ i ∈ Finset.Ioc M (M + (k + 1)), z i := by
      rw [sum_Ioc_add_eq_sum_range (fun i => z i)]
      rfl
    rw [he, Finset.sum_sub_distrib, hsumz, ← hadj z hzint (k + 1)]
    exact norm_sum_Ioc_unitPhase_sub_integral_le hM (by omega) hτ
  obtain ⟨J, rfl⟩ : ∃ J, B = M + J := ⟨B - M, by omega⟩
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp only [add_zero, Finset.Ioc_self, Finset.sum_empty, intervalIntegral.integral_same,
      sub_zero, norm_zero]
    positivity
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  have hsumF : ∑ k ∈ Finset.Ioc M (M + (J' + 1)), ((k : ℝ) : ℂ) ^ (-w) =
      ∑ j ∈ range (J' + 1), ((a (j + 1) : ℝ) : ℂ) * z ((M + (j + 1) : ℕ) : ℝ) := by
    rw [sum_Ioc_add_eq_sum_range (fun k => F k)]
    refine sum_congr rfl fun j _ => ?_
    show F ((M + (j + 1) : ℕ) : ℝ) = _
    rw [hFz _ (hpt (j + 1))]
  rw [show (∫ u in (M : ℝ)..((M + (J' + 1) : ℕ) : ℝ), ((u : ℝ) : ℂ) ^ (-w)) =
    ∫ u in (M : ℝ)..((M + (J' + 1) : ℕ) : ℝ), F u from rfl, hadj F hFint, hsumF]
  have hsplit : ∑ j ∈ range (J' + 1), ((a (j + 1) : ℝ) : ℂ) * z ((M + (j + 1) : ℕ) : ℝ) -
      ∑ j ∈ range (J' + 1), ∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), F u =
      ∑ j ∈ range (J' + 1), ((a (j + 1) : ℝ) : ℂ) * e j -
        ∑ j ∈ range (J' + 1), ((∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), F u) -
          ((a (j + 1) : ℝ) : ℂ) * ∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), z u) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [he]
    ring
  rw [hsplit]
  -- the main part by summation by parts, the rest telescopes
  have hmain := norm_sum_mul_le_of_partial (fun j => a (j + 1)) e J' (fun k _ => hpart k)
  have htel : |a (J' + 1)| + ∑ m ∈ range J', |a (m + 1 + 1) - a (m + 1)| = a 1 := by
    rw [abs_of_nonneg (ha0 _)]
    have : ∀ m ∈ range J', |a (m + 1 + 1) - a (m + 1)| = a (m + 1) - a (m + 1 + 1) :=
      fun m _ => by rw [abs_of_nonpos (by linarith [ha_anti (m + 1)])]; ring
    rw [sum_congr rfl this, Finset.sum_range_sub' (fun m => a (m + 1))]
    ring
  rw [htel] at hmain
  have hrest : ‖∑ j ∈ range (J' + 1), ((∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), F u) -
      ((a (j + 1) : ℝ) : ℂ) * ∫ u in ((M + j : ℕ) : ℝ)..((M + (j + 1) : ℕ) : ℝ), z u)‖ ≤ a 0 := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun j _ => hpiece j).trans ?_)
    rw [Finset.sum_range_sub' a]
    linarith [ha0 (J' + 1)]
  have ha1 : a 1 ≤ a 0 := ha_anti 0
  have ha0M : a 0 = (M : ℝ) ^ (-w.re) := by simp [ha]
  refine (norm_sub_le _ _).trans ?_
  rw [← ha0M]
  linarith

/-! ### The strip error below the grid -/

/-- **The strip error below the grid** (Titchmarsh 4.11): for `0 < Re w`, `w ≠ 1`, `|Im w| ≤ πM`,
`|Σ_{k≤M} k^{−w} − M^{1−w}/(1−w) − ζ(w)| ≤ 9 M^{−Re w}`, uniformly in the height. -/
theorem norm_zetaStripError_le_grid {w : ℂ} (hw0 : 0 < w.re) (hw1 : w ≠ 1) {M : ℕ} (hM : 1 ≤ M)
    (hτ : |w.im| ≤ Real.pi * M) :
    ‖RHTower.zetaStripError w M‖ ≤ 9 * (M : ℝ) ^ (-w.re) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hX : 0 < (M : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos hM0 _
  -- a far horizon `B` where the Euler–Maclaurin error is below `M^{−Re w}`
  have hlim : Tendsto (fun B : ℕ => (2 + ‖w‖) * (B : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hw0).comp tendsto_natCast_atTop_atTop).const_mul
      (2 + ‖w‖)
  obtain ⟨B, hB⟩ := ((hlim.eventually (gt_mem_nhds hX)).and
    ((eventually_ge_atTop M).and (eventually_ge_atTop ⌈‖w‖⌉₊))).exists
  obtain ⟨hBsmall, hMB, hwB⟩ := hB
  have hB1 : 1 ≤ B := le_trans hM hMB
  have hwB' : ‖w‖ ≤ B := (Nat.le_ceil _).trans (by exact_mod_cast hwB)
  have hEB := norm_zetaStripError_le hw0 hw1 hB1 hwB'
  -- `E(w, B) − E(w, M)` is the tail sum minus the tail integral
  have hdiff : RHTower.zetaStripError w B - RHTower.zetaStripError w M =
      ∑ k ∈ Finset.Ioc M B, ((k : ℝ) : ℂ) ^ (-w) - ∫ u in (M : ℝ)..B, ((u : ℝ) : ℂ) ^ (-w) := by
    have hIcc : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hsplit : ∑ k ∈ Finset.Icc 1 B, ((k : ℝ) : ℂ) ^ (-w) =
        ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) : ℂ) ^ (-w) + ∑ k ∈ Finset.Ioc M B, ((k : ℝ) : ℂ) ^ (-w) := by
      rw [hIcc, hIcc, Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMB]
    have hne : (-w : ℂ) ≠ -1 := fun h => hw1 (by linear_combination -h)
    have h0 : (0 : ℝ) ∉ Set.uIcc (M : ℝ) B := by
      rw [Set.uIcc_of_le (by exact_mod_cast hMB)]
      intro h; linarith [h.1]
    have hint := integral_cpow (a := (M : ℝ)) (b := B) (r := -w) (Or.inr ⟨hne, h0⟩)
    unfold RHTower.zetaStripError
    rw [hsplit, hint, show -w + 1 = 1 - w by ring]
    ring
  have hMB' := norm_sum_Ioc_cpow_sub_integral_le hM hMB hw0.le hτ
  have : RHTower.zetaStripError w M = RHTower.zetaStripError w B -
      (∑ k ∈ Finset.Ioc M B, ((k : ℝ) : ℂ) ^ (-w) - ∫ u in (M : ℝ)..B, ((u : ℝ) : ℂ) ^ (-w)) := by
    rw [← hdiff]; ring
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-! ### The conductor polynomial at a zero below its grid -/

/-- One divisor below the grid: with `M = ⌊N/d⌋ ≥ 1` and `|Im s| ≤ πM`,
`‖ζ(1−s) + (M^s − (N/d)^s)/s + E(1−s, M)‖ ≤ 12 M^{Re s − 1}` at a zero of `ζ(1 − s)`. -/
theorem norm_divisorTerm_le_grid {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {d N : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N)
    (hτ : |s.im| ≤ Real.pi * (N / d : ℕ)) :
    ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d)‖ ≤ 12 * ((N / d : ℕ) : ℝ) ^ (s.re - 1) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0'
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨M, hM⟩ : ∃ M, M = N / d := ⟨_, rfl⟩
  rw [← hM] at hτ ⊢
  have hM1 : 1 ≤ M := by rw [hM]; exact (Nat.one_le_div_iff (by omega)).mpr hdN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hfl : ⌊(N : ℝ) / d⌋₊ = M := by rw [hM]; exact Nat.floor_div_eq_div N d
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hx1 : (1 : ℝ) ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ hd0, one_mul]; exact_mod_cast hdN
  have hxM : (M : ℝ) ≤ (N : ℝ) / d := by rw [← hfl]; exact Nat.floor_le (by linarith)
  have hxlt : (N : ℝ) / d < M + 1 := by rw [← hfl]; exact Nat.lt_floor_add_one _
  have hXM : 0 < (M : ℝ) ^ (s.re - 1) := Real.rpow_pos_of_pos hM0 _
  -- the floor term
  have hfloor : ‖((((M : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s‖ ≤
      3 * (M : ℝ) ^ (s.re - 1) := by
    rw [norm_div]
    rcases le_or_gt ‖s‖ (M : ℝ) with hsM | hsM
    · have h := RHTower.norm_cpow_natFloor_sub_cpow_le (s := s) hx1 (by rw [hfl]; exact hsM)
      rw [hfl] at h
      rw [div_le_iff₀ hsn]
      nlinarith
    · rw [div_le_iff₀ hsn]
      have h1 : ‖(((M : ℕ) : ℝ) : ℂ) ^ s‖ = (M : ℝ) ^ s.re :=
        Complex.norm_cpow_eq_rpow_re_of_pos hM0 s
      have h2 : ‖(((N : ℝ) / d : ℝ) : ℂ) ^ s‖ = ((N : ℝ) / d) ^ s.re :=
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) s
      have h3 : ((N : ℝ) / d) ^ s.re ≤ (2 * M) ^ s.re :=
        Real.rpow_le_rpow (by linarith) (by linarith) hs0.le
      have h4 : (2 * (M : ℝ)) ^ s.re ≤ 2 * (M : ℝ) ^ s.re := by
        rw [Real.mul_rpow (by norm_num) hM0.le]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 : ℝ) ^ s.re ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1.le
          _ = 2 := Real.rpow_one 2
      have h5 : (M : ℝ) ^ s.re = (M : ℝ) ^ (s.re - 1) * M := by
        rw [Real.rpow_sub hM0, Real.rpow_one]; field_simp
      calc ‖(((M : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s‖
          ≤ ‖(((M : ℕ) : ℝ) : ℂ) ^ s‖ + ‖(((N : ℝ) / d : ℝ) : ℂ) ^ s‖ := norm_sub_le _ _
        _ ≤ 3 * (M : ℝ) ^ s.re := by rw [h1, h2]; linarith
        _ = 3 * (M : ℝ) ^ (s.re - 1) * M := by rw [h5]; ring
        _ ≤ 3 * (M : ℝ) ^ (s.re - 1) * ‖s‖ := by gcongr
  -- the strip error at `w = 1 − s`
  have hw0 : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw1 : (1 : ℂ) - s ≠ 1 := fun h => hs0' (by linear_combination -h)
  have hwim : |(1 - s).im| ≤ Real.pi * M := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hτ
  have hstr := norm_zetaStripError_le_grid hw0 hw1 hM1 hwim
  have hre : -(1 - s).re = s.re - 1 := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hre] at hstr
  rw [hz, zero_add]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **The conductor polynomial at a zero below its grid.** If `ζ(1 − s) = 0`, `0 < Re s < 1`,
`N ≥ 2e` and `|Im s| ≤ π⌊N/e⌋`, then `‖D_e(s;N) − [e = 1]N^s/s‖ ≤ 24 e³ N^{Re s − 1}`. -/
theorem norm_conductorDirichlet_sub_horizonTerm_le_grid {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) (hz : riemannZeta (1 - s) = 0) {e N : ℕ} (he : 1 ≤ e) (heN : 2 * e ≤ N)
    (hτ : |s.im| ≤ Real.pi * (N / e : ℕ)) :
    ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤ 24 * (e : ℝ) ^ 3 * (N : ℝ) ^ (s.re - 1) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hrw : conductorDirichlet e N s - horizonTerm e N s =
      ∑ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
        (riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
          RHTower.zetaStripError (1 - s) (N / d)) := by
    rw [conductorDirichlet_eq, horizonTerm_eq_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [partialZeta_eq]
    field_simp
    ring
  rw [hrw]
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have he1R : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hN0 : (0 : ℝ) < N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hσ : s.re - 1 ≤ 0 := by linarith
  have hterm : ∀ d ∈ e.divisors, ‖(moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
      (riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d))‖ ≤
      24 * (e : ℝ) ^ 2 * (N : ℝ) ^ (s.re - 1) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hde : d ≤ e := Nat.divisor_le hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdeR : (d : ℝ) ≤ e := by exact_mod_cast hde
    have hτd : |s.im| ≤ Real.pi * (N / d : ℕ) := by
      refine hτ.trans (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le)
      exact_mod_cast Nat.div_le_div_left hde hd1
    have hdiv := norm_divisorTerm_le_grid hs0 hs1 hz hd1 (by omega) hτd
    have hμ : ‖(moebiusReal (e / d) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_moebiusReal_le _
    have hds : ‖((d : ℝ) : ℂ) ^ s‖ ≤ e := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hd0]
      calc (d : ℝ) ^ s.re ≤ (d : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) hs1.le
        _ = d := Real.rpow_one _
        _ ≤ e := hdeR
    -- `⌊N/d⌋ ≥ N/(2e)`, so `⌊N/d⌋^{σ−1} ≤ 2e N^{σ−1}`
    have hMd : (N : ℝ) / (2 * e) ≤ ((N / d : ℕ) : ℝ) := by
      have h1 := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
      have h1' : (N : ℝ) < (((N / d) * d + d : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      have h2 : (2 * d : ℝ) ≤ N := by
        have : 2 * d ≤ N := by omega
        exact_mod_cast this
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hNpos : (0 : ℝ) < (N : ℝ) / (2 * e) := by positivity
    have hM : ((N / d : ℕ) : ℝ) ^ (s.re - 1) ≤ 2 * e * (N : ℝ) ^ (s.re - 1) := by
      refine (Real.rpow_le_rpow_of_nonpos hNpos hMd hσ).trans ?_
      rw [div_eq_mul_inv, Real.mul_rpow hN0.le (by positivity), Real.inv_rpow (by positivity),
        ← Real.rpow_neg (by positivity), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (2 * (e : ℝ)) ^ (-(s.re - 1)) ≤ (2 * (e : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 * e := Real.rpow_one _
    rw [norm_mul, norm_mul]
    calc ‖(moebiusReal (e / d) : ℂ)‖ * ‖((d : ℝ) : ℂ) ^ s‖ *
          ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
            RHTower.zetaStripError (1 - s) (N / d)‖
        ≤ 1 * e * (12 * (2 * e * (N : ℝ) ^ (s.re - 1))) := by
          gcongr
          exact hdiv.trans (mul_le_mul_of_nonneg_left hM (by norm_num))
      _ = 24 * (e : ℝ) ^ 2 * (N : ℝ) ^ (s.re - 1) := by ring
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hcard : (e.divisors.card : ℝ) ≤ e := by exact_mod_cast Nat.card_divisors_le_self e
  calc (e.divisors.card : ℝ) * (24 * (e : ℝ) ^ 2 * (N : ℝ) ^ (s.re - 1)) ≤
        e * (24 * (e : ℝ) ^ 2 * (N : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
