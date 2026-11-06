import GaloisForLFunctions.HTGeometry.HamburgerIntegralMassRigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationNearIntegers

/-!
# Integrable functional-equation defects at unit density are rigid

For a positive discrete spectrum beginning at 1, with each atom of mass at least 1, an
integrable uncompleted Riemann functional-equation defect and pole residue at most 1 force
the positive-integer counting measure. The defect contributes no radial residue to the
Laplace identity. Positivity then saturates every atom's cosine bound.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Saturation of the cosine bound at every atom forces all frequencies onto the integer lattice;
the zero limits at missing frequencies then fill the lattice. -/
private theorem integer_spectrum_of_unit_abel_limits {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hunit : ∀ n, a n = 1) (ha : Summable fun n => a n / lam n ^ 2)
    (hC0 : Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))))
    (hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))))
    (hgap : ∀ τ c : ℝ, 0 < τ → 0 < c → (∀ n, c * lam n ≤ |lam n - τ|) →
      Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 0)) :
    ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => by rw [hunit n]; norm_num
  have hπ2 : 0 < 1 / (2 * Real.pi) := by positivity
  -- integral frequencies
  have hint : ∀ m, ∃ K : ℕ, lam m = K := by
    intro m
    set K : ℕ := ⌊lam m⌋₊ with hK
    set f : ℝ := lam m - K with hf
    have hf0 : 0 ≤ f := by rw [hf, hK]; linarith [Nat.floor_le (hpos m).le]
    have hf1 : f < 1 := by rw [hf, hK]; linarith [Nat.lt_floor_add_one (lam m)]
    refine ⟨K, ?_⟩
    by_contra hne
    have hfpos : 0 < f := lt_of_le_of_ne hf0 (fun h => hne (by rw [hf] at h; linarith))
    -- `C_f → 0` since `f ∈ (0, 1)` is no atom
    have hCf : Tendsto (abelCos a lam f) (𝓝[>] 0) (𝓝 0) := by
      refine hgap f (1 - f) hfpos (by linarith) fun n => ?_
      rw [abs_of_pos (by linarith [hlam n])]
      nlinarith [hlam n]
    -- `C_0 - C_f ≤ 2(C_0 - C_{λ_m}) + 2K²(C_0 - C_{λ_0})`
    have hbound : ∀ ε, 0 < ε → abelCos a lam 0 ε - abelCos a lam f ε ≤
        2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε) +
          2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε) := by
      intro ε hε
      rw [abelCos_zero_sub hlam ha0 ha f hε, abelCos_zero_sub hlam ha0 ha (lam m) hε,
        abelCos_zero_sub hlam ha0 ha (lam 0) hε]
      have sm := summable_abelGap hlam ha0 ha (lam m) hε
      have s1 := summable_abelGap hlam ha0 ha (lam 0) hε
      have hsum : 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
          2 * (K : ℝ) ^ 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam 0))) =
          ∑' n, (2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
            2 * (K : ℝ) ^ 2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
              (1 - Real.cos (2 * Real.pi * lam n * lam 0)))) := by
        rw [(sm.mul_left 2).tsum_add (s1.mul_left _), tsum_mul_left, tsum_mul_left]
      have hle : ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * f)) ≤
          2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
          2 * (K : ℝ) ^ 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam 0))) := by
        rw [hsum]
        refine (summable_abelGap hlam ha0 ha f hε).tsum_le_tsum (fun n => ?_)
          ((sm.mul_left 2).add (s1.mul_left _))
        have hw := mul_nonneg (ha0 n) (Real.exp_pos (-(2 * Real.pi * lam n * ε))).le
        have htrig := one_sub_cos_frac_le (2 * Real.pi * lam n) (lam m) K
        rw [hlam0, mul_one]
        have e1 : 2 * Real.pi * lam n * f = 2 * Real.pi * lam n * (lam m - K) := by rw [hf]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left htrig hw]
      nlinarith [hle, hε.le]
    -- limits: the right side tends to `0`, so `C_f → 1/(2π)`
    have hR : Tendsto (fun ε => 2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε) +
        2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε => 2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε)) (𝓝[>] 0)
          (𝓝 0) := by
        have := (hC0.sub (hatom m)).const_mul 2
        rwa [hunit m, sub_self, mul_zero] at this
      have h2 : Tendsto (fun ε => 2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε))
          (𝓝[>] 0) (𝓝 0) := by
        have := (hC0.sub (hatom 0)).const_mul (2 * (K : ℝ) ^ 2)
        rwa [hunit 0, sub_self, mul_zero] at this
      simpa using h1.add h2
    have hlow : Tendsto (fun ε => abelCos a lam 0 ε - (2 * (abelCos a lam 0 ε -
        abelCos a lam (lam m) ε) + 2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε -
          abelCos a lam (lam 0) ε))) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      simpa using hC0.sub hR
    have hge : 1 / (2 * Real.pi) ≤ 0 := by
      refine le_of_tendsto_of_tendsto hlow hCf ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have := hbound ε hε
      linarith
    linarith
  -- every positive integer is a frequency
  have hsurj : ∀ k : ℕ, 1 ≤ k → ∃ n, lam n = k := by
    intro k hk
    by_contra hnone
    push Not at hnone
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    -- all frequencies are integers different from `k`
    have hsep : ∀ n, 1 / (2 * k) * lam n ≤ |lam n - k| := by
      intro n
      obtain ⟨K, hKn⟩ := hint n
      have hne : K ≠ k := fun h => hnone n (by rw [hKn, h])
      have hdist : 1 ≤ |lam n - k| := by
        rw [hKn]
        rcases lt_or_gt_of_ne hne with h | h
        · have : (K : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (k : ℝ) + 1 ≤ K := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rcases le_or_gt (lam n) (2 * k) with h | h
      · calc 1 / (2 * k) * lam n ≤ 1 / (2 * k) * (2 * k) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 1 := by field_simp
          _ ≤ |lam n - k| := hdist
      · rw [abs_of_pos (by linarith)]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have : 1 / (2 * (k : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        nlinarith [hpos n]
    have hCk := hgap k (1 / (2 * k)) hk0 (by positivity) hsep
    have heq : ∀ ε, abelCos a lam k ε = abelCos a lam 0 ε := by
      intro ε
      unfold abelCos
      congr 1
      refine tsum_congr fun n => ?_
      obtain ⟨K, hKn⟩ := hint n
      have : Real.cos (2 * Real.pi * lam n * k) = 1 := by
        rw [hKn, show 2 * Real.pi * (K : ℝ) * k = ((K * k : ℕ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        exact Real.cos_nat_mul_two_pi _
      rw [this]; simp
    have : Tendsto (abelCos a lam k) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      rw [show abelCos a lam k = abelCos a lam 0 from funext heq]; exact hC0
    have := tendsto_nhds_unique this hCk
    linarith
  -- strict monotonicity pins `λ_n = n + 1`
  have hval : ∀ n, lam n = n + 1 := by
    intro n
    induction n with
    | zero => simp [hlam0]
    | succ n ih =>
      obtain ⟨K, hK⟩ := hint (n + 1)
      have hlt : lam n < lam (n + 1) := hmono (Nat.lt_succ_self n)
      have hKge : n + 2 ≤ K := by
        rw [ih, hK] at hlt
        have : (n : ℝ) + 1 < K := by linarith
        exact_mod_cast (show n + 1 < K by exact_mod_cast this)
      obtain ⟨m, hm⟩ := hsurj (n + 2) (by omega)
      have hmn : n + 1 ≤ m := by
        by_contra h
        push Not at h
        have : lam m ≤ lam n := hmono.monotone (by omega)
        rw [hm, ih] at this
        push_cast at this
        linarith
      have hle : lam (n + 1) ≤ lam m := hmono.monotone hmn
      rw [hK, hm] at hle
      have hKle : K ≤ n + 2 := by exact_mod_cast hle
      rw [hK]
      push_cast
      have : K = n + 2 := le_antisymm hKle hKge
      rw [this]; push_cast; ring
  exact fun n => ⟨hval n, hunit n⟩


/-- An integrable defect has no radial residue at any point of the imaginary axis. -/
theorem tendsto_mul_integrable_defectLaplace {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hgi : Integrable g) (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  let M : ℝ := ∫ t, ‖g t‖
  have hM : 0 ≤ M := integral_nonneg fun t => norm_nonneg (g t)
  refine squeeze_zero_norm'
    (a := fun ε : ℝ => (3 / (2 * Real.pi) * M) * ε ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    let z : ℂ := (ε : ℂ) + (y : ℂ) * I
    have hz : 0 < z.re := by simpa [z] using hε0
    have hnorm : ε ≤ ‖z‖ := by
      have h := Complex.abs_re_le_norm z
      simpa [z, abs_of_pos hε0] using h
    have hδ : 0 < 2 * (z.re / ‖z‖) := mul_pos two_pos (pos_re_div_norm hz)
    have hmass : abelMass g (2 * (z.re / ‖z‖)) ≤ M := by
      apply integral_mono (integrable_abelMass hgm.aestronglyMeasurable hgb hδ) hgi.norm
      intro t
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hδ.le (abs_nonneg t))))
    have hpow : ‖z‖ ^ (-(1 / 2 : ℝ)) ≤ ε ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε0 hnorm (by norm_num)
    have hbound : ‖defectLaplace g z‖ ≤
        3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * M :=
      (norm_defectLaplace_le hgm.aestronglyMeasurable hgb hz).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hmass
          (integral_nonneg fun t => by positivity) (by positivity))
    have he : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hε0.le (by norm_num)]
      norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    calc ε * ‖defectLaplace g z‖ ≤ ε * (3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * M) :=
          mul_le_mul_of_nonneg_left hbound hε0.le
      _ = (3 / (2 * Real.pi) * M) * ε ^ (1 / 2 : ℝ) := by rw [← he]; ring
  · have h := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using (h.mono_left nhdsWithin_le_nhds).const_mul (3 / (2 * Real.pi) * M)

/-- The defective Laplace identity for arbitrary nonnegative discrete spectra. -/
theorem freqSeries_eq_of_theta_defect {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {z : ℂ} (hz : 0 < z.re) :
    freqSeries (fun n => (a n : ℂ)) lam z = freqDual (fun n => (a n : ℂ)) lam z +
      -β / (Real.pi * z) + β + defectLaplace g z := by
  let ν : Measure ℝ := Measure.sum fun n : ℕ => ENNReal.ofReal (a n) • Measure.dirac (lam n)
  have hc : ∀ n, ENNReal.ofReal (a n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsupp : ν (Iio 1) = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ measurableSet_Iio]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simp [hlam n]), mul_zero]
  have hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν := by
    refine integrable_sum_dirac hc (ha.congr fun n => ?_)
    have hl : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    rw [ENNReal.toReal_ofReal (ha0 n), Real.norm_eq_abs, abs_of_nonneg (by positivity),
      mul_one_div]
  have htheta : ∀ x, measureTheta ν x = freqTheta (fun n => (a n : ℂ)) lam x := by
    intro x
    unfold measureTheta freqTheta
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]
  have hseries : measureSeries ν z = freqSeries (fun n => (a n : ℂ)) lam z := by
    unfold measureSeries freqSeries
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]; ring
  have hdual : measureDual ν z = freqDual (fun n => (a n : ℂ)) lam z := by
    unfold measureDual freqDual
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]
  rw [← hseries, ← hdual]
  exact measureSeries_eq_of_theta_defect hsupp hmom hgm hgb
    (fun x hx => by rw [htheta x, htheta x⁻¹]; exact hθ x hx) hz

/-- At a positive height the defective Laplace identity has exactly the original atomic residue. -/
theorem abel_limit_of_defective_series {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hL : ∀ z : ℂ, 0 < z.re →
      freqSeries (fun n => (a n : ℂ)) lam z = freqDual (fun n => (a n : ℂ)) lam z +
        -β / (Real.pi * z) + β + defectLaplace g z)
    {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hres : Tendsto (fun ε : ℝ => (ε : ℂ) * freqSeries (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝 w)) :
    Tendsto (abelCos a lam y) (𝓝[>] 0) (𝓝 w.re) := by
  have hy0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hy.ne') I_ne_zero
  have hcont : ContinuousAt (fun ε : ℝ => (ε : ℂ) * β /
      (Real.pi * ((ε : ℂ) + (y : ℂ) * I)) - (ε : ℂ) * β) 0 := by
    refine (ContinuousAt.div (by fun_prop) (by fun_prop) ?_).sub (by fun_prop)
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simpa using mul_ne_zero hp hy0
  have hlin : Tendsto (fun ε : ℝ => (ε : ℂ) * β /
      (Real.pi * ((ε : ℂ) + (y : ℂ) * I)) - (ε : ℂ) * β) (𝓝[>] 0) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_abelCos_of_tendsto hlam ha0 ha
  have hh := (hres.add hlin).sub (tendsto_mul_integrable_defectLaplace hgm hgb hgi y)
  simp only [add_zero, sub_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hL _ (by simpa using hε)]
  ring

/-- The Abel density is the pole residue even when the functional equation has an integrable defect. -/
theorem tendsto_abelCos_zero_of_theta_defect {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hC0 : Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
    have hres := tendsto_mul_freqSeries_ofReal (a := fun n => (a n : ℂ)) hlam haC
    have hlin : Tendsto (fun ε : ℝ => (β : ℂ) / Real.pi - (ε : ℂ) * β)
        (𝓝[>] 0) (𝓝 ((β : ℂ) / Real.pi)) := by
      simpa using ((by fun_prop : Continuous fun ε : ℝ =>
        (β : ℂ) / Real.pi - (ε : ℂ) * β).tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := (hres.add hlin).sub (tendsto_mul_integrable_defectLaplace hgm hgb hgi 0)
    simp only [zero_add, sub_zero, Complex.ofReal_zero, zero_mul, add_zero] at hh
    have hF : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
        ((ε : ℂ) + ((0 : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 ((β : ℂ) / Real.pi)) := by
      refine hh.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have he : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rw [hL _ (by simpa using hε)]
      field_simp
      ring
    have hh := tendsto_abelCos_of_tendsto hlam ha0 ha hF
    have hre : ((β : ℂ) / Real.pi).re = β / Real.pi := by
      rw [show ((β : ℂ) / Real.pi) = ((β / Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rwa [hre] at hh
  exact hC0

/-- An integrable defect cannot deform a spectrum whose pole residue is at most one.
Every atom has mass at least one; positivity makes the mass and density inequalities equalities. -/
theorem integer_spectrum_of_integrable_theta_defect {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ} (hβ : β ≤ 1 / 2)
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_trans zero_le_one (ha1 n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ
    (z := z) hz
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  have hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))) := by
    intro m
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
    have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
      (hpos m) hc hsep
    have hh := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos m) hres
    have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
      rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    rwa [hre] at hh
  have hmass : ∀ m, a m ≤ 2 * β := by
    intro m
    have hh : a m / (2 * Real.pi) ≤ β / Real.pi := by
      refine le_of_tendsto_of_tendsto (hatom m) hC0 ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
    have hp := Real.pi_pos
    rw [div_le_div_iff₀ (by positivity) hp] at hh
    nlinarith only [hh, hp]
  have hb : β = 1 / 2 := by linarith only [hmass 0, ha1 0, hβ]
  have hunit : ∀ m, a m = 1 := fun m => by linarith only [hmass m, ha1 m, hβ]
  refine ⟨hb, integer_spectrum_of_unit_abel_limits hmono hlam0 hunit ha ?_ hatom ?_⟩
  · have hratio : β / Real.pi = 1 / (2 * Real.pi) := by rw [hb]; ring
    rwa [hratio] at hC0
  · intro y c hy hc hsep
    have hres := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ)) hlam haC hy.le hc hsep
    simpa using abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL hy hres

/-- Critical-line form of unit-density rigidity. The generalized Dirichlet series is allowed
arbitrary real frequencies; integrability of the reflection defect forces the ordinary integers. -/
theorem integer_spectrum_of_integrable_critical_line_defect {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n)
    (ha3 : Summable fun n => a n * lam n ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β C : ℝ} (hβ : β ≤ 1 / 2)
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * (∑' n, (a n : ℂ) * (lam n : ℂ) ^ (-s)) =
        E s + (β : ℂ) * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -((β : ℂ) * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) +
        Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hgi : Integrable g) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_trans zero_le_one (ha1 n)
  have ha : Summable fun n => a n / lam n ^ 2 := by
    refine ha3.of_nonneg_of_le (fun n => div_nonneg (ha0 n) (sq_nonneg _)) fun n => ?_
    have hl : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    have heq : 1 / lam n ^ 2 = lam n ^ (-2 : ℝ) := by
      rw [one_div, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hl.le,
        Real.rpow_natCast]
    rw [div_eq_mul_one_div, heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hlam n) (by norm_num)) (ha0 n)
  let ν : Measure ℝ := Measure.sum fun n : ℕ => ENNReal.ofReal (a n) • Measure.dirac (lam n)
  have hc : ∀ n, ENNReal.ofReal (a n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsupp : ν (Iio 1) = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ measurableSet_Iio]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simp [hlam n]), mul_zero]
  have hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν := by
    refine integrable_sum_dirac hc (ha3.congr fun n => ?_)
    rw [ENNReal.toReal_ofReal (ha0 n), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hlam n)) _)]
  have hmom2 := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  have htheta_eq : ∀ x, measureTheta ν x = freqTheta (fun n => (a n : ℂ)) lam x := by
    intro x
    unfold measureTheta freqTheta
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]
  have hdir : ∀ s, measureDirichlet ν s = ∑' n, (a n : ℂ) * (lam n : ℂ) ^ (-s) := by
    intro s
    unfold measureDirichlet
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom2
  have hθm : MellinConvergent (measureTheta ν) (3 / 4) := by
    have h := hasMellin_measureTheta hsupp (s := (3 / 2 : ℂ)) (by norm_num)
      (by simpa using hmom) hmom2
    simpa [show ((3 / 2 : ℂ) / 2) = (3 / 4 : ℂ) by ring] using h.1
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (measureTheta ν) (s / 2) = E s + (β : ℂ) * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hm := hasMellin_measureTheta hsupp (s := s) (by linarith only [hs])
      (by rw [hs]; exact hmom) hmom2
    rw [hm.2, hdir]; exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact integrable_Gammaℝ_mul hgm.aestronglyMeasurable hgb
  apply integer_spectrum_of_integrable_theta_defect hmono hlam0 ha1 ha hβ hgm hgb hgi
  intro x hx
  have hh := critical_line_even_theta_relation_defect
    (d := fun s => Complex.Gammaℝ s * g (s.im / 2))
    (continuousOn_measureTheta hsupp hmom2) hθm hEc hEd hdecay hR' hC hdint hx
  simp only [him, htheta_eq] at hh
  unfold defectKernel
  linear_combination hh

end GaloisForLFunctions.ArithmeticPositiveDuality
