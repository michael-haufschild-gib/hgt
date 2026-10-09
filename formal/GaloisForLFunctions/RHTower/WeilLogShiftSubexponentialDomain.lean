import GaloisForLFunctions.RHTower.WeilLogShiftCofinalPotential

/-!
# The potential domain is exactly subexponential coefficient growth

For arbitrary signed weights, whole-line paired-kernel convergence is
equivalent to summability after every positive exponential damping, and to
subexponential pointwise growth. Finite excess then identifies this elementary
growth condition with cofinal probe lower bounds and supplies a potential
positivity receiver without explicit convergence assumptions.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Each fixed log-kernel potential is bounded above by an exponentially
damped sequence in the integer index. -/
theorem exists_paired_logKernel_exponential_upper (y : ℝ) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      riemannAutocorr (y + log n) + riemannAutocorr (y - log n) ≤
        C * exp (-(ε * n)) := by
  obtain ⟨C, hC0, hC⟩ := ExposingRayTail.autocorr_upper (c := π / 2)
    (by positivity) (by linarith only [pi_pos])
  let ε := π * exp (-|y|)
  refine ⟨2 * C, ε, by positivity, by dsimp only [ε]; positivity, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbound (z : ℝ) (hz : log n - |y| ≤ |z|) :
      riemannAutocorr z ≤ C * exp (-(ε * n)) := by
    have he := exp_le_exp.mpr hz
    rw [sub_eq_add_neg, exp_add, exp_log hnpos] at he
    have hrate : ε * n ≤ π * exp |z| := by
      have h := mul_le_mul_of_nonneg_left he pi_pos.le
      dsimp only [ε]
      nlinarith only [h]
    have hk := hC z
    change riemannAutocorr z ≤ _ at hk
    rw [show 2 * (π / 2) = π by ring] at hk
    exact hk.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (neg_le_neg hrate)) hC0.le)
  have hp := hbound (y + log n) (by
    linarith only [neg_le_abs y, le_abs_self (y + log n)])
  have hm := hbound (y - log n) (by
    linarith only [le_abs_self y, neg_le_abs (y - log n)])
  linarith only [hp, hm]

/-- Every positive exponential damping rate is bounded below by a suitable
shifted log-kernel potential, up to a positive constant and a finite head. -/
theorem exists_paired_logKernel_exponential_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ y D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      D * exp (-(ε * n)) ≤
        riemannAutocorr (y + log n) + riemannAutocorr (y - log n) := by
  obtain ⟨D, Y, hD, hbound⟩ := ExposingRayTail.autocorr_lower (b := 4 * π)
    (by linarith only [pi_pos])
  let y := -log (ε / (4 * π))
  have hscale : 4 * π * exp (-y) = ε := by
    dsimp only [y]
    rw [neg_neg, exp_log (div_pos hε (by positivity))]
    field_simp
  refine ⟨y, D, hD, eventually_atTop.mpr ⟨⌊exp (Y + y)⌋₊ + 1, fun n hn => ?_⟩⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (⌊exp (Y + y)⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hlog : Y + y < log n := (lt_log_iff_exp_lt hnpos).mpr
    ((Nat.lt_floor_add_one _).trans_le hnR)
  have hk := hbound (log n - y) (by linarith only [hlog])
  change D * exp (-(4 * π * exp (log n - y))) ≤ riemannAutocorr (log n - y) at hk
  have heq : 4 * π * exp (log n - y) = ε * n := by
    rw [sub_eq_add_neg, exp_add, exp_log hnpos]
    calc 4 * π * ((n : ℝ) * exp (-y)) = (4 * π * exp (-y)) * n := by ring
      _ = ε * n := by rw [hscale]
  rw [heq, show log n - y = -(y - log n) by ring, riemannAutocorr_neg] at hk
  linarith only [hk, riemannAutocorr_nonneg (y + log n)]

/-- Whole-line kernel-potential convergence is equivalent to summability after
every positive exponential damping of the absolute coefficient sequence. -/
theorem summable_kernelPotential_iff_exponential_damping (v : ℕ → ℝ) :
    (∀ y : ℝ, Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) ↔
    ∀ ε : ℝ, 0 < ε → Summable fun n => |v n| * exp (-(ε * n)) := by
  constructor
  · intro hs ε hε
    obtain ⟨y, D, hD, hlower⟩ := exists_paired_logKernel_exponential_lower hε
    refine ((hs y).norm.mul_left (1 / D)).of_norm_bounded_eventually_nat ?_
    filter_upwards [hlower] with n hn
    have h := mul_le_mul_of_nonneg_left hn (abs_nonneg (v n))
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (exp_pos (-(ε * n))),
      abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (y + log n))
        (riemannAutocorr_nonneg (y - log n)))]
    calc
      |v n| * exp (-(ε * n)) ≤
          (|v n| * (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) / D :=
        (le_div_iff₀ hD).mpr (by nlinarith only [h])
      _ = _ := by ring
  · intro hs y
    obtain ⟨C, ε, hC, hε, hupper⟩ := exists_paired_logKernel_exponential_upper y
    refine ((hs ε hε).mul_left C).of_norm_bounded_eventually_nat ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h := mul_le_mul_of_nonneg_left (hupper n hn) (abs_nonneg (v n))
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (y + log n))
        (riemannAutocorr_nonneg (y - log n)))]
    nlinarith only [h]

/-- Summability after every positive exponential damping is exactly
subexponential pointwise growth, for arbitrary real sequences. -/
theorem summable_exponential_damping_iff_subexponential (v : ℕ → ℝ) :
    (∀ ε : ℝ, 0 < ε → Summable fun n => |v n| * exp (-(ε * n))) ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |v n| ≤ C * exp (ε * n) := by
  constructor
  · intro hs ε hε
    let C := ∑' n, |v n| * exp (-(ε * n))
    refine ⟨C, tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (exp_pos _).le), fun n => ?_⟩
    have ht := (hs ε hε).le_tsum n
      (fun j _ => mul_nonneg (abs_nonneg (v j)) (exp_pos (-(ε * j))).le)
    have heq : exp (-(ε * n)) * exp (ε * n) = 1 := by rw [← exp_add]; simp
    calc
      |v n| = (|v n| * exp (-(ε * n))) * exp (ε * n) := by rw [mul_assoc, heq, mul_one]
      _ ≤ C * exp (ε * n) := mul_le_mul_of_nonneg_right ht (exp_pos _).le
  · intro hg ε hε
    obtain ⟨C, hC0, hC⟩ := hg (ε / 2) (by positivity)
    have hgeo : Summable fun n : ℕ => exp ((n : ℝ) * (-(ε / 2))) :=
      summable_exp_nat_mul_iff.mpr (by linarith only [hε])
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (exp_pos _).le) (fun n => ?_) (hgeo.mul_left C)
    calc
      |v n| * exp (-(ε * n)) ≤ (C * exp (ε / 2 * n)) * exp (-(ε * n)) :=
        mul_le_mul_of_nonneg_right (hC n) (exp_pos _).le
      _ = C * exp ((n : ℝ) * (-(ε / 2))) := by
        rw [mul_assoc, ← exp_add,
          show ε / 2 * (n : ℝ) + -(ε * n) = (n : ℝ) * (-(ε / 2)) by ring]

/-- The full real-shift potential domain is exactly subexponential coefficient
growth. No sign restriction or finite-excess assumption is needed. -/
theorem summable_kernelPotential_iff_subexponential (v : ℕ → ℝ) :
    (∀ y : ℝ, Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |v n| ≤ C * exp (ε * n) :=
  (summable_kernelPotential_iff_exponential_damping v).trans
    (summable_exponential_damping_iff_subexponential v)

/-- With finite excess, subexponential normalized-deviation growth is exactly
detected by lower bounds on any cofinal sequence of actual probes. -/
theorem subexponential_deviation_iff_cofinal_probe_lower_bounds {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (m : ℕ → ℕ)
    (hcofinal : ∀ R : ℝ, ∃ j : ℕ, R ≤ log (m j)) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |weilDeviation lam n| ≤ C * exp (ε * n)) ↔
    ∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log (m j)))
        (logShiftRiemannDifference k (log (m j))))).re :=
  (summable_kernelPotential_iff_subexponential (weilDeviation lam)).symm.trans
    (summable_potential_iff_cofinal_probe_lower_bounds hexc m hcofinal)

/-- Subexponential normalized-deviation growth supplies the exact convergence
domain for the finite-excess potential-inequality positivity criterion. -/
theorem weilLogShiftAsymptoticPositive_iff_subexponential_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |weilDeviation lam n| ≤ C * exp (ε * n)) ∧
      ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (log m) := by
  constructor
  · intro hpos
    exact ⟨(summable_kernelPotential_iff_subexponential (weilDeviation lam)).mp
      (summable_potential_of_logShiftAsymptoticPositive hpos hexc),
      logShiftAsymptotic_potential_le_of_summable_excess hpos hexc⟩
  · rintro ⟨hgrowth, hpotential⟩
    have hs := (summable_kernelPotential_iff_subexponential (weilDeviation lam)).mpr hgrowth
    exact (weilLogShiftAsymptoticPositive_iff_sampled_potential hexc).mpr
      (fun m hm => ⟨hs (log m), hpotential m hm⟩)

end RHTower
