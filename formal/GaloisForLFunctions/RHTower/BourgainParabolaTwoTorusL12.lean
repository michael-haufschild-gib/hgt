/-
# Twelfth-moment baseline for the discrete parabola

The exact two-torus `L⁶` theorem and the pointwise `L¹` bound give the
unconditional baseline

`∫_{T²} |Σ aₙ e(nu+n²v)|¹²
  ≪ε H^ε (Σ|aₙ|)⁶ (Σ|aₙ|²)³`.

For unit coefficients this is `H^(9+ε)`.  Bourgain's four-dimensional
decoupling theorem improves this baseline to `H^(6+ε)`; keeping the baseline
explicit isolates the exact three-power gain still required.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaTwoTorusL6

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Pointwise `L¹` bound for the two-torus parabola sum. -/
theorem norm_bourgainParabolaTwoTorusSum_le_l1
    (H : ℕ) (a : Fin H → ℂ) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖bourgainParabolaTwoTorusSum H a u v‖ ≤
      ∑ n : Fin H, ‖a n‖ := by
  calc
    ‖bourgainParabolaTwoTorusSum H a u v‖ ≤
        ∑ n : Fin H,
          ‖a n * u ^ bourgainIndex n *
            v ^ (bourgainIndex n ^ (2 : ℕ))‖ := by
      exact norm_sum_le _ _
    _ = ∑ n : Fin H, ‖a n‖ := by
      apply Fintype.sum_congr
      intro n
      simp [norm_pow, hu, hv]

/-- Joint continuity of the finite two-variable parabola sum. -/
theorem continuous_bourgainParabolaTwoTorusSum
    (H : ℕ) (a : Fin H → ℂ) :
    Continuous fun p : ℂ × ℂ =>
      bourgainParabolaTwoTorusSum H a p.1 p.2 := by
  rw [show
    (fun p : ℂ × ℂ =>
      bourgainParabolaTwoTorusSum H a p.1 p.2) =
    (fun p : ℂ × ℂ =>
      ∑ n : Fin H,
        a n * p.1 ^ bourgainIndex n *
          p.2 ^ (bourgainIndex n ^ (2 : ℕ))) by
      funext p
      rfl]
  apply continuous_finsetSum
  intro n _
  fun_prop

/-- On the unit two-torus, the twelfth power is the sixth power times a
uniform `L¹` factor. -/
theorem norm_bourgainParabolaTwoTorusSum_pow_twelve_le
    (H : ℕ) (a : Fin H → ℂ) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ) ≤
      (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ) *
        ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ) := by
  have hnorm :=
    norm_bourgainParabolaTwoTorusSum_le_l1 H a hu hv
  have hpow :
      ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ) ≤
        (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 6
  calc
    ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ) =
        ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ) *
          ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ) := by ring
    _ ≤ (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ) *
          ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)

/-- Nested circle averages preserve pointwise inequalities between continuous
two-variable real functions. -/
theorem circleAverage_circleAverage_mono
    {f g : ℂ → ℂ → ℝ}
    (hf : Continuous fun p : ℂ × ℂ => f p.1 p.2)
    (hg : Continuous fun p : ℂ × ℂ => g p.1 p.2)
    (hfg :
      ∀ u ∈ Metric.sphere (0 : ℂ) 1,
        ∀ v ∈ Metric.sphere (0 : ℂ) 1,
          f u v ≤ g u v) :
    Real.circleAverage
        (fun v => Real.circleAverage (fun u => f u v) 0 1) 0 1 ≤
      Real.circleAverage
        (fun v => Real.circleAverage (fun u => g u v) 0 1) 0 1 := by
  have hfInner :
      Continuous (fun v =>
        Real.circleAverage (fun u => f u v) 0 1) := by
    fun_prop [Real.circleAverage]
  have hgInner :
      Continuous (fun v =>
        Real.circleAverage (fun u => g u v) 0 1) := by
    fun_prop [Real.circleAverage]
  apply Real.circleAverage_mono
    (hfInner.continuousOn.circleIntegrable (by norm_num))
    (hgInner.continuousOn.circleIntegrable (by norm_num))
  intro v hv
  have hfu : Continuous (fun u => f u v) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hgu : Continuous (fun u => g u v) :=
    hg.comp (continuous_id.prodMk continuous_const)
  apply Real.circleAverage_mono
    (hfu.continuousOn.circleIntegrable (by norm_num))
    (hgu.continuousOn.circleIntegrable (by norm_num))
  intro u hu
  exact hfg u (by simpa using hu) v (by simpa using hv)

/-- The pointwise `L¹` estimate lifts to the nested torus averages. -/
theorem circleAverage_circleAverage_parabola_norm_pow_twelve_le_l1
    (H : ℕ) (a : Fin H → ℂ) :
    Real.circleAverage
        (fun v =>
          Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ))
            0 1)
        0 1 ≤
      (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ) *
        Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
              0 1)
          0 1 := by
  let L : ℝ := (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ)
  have hmono :
      Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ))
              0 1)
          0 1 ≤
        Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                L *
                  ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
              0 1)
          0 1 := by
    apply circleAverage_circleAverage_mono
    · exact (continuous_bourgainParabolaTwoTorusSum H a).norm.pow 12
    · exact continuous_const.mul
        ((continuous_bourgainParabolaTwoTorusSum H a).norm.pow 6)
    · intro u hu v hv
      have hunorm : ‖u‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hu
      have hvnorm : ‖v‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hv
      simpa [L] using
        norm_bourgainParabolaTwoTorusSum_pow_twelve_le H a hunorm hvnorm
  calc
    Real.circleAverage
        (fun v =>
          Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ))
            0 1)
        0 1 ≤
      Real.circleAverage
        (fun v =>
          Real.circleAverage
            (fun u =>
              L * ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
            0 1)
        0 1 := hmono
    _ = Real.circleAverage
        (fun v =>
          L * Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
            0 1)
        0 1 := by
      apply Real.circleAverage_congr_sphere
      intro v _
      change
        Real.circleAverage
            (fun u =>
              L * ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
            0 1 =
          L * Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
            0 1
      simpa [smul_eq_mul] using
        (Real.circleAverage_fun_smul
          (a := L)
          (f := fun u =>
            ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
          (c := 0) (R := 1))
    _ = L *
        Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
              0 1)
          0 1 := by
      simpa [smul_eq_mul] using
        (Real.circleAverage_fun_smul
          (a := L)
          (f := fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
              0 1)
          (c := 0) (R := 1))
    _ = (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ) *
        Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
              0 1)
          0 1 := by rfl

/-- Unconditional weighted `H^(9+ε)`-scale baseline. -/
theorem circleAverage_circleAverage_parabola_norm_pow_twelve_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a : Fin H → ℂ),
        Real.circleAverage
            (fun v =>
              Real.circleAverage
                (fun u =>
                  ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ))
                0 1)
            0 1 ≤
          (∑ n : Fin H, ‖a n‖) ^ (6 : ℕ) *
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hsix⟩ :=
    circleAverage_circleAverage_parabola_norm_pow_six_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a
  exact
    (circleAverage_circleAverage_parabola_norm_pow_twelve_le_l1 H a).trans
      (mul_le_mul_of_nonneg_left (hsix H a) (by positivity))

/-- Any unimodular coefficients give the explicit `H^9` baseline.  This
uniform form is the one needed after inserting Bourgain's higher-order phase
twists into the coefficients. -/
theorem circleAverage_circleAverage_parabola_norm_one_coeff_pow_twelve_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a : Fin H → ℂ),
        (∀ n, ‖a n‖ = 1) →
        Real.circleAverage
            (fun v =>
              Real.circleAverage
                (fun u =>
                  ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ))
                0 1)
            0 1 ≤
          C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by
  obtain ⟨C, hC, hweighted⟩ :=
    circleAverage_circleAverage_parabola_norm_pow_twelve_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a ha
  have h := hweighted H a
  have h' :
      Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (12 : ℕ))
              0 1)
          0 1 ≤
        (H : ℝ) ^ (6 : ℕ) *
          (C * (H : ℝ) ^ ε * (H : ℝ) ^ (3 : ℕ)) := by
    simpa [ha, Finset.sum_const, nsmul_eq_mul] using h
  calc
    _ ≤ (H : ℝ) ^ (6 : ℕ) *
        (C * (H : ℝ) ^ ε * (H : ℝ) ^ (3 : ℕ)) := h'
    _ = C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by ring

/-- Unit coefficients give the explicit `H^9` baseline (up to `H^ε`). -/
theorem circleAverage_circleAverage_parabola_one_norm_pow_twelve_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℕ,
        Real.circleAverage
            (fun v =>
              Real.circleAverage
                (fun u =>
                  ‖bourgainParabolaTwoTorusSum H (fun _ => 1) u v‖ ^
                    (12 : ℕ))
                0 1)
            0 1 ≤
          C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by
  obtain ⟨C, hC, hweighted⟩ :=
    circleAverage_circleAverage_parabola_norm_pow_twelve_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H
  have h := hweighted H (fun _ => 1)
  have h' :
      Real.circleAverage
          (fun v =>
            Real.circleAverage
              (fun u =>
                ‖bourgainParabolaTwoTorusSum H (fun _ => 1) u v‖ ^
                  (12 : ℕ))
              0 1)
          0 1 ≤
        (H : ℝ) ^ (6 : ℕ) *
          (C * (H : ℝ) ^ ε * (H : ℝ) ^ (3 : ℕ)) := by
    simpa [norm_one, Finset.sum_const, nsmul_eq_mul] using h
  calc
    _ ≤ (H : ℝ) ^ (6 : ℕ) *
        (C * (H : ℝ) ^ ε * (H : ℝ) ^ (3 : ℕ)) := h'
    _ = C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by ring

end

end RHTower
