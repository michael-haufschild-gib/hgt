import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

/-!
# Signed finite translation-edge bounds

The arithmetic product-fibre bridge translates by a negative logarithmic displacement, whereas
the existing factorial-envelope estimates were stated for a nonnegative displacement.  The raw
Taylor remainder estimates are sign-insensitive.  Replacing the displacement by its absolute
value gives the same geometric degree decay while retaining the original signed top edge.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The value edge at an arbitrary signed displacement is controlled by the shifted envelope at
the absolute displacement. -/
theorem norm_eval_finitePositivePhaseTranslationTopEdge_le_absShiftedFactorialEnvelope
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      3 * (((R : ℝ) * (x + |a|)) ^ (2 * d + 1) / (2 * d + 1).factorial *
        Real.exp ((R : ℝ) * (x + |a|))) := by
  let N : ℕ := 2 * d + 1
  let rx : ℝ := ‖(x : ℂ) * I * z‖
  let ra : ℝ := ‖(a : ℂ) * I * z‖
  let rs : ℝ := ‖((x + a : ℝ) : ℂ) * I * z‖
  let B : ℝ := (R : ℝ) * (x + |a|)
  have habs : 0 ≤ |a| := abs_nonneg a
  have hxa : 0 ≤ x + |a| := add_nonneg hx habs
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hxa
  have hsumabs : |x + a| ≤ x + |a| := by
    calc
      |x + a| ≤ |x| + |a| := abs_add_le x a
      _ = x + |a| := by rw [abs_of_nonneg hx]
  have hrx : rx = x * ‖z‖ := by simp [rx, abs_of_nonneg hx]
  have hra : ra = |a| * ‖z‖ := by simp [ra]
  have hrs : rs = |x + a| * ‖z‖ := by
    simp only [rs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one]
  have hrsle : rs ≤ B := by
    rw [hrs]
    dsimp only [B]
    calc
      |x + a| * ‖z‖ ≤ (x + |a|) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hsumabs (norm_nonneg z)
      _ ≤ (x + |a|) * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hz hxa
      _ = (R : ℝ) * (x + |a|) := by ring
  have hrxle : rx ≤ B := by
    rw [hrx]
    dsimp only [B]
    calc
      x * ‖z‖ ≤ x * (R : ℝ) := mul_le_mul_of_nonneg_left hz hx
      _ ≤ (R : ℝ) * (x + |a|) := by
        have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
        nlinarith
  have hrale : ra ≤ B := by
    rw [hra]
    dsimp only [B]
    calc
      |a| * ‖z‖ ≤ |a| * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hz habs
      _ ≤ (R : ℝ) * (x + |a|) := by
        have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
        nlinarith
  have hsumle : rx + ra ≤ B := by
    rw [hrx, hra]
    dsimp only [B]
    calc
      x * ‖z‖ + |a| * ‖z‖ = (x + |a|) * ‖z‖ := by ring
      _ ≤ (x + |a|) * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hz hxa
      _ = (R : ℝ) * (x + |a|) := by ring
  have htermX :
      (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra ≤
        (B ^ N / N.factorial) * Real.exp B := by
    rw [show (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra =
      (rx ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    gcongr
  have htermA :
      Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) ≤
        (B ^ N / N.factorial) * Real.exp B := by
    rw [show Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) =
      (ra ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    gcongr
  have htermS :
      (rs ^ N / N.factorial) * Real.exp rs ≤
        (B ^ N / N.factorial) * Real.exp B := by
    gcongr
  have h := norm_eval_finitePositivePhaseTranslationTopEdge_le d x a z
  change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra +
        Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) +
        (rs ^ N / N.factorial) * Real.exp rs at h
  change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      3 * (B ^ N / N.factorial * Real.exp B)
  nlinarith

/-- The derivative edge obeys the same signed envelope, with only the existing linear cutoff
losses. -/
theorem norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le_absShiftedFactorialEnvelope
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hRone : 1 ≤ R) (hx : 0 ≤ x) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      3 * (2 * d + 1 : ℕ) *
          ((((R : ℝ) * (x + |a|)) ^ (2 * d + 1) / (2 * d + 1).factorial) *
            Real.exp ((R : ℝ) * (x + |a|))) +
        2 * (2 * d + 2 : ℕ) *
          ((((R : ℝ) * (x + |a|)) ^ (2 * d + 2) / (2 * d + 2).factorial) *
            Real.exp ((R : ℝ) * (x + |a|))) := by
  let M : ℕ := 2 * d
  let N : ℕ := M + 1
  let rx : ℝ := ‖(x : ℂ) * I * z‖
  let ra : ℝ := ‖(a : ℂ) * I * z‖
  let rs : ℝ := ‖((x + a : ℝ) : ℂ) * I * z‖
  let cx : ℝ := ‖(x : ℂ) * I‖
  let ca : ℝ := ‖(a : ℂ) * I‖
  let cs : ℝ := ‖((x + a : ℝ) : ℂ) * I‖
  let B : ℝ := (R : ℝ) * (x + |a|)
  let EN : ℝ := (B ^ N / N.factorial) * Real.exp B
  let EN1 : ℝ := (B ^ (N + 1) / (N + 1).factorial) * Real.exp B
  have habs : 0 ≤ |a| := abs_nonneg a
  have hxa : 0 ≤ x + |a| := add_nonneg hx habs
  have hR : (1 : ℝ) ≤ R := by exact_mod_cast hRone
  have hB : 0 ≤ B := mul_nonneg (by positivity) hxa
  have hsumabs : |x + a| ≤ x + |a| := by
    calc
      |x + a| ≤ |x| + |a| := abs_add_le x a
      _ = x + |a| := by rw [abs_of_nonneg hx]
  have hrx : rx = x * ‖z‖ := by simp [rx, abs_of_nonneg hx]
  have hra : ra = |a| * ‖z‖ := by simp [ra]
  have hrs : rs = |x + a| * ‖z‖ := by
    simp only [rs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one]
  have hcx : cx = x := by simp [cx, abs_of_nonneg hx]
  have hca : ca = |a| := by simp [ca]
  have hcs : cs = |x + a| := by
    simp only [cs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one]
  have hrsle : rs ≤ B := by
    rw [hrs]
    dsimp only [B]
    calc
      |x + a| * ‖z‖ ≤ (x + |a|) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hsumabs (norm_nonneg z)
      _ ≤ (x + |a|) * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hz hxa
      _ = (R : ℝ) * (x + |a|) := by ring
  have hrxle : rx ≤ B := by
    rw [hrx]
    dsimp only [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hrale : ra ≤ B := by
    rw [hra]
    dsimp only [B]
    nlinarith [mul_le_mul_of_nonneg_left hz habs]
  have hsumle : rx + ra ≤ B := by
    rw [hrx, hra]
    dsimp only [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hcxle : cx ≤ B := by
    rw [hcx]
    dsimp only [B]
    have hsmall : x ≤ x + |a| := by linarith
    have hscale : x + |a| ≤ (R : ℝ) * (x + |a|) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hxa
    exact hsmall.trans hscale
  have hcale : ca ≤ B := by
    rw [hca]
    dsimp only [B]
    have hsmall : |a| ≤ x + |a| := by linarith
    have hscale : x + |a| ≤ (R : ℝ) * (x + |a|) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hxa
    exact hsmall.trans hscale
  have hcsle : cs ≤ B := by
    rw [hcs]
    dsimp only [B]
    have hscale : x + |a| ≤ (R : ℝ) * (x + |a|) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hxa
    exact hsumabs.trans hscale
  have hMN : N = 2 * d + 1 := by dsimp [N, M]
  have hderX :
      (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra ≤
        N * EN := by
    rw [show (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra =
      cx * (rx ^ M / M.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ M / M.factorial) * Real.exp B := by gcongr
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hderA :
      Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) ≤
        N * EN := by
    rw [show Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) =
      ca * (ra ^ M / M.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ M / M.factorial) * Real.exp B := by gcongr
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hderS :
      cs * ((rs ^ M / M.factorial) * Real.exp rs) ≤ N * EN := by
    have htailS : (rs ^ M / M.factorial) * Real.exp rs ≤
        (B ^ M / M.factorial) * Real.exp B := by gcongr
    calc
      _ ≤ B * ((B ^ M / M.factorial) * Real.exp B) :=
        mul_le_mul hcsle htailS (by positivity) hB
      _ = B * (B ^ M / M.factorial) * Real.exp B := by ring
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hvalA :
      cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) ≤
        (N + 1) * EN1 := by
    rw [show cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) =
      cx * (ra ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ N / N.factorial) * Real.exp B := by gcongr
      _ = (N + 1) * EN1 := by
        dsimp only [EN1]
        rw [← mul_assoc, mul_factorialEnvelope_eq_succ]
  have hvalX :
      ((rx ^ N / N.factorial) * Real.exp rx) *
          (ca * Real.exp ra) ≤ (N + 1) * EN1 := by
    rw [show ((rx ^ N / N.factorial) * Real.exp rx) *
        (ca * Real.exp ra) =
      ca * (rx ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ N / N.factorial) * Real.exp B := by gcongr
      _ = (N + 1) * EN1 := by
        dsimp only [EN1]
        rw [← mul_assoc, mul_factorialEnvelope_eq_succ]
  have h := norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le d x a z
  change ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra +
        cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) +
        ((rx ^ N / N.factorial) * Real.exp rx) * (ca * Real.exp ra) +
        Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) +
        cs * ((rs ^ M / M.factorial) * Real.exp rs) at h
  have hcomb : ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      3 * N * EN + 2 * (N + 1) * EN1 := by nlinarith
  calc
    _ ≤ 3 * N * EN + 2 * (N + 1) * EN1 := hcomb
    _ = _ := by
      dsimp only [EN, EN1, B]
      rw [hMN]
      push_cast
      ring

end

end RHTower
