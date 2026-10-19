import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds

/-!
# Pointwise bounds for the ground jumps and the potential kernel of the shifted ground states

With `R ≥ 1` a support radius of the even factor `u`, `M_u`, `L_u` a bound and a Lipschitz constant of
`u`, `M_ω` a bound of `ω_a` on `[−R−1, R+1]`, and `L_Φ`, `L_m` Lipschitz constants of Riemann's kernel
and of the shift difference on `[−R−1, R+1]`, the potential kernel of `ω_a` satisfies on `0 < x ≤ R`

    |K_a(t,x)| ≤ Φ(0)(2 M_ω L_Φ + 2 L_m) t            (0 < t ≤ 1),
    |K_a(t,x)| ≤ Φ(0)(2 M_ω Φ(0) + 2 Φ(0))            (all t),
    |K_a(t,x)| ≤ Φ(0)(2 M_ω + 2) Φ(t − R − a)         (t ≥ R + a),

and the same-side and reflected ground jumps satisfy linear-in-`t` and `Φ(t − R − a)`-decay bounds.
These are the estimates behind the admissibility of `ω_a` in the folded ground-state representation.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Small-shift bound -/

theorem abs_abs_sub_sub_le {x t : ℝ} (hx : 0 ≤ x) : abs (|x - t| - x) ≤ |t| := by
  have h := abs_abs_sub_abs_le_abs_sub (x - t) x
  rw [abs_of_nonneg hx] at h
  rw [show x - t - x = -t by ring, abs_neg] at h
  exact h

theorem shiftedPotentialKernel_abs_le_linear {a R Mω LΦ Lm : ℝ} (hR : 1 ≤ R)
    (hMω : ∀ y ∈ Icc (-R - 1) (R + 1), |shiftedGroundState a y| ≤ Mω)
    (hLΦ : ∀ y ∈ Icc (-R - 1) (R + 1), ∀ z ∈ Icc (-R - 1) (R + 1),
      |riemannKernelReal z - riemannKernelReal y| ≤ LΦ * |z - y|)
    (hLm : ∀ y ∈ Icc (-R - 1) (R + 1), ∀ z ∈ Icc (-R - 1) (R + 1),
      |shiftDifference a z - shiftDifference a y| ≤ Lm * |z - y|)
    {t x : ℝ} (hx0 : 0 < x) (hxR : x ≤ R) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |shiftedPotentialKernel a t x| ≤
      riemannKernelReal 0 * (2 * Mω * LΦ + 2 * Lm) * t := by
  have hx : x ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
  have hxt : x + t ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
  have habs_le : |x - t| ≤ R := by
    rw [abs_le]
    constructor <;> linarith
  have hxa : |x - t| ∈ Icc (-R - 1) (R + 1) := ⟨by linarith [abs_nonneg (x - t)], by linarith⟩
  have hd : abs (|x - t| - x) ≤ t := by
    have := abs_abs_sub_sub_le (t := t) hx0.le
    rwa [abs_of_pos ht0] at this
  have hΦ1 := hLΦ x hx (x + t) hxt
  have hΦ2 := hLΦ x hx |x - t| hxa
  have hm1 := hLm x hx (x + t) hxt
  have hm2 := hLm x hx |x - t| hxa
  rw [show x + t - x = t by ring, abs_of_pos ht0] at hΦ1 hm1
  have hLΦ0 : 0 ≤ LΦ := by
    rcases le_or_gt 0 LΦ with h | h
    · exact h
    · exfalso
      have hneg : LΦ * t < 0 := mul_neg_of_neg_of_pos h ht0
      linarith [abs_nonneg (riemannKernelReal (x + t) - riemannKernelReal x)]
  have hLm0 : 0 ≤ Lm := by
    rcases le_or_gt 0 Lm with h | h
    · exact h
    · exfalso
      have hneg : Lm * t < 0 := mul_neg_of_neg_of_pos h ht0
      linarith [abs_nonneg (shiftDifference a (x + t) - shiftDifference a x)]
  have hΦ2' : abs (riemannKernelReal |x - t| - riemannKernelReal x) ≤ LΦ * t :=
    hΦ2.trans (mul_le_mul_of_nonneg_left hd hLΦ0)
  have hm2' : abs (shiftDifference a |x - t| - shiftDifference a x) ≤ Lm * t :=
    hm2.trans (mul_le_mul_of_nonneg_left hd hLm0)
  have hω := hMω x hx
  have hmx := abs_shiftDifference_le a x
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hMω0 : 0 ≤ Mω := le_trans (abs_nonneg _) hω
  rw [shiftedPotentialKernel_eq_differences, abs_mul]
  set y := |x - t| with hy
  have e1 := mul_le_mul hω hΦ1 (abs_nonneg _) hMω0
  have e2 := mul_le_mul hω hΦ2' (abs_nonneg _) hMω0
  calc |shiftDifference a x| *
        |shiftedGroundState a x * (riemannKernelReal (x + t) - riemannKernelReal x) +
          shiftedGroundState a x * (riemannKernelReal y - riemannKernelReal x) -
          (shiftDifference a (x + t) - shiftDifference a x) -
          (shiftDifference a y - shiftDifference a x)|
      ≤ riemannKernelReal 0 *
        (|shiftedGroundState a x| * |riemannKernelReal (x + t) - riemannKernelReal x| +
          |shiftedGroundState a x| * |riemannKernelReal y - riemannKernelReal x| +
          |shiftDifference a (x + t) - shiftDifference a x| +
          |shiftDifference a y - shiftDifference a x|) := by
        apply mul_le_mul hmx _ (abs_nonneg _) hΘ0
        calc |shiftedGroundState a x * (riemannKernelReal (x + t) - riemannKernelReal x) +
              shiftedGroundState a x * (riemannKernelReal y - riemannKernelReal x) -
              (shiftDifference a (x + t) - shiftDifference a x) -
              (shiftDifference a y - shiftDifference a x)|
            ≤ |shiftedGroundState a x * (riemannKernelReal (x + t) - riemannKernelReal x) +
              shiftedGroundState a x * (riemannKernelReal y - riemannKernelReal x) -
              (shiftDifference a (x + t) - shiftDifference a x)| +
              |shiftDifference a y - shiftDifference a x| := abs_sub _ _
          _ ≤ (|shiftedGroundState a x * (riemannKernelReal (x + t) - riemannKernelReal x) +
              shiftedGroundState a x * (riemannKernelReal y - riemannKernelReal x)| +
              |shiftDifference a (x + t) - shiftDifference a x|) +
              |shiftDifference a y - shiftDifference a x| := by
                gcongr
                exact abs_sub _ _
          _ ≤ ((|shiftedGroundState a x * (riemannKernelReal (x + t) - riemannKernelReal x)| +
              |shiftedGroundState a x * (riemannKernelReal y - riemannKernelReal x)|) +
              |shiftDifference a (x + t) - shiftDifference a x|) +
              |shiftDifference a y - shiftDifference a x| := by
                gcongr
                exact abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ riemannKernelReal 0 * (Mω * (LΦ * t) + Mω * (LΦ * t) + Lm * t + Lm * t) := by
        apply mul_le_mul_of_nonneg_left _ hΘ0
        linarith
    _ = riemannKernelReal 0 * (2 * Mω * LΦ + 2 * Lm) * t := by ring

/-! ### Uniform and decaying bounds -/

theorem shiftedPotentialKernel_abs_le_uniform {a R Mω : ℝ}
    (hMω : ∀ y ∈ Icc (-R - 1) (R + 1), |shiftedGroundState a y| ≤ Mω)
    {t x : ℝ} (hx0 : 0 < x) (hxR : x ≤ R) :
    |shiftedPotentialKernel a t x| ≤
      riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) := by
  have hRge : 0 ≤ R := le_trans hx0.le hxR
  have hx : x ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
  have hω := hMω x hx
  have hMω0 : 0 ≤ Mω := le_trans (abs_nonneg _) hω
  have hΘ0 := (riemannKernelReal_pos 0).le
  have h1 := riemannKernelReal_le_zero_point (x + t)
  have h2 := riemannKernelReal_le_zero_point |x - t|
  have h3 := abs_shiftDifference_le a (x + t)
  have h4 := abs_shiftDifference_le a |x - t|
  have hp1 := (riemannKernelReal_pos (x + t)).le
  have hp2 := (riemannKernelReal_pos |x - t|).le
  unfold shiftedPotentialKernel
  rw [abs_mul]
  set y := |x - t| with hy
  have hsum : 0 ≤ riemannKernelReal (x + t) + riemannKernelReal y := add_nonneg hp1 hp2
  calc |shiftDifference a x| *
        |shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal y) -
          (shiftDifference a (x + t) + shiftDifference a y)|
      ≤ riemannKernelReal 0 *
        (|shiftedGroundState a x| * (riemannKernelReal (x + t) + riemannKernelReal y) +
          (|shiftDifference a (x + t)| + |shiftDifference a y|)) := by
        apply mul_le_mul (abs_shiftDifference_le a x) _ (abs_nonneg _) hΘ0
        calc |shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal y) -
              (shiftDifference a (x + t) + shiftDifference a y)|
            ≤ |shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal y)| +
              |shiftDifference a (x + t) + shiftDifference a y| := abs_sub _ _
          _ ≤ |shiftedGroundState a x| * (riemannKernelReal (x + t) + riemannKernelReal y) +
              (|shiftDifference a (x + t)| + |shiftDifference a y|) := by
                rw [abs_mul, abs_of_nonneg hsum]
                gcongr
                exact abs_add_le _ _
    _ ≤ riemannKernelReal 0 *
        (Mω * (riemannKernelReal 0 + riemannKernelReal 0) +
          (riemannKernelReal 0 + riemannKernelReal 0)) := by
        apply mul_le_mul_of_nonneg_left _ hΘ0
        have := mul_le_mul hω (add_le_add h1 h2) hsum hMω0
        linarith
    _ = riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) := by ring

theorem shiftedPotentialKernel_abs_le_decay {a R Mω : ℝ} (ha : 0 < a)
    (hMω : ∀ y ∈ Icc (-R - 1) (R + 1), |shiftedGroundState a y| ≤ Mω)
    {t x : ℝ} (hx0 : 0 < x) (hxR : x ≤ R) (ht : R + a ≤ t) :
    |shiftedPotentialKernel a t x| ≤
      riemannKernelReal 0 * (2 * Mω + 2) * riemannKernelReal (t - R - a) := by
  have hRge : 0 ≤ R := le_trans hx0.le hxR
  have hx : x ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
  have hω := hMω x hx
  have hMω0 : 0 ≤ Mω := le_trans (abs_nonneg _) hω
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hc0 : 0 ≤ t - R - a := by linarith
  have habs : |x - t| = t - x := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have h1 : riemannKernelReal (x + t) ≤ riemannKernelReal (t - R - a) :=
    riemannKernelReal_antitone_of_nonneg hc0 (by linarith)
  have h2 : riemannKernelReal |x - t| ≤ riemannKernelReal (t - R - a) := by
    rw [habs]
    exact riemannKernelReal_antitone_of_nonneg hc0 (by linarith)
  have h3 : |shiftDifference a (x + t)| ≤ riemannKernelReal (t - R - a) :=
    (abs_shiftDifference_le_kernel_of_nonneg ha.le (by linarith)).trans
      (riemannKernelReal_antitone_of_nonneg hc0 (by linarith))
  have h4 : abs (shiftDifference a |x - t|) ≤ riemannKernelReal (t - R - a) := by
    rw [habs]
    exact (abs_shiftDifference_le_kernel_of_nonneg ha.le (by linarith)).trans
      (riemannKernelReal_antitone_of_nonneg hc0 (by linarith))
  have hK := (riemannKernelReal_pos (t - R - a)).le
  have hp1 := (riemannKernelReal_pos (x + t)).le
  have hp2 := (riemannKernelReal_pos |x - t|).le
  unfold shiftedPotentialKernel
  rw [abs_mul]
  set y := |x - t| with hy
  have hsum : 0 ≤ riemannKernelReal (x + t) + riemannKernelReal y := add_nonneg hp1 hp2
  calc |shiftDifference a x| *
        |shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal y) -
          (shiftDifference a (x + t) + shiftDifference a y)|
      ≤ riemannKernelReal 0 *
        (|shiftedGroundState a x| * (riemannKernelReal (x + t) + riemannKernelReal y) +
          (|shiftDifference a (x + t)| + |shiftDifference a y|)) := by
        apply mul_le_mul (abs_shiftDifference_le a x) _ (abs_nonneg _) hΘ0
        calc |shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal y) -
              (shiftDifference a (x + t) + shiftDifference a y)|
            ≤ |shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal y)| +
              |shiftDifference a (x + t) + shiftDifference a y| := abs_sub _ _
          _ ≤ |shiftedGroundState a x| * (riemannKernelReal (x + t) + riemannKernelReal y) +
              (|shiftDifference a (x + t)| + |shiftDifference a y|) := by
                rw [abs_mul, abs_of_nonneg hsum]
                gcongr
                exact abs_add_le _ _
    _ ≤ riemannKernelReal 0 *
        (Mω * (riemannKernelReal (t - R - a) + riemannKernelReal (t - R - a)) +
          (riemannKernelReal (t - R - a) + riemannKernelReal (t - R - a))) := by
        apply mul_le_mul_of_nonneg_left _ hΘ0
        have := mul_le_mul hω (add_le_add h1 h2) hsum hMω0
        linarith
    _ = riemannKernelReal 0 * (2 * Mω + 2) * riemannKernelReal (t - R - a) := by ring

/-- The unified decay bound `|K_a(t,x)| ≤ K Φ(t − R − a)` for all `t ≥ 0`, `0 < x ≤ R`. -/
theorem shiftedPotentialKernel_abs_le_decay_all {a R Mω : ℝ} (ha : 0 < a)
    (hMω : ∀ y ∈ Icc (-R - 1) (R + 1), |shiftedGroundState a y| ≤ Mω)
    {t x : ℝ} (hx0 : 0 < x) (hxR : x ≤ R) (ht : 0 ≤ t) :
    |shiftedPotentialKernel a t x| ≤
      max (riemannKernelReal 0 * (2 * Mω + 2))
        (riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) /
          riemannKernelReal (R + a)) * riemannKernelReal (t - R - a) := by
  have hK := (riemannKernelReal_pos (t - R - a)).le
  rcases le_or_gt (R + a) t with h | h
  · exact (shiftedPotentialKernel_abs_le_decay ha hMω hx0 hxR h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hK)
  · have hu := shiftedPotentialKernel_abs_le_uniform hMω hx0 hxR (t := t)
    have hΦ : riemannKernelReal (R + a) ≤ riemannKernelReal (t - R - a) := by
      have := riemannKernelReal_sub_ge_of_le ht h.le
      rwa [← sub_sub] at this
    have hΦpos := riemannKernelReal_pos (R + a)
    have hC0 : 0 ≤ riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) :=
      le_trans (abs_nonneg _) hu
    calc |shiftedPotentialKernel a t x|
        ≤ riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) := hu
      _ = riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) /
            riemannKernelReal (R + a) * riemannKernelReal (R + a) := by
            field_simp
      _ ≤ riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) /
            riemannKernelReal (R + a) * riemannKernelReal (t - R - a) :=
            mul_le_mul_of_nonneg_left hΦ (div_nonneg hC0 hΦpos.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hK

/-- The unified linear bound `|K_a(t,x)| ≤ K t` for all `t > 0`, `0 < x ≤ R`. -/
theorem shiftedPotentialKernel_abs_le_linear_all {a R Mω LΦ Lm : ℝ} (hR : 1 ≤ R)
    (hMω : ∀ y ∈ Icc (-R - 1) (R + 1), |shiftedGroundState a y| ≤ Mω)
    (hLΦ : ∀ y ∈ Icc (-R - 1) (R + 1), ∀ z ∈ Icc (-R - 1) (R + 1),
      |riemannKernelReal z - riemannKernelReal y| ≤ LΦ * |z - y|)
    (hLm : ∀ y ∈ Icc (-R - 1) (R + 1), ∀ z ∈ Icc (-R - 1) (R + 1),
      |shiftDifference a z - shiftDifference a y| ≤ Lm * |z - y|)
    {t x : ℝ} (hx0 : 0 < x) (hxR : x ≤ R) (ht0 : 0 < t) :
    |shiftedPotentialKernel a t x| ≤
      max (riemannKernelReal 0 * (2 * Mω * LΦ + 2 * Lm))
        (riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0)) * t := by
  rcases le_or_gt t 1 with h1 | h1
  · exact (shiftedPotentialKernel_abs_le_linear hR hMω hLΦ hLm hx0 hxR ht0 h1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le)
  · have hu := shiftedPotentialKernel_abs_le_uniform hMω hx0 hxR (t := t)
    have hC0 : 0 ≤ riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) :=
      le_trans (abs_nonneg _) hu
    calc |shiftedPotentialKernel a t x|
        ≤ riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) := hu
      _ ≤ riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) * t := by
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) ht0.le

/-! ### Bounds on the ground jumps -/

theorem sq_abs_sub_le_of_bounded {Mu : ℝ} {p q : ℝ} (hp : |p| ≤ Mu) (hq : |q| ≤ Mu) :
    |(p - q) ^ 2| ≤ 4 * Mu ^ 2 := by
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) hp
  have h2 : |p - q| ≤ 2 * Mu := by
    calc |p - q| ≤ |p| + |q| := abs_sub _ _
      _ ≤ Mu + Mu := add_le_add hp hq
      _ = 2 * Mu := by ring
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  calc |p - q| ^ 2 ≤ (2 * Mu) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = 4 * Mu ^ 2 := by ring

theorem sq_abs_add_le_of_bounded {Mu : ℝ} {p q : ℝ} (hp : |p| ≤ Mu) (hq : |q| ≤ Mu) :
    |(p + q) ^ 2| ≤ 4 * Mu ^ 2 := by
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) hp
  have h2 : |p + q| ≤ 2 * Mu := by
    calc |p + q| ≤ |p| + |q| := abs_add_le _ _
      _ ≤ Mu + Mu := add_le_add hp hq
      _ = 2 * Mu := by ring
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  calc |p + q| ^ 2 ≤ (2 * Mu) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = 4 * Mu ^ 2 := by ring

/-- Same-side ground jump: linear in `t`, supported in `x ≤ R`. -/
theorem sameSideGroundJump_shiftedGroundState_abs_le_linear {a R Mu Lu : ℝ}
    {u : ℝ → ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hMu : ∀ x, |u x| ≤ Mu)
    (hLu : ∀ x y, |u y - u x| ≤ Lu * |y - x|) {t x : ℝ} (hx0 : 0 < x) (ht0 : 0 < t) :
    |sameSideGroundJump (shiftedGroundState a) u t x| ≤
      riemannKernelReal 0 ^ 2 * (Lu ^ 2 + 4 * Mu ^ 2) * t *
        (if x ≤ R then 1 else 0) := by
  rw [sameSideGroundJump_shiftedGroundState]
  have hΘ := (riemannKernelReal_pos 0).le
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
  split_ifs with hxR
  · have hm1 := abs_shiftDifference_le a x
    have hm2 := abs_shiftDifference_le a (x + t)
    have hLu0 : 0 ≤ Lu := by
      have h := hLu x (x + 1)
      rw [show x + 1 - x = 1 by ring, abs_one, mul_one] at h
      exact le_trans (abs_nonneg _) h
    rw [abs_mul, abs_mul, mul_one]
    have hprod : |shiftDifference a x| * |shiftDifference a (x + t)| ≤ riemannKernelReal 0 ^ 2 := by
      calc |shiftDifference a x| * |shiftDifference a (x + t)|
          ≤ riemannKernelReal 0 * riemannKernelReal 0 :=
            mul_le_mul hm1 hm2 (abs_nonneg _) hΘ
        _ = riemannKernelReal 0 ^ 2 := by ring
    have hsq : |(u x - u (x + t)) ^ 2| ≤ (Lu ^ 2 + 4 * Mu ^ 2) * t := by
      rcases le_or_gt t 1 with h1 | h1
      · have hl := hLu (x + t) x
        rw [show x - (x + t) = -t by ring, abs_neg, abs_of_pos ht0] at hl
        have hsq' : (u x - u (x + t)) ^ 2 ≤ (Lu * t) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hl 2
        have hlt : (Lu * t) ^ 2 ≤ Lu ^ 2 * t := by
          have : (Lu * t) ^ 2 = Lu ^ 2 * t * t := by ring
          rw [this]
          exact mul_le_of_le_one_right (by positivity) h1
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg Lu, sq_nonneg Mu]
      · have h4 := sq_abs_sub_le_of_bounded (hMu x) (hMu (x + t))
        have : 4 * Mu ^ 2 ≤ (Lu ^ 2 + 4 * Mu ^ 2) * t := by
          nlinarith [sq_nonneg Lu, sq_nonneg Mu]
        linarith
    calc |shiftDifference a x| * |shiftDifference a (x + t)| * |(u x - u (x + t)) ^ 2|
        ≤ riemannKernelReal 0 ^ 2 * ((Lu ^ 2 + 4 * Mu ^ 2) * t) :=
          mul_le_mul hprod hsq (abs_nonneg _) (by positivity)
      _ = riemannKernelReal 0 ^ 2 * (Lu ^ 2 + 4 * Mu ^ 2) * t := by ring
  · rw [not_le] at hxR
    have h1 : u x = 0 := hsupp x (by rw [abs_of_pos hx0]; exact hxR)
    have h2 : u (x + t) = 0 := hsupp (x + t) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [h1, h2]
    simp

/-- Same-side ground jump: decay in `t`, supported in `x ≤ R`. -/
theorem sameSideGroundJump_shiftedGroundState_abs_le_decay {a R Mu : ℝ} (ha : 0 < a) (hR : 1 ≤ R)
    {u : ℝ → ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hMu : ∀ x, |u x| ≤ Mu)
    {t x : ℝ} (hx0 : 0 < x) (ht : R + a ≤ t) :
    |sameSideGroundJump (shiftedGroundState a) u t x| ≤
      4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) *
        (if x ≤ R then 1 else 0) := by
  rw [sameSideGroundJump_shiftedGroundState]
  split_ifs with hxR
  · have hΘ := (riemannKernelReal_pos 0).le
    have hm1 := abs_shiftDifference_le a x
    have hc0 : 0 ≤ t - R - a := by linarith
    have hm2 : |shiftDifference a (x + t)| ≤ riemannKernelReal (t - R - a) :=
      (abs_shiftDifference_le_kernel_of_nonneg ha.le (by linarith)).trans
        (riemannKernelReal_antitone_of_nonneg hc0 (by linarith))
    have hsq := sq_abs_sub_le_of_bounded (hMu x) (hMu (x + t))
    have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
    rw [abs_mul, abs_mul, mul_one]
    have hK := (riemannKernelReal_pos (t - R - a)).le
    calc |shiftDifference a x| * |shiftDifference a (x + t)| * |(u x - u (x + t)) ^ 2|
        ≤ riemannKernelReal 0 * riemannKernelReal (t - R - a) * (4 * Mu ^ 2) :=
          mul_le_mul (mul_le_mul hm1 hm2 (abs_nonneg _) hΘ) hsq (abs_nonneg _) (by positivity)
      _ = 4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) := by ring
  · rw [not_le] at hxR
    have h1 : u x = 0 := hsupp x (by rw [abs_of_pos hx0]; exact hxR)
    have h2 : u (x + t) = 0 := hsupp (x + t) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [h1, h2]
    simp

/-- Reflected ground jump: uniformly bounded. -/
theorem reflectedGroundJump_shiftedGroundState_abs_le {a Mu : ℝ} {u : ℝ → ℝ}
    (hMu : ∀ x, |u x| ≤ Mu) (t x : ℝ) :
    |reflectedGroundJump (shiftedGroundState a) u t x| ≤
      4 * riemannKernelReal 0 ^ 2 * Mu ^ 2 := by
  rw [reflectedGroundJump_shiftedGroundState]
  have hΘ := (riemannKernelReal_pos 0).le
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
  have hsq := sq_abs_add_le_of_bounded (hMu x) (hMu (t - x))
  rw [abs_mul, abs_mul]
  calc |shiftDifference a x| * |shiftDifference a (t - x)| * |(u x + u (t - x)) ^ 2|
      ≤ riemannKernelReal 0 * riemannKernelReal 0 * (4 * Mu ^ 2) :=
        mul_le_mul (mul_le_mul (abs_shiftDifference_le a x) (abs_shiftDifference_le a (t - x))
          (abs_nonneg _) hΘ) hsq (abs_nonneg _) (by positivity)
    _ = 4 * riemannKernelReal 0 ^ 2 * Mu ^ 2 := by ring

/-- Reflected ground jump: decay in `t`, supported in `x ≤ R` or `x ≥ t − R`. -/
theorem reflectedGroundJump_shiftedGroundState_abs_le_decay {a R Mu : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hMu : ∀ x, |u x| ≤ Mu)
    {t x : ℝ} (hx0 : 0 < x) (hxt : x < t) (ht : R + a ≤ t) :
    |reflectedGroundJump (shiftedGroundState a) u t x| ≤
      4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) *
        ((if x ≤ R then 1 else 0) + (if t - R ≤ x then 1 else 0)) := by
  rw [reflectedGroundJump_shiftedGroundState]
  have hΘ := (riemannKernelReal_pos 0).le
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
  have hc0 : 0 ≤ t - R - a := by linarith
  have hK := (riemannKernelReal_pos (t - R - a)).le
  have hsq := sq_abs_add_le_of_bounded (hMu x) (hMu (t - x))
  have hbase : 0 ≤ 4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) := by
    positivity
  have hind1 : (0 : ℝ) ≤ if x ≤ R then 1 else 0 := by split_ifs <;> norm_num
  have hind2 : (0 : ℝ) ≤ if t - R ≤ x then 1 else 0 := by split_ifs <;> norm_num
  rw [abs_mul, abs_mul]
  by_cases hxR : x ≤ R
  · have hm2 : |shiftDifference a (t - x)| ≤ riemannKernelReal (t - R - a) :=
      (abs_shiftDifference_le_kernel_of_nonneg ha.le (by linarith)).trans
        (riemannKernelReal_antitone_of_nonneg hc0 (by linarith))
    have hle : |shiftDifference a x| * |shiftDifference a (t - x)| * |(u x + u (t - x)) ^ 2| ≤
        4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) := by
      calc |shiftDifference a x| * |shiftDifference a (t - x)| * |(u x + u (t - x)) ^ 2|
          ≤ riemannKernelReal 0 * riemannKernelReal (t - R - a) * (4 * Mu ^ 2) :=
            mul_le_mul (mul_le_mul (abs_shiftDifference_le a x) hm2 (abs_nonneg _) hΘ) hsq
              (abs_nonneg _) (by positivity)
        _ = 4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) := by ring
    rw [if_pos hxR]
    nlinarith
  · rw [not_le] at hxR
    have hux : u x = 0 := hsupp x (by rw [abs_of_pos hx0]; exact hxR)
    by_cases hxt' : t - R ≤ x
    · have hm1 : |shiftDifference a x| ≤ riemannKernelReal (t - R - a) :=
        (abs_shiftDifference_le_kernel_of_nonneg ha.le hx0.le).trans
          (riemannKernelReal_antitone_of_nonneg hc0 (by linarith))
      have hle : |shiftDifference a x| * |shiftDifference a (t - x)| * |(u x + u (t - x)) ^ 2| ≤
          4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) := by
        calc |shiftDifference a x| * |shiftDifference a (t - x)| * |(u x + u (t - x)) ^ 2|
            ≤ riemannKernelReal (t - R - a) * riemannKernelReal 0 * (4 * Mu ^ 2) :=
              mul_le_mul (mul_le_mul hm1 (abs_shiftDifference_le a (t - x)) (abs_nonneg _) hK) hsq
                (abs_nonneg _) (by positivity)
          _ = 4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) := by ring
      rw [if_neg (not_le.mpr hxR), if_pos hxt']
      linarith
    · rw [not_le] at hxt'
      have hutx : u (t - x) = 0 := hsupp (t - x) (by rw [abs_of_pos (by linarith)]; linarith)
      have hzero : |shiftDifference a x| * |shiftDifference a (t - x)| * |(u x + u (t - x)) ^ 2| = 0 := by
        rw [hux, hutx]
        simp
      rw [hzero]
      exact mul_nonneg hbase (add_nonneg hind1 hind2)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
