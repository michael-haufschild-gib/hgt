/-
The radius–height coupling forced by the window-certificate faces.

The anchor, sphere-sup, and Jensen-quotient faces admit at most one zero of the real
completed carrier inside the anchored window, so the window contains an off-zero closed
subinterval of at least half its length.  On that subinterval the segment-length laws cap
the length by `(π + Borel–Carathéodory budget)/windingFloor`, and every modulus datum the
budget needs is discharged from the certificate's own scalars: the difference-quotient sup
comes from the sphere sup through the maximum principle, and its center value is floored by
the anchor through the linear factorization.  Consequence: the face list forces
`rz·windingFloor(T − rz) ≤ π + (4·rz/(rJ − rz))·(log(M_J/(RJ − rJ) + 1) − log m_J)` —
the admissible anchor radius shrinks like `1/log T`, and a certificate whose radius is out
of scale with its height is refuted by its own faces with no further analytic input.
-/
import GaloisForLFunctions.RHTower.ArgumentVariation
import GaloisForLFunctions.RHTower.AnchorZeroBudget
import GaloisForLFunctions.RHTower.JensenCount
import GaloisForLFunctions.RHTower.CarrierSlope

open Complex Metric

namespace RHTower

/-- An interval carrying at most one zero of `f` contains, for every `ε > 0`, a closed
subinterval of length at least half the interval minus `ε` on which `f` does not vanish:
either `f` has no zero at all, or its unique zero leaves one of the two flanking pieces
with at least half the length. -/
theorem exists_offzero_subinterval {f : ℝ → ℝ} {A B ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (B - A) / 2)
    (hone : ∀ t₁ ∈ Set.Icc A B, ∀ t₂ ∈ Set.Icc A B, t₁ < t₂ →
      f t₁ = 0 → f t₂ = 0 → False) :
    ∃ a b, A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ (B - A) / 2 - ε ≤ b - a ∧
      ∀ τ ∈ Set.Icc a b, f τ ≠ 0 := by
  have hAB : A ≤ B := by linarith
  by_cases hzero : ∃ z ∈ Set.Icc A B, f z = 0
  · obtain ⟨z, hz, hfz⟩ := hzero
    rcases le_total (z - A) (B - z) with hside | hside
    · have hBz : (B - A) / 2 ≤ B - z := by linarith
      refine ⟨z + ε, B, ?_, ?_, le_rfl, ?_, ?_⟩
      · linarith [hz.1]
      · linarith
      · linarith
      · intro τ hτ hfτ
        exact hone z hz τ ⟨by linarith [hτ.1, hz.1], hτ.2⟩ (by linarith [hτ.1]) hfz hfτ
    · have hzA : (B - A) / 2 ≤ z - A := by linarith
      refine ⟨A, z - ε, le_rfl, ?_, ?_, ?_, ?_⟩
      · linarith
      · linarith [hz.2]
      · linarith
      · intro τ hτ hfτ
        exact hone τ ⟨hτ.1, by linarith [hτ.2, hz.2]⟩ z hz (by linarith [hτ.2]) hfτ hfz
  · push Not at hzero
    exact ⟨A, B, le_rfl, hAB, le_rfl, by linarith, fun τ hτ => hzero τ hτ⟩

/-- **The margin form of the radius–height coupling at one anchor height.**  An anchor
floor `m_J` at height `τ₀ ≥ T`, a carrier sup `M_J` on the outer Jensen sphere, and a
Jensen quotient below two force, for every positive margin `ε < rz`,
`(rz − ε)·windingFloor(T − rz) ≤ π + (4·rz/(rJ − rz))·(log(M_J/(RJ − rJ) + 1) − log m_J)`.
Mechanism: the faces admit at most one zero of the real completed carrier on the window
`[τ₀ − rz, τ₀ + rz]`, the off-zero half-window falls under the segment-length laws, and the
Borel–Carathéodory budget is discharged from the faces — the difference-quotient sup by the
maximum principle from the sphere sup, its center value floored by the anchor through the
linear factorization. -/
theorem anchor_window_margin_scale {N : ℕ} {T τ₀ rz rJ RJ m_J M_J ε : ℝ}
    (hrz0 : 0 < rz) (hrzrJ : rz < rJ) (hrJR : rJ < RJ) (hRJ12 : RJ < 1 / 2)
    (hTrz : 0 < T - rz) (hτ₀T : T ≤ τ₀)
    (hwindT : 0 < (Real.log ((T - rz) / (2 * Real.pi)) -
      (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2)
    (hmJ0 : 0 < m_J) (hMJ : 1 ≤ M_J)
    (hanc : m_J ≤ ‖gN N (linePt τ₀)‖)
    (hbnd : ∀ z ∈ sphere (linePt τ₀) RJ, ‖gN N z‖ ≤ M_J)
    (hjensen : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hε0 : 0 < ε) (hεrz : ε < rz) :
    (rz - ε) * ((Real.log ((T - rz) / (2 * Real.pi)) -
        (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2) ≤
      Real.pi + 4 * rz / (rJ - rz) *
        (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) := by
  have hrJ0 : 0 < rJ := lt_trans hrz0 hrzrJ
  have hRJ0 : 0 < RJ := lt_trans hrJ0 hrJR
  have hRJrJ0 : 0 < RJ - rJ := by linarith
  have hMJ0 : (0 : ℝ) < M_J := lt_of_lt_of_le one_pos hMJ
  have hgc0 : 0 < ‖gN N (linePt τ₀)‖ := lt_of_lt_of_le hmJ0 hanc
  have hfc : gN N (linePt τ₀) ≠ 0 := norm_pos_iff.mp hgc0
  -- the closed outer disc sits in the strip
  have hball : ∀ z ∈ closedBall (linePt τ₀) RJ, z.re < 1 := by
    intro z hz
    have h1 : ‖z - linePt τ₀‖ ≤ RJ := by rwa [mem_closedBall, dist_eq_norm] at hz
    have h2 : |(z - linePt τ₀).re| ≤ RJ := le_trans (Complex.abs_re_le_norm _) h1
    have h3 : (z - linePt τ₀).re = z.re - 1 / 2 := by
      rw [Complex.sub_re, linePt_re]
    rw [h3] at h2
    have h4 := abs_le.mp h2
    linarith [h4.2]
  have hgan : AnalyticOnNhd ℂ (gN N) (closedBall (linePt τ₀) RJ) := by
    intro z hz
    exact gN_analyticAt (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [hball z hz]))
  -- maximum principle: the sphere sup bounds the carrier on the closed disc
  have hMball : ∀ z ∈ closedBall (linePt τ₀) RJ, ‖gN N z‖ ≤ M_J := by
    exact norm_le_on_closedBall_of_sphere hRJ0 hgan hbnd
  have hgcM : ‖gN N (linePt τ₀)‖ ≤ M_J :=
    hMball (linePt τ₀) (mem_closedBall_self hRJ0.le)
  -- the Jensen quotient transfers from the floor to the center value
  have hjensen' : Real.log (M_J / ‖gN N (linePt τ₀)‖) / Real.log (RJ / rJ) < 2 := by
    have harg : M_J / ‖gN N (linePt τ₀)‖ ≤ M_J / m_J :=
      div_le_div₀ hMJ0.le le_rfl hmJ0 hanc
    have hlog := Real.log_le_log (by positivity) harg
    have hlogRr : 0 < Real.log (RJ / rJ) :=
      Real.log_pos ((one_lt_div hrJ0).mpr hrJR)
    calc Real.log (M_J / ‖gN N (linePt τ₀)‖) / Real.log (RJ / rJ)
        ≤ Real.log (M_J / m_J) / Real.log (RJ / rJ) := by gcongr
      _ < 2 := hjensen
  have hMdM : M_J ≤ M_J / (RJ - rJ) := by
    rw [le_div_iff₀ hRJrJ0]
    nlinarith
  -- at most one zero of the real completed carrier on the anchored window
  have hone : ∀ t₁ ∈ Set.Icc (τ₀ - rz) (τ₀ + rz), ∀ t₂ ∈ Set.Icc (τ₀ - rz) (τ₀ + rz),
      t₁ < t₂ → (completedGN N (linePt t₁)).re = 0 →
      (completedGN N (linePt t₂)).re = 0 → False := by
    intro t₁ ht₁ t₂ ht₂ hlt hz₁ hz₂
    refine anchor_jensen_faces_false_of_two_sign_brackets (N := N) (τc := τ₀)
      hrJ0 hrJR hball hmJ0 hanc hMJ hbnd hjensen
      (le_refl t₁) hlt (le_refl t₂) ?_ ?_ ?_
    · intro t ht
      rw [mem_closedBall, dist_eq_norm, norm_linePt_sub, abs_le]
      have h1 : τ₀ - rz ≤ t := le_trans ht₁.1 ht.1
      have h2 : t ≤ τ₀ + rz := le_trans ht.2 ht₂.2
      constructor <;> linarith
    · rw [hz₁]
      norm_num
    · rw [hz₂]
      norm_num
  obtain ⟨a, b, hAa, hab, hbB, hlen, hne0⟩ :=
    exists_offzero_subinterval (f := fun τ => (completedGN N (linePt τ)).re)
      (A := τ₀ - rz) (B := τ₀ + rz) hε0 (by linarith) hone
  have hrzlen : rz - ε ≤ b - a := by linarith [hlen]
  -- left endpoint height and its winding floor
  have ha0 : 0 < a := by linarith
  have haT : T - rz ≤ a := by linarith
  have hflra : (Real.log ((T - rz) / (2 * Real.pi)) -
      (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2 ≤
      (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2 :=
    winding_floor_expr_mono hTrz haT
  have hflra0 : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2 :=
    lt_of_lt_of_le hwindT hflra
  -- the off-zero subinterval sits inside the inner Jensen disc
  have hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τ₀) rJ := by
    intro τ hτ
    rw [mem_ball, dist_eq_norm, norm_linePt_sub, abs_lt]
    have h1 : τ₀ - rz ≤ τ := le_trans hAa hτ.1
    have h2 : τ ≤ τ₀ + rz := le_trans hτ.2 hbB
    constructor <;> linarith
  have haτ₀ : |a - τ₀| ≤ rz := by
    rw [abs_le]
    constructor <;> linarith [hAa, hab, hbB]
  have hbτ₀ : |b - τ₀| ≤ rz := by
    rw [abs_le]
    constructor <;> linarith [hAa, hab, hbB]
  -- Borel–Carathéodory prefactors are monotone in the endpoint distance
  have hpre : ∀ x : ℝ, |x| ≤ rz → 2 * |x| / (rJ - |x|) ≤ 2 * rz / (rJ - rz) := by
    intro x hx
    have hx0 : 0 ≤ |x| := abs_nonneg x
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hx hrJ0.le]
  have hprefsum : 2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|) ≤
      4 * rz / (rJ - rz) := by
    have h1 := hpre (a - τ₀) haτ₀
    have h2 := hpre (b - τ₀) hbτ₀
    have h3 : 2 * rz / (rJ - rz) + 2 * rz / (rJ - rz) = 4 * rz / (rJ - rz) := by
      ring
    linarith
  have hprefMax0 : (0 : ℝ) ≤ 4 * rz / (rJ - rz) := by positivity
  by_cases hzf : ∀ z ∈ ball (linePt τ₀) rJ, gN N z ≠ 0
  · -- zero-free disc: the zero-free segment-length law
    have hball' : ∀ z ∈ ball (linePt τ₀) rJ, z.re < 1 := fun z hz =>
      hball z (closedBall_subset_closedBall hrJR.le (ball_subset_closedBall hz))
    have hM' : ∀ z ∈ ball (linePt τ₀) rJ, ‖gN N z‖ ≤ M_J + 1 := by
      intro z hz
      have hzm : z ∈ closedBall (linePt τ₀) RJ :=
        closedBall_subset_closedBall hrJR.le (ball_subset_closedBall hz)
      linarith [hMball z hzm]
    have hlt' : ‖gN N (linePt τ₀)‖ < M_J + 1 := by linarith
    have hlaw := sign_constant_segment_length_le N (τc := τ₀) (R := rJ) (M := M_J + 1)
      hrJ0 ha0 hflra0 hball' hzf hM' hlt' hab hseg hne0
    rw [le_div_iff₀ hflra0] at hlaw
    have hLzf0 : 0 ≤ Real.log (M_J + 1) - Real.log ‖gN N (linePt τ₀)‖ := by
      have := Real.log_le_log hgc0 (by linarith : ‖gN N (linePt τ₀)‖ ≤ M_J + 1)
      linarith
    have hLzf : Real.log (M_J + 1) - Real.log ‖gN N (linePt τ₀)‖ ≤
        Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J := by
      have h1 : Real.log (M_J + 1) ≤ Real.log (M_J / (RJ - rJ) + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      have h2 : Real.log m_J ≤ Real.log ‖gN N (linePt τ₀)‖ :=
        Real.log_le_log hmJ0 hanc
      linarith
    have hX : (2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|)) *
        (Real.log (M_J + 1) - Real.log ‖gN N (linePt τ₀)‖) ≤
        4 * rz / (rJ - rz) * (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) :=
      calc (2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|)) *
          (Real.log (M_J + 1) - Real.log ‖gN N (linePt τ₀)‖)
          ≤ 4 * rz / (rJ - rz) *
            (Real.log (M_J + 1) - Real.log ‖gN N (linePt τ₀)‖) :=
            mul_le_mul_of_nonneg_right hprefsum hLzf0
        _ ≤ 4 * rz / (rJ - rz) *
            (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) :=
            mul_le_mul_of_nonneg_left hLzf hprefMax0
    calc (rz - ε) * ((Real.log ((T - rz) / (2 * Real.pi)) -
          (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2)
        ≤ (b - a) * ((Real.log ((T - rz) / (2 * Real.pi)) -
            (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2) :=
          mul_le_mul_of_nonneg_right hrzlen hwindT.le
      _ ≤ (b - a) * ((Real.log (a / (2 * Real.pi)) -
            (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) :=
          mul_le_mul_of_nonneg_left hflra (by linarith)
      _ ≤ (2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|)) *
            (Real.log (M_J + 1) - Real.log ‖gN N (linePt τ₀)‖) := hlaw
      _ ≤ 4 * rz / (rJ - rz) * (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) := hX
      _ ≤ Real.pi + 4 * rz / (rJ - rz) *
            (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) := by
          linarith [Real.pi_pos]
  · -- one carrier zero in the disc: the one-zero segment-length law
    push Not at hzf
    obtain ⟨ρ', hρ'mem, hρ'z⟩ := hzf
    have hρ'cb : ρ' ∈ closedBall (linePt τ₀) rJ := ball_subset_closedBall hρ'mem
    obtain ⟨hd_an, hd_ne, hfact, _⟩ := gN_one_zero_window_of_jensen hrJ0 hrJR hball
      hfc hMJ hbnd hjensen' hρ'cb hρ'z
    -- difference-quotient sup from the sphere sup
    have hds_sup : ∀ z ∈ closedBall (linePt τ₀) RJ,
        ‖dslope (gN N) ρ' z‖ ≤ M_J / (RJ - rJ) := by
      refine dslope_norm_le_of_boundary_sup (dρ := rJ) hrJ0.le ?_ hrJR hgan hρ'z hbnd
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hρ'cb
    have hMd : ∀ z ∈ ball (linePt τ₀) rJ,
        ‖dslope (gN N) ρ' z‖ ≤ M_J / (RJ - rJ) + 1 := by
      intro z hz
      have hzm : z ∈ closedBall (linePt τ₀) RJ :=
        closedBall_subset_closedBall hrJR.le (ball_subset_closedBall hz)
      linarith [hds_sup z hzm]
    have hltd : ‖dslope (gN N) ρ' (linePt τ₀)‖ < M_J / (RJ - rJ) + 1 := by
      have := hds_sup (linePt τ₀) (mem_closedBall_self hRJ0.le)
      linarith
    -- center difference-quotient floor from the anchor
    have hdsc : m_J / rJ ≤ ‖dslope (gN N) ρ' (linePt τ₀)‖ := by
      have hfc_eq : gN N (linePt τ₀) =
          (linePt τ₀ - ρ') * dslope (gN N) ρ' (linePt τ₀) :=
        hfact (linePt τ₀) (mem_ball_self hrJ0)
      have hdist : ‖linePt τ₀ - ρ'‖ ≤ rJ := by
        rw [norm_sub_rev, ← dist_eq_norm]
        exact mem_closedBall.mp hρ'cb
      have h2 : m_J ≤ ‖dslope (gN N) ρ' (linePt τ₀)‖ * rJ :=
        calc m_J ≤ ‖gN N (linePt τ₀)‖ := hanc
          _ = ‖linePt τ₀ - ρ'‖ * ‖dslope (gN N) ρ' (linePt τ₀)‖ := by
              rw [hfc_eq, norm_mul]
          _ ≤ rJ * ‖dslope (gN N) ρ' (linePt τ₀)‖ :=
              mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
          _ = ‖dslope (gN N) ρ' (linePt τ₀)‖ * rJ := by ring
      rw [div_le_iff₀ hrJ0]
      exact h2
    have hdsc0 : 0 < ‖dslope (gN N) ρ' (linePt τ₀)‖ :=
      lt_of_lt_of_le (by positivity) hdsc
    have hlaw := sign_constant_segment_length_le_one_zero N (τc := τ₀) (R := rJ)
      (Md := M_J / (RJ - rJ) + 1) (ρ' := ρ') hrJ0 ha0 hflra0 hd_an hd_ne hfact
      hMd hltd hab hseg hne0
    rw [le_div_iff₀ hflra0] at hlaw
    have hmJrJ : m_J ≤ m_J / rJ := by
      rw [le_div_iff₀ hrJ0]
      nlinarith
    have hLoz0 : 0 ≤ Real.log (M_J / (RJ - rJ) + 1) -
        Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖ := by
      have := Real.log_le_log hdsc0 hltd.le
      linarith
    have hLoz : Real.log (M_J / (RJ - rJ) + 1) -
        Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖ ≤
        Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J := by
      have h2 : Real.log m_J ≤ Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖ :=
        Real.log_le_log hmJ0 (le_trans hmJrJ hdsc)
      linarith
    have hX : (2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|)) *
        (Real.log (M_J / (RJ - rJ) + 1) -
          Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖) ≤
        4 * rz / (rJ - rz) * (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) :=
      calc (2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|)) *
          (Real.log (M_J / (RJ - rJ) + 1) -
            Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖)
          ≤ 4 * rz / (rJ - rz) *
            (Real.log (M_J / (RJ - rJ) + 1) -
              Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖) :=
            mul_le_mul_of_nonneg_right hprefsum hLoz0
        _ ≤ 4 * rz / (rJ - rz) *
            (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) :=
            mul_le_mul_of_nonneg_left hLoz hprefMax0
    calc (rz - ε) * ((Real.log ((T - rz) / (2 * Real.pi)) -
          (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2)
        ≤ (b - a) * ((Real.log ((T - rz) / (2 * Real.pi)) -
            (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2) :=
          mul_le_mul_of_nonneg_right hrzlen hwindT.le
      _ ≤ (b - a) * ((Real.log (a / (2 * Real.pi)) -
            (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) :=
          mul_le_mul_of_nonneg_left hflra (by linarith)
      _ ≤ Real.pi + (2 * |a - τ₀| / (rJ - |a - τ₀|) + 2 * |b - τ₀| / (rJ - |b - τ₀|)) *
            (Real.log (M_J / (RJ - rJ) + 1) -
              Real.log ‖dslope (gN N) ρ' (linePt τ₀)‖) := hlaw
      _ ≤ Real.pi + 4 * rz / (rJ - rz) *
            (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) := by
          linarith [hX]

end RHTower

namespace RHTower

/-- **The certificate faces force the radius–height coupling.**  Window-certificate data
satisfying the geometry, winding-threshold, anchor, sphere-sup, and Jensen-quotient faces
obey
`rz·windingFloor(T − rz) ≤ π + (4·rz/(rJ − rz))·(log(M_J/(RJ − rJ) + 1) − log m_J)`:
since the winding floor at height `T` grows like `½·log(T/2π)`, the admissible anchor
radius shrinks like `1/log T`, as a theorem about the face list — a certificate whose
radius is out of scale with its height is refuted by its own faces.  The margin form
at the anchor height supplies every positive margin; this eliminates the margin. -/
theorem residual_faces_force_radius_scale {N : ℕ}
    {T U rz rJ RJ m_J M_J : ℝ}
    (hrz0 : 0 < rz) (hrzrJ : rz < rJ) (hrJR : rJ < RJ) (hRJ12 : RJ < 1 / 2)
    (hTrz : 0 < T - rz)
    (hwindT : 0 < (Real.log ((T - rz) / (2 * Real.pi)) -
      (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2)
    (hmJ0 : 0 < m_J) (hMJ : 1 ≤ M_J)
    (hanchor : ∃ τ ∈ Set.Icc T (T + U), m_J ≤ ‖gN N (linePt τ)‖)
    (hbound : ∀ τ ∈ Set.Icc T (T + U),
      ∀ z ∈ sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J)
    (hjensen : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2) :
    rz * ((Real.log ((T - rz) / (2 * Real.pi)) -
        (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2) ≤
      Real.pi + 4 * rz / (rJ - rz) *
        (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) := by
  obtain ⟨τ₀, hτ₀, hanc⟩ := hanchor
  have hbnd : ∀ z ∈ sphere (linePt τ₀) RJ, ‖gN N z‖ ≤ M_J := by
    intro z hz
    exact hbound τ₀ hτ₀ z (by simpa [linePt] using hz)
  set flr : ℝ := (Real.log ((T - rz) / (2 * Real.pi)) -
    (4 / (T - rz) ^ (2 : ℕ) + Real.pi / (T - rz))) / 2 with hflr_def
  set BCB : ℝ := 4 * rz / (rJ - rz) *
    (Real.log (M_J / (RJ - rJ) + 1) - Real.log m_J) with hBCB_def
  by_contra hcon
  push Not at hcon
  have hflr0 : 0 < flr := hwindT
  have hflrne : flr ≠ 0 := hflr0.ne'
  have hδ0 : 0 < rz * flr - (Real.pi + BCB) := by linarith
  obtain ⟨ε, hε0, hεrz, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < rz ∧
      ε * flr ≤ (rz * flr - (Real.pi + BCB)) / 2 := by
    refine ⟨min (rz / 2) ((rz * flr - (Real.pi + BCB)) / (2 * flr)), ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (div_pos hδ0 (by linarith))
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have h1 : min (rz / 2) ((rz * flr - (Real.pi + BCB)) / (2 * flr)) ≤
          (rz * flr - (Real.pi + BCB)) / (2 * flr) := min_le_right _ _
      have h2 : min (rz / 2) ((rz * flr - (Real.pi + BCB)) / (2 * flr)) * flr ≤
          ((rz * flr - (Real.pi + BCB)) / (2 * flr)) * flr :=
        mul_le_mul_of_nonneg_right h1 hflr0.le
      have h3 : ((rz * flr - (Real.pi + BCB)) / (2 * flr)) * flr =
          (rz * flr - (Real.pi + BCB)) / 2 := by
        rw [← div_div, div_mul_cancel₀ _ hflrne]
      linarith
  have hk := anchor_window_margin_scale hrz0 hrzrJ hrJR hRJ12 hTrz hτ₀.1 hwindT
    hmJ0 hMJ hanc hbnd hjensen hε0 hεrz
  rw [← hflr_def, ← hBCB_def] at hk
  have hexp : (rz - ε) * flr = rz * flr - ε * flr := by ring
  rw [hexp] at hk
  linarith

end RHTower
