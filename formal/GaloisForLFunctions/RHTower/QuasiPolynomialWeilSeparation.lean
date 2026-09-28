import GaloisForLFunctions.RHTower.TiltedWeilSpectralSeparation

/-!
# Quasi-polynomial precision for the finite-level Weil form

`TiltedWeilSpectralSeparation` shows that below the Landau horizon an off-line zero at height `t`
forces `μ(a) ≤ -e^{-2εt}/(poly · B_θ²)`, where `θ = π/4 - ε` and
`B_θ = 2^N ∫‖Φ(u + iθ)‖ e^{3N|u|/2}` is the size of the tilted Riemann kernel. This file makes
`B_θ` explicit as `θ → π/4`.

* `norm_tiltedPhi_le_hump`: with `c = cos 2θ`,
  `‖Φ(u + iθ)‖ ≤ (18/c²)(e^{u/2} + (2/(πc)) e^{-3u/2})` for all `u`. Each theta term is bounded by
  `s² e^{-s} ≤ (16/e²) e^{-s/2}` and `s e^{-s} ≤ (2/e) e^{-s/2}` with `s = π c n² e^{2u}`. The
  Gaussian series is then summed geometrically.
* `expTail_tiltedPhi_zero_le`, `log_tiltedSize_le`:
  `log B_θ ≤ N log 2 + log(72U/c³ + 2M) + (3N/2 + 11/2) U` with `U = ½ log((3N/2 + 6)/c)`, so
  `B_θ ≤ (N/c)^{O(N)}`.
* **`weilFloor_quasipolynomial_separation`**: below the Landau horizon, `log(1/η)` is at most
  `2(π/4 - θ) t₀ + O(N log(N/c)) + O(log t₀ (log log t₀ + log 1/δ₀)) + log a`. With
  `ε ≍ (log² t₀ + log t₀ log 1/δ₀)/t₀`, the Landau hypothesis holds for `t₀ ≤ 2π e^{2a-3/4}/(1+κ)`
  (`κ > 0` fixed). There a floor `μ(a) ≥ -exp(-C_κ (log² t + log t log 1/δ))` excludes every off-line
  zero. Reaching `(1 - o(1)) 2π e^{2a-3/4}` needs `ε ≫ log² t/t`, and precision `exp(-ω(log² t))`.
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Mt" => tiltedPhiTailConst

/-! ## Elementary Gaussian bounds -/

/-- `s e^{-s/2} ≤ 2/e`. -/
theorem mul_exp_neg_half_le {s : ℝ} (_hs : 0 ≤ s) : s * Real.exp (-(s / 2)) ≤ 2 / Real.exp 1 := by
  have h := Real.add_one_le_exp (s / 2 - 1)
  have e : Real.exp (s / 2 - 1) = Real.exp (s / 2) / Real.exp 1 := by
    rw [Real.exp_sub]
  rw [e] at h
  have he := Real.exp_pos 1
  have hes := Real.exp_pos (s / 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hes he]
  have : s / 2 ≤ Real.exp (s / 2) / Real.exp 1 := by linarith
  rw [le_div_iff₀ he] at this
  linarith

/-- `s² e^{-s} ≤ (16/e²) e^{-s/2}`. -/
theorem sq_mul_exp_neg_le_exp_half {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * Real.exp (-s) ≤ 16 / Real.exp 1 ^ 2 * Real.exp (-(s / 2)) := by
  have h := mul_exp_neg_half_le (s := s / 2) (by linarith)
  have e1 : Real.exp (-s) = Real.exp (-(s / 2 / 2)) ^ 2 * Real.exp (-(s / 2)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hq : 0 ≤ s / 2 * Real.exp (-(s / 2 / 2)) := by positivity
  have h2 : (s / 2 * Real.exp (-(s / 2 / 2))) ^ 2 ≤ (2 / Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ hq h 2
  rw [e1]
  have he := (Real.exp_pos (-(s / 2))).le
  calc s ^ 2 * (Real.exp (-(s / 2 / 2)) ^ 2 * Real.exp (-(s / 2)))
      = 4 * (s / 2 * Real.exp (-(s / 2 / 2))) ^ 2 * Real.exp (-(s / 2)) := by ring
    _ ≤ 4 * (2 / Real.exp 1) ^ 2 * Real.exp (-(s / 2)) := by gcongr
    _ = 16 / Real.exp 1 ^ 2 * Real.exp (-(s / 2)) := by ring

/-- `s e^{-s} ≤ (2/e) e^{-s/2}`. -/
theorem mul_exp_neg_le_exp_half {s : ℝ} (hs : 0 ≤ s) :
    s * Real.exp (-s) ≤ 2 / Real.exp 1 * Real.exp (-(s / 2)) := by
  have h := mul_exp_neg_half_le hs
  have e1 : Real.exp (-s) = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  have he := (Real.exp_pos (-(s / 2))).le
  calc s * (Real.exp (-(s / 2)) * Real.exp (-(s / 2)))
      = (s * Real.exp (-(s / 2))) * Real.exp (-(s / 2)) := by ring
    _ ≤ 2 / Real.exp 1 * Real.exp (-(s / 2)) := mul_le_mul_of_nonneg_right h he

/-- The Gaussian series is dominated by the geometric one: `Σ_{n ≥ 0} e^{-αn²} ≤ 1 + 1/α`. -/
theorem tsum_exp_neg_mul_sq_le {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => Real.exp (-(α * (n : ℝ) ^ 2))) ∧
      ∑' n : ℕ, Real.exp (-(α * (n : ℝ) ^ 2)) ≤ 1 + 1 / α := by
  set r := Real.exp (-α) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hle : ∀ n : ℕ, Real.exp (-(α * (n : ℝ) ^ 2)) ≤ r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith
  have hs : Summable (fun n : ℕ => Real.exp (-(α * (n : ℝ) ^ 2))) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hgeo
  refine ⟨hs, (hs.tsum_le_tsum hle hgeo).trans ?_⟩
  rw [tsum_geometric_of_lt_one hr0 hr1]
  -- `1/(1 - e^{-α}) ≤ 1 + 1/α` since `e^{-α} ≤ 1/(1+α)`
  have h1 : r ≤ 1 / (1 + α) := by
    rw [hr, Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp α])
  have h2 : α / (1 + α) ≤ 1 - r := by
    have : 1 / (1 + α) = 1 - α / (1 + α) := by field_simp; ring
    linarith
  have h3 : 0 < α / (1 + α) := by positivity
  calc (1 - r)⁻¹ ≤ (α / (1 + α))⁻¹ := inv_anti₀ h3 h2
    _ = 1 + 1 / α := by field_simp; ring

/-! ## The hump of the tilted kernel -/

/-- **Uniform bound on the tilted kernel.** With `c = cos 2θ`,
`‖Φ(u + iθ)‖ ≤ (18/c²)(e^{u/2} + (2/(πc)) e^{-3u/2})` for every real `u`. -/
theorem norm_tiltedPhi_le_hump {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (u : ℝ) :
    ‖tiltedPhi θ u‖ ≤ 18 / Real.cos (2 * θ) ^ 2 *
      (Real.exp (u / 2) + 2 / (π * Real.cos (2 * θ)) * Real.exp (-(3 / 2 * u))) := by
  obtain ⟨c, hcdef⟩ : ∃ x, x = Real.cos (2 * θ) := ⟨_, rfl⟩
  rw [← hcdef]
  have hc : 0 < c := by rw [hcdef]; exact cos_two_mul_pos_of_tilt hθ0 hθ
  have hc1 : c ≤ 1 := by rw [hcdef]; exact Real.cos_le_one _
  set z : ℂ := (u : ℂ) + (θ : ℂ) * I with hz
  have hzre : z.re = u := by simp [hz]
  have hzim : |z.im| ≤ θ := by simp [hz, abs_of_nonneg hθ0]
  set x := Real.exp (2 * u) with hx
  have hx0 : 0 < x := Real.exp_pos _
  set α := π * c * x / 2 with hα
  have hα0 : 0 < α := by rw [hα]; have := Real.pi_pos; positivity
  obtain ⟨hs, hsum⟩ := tsum_exp_neg_mul_sq_le hα0
  set K := 18 / c ^ 2 * Real.exp (u / 2) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hterm : ∀ n : ℕ, ‖thetaCuspComplexTerm z n‖ ≤ K * Real.exp (-(α * (n : ℝ) ^ 2)) := by
    intro n
    have h := norm_thetaCuspComplexTerm_le_pointwise hθ.le hzim n
    rw [hzre, ← hcdef] at h
    set s := π * c * (n : ℝ) ^ 2 * x with hsdef
    have hs0 : 0 ≤ s := by rw [hsdef]; have := Real.pi_pos; positivity
    have hpc : 0 < π * c := mul_pos Real.pi_pos hc
    have e4 : (n : ℝ) ^ 4 * Real.exp (4 * u) = s ^ 2 / (π * c) ^ 2 := by
      rw [hsdef, hx, show Real.exp (4 * u) = Real.exp (2 * u) ^ 2 by
        rw [sq, ← Real.exp_add]; ring_nf]
      field_simp
    have e2 : (n : ℝ) ^ 2 * Real.exp (2 * u) = s / (π * c) := by
      rw [hsdef, hx]; field_simp
    have eg : Real.exp (-(π * c) * (n : ℝ) ^ 2 * Real.exp (2 * u)) = Real.exp (-s) := by
      rw [hsdef, hx]; congr 1; ring
    have eα : α * (n : ℝ) ^ 2 = s / 2 := by rw [hα, hsdef]; ring
    rw [eα]
    have hb1 := sq_mul_exp_neg_le_exp_half hs0
    have hb2 := mul_exp_neg_le_exp_half hs0
    have he1 : 16 / Real.exp 1 ^ 2 ≤ 3 := by
      have := Real.exp_one_gt_d9
      have h2 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
        pow_le_pow_left₀ (by norm_num) this.le 2
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have he2 : 2 / Real.exp 1 ≤ 1 := by
      have := Real.add_one_le_exp 1
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    have hE := (Real.exp_pos (-(s / 2))).le
    have hpi : (3 : ℝ) < π := Real.pi_gt_three
    calc ‖thetaCuspComplexTerm z n‖
        ≤ Real.exp (u / 2) * (2 * π) *
            (2 * π * (n : ℝ) ^ 4 * Real.exp (4 * u) + 3 * (n : ℝ) ^ 2 * Real.exp (2 * u)) *
            Real.exp (-(π * c) * (n : ℝ) ^ 2 * Real.exp (2 * u)) := h
      _ = Real.exp (u / 2) * (2 * π) *
            (2 * π * (s ^ 2 * Real.exp (-s)) / (π * c) ^ 2 +
              3 * (s * Real.exp (-s)) / (π * c)) := by
          rw [show 2 * π * (n : ℝ) ^ 4 * Real.exp (4 * u) =
              2 * π * ((n : ℝ) ^ 4 * Real.exp (4 * u)) by ring,
            show 3 * (n : ℝ) ^ 2 * Real.exp (2 * u) = 3 * ((n : ℝ) ^ 2 * Real.exp (2 * u)) by ring,
            e4, e2, eg]
          field_simp
      _ ≤ Real.exp (u / 2) * (2 * π) *
            (2 * π * (3 * Real.exp (-(s / 2))) / (π * c) ^ 2 +
              3 * (1 * Real.exp (-(s / 2))) / (π * c)) := by
          have hb1' : s ^ 2 * Real.exp (-s) ≤ 3 * Real.exp (-(s / 2)) :=
            hb1.trans (mul_le_mul_of_nonneg_right he1 hE)
          have hb2' : s * Real.exp (-s) ≤ 1 * Real.exp (-(s / 2)) :=
            hb2.trans (mul_le_mul_of_nonneg_right he2 hE)
          gcongr
      _ = (12 / c ^ 2 + 6 / c) * Real.exp (u / 2) * Real.exp (-(s / 2)) := by
          field_simp; ring
      _ ≤ 18 / c ^ 2 * Real.exp (u / 2) * Real.exp (-(s / 2)) := by
          apply mul_le_mul_of_nonneg_right _ hE
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have h6 : 6 / c ≤ 6 / c ^ 2 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith
          have h18 : 12 / c ^ 2 + 6 / c ^ 2 = 18 / c ^ 2 := by ring
          linarith
      _ = K * Real.exp (-(s / 2)) := by rw [hK]
  have hsumK : Summable (fun n : ℕ => K * Real.exp (-(α * (n : ℝ) ^ 2))) := hs.mul_left K
  have hnorm : Summable (fun n : ℕ => ‖thetaCuspComplexTerm z n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumK
  have hΦ : tiltedPhi θ u = ∑' n : ℕ, thetaCuspComplexTerm z n := rfl
  rw [hΦ]
  calc ‖∑' n : ℕ, thetaCuspComplexTerm z n‖ ≤ ∑' n : ℕ, ‖thetaCuspComplexTerm z n‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, K * Real.exp (-(α * (n : ℝ) ^ 2)) := hnorm.tsum_le_tsum hterm hsumK
    _ = K * ∑' n : ℕ, Real.exp (-(α * (n : ℝ) ^ 2)) := tsum_mul_left
    _ ≤ K * (1 + 1 / α) := mul_le_mul_of_nonneg_left hsum hK0
    _ = 18 / c ^ 2 * (Real.exp (u / 2) + 2 / (π * c) * Real.exp (-(3 / 2 * u))) := by
        rw [hK, hα, hx]
        have e : Real.exp (-(3 / 2 * u)) = Real.exp (u / 2) / Real.exp (2 * u) := by
          rw [← Real.exp_sub]; ring_nf
        rw [e]
        have := Real.pi_pos
        have hx' := Real.exp_pos (2 * u)
        field_simp
        try ring

/-- On `|u| < U`: `‖Φ(u + iθ)‖ e^{c'|u|} ≤ (36/c³) e^{(c' + 3/2)U}`. -/
theorem norm_tiltedPhi_mul_exp_le_of_abs_lt {θ c' U u : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hc' : 0 ≤ c') (hu : |u| < U) :
    ‖tiltedPhi θ u‖ * Real.exp (c' * |u|) ≤
      36 / Real.cos (2 * θ) ^ 3 * Real.exp ((c' + 3 / 2) * U) := by
  have h := norm_tiltedPhi_le_hump hθ0 hθ u
  obtain ⟨c, hcdef⟩ : ∃ x, x = Real.cos (2 * θ) := ⟨_, rfl⟩
  rw [← hcdef] at h ⊢
  have hc : 0 < c := by rw [hcdef]; exact cos_two_mul_pos_of_tilt hθ0 hθ
  have hc1 : c ≤ 1 := by rw [hcdef]; exact Real.cos_le_one _
  have hU : 0 ≤ U := (abs_nonneg u).trans hu.le
  have h1 : Real.exp (u / 2) ≤ Real.exp (3 / 2 * U) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self u])
  have h2 : Real.exp (-(3 / 2 * u)) ≤ Real.exp (3 / 2 * U) :=
    Real.exp_le_exp.mpr (by linarith [neg_abs_le u])
  have h3 : 2 / (π * c) ≤ 1 / c := by
    rw [div_le_div_iff₀ (by positivity) hc]; nlinarith [Real.pi_gt_three]
  have hsum : Real.exp (u / 2) + 2 / (π * c) * Real.exp (-(3 / 2 * u)) ≤
      2 / c * Real.exp (3 / 2 * U) := by
    have h4 : 2 / (π * c) * Real.exp (-(3 / 2 * u)) ≤ 1 / c * Real.exp (3 / 2 * U) :=
      mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
    have h5 : Real.exp (3 / 2 * U) ≤ 1 / c * Real.exp (3 / 2 * U) := by
      apply le_mul_of_one_le_left (Real.exp_pos _).le
      rw [le_div_iff₀ hc]; linarith
    have e : 2 / c * Real.exp (3 / 2 * U) = 1 / c * Real.exp (3 / 2 * U) + 1 / c * Real.exp (3 / 2 * U) := by
      ring
    linarith
  have hcu : Real.exp (c' * |u|) ≤ Real.exp (c' * U) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.le hc')
  have hn := norm_nonneg (tiltedPhi θ u)
  calc ‖tiltedPhi θ u‖ * Real.exp (c' * |u|)
      ≤ (18 / c ^ 2 * (2 / c * Real.exp (3 / 2 * U))) * Real.exp (c' * U) := by
        apply mul_le_mul (h.trans (mul_le_mul_of_nonneg_left hsum (by positivity))) hcu
          (Real.exp_pos _).le (by positivity)
    _ = 36 / c ^ 3 * Real.exp ((c' + 3 / 2) * U) := by
        rw [show (c' + 3 / 2) * U = 3 / 2 * U + c' * U by ring, Real.exp_add]
        field_simp; ring

/-- **The size of the tilted kernel, explicitly.** With `c = cos 2θ`, for `c' ≥ 0` and `U ≥ 0`
with `c' + 11/2 ≤ 2π c e^{2U}`:
`∫ ‖Φ(u + iθ)‖ e^{c'|u|} ≤ (72 U/c³) e^{(c' + 3/2)U} + 2M e^{(c' + 11/2)U} e^{-π c e^{2U}}`. -/
theorem expTail_tiltedPhi_zero_le {θ c' U : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (hc' : 0 ≤ c')
    (hU : 0 ≤ U) (hrate : c' + 11 / 2 ≤ 2 * π * Real.cos (2 * θ) * Real.exp (2 * U)) :
    expTail (tiltedPhi θ) c' 0 ≤
      72 * U / Real.cos (2 * θ) ^ 3 * Real.exp ((c' + 3 / 2) * U) +
        2 * Mt * Real.exp ((c' + 11 / 2) * U) *
          Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * U))) := by
  have hg := superExpDecay_tiltedPhi hθ0 hθ
  set F : ℝ → ℝ := fun u => ‖tiltedPhi θ u‖ * Real.exp (c' * |u|) with hF
  have hFi : Integrable F := hg.2 c'
  set S : Set ℝ := {u : ℝ | U ≤ |u|} with hS
  have hSm : MeasurableSet S := measurableSet_absGe U
  have h0 : expTail (tiltedPhi θ) c' 0 = ∫ u, F u := by
    unfold expTail; congr 1; funext u; simp [indicator, hF]
  have hsplit : (∫ u in S, F u) + (∫ u in Sᶜ, F u) = ∫ u, F u := integral_add_compl hSm hFi
  have htail : (∫ u in S, F u) = expTail (tiltedPhi θ) c' U := by
    unfold expTail; rw [integral_indicator hSm]
  have hT := expTail_tiltedPhi_le hθ0 hθ hc' hrate
  have hcomp : Sᶜ = Set.Ioo (-U) U := by
    ext u; simp [hS, abs_lt]
  set C0 := 36 / Real.cos (2 * θ) ^ 3 * Real.exp ((c' + 3 / 2) * U) with hC0
  have hC00 : 0 ≤ C0 := by
    have := cos_two_mul_pos_of_tilt hθ0 hθ; rw [hC0]; positivity
  have hhump : (∫ u in Sᶜ, F u) ≤ ∫ u in Sᶜ, C0 := by
    refine setIntegral_mono_on hFi.integrableOn ?_ hSm.compl fun u hu => ?_
    · rw [hcomp]; exact integrableOn_const (by simp) (by simp)
    · have hu' : |u| < U := by
        have : u ∉ S := hu
        simp only [hS, mem_setOf_eq, not_le] at this; exact this
      exact norm_tiltedPhi_mul_exp_le_of_abs_lt hθ0 hθ hc' hu'
  have hvol : (∫ u in Sᶜ, C0) = 2 * U * C0 := by
    rw [setIntegral_const, hcomp, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [h0, ← hsplit, htail]
  have e : 2 * U * C0 = 72 * U / Real.cos (2 * θ) ^ 3 * Real.exp ((c' + 3 / 2) * U) := by
    rw [hC0]; ring
  linarith [hhump, hvol, hT]

/-- **Logarithmic size of `B_θ`.** For `N ≥ 0` and `c = cos 2θ`, with `U = ½ log((3N/2 + 6)/c)`:
`log(2^N ∫‖Φ_θ‖ e^{3N|u|/2}) ≤ N log 2 + log(72U/c³ + 2M) + (3N/2 + 11/2) U`, provided the
integral is positive. Since `U = O(log N + log 1/c)`, `B_θ ≤ (N/c)^{O(N)}`. -/
theorem log_tiltedSize_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (N : ℕ)
    (hpos : 0 < expTail (tiltedPhi θ) (3 / 2 * N) 0) :
    Real.log (2 ^ N * expTail (tiltedPhi θ) (3 / 2 * N) 0) ≤
      N * Real.log 2 +
        Real.log (72 * (1 / 2 * Real.log ((3 / 2 * N + 6) / Real.cos (2 * θ))) /
          Real.cos (2 * θ) ^ 3 + 2 * Mt) +
        (3 / 2 * N + 11 / 2) * (1 / 2 * Real.log ((3 / 2 * N + 6) / Real.cos (2 * θ))) := by
  have hc := cos_two_mul_pos_of_tilt hθ0 hθ
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one _
  set c := Real.cos (2 * θ) with hcdef
  set U := 1 / 2 * Real.log ((3 / 2 * N + 6) / c) with hU
  have hQ : 1 ≤ (3 / 2 * N + 6) / c := by
    rw [le_div_iff₀ hc]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
  have hU0 : 0 ≤ U := by rw [hU]; have := Real.log_nonneg hQ; linarith
  have he2U : Real.exp (2 * U) = (3 / 2 * N + 6) / c := by
    rw [hU, show 2 * (1 / 2 * Real.log ((3 / 2 * N + 6) / c)) = Real.log ((3 / 2 * N + 6) / c) by
      ring, Real.exp_log (by linarith)]
  have hrate : 3 / 2 * (N : ℝ) + 11 / 2 ≤ 2 * π * c * Real.exp (2 * U) := by
    rw [he2U]
    have : 2 * π * c * ((3 / 2 * N + 6) / c) = 2 * π * (3 / 2 * N + 6) := by field_simp
    rw [this]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [Real.pi_gt_three]
  have hb := expTail_tiltedPhi_zero_le hθ0 hθ (c' := 3 / 2 * N) (by positivity) hU0 hrate
  have hM := tiltedPhiTailConst_nonneg
  have hle : expTail (tiltedPhi θ) (3 / 2 * N) 0 ≤
      (72 * U / c ^ 3 + 2 * Mt) * Real.exp ((3 / 2 * N + 11 / 2) * U) := by
    refine hb.trans ?_
    have h1 : Real.exp ((3 / 2 * N + 3 / 2) * U) ≤ Real.exp ((3 / 2 * N + 11 / 2) * U) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(π * c * Real.exp (2 * U))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := Real.exp_pos (2 * U); nlinarith [Real.pi_pos])
    have hA : 0 ≤ 72 * U / c ^ 3 := by positivity
    have hE := (Real.exp_pos ((3 / 2 * N + 11 / 2) * U)).le
    calc 72 * U / c ^ 3 * Real.exp ((3 / 2 * N + 3 / 2) * U) +
          2 * Mt * Real.exp ((3 / 2 * N + 11 / 2) * U) * Real.exp (-(π * c * Real.exp (2 * U)))
        ≤ 72 * U / c ^ 3 * Real.exp ((3 / 2 * N + 11 / 2) * U) +
          2 * Mt * Real.exp ((3 / 2 * N + 11 / 2) * U) * 1 := by gcongr
      _ = _ := by ring
  have hMpos : 0 < Mt := by
    unfold tiltedPhiTailConst
    have hs : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2)) :=
      summable_pow_mul_exp_neg_nat_sq 4 (by norm_num : (0 : ℝ) < 1)
    have h1 : (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2)) 1 ≤
        ∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2) :=
      hs.le_tsum 1 (fun j _ => by positivity)
    have h1' : 0 < (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2)) 1 := by
      simp only [Nat.cast_one, one_pow, one_mul]; exact Real.exp_pos _
    have := Real.pi_pos
    have := Real.exp_pos 1
    have : 0 < ∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2) := lt_of_lt_of_le h1' h1
    positivity
  have hA : 0 < 72 * U / c ^ 3 + 2 * Mt := by
    have : 0 ≤ 72 * U / c ^ 3 := by positivity
    linarith
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [Real.log_mul (by positivity) hpos.ne', Real.log_pow]
  linarith

/-- **Quasi-polynomial spectral separation.** There are absolute constants `K₀, K₁` such that, for
every tilt `0 ≤ θ < π/4` (`c = cos 2θ`), if the bottom of the level-`a` Weil form is at least `-η`
with `η > 0` (`a ≥ 1`), then every zero `ρ₀ = β₀ + it₀` with `β₀ > ½`, `t₀ ≥ 101`,
`6 + 3N/2 ≤ 2π c e^{2X}` and below the Landau horizon (`2K₀ P² ≤ e^{2θ(t₀ - 3/4)}`, `P` as in
`weilFloor_tilted_spectral_separation`) satisfies

`log(1/η) ≤ 2(π/4 - θ) t₀ + π/2 + 3θ/2 + 2L_N + 2 log(N+1) + 4 log(t₀+3)
  + 2(N log 2 + log(72U/c³ + 2M) + (3N/2 + 11/2) U) + log(2K₁ a)`,

where `U = ½ log((3N/2 + 6)/c)`. With `θ = π/4 - ε`, `c = sin 2ε`, and
`ε ≍ log t₀ (log log t₀ + log 1/δ₀)/t₀`, every term on the right is
`O(log² t₀ + log t₀ log 1/δ₀)`. That choice of `ε` meets the Landau hypothesis for
`t₀ ≤ 2π e^{2a-3/4}/(1+κ)` with `κ > 0` fixed; there, a floor
`μ(a) ≥ -exp(-C_κ (log² t + log t log 1/δ))` excludes off-line zeros up to height `t`. -/
theorem weilFloor_quasipolynomial_separation :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {θ a η : ℝ}, 0 ≤ θ → 2 * θ < π / 2 → 1 ≤ a → 0 < η →
      WeilFloorAtLevel zetaZeroConfig a η →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        6 + 3 / 2 * (windowCount ρ₀.im : ℝ) ≤
          2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) →
        2 * K₀ * (2 ^ windowCount ρ₀.im * ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) *
            (ρ₀.im + 3) ^ 2 * (Real.exp ((6 + 3 / 2 * windowCount ρ₀.im) * (a - 3 / 8)) *
              Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))))) ^ 2 ≤
          Real.exp (2 * θ * (ρ₀.im - 3 / 4)) →
        Real.log (1 / η) ≤ 2 * (π / 4 - θ) * ρ₀.im + (π / 2 + 3 / 2 * θ) +
          2 * (Real.log 32 + windowCount ρ₀.im * Real.log 3 +
            windowCount ρ₀.im * Real.log (32 * (windowCount ρ₀.im + 1 : ℝ)) +
            2 * windowCount ρ₀.im * Real.log (16 * Real.exp 1 / (ρ₀.re - 1 / 2)) +
            (2 + windowCount ρ₀.im * Real.log 5 + 3 * (windowLogConst * Real.log ρ₀.im)) -
            Real.log (ρ₀.re - 1 / 2)) +
          2 * Real.log (windowCount ρ₀.im + 1) + 4 * Real.log (ρ₀.im + 3) +
          2 * (windowCount ρ₀.im * Real.log 2 +
            Real.log (72 * (1 / 2 * Real.log ((3 / 2 * windowCount ρ₀.im + 6) /
              Real.cos (2 * θ))) / Real.cos (2 * θ) ^ 3 + 2 * Mt) +
            (3 / 2 * windowCount ρ₀.im + 11 / 2) *
              (1 / 2 * Real.log ((3 / 2 * windowCount ρ₀.im + 6) / Real.cos (2 * θ)))) +
          Real.log (2 * K₁ * a) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hprod⟩ := weilFloor_excludes_tilted_cluster
  obtain ⟨K₀', K₁', hK₀', hK₁', hlogf⟩ := weilFloor_tilted_spectral_separation
  refine ⟨max K₀ K₀', max K₁ K₁', lt_max_of_lt_left hK₀, lt_max_of_lt_left hK₁, ?_⟩
  intro θ a η hθ0 hθ ha hη hH ρ₀ hρ₀ hβ ht hlam hland
  set W := windowCount ρ₀.im with hW
  obtain ⟨P, hP⟩ : ∃ x, x = 2 ^ W * ((W + 1 : ℝ) *
      ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) W) * (ρ₀.im + 3) ^ 2 *
      (Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))))) := ⟨_, rfl⟩
  rw [← hP] at hland
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg _
  have hland0 : 2 * K₀ * P ^ 2 ≤ Real.exp (2 * θ * (ρ₀.im - 3 / 4)) :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left K₀ K₀']) hP2) hland
  have hland1 : 2 * K₀' * P ^ 2 ≤ Real.exp (2 * θ * (ρ₀.im - 3 / 4)) :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith [le_max_right K₀ K₀']) hP2) hland
  have hpos : 0 < expTail (tiltedPhi θ) (3 / 2 * W) 0 := by
    rcases (expTail_nonneg (tiltedPhi θ) (3 / 2 * W) 0).lt_or_eq with hb | hb
    · exact hb
    · exfalso
      have hm := hprod hθ0 hθ ha hη.le hH hρ₀ hβ ht hlam
      rw [← hW, ← hP, ← hb] at hm
      simp only [mul_zero, zero_pow two_ne_zero, add_zero] at hm
      have hA := Real.exp_pos (2 * θ * (ρ₀.im - 3 / 4))
      nlinarith
  have hl := hlogf hθ0 hθ ha hη hH hρ₀ hβ ht hlam (by rw [← hW, ← hP]; exact hland1) hpos
  have hs := log_tiltedSize_le hθ0 hθ W hpos
  have hK : Real.log (2 * K₁' * a) ≤ Real.log (2 * max K₁ K₁' * a) := by
    apply Real.log_le_log (by positivity)
    have : K₁' ≤ max K₁ K₁' := le_max_right _ _
    have : (0 : ℝ) < a := by linarith
    nlinarith
  linarith

end

end RHTower
