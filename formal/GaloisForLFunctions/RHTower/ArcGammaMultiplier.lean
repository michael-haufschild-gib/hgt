import GaloisForLFunctions.RHTower.ShiftedGammaSpectralIdentity
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay

/-!
# The arc multiplier `R(s) = Σ_j w_j Q_j(z) Q_j(−z)`

For nonnegative weights `w_j` with `S = Σ_j w_j (j! (3/2)^j)² < ∞` put, with `z = −i(s − ½)`,

`R(s) = Σ_j w_j Q_j(z) Q_j(−z)`   (`arcGammaMultiplier`).

* `‖R(s)‖ ≤ 9 S 3^{|Im s|}` on `|Re s − ½| ≤ 3/2` (`norm_arcGammaMultiplier_le`), from
  `‖Q_j(z)‖ ≤ 3 j!(3/2)^j 3^{|Re z|/2}`; hence `R` is holomorphic on `|Re s − ½| < 3/2`
  (`differentiableAt_arcGammaMultiplier`).
* `ξ(s)² R(s) = Σ_j w_j Φ_j(z) Φ_j(−z)` with `Φ_j = Ξ·Q_j`, so on `½ ≤ Re s ≤ 5/4`
  `‖ξ(s)² R(s)‖ ≤ C/(1 + (Im s)²)` (`exists_norm_xi_sq_mul_arcGammaMultiplier_le`).
* `‖G(s)² R(s)‖ ≤ C'/(1 + (Im s)²)` on the same strip (`exists_norm_archXi_sq_mul_arcGammaMultiplier_le`),
  because `|G(s)|²` decays like `e^{−π|Im s|/2}` and `π/2 > log 3`.
* On the critical line `R(½ + iτ) = Σ_j w_j |Q_j(τ)|²` (`arcGammaMultiplier_criticalLine`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

/-- `R(s) = Σ_j w_j Q_j(z) Q_j(−z)` with `z = −i(s − ½)`. -/
def arcGammaMultiplier (w : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' j, (w j : ℂ) * (shiftedGammaPoly j (-I * (s - 1 / 2)) * shiftedGammaPoly j (I * (s - 1 / 2)))

theorem im_neg_I_mul_sub_half (s : ℂ) : (-I * (s - 1 / 2)).im = -(s.re - 1 / 2) := by simp
theorem re_neg_I_mul_sub_half (s : ℂ) : (-I * (s - 1 / 2)).re = s.im := by simp
theorem im_I_mul_sub_half (s : ℂ) : (I * (s - 1 / 2)).im = s.re - 1 / 2 := by simp
theorem re_I_mul_sub_half (s : ℂ) : (I * (s - 1 / 2)).re = -s.im := by simp

/-- The term bound `‖w_j Q_j(z) Q_j(−z)‖ ≤ 9 w_j (j!(3/2)^j)² 3^{|Im s|}`. -/
theorem norm_arcGammaMultiplier_term_le {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (j : ℕ) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ 3 / 2) :
    ‖(w j : ℂ) * (shiftedGammaPoly j (-I * (s - 1 / 2)) * shiftedGammaPoly j (I * (s - 1 / 2)))‖ ≤
      9 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) * Real.exp (Real.log 3 * |s.im|) := by
  have h1 := norm_shiftedGammaPoly_le_factorial j (z := -I * (s - 1 / 2))
    (by rw [im_neg_I_mul_sub_half, abs_neg]; exact hs)
  have h2 := norm_shiftedGammaPoly_le_factorial j (z := I * (s - 1 / 2))
    (by rw [im_I_mul_sub_half]; exact hs)
  rw [re_neg_I_mul_sub_half] at h1
  rw [re_I_mul_sub_half, abs_neg] at h2
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
  have hJ : 0 ≤ (j ! : ℝ) * (3 / 2 : ℝ) ^ j := by positivity
  have he : Real.exp (Real.log 3 / 2 * |s.im|) * Real.exp (Real.log 3 / 2 * |s.im|) =
      Real.exp (Real.log 3 * |s.im|) := by rw [← Real.exp_add]; ring_nf
  calc w j * (‖shiftedGammaPoly j (-I * (s - 1 / 2))‖ * ‖shiftedGammaPoly j (I * (s - 1 / 2))‖) ≤
      w j * ((3 * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (Real.log 3 / 2 * |s.im|)) *
        (3 * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (Real.log 3 / 2 * |s.im|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (hw j)
    _ = 9 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) *
        (Real.exp (Real.log 3 / 2 * |s.im|) * Real.exp (Real.log 3 / 2 * |s.im|)) := by ring
    _ = _ := by rw [he]

theorem summable_norm_arcGammaMultiplier_term {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ 3 / 2) :
    Summable fun j => ‖(w j : ℂ) *
      (shiftedGammaPoly j (-I * (s - 1 / 2)) * shiftedGammaPoly j (I * (s - 1 / 2)))‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_arcGammaMultiplier_term_le hw j hs)
    ((hsum.mul_left 9).mul_right _)

/-- `‖R(s)‖ ≤ 9 S 3^{|Im s|}`. -/
theorem norm_arcGammaMultiplier_le {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ 3 / 2) :
    ‖arcGammaMultiplier w s‖ ≤
      9 * (∑' j, w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) * Real.exp (Real.log 3 * |s.im|) := by
  unfold arcGammaMultiplier
  refine (norm_tsum_le_tsum_norm (summable_norm_arcGammaMultiplier_term hw hsum hs)).trans ?_
  refine (Summable.tsum_le_tsum (fun j => norm_arcGammaMultiplier_term_le hw j hs)
    (summable_norm_arcGammaMultiplier_term hw hsum hs) ((hsum.mul_left 9).mul_right _)).trans
    (le_of_eq ?_)
  rw [tsum_mul_right, tsum_mul_left]

/-- **Holomorphy of the arc multiplier** on `|Re s − ½| < 3/2`. -/
theorem differentiableAt_arcGammaMultiplier {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) {s₀ : ℂ}
    (hs₀ : |s₀.re - 1 / 2| < 3 / 2) : DifferentiableAt ℂ (arcGammaMultiplier w) s₀ := by
  set T : ℝ := |s₀.im| + 1
  set U : Set ℂ := {s | |s.re - 1 / 2| < 3 / 2 ∧ |s.im| < T} with hU
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
      continuous_const).inter (isOpen_lt (continuous_abs.comp Complex.continuous_im)
      continuous_const)
  have hs₀U : s₀ ∈ U := ⟨hs₀, by simp [T]⟩
  have hdiff : DifferentiableOn ℂ (arcGammaMultiplier w) U := by
    unfold arcGammaMultiplier
    refine differentiableOn_tsum_of_summable_norm
      ((hsum.mul_left 9).mul_right (Real.exp (Real.log 3 * T))) (fun j => ?_) hUo
      (fun j s hs => ?_)
    · unfold shiftedGammaPoly
      intro s _
      fun_prop
    · refine (norm_arcGammaMultiplier_term_le hw j hs.1.le).trans ?_
      have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have he : Real.exp (Real.log 3 * |s.im|) ≤ Real.exp (Real.log 3 * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2.le hl)
      have h0 : 0 ≤ 9 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) := by
        have := hw j; positivity
      exact mul_le_mul_of_nonneg_left he h0
  exact hdiff.differentiableAt (hUo.mem_nhds hs₀U)

/-! ### Decay on the strip -/

/-- `e^{−a|t|} ≤ (1 + 2/a²)/(1 + t²)` for `a > 0`. -/
theorem exp_neg_mul_abs_le_inv_one_add_sq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Real.exp (-(a * |t|)) ≤ (1 + 2 / a ^ 2) / (1 + t ^ 2) := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := a * |t|) (by positivity)
  have hE : 0 < Real.exp (a * |t|) := Real.exp_pos _
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hE (by positivity), one_mul]
  have ht : (a * |t|) ^ 2 = a ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
  have h2 : (1 + 2 / a ^ 2) * (1 + (a * |t|) ^ 2 / 2) ≥ 1 + t ^ 2 := by
    rw [ht]
    have ha2 : 0 < a ^ 2 := by positivity
    have e : (1 + 2 / a ^ 2) * (1 + a ^ 2 * t ^ 2 / 2) = 1 + t ^ 2 + a ^ 2 * t ^ 2 / 2 + 2 / a ^ 2 := by
      field_simp; ring
    rw [e]
    have : 0 ≤ a ^ 2 * t ^ 2 / 2 := by positivity
    have : 0 ≤ 2 / a ^ 2 := by positivity
    linarith
  have h3 : 1 + (a * |t|) ^ 2 / 2 ≤ Real.exp (a * |t|) := by
    nlinarith [abs_nonneg t, mul_nonneg ha.le (abs_nonneg t)]
  calc 1 + t ^ 2 ≤ (1 + 2 / a ^ 2) * (1 + (a * |t|) ^ 2 / 2) := h2
    _ ≤ (1 + 2 / a ^ 2) * Real.exp (a * |t|) := by gcongr

/-- `ξ(s)² R(s) = Σ_j w_j Φ_j(z) Φ_j(−z)`, `z = −i(s − ½)`. -/
theorem xi_sq_mul_arcGammaMultiplier (w : ℕ → ℝ) (s : ℂ) :
    RHTower.xi s ^ 2 * arcGammaMultiplier w s =
      ∑' j, (w j : ℂ) * (xiShiftedGamma j (-I * (s - 1 / 2)) * xiShiftedGamma j (I * (s - 1 / 2))) := by
  have hX : RHTower.XiC (-I * (s - 1 / 2)) = RHTower.xi s := by
    unfold RHTower.XiC
    congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  have hX' : RHTower.XiC (I * (s - 1 / 2)) = RHTower.xi s := by
    rw [show I * (s - 1 / 2) = -(-I * (s - 1 / 2)) by ring, RHTower.XiC_even, hX]
  unfold arcGammaMultiplier xiShiftedGamma
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [hX, hX']
  ring

/-- **Quadratic decay of `ξ² R`** on `½ ≤ Re s ≤ 5/4`. -/
theorem exists_norm_xi_sq_mul_arcGammaMultiplier_le {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 / 4 →
      ‖RHTower.xi s ^ 2 * arcGammaMultiplier w s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C, hC, hj⟩ := exists_stripDecay_xiShiftedGamma
  set ε := xiShiftedGammaRate
  have hε := xiShiftedGammaRate_pos
  set S := ∑' j, w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun j => mul_nonneg (hw j) (sq_nonneg _)
  refine ⟨C ^ 2 * S * (1 + 2 / (2 * ε) ^ 2), fun s hs1 hs2 => ?_⟩
  rw [xi_sq_mul_arcGammaMultiplier]
  have him1 : |(-I * (s - 1 / 2)).im| ≤ 3 / 4 := by
    rw [im_neg_I_mul_sub_half, abs_neg, abs_le]; constructor <;> linarith
  have him2 : |(I * (s - 1 / 2)).im| ≤ 3 / 4 := by
    rw [im_I_mul_sub_half, abs_le]; constructor <;> linarith
  have hterm : ∀ j, ‖(w j : ℂ) * (xiShiftedGamma j (-I * (s - 1 / 2)) *
      xiShiftedGamma j (I * (s - 1 / 2)))‖ ≤
      C ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) * Real.exp (-(2 * ε * |s.im|)) := by
    intro j
    have b1 := (hj j).bound _ him1
    have b2 := (hj j).bound _ him2
    rw [re_neg_I_mul_sub_half] at b1
    rw [re_I_mul_sub_half, abs_neg] at b2
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    have hJ : 0 ≤ C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) := by positivity
    calc w j * (‖xiShiftedGamma j (-I * (s - 1 / 2))‖ * ‖xiShiftedGamma j (I * (s - 1 / 2))‖) ≤
        w j * ((C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (-(ε * |s.im|))) *
          (C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (-(ε * |s.im|)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) (hw j)
      _ = C ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) *
          (Real.exp (-(ε * |s.im|)) * Real.exp (-(ε * |s.im|))) := by ring
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hsumB : Summable fun j => C ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) *
      Real.exp (-(2 * ε * |s.im|)) := (hsum.mul_left _).mul_right _
  have hsumN := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumB
  refine (norm_tsum_le_tsum_norm hsumN).trans ((Summable.tsum_le_tsum hterm hsumN hsumB).trans ?_)
  rw [tsum_mul_right, tsum_mul_left]
  have he := exp_neg_mul_abs_le_inv_one_add_sq (a := 2 * ε) (by positivity) s.im
  have hC2 : 0 ≤ C ^ 2 * S := by positivity
  calc C ^ 2 * S * Real.exp (-(2 * ε * |s.im|)) ≤
      C ^ 2 * S * ((1 + 2 / (2 * ε) ^ 2) / (1 + s.im ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using he) hC2
    _ = _ := by ring

/-- `R(½ + iτ) = Σ_j w_j |Q_j(τ)|²`. -/
theorem arcGammaMultiplier_criticalLine (w : ℕ → ℝ) (τ : ℝ) :
    arcGammaMultiplier w (1 / 2 + (τ : ℂ) * I) =
      ∑' j, ((w j * ‖shiftedGammaPoly j τ‖ ^ 2 : ℝ) : ℂ) := by
  unfold arcGammaMultiplier
  refine tsum_congr fun j => ?_
  have e1 : -I * (1 / 2 + (τ : ℂ) * I - 1 / 2) = (τ : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  have e2 : I * (1 / 2 + (τ : ℂ) * I - 1 / 2) = -(τ : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  have hneg : shiftedGammaPoly j (-(τ : ℂ)) = conj (shiftedGammaPoly j τ) := by
    unfold shiftedGammaPoly
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [map_add, map_natCast, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  rw [hneg, Complex.mul_conj']
  push_cast
  ring

/-! ### The archimedean factor -/

/-- `|Γ(s/2)| ≤ K (1 + |Im s|)^N e^{−π|Im s|/4}` on `½ ≤ Re s ≤ 5/4`. -/
theorem exists_norm_Gamma_half_le :
    ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 / 4 →
      ‖Complex.Gamma (s / 2)‖ ≤ K * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im| / 4)) := by
  obtain ⟨CΓ, N, hCΓ, hΓ⟩ := GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip
    (1 / 4) (5 / 8)
  -- the compact part `|Im s| ≤ 2`
  set K₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (1 / 2 : ℝ) (5 / 4) ×ˢ Set.Icc (-2 : ℝ) 2) with hK₀
  have hK₀c : IsCompact K₀ := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn (fun s : ℂ => Complex.Gamma (s / 2)) K₀ := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hre : 0 < (((p.1 : ℂ) + (p.2 : ℂ) * I) / 2).re := by
      simp; linarith [hp.1.1]
    refine ContinuousAt.continuousWithinAt ?_
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).continuousAt.comp (by fun_prop)
    have := congrArg Complex.re hm
    rw [Complex.neg_re, Complex.natCast_re] at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨M, hM⟩ := hK₀c.exists_bound_of_continuousOn hcont
  refine ⟨max CΓ (max M 0 * Real.exp (Real.pi / 2)), N, le_max_of_le_left hCΓ,
    fun s hs1 hs2 => ?_⟩
  have hE : 0 < Real.exp (-(Real.pi * |s.im| / 4)) := Real.exp_pos _
  have hP : 1 ≤ (1 + |s.im|) ^ N := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases le_or_gt |s.im| 2 with ht | ht
  · have hs : s ∈ K₀ := ⟨(s.re, s.im), ⟨⟨hs1, hs2⟩, abs_le.mp ht⟩, by
      simp [Complex.re_add_im]⟩
    have h1 := (hM s hs).trans (le_max_left M 0)
    have h2 : Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |s.im| / 4)) ≥ 1 := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith [Real.pi_pos]
    calc ‖Complex.Gamma (s / 2)‖ ≤ max M 0 := h1
      _ ≤ max M 0 * (Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |s.im| / 4))) := by
          nlinarith [le_max_right M 0]
      _ ≤ max M 0 * Real.exp (Real.pi / 2) * (1 + |s.im|) ^ N *
            Real.exp (-(Real.pi * |s.im| / 4)) := by
          have : 0 ≤ max M 0 * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |s.im| / 4)) := by
            positivity
          nlinarith
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · have hz1 : (1 / 4 : ℝ) ≤ (s / 2).re := by simp; linarith
    have hz2 : (s / 2).re ≤ 5 / 8 := by simp; linarith
    have hz3 : 1 ≤ |(s / 2).im| := by
      simp only [Complex.div_ofNat_im, abs_div, abs_two]; linarith
    have h := hΓ (s / 2) hz1 hz2 hz3
    have him : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
    rw [him] at h
    have hpow : (|s.im| / 2) ^ N ≤ (1 + |s.im|) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s.im]) N
    have hexp : Real.exp (-(Real.pi * (|s.im| / 2) / 2)) = Real.exp (-(Real.pi * |s.im| / 4)) := by
      congr 1; ring
    rw [hexp] at h
    calc ‖Complex.Gamma (s / 2)‖ ≤ CΓ * (|s.im| / 2) ^ N * Real.exp (-(Real.pi * |s.im| / 4)) := h
      _ ≤ max CΓ (max M 0 * Real.exp (Real.pi / 2)) * (1 + |s.im|) ^ N *
            Real.exp (-(Real.pi * |s.im| / 4)) := by
          gcongr
          exact le_max_left _ _

/-- `(1 + |t|)^k e^{−a|t|} ≤ k! a^{−k} e^a` for `a > 0`. -/
theorem one_add_abs_pow_mul_exp_neg_le_factorial {a : ℝ} (ha : 0 < a) (k : ℕ) (t : ℝ) :
    (1 + |t|) ^ k * Real.exp (-(a * |t|)) ≤ k ! / a ^ k * Real.exp a := by
  have h := Real.pow_div_factorial_le_exp (a * (1 + |t|)) (by positivity) k
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hak : 0 < a ^ k := by positivity
  rw [mul_pow, div_le_iff₀ hk] at h
  have e : Real.exp (a * (1 + |t|)) = Real.exp a * Real.exp (a * |t|) := by
    rw [← Real.exp_add]; ring_nf
  rw [e] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc (1 + |t|) ^ k = (a ^ k * (1 + |t|) ^ k) / a ^ k := by field_simp
    _ ≤ (Real.exp a * Real.exp (a * |t|) * k !) / a ^ k := by gcongr
    _ = k ! / a ^ k * Real.exp a * Real.exp (a * |t|) := by ring

/-- **Quadratic decay of `G² R`** on `½ ≤ Re s ≤ 5/4`. -/
theorem exists_norm_archXi_sq_mul_arcGammaMultiplier_le {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 / 4 →
      ‖ExactNullDivisorTransfer.archXi s ^ 2 * arcGammaMultiplier w s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨K, N, hK, hΓ⟩ := exists_norm_Gamma_half_le
  set S := ∑' j, w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun j => mul_nonneg (hw j) (sq_nonneg _)
  set a : ℝ := Real.pi / 2 - Real.log 3
  have ha : 0 < a := by
    have h : Real.log 3 < 3 / 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (x := 3 / 2) (by norm_num)
      linarith
    have : (3 : ℝ) < Real.pi := Real.pi_gt_three
    simp only [a]; linarith
  set k := 2 * N + 6
  refine ⟨9 * S * K ^ 2 / 4 * 16 * (k ! / a ^ k * Real.exp a), fun s hs1 hs2 => ?_⟩
  set t := s.im
  have hR := norm_arcGammaMultiplier_le hw hsum (s := s) (by rw [abs_le]; constructor <;> linarith)
  have hG := hΓ s hs1 hs2
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith
  have hss : ‖s * (s - 1) / 2‖ ≤ (2 + |t|) ^ 2 / 2 := by
    rw [norm_div, norm_mul, Complex.norm_ofNat]
    have h1 : ‖s‖ ≤ 2 + |t| := (Complex.norm_le_abs_re_add_abs_im s).trans (by
      rw [abs_of_pos (by linarith)]; linarith)
    have h2 : ‖s - 1‖ ≤ 2 + |t| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have h3 : |(s - 1).re| ≤ 2 := by
        rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith
      have h4 : (s - 1).im = t := by simp [t]
      rw [h4]
      linarith
    have := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    rw [sq]
    linarith
  have hX : ‖ExactNullDivisorTransfer.archXi s‖ ≤
      (2 + |t|) ^ 2 / 2 * (K * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 4))) := by
    unfold ExactNullDivisorTransfer.archXi
    rw [Complex.Gammaℝ_def, norm_mul, norm_mul]
    calc ‖s * (s - 1) / 2‖ * (‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖) ≤
        (2 + |t|) ^ 2 / 2 * (1 * (K * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 4)))) :=
          mul_le_mul hss (mul_le_mul hpi hG (norm_nonneg _) zero_le_one)
            (by positivity) (by positivity)
      _ = _ := by rw [one_mul]
  have h2t : (2 + |t|) ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
  have hmain : ‖ExactNullDivisorTransfer.archXi s ^ 2 * arcGammaMultiplier w s‖ ≤
      9 * S * K ^ 2 / 4 * 16 * ((1 + |t|) ^ (2 * N + 4) * Real.exp (-(a * |t|))) := by
    rw [norm_mul, norm_pow]
    have hX2 := pow_le_pow_left₀ (norm_nonneg _) hX 2
    have hexp : Real.exp (-(Real.pi * |t| / 4)) ^ 2 * Real.exp (Real.log 3 * |t|) =
        Real.exp (-(a * |t|)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; simp only [a]; push_cast; ring
    have h24 : (2 + |t|) ^ 4 ≤ 16 * (1 + |t|) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) h2t 4
      linarith [show (2 * (1 + |t|)) ^ 4 = 16 * (1 + |t|) ^ 4 by ring]
    calc ‖ExactNullDivisorTransfer.archXi s‖ ^ 2 * ‖arcGammaMultiplier w s‖ ≤
        ((2 + |t|) ^ 2 / 2 * (K * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 4)))) ^ 2 *
          (9 * S * Real.exp (Real.log 3 * |t|)) :=
          mul_le_mul hX2 hR (norm_nonneg _) (by positivity)
      _ = 9 * S * K ^ 2 / 4 * ((2 + |t|) ^ 4 * (1 + |t|) ^ (2 * N) *
            (Real.exp (-(Real.pi * |t| / 4)) ^ 2 * Real.exp (Real.log 3 * |t|))) := by ring
      _ = 9 * S * K ^ 2 / 4 * ((2 + |t|) ^ 4 * (1 + |t|) ^ (2 * N) * Real.exp (-(a * |t|))) := by
          rw [hexp]
      _ ≤ 9 * S * K ^ 2 / 4 * ((16 * (1 + |t|) ^ 4) * (1 + |t|) ^ (2 * N) *
            Real.exp (-(a * |t|))) := by gcongr
      _ = _ := by ring
  have hbound := one_add_abs_pow_mul_exp_neg_le_factorial ha k t
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hC0 : 0 ≤ 9 * S * K ^ 2 / 4 := by positivity
  calc ‖ExactNullDivisorTransfer.archXi s ^ 2 * arcGammaMultiplier w s‖ * (1 + t ^ 2) ≤
      9 * S * K ^ 2 / 4 * 16 * ((1 + |t|) ^ (2 * N + 4) * Real.exp (-(a * |t|))) *
        (1 + |t|) ^ 2 := mul_le_mul hmain hsq (by positivity) (by positivity)
    _ = 9 * S * K ^ 2 / 4 * 16 * ((1 + |t|) ^ k * Real.exp (-(a * |t|))) := by
        simp only [k]; ring
    _ ≤ 9 * S * K ^ 2 / 4 * 16 * (k ! / a ^ k * Real.exp a) := by gcongr

end RHTower.WeilSpectral
