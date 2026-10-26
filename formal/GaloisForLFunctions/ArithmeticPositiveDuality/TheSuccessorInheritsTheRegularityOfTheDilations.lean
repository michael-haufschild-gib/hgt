import GaloisForLFunctions.ArithmeticPositiveDuality.TheSuccessorSeesOnlyTheContinuousDilationSpectrum

/-!
# The successor inherits the regularity of the dilations

**Theorem** (`norm_successor_dilate_sub_le`). For every positive-definite `φ` on `Aff(ℚ)`, every
`r ∈ ℚˣ` and every `b ∈ ℚ`,
`|φ(x ↦ x + rb) − φ(x ↦ x + b)| ≤ 2 φ(1)^{1/2} (2 Re(φ(1) − φ(x ↦ x/r)))^{1/2}`.

The modulus of continuity of the successor in the multiplicative variable is controlled by the
modulus of continuity of the dilation part at `1`.

**Corollary** (`tendsto_successor_of_continuousAt_dilation`). If the dilation part is continuous at
`1` for the real topology (in particular if it is archimedean), the successor is continuous on
`ℚ ∖ {0}` for the real topology. So no successor with a jump at a nonzero point, such as the
integer successor `1_ℤ` (P18) or any discontinuous periodic successor, is compatible with an
archimedean dilation part: arithmetic successors and archimedean dilation correlations, Weil's
among them, live in different regularity classes.

Mechanism. `π(x ↦ x + rb) = π_r π(x ↦ x + b) π_r⁻¹` in the GNS space, so
`φ(x ↦ x + rb) = ⟨η, π(x ↦ x + b)η⟩` with `η = π(x ↦ x/r)ξ`, and
`‖η − ξ‖² = 2 Re(φ(1) − φ(x ↦ x/r))`.
-/

open Complex Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
include hφ

theorem affVec_norm_sq : ‖affVec hφ‖ ^ 2 = (φ 1).re := by
  have h := inner_affRep hφ 1 1
  rw [rep_one_apply, inv_one, one_mul, inner_self_complex] at h
  rw [← h, Complex.ofReal_re]

/-- **Regularity transfer.** `|φ(x + rb) − φ(x + b)| ≤ 2‖ξ‖‖π(x ↦ x/r)ξ − ξ‖`. -/
theorem norm_successor_dilate_sub_le (r : ℚˣ) (b : ℚ) :
    ‖φ (translation ((r : ℚ) * b)) - φ (translation b)‖ ≤
      2 * Real.sqrt (φ 1).re * Real.sqrt (2 * (φ 1 - φ (dilation r⁻¹)).re) := by
  have hφg : ∀ g, φ g = ⟪affVec hφ, affRep hφ g (affVec hφ)⟫_ℂ := fun g =>
    (inner_gnsCyclic_gnsRep (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) g).symm
  obtain ⟨η, hη⟩ : ∃ η, affRep hφ (dilation r⁻¹) (affVec hφ) = η := ⟨_, rfl⟩
  -- conjugation by the dilation: `φ(x + rb) = ⟨η, π(x + b)η⟩`
  have hconj : φ (translation ((r : ℚ) * b)) = ⟪η, affRep hφ (translation b) η⟫_ℂ := by
    rw [hφg, ← dilation_mul_translation_mul_inv, map_mul, map_mul, LinearIsometryEquiv.coe_mul,
      LinearIsometryEquiv.coe_mul, Function.comp_apply, Function.comp_apply, inner_rep_dilation,
      ← map_inv dilation r, hη]
  have hnorm : ‖η‖ = ‖affVec hφ‖ := by rw [← hη, LinearIsometryEquiv.norm_map]
  have hd2 : ‖η - affVec hφ‖ ^ 2 = 2 * (φ 1 - φ (dilation r⁻¹)).re := by
    rw [norm_sub_sq (𝕜 := ℂ), hnorm, ← inner_conj_symm, RCLike.re_to_complex, Complex.conj_re,
      ← hη, ← hφg, affVec_norm_sq hφ, Complex.sub_re]
    ring
  have hξ : ‖affVec hφ‖ = Real.sqrt (φ 1).re := by
    rw [← affVec_norm_sq hφ, Real.sqrt_sq (norm_nonneg _)]
  have hd : ‖η - affVec hφ‖ = Real.sqrt (2 * (φ 1 - φ (dilation r⁻¹)).re) := by
    rw [← hd2, Real.sqrt_sq (norm_nonneg _)]
  rw [hconj, hφg (translation b)]
  calc ‖⟪η, affRep hφ (translation b) η⟫_ℂ -
        ⟪affVec hφ, affRep hφ (translation b) (affVec hφ)⟫_ℂ‖
      = ‖⟪η - affVec hφ, affRep hφ (translation b) η⟫_ℂ +
          ⟪affVec hφ, affRep hφ (translation b) (η - affVec hφ)⟫_ℂ‖ := by
        rw [inner_sub_left, map_sub, inner_sub_right]; ring_nf
    _ ≤ ‖η - affVec hφ‖ * ‖η‖ + ‖affVec hφ‖ * ‖η - affVec hφ‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_inner_le_norm _ _).trans (by rw [LinearIsometryEquiv.norm_map])
        · exact (norm_inner_le_norm _ _).trans (by rw [LinearIsometryEquiv.norm_map])
    _ = 2 * Real.sqrt (φ 1).re * Real.sqrt (2 * (φ 1 - φ (dilation r⁻¹)).re) := by
        rw [hnorm, hξ, hd]; ring

/-- **Archimedean dilation parts force continuous successors.** If `φ(x ↦ ux) → φ(1)` as
`u → 1` in `ℚ_{>0}` for the real topology, then `b_n → b ≠ 0` in `ℝ` with `b_n ∈ ℚ` gives
`φ(x ↦ x + b_n) → φ(x ↦ x + b)`. -/
theorem tendsto_successor_of_continuousAt_dilation
    (hcont : ∀ u : ℕ → ℚˣ, (∀ n, 0 < (u n : ℚ)) → Tendsto (fun n => ((u n : ℚ) : ℝ)) atTop (𝓝 1) →
      Tendsto (fun n => φ (dilation (u n))) atTop (𝓝 (φ 1)))
    {b : ℚ} (hb : b ≠ 0) {c : ℕ → ℚ} (hc : Tendsto (fun n => ((c n : ℚ) : ℝ)) atTop (𝓝 (b : ℝ))) :
    Tendsto (fun n => φ (translation (c n))) atTop (𝓝 (φ (translation b))) := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  -- eventually `c n ≠ 0`; write `c n = r_n b` with `r_n → 1`
  have hev : ∀ᶠ n in atTop, c n ≠ 0 := by
    exact (hc.eventually_ne hb').mono fun n hn h => hn (by rw [h, Rat.cast_zero])
  set r : ℕ → ℚˣ := fun n => if h : c n = 0 then 1 else Units.mk0 (c n / b) (div_ne_zero h hb)
  have hr : ∀ᶠ n in atTop, ((r n : ℚˣ) : ℚ) * b = c n := hev.mono fun n hn => by
    simp only [r, dif_neg hn, Units.val_mk0]; field_simp
  have hrlim : Tendsto (fun n => ((((r n)⁻¹ : ℚˣ) : ℚ) : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => (b : ℝ) / (c n : ℝ)) atTop (𝓝 1) := by
      simpa [div_self hb'] using (tendsto_const_nhds (x := (b : ℝ))).div hc hb'
    refine h1.congr' (hev.mono fun n hn => ?_)
    simp only [r, dif_neg hn, Units.val_inv_eq_inv_val, Units.val_mk0]
    push_cast
    rw [inv_div]
  have hrpos : ∀ᶠ n in atTop, 0 < (((r n)⁻¹ : ℚˣ) : ℚ) := by
    have := hrlim.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact this.mono fun n hn => by exact_mod_cast hn
  -- the dilation defect tends to zero
  have hdil : Tendsto (fun n => φ (dilation (r n)⁻¹)) atTop (𝓝 (φ 1)) := by
    set u : ℕ → ℚˣ := fun n => if 0 < (((r n)⁻¹ : ℚˣ) : ℚ) then (r n)⁻¹ else 1
    have hupos : ∀ n, 0 < (u n : ℚ) := fun n => by
      simp only [u]; split_ifs with h
      · exact h
      · simp
    have hueq : ∀ᶠ n in atTop, u n = (r n)⁻¹ := hrpos.mono fun n hn => by simp only [u, if_pos hn]
    have hulim : Tendsto (fun n => ((u n : ℚ) : ℝ)) atTop (𝓝 1) :=
      hrlim.congr' (hueq.mono fun n hn => by rw [hn])
    exact (hcont u hupos hulim).congr' (hueq.mono fun n hn => by rw [hn])
  have hbound : Tendsto (fun n => 2 * Real.sqrt (φ 1).re *
      Real.sqrt (2 * (φ 1 - φ (dilation (r n)⁻¹)).re)) atTop (𝓝 0) := by
    have hf : Continuous fun z : ℂ => 2 * Real.sqrt (φ 1).re * Real.sqrt (2 * (φ 1 - z).re) :=
      continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.mul
        (Complex.continuous_re.comp (continuous_const.sub continuous_id))))
    have h := (hf.tendsto (φ 1)).comp hdil
    simp only [sub_self, Complex.zero_re, mul_zero, Real.sqrt_zero] at h
    exact h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hbound
  filter_upwards [hr] with n hn
  rw [← hn]
  exact norm_successor_dilate_sub_le hφ (r n) b

end GaloisForLFunctions.ArithmeticPositiveDuality
