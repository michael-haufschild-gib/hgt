import GaloisForLFunctions.HTGeometry.BorelSeriesParityLaplace
import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem

/-!
# Laplace inversion of Borel series on rectangle contours

For a rectangle `R` with the origin in its interior:

* `∮_{∂R} p^j dp = 2πi` if `j = -1` and `0` otherwise (`rectangleIntegral_zpow`);
* `∮_{∂R} p^m e^{tp} p^{-N-1} dp = 2πi t^{N-m}/(N-m)!` for `m ≤ N` and `0` otherwise
  (`rectangleIntegral_pow_mul_cexp_mul_inv_pow`), by expanding `e^{tp}` and integrating
  monomials;
* if `|b_N| ≤ M R^N` and `ρ ≤ |p|` on `∂R` for some `ρ > R`, then the Laurent symbol
  `G(p) = Σ_N b_N p^{-N-1}` inverts the Borel series `v(t) = Σ_N b_N t^N/N!` together with all its
  derivatives: `∮_{∂R} p^m e^{tp} G(p) dp = 2πi v^{(m)}(t)`
  (`rectangleIntegral_borelLaplaceInversion`).

A function holomorphic on the closed frame between a rectangle and an inner open box has the same
boundary integral over both rectangles (`rectangleIntegral_eq_of_differentiableOn_frame`).
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Deformation across a frame -/

private theorem re_ofReal_add_ofReal_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

private theorem im_ofReal_add_ofReal_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

private theorem mem_rect_iff {a b c d : ℝ} (hac : a ≤ c) (hbd : b ≤ d) (p : ℂ) :
    p ∈ Rectangle ((a : ℂ) + b * I) ((c : ℂ) + d * I) ↔
      a ≤ p.re ∧ p.re ≤ c ∧ b ≤ p.im ∧ p.im ≤ d := by
  rw [mem_Rect (by simpa using hac) (by simpa using hbd)]
  simp

private theorem rect_subset_frame {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ a b c d : ℝ} (hx : x₀ ≤ x₃)
    (hy : y₀ ≤ y₃) (hac : a ≤ c) (hbd : b ≤ d) (ha : x₀ ≤ a) (hc : c ≤ x₃) (hb : y₀ ≤ b)
    (hd : d ≤ y₃) (hout : c ≤ x₁ ∨ x₂ ≤ a ∨ d ≤ y₁ ∨ y₂ ≤ b) :
    Rectangle ((a : ℂ) + b * I) ((c : ℂ) + d * I) ⊆
      Rectangle ((x₀ : ℂ) + y₀ * I) ((x₃ : ℂ) + y₃ * I) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) := by
  intro p hp
  rw [mem_rect_iff hac hbd] at hp
  refine ⟨(mem_rect_iff hx hy p).2 ⟨by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rcases hout with h | h | h | h <;> linarith [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

private theorem border_subset_frame {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ a b c d : ℝ} (hx : x₀ ≤ x₃)
    (hy : y₀ ≤ y₃) (hac : a ≤ c) (hbd : b ≤ d) (ha : x₀ ≤ a) (hc : c ≤ x₃) (hb : y₀ ≤ b)
    (hd : d ≤ y₃) (ha' : a ≤ x₁ ∨ x₂ ≤ a) (hc' : c ≤ x₁ ∨ x₂ ≤ c) (hb' : b ≤ y₁ ∨ y₂ ≤ b)
    (hd' : d ≤ y₁ ∨ y₂ ≤ d) :
    RectangleBorder ((a : ℂ) + b * I) ((c : ℂ) + d * I) ⊆
      Rectangle ((x₀ : ℂ) + y₀ * I) ((x₃ : ℂ) + y₃ * I) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) := by
  intro p hp
  have hR := rectangleBorder_subset_rectangle _ _ hp
  rw [mem_rect_iff hac hbd] at hR
  refine ⟨(mem_rect_iff hx hy p).2 ⟨by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  simp only [RectangleBorder, re_ofReal_add_ofReal_mul_I, im_ofReal_add_ofReal_mul_I,
    mem_union, mem_reProdIm, mem_singleton_iff] at hp
  rcases hp with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
  · rcases hb' with h' | h' <;> linarith
  · rcases ha' with h' | h' <;> linarith
  · rcases hd' with h' | h' <;> linarith
  · rcases hc' with h' | h' <;> linarith

/-- **Frame deformation.**  If `f` is holomorphic on the closed frame
`[x₀,x₃]×[y₀,y₃] \ (x₁,x₂)×(y₁,y₂)`, the boundary integrals over the outer and the inner rectangle
coincide. -/
theorem rectangleIntegral_eq_of_differentiableOn_frame {f : ℂ → ℂ}
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (hx₀ : x₀ ≤ x₁) (hx₁ : x₁ ≤ x₂) (hx₂ : x₂ ≤ x₃)
    (hy₀ : y₀ ≤ y₁) (hy₁ : y₁ ≤ y₂) (hy₂ : y₂ ≤ y₃)
    (hf : DifferentiableOn ℂ f
      (Rectangle ((x₀ : ℂ) + y₀ * I) ((x₃ : ℂ) + y₃ * I) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂))) :
    RectangleIntegral f ((x₀ : ℂ) + y₀ * I) ((x₃ : ℂ) + y₃ * I) =
      RectangleIntegral f ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) := by
  have hx : x₀ ≤ x₃ := by linarith
  have hy : y₀ ≤ y₃ := by linarith
  have hc := hf.continuousOn
  have bi : ∀ {a b c d : ℝ}, a ≤ c → b ≤ d → x₀ ≤ a → c ≤ x₃ → y₀ ≤ b → d ≤ y₃ →
      (a ≤ x₁ ∨ x₂ ≤ a) → (c ≤ x₁ ∨ x₂ ≤ c) → (b ≤ y₁ ∨ y₂ ≤ b) → (d ≤ y₁ ∨ y₂ ≤ d) →
      RectangleBorderIntegrable f ((a : ℂ) + b * I) ((c : ℂ) + d * I) :=
    fun hac hbd ha hc' hb hd ha' hc'' hb' hd' => ContinuousOn.rectangleBorder_integrable
      (hc.mono (border_subset_frame hx hy hac hbd ha hc' hb hd ha' hc'' hb' hd'))
  have vz : ∀ {a b c d : ℝ}, a ≤ c → b ≤ d → x₀ ≤ a → c ≤ x₃ → y₀ ≤ b → d ≤ y₃ →
      (c ≤ x₁ ∨ x₂ ≤ a ∨ d ≤ y₁ ∨ y₂ ≤ b) →
      RectangleIntegral f ((a : ℂ) + b * I) ((c : ℂ) + d * I) = 0 :=
    fun hac hbd ha hc' hb hd hout => HolomorphicOn.vanishesOnRectangle hf
      (rect_subset_frame hx hy hac hbd ha hc' hb hd hout)
  have h₁ := RectangleIntegralVSplit' (f := f) (x₀ := x₀) (x₁ := x₃) (y₀ := y₀) (y₁ := y₃)
    (b := y₁) (by rw [uIcc_of_le hy]; exact ⟨hy₀, by linarith⟩)
    (bi hx hy le_rfl le_rfl le_rfl le_rfl (Or.inl hx₀) (Or.inr hx₂) (Or.inl hy₀) (Or.inr hy₂))
  have h₂ : RectangleIntegral f ((x₀ : ℂ) + y₀ * I) ((x₃ : ℂ) + y₁ * I) = 0 :=
    vz hx hy₀ le_rfl le_rfl le_rfl (by linarith) (Or.inr (Or.inr (Or.inl le_rfl)))
  have h₃ := RectangleIntegralVSplit' (f := f) (x₀ := x₀) (x₁ := x₃) (y₀ := y₁) (y₁ := y₃)
    (b := y₂) (by rw [uIcc_of_le (by linarith)]; exact ⟨hy₁, hy₂⟩)
    (bi hx (by linarith) le_rfl le_rfl hy₀ le_rfl (Or.inl hx₀) (Or.inr hx₂) (Or.inl le_rfl)
      (Or.inr hy₂))
  have h₄ : RectangleIntegral f ((x₀ : ℂ) + y₂ * I) ((x₃ : ℂ) + y₃ * I) = 0 :=
    vz hx hy₂ le_rfl le_rfl (by linarith) le_rfl (Or.inr (Or.inr (Or.inr le_rfl)))
  have h₅ := RectangleIntegralHSplit' (f := f) (x₀ := x₀) (x₁ := x₃) (y₀ := y₁) (y₁ := y₂)
    (a := x₁) (by rw [uIcc_of_le hx]; exact ⟨hx₀, by linarith⟩)
    (bi hx hy₁ le_rfl le_rfl hy₀ (by linarith) (Or.inl hx₀) (Or.inr hx₂) (Or.inl le_rfl)
      (Or.inr le_rfl))
  have h₆ : RectangleIntegral f ((x₀ : ℂ) + y₁ * I) ((x₁ : ℂ) + y₂ * I) = 0 :=
    vz hx₀ hy₁ le_rfl (by linarith) hy₀ (by linarith) (Or.inl le_rfl)
  have h₇ := RectangleIntegralHSplit' (f := f) (x₀ := x₁) (x₁ := x₃) (y₀ := y₁) (y₁ := y₂)
    (a := x₂) (by rw [uIcc_of_le (by linarith)]; exact ⟨hx₁, hx₂⟩)
    (bi (by linarith) hy₁ hx₀ le_rfl hy₀ (by linarith) (Or.inl le_rfl) (Or.inr hx₂)
      (Or.inl le_rfl) (Or.inr le_rfl))
  have h₈ : RectangleIntegral f ((x₂ : ℂ) + y₁ * I) ((x₃ : ℂ) + y₂ * I) = 0 :=
    vz hx₂ hy₁ (by linarith) le_rfl hy₀ (by linarith) (Or.inr (Or.inl le_rfl))
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  ring

/-! ## Compactness and series interchange on the border -/

theorem isCompact_rectangleBorder (z w : ℂ) : IsCompact (RectangleBorder z w) :=
  (((isCompact_uIcc.reProdIm isCompact_singleton).union
    (isCompact_singleton.reProdIm isCompact_uIcc)).union
    (isCompact_uIcc.reProdIm isCompact_singleton)).union
    (isCompact_singleton.reProdIm isCompact_uIcc)

private theorem hasSum_intervalIntegral_comp {F : ℕ → ℂ → ℂ} {S : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {B : ℕ → ℝ} (hγ : Continuous γ) (hmaps : MapsTo γ [[a, b]] S)
    (hF : ∀ k, ContinuousOn (F k) S) (hB : Summable B) (hb : ∀ k, ∀ s ∈ S, ‖F k s‖ ≤ B k) :
    HasSum (fun k => ∫ x in a..b, F k (γ x)) (∫ x in a..b, ∑' k, F k (γ x)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => B k)
    (fun k => ?_) (fun k => Eventually.of_forall fun x hx => hb k _ (hmaps (uIoc_subset_uIcc hx)))
    (Eventually.of_forall fun _ _ => hB) intervalIntegrable_const
    (Eventually.of_forall fun x hx => ?_)
  · exact (((hF k).comp hγ.continuousOn hmaps).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact (Summable.of_norm_bounded hB fun k => hb k _ (hmaps (uIoc_subset_uIcc hx))).hasSum

/-- **Termwise integration on a rectangle border** under a summable uniform bound. -/
theorem hasSum_rectangleIntegral {F : ℕ → ℂ → ℂ} {z w : ℂ} {B : ℕ → ℝ}
    (hF : ∀ k, ContinuousOn (F k) (RectangleBorder z w)) (hB : Summable B)
    (hb : ∀ k, ∀ s ∈ RectangleBorder z w, ‖F k s‖ ≤ B k) :
    HasSum (fun k => RectangleIntegral (F k) z w)
      (RectangleIntegral (fun s => ∑' k, F k s) z w) := by
  have h1 := hasSum_intervalIntegral_comp (γ := fun x : ℝ => (x : ℂ) + z.im * I) (by fun_prop)
    (mapsTo_rectangleBorder_left_im z w) hF hB hb
  have h2 := hasSum_intervalIntegral_comp (γ := fun x : ℝ => (x : ℂ) + w.im * I) (by fun_prop)
    (mapsTo_rectangleBorder_right_im z w) hF hB hb
  have h3 := hasSum_intervalIntegral_comp (γ := fun y : ℝ => (w.re : ℂ) + y * I) (by fun_prop)
    (mapsTo_rectangleBorder_right_re z w) hF hB hb
  have h4 := hasSum_intervalIntegral_comp (γ := fun y : ℝ => (z.re : ℂ) + y * I) (by fun_prop)
    (mapsTo_rectangleBorder_left_re z w) hF hB hb
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  exact ((h1.sub h2).add (h3.mul_left I)).sub (h4.mul_left I)

/-! ## Monomials and exponential monomials -/

/-- **Monomial residues.**  `∮_{∂R} p^j dp = 2πi·[j = -1]` when `0` is interior to `R`. -/
theorem rectangleIntegral_zpow {z w : ℂ} (hz : z.re < 0) (hz' : z.im < 0) (hw : 0 < w.re)
    (hw' : 0 < w.im) (j : ℤ) :
    RectangleIntegral (fun p => p ^ j) z w = if j = -1 then 2 * π * I else 0 := by
  by_cases hj : j = -1
  · subst hj
    rw [if_pos rfl]
    have h := ResidueTheoremAtOrigin' (c := 1) hz hz' hw hw'
    have e : (fun p : ℂ => p ^ (-1 : ℤ)) = fun s => 1 / s := by
      funext p; rw [zpow_neg_one, one_div]
    rw [e, h]; ring
  rw [if_neg hj]
  rcases le_or_gt 0 j with h0 | h0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    simp only [zpow_natCast]
    exact HolomorphicOn.vanishesOnRectangle (U := univ) (differentiable_pow n).differentiableOn
      (subset_univ _)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    have hn2 : 2 ≤ n := by omega
    have e : (fun p : ℂ => p ^ j) = fun s => ((s - 0) ^ n)⁻¹ := by
      funext p; rw [hn, zpow_neg, zpow_natCast, sub_zero]
    rw [e]
    exact rectangleIntegral_inv_pow_eq_zero hn2 (by simpa using hz.ne) (by simpa using hw.ne')
      (by simpa using hz'.ne) (by simpa using hw'.ne')

private theorem norm_le_abs_corners_of_mem_rectangle {z w p : ℂ} (hp : p ∈ Rectangle z w) :
    ‖p‖ ≤ |z.re| + |w.re| + (|z.im| + |w.im|) := by
  obtain ⟨h1, h2⟩ := hp
  have hre : |p.re| ≤ |z.re| + |w.re| := by
    rcases le_total z.re w.re with h | h
    · rw [uIcc_of_le h] at h1; rw [abs_le]; constructor <;>
        cases abs_cases z.re <;> cases abs_cases w.re <;> linarith [h1.1, h1.2]
    · rw [uIcc_of_ge h] at h1; rw [abs_le]; constructor <;>
        cases abs_cases z.re <;> cases abs_cases w.re <;> linarith [h1.1, h1.2]
  have him : |p.im| ≤ |z.im| + |w.im| := by
    rcases le_total z.im w.im with h | h
    · rw [uIcc_of_le h] at h2; rw [abs_le]; constructor <;>
        cases abs_cases z.im <;> cases abs_cases w.im <;> linarith [h2.1, h2.2]
    · rw [uIcc_of_ge h] at h2; rw [abs_le]; constructor <;>
        cases abs_cases z.im <;> cases abs_cases w.im <;> linarith [h2.1, h2.2]
  exact (norm_le_abs_re_add_abs_im p).trans (add_le_add hre him)

private theorem lowerRadius_le_norm_of_mem_border {z w p : ℂ} (hz : z.re < 0) (hz' : z.im < 0)
    (hw : 0 < w.re) (hw' : 0 < w.im) (hp : p ∈ RectangleBorder z w) :
    min (min (-z.re) w.re) (min (-z.im) w.im) ≤ ‖p‖ := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hp
  have hre := abs_re_le_norm p
  have him := abs_im_le_norm p
  rcases hp with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
  · rw [h, abs_of_neg hz'] at him
    exact (min_le_right _ _).trans ((min_le_left _ _).trans him)
  · rw [h, abs_of_neg hz] at hre
    exact (min_le_left _ _).trans ((min_le_left _ _).trans hre)
  · rw [h, abs_of_pos hw'] at him
    exact (min_le_right _ _).trans ((min_le_right _ _).trans him)
  · rw [h, abs_of_pos hw] at hre
    exact (min_le_left _ _).trans ((min_le_right _ _).trans hre)

private theorem cexp_eq_tsum (x : ℂ) : cexp x = ∑' k : ℕ, ((k.factorial : ℂ))⁻¹ * x ^ k := by
  rw [Complex.exp_eq_exp_ℂ, (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).tsum_eq.symm]
  simp only [smul_eq_mul]

private theorem rectangleIntegral_const_mul' (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    RectangleIntegral (fun s => c * f s) z w = c * RectangleIntegral f z w := by
  simpa only [smul_eq_mul] using RectangleIntegral.const_smul f z w c

/-- **Exponential monomial residues.**
`∮_{∂R} p^m e^{tp} p^{-N-1} dp = 2πi t^{N-m}/(N-m)!` for `m ≤ N`, and `0` for `m > N`. -/
theorem rectangleIntegral_pow_mul_cexp_mul_inv_pow {z w : ℂ} (hz : z.re < 0) (hz' : z.im < 0)
    (hw : 0 < w.re) (hw' : 0 < w.im) (t : ℂ) (m N : ℕ) :
    RectangleIntegral (fun p => p ^ m * cexp (t * p) * (p ^ (N + 1))⁻¹) z w =
      2 * π * I * (if m ≤ N then t ^ (N - m) / ((N - m).factorial : ℂ) else 0) := by
  set ρ := min (min (-z.re) w.re) (min (-z.im) w.im) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min (by linarith) hw) (lt_min (by linarith) hw')
  set L := |z.re| + |w.re| + (|z.im| + |w.im|)
  have hne : ∀ p ∈ RectangleBorder z w, p ≠ 0 := fun p hp h0 => by
    have := lowerRadius_le_norm_of_mem_border hz hz' hw hw' hp
    rw [h0, norm_zero] at this; linarith
  set F : ℕ → ℂ → ℂ := fun k p => p ^ m * (((k.factorial : ℂ))⁻¹ * (t * p) ^ k) * (p ^ (N + 1))⁻¹
    with hFdef
  have hsum : (fun p => ∑' k, F k p) = fun p => p ^ m * cexp (t * p) * (p ^ (N + 1))⁻¹ := by
    funext p
    simp only [hFdef]
    rw [tsum_mul_right, tsum_mul_left, cexp_eq_tsum]
  have hF : ∀ k, ContinuousOn (F k) (RectangleBorder z w) := fun k => by
    simp only [hFdef]
    exact ((by fun_prop : Continuous fun p : ℂ =>
      p ^ m * (((k.factorial : ℂ))⁻¹ * (t * p) ^ k)).continuousOn).mul
      (((continuous_pow (N + 1)).continuousOn).inv₀ fun p hp => pow_ne_zero _ (hne p hp))
  have hB : Summable fun k : ℕ =>
      L ^ m * ((‖t‖ * L) ^ k / (k.factorial : ℝ)) * (ρ ^ (N + 1))⁻¹ :=
    ((Real.summable_pow_div_factorial (‖t‖ * L)).mul_left (L ^ m)).mul_right _
  have hb : ∀ k, ∀ p ∈ RectangleBorder z w,
      ‖F k p‖ ≤ L ^ m * ((‖t‖ * L) ^ k / (k.factorial : ℝ)) * (ρ ^ (N + 1))⁻¹ := by
    intro k p hp
    have hpL := norm_le_abs_corners_of_mem_rectangle (rectangleBorder_subset_rectangle z w hp)
    have hpρ := lowerRadius_le_norm_of_mem_border hz hz' hw hw' hp
    simp only [hFdef, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : ‖p‖ ^ m ≤ L ^ m := pow_le_pow_left₀ (norm_nonneg _) hpL m
    have h2 : (‖t‖ * ‖p‖) ^ k ≤ (‖t‖ * L) ^ k :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hpL (norm_nonneg _)) k
    have h3 : (‖p‖ ^ (N + 1))⁻¹ ≤ (ρ ^ (N + 1))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hρ.le hpρ _)
    have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    calc ‖p‖ ^ m * ((k.factorial : ℝ)⁻¹ * (‖t‖ * ‖p‖) ^ k) * (‖p‖ ^ (N + 1))⁻¹ ≤
        L ^ m * ((k.factorial : ℝ)⁻¹ * (‖t‖ * L) ^ k) * (ρ ^ (N + 1))⁻¹ := by gcongr
      _ = L ^ m * ((‖t‖ * L) ^ k / (k.factorial : ℝ)) * (ρ ^ (N + 1))⁻¹ := by ring
  have hhas := hasSum_rectangleIntegral hF hB hb
  rw [hsum] at hhas
  have hterm : ∀ k, RectangleIntegral (F k) z w =
      ((k.factorial : ℂ))⁻¹ * t ^ k *
        (if ((m + k : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = -1 then 2 * π * I else 0) := by
    intro k
    rw [← rectangleIntegral_zpow hz hz' hw hw', ← rectangleIntegral_const_mul']
    refine RectangleIntegral_congr fun p hp => ?_
    have hp0 := hne p hp
    simp only [hFdef]
    rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast, mul_pow, pow_add, div_eq_mul_inv]
    ring
  simp_rw [hterm] at hhas
  refine hhas.unique ?_
  by_cases hmN : m ≤ N
  · rw [if_pos hmN]
    have hval : ∀ k, ((k.factorial : ℂ))⁻¹ * t ^ k *
        (if ((m + k : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = -1 then 2 * π * I else 0) =
        if k = N - m then 2 * π * I * (t ^ (N - m) / ((N - m).factorial : ℂ)) else 0 := by
      intro k
      by_cases hk : k = N - m
      · subst hk
        rw [if_pos (by omega), if_pos rfl]
        ring
      · rw [if_neg (by omega), if_neg hk, mul_zero]
    simp_rw [hval]
    exact hasSum_ite_eq _ _
  · rw [if_neg hmN, mul_zero]
    have hval : ∀ k, ((k.factorial : ℂ))⁻¹ * t ^ k *
        (if ((m + k : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = -1 then 2 * π * I else 0) = 0 := by
      intro k
      rw [if_neg (by omega), mul_zero]
    simp_rw [hval]
    exact hasSum_zero

/-! ## Laplace inversion -/


/-- **Laplace inversion of a Borel series.**  If `|b_N| ≤ M R^N` and `ρ ≤ |p|` on `∂R` with
`ρ > R ≥ 0`, and the origin is interior to `R`, then for every real `t` and every `m`,
`∮_{∂R} p^m e^{tp} Σ_N b_N p^{-N-1} dp = 2πi (Σ_N b_N t^N/N!)^{(m)}`. -/
theorem rectangleIntegral_borelLaplaceInversion {b : ℕ → ℝ} {M R ρ : ℝ}
    (hb : GeometricCoeffBound b M R) (hR : 0 ≤ R) (hρ : R < ρ) {z w : ℂ} (hz : z.re < 0)
    (hz' : z.im < 0) (hw : 0 < w.re) (hw' : 0 < w.im)
    (hborder : ∀ p ∈ RectangleBorder z w, ρ ≤ ‖p‖) (m : ℕ) (t : ℝ) :
    RectangleIntegral (fun p => p ^ m * cexp (t * p) * ∑' N, (b N : ℂ) * (p ^ (N + 1))⁻¹) z w =
      2 * π * I * ((iteratedDeriv m (borelSeries b) t : ℝ) : ℂ) := by
  have hρ0 : 0 < ρ := hR.trans_lt hρ
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (hb 0); simpa using this
  set L := |z.re| + |w.re| + (|z.im| + |w.im|)
  have hne : ∀ p ∈ RectangleBorder z w, p ≠ 0 := fun p hp h0 => by
    have := hborder p hp
    rw [h0, norm_zero] at this; linarith
  set F : ℕ → ℂ → ℂ := fun N p => p ^ m * cexp (t * p) * ((b N : ℂ) * (p ^ (N + 1))⁻¹)
    with hFdef
  have hsum : (fun p => ∑' N, F N p) =
      fun p => p ^ m * cexp (t * p) * ∑' N, (b N : ℂ) * (p ^ (N + 1))⁻¹ := by
    funext p
    simp only [hFdef]
    rw [tsum_mul_left]
  have hF : ∀ N, ContinuousOn (F N) (RectangleBorder z w) := fun N => by
    simp only [hFdef]
    exact ((by fun_prop : Continuous fun p : ℂ => p ^ m * cexp (t * p)).continuousOn).mul
      (continuousOn_const.mul
        (((continuous_pow (N + 1)).continuousOn).inv₀ fun p hp => pow_ne_zero _ (hne p hp)))
  have hB : Summable fun N : ℕ => L ^ m * Real.exp (|t| * L) * (M / ρ * (R / ρ) ^ N) :=
    ((summable_geometric_of_lt_one (div_nonneg hR hρ0.le) ((div_lt_one hρ0).2 hρ)).mul_left
      (M / ρ)).mul_left _
  have hbd : ∀ N, ∀ p ∈ RectangleBorder z w,
      ‖F N p‖ ≤ L ^ m * Real.exp (|t| * L) * (M / ρ * (R / ρ) ^ N) := by
    intro N p hp
    have hpL := norm_le_abs_corners_of_mem_rectangle (rectangleBorder_subset_rectangle z w hp)
    have hpρ := hborder p hp
    simp only [hFdef, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖p‖ ^ m ≤ L ^ m := pow_le_pow_left₀ (norm_nonneg _) hpL m
    have h2 : ‖cexp ((t : ℂ) * p)‖ ≤ Real.exp (|t| * L) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.2 ?_
      have hre : ((t : ℂ) * p).re = t * p.re := by simp
      rw [hre]
      calc t * p.re ≤ |t * p.re| := le_abs_self _
        _ = |t| * |p.re| := abs_mul _ _
        _ ≤ |t| * L := mul_le_mul_of_nonneg_left ((abs_re_le_norm p).trans hpL) (abs_nonneg _)
    have h3 : |b N| * (‖p‖ ^ (N + 1))⁻¹ ≤ M / ρ * (R / ρ) ^ N := by
      have hpN : ρ ^ (N + 1) ≤ ‖p‖ ^ (N + 1) := pow_le_pow_left₀ hρ0.le hpρ _
      calc |b N| * (‖p‖ ^ (N + 1))⁻¹ ≤ M * R ^ N * (ρ ^ (N + 1))⁻¹ :=
            mul_le_mul (hb N) (inv_anti₀ (by positivity) hpN) (by positivity) (by positivity)
        _ = M / ρ * (R / ρ) ^ N := by rw [div_pow, pow_succ]; field_simp
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (by positivity)
      (by positivity)
  have hhas := hasSum_rectangleIntegral hF hB hbd
  rw [hsum] at hhas
  have hterm : ∀ N, RectangleIntegral (F N) z w = 2 * π * I *
      (if m ≤ N then (b N : ℂ) * ((t : ℂ) ^ (N - m) / ((N - m).factorial : ℂ)) else 0) := by
    intro N
    have h := rectangleIntegral_pow_mul_cexp_mul_inv_pow hz hz' hw hw' (t : ℂ) m N
    have e : F N = fun p => (b N : ℂ) * (p ^ m * cexp (t * p) * (p ^ (N + 1))⁻¹) := by
      funext p; simp only [hFdef]; ring
    rw [e, rectangleIntegral_const_mul', h]
    split_ifs <;> ring
  simp_rw [hterm] at hhas
  refine hhas.unique ?_
  refine HasSum.mul_left (2 * π * I) ?_
  rw [← hasSum_nat_add_iff' m]
  have hzero : ∀ i ∈ Finset.range m,
      (if m ≤ i then (b i : ℂ) * ((t : ℂ) ^ (i - m) / ((i - m).factorial : ℂ)) else 0) = 0 :=
    fun i hi => if_neg (by simp at hi; omega)
  rw [Finset.sum_eq_zero hzero, sub_zero]
  have hser := (summable_borelTerm (geometricCoeffBound_shift_add hb m) t).hasSum
  rw [iteratedDeriv_borelSeries hb m]
  have hc := (Complex.hasSum_ofReal).2 hser
  refine hc.congr_fun fun j => ?_
  rw [if_pos (by omega), Nat.add_sub_cancel]
  simp only [dividedPowerFn]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
