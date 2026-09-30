import GaloisForLFunctions.RHTower.WeilFullConeExtremePoint

/-!
# `Λ` is an exposed point of the full Weil cone

Let `K = Φ ⋆ Φ̃` be the autocorrelation of Riemann's kernel (`riemannKernelAutocorr`), a positive
function with double-exponential decay, and put
`ℓ(v) = Σ_{n ≥ 2} v(n) n^{−1/2} (K(log n) + K(−log n))`.

**Theorem** (`weilFullCone_exposed_at_vonMangoldt`, unconditional). Let `lam` be Weil-positive
with the pole term. Then `ℓ(lam − Λ) ≤ 0`, and `ℓ(lam − Λ) = 0` only if `lam = Λ` on `n ≥ 2`.

No growth hypothesis is needed. The level-wise box `|lam(n)| ≤ √n (log n + C₀)` of Weil-positive
weights gives `Σ |lam(n) − Λ(n)| n^{−2} < ∞` (`summable_sub_vonMangoldt_div_sq`), which is all
the injectivity of the Riemann-kernel transform uses. For the same reason `Λ` is an extreme point
with no hypothesis on the direction (`weilFullCone_extreme_at_vonMangoldt`).

So the Weil cone lies in the half-space `ℓ(lam) ≤ ℓ(Λ)` and touches its boundary only at `Λ`:
`Λ` is the unique maximizer of `ℓ` over the cone. This strengthens both the majorant rigidity
(`eq_vonMangoldt_of_weilPositiveFull_of_ge`: `K > 0` makes `ℓ(w) > 0` for a nonzero majorant
direction) and extremality (`eq_zero_of_weilPositiveFull_add_of_sub`).

The proof tests Weil positivity on `Φχ_L + εH`.
* At `ε = 0` the zero side tends to `0`, so `ℓ(lam − Λ) ≤ 0`.
* If `ℓ(lam − Λ) = 0`, the first variation in `ε` must vanish for both signs of `ε`. So the pairing
  with `Φ ⋆ H` vanishes for every test `H`, and the injectivity of the Riemann-kernel transform
  gives `lam = Λ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-- The autocorrelation `K(y) = ∫ Φ(t) Φ(t − y) dt` of Riemann's kernel. -/
def riemannKernelAutocorr (y : ℝ) : ℝ := crossCorr riemannKernelReal riemannKernelReal y

theorem integrable_exp_neg_two_abs_sub (y : ℝ) :
    Integrable fun t : ℝ => Real.exp (-(2 * |t - y|)) := by
  have h := (integrable_exp_neg_abs.comp_mul_left' (two_ne_zero (α := ℝ))).comp_sub_right y
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [abs_mul, abs_two]

theorem exp_neg_two_abs_sub_integral (y : ℝ) :
    ∫ t : ℝ, Real.exp (-(2 * |t - y|)) = ∫ v : ℝ, Real.exp (-(2 * |v|)) :=
  integral_sub_right_eq_self (μ := volume) (fun v : ℝ => Real.exp (-(2 * |v|))) y

/-- `|Z₁(t) Z₂(t − y)| ≤ A B e^{−2|y|} (e^{−2|t−y|} + e^{−2|t|})` when `|Z₁| ≤ A e^{−2|·|}`,
`|Z₂| ≤ B e^{−4|·|}` or the roles are swapped; the `L¹` bound of the correlation. -/
theorem abs_integral_mul_shift_le {Z₁ Z₂ : ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h₁ : ∀ t, |Z₁ t| ≤ A * Real.exp (-(2 * |t|))) (h₂ : ∀ t, |Z₂ t| ≤ B * Real.exp (-(4 * |t|)))
    (y : ℝ) :
    |∫ t, Z₁ t * Z₂ (t - y)| ≤
      A * B * (∫ v : ℝ, Real.exp (-(2 * |v|))) * Real.exp (-(2 * |y|)) := by
  rw [← Real.norm_eq_abs]
  have hmaj : Integrable fun t : ℝ => A * B * Real.exp (-(2 * |y|)) * Real.exp (-(2 * |t - y|)) :=
    (integrable_exp_neg_two_abs_sub y).const_mul _
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    have e1 := h₁ t
    have e2 := h₂ (t - y)
    have hexp : Real.exp (-(2 * |t|)) * Real.exp (-(4 * |t - y|)) ≤
        Real.exp (-(2 * |y|)) * Real.exp (-(2 * |t - y|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : |y| ≤ |t| + |t - y| := by
        rw [abs_le]; constructor <;>
          linarith [le_abs_self t, neg_abs_le t, le_abs_self (t - y), neg_abs_le (t - y)]
      linarith [abs_nonneg (t - y)]
    calc |Z₁ t| * |Z₂ (t - y)| ≤ (A * Real.exp (-(2 * |t|))) * (B * Real.exp (-(4 * |t - y|))) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = A * B * (Real.exp (-(2 * |t|)) * Real.exp (-(4 * |t - y|))) := by ring
      _ ≤ A * B * (Real.exp (-(2 * |y|)) * Real.exp (-(2 * |t - y|))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  · rw [integral_const_mul, exp_neg_two_abs_sub_integral]; ring

theorem integrable_riemannKernel_mul_shift {Z : ℝ → ℝ} {A : ℝ} (hZc : Continuous Z) (hA : 0 ≤ A)
    (hZ : ∀ t, |Z t| ≤ A * Real.exp (-(2 * |t|))) (y : ℝ) :
    Integrable fun t => Z t * riemannKernelReal (t - y) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  have hmaj : Integrable fun t : ℝ => A * C * Real.exp (-(2 * |t - y|)) :=
    (integrable_exp_neg_two_abs_sub y).const_mul _
  refine hmaj.mono' (hZc.mul (continuous_riemannKernelReal.comp
    (continuous_id.sub continuous_const))).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _)]
  have e1 := hZ t
  have e2 := hC (t - y)
  have hexp : Real.exp (-(2 * |t|)) * Real.exp (-(4 * |t - y|)) ≤ Real.exp (-(2 * |t - y|)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg t, abs_nonneg (t - y)]
  calc |Z t| * riemannKernelReal (t - y) ≤ (A * Real.exp (-(2 * |t|))) * (C * Real.exp (-(4 * |t - y|))) :=
        mul_le_mul e1 e2 (riemannKernelReal_pos _).le (by positivity)
    _ = A * C * (Real.exp (-(2 * |t|)) * Real.exp (-(4 * |t - y|))) := by ring
    _ ≤ A * C * Real.exp (-(2 * |t - y|)) := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Decay of the autocorrelation and of its truncation defect.** For some `C₁, C₂ ≥ 0`,
`|Φχ_L ⋆ Φχ_L~ − K|(y) ≤ C₁ e^{−2(L−1)} e^{−2|y|}` and `|K(y)| ≤ C₂ e^{−2|y|}`. -/
theorem exists_riemannKernelAutocorr_decay :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ L y, |crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y -
        riemannKernelAutocorr y| ≤ C₁ * Real.exp (-(2 * (L - 1))) * Real.exp (-(2 * |y|))) ∧
      ∀ y, |riemannKernelAutocorr y| ≤ C₂ * Real.exp (-(2 * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  set G₂ := ∫ v : ℝ, Real.exp (-(2 * |v|)) with hG₂
  have hG₂0 : 0 ≤ G₂ := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨2 * (C * C * G₂), C * C * G₂, by positivity, by positivity, fun L => ?_, fun y =>
    abs_integral_mul_shift_le hC0 hC0 (fun t => by
      rw [abs_of_pos (riemannKernelReal_pos t)]
      exact (hC t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by nlinarith [abs_nonneg t])) hC0)) (fun t => by
      rw [abs_of_pos (riemannKernelReal_pos t)]; exact hC t) y⟩
  set E := Real.exp (-(2 * (L - 1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- pointwise bounds
  have hΦ2 : ∀ t, |riemannKernelReal t| ≤ C * Real.exp (-(2 * |t|)) := by
    intro t
    rw [abs_of_pos (riemannKernelReal_pos t)]
    exact (hC t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t])) hC0)
  have hΦ4 : ∀ t, |riemannKernelReal t| ≤ C * Real.exp (-(4 * |t|)) := fun t => by
    rw [abs_of_pos (riemannKernelReal_pos t)]; exact hC t
  have hU4 : ∀ t, |truncatedRiemannKernelReal L t| ≤ C * Real.exp (-(4 * |t|)) := by
    intro t
    rw [abs_of_nonneg (truncatedRiemannKernelReal_nonneg L t)]
    have := (riemannKernelReal_sub_truncated_le hC L t).1
    linarith [hC t]
  have hD2 : ∀ t, |truncatedRiemannKernelReal L t - riemannKernelReal t| ≤ C * E * Real.exp (-(2 * |t|)) := by
    intro t
    obtain ⟨h1, h2⟩ := riemannKernelReal_sub_truncated_le hC L t
    rw [abs_sub_comm, abs_of_nonneg h1]; exact h2
  -- the defect of the autocorrelation
  have hUc := continuous_truncatedRiemannKernelReal L
  have hUcs := hasCompactSupport_truncatedRiemannKernelReal L
  have hΦc := continuous_riemannKernelReal
  have hDc : Continuous fun t => truncatedRiemannKernelReal L t - riemannKernelReal t := hUc.sub hΦc
  set D : ℝ → ℝ := fun y => crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y -
    riemannKernelAutocorr y with hDdef
  have hDbound : ∀ y, |D y| ≤ 2 * (C * C * G₂) * E * Real.exp (-(2 * |y|)) := by
    intro y
    have iUU := integrable_translate_prod hUc hUcs hUc y
    have iΦΦ := integrable_riemannKernel_mul_shift hΦc hC0 hΦ2 y
    have i1 := integrable_mul_translate_right hDc hUc hUcs y
    have i2 : Integrable fun t => riemannKernelReal t *
        (truncatedRiemannKernelReal L (t - y) - riemannKernelReal (t - y)) := by
      have h := (integrable_riemannKernel_mul_shift hDc (by positivity) hD2 (-y)).comp_sub_right y
      refine h.congr (Eventually.of_forall fun t => ?_)
      simp only
      rw [show t - y - -y = t by ring]; ring
    have hsplit : D y = (∫ t, (truncatedRiemannKernelReal L t - riemannKernelReal t) *
        truncatedRiemannKernelReal L (t - y)) + ∫ t, riemannKernelReal t *
          (truncatedRiemannKernelReal L (t - y) - riemannKernelReal (t - y)) := by
      simp only [hDdef, riemannKernelAutocorr, crossCorr]
      rw [← integral_sub iUU iΦΦ, ← integral_add i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only; ring
    have hsecond : (∫ t, riemannKernelReal t *
        (truncatedRiemannKernelReal L (t - y) - riemannKernelReal (t - y))) =
        ∫ s, (truncatedRiemannKernelReal L s - riemannKernelReal s) * riemannKernelReal (s - -y) := by
      rw [← integral_add_right_eq_self (μ := volume) (fun t => riemannKernelReal t *
        (truncatedRiemannKernelReal L (t - y) - riemannKernelReal (t - y))) y]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only
      rw [show s + y - y = s by ring, show s - -y = s + y by ring]; ring
    have b1 := abs_integral_mul_shift_le (by positivity) hC0 hD2 hU4 y
    have b2 := abs_integral_mul_shift_le (by positivity) hC0 hD2 hΦ4 (-y)
    rw [abs_neg] at b2
    rw [hsplit, hsecond]
    calc _ ≤ |∫ t, (truncatedRiemannKernelReal L t - riemannKernelReal t) *
          truncatedRiemannKernelReal L (t - y)| +
        |∫ s, (truncatedRiemannKernelReal L s - riemannKernelReal s) * riemannKernelReal (s - -y)| :=
          abs_add_le _ _
      _ ≤ _ := by linarith
  intro y
  exact hDbound y

/-- **Truncation limit for the autocorrelation pairing.**
`|T_w(Φχ_L, Φχ_L) − ℓ(w)| ≤ K e^{−2(L−1)}`. -/
theorem exists_abs_atomPairing_truncatedAutocorr_sub_le {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) -
        atomPairing w riemannKernelAutocorr| ≤ K * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hDbound', hKbound⟩ := exists_riemannKernelAutocorr_decay
  set Sw := ∑' n : ℕ, |w n| / (n : ℝ) ^ 2 with hSw
  have hSw0 : 0 ≤ Sw := tsum_nonneg fun _ => by positivity
  refine ⟨2 * C₁ * Sw, by positivity, fun L => ?_⟩
  set E := Real.exp (-(2 * (L - 1))) with hE
  set D : ℝ → ℝ := fun y => crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y -
    riemannKernelAutocorr y with hDdef
  have hDbound : ∀ y, |D y| ≤ (C₁ * E) * Real.exp (-(2 * |y|)) := hDbound' L
  obtain ⟨hsD, hDsum⟩ := summable_atomPairing_of_decay hw2 hDbound
  obtain ⟨hsK, -⟩ := summable_atomPairing_of_decay hw2 hKbound
  have hU : ∀ t, |L| < |t| → truncatedRiemannKernelReal L t = 0 := fun t ht =>
    truncatedRiemannKernelReal_eq_zero (lt_of_le_of_lt (le_abs_self L) ht)
  have hsU := summable_atomPairing w
    (g := crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L))
    (R := |L| + |L|) fun y hy => crossCorr_eq_zero hU hU hy
  have hsub : atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) -
      atomPairing w riemannKernelAutocorr = atomPairing w D := by
    unfold atomPairing
    rw [← hsU.tsum_sub hsK]
    refine tsum_congr fun n => ?_
    simp only [hDdef]; ring
  rw [hsub]
  calc |atomPairing w D| ≤ 2 * (C₁ * E) * Sw := hDsum
    _ = _ := by rw [hE]; ring

theorem riemannKernelAutocorr_pos (y : ℝ) : 0 < riemannKernelAutocorr y := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  have hΦ2 : ∀ t, |riemannKernelReal t| ≤ C * Real.exp (-(2 * |t|)) := by
    intro t
    rw [abs_of_pos (riemannKernelReal_pos t)]
    exact (hC t).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t])) hC0)
  have hint := integrable_riemannKernel_mul_shift continuous_riemannKernelReal hC0 hΦ2 y
  unfold riemannKernelAutocorr crossCorr
  rw [integral_pos_iff_support_of_nonneg (fun t => mul_nonneg (riemannKernelReal_pos t).le
    (riemannKernelReal_pos _).le) hint]
  have hsupp : Function.support (fun t => riemannKernelReal t * riemannKernelReal (t - y)) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (mul_pos (riemannKernelReal_pos t) (riemannKernelReal_pos _)).ne'
  rw [hsupp, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- `K e^{−2(L−1)} ≤ δ` for all large `L`. -/
theorem exists_forall_mul_exp_le {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → K * Real.exp (-(2 * (L - 1))) ≤ δ := by
  refine ⟨1 + K / δ, fun L hL => ?_⟩
  have h1 : 2 * K / δ ≤ Real.exp (2 * (L - 1)) := by
    have := Real.add_one_le_exp (2 * (L - 1))
    have : K / δ ≤ L - 1 := by linarith
    have hKδ : 0 ≤ K / δ := div_nonneg hK hδ.le
    have : 2 * K / δ = 2 * (K / δ) := by ring
    linarith
  have hE : Real.exp (-(2 * (L - 1))) * Real.exp (2 * (L - 1)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hδ] at h1
  have hEpos := Real.exp_pos (-(2 * (L - 1)))
  nlinarith

theorem contDiff_ofReal_truncatedRiemannKernelReal (L : ℝ) :
    ContDiff ℝ 2 fun u => (truncatedRiemannKernelReal L u : ℂ) := by
  have h : (fun u => (truncatedRiemannKernelReal L u : ℂ)) = truncatedRiemannKernel L :=
    funext fun u => (truncatedRiemannKernel_eq L u).symm
  rw [h]; exact contDiff_nearRadicalTest L _

/-- The one-sided bound: a Weil-positive `Λ + w` has `T_w(F) ≤ Re W(F, F)`. -/
theorem atomPairing_le_re_W {w : ℕ → ℝ}
    (hW : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) :
    atomPairing w (crossCorr F F) ≤ (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
  have h := hW _ hF (hFc.comp_left Complex.ofReal_zero)
  rw [re_weilFullFunctional_add_eq w hF hFc] at h
  linarith

/-- **Supporting hyperplane.** Every Weil-positive `lam` in the class `Σ|lam − Λ|n^{−2} < ∞`
satisfies `ℓ(lam − Λ) ≤ 0`. -/
theorem atomPairing_riemannKernelAutocorr_nonpos {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hw2 : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2) :
    atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr ≤ 0 := by
  set w : ℕ → ℝ := fun n => lam n - ArithmeticFunction.vonMangoldt n with hw
  have hW' : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n := by
    have : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n) = lam := funext fun n => by
      simp only [hw]; ring
    rw [this]; exact hW
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_abs_atomPairing_truncatedAutocorr_sub_le hw2
  by_contra hpos
  push Not at hpos
  set ℓ := atomPairing w riemannKernelAutocorr
  obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := ℓ / 3) (by linarith)
  obtain ⟨L₂, hL₂⟩ := exists_forall_mul_exp_le hK₀0 (δ := ℓ / 3) (by linarith)
  set L := max L₁ L₂
  have h1 := hL₁ L (le_max_left _ _)
  have h2 := hL₂ L (le_max_right _ _)
  have h3 := hK₀ L
  have h4 := atomPairing_le_re_W hW' (contDiff_ofReal_truncatedRiemannKernelReal L)
    (hasCompactSupport_truncatedRiemannKernelReal L)
  have h5 : (zetaZeroConfig.W (fun u => (truncatedRiemannKernelReal L u : ℂ))
      (fun u => (truncatedRiemannKernelReal L u : ℂ))).re ≤
      (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 := by
    have h : (fun u => (truncatedRiemannKernelReal L u : ℂ)) = truncatedRiemannKernel L :=
      funext fun u => (truncatedRiemannKernel_eq L u).symm
    rw [h]
    obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    exact (Complex.re_le_norm _).trans (norm_W_le_of_zero_bound
      (truncatedRiemannTailEnergy_nonneg L) (truncatedRiemannKernel_zero_bound L hΛ'))
  have hℓ := (abs_le.mp h3).1
  linarith

/-- **Equality only at `Λ`.** If `ℓ(lam − Λ) = 0` for a Weil-positive `lam` in the class, then
`lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_atomPairing_eq_zero {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hw2 : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2)
    (h0 : atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr = 0) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set w : ℕ → ℝ := fun n => lam n - ArithmeticFunction.vonMangoldt n with hw
  have hW' : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n := by
    have : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n) = lam := funext fun n => by
      simp only [hw]; ring
    rw [this]; exact hW
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_abs_atomPairing_truncatedAutocorr_sub_le hw2
  have hstep1 : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H →
      atomPairing w (crossCorr riemannKernelReal H) = 0 := by
    intro H hH hHc
    obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_atomPairing_truncated_sub_le hw2 hH.continuous hHc
    set T := atomPairing w (crossCorr riemannKernelReal H) with hT
    set T2 := atomPairing w (crossCorr H H)
    set EH := testEnergy H
    have hS0 := zetaInvSqSum_nonneg
    set M₂ := (5 / 4) * zetaInvSqSum * (2 * EH ^ 2) + |T2| with hM₂
    have hM₂0 : 0 ≤ M₂ := by positivity
    have hsign : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * T ≤ 0 := by
      intro s hs
      have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
      by_contra hpos
      push Not at hpos
      set τ := s * T with hτ
      set η := τ / (2 * M₂ + 2) with hη
      have hηpos : 0 < η := by positivity
      obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := η * τ / 16) (by positivity)
      obtain ⟨L₂, hL₂⟩ := exists_forall_mul_exp_le hK₀0 (δ := η * τ / 8) (by positivity)
      obtain ⟨L₃, hL₃⟩ := exists_forall_mul_exp_le hK₁0 (δ := τ / 8) (by positivity)
      set L := max (max L₁ L₂) L₃
      have hE := hL₁ L (le_trans (le_max_left _ _) (le_max_left _ _))
      have hT0 : |atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L))|
          ≤ η * τ / 8 := by
        have := (hK₀ L).trans (hL₂ L (le_trans (le_max_right _ _) (le_max_left _ _)))
        rwa [h0, sub_zero] at this
      have hT1 : |atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) - T| ≤ τ / 8 :=
        (hK₁ L).trans (hL₃ L (le_max_right _ _))
      set ε := s * η with hε
      have hεabs : |ε| = η := by rw [hε, abs_mul, hsabs, one_mul, abs_of_pos hηpos]
      have hone := atomPairing_le_re_W hW' (contDiff_perturbedKernel L ε hH)
        (hasCompactSupport_perturbedKernel L ε hHc)
      rw [atomPairing_perturbedKernel w L ε hH.continuous hHc] at hone
      have hWb := (Complex.re_le_norm _).trans (norm_W_perturbedKernel_le L ε hH hHc)
      rw [hεabs] at hWb
      set EL := truncatedRiemannTailEnergy L
      set T0 := atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L))
      set T1 := atomPairing w (crossCorr (truncatedRiemannKernelReal L) H)
      have hsq : (EL + η * EH) ^ 2 ≤ 2 * EL ^ 2 + 2 * (η ^ 2 * EH ^ 2) := by
        nlinarith [sq_nonneg (EL - η * EH)]
      have hε2 : ε ^ 2 = η ^ 2 := by rw [hε, mul_pow, hs2, one_mul]
      have hkey : 2 * η * (s * T1) ≤ η * τ / 4 + η ^ 2 * M₂ := by
        have hmain : T0 + 2 * ε * T1 + ε ^ 2 * T2 ≤
            (5 / 4) * zetaInvSqSum * (EL + η * EH) ^ 2 := hone.trans hWb
        rw [hε2] at hmain
        have hb : (5 / 4) * zetaInvSqSum * (EL + η * EH) ^ 2 ≤
            2 * ((5 / 4) * zetaInvSqSum * EL ^ 2) + η ^ 2 * ((5 / 4) * zetaInvSqSum * (2 * EH ^ 2)) := by
          have h := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (5 / 4) * zetaInvSqSum)
          have e : (5 / 4) * zetaInvSqSum * (2 * EL ^ 2 + 2 * (η ^ 2 * EH ^ 2)) =
              2 * ((5 / 4) * zetaInvSqSum * EL ^ 2) +
                η ^ 2 * ((5 / 4) * zetaInvSqSum * (2 * EH ^ 2)) := by ring
          linarith
        have hT0' : -T0 ≤ η * τ / 8 := (neg_le_abs T0).trans hT0
        have hT2' : η ^ 2 * (-T2) ≤ η ^ 2 * |T2| :=
          mul_le_mul_of_nonneg_left (neg_le_abs T2) (sq_nonneg η)
        have hε' : 2 * ε * T1 = 2 * η * (s * T1) := by rw [hε]; ring
        have hM : η ^ 2 * M₂ = η ^ 2 * ((5 / 4) * zetaInvSqSum * (2 * EH ^ 2)) + η ^ 2 * |T2| := by
          rw [hM₂]; ring
        have hneg : η ^ 2 * (-T2) = -(η ^ 2 * T2) := by ring
        linarith
      have hsT1 : s * T1 ≤ τ / 8 + η * M₂ / 2 := by
        have e : 2 * η * (τ / 8 + η * M₂ / 2) = η * τ / 4 + η ^ 2 * M₂ := by ring
        have : 2 * η * (s * T1) ≤ 2 * η * (τ / 8 + η * M₂ / 2) := by rw [e]; exact hkey
        exact le_of_mul_le_mul_left this (by positivity)
      have hηM : η * M₂ ≤ τ / 2 := by
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have e : τ / 2 * (2 * M₂ + 2) = τ * M₂ + τ := by ring
        linarith
      have hdiff : s * T ≤ s * T1 + τ / 8 := by
        have h1 : s * (T - T1) ≤ |T - T1| := by
          calc s * (T - T1) ≤ |s * (T - T1)| := le_abs_self _
            _ = |T - T1| := by rw [abs_mul, hsabs, one_mul]
        rw [abs_sub_comm] at h1
        have e : s * T = s * T1 + s * (T - T1) := by ring
        linarith
      linarith
    have h1 := hsign 1 (Or.inl rfl)
    have h2 := hsign (-1) (Or.inr rfl)
    linarith
  have := eq_zero_of_forall_atomPairing_riemannKernel_eq_zero hw2 hstep1
  intro n hn
  have h : lam n - ArithmeticFunction.vonMangoldt n = 0 := this n hn
  linarith

/-! ## The supporting inequality for every Weil-positive system -/

/-- Full-cone Weil positivity implies the corpus's polar, level-wise Weil positivity. -/
theorem weilPositive_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    WeilPositive lam := by
  intro a ha f hf hfs hp hm
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  obtain ⟨-, -, hks, -, -⟩ := weilTest_self_data hf hfs
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  set k := EF.weilTest f f with hk
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  rw [integral_weilAtomSymbol_eq_sub hf hfs lam]
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  rw [← hN] at hWf
  have hre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hWf, Complex.ofReal_re]; field_simp
  rw [hre]
  have hfull := hW f hf hfc
  rw [weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional hf hfc, Complex.sub_re] at hfull
  have hvan : ∀ n : ℕ, N < n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * a) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * a))
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hlog : 2 * a < Real.log n := by rw [Real.lt_log_iff_exp_lt hnpos]; exact hn'
    have hout : ∀ y : ℝ, 2 * a < |y| → k y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hks hmem
      rw [mem_Icc] at this
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0] at hy; linarith [this.2]
      · rw [abs_of_neg h0] at hy; linarith [this.1]
    have hl0 : 0 < Real.log n := by linarith
    exact ⟨hout _ (by rw [abs_of_pos hl0]; exact hlog),
      hout _ (by rw [abs_neg, abs_of_pos hl0]; exact hlog)⟩
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re =
      ∑ n ∈ Finset.Icc 2 N, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
        (k (Real.log n) + k (-Real.log n)).re := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N) (fun n hn => ?_), Complex.re_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1, Complex.re_ofReal_mul]
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · rw [if_neg (by omega), Complex.ofReal_zero, zero_mul]
      · rw [(hvan n h).1, (hvan n h).2, add_zero, mul_zero]
  rw [hsum] at hfull
  have hπ : 0 < π := Real.pi_pos
  nlinarith

/-- Polar Weil-positive weights have `Σ |lam(n) − Λ(n)| n^{−2} < ∞`, by the level-wise box
`|lam(n)| ≤ √n (log n + C₀)`. -/
theorem summable_sub_vonMangoldt_div_sq_of_weilPositive {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := abs_le_of_weilPositive hW
  set B := 8 + |C₀| with hB
  have hbound : ∀ n : ℕ, |lam (n + 2) - ArithmeticFunction.vonMangoldt (n + 2)| / ((n + 2 : ℕ) : ℝ) ^ 2 ≤
      B * (((n + 2 : ℕ) : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by
    intro n
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((n + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
    rw [← hx]
    have hx1 : 1 ≤ x := by rw [hx]; push_cast; linarith
    have hx0 : 0 < x := by linarith
    have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
      linarith [show x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) by ring]
    have hlam := hC₀ (n + 2) (by omega)
    rw [← hx] at hlam
    have hΛ : (ArithmeticFunction.vonMangoldt (n + 2) : ℝ) ≤ Real.log x := by
      rw [hx]; exact ArithmeticFunction.vonMangoldt_le_log
    have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt (n + 2) := ArithmeticFunction.vonMangoldt_nonneg
    have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have h14 : x ^ (1 / 4 : ℝ) ≤ x ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h12 : x ^ (1 / 2 : ℝ) ≤ x ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hmul : x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    have h54 : x ^ (3 / 4 : ℝ) * x ^ (5 / 4 : ℝ) = x ^ 2 := by
      rw [← Real.rpow_add hx0]; norm_num
    have hpos14 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
    have hpos12 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hpos54 : 0 < x ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hlogpos : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hw : |lam (n + 2) - ArithmeticFunction.vonMangoldt (n + 2)| ≤ B * x ^ (3 / 4 : ℝ) := by
      have h1 : |lam (n + 2) - ArithmeticFunction.vonMangoldt (n + 2)| ≤
          |lam (n + 2)| + ArithmeticFunction.vonMangoldt (n + 2) := by
        have := abs_sub (lam (n + 2)) (ArithmeticFunction.vonMangoldt (n + 2))
        rwa [abs_of_nonneg hΛ0] at this
      have h2 : |lam (n + 2)| ≤ x ^ (1 / 2 : ℝ) * (4 * x ^ (1 / 4 : ℝ) + |C₀|) := by
        rw [← hsq]
        refine hlam.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
        linarith [le_abs_self C₀]
      have h3 : x ^ (1 / 2 : ℝ) * (4 * x ^ (1 / 4 : ℝ) + |C₀|) ≤ 4 * x ^ (3 / 4 : ℝ) + |C₀| * x ^ (3 / 4 : ℝ) := by
        rw [mul_add, show x ^ (1 / 2 : ℝ) * (4 * x ^ (1 / 4 : ℝ)) = 4 * (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) by ring,
          hmul]
        nlinarith [abs_nonneg C₀]
      rw [hB]
      nlinarith
    rw [div_le_iff₀ (by positivity), show x ^ 2 = x ^ (3 / 4 : ℝ) * x ^ (5 / 4 : ℝ) from h54.symm]
    calc |lam (n + 2) - ArithmeticFunction.vonMangoldt (n + 2)| ≤ B * x ^ (3 / 4 : ℝ) := hw
      _ = B * (x ^ (5 / 4 : ℝ))⁻¹ * (x ^ (3 / 4 : ℝ) * x ^ (5 / 4 : ℝ)) := by
          field_simp
  have hs : Summable fun n : ℕ => B * (((n + 2 : ℕ) : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by
    have := (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4))
    exact (this.mul_left B).congr fun n => by push_cast; ring_nf
  refine (summable_nat_add_iff 2).mp (Summable.of_nonneg_of_le (fun _ => by positivity) hbound hs)


/-- Full-cone Weil-positive weights have `Σ |lam(n) − Λ(n)| n^{−2} < ∞`. -/
theorem summable_sub_vonMangoldt_div_sq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2 :=
  summable_sub_vonMangoldt_div_sq_of_weilPositive (weilPositive_of_weilPositiveFull hW)
/-- **Supporting hyperplane, unconditional.** Every Weil-positive `lam` satisfies
`Σ_{n ≥ 2} lam(n) n^{−1/2}(K(log n) + K(−log n)) ≤ Σ_{n ≥ 2} Λ(n) n^{−1/2}(K(log n) + K(−log n))`,
in the form `ℓ(lam − Λ) ≤ 0`. -/
theorem atomPairing_riemannKernelAutocorr_nonpos_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr ≤ 0 :=
  atomPairing_riemannKernelAutocorr_nonpos hW (summable_sub_vonMangoldt_div_sq hW)

/-- **`Λ` is an exposed point of the full Weil cone.** Every Weil-positive `lam` has
`ℓ(lam − Λ) ≤ 0`, with equality only if `lam = Λ` on `n ≥ 2`. The exposing functional `ℓ` has
the strictly positive kernel `Φ ⋆ Φ̃`. No summability hypothesis: Weil positivity bounds
`|lam(n)| ≤ √n (log n + C₀)`. -/
theorem weilFullCone_exposed_at_vonMangoldt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr ≤ 0 ∧
      (atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr = 0 →
        ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) :=
  ⟨atomPairing_riemannKernelAutocorr_nonpos hW (summable_sub_vonMangoldt_div_sq hW),
    eq_vonMangoldt_of_weilPositiveFull_of_atomPairing_eq_zero hW (summable_sub_vonMangoldt_div_sq hW)⟩

/-- **`Λ` is an extreme point of the full Weil cone**, with no hypothesis on `w`: if `Λ + w` and
`Λ − w` are both Weil-positive, then `w(n) = 0` for all `n ≥ 2`. -/
theorem weilFullCone_extreme_at_vonMangoldt {w : ℕ → ℝ}
    (hp : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) :
    ∀ n, 2 ≤ n → w n = 0 := by
  have hw2 := summable_sub_vonMangoldt_div_sq hp
  simp only [add_sub_cancel_left] at hw2
  exact eq_zero_of_weilPositiveFull_add_of_sub hw2 hp hm

/-! ## RH criteria -/

/-- Under RH the zero side is `Σ m_ρ |f̂(γ_ρ)|² ≥ 0` for every test, so `Λ` is Weil-positive in the
full cone. -/
theorem weilPositiveFull_vonMangoldt_of_riemannHypothesis (hRH : RiemannHypothesis) :
    WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  intro f hf hfc
  rw [← zeta_W_eq_weilFullFunctional hf hfc]
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨hsum, -⟩ := WeilEF.EF_lit_zetaZeroConfig _ hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (EF.weilTest f f) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  rw [hterm] at hsum
  rw [ZeroConfig.W, Complex.re_tsum hsum]
  refine tsum_nonneg fun ρ => ?_
  have hre : (ρ : ℂ).re = 1 / 2 := Zeta23.RH_implies_on_line hRH ρ.2
  have hreal : conj (gammaOf (ρ : ℂ)) = gammaOf ρ := by
    apply Complex.conj_eq_iff_im.mpr
    rw [WeilEF.gammaOf_im, hre]; ring
  simp only [ZeroConfig.Wsummand, hreal]
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

/-- **Weil's criterion in the full cone.** -/
theorem riemannHypothesis_iff_weilPositiveFull_vonMangoldt :
    RiemannHypothesis ↔ WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨weilPositiveFull_vonMangoldt_of_riemannHypothesis, fun h =>
    riemannHypothesis_iff_weilPositive_vonMangoldt.mpr (weilPositive_of_weilPositiveFull h)⟩

theorem weilFullFunctional_congr {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n)
    (k : ℝ → ℂ) : weilFullFunctional lam k = weilFullFunctional lam' k := by
  unfold weilFullFunctional
  congr 3
  funext n
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, if_pos hn, h n hn]
  · rw [if_neg hn, if_neg hn]

/-- **RH as an extremal value of `ℓ` on the Weil cone.** RH holds iff some full-cone
Weil-positive `lam` reaches `ℓ(lam) ≥ ℓ(Λ)`. Such a `lam` then equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_atomPairing_nonneg :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      0 ≤ atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr := by
  constructor
  · intro hRH
    refine ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH, ?_⟩
    simp only [sub_self]
    unfold atomPairing
    simp
  · rintro ⟨lam, hW, hge⟩
    obtain ⟨hle, heq⟩ := weilFullCone_exposed_at_vonMangoldt hW
    have h := heq (le_antisymm hle hge)
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

/-! ## Quantitative exposedness -/

theorem tendsto_mul_exp_neg_atTop (K : ℝ) :
    Tendsto (fun L : ℝ => K * Real.exp (-(2 * (L - 1)))) atTop (𝓝 0) := by
  have h : Tendsto (fun L : ℝ => 2 * (L - 1)) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b / 2 + 1, fun L hL => by linarith⟩
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h).const_mul K
  simpa [Function.comp_def] using this

theorem tendsto_of_abs_sub_le {f : ℝ → ℝ} {a K : ℝ}
    (h : ∀ L, |f L - a| ≤ K * Real.exp (-(2 * (L - 1)))) : Tendsto f atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun L => by rw [Real.norm_eq_abs]; exact h L)
    (tendsto_mul_exp_neg_atTop K)

theorem tendsto_nearRadicalEnergy :
    Tendsto (fun L : ℝ => (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨L₀, hL₀⟩ := exists_nearRadicalEnergy_le (ε := δ / 2) (by positivity)
  refine ⟨L₀, fun L hL => ?_⟩
  have h0 : 0 ≤ (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 := by
    have := zetaInvSqSum_nonneg; positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith [hL₀ L hL]

/-- **Quantitative exposedness.** For a Weil-positive `lam` with deviation `w = lam − Λ`
(`Σ|w|n^{−2} < ∞`) and a real `C²` compactly supported test `H`,
`T_w(Φ, H)² ≤ (ℓ(Λ) − ℓ(lam)) · ((5/4) S E_H² − T_w(H, H))`.
The `ℓ`-deficit controls every Riemann-kernel moment of the deviation. -/
theorem sq_atomPairing_riemannKernel_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hw2 : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2)
    {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
        (crossCorr riemannKernelReal H) ^ 2 ≤
      (-atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) riemannKernelAutocorr) *
        ((5 / 4) * zetaInvSqSum * testEnergy H ^ 2 -
          atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) (crossCorr H H)) := by
  set w : ℕ → ℝ := fun n => lam n - ArithmeticFunction.vonMangoldt n with hw
  have hW' : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n := by
    have : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n) = lam := funext fun n => by
      simp only [hw]; ring
    rw [this]; exact hW
  set ℓ := atomPairing w riemannKernelAutocorr with hℓ
  set T := atomPairing w (crossCorr riemannKernelReal H) with hT
  set T2 := atomPairing w (crossCorr H H) with hT2
  set EH := testEnergy H with hEH
  set q := (5 / 4) * zetaInvSqSum with hq
  have hq0 : 0 ≤ q := by have := zetaInvSqSum_nonneg; rw [hq]; positivity
  obtain ⟨K₀, -, hK₀⟩ := exists_abs_atomPairing_truncatedAutocorr_sub_le hw2
  obtain ⟨K₁, -, hK₁⟩ := exists_abs_atomPairing_truncated_sub_le hw2 hH.continuous hHc
  have hT0 := tendsto_of_abs_sub_le hK₀
  have hT1 := tendsto_of_abs_sub_le hK₁
  have hE2 := tendsto_nearRadicalEnergy
  -- `q E_L = √(q · q E_L²) → 0`
  have hEL : Tendsto (fun L : ℝ => q * truncatedRiemannTailEnergy L) atTop (𝓝 0) := by
    have hq2 := hE2.const_mul q
    rw [mul_zero] at hq2
    have h := (Real.continuous_sqrt.tendsto 0).comp hq2
    rw [Real.sqrt_zero] at h
    refine h.congr fun L => ?_
    simp only [Function.comp_apply]
    have hE0 := truncatedRiemannTailEnergy_nonneg L
    rw [show q * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) =
      (q * truncatedRiemannTailEnergy L) ^ 2 by rw [hq]; ring,
      Real.sqrt_sq (by positivity)]
  have hquad : ∀ ε : ℝ, ℓ + 2 * ε * T + ε ^ 2 * T2 ≤ q * (ε ^ 2 * EH ^ 2) := by
    intro ε
    have hL : ∀ L : ℝ,
        atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) +
          2 * ε * atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) + ε ^ 2 * T2 ≤
        q * truncatedRiemannTailEnergy L ^ 2 + 2 * |ε| * EH * (q * truncatedRiemannTailEnergy L) +
          q * (ε ^ 2 * EH ^ 2) := by
      intro L
      have hone := atomPairing_le_re_W hW' (contDiff_perturbedKernel L ε hH)
        (hasCompactSupport_perturbedKernel L ε hHc)
      rw [atomPairing_perturbedKernel w L ε hH.continuous hHc, ← hT2] at hone
      have hWb := (Complex.re_le_norm _).trans (norm_W_perturbedKernel_le L ε hH hHc)
      rw [← hq, ← hEH] at hWb
      have e : q * (truncatedRiemannTailEnergy L + |ε| * EH) ^ 2 =
          q * truncatedRiemannTailEnergy L ^ 2 + 2 * |ε| * EH * (q * truncatedRiemannTailEnergy L) +
            q * (ε ^ 2 * EH ^ 2) := by
        rw [show ε ^ 2 = |ε| ^ 2 from (sq_abs ε).symm]; ring
      linarith
    have hleft : Tendsto (fun L : ℝ =>
        atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) +
          2 * ε * atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) + ε ^ 2 * T2) atTop
        (𝓝 (ℓ + 2 * ε * T + ε ^ 2 * T2)) :=
      (hT0.add (hT1.const_mul (2 * ε))).add tendsto_const_nhds
    have hright : Tendsto (fun L : ℝ => q * truncatedRiemannTailEnergy L ^ 2 +
        2 * |ε| * EH * (q * truncatedRiemannTailEnergy L) + q * (ε ^ 2 * EH ^ 2)) atTop
        (𝓝 (0 + 2 * |ε| * EH * 0 + q * (ε ^ 2 * EH ^ 2))) := by
      refine ((?_ : Tendsto _ _ _).add (hEL.const_mul _)).add tendsto_const_nhds
      simpa [hq, mul_assoc] using hE2
    have := le_of_tendsto_of_tendsto' hleft hright hL
    simpa using this
  have hdisc := discrim_le_zero (a := q * EH ^ 2 - T2) (b := -(2 * T)) (c := -ℓ) fun ε => by
    have := hquad ε
    nlinarith
  unfold discrim at hdisc
  nlinarith

end

end RHTower
