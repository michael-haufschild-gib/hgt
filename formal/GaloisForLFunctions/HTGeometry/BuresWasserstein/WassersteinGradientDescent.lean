import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinUniqueness
import GaloisForLFunctions.HTGeometry.RobbinsMonroRecursion

/-!
# Convergence of the perturbed gradient descent

Global strong monotonicity turns the explicit step into a genuine contraction on a Loewner
interval:

`‖(X - tΦ(X)) - (Y - tΦ(Y))‖²_HS ≤ (1 - 2tκ + t²L²) ‖X - Y‖²_HS`,   `κ = α²/(2β³)`,

with no defect term at all — the defect `C‖X-Y‖/N` of the local estimate is killed by letting
the subdivision `N` grow.  Since `1 - 2tκ + t²L² = (1 - tκ + t²L²/2)² - (tκ - t²L²/2)²`, the
square root of the contraction factor is at most `1 - tκ + t²L²/2`, and for `t ≤ κ/L²` this is
at most `1 - tκ/2`.  A perturbed iteration `X_{k+1} = X_k - λ_k Φ(X_k) + r_k` with
`‖r_k‖_HS ≤ C λ_k²` therefore obeys the Robbins–Monro recursion, and converges to the
Wasserstein point whenever `∑ λ = ∞` and `∑ λ² < ∞`.
-/

open scoped NNReal Ring BigOperators
open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- **The explicit gradient step contracts, with no second-order defect.** -/
theorem hsNormSq_gradientStep_sub_le_global {X Y : E →L[ℂ] E} {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 ≤ t)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) :
    hsNormSq ((X - t • wassField s w Av X) - (Y - t • wassField s w Av Y))
      ≤ (1 - 2 * t * (α * α / (2 * (β * (β * β)))) + t ^ 2 * (wassLipConst α β) ^ 2)
        * hsNormSq (X - Y) := by
  obtain ⟨D, hDdef⟩ : ∃ z : E →L[ℂ] E,
      z = wassField s w Av X - wassField s w Av Y := ⟨_, rfl⟩
  have hDHS : IsHilbertSchmidt D := by
    rw [hDdef]; exact isHilbertSchmidt_wassField_sub hα hβ hA hX hY hAα hAβ hXβ hYβ hPHS
  have hZ : (X - t • wassField s w Av X) - (Y - t • wassField s w Av Y)
      = (X - Y) - t • D := by rw [hDdef, smul_sub]; abel_nf
  rw [hZ]
  have hsq : hsNormSq (t • D) = t ^ 2 * hsNormSq D := by
    have h1 : hsNormSq (t • D) = (hsNorm (t • D)) ^ 2 := (sq_hsNorm _).symm
    rw [h1, hsNorm_real_smul, mul_pow, sq_abs, sq_hsNorm]
  have hexp : hsNormSq ((X - Y) - t • D)
      = hsNormSq (X - Y) - 2 * (t * RCLike.re (hsInner D (X - Y))) + t ^ 2 * hsNormSq D := by
    rw [hsNormSq_sub hPHS (hDHS.real_smul t), hsq, hsInner_real_smul_right]
    congr 2
    have hconj : RCLike.re (hsInner (X - Y) D) = RCLike.re (hsInner D (X - Y)) := by
      rw [hsInner_conj_symm (X - Y) D, RCLike.conj_re]
    simp [hconj]
  rw [hexp]
  have hlip : hsNormSq D ≤ (wassLipConst α β) ^ 2 * hsNormSq (X - Y) := by
    have h := hsNorm_wassField_sub_le hα hβ hw hwsum hA hX hY hAα hAβ hXα hXβ hYα hYβ hPHS
    rw [hDdef]
    have h2 : (hsNorm (wassField s w Av X - wassField s w Av Y)) ^ 2
        ≤ (wassLipConst α β * hsNorm (X - Y)) ^ 2 :=
      pow_le_pow_left₀ (hsNorm_nonneg _) h 2
    rw [sq_hsNorm, mul_pow, sq_hsNorm] at h2
    exact h2
  -- the monotonicity term, with the defect divided by an arbitrary `N`
  have hmono : ∀ N : ℕ, 0 < N →
      (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
        * hsNormSq (X - Y) ≤ RCLike.re (hsInner D (X - Y)) := by
    intro N hN
    rw [hDdef]
    exact re_hsInner_wassField_sub_lower_global hα hβ hw hwsum hA hAα hAβ hXα hXβ hYα hYβ
      hPHS hN
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- pick a subdivision fine enough that the defect contributes less than `ε`
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((2 * t * secondOrderConst α β * ‖X - Y‖ * hsNormSq (X - Y) + 1) / ε)
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    refine lt_of_le_of_lt ?_ hN
    have hC : (0:ℝ) ≤ secondOrderConst α β := (secondOrderConst_pos hα hβ).le
    have hq : (0:ℝ) ≤ hsNormSq (X - Y) := hsNormSq_nonneg _
    have hnum : (0:ℝ) ≤ 2 * t * secondOrderConst α β * ‖X - Y‖ * hsNormSq (X - Y) + 1 := by
      have h0 : (0:ℝ) ≤ 2 * t * secondOrderConst α β * ‖X - Y‖ * hsNormSq (X - Y) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hC) (norm_nonneg _)) hq
      linarith
    exact div_nonneg hnum hε.le
  have hNpos : 0 < N := by exact_mod_cast hN0
  have hkey := hmono N hNpos
  have hdefect : 2 * t * (secondOrderConst α β * (‖X - Y‖ / (N : ℝ))) * hsNormSq (X - Y) ≤ ε := by
    rw [div_lt_iff₀ hε] at hN
    have hid : 2 * t * (secondOrderConst α β * (‖X - Y‖ / (N : ℝ))) * hsNormSq (X - Y)
        = (2 * t * secondOrderConst α β * ‖X - Y‖ * hsNormSq (X - Y)) / (N : ℝ) := by
      field_simp
    rw [hid, div_le_iff₀ hN0]
    nlinarith [hN, hε]
  nlinarith [hkey, hlip, ht, sq_nonneg t, hsNormSq_nonneg (X - Y), hdefect]

/-- The square-root form of the contraction. -/
theorem hsNorm_gradientStep_sub_le_global {X Y : E →L[ℂ] E} {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 ≤ t)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y))
    (hfac : 0 ≤ 1 - t * (α * α / (2 * (β * (β * β))))
      + t ^ 2 * (wassLipConst α β) ^ 2 / 2) :
    hsNorm ((X - t • wassField s w Av X) - (Y - t • wassField s w Av Y))
      ≤ (1 - t * (α * α / (2 * (β * (β * β)))) + t ^ 2 * (wassLipConst α β) ^ 2 / 2)
        * hsNorm (X - Y) := by
  have hq := hsNormSq_gradientStep_sub_le_global hα hβ ht hw hwsum hA hX hY hAα hAβ
    hXα hXβ hYα hYβ hPHS
  have hcmp : (1 - 2 * t * (α * α / (2 * (β * (β * β)))) + t ^ 2 * (wassLipConst α β) ^ 2)
      ≤ (1 - t * (α * α / (2 * (β * (β * β)))) + t ^ 2 * (wassLipConst α β) ^ 2 / 2) ^ 2 := by
    nlinarith [sq_nonneg (t * (α * α / (2 * (β * (β * β)))) - t ^ 2 * (wassLipConst α β) ^ 2 / 2)]
  have hqnn : (0 : ℝ) ≤ hsNormSq (X - Y) := hsNormSq_nonneg _
  have h2 : hsNorm ((X - t • wassField s w Av X) - (Y - t • wassField s w Av Y)) ^ 2
      ≤ ((1 - t * (α * α / (2 * (β * (β * β)))) + t ^ 2 * (wassLipConst α β) ^ 2 / 2)
        * hsNorm (X - Y)) ^ 2 := by
    rw [sq_hsNorm, mul_pow, sq_hsNorm]
    nlinarith [hq, hcmp, hqnn]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (hsNorm_nonneg _),
    Real.sqrt_sq (mul_nonneg hfac (hsNorm_nonneg _))] at h3

/-- **Proposition 4.15 (Kim–Mer–Pálfia), in the Hilbert–Schmidt metric.**  A perturbed gradient
iteration with square-summable, non-summable steps converges to the Wasserstein point. -/
theorem tendsto_hsNorm_sub_isWassersteinPoint {α β Cr : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    {Xseq : ℕ → E →L[ℂ] E} {Xstar : E →L[ℂ] E} {lam : ℕ → ℝ}
    (hXstarW : IsWassersteinPoint s w Av Xstar)
    (hXstarα : α • (1 : E →L[ℂ] E) ≤ Xstar) (hXstarβ : Xstar ≤ β • (1 : E →L[ℂ] E))
    (hXpos : ∀ n, IsStrictlyPositive (Xseq n))
    (hXa : ∀ n, α • (1 : E →L[ℂ] E) ≤ Xseq n) (hXb : ∀ n, Xseq n ≤ β • (1 : E →L[ℂ] E))
    (hXHS : ∀ n, IsHilbertSchmidt (Xseq n - Xstar))
    (hCr : 0 ≤ Cr) (hlam : ∀ n, 0 ≤ lam n)
    (hlamκ : ∀ n, (α * α / (2 * (β * (β * β)))) * lam n ≤ 1)
    (hlamL : ∀ n, lam n * (wassLipConst α β) ^ 2 ≤ α * α / (2 * (β * (β * β))))
    (hstep : ∀ n, hsNorm (Xseq (n + 1)
        - (Xseq n - lam n • wassField s w Av (Xseq n))) ≤ Cr * (lam n) ^ 2)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, lam k) atTop atTop)
    (hsum : Summable (fun n => (lam n) ^ 2)) :
    Tendsto (fun n => hsNorm (Xseq n - Xstar)) atTop (nhds 0) := by
  obtain ⟨κ, hκdef⟩ : ∃ k : ℝ, k = α * α / (2 * (β * (β * β))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hΦstar : wassField s w Av Xstar = 0 :=
    wassField_eq_zero_of_isWassersteinPoint hwsum hXstarW
  have hrec : ∀ n, hsNorm (Xseq (n + 1) - Xstar)
      ≤ (1 - (κ / 2) * lam n) * hsNorm (Xseq n - Xstar) + Cr * (lam n) ^ 2 := by
    intro n
    have hfacr : 0 ≤ 1 - lam n * (α * α / (2 * (β * (β * β))))
        + (lam n) ^ 2 * (wassLipConst α β) ^ 2 / 2 := by
      have h1 : (α * α / (2 * (β * (β * β)))) * lam n ≤ 1 := hlamκ n
      have h2 : (0:ℝ) ≤ (lam n) ^ 2 * (wassLipConst α β) ^ 2 / 2 := by positivity
      nlinarith [h1, h2]
    have hcontr := hsNorm_gradientStep_sub_le_global (t := lam n) hα hβ (hlam n) hw hwsum hA
      (hXpos n) hXstarW.1 hAα hAβ (hXa n) (hXb n) hXstarα hXstarβ (hXHS n) hfacr
    rw [hΦstar, smul_zero, sub_zero] at hcontr
    have hQHS : IsHilbertSchmidt (wassField s w Av (Xseq n)) := by
      have h := isHilbertSchmidt_wassField_sub (w := w) hα hβ hA (hXpos n) hXstarW.1 hAα hAβ
        (hXb n) hXstarβ (hXHS n)
      rwa [hΦstar, sub_zero] at h
    have hAHS : IsHilbertSchmidt
        (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n))) := by
      have hid : Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n))
          = (Xseq (n + 1) - Xstar)
            - ((Xseq n - Xstar) - lam n • wassField s w Av (Xseq n)) := by abel_nf
      rw [hid]
      exact (hXHS (n + 1)).sub ((hXHS n).sub (hQHS.real_smul _))
    have hBHS : IsHilbertSchmidt ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar) := by
      have hid : (Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar
          = (Xseq n - Xstar) - lam n • wassField s w Av (Xseq n) := by abel_nf
      rw [hid]
      exact (hXHS n).sub (hQHS.real_smul _)
    have htri : hsNorm (Xseq (n + 1) - Xstar)
        ≤ hsNorm (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n)))
          + hsNorm ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar) := by
      have hid : Xseq (n + 1) - Xstar
          = (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n)))
            + ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar) := by abel_nf
      rw [hid]
      exact hsNorm_add_le hAHS hBHS
    have hshrink : (1 - lam n * (α * α / (2 * (β * (β * β))))
          + (lam n) ^ 2 * (wassLipConst α β) ^ 2 / 2)
        ≤ 1 - (κ / 2) * lam n := by
      rw [hκdef]
      have hL := hlamL n
      nlinarith [hL, hlam n]
    have hstep' := hstep n
    have hnn : (0 : ℝ) ≤ hsNorm (Xseq n - Xstar) := hsNorm_nonneg _
    nlinarith [htri, hcontr, hstep', hshrink, hnn]
  refine tendsto_zero_of_robbins (κ := κ / 2) (C := Cr) (by positivity) hCr
    (fun n => hsNorm_nonneg _) hlam ?_ hrec hdiv hsum
  intro n
  have h1 : κ * lam n ≤ 1 := by rw [hκdef]; exact hlamκ n
  nlinarith [h1, hlam n, hκ0]

/-- **Proposition 4.15 with a state-dependent error.**  The error term may grow linearly in the
current distance to the Wasserstein point: the extra `Cr d λ²` is absorbed by the contraction
once `λ ≤ κ/(4Cr)`. -/
theorem tendsto_hsNorm_sub_isWassersteinPoint' {α β Cr : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    {Xseq : ℕ → E →L[ℂ] E} {Xstar : E →L[ℂ] E} {lam : ℕ → ℝ}
    (hXstarW : IsWassersteinPoint s w Av Xstar)
    (hXstarα : α • (1 : E →L[ℂ] E) ≤ Xstar) (hXstarβ : Xstar ≤ β • (1 : E →L[ℂ] E))
    (hXpos : ∀ n, IsStrictlyPositive (Xseq n))
    (hXa : ∀ n, α • (1 : E →L[ℂ] E) ≤ Xseq n) (hXb : ∀ n, Xseq n ≤ β • (1 : E →L[ℂ] E))
    (hXHS : ∀ n, IsHilbertSchmidt (Xseq n - Xstar))
    (hCr : 0 ≤ Cr) (hlam : ∀ n, 0 ≤ lam n)
    (hlamκ : ∀ n, (α * α / (2 * (β * (β * β)))) * lam n ≤ 1)
    (hlamL : ∀ n, lam n * (wassLipConst α β) ^ 2 ≤ (α * α / (2 * (β * (β * β)))) / 2)
    (hlamCr : ∀ n, Cr * lam n ≤ (α * α / (2 * (β * (β * β)))) / 8)
    (hstep : ∀ n, hsNorm (Xseq (n + 1)
        - (Xseq n - lam n • wassField s w Av (Xseq n)))
      ≤ Cr * (1 + hsNorm (Xseq n - Xstar)) * (lam n) ^ 2)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, lam k) atTop atTop)
    (hsum : Summable (fun n => (lam n) ^ 2)) :
    Tendsto (fun n => hsNorm (Xseq n - Xstar)) atTop (nhds 0) := by
  obtain ⟨κ, hκdef⟩ : ∃ k : ℝ, k = α * α / (2 * (β * (β * β))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hΦstar : wassField s w Av Xstar = 0 :=
    wassField_eq_zero_of_isWassersteinPoint hwsum hXstarW
  have hrec : ∀ n, hsNorm (Xseq (n + 1) - Xstar)
      ≤ (1 - (κ / 4) * lam n) * hsNorm (Xseq n - Xstar) + Cr * (lam n) ^ 2 := by
    intro n
    have hfacr : 0 ≤ 1 - lam n * (α * α / (2 * (β * (β * β))))
        + (lam n) ^ 2 * (wassLipConst α β) ^ 2 / 2 := by
      have h1 : (α * α / (2 * (β * (β * β)))) * lam n ≤ 1 := hlamκ n
      have h2 : (0:ℝ) ≤ (lam n) ^ 2 * (wassLipConst α β) ^ 2 / 2 := by positivity
      nlinarith [h1, h2]
    have hcontr := hsNorm_gradientStep_sub_le_global (t := lam n) hα hβ (hlam n) hw hwsum hA
      (hXpos n) hXstarW.1 hAα hAβ (hXa n) (hXb n) hXstarα hXstarβ (hXHS n) hfacr
    rw [hΦstar, smul_zero, sub_zero] at hcontr
    have hQHS : IsHilbertSchmidt (wassField s w Av (Xseq n)) := by
      have h := isHilbertSchmidt_wassField_sub (w := w) hα hβ hA (hXpos n) hXstarW.1 hAα hAβ
        (hXb n) hXstarβ (hXHS n)
      rwa [hΦstar, sub_zero] at h
    have hAHS : IsHilbertSchmidt
        (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n))) := by
      have hid : Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n))
          = (Xseq (n + 1) - Xstar)
            - ((Xseq n - Xstar) - lam n • wassField s w Av (Xseq n)) := by abel_nf
      rw [hid]
      exact (hXHS (n + 1)).sub ((hXHS n).sub (hQHS.real_smul _))
    have hBHS : IsHilbertSchmidt ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar) := by
      have hid : (Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar
          = (Xseq n - Xstar) - lam n • wassField s w Av (Xseq n) := by abel_nf
      rw [hid]
      exact (hXHS n).sub (hQHS.real_smul _)
    have htri : hsNorm (Xseq (n + 1) - Xstar)
        ≤ hsNorm (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n)))
          + hsNorm ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar) := by
      have hid : Xseq (n + 1) - Xstar
          = (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n)))
            + ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar) := by abel_nf
      rw [hid]
      exact hsNorm_add_le hAHS hBHS
    have hshrink : (1 - lam n * (α * α / (2 * (β * (β * β))))
          + (lam n) ^ 2 * (wassLipConst α β) ^ 2 / 2)
        ≤ 1 - (κ / 2) * lam n := by
      rw [hκdef]
      have hL := hlamL n
      nlinarith [hL, hlam n]
    have hstep' := hstep n
    have hnn : (0 : ℝ) ≤ hsNorm (Xseq n - Xstar) := hsNorm_nonneg _
    have habs : Cr * lam n * hsNorm (Xseq n - Xstar) * lam n
        ≤ (κ / 4) * lam n * hsNorm (Xseq n - Xstar) := by
      have h1 : Cr * lam n ≤ κ / 8 := by rw [hκdef]; exact hlamCr n
      nlinarith [h1, hnn, hlam n, hκ0, mul_nonneg (hlam n) hnn]
    have hcontrd : hsNorm ((Xseq n - lam n • wassField s w Av (Xseq n)) - Xstar)
        ≤ (1 - (κ / 2) * lam n) * hsNorm (Xseq n - Xstar) :=
      hcontr.trans (mul_le_mul_of_nonneg_right hshrink hnn)
    have hstep2 : hsNorm (Xseq (n + 1) - (Xseq n - lam n • wassField s w Av (Xseq n)))
        ≤ Cr * (lam n) ^ 2 + Cr * lam n * hsNorm (Xseq n - Xstar) * lam n := by
      refine hstep'.trans (le_of_eq ?_)
      ring
    linarith [htri, hstep2, hcontrd, habs]
  refine tendsto_zero_of_robbins (κ := κ / 4) (C := Cr) (by positivity) hCr
    (fun n => hsNorm_nonneg _) hlam ?_ hrec hdiv hsum
  intro n
  have h1 : κ * lam n ≤ 1 := by rw [hκdef]; exact hlamκ n
  nlinarith [h1, hlam n, hκ0]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
