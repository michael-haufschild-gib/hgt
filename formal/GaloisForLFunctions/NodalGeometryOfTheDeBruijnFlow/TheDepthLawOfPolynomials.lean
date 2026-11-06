import GaloisForLFunctions.FiniteFreeProbability.WalshHalfPlaneTheorem
import GaloisForLFunctions.FiniteFreeProbability.QuadraticPhaseHorizon
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeDeBruijnNewman

/-!
# The depth law of polynomials

The exact model of the depth law. On polynomials of degree `n + 1` the flow `∂_t = −∂²` runs backward as `e^{tD²}`, which is the finite free
convolution with `e^{tD²}X^{n+1}`, whose roots are `i√(2t) h`, `h` a zero of the Hermite polynomial `He_{n+1}`. So Walsh's theorem gives: heat time
`t` can remove a depth of at most `√(2t) h_max` (`abs_im_le_of_forward`), `h_max < 2√(n + 1)` being the largest Hermite zero.

**The depth law.** If `q` has degree `n + 1` and `e^{−tD²}q` is real-rooted, then every root of `q` satisfies
`(Im z)² ≤ 2t h_max² < 8(n + 1)t` (`im_sq_lt_of_forward_real`): a root of depth `d` needs heat time `> d²/(8n)` to reach the real line, for a
polynomial with `n` roots. Equality holds at the Hermite cluster `q = e^{tD²}X^{n+1}` (`exists_root_depth_eq`), and `h_max²/(n + 1) → 4`, so the
constant `8` is sharp. This is the quadratic law in the depth and it is the truth for clusters; the linear law `t* ≍ d/log X` of a crystal of density
`log X` is a statement about the actual distribution of the other roots.
-/

open Polynomial Complex
open FiniteFreeProbability GaloisForLFunctions.ArithmeticLocalDivisorGeometry GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- The rotation `σ = i√(2t)`, with `σ² = −2t`. -/
theorem sq_I_mul_sqrt {t : ℝ} (ht : 0 ≤ t) :
    (I * ((Real.sqrt (2 * t) : ℝ) : ℂ)) ^ 2 = -2 * (t : ℂ) := by
  have h : ((Real.sqrt (2 * t) : ℝ) : ℂ) ^ 2 = 2 * (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rw [mul_pow, h, I_sq]
  ring

/-- **The roots of `e^{tD²}X^d`** are `i√(2t) h`, `He_d(h) = 0`. -/
theorem isRoot_hermiteFF_iff {t : ℝ} (ht : 0 < t) (d : ℕ) (y : ℂ) :
    (hermiteFF (t : ℂ) d).IsRoot y ↔
      ∃ h : ℝ, (hermiteReal d).IsRoot h ∧ y = I * ((Real.sqrt (2 * t) : ℝ) : ℂ) * h := by
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  have hσ : I * ((Real.sqrt (2 * t) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (by exact_mod_cast hs.ne')
  rw [hermiteFF, IsRoot, eval_heatOp_X_pow_scale hσ (sq_I_mul_sqrt ht.le), heatOp_neg_half_eq_map]
  constructor
  · intro hx
    have hz : ((hermiteReal d).map (algebraMap ℝ ℂ)).eval (y / (I * ((Real.sqrt (2 * t) : ℝ) : ℂ))) = 0 :=
      (mul_eq_zero.1 hx).resolve_left (pow_ne_zero _ hσ)
    have him := im_eq_zero_of_splits (splits_hermiteReal d) (FiniteFreeProbability.hermiteReal_ne_zero d)
      (z := y / (I * ((Real.sqrt (2 * t) : ℝ) : ℂ))) (by rwa [aeval_def, eval₂_eq_eval_map])
    set z := y / (I * ((Real.sqrt (2 * t) : ℝ) : ℂ)) with hzdef
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    refine ⟨z.re, ?_, ?_⟩
    · rw [hzre, eval_map, show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl,
        eval₂_at_apply] at hz
      exact (algebraMap ℝ ℂ).injective (by rw [hz, map_zero])
    · rw [← hzre, hzdef, mul_div_cancel₀ y hσ]
  · rintro ⟨h, hh, rfl⟩
    rw [mul_div_cancel_left₀ _ hσ, eval_map, show ((h : ℝ) : ℂ) = algebraMap ℝ ℂ h from rfl,
      eval₂_at_apply, hh.eq_zero, map_zero, mul_zero]

theorem im_I_mul_sqrt_mul (s h : ℝ) : (I * (s : ℂ) * (h : ℂ)).im = s * h := by
  simp [Complex.mul_im, Complex.mul_re]

/-- The roots of `e^{tD²}X^{n+1}` have imaginary part at most `√(2t) h_max`. -/
theorem root_im_le_hermiteFF {t : ℝ} (ht : 0 < t) (n : ℕ) (y : ℂ) (hy : (hermiteFF (t : ℂ) (n + 1)).IsRoot y) :
    y.im ≤ Real.sqrt (2 * t) * hermiteEdge n := by
  obtain ⟨h, hh, rfl⟩ := (isRoot_hermiteFF_iff ht (n + 1) y).mp hy
  rw [im_I_mul_sqrt_mul]
  exact mul_le_mul_of_nonneg_left (le_hermiteEdge_of_root n hh.eq_zero) (Real.sqrt_nonneg _)

/-- The complex Hermite polynomial is the lift of the real one. -/
theorem hermiteFF_ofReal (t : ℝ) (d : ℕ) :
    hermiteFF (t : ℂ) d = (hermiteFF t d).map (algebraMap ℝ ℂ) := by
  rw [hermiteFF, hermiteFF, heatOp_map]
  simp

/-- **Walsh for the backward flow.** If the roots of `p` lie in `Im ≤ a`, those of `e^{tD²}p` lie in `Im ≤ a + √(2t) h_max`. -/
theorem root_im_le_heatOp {n : ℕ} {p : ℂ[X]} (hp : p.natDegree = n + 1) {a t : ℝ} (ht : 0 < t)
    (hpa : ∀ r, p.IsRoot r → r.im ≤ a) {z : ℂ} (hz : (heatOp (t : ℂ) (n + 1) p).IsRoot z) :
    z.im ≤ a + Real.sqrt (2 * t) * hermiteEdge n := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  rw [heatOp_eq_ffConv hp.le] at hz
  have hmapinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  have hq0 : hermiteFF (t : ℂ) (n + 1) ≠ 0 := by
    rw [hermiteFF_ofReal, Polynomial.map_ne_zero_iff hmapinj]
    intro h
    have := coeff_hermiteFF_self t (n + 1)
    rw [h, coeff_zero] at this
    exact zero_ne_one this
  have hqd : (hermiteFF (t : ℂ) (n + 1)).natDegree ≤ n + 1 := by
    rw [hermiteFF_ofReal, natDegree_map_eq_of_injective hmapinj]
    refine (natDegree_heatOp_le _ _ _).trans ?_
    simp
  exact ffConv_root_im_le hp0 hp hq0 hqd hpa (root_im_le_hermiteFF ht n) hz

/-- **Depth at time `0` against depth at time `t`.** For a real polynomial `q` of degree `n + 1`, if the roots of `e^{−tD²}q` lie in `|Im| ≤ a`
then those of `q` lie in `|Im| ≤ a + √(2t) h_max`: heat time `t` removes a depth of at most `√(2t) h_max`. -/
theorem abs_im_le_of_forward {n : ℕ} {q : ℝ[X]} (hq : q.natDegree = n + 1) {a t : ℝ} (ht : 0 < t)
    (ha : ∀ r : ℂ, aeval r (heatOp (-t) (n + 1) q) = 0 → |r.im| ≤ a) {z : ℂ} (hz : aeval z q = 0) :
    |z.im| ≤ a + Real.sqrt (2 * t) * hermiteEdge n := by
  set φ := algebraMap ℝ ℂ with hφ
  have hinj : Function.Injective φ := φ.injective
  set p := heatOp (-t) (n + 1) q with hpdef
  have hback : heatOp t (n + 1) p = q := by
    rw [hpdef, heatOp_heatOp hq.le]
    simp only [add_neg_cancel]
    exact heatOp_zero _ _
  have hpdeg : p.natDegree = n + 1 := by
    refine le_antisymm ((natDegree_heatOp_le _ _ _).trans hq.le) ?_
    rw [← hq]
    conv_lhs => rw [← hback]
    exact natDegree_heatOp_le _ _ _
  have hmapdeg : (p.map φ).natDegree = n + 1 := by
    rw [natDegree_map_eq_of_injective hinj, hpdeg]
  have hroots : ∀ r, (p.map φ).IsRoot r → r.im ≤ a := fun r hr =>
    (le_abs_self _).trans (ha r (by rwa [aeval_def, eval₂_eq_eval_map]))
  have hup (w : ℂ) (hw : aeval w q = 0) : w.im ≤ a + Real.sqrt (2 * t) * hermiteEdge n := by
    refine root_im_le_heatOp hmapdeg ht hroots ?_
    have heq : heatOp (t : ℂ) (n + 1) (p.map φ) = q.map φ := by
      have := heatOp_map φ t (n + 1) p
      rw [hback] at this
      exact this.symm
    rw [heq]
    rwa [IsRoot, eval_map, ← aeval_def]
  have hconj : aeval ((starRingEnd ℂ) z) q = 0 := by
    have := aeval_conj q z
    rw [hz, map_zero] at this
    exact this
  have h1 := hup z hz
  have h2 := hup _ hconj
  rw [Complex.conj_im] at h2
  rw [abs_le]
  constructor <;> linarith only [h1, h2]

/-- **The depth law of polynomials.** If `e^{−tD²}q` is real-rooted, every root of `q` satisfies
`(Im z)² ≤ 2t h_max² < 8(n + 1)t`. -/
theorem im_sq_lt_of_forward_real {n : ℕ} {q : ℝ[X]} (hq : q.natDegree = n + 1) {t : ℝ} (ht : 0 < t)
    (hreal : ∀ r : ℂ, aeval r (heatOp (-t) (n + 1) q) = 0 → r.im = 0) {z : ℂ} (hz : aeval z q = 0) :
    z.im ^ 2 ≤ 2 * t * hermiteEdge n ^ 2 ∧ z.im ^ 2 < 8 * ((n : ℝ) + 1) * t := by
  have h := abs_im_le_of_forward hq (a := 0) ht (fun r hr => by rw [hreal r hr, abs_zero]) hz
  rw [zero_add] at h
  have he := hermiteEdge_nonneg n
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  have hsq : z.im ^ 2 ≤ 2 * t * hermiteEdge n ^ 2 := by
    rw [← sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg _) h 2
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at this
  refine ⟨hsq, hsq.trans_lt ?_⟩
  have h2 := hermiteEdge_lt_two_sqrt n
  have h3 : hermiteEdge n ^ 2 < (2 * Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 := pow_lt_pow_left₀ h2 he (by norm_num)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h3
  push_cast at h3
  nlinarith only [h3, ht]

/-- **Sharpness.** The Hermite cluster reaches the real line at time `t` from depth `√(2t) h_max`. -/
theorem exists_root_depth_eq {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∃ y : ℂ, (hermiteFF (t : ℂ) (n + 1)).IsRoot y ∧ y.im = Real.sqrt (2 * t) * hermiteEdge n := by
  refine ⟨I * ((Real.sqrt (2 * t) : ℝ) : ℂ) * (hermiteEdge n : ℝ), ?_, im_I_mul_sqrt_mul _ _⟩
  exact (isRoot_hermiteFF_iff ht (n + 1) _).mpr ⟨hermiteEdge n, hermiteEdge_isRoot n, rfl⟩

/-- At the Hermite cluster the forward image is the real-rooted monomial. -/
theorem heatOp_neg_hermiteFF (t : ℝ) (n : ℕ) : heatOp (-t) n (hermiteFF t n) = X ^ n := by
  rw [hermiteFF, heatOp_heatOp (natDegree_X_pow_le n)]
  simp only [neg_add_cancel]
  exact heatOp_zero _ _

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
