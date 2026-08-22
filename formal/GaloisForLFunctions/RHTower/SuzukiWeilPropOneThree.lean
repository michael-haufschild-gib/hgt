import GaloisForLFunctions.RHTower.SuzukiWeilFrakSZeroSeries

/-!
# Suzuki, Proposition 1.3: the transform of a test function is square integrable

Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3),
Proposition 1.3 (`prop_102`): for `phi` in `C_c^infty(R)`,

`Phat_phi(z) = integral over R of S_t^#(z) phi(t) dt`      (eq. 1.7)

belongs to `L^2(R)`.  Unconditional.

`S_t` is taken in the zero-series form `suzukiFrakSFull`, which agrees with eq. (1.5)/(1.6) for
`t > 0` and, unlike the paper's even extension, is the object that equations (3.6)–(3.8) actually
use — see `GaloisForLFunctions.RHTower.SuzukiWeilFrakSZeroSeries` for why the even extension makes
Lemma 3.2 and eq. (1.9) false.

The published proof invokes Minkowski's integral inequality together with the uniformity of the
`L^2` norm of `S_t` on compact sets of `t`.  Here neither is needed: the master bound of
Proposition 1.2 is *pointwise*, `‖S_t(x)‖ <= C(|t|) (1+|x|)^{-3/4}` with `C` explicit and
nondecreasing (`suzukiFrakSConst_mono`), so on the support of `phi` it is dominated by `C(T)`, and

`‖Phat_phi(x)‖ <= C(T) (1+|x|)^{-3/4} * ‖phi‖_{L^1}`

follows from `‖integral‖ <= integral of ‖.‖` alone.  The same dominating function as in
Proposition 1.2 then gives membership.  Measurability of `x |-> Phat_phi(x)` comes from the joint
measurability of the zero series in `(x,t)` and `AEStronglyMeasurable.integral_prod_right'`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Suzuki eq. (1.7) -/

/-- The Schwarz partner of `𝔖_t`, in the zero-series form valid for every real `t`. -/
def suzukiFrakSSharp (t : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (suzukiFrakSFull t ((starRingEnd ℂ) z))

/-- **Suzuki eq. (1.7).**  `𝒫̂_φ(z) = ∫_ℝ 𝔖_t^♯(z) φ(t) dt`. -/
def suzukiPHat (φ : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, suzukiFrakSSharp t z * φ t

theorem suzukiFrakSSharp_ofReal (t x : ℝ) :
    suzukiFrakSSharp t ((x : ℝ) : ℂ)
      = (starRingEnd ℂ) (suzukiFrakSFull t ((x : ℝ) : ℂ)) := by
  rw [suzukiFrakSSharp, Complex.conj_ofReal]

theorem norm_suzukiFrakSSharp_ofReal_le {T : ℝ} {t : ℝ} (htT : |t| ≤ T)
    {x : ℝ} (hx : x ≠ 0) (hXi : XiC ((x : ℝ) : ℂ) ≠ 0) :
    ‖suzukiFrakSSharp t ((x : ℝ) : ℂ)‖ ≤ suzukiFrakSConst T * decayW x := by
  rw [suzukiFrakSSharp_ofReal, Complex.norm_conj]
  exact le_trans (norm_suzukiFrakSFull_le t hx hXi)
    (mul_le_mul_of_nonneg_right (suzukiFrakSConst_mono (abs_nonneg t) htT) (decayW_pos x).le)

theorem norm_suzukiPHat_ofReal_le {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0)
    {x : ℝ} (hx : x ≠ 0) (hXi : XiC ((x : ℝ) : ℂ) ≠ 0) :
    ‖suzukiPHat φ ((x : ℝ) : ℂ)‖
      ≤ (suzukiFrakSConst T * decayW x) * ∫ t : ℝ, ‖φ t‖ := by
  have hbound : ∀ t : ℝ, ‖suzukiFrakSSharp t ((x : ℝ) : ℂ) * φ t‖
      ≤ (suzukiFrakSConst T * decayW x) * ‖φ t‖ := by
    intro t
    rcases le_or_gt |t| T with h | h
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_suzukiFrakSSharp_ofReal_le h hx hXi) (norm_nonneg _)
    · simp [hsupp t h]
  calc ‖suzukiPHat φ ((x : ℝ) : ℂ)‖
      ≤ ∫ t : ℝ, ‖suzukiFrakSSharp t ((x : ℝ) : ℂ) * φ t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (suzukiFrakSConst T * decayW x) * ‖φ t‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hφ.norm.const_mul _) (Filter.Eventually.of_forall hbound)
    _ = (suzukiFrakSConst T * decayW x) * ∫ t : ℝ, ‖φ t‖ := integral_const_mul _ _

theorem measurable_uncurry_suzukiFrakSSharp :
    Measurable (fun p : ℝ × ℝ => suzukiFrakSSharp p.2 ((p.1 : ℝ) : ℂ)) := by
  have hfun : (fun p : ℝ × ℝ => suzukiFrakSSharp p.2 ((p.1 : ℝ) : ℂ))
      = fun p : ℝ × ℝ => (starRingEnd ℂ) (suzukiFrakSFull p.2 ((p.1 : ℝ) : ℂ)) := by
    funext p
    exact suzukiFrakSSharp_ofReal p.2 p.1
  rw [hfun]
  exact Complex.continuous_conj.measurable.comp measurable_uncurry_suzukiFrakSFull

theorem aestronglyMeasurable_suzukiPHat {φ : ℝ → ℂ} (hφ : Measurable φ) :
    AEStronglyMeasurable (fun x : ℝ => suzukiPHat φ ((x : ℝ) : ℂ)) volume := by
  have hmeas : Measurable (fun p : ℝ × ℝ => suzukiFrakSSharp p.2 ((p.1 : ℝ) : ℂ) * φ p.2) :=
    measurable_uncurry_suzukiFrakSSharp.mul (hφ.comp measurable_snd)
  exact hmeas.aestronglyMeasurable.integral_prod_right'

/-! ## Suzuki, Proposition 1.3 -/

theorem memLp_suzukiPHat {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : Integrable φ) {T : ℝ}
    (hTnn : 0 ≤ T) (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) :
    MemLp (fun x : ℝ => suzukiPHat φ ((x : ℝ) : ℂ)) 2 volume := by
  have hmeas := aestronglyMeasurable_suzukiPHat hφm
  have hIL : (0 : ℝ) ≤ ∫ t : ℝ, ‖φ t‖ := integral_nonneg fun t => norm_nonneg _
  have hCnn : (0 : ℝ) ≤ suzukiFrakSConst T * ∫ t : ℝ, ‖φ t‖ :=
    mul_nonneg (suzukiFrakSConst_nonneg hTnn) hIL
  refine (memLp_decayW (suzukiFrakSConst T * ∫ t : ℝ, ‖φ t‖)).of_le hmeas ?_
  filter_upwards [ae_ne_zero_and_XiC_ne_zero] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hCnn (decayW_pos x).le)]
  calc ‖suzukiPHat φ ((x : ℝ) : ℂ)‖
      ≤ (suzukiFrakSConst T * decayW x) * ∫ t : ℝ, ‖φ t‖ :=
        norm_suzukiPHat_ofReal_le hφ hsupp hx.1 hx.2
    _ = (suzukiFrakSConst T * ∫ t : ℝ, ‖φ t‖) * decayW x := by ring

theorem exists_support_bound {φ : ℝ → ℂ} (h : HasCompactSupport φ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T < |t| → φ t = 0 := by
  obtain ⟨R, hR⟩ := h.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0, le_max_right _ _, fun t ht => ?_⟩
  have hnot : t ∉ tsupport φ := by
    intro hmem
    have hb := hR hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hb
    have : |t| ≤ max R 0 := le_trans hb (le_max_left _ _)
    linarith
  exact image_eq_zero_of_notMem_tsupport hnot

/-- **Suzuki, Proposition 1.3.**  For every continuous compactly supported `φ` — in particular for
every `φ ∈ C_c^∞(ℝ)` — the transform `𝒫̂_φ` of eq. (1.7) belongs to `L²(ℝ)`.  Unconditional. -/
theorem memLp_suzukiPHat_of_compactSupport {φ : ℝ → ℂ} (hcont : Continuous φ)
    (hsupp : HasCompactSupport φ) :
    MemLp (fun x : ℝ => suzukiPHat φ ((x : ℝ) : ℂ)) 2 volume := by
  obtain ⟨T, hT, hTs⟩ := exists_support_bound hsupp
  exact memLp_suzukiPHat hcont.measurable (hcont.integrable_of_hasCompactSupport hsupp) hT hTs

end
end RHTower

