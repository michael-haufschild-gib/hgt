import GaloisForLFunctions.RHTower.SqrtTwoFreeMonoidPrimeTransversal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The window defect of a prime of `ℤ[√2]`

Put `r = 1 + √2`. For `x ≠ 0` let `D(x) = log |x̄| / log r` (with `x̄` the conjugate embedding)
and let `t(x) = ⌈D(x)⌉ − D(x) ∈ [0,1)`.

* Associates differ by units, whose embeddings are powers of `±r`. So `D` changes by an integer
  along associates and `t` is an invariant of the associate class.
* **Window bound.** If `y` is associated to `x` and `|ȳ| ≤ 1`, then `|ȳ| ≤ r^{−t(x)}`.
* **Pairing.** `D(x) + D(x̄) = log|N x| / log r`. Hence `t(x) + t(x̄) ≥ 1 − {log|N x|/log r}`.
* **Per-generator bound.** For `g` in the window with a prime factor `π` and `σ ≥ 1`:
  `g^{−σ} ≤ |N π|^{−σ} · max(½, r^{−t(π)})`. If `g ~ π` the window bound applies; otherwise
  `|N g| ≥ 2|N π|`.
-/

noncomputable section

namespace RHTower.SqrtTwo

open UniqueFactorizationMonoid

/-- The ratio `r = 1 + √2` of the unit lattice. -/
def rr : ℝ := 1 + Real.sqrt 2

theorem one_lt_rr : 1 < rr := by
  have := one_lt_sqrt_two; unfold rr; linarith

theorem rr_pos : 0 < rr := by have := one_lt_rr; linarith

theorem log_rr_pos : 0 < Real.log rr := Real.log_pos one_lt_rr

theorem emb_injective : Function.Injective emb :=
  Zsqrtd.toReal_injective (by norm_num) two_ne_mul_self

theorem emb_ne_zero {x : ℤ√2} (hx : x ≠ 0) : emb x ≠ 0 := by
  intro h; exact hx (emb_injective (by rw [h, map_zero]))

theorem star_ne_zero' {x : ℤ√2} (hx : x ≠ 0) : star x ≠ 0 := by
  intro h; apply hx; have := congrArg star h; simpa using this

theorem abs_emb_mul_abs_emb_star (x : ℤ√2) :
    |emb x| * |emb (star x)| = ((x.norm.natAbs : ℕ) : ℝ) := by
  rw [← abs_mul, emb_mul_emb_star, Nat.cast_natAbs, Int.cast_abs]

/-- Unit embeddings are powers of `r` in absolute value. -/
theorem exists_abs_emb_unit (V : (ℤ√2)ˣ) : ∃ k : ℤ, |emb (V : ℤ√2)| = rr ^ k := by
  have hne : emb (V : ℤ√2) ≠ 0 := emb_ne_zero V.ne_zero
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < emb ((-V : (ℤ√2)ˣ) : ℤ√2) := by
      rw [Units.val_neg, map_neg]; linarith
    obtain ⟨k, hk⟩ := exists_zpow_eq_of_emb_pos (-V) hpos'
    refine ⟨k, ?_⟩
    have h := congrArg (fun W : (ℤ√2)ˣ => emb (W : ℤ√2)) hk
    simp only [Units.val_neg, map_neg] at h
    rw [emb_zpow_fundUnitU] at h
    rw [abs_of_neg hneg, h, rr]
  · obtain ⟨k, hk⟩ := exists_zpow_eq_of_emb_pos V hpos
    refine ⟨k, ?_⟩
    rw [abs_of_pos hpos, hk, emb_zpow_fundUnitU, rr]

/-- `D(x) = log |x̄| / log r`. -/
def logDefect (x : ℤ√2) : ℝ := Real.log |emb (star x)| / Real.log rr

/-- The window defect `t(x) = ⌈D(x)⌉ − D(x) ∈ [0,1)`. -/
def windowDefect (x : ℤ√2) : ℝ := ⌈logDefect x⌉ - logDefect x

theorem windowDefect_nonneg (x : ℤ√2) : 0 ≤ windowDefect x := by
  unfold windowDefect; linarith [Int.le_ceil (logDefect x)]

theorem windowDefect_lt_one (x : ℤ√2) : windowDefect x < 1 := by
  unfold windowDefect; linarith [Int.ceil_lt_add_one (logDefect x)]

theorem rr_rpow_logDefect {x : ℤ√2} (hx : x ≠ 0) : rr ^ logDefect x = |emb (star x)| := by
  have hpos : 0 < |emb (star x)| := abs_pos.mpr (emb_ne_zero (star_ne_zero' hx))
  rw [logDefect, Real.rpow_def_of_pos rr_pos, mul_div_cancel₀ _ log_rr_pos.ne', Real.exp_log hpos]

/-- Along associates the defect `D` moves by an integer. -/
theorem exists_logDefect_eq_sub_of_associated {x y : ℤ√2} (hx : x ≠ 0)
    (hxy : Associated x y) : ∃ k : ℤ, logDefect y = logDefect x - k := by
  obtain ⟨V, rfl⟩ := hxy
  obtain ⟨k, hk⟩ := exists_abs_emb_unit V
  refine ⟨k, ?_⟩
  have hV : |emb (star (V : ℤ√2))| = rr ^ (-k) := by
    have hprod := abs_emb_mul_abs_emb_star (V : ℤ√2)
    have hnorm : ((V : ℤ√2).norm.natAbs : ℝ) = 1 := by
      rw [Zsqrtd.norm_eq_one_iff.mpr V.isUnit]; simp
    rw [hnorm, hk] at hprod
    rw [zpow_neg]; exact eq_inv_of_mul_eq_one_right hprod
  have hsx : 0 < |emb (star x)| := abs_pos.mpr (emb_ne_zero (star_ne_zero' hx))
  unfold logDefect
  rw [star_mul, map_mul, abs_mul, hV, Real.log_mul (zpow_pos rr_pos _).ne' hsx.ne', Real.log_zpow]
  field_simp [log_rr_pos.ne']
  push_cast
  ring

/-- The window defect is an invariant of the associate class. -/
theorem windowDefect_eq_of_associated {x y : ℤ√2} (hx : x ≠ 0) (hxy : Associated x y) :
    windowDefect y = windowDefect x := by
  obtain ⟨k, hk⟩ := exists_logDefect_eq_sub_of_associated hx hxy
  unfold windowDefect
  rw [hk, Int.ceil_sub_intCast]
  push_cast; ring

/-- **Window bound.** An associate of `x` inside the window has `|ȳ| ≤ r^{−t(x)}`. -/
theorem abs_emb_star_le_of_associated {x y : ℤ√2} (hx : x ≠ 0) (hxy : Associated x y)
    (hwin : |emb (star y)| ≤ 1) : |emb (star y)| ≤ rr ^ (-windowDefect x) := by
  have hy : y ≠ 0 := by
    rintro rfl; exact hx (hxy.symm.eq_zero_iff.mp rfl)
  obtain ⟨k, hk⟩ := exists_logDefect_eq_sub_of_associated hx hxy
  have hDy : logDefect y ≤ 0 := by
    unfold logDefect
    exact div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos (abs_nonneg _) hwin) log_rr_pos.le
  have hk' : logDefect x ≤ k := by linarith
  have hceil : (⌈logDefect x⌉ : ℝ) ≤ k := by exact_mod_cast Int.ceil_le.mpr hk'
  rw [← rr_rpow_logDefect hy]
  apply Real.rpow_le_rpow_of_exponent_le one_lt_rr.le
  unfold windowDefect; linarith

/-- **Pairing.** `D(x) + D(x̄) = log |N x| / log r`. -/
theorem logDefect_add_logDefect_star {x : ℤ√2} (hx : x ≠ 0) :
    logDefect x + logDefect (star x) =
      Real.log ((x.norm.natAbs : ℕ) : ℝ) / Real.log rr := by
  unfold logDefect
  rw [star_star, ← add_div, ← Real.log_mul (abs_pos.mpr (emb_ne_zero (star_ne_zero' hx))).ne'
    (abs_pos.mpr (emb_ne_zero hx)).ne', mul_comm, abs_emb_mul_abs_emb_star]

/-- If `{log |N x| / log r} ≥ δ`, then the two conjugate defects sum to at least `1 − {·}`. -/
theorem one_sub_fract_le_windowDefect_add {x : ℤ√2} (hx : x ≠ 0)
    (hfr : 0 < Int.fract (Real.log ((x.norm.natAbs : ℕ) : ℝ) / Real.log rr)) :
    1 - Int.fract (Real.log ((x.norm.natAbs : ℕ) : ℝ) / Real.log rr) ≤
      windowDefect x + windowDefect (star x) := by
  set L := Real.log ((x.norm.natAbs : ℕ) : ℝ) / Real.log rr with hL
  have hsum := logDefect_add_logDefect_star hx
  rw [← hL] at hsum
  have ht := windowDefect_nonneg x
  have ht' := windowDefect_nonneg (star x)
  set m : ℤ := ⌈logDefect x⌉ + ⌈logDefect (star x)⌉ - ⌊L⌋ with hm
  have hexpr : windowDefect x + windowDefect (star x) = m - Int.fract L := by
    unfold windowDefect
    rw [hm, Int.fract]
    push_cast
    linarith
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0 : ℝ) < m := by
      have := Int.fract_lt_one L
      linarith
    have : (0 : ℤ) < m := by exact_mod_cast this
    exact_mod_cast this
  linarith

/-- The absolute norm of a nonunit is at least `2`. -/
theorem two_le_natAbs_norm {h : ℤ√2} (hh : h ≠ 0) (hu : ¬ IsUnit h) : 2 ≤ h.norm.natAbs := by
  have h0 : h.norm.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (norm_ne_zero hh)
  have h1 : h.norm.natAbs ≠ 1 := fun h1 => hu (Zsqrtd.norm_eq_one_iff.mp h1)
  omega

/-- **Per-generator bound.** For `g` in the window with a normalized prime factor `π` and
`σ ≥ 1`: `g^{−σ} ≤ |N π|^{−σ} · max(½, r^{−t(π)})`. -/
theorem emb_rpow_neg_le {g π : ℤ√2} (hg : 0 < emb g) (hwin : |emb (star g)| ≤ 1)
    (hπ : π ∈ normalizedFactors g) {σ : ℝ} (hσ : 1 ≤ σ) :
    emb g ^ (-σ) ≤ ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * max (1 / 2) (rr ^ (-windowDefect π)) := by
  have hg0 : g ≠ 0 := ne_zero_of_emb_pos hg
  have hπp : Prime π := prime_of_normalized_factor π hπ
  have hπ0 : π ≠ 0 := hπp.ne_zero
  obtain ⟨h, rfl⟩ := dvd_of_mem_normalizedFactors hπ
  have hh0 : h ≠ 0 := right_ne_zero_of_mul hg0
  have hNπ : (1 : ℝ) ≤ ((π.norm.natAbs : ℕ) : ℝ) := by
    have := two_le_natAbs_norm hπ0 hπp.not_unit
    exact_mod_cast (by omega : 1 ≤ π.norm.natAbs)
  have hNπpos : (0 : ℝ) < ((π.norm.natAbs : ℕ) : ℝ) := by linarith
  have hstarpos : 0 < |emb (star (π * h))| := abs_pos.mpr (emb_ne_zero (star_ne_zero' hg0))
  -- `g = |N g| / |ḡ|`
  have hgval : emb (π * h) = ((π * h).norm.natAbs : ℝ) / |emb (star (π * h))| := by
    have := abs_emb_mul_abs_emb_star (π * h)
    rw [abs_of_pos hg] at this
    field_simp
    linarith
  have hNmul : (((π * h).norm.natAbs : ℕ) : ℝ) =
      ((π.norm.natAbs : ℕ) : ℝ) * ((h.norm.natAbs : ℕ) : ℝ) := by
    rw [Zsqrtd.norm_mul, Int.natAbs_mul]; push_cast; ring
  by_cases hu : IsUnit h
  · -- `g ~ π`
    have hassoc : Associated π (π * h) := ⟨hu.unit, rfl⟩
    have hwb := abs_emb_star_le_of_associated hπ0 hassoc hwin
    have hNh : ((h.norm.natAbs : ℕ) : ℝ) = 1 := by
      rw [Zsqrtd.norm_eq_one_iff.mpr hu]; simp
    have hge : ((π.norm.natAbs : ℕ) : ℝ) * rr ^ windowDefect π ≤ emb (π * h) := by
      rw [hgval, hNmul, hNh, mul_one, le_div_iff₀ hstarpos]
      have hrt : 0 < rr ^ windowDefect π := Real.rpow_pos_of_pos rr_pos _
      calc ((π.norm.natAbs : ℕ) : ℝ) * rr ^ windowDefect π * |emb (star (π * h))|
          ≤ ((π.norm.natAbs : ℕ) : ℝ) * rr ^ windowDefect π * rr ^ (-windowDefect π) := by
            gcongr
        _ = ((π.norm.natAbs : ℕ) : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add rr_pos, add_neg_cancel, Real.rpow_zero, mul_one]
    have hpos1 : 0 < ((π.norm.natAbs : ℕ) : ℝ) * rr ^ windowDefect π :=
      mul_pos hNπpos (Real.rpow_pos_of_pos rr_pos _)
    calc emb (π * h) ^ (-σ)
        ≤ (((π.norm.natAbs : ℕ) : ℝ) * rr ^ windowDefect π) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hpos1 hge (by linarith)
      _ = ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * rr ^ (-σ * windowDefect π) := by
          rw [Real.mul_rpow hNπpos.le (Real.rpow_pos_of_pos rr_pos _).le, ← Real.rpow_mul rr_pos.le,
            mul_comm (windowDefect π)]
      _ ≤ ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * rr ^ (-windowDefect π) := by
          gcongr
          · exact one_lt_rr.le
          · nlinarith [windowDefect_nonneg π]
      _ ≤ ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * max (1 / 2) (rr ^ (-windowDefect π)) := by
          gcongr; exact le_max_right _ _
  · -- `|N g| ≥ 2 |N π|`
    have hNh : (2 : ℝ) ≤ ((h.norm.natAbs : ℕ) : ℝ) := by
      exact_mod_cast two_le_natAbs_norm hh0 hu
    have hge : 2 * ((π.norm.natAbs : ℕ) : ℝ) ≤ emb (π * h) := by
      rw [hgval, hNmul, le_div_iff₀ hstarpos]
      calc 2 * ((π.norm.natAbs : ℕ) : ℝ) * |emb (star (π * h))|
          ≤ 2 * ((π.norm.natAbs : ℕ) : ℝ) * 1 := by gcongr
        _ ≤ ((π.norm.natAbs : ℕ) : ℝ) * ((h.norm.natAbs : ℕ) : ℝ) := by nlinarith
    have hpos2 : 0 < 2 * ((π.norm.natAbs : ℕ) : ℝ) := by linarith
    calc emb (π * h) ^ (-σ)
        ≤ (2 * ((π.norm.natAbs : ℕ) : ℝ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hpos2 hge (by linarith)
      _ = (2 : ℝ) ^ (-σ) * ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) :=
          Real.mul_rpow (by norm_num) hNπpos.le
      _ ≤ (1 / 2) * ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) := by
          gcongr
          calc (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
      _ ≤ ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * max (1 / 2) (rr ^ (-windowDefect π)) := by
          rw [mul_comm]; gcongr; exact le_max_left _ _

end RHTower.SqrtTwo
