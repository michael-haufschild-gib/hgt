import GaloisForLFunctions.RHTower.DualCarrierWeightOscillation
import GaloisForLFunctions.RHTower.DualCarrierWeightRightShift
import GaloisForLFunctions.RHTower.DirectOffDiagonalEnvelope

/-!
# The dual off-diagonal of the block twisted moment: the envelope

On the Levinson lines `s₁ = σ₀+it`, `s₂ = σ₀−it`, `σ₀ = 1/2 − d`, the dual side of the product
approximate functional equation carries the modulus weight `χ(s₁)χ(s₂)` and the two-ratio dual
weight at `Y = mn·x`; against the block window `w` and the twist `(k/h)^{it}` its `(m,n,h,k)`-term
is `(mn)^{-(1/2+d)} (hk)^{-(1/2−d)} ∫ w A_{mnx} e^{-iξt}` with `ξ = log(nh) − log(mk)`.

Two bounds are available for one term.

* **Oscillation** (small `mn`): the frequency-side integration by parts of
  `exists_norm_integral_blockWindow_dualCarrierWeight_le` gives decay `|ξ|^{-K}`, and off the
  diagonal `|ξ| ≥ 1/(2√(hk·mn))`, so the term is
  `≤ Osc · (hk)^{K/2−1/2+d} (mn)^{K/2−3/2−d}`.
* **Right shift** (large `mn`): `exists_norm_dualCarrierWeight_le_rightShift` gives
  `‖A_Y(t)‖ ≤ C (1+|t|)^{2K''+1} Y^{-(1/2−d+K'')}`, so the term is
  `≤ Shift · (hk)^{-(1/2−d)} (mn)^{-(1+K'')}`.

Neither bound alone is summable with the required height decay.  The **uniform envelope**
interpolates them at a free threshold `Y₀`: multiplying the first bound by `(Y₀/mn)^{K/2+1} ≥ 1`
when `mn ≤ Y₀` and the second by `(mn/Y₀)^{K''−1} ≥ 1` when `mn > Y₀` gives for *every* pair

`term ≤ Osc (hk)^{K/2−1/2+d} Y₀^{K/2+1} (mn)^{-(5/2+d)} + Shift (hk)^{-(1/2−d)} Y₀^{-(K''−1)} (mn)^{-2}`,

which is summable over `(m,n)` with sums `ζ(5/2+d)²` and `ζ(2)²`.  With `Y₀ = a^{1+ε₁}`,
`η ≍ a`, `x ≍ a` the first part decays like `a^{K(θ−1/2+ε₁/2)}` after the `(h,k)`-sum over
`h,k ≤ a^θ` and the second like `a^{-ε₁K''}`: this is the dual side of the Levinson threshold.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- One dual off-diagonal term of the block twisted moment, in absolute value: the coefficient
`(mn)^{-(1/2+d)} (hk)^{-(1/2−d)}` and the window integral of the dual carrier weight at
`Y = mn·x` against the phase `e^{-i(log(nh) − log(mk))t}`; zero on the dual diagonal
`nh = mk`. -/
def dualOffDiagTerm (d x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) : ℝ :=
  if (P.2 + 1) * h ≠ (P.1 + 1) * k then
    (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d))) * (((h : ℝ) * k) ^ (-(1 / 2 - d)))
      * ‖∫ t, blockWindowC p q η t * dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1) * x) t
          * Complex.exp (-(((Real.log (((P.2 + 1) * h : ℕ) : ℝ)
              - Real.log (((P.1 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ) * t) * I)‖
  else 0

theorem dualOffDiagTerm_nonneg (d x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) :
    0 ≤ dualOffDiagTerm d x p q η h k P := by
  unfold dualOffDiagTerm
  split_ifs
  · positivity
  · exact le_rfl

/-- The oscillation-regime constant: the frequency-side integration-by-parts bound with the
separation factor `2^K` absorbed. -/
def dualOffDiagOscConst (K : ℕ) (C x p q η : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ((x⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
    (windowCarrierJetConst K η (p - η) ((p - η) / 2)
        * (Real.exp 8 * (1 + (q + η) + (p - η) / 2) ^ 4) * Real.sqrt Real.pi * 2 ^ K
      + C * (1 + (q + η)) ^ 4
        * (Real.exp 16 * Real.exp (-(((p - η) / 2) ^ 2) / 2) * Real.sqrt (4 * Real.pi)))

theorem dualOffDiagOscConst_nonneg (K : ℕ) {C x p q η : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) :
    0 ≤ dualOffDiagOscConst K C x p q η := by
  unfold dualOffDiagOscConst
  have hlen : 0 ≤ q - p + 2 * η := by linarith
  have hJ := windowCarrierJetConst_nonneg K hη (show 0 < p - η by linarith) ((p - η) / 2)
  have hqη : 0 ≤ q + η := by linarith
  have h1 : 0 ≤ 1 + (q + η) + (p - η) / 2 := by linarith
  positivity

/-- The right-shift-regime constant. -/
def dualOffDiagShiftConst (K'' : ℕ) (C d x p q η : ℝ) : ℝ :=
  (q - p + 2 * η) *
    (C * (1 + (q + η)) ^ (2 * ((K'' : ℝ) + 1 / 2)) * x ^ (-(1 / 2 - d + K'')))

theorem dualOffDiagShiftConst_nonneg (K'' : ℕ) {C d x p q η : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) :
    0 ≤ dualOffDiagShiftConst K'' C d x p q η := by
  unfold dualOffDiagShiftConst
  have hlen : 0 ≤ q - p + 2 * η := by linarith
  have hqη : 0 ≤ 1 + (q + η) := by linarith
  positivity

/-! ## The oscillation bound -/

/-- **Oscillation envelope of one dual off-diagonal term.** -/
theorem dualOffDiagTerm_le_osc {d : ℝ} (K : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (p q η y ξ : ℝ), 4 ≤ p - η → p ≤ q → 0 < η → 0 < y → ξ ≠ 0 →
      ‖∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * ((y⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
          (windowCarrierJetConst K η (p - η) ((p - η) / 2)
              * (Real.exp 8 * (1 + (q + η) + (p - η) / 2) ^ 4) * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(((p - η) / 2) ^ 2) / 2) * Real.sqrt (4 * Real.pi))))
    {x p q η : ℝ} (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (P : ℕ × ℕ) :
    dualOffDiagTerm d x p q η h k P
      ≤ dualOffDiagOscConst K C x p q η * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d)
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ ((K : ℝ) / 2 - 3 / 2 - d)) := by
  unfold dualOffDiagTerm
  split_ifs with hne
  · have hm : (0 : ℝ) < P.1 + 1 := by positivity
    have hn : (0 : ℝ) < P.2 + 1 := by positivity
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    set mn : ℝ := (P.1 + 1 : ℝ) * (P.2 + 1) with hmn
    set hk' : ℝ := (h : ℝ) * k with hhk
    have hmn0 : 0 < mn := by positivity
    have hhk0 : 0 < hk' := by positivity
    have hmn1 : 1 ≤ mn := by
      rw [hmn]
      have h1 : (1 : ℝ) ≤ P.1 + 1 := by
        have : (0 : ℝ) ≤ P.1 := by positivity
        linarith
      have h2 : (1 : ℝ) ≤ P.2 + 1 := by
        have : (0 : ℝ) ≤ P.2 := by positivity
        linarith
      nlinarith
    have hhk1 : 1 ≤ hk' := by
      rw [hhk]
      have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have h2 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    -- the frequency and its separation
    have hAn : 0 < (P.2 + 1) * h := by positivity
    have hBn : 0 < (P.1 + 1) * k := by positivity
    have hsep := inv_two_sqrt_le_abs_log_sub_log hAn hBn hne
    set ξ : ℝ := Real.log (((P.2 + 1) * h : ℕ) : ℝ) - Real.log (((P.1 + 1) * k : ℕ) : ℝ) with hξ
    have hprod : ((((P.2 + 1) * h : ℕ) : ℝ) * (((P.1 + 1) * k : ℕ) : ℝ)) = mn * hk' := by
      push_cast
      ring
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hsep
      have : (0 : ℝ) < 1 / (2 * Real.sqrt ((((P.2 + 1) * h : ℕ) : ℝ) * (((P.1 + 1) * k : ℕ) : ℝ))) := by
        rw [hprod]
        positivity
      linarith
    have hinv : 1 / |ξ| ^ K ≤ 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by
      have h1 : 1 / |ξ| ≤ 2 * Real.sqrt (mn * hk') := by
        rw [← hprod]
        have hpos : 0 < 2 * Real.sqrt ((((P.2 + 1) * h : ℕ) : ℝ) * (((P.1 + 1) * k : ℕ) : ℝ)) := by
          rw [hprod]; positivity
        rw [div_le_iff₀ (abs_pos.mpr hξ0)]
        have := hsep
        rw [div_le_iff₀ hpos] at this
        linarith
      have h2 : (1 / |ξ|) ^ K ≤ (2 * Real.sqrt (mn * hk')) ^ K :=
        pow_le_pow_left₀ (by positivity) h1 K
      rw [one_div_pow] at h2
      refine h2.trans (le_of_eq ?_)
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity),
        show (1 / 2 : ℝ) * K = (K : ℝ) / 2 by ring]
    -- the oscillation bound at `y = mn·x`
    have hy : 0 < mn * x := by positivity
    have hosc := hC p q η (mn * x) ξ hL hpq hη hy hξ0
    -- notation for the two pieces
    set J : ℝ := windowCarrierJetConst K η (p - η) ((p - η) / 2)
      * (Real.exp 8 * (1 + (q + η) + (p - η) / 2) ^ 4) * Real.sqrt Real.pi with hJdef
    set G : ℝ := C * (1 + (q + η)) ^ 4
      * (Real.exp 16 * Real.exp (-(((p - η) / 2) ^ 2) / 2) * Real.sqrt (4 * Real.pi)) with hGdef
    have hJ0 : 0 ≤ J := by
      have := windowCarrierJetConst_nonneg K hη (show 0 < p - η by linarith) ((p - η) / 2)
      have h1 : 0 ≤ 1 + (q + η) + (p - η) / 2 := by linarith
      positivity
    have hG0 : 0 ≤ G := by
      have : 0 ≤ 1 + (q + η) := by linarith
      positivity
    have hlen : 0 ≤ q - p + 2 * η := by linarith
    have hpow1 : 1 ≤ (mn * hk') ^ ((K : ℝ) / 2) :=
      Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hmn1 hhk1) (by positivity)
    -- combine: `J/|ξ|^K + G ≤ (J 2^K + G) (mn hk')^{K/2}`
    have hcomb : J / |ξ| ^ K + G ≤ (J * 2 ^ K + G) * (mn * hk') ^ ((K : ℝ) / 2) := by
      have h1 : J / |ξ| ^ K ≤ J * 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by
        rw [div_eq_mul_one_div]
        calc J * (1 / |ξ| ^ K) ≤ J * (2 ^ K * (mn * hk') ^ ((K : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hinv hJ0
          _ = J * 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by ring
      have h2 : G ≤ G * (mn * hk') ^ ((K : ℝ) / 2) := le_mul_of_one_le_right hG0 hpow1
      linarith
    have hosc' : ‖∫ t, blockWindowC p q η t * dualCarrierWeight d (mn * x) t
        * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * (((mn * x)⁻¹ * Real.exp 1) * (q - p + 2 * η))
          * ((J * 2 ^ K + G) * (mn * hk') ^ ((K : ℝ) / 2)) := by
      refine hosc.trans ?_
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    -- assemble the powers
    have hsplit : (mn * hk') ^ ((K : ℝ) / 2) = mn ^ ((K : ℝ) / 2) * hk' ^ ((K : ℝ) / 2) :=
      Real.mul_rpow hmn0.le hhk0.le
    have hmninv : (mn * x)⁻¹ = mn ^ (-(1 : ℝ)) * x⁻¹ := by
      rw [Real.rpow_neg_one, mul_inv]
    calc mn ^ (-(1 / 2 + d)) * hk' ^ (-(1 / 2 - d))
          * ‖∫ t, blockWindowC p q η t * dualCarrierWeight d (mn * x) t
              * Complex.exp (-(ξ * t) * I)‖
        ≤ mn ^ (-(1 / 2 + d)) * hk' ^ (-(1 / 2 - d))
          * ((1 / (2 * Real.pi)) * (((mn * x)⁻¹ * Real.exp 1) * (q - p + 2 * η))
            * ((J * 2 ^ K + G) * (mn * hk') ^ ((K : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hosc' (by positivity)
      _ = dualOffDiagOscConst K C x p q η * hk' ^ ((K : ℝ) / 2 - 1 / 2 + d)
            * mn ^ ((K : ℝ) / 2 - 3 / 2 - d) := by
          rw [hsplit, hmninv, dualOffDiagOscConst, ← hJdef, ← hGdef,
            show hk' ^ ((K : ℝ) / 2 - 1 / 2 + d) = hk' ^ (-(1 / 2 - d)) * hk' ^ ((K : ℝ) / 2) by
              rw [← Real.rpow_add hhk0]; ring_nf,
            show mn ^ ((K : ℝ) / 2 - 3 / 2 - d)
                = mn ^ (-(1 / 2 + d)) * mn ^ (-(1 : ℝ)) * mn ^ ((K : ℝ) / 2) by
              rw [← Real.rpow_add hmn0, ← Real.rpow_add hmn0]; ring_nf]
          ring
  · exact mul_nonneg (mul_nonneg (dualOffDiagOscConst_nonneg K hC0 hx hη hL hpq)
      (by positivity)) (by positivity)

/-! ## The right-shift bound -/

/-- **Right-shift envelope of one dual off-diagonal term**: the window integral is bounded by the
window length times the supremum of the carrier weight on the window support. -/
theorem dualOffDiagTerm_le_shift {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (K'' : ℕ) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ Y τ : ℝ, 0 < Y → ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((K'' : ℝ) + 1 / 2)) * Y ^ (-(1 / 2 - d + K'')))
    {x p q η : ℝ} (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (P : ℕ × ℕ) :
    dualOffDiagTerm d x p q η h k P
      ≤ dualOffDiagShiftConst K'' C d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 + (K'' : ℝ)))) := by
  unfold dualOffDiagTerm
  split_ifs with hne
  · have hm : (0 : ℝ) < P.1 + 1 := by positivity
    have hn : (0 : ℝ) < P.2 + 1 := by positivity
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    set mn : ℝ := (P.1 + 1 : ℝ) * (P.2 + 1) with hmn
    set hk' : ℝ := (h : ℝ) * k with hhk
    have hmn0 : 0 < mn := by positivity
    have hhk0 : 0 < hk' := by positivity
    set ξ : ℝ := Real.log (((P.2 + 1) * h : ℕ) : ℝ) - Real.log (((P.1 + 1) * k : ℕ) : ℝ) with hξ
    have hlen : 0 ≤ q - p + 2 * η := by linarith
    have hqη : 0 ≤ q + η := by linarith
    have hy : 0 < mn * x := by positivity
    -- the pointwise supremum on the window support
    set M : ℝ := C * (1 + (q + η)) ^ (2 * ((K'' : ℝ) + 1 / 2)) * (mn * x) ^ (-(1 / 2 - d + K''))
      with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hbound : ∀ t : ℝ, ‖blockWindowC p q η t * dualCarrierWeight d (mn * x) t
        * Complex.exp (-(ξ * t) * I)‖
        ≤ (Set.Icc (p - η) (q + η)).indicator (fun _ => M) t := by
      intro t
      by_cases ht : t ∈ Set.Icc (p - η) (q + η)
      · rw [Set.indicator_of_mem ht, norm_mul, norm_mul, norm_cexp_neg_mul_I, mul_one]
        have hw := norm_blockWindowC_le_one p q η t
        have hA := hC (mn * x) t hy
        have habs : |t| ≤ q + η := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        have hpow : (1 + |t|) ^ (2 * ((K'' : ℝ) + 1 / 2))
            ≤ (1 + (q + η)) ^ (2 * ((K'' : ℝ) + 1 / 2)) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
        have hA' : ‖dualCarrierWeight d (mn * x) t‖ ≤ M := by
          refine hA.trans ?_
          rw [hMdef]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0)
            (by positivity)
        calc ‖blockWindowC p q η t‖ * ‖dualCarrierWeight d (mn * x) t‖
            ≤ 1 * M := mul_le_mul hw hA' (norm_nonneg _) zero_le_one
          _ = M := one_mul _
      · rw [Set.indicator_of_notMem ht, blockWindowC_eq_zero hη ht, zero_mul, zero_mul,
          norm_zero]
    have hint : Integrable ((Set.Icc (p - η) (q + η)).indicator (fun _ => M)) :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hI : ‖∫ t, blockWindowC p q η t * dualCarrierWeight d (mn * x) t
        * Complex.exp (-(ξ * t) * I)‖ ≤ (q - p + 2 * η) * M := by
      refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)).trans
        (le_of_eq ?_)
      rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith)]
      ring_nf
    have hsplit : (mn * x) ^ (-(1 / 2 - d + K'')) = mn ^ (-(1 / 2 - d + K'')) * x ^ (-(1 / 2 - d + K'')) :=
      Real.mul_rpow hmn0.le hx.le
    calc mn ^ (-(1 / 2 + d)) * hk' ^ (-(1 / 2 - d))
          * ‖∫ t, blockWindowC p q η t * dualCarrierWeight d (mn * x) t
              * Complex.exp (-(ξ * t) * I)‖
        ≤ mn ^ (-(1 / 2 + d)) * hk' ^ (-(1 / 2 - d)) * ((q - p + 2 * η) * M) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = dualOffDiagShiftConst K'' C d x p q η * hk' ^ (-(1 / 2 - d))
            * mn ^ (-(1 + (K'' : ℝ))) := by
          rw [hMdef, hsplit, dualOffDiagShiftConst,
            show mn ^ (-(1 + (K'' : ℝ))) = mn ^ (-(1 / 2 + d)) * mn ^ (-(1 / 2 - d + K'')) by
              rw [← Real.rpow_add hmn0]; ring_nf]
          ring
  · exact mul_nonneg (mul_nonneg (dualOffDiagShiftConst_nonneg K'' hC0 hx hη hL hpq)
      (by positivity)) (by positivity)

/-! ## The uniform two-regime envelope -/

/-- **The uniform envelope at threshold `Y₀`.** -/
theorem dualOffDiagTerm_le_envelope {d : ℝ} {K K'' : ℕ} (hK'' : 1 ≤ K'')
    {Osc Sh : ℝ} (hOsc : 0 ≤ Osc) (hSh : 0 ≤ Sh) {x p q η : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {Y₀ : ℝ} (hY₀ : 0 < Y₀) (P : ℕ × ℕ)
    (h1 : dualOffDiagTerm d x p q η h k P
      ≤ Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d)
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ ((K : ℝ) / 2 - 3 / 2 - d)))
    (h2 : dualOffDiagTerm d x p q η h k P
      ≤ Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d))
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 + (K'' : ℝ))))) :
    dualOffDiagTerm d x p q η h k P
      ≤ Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ))) := by
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  set mn : ℝ := (P.1 + 1 : ℝ) * (P.2 + 1) with hmn
  set hk' : ℝ := (h : ℝ) * k with hhk
  have hmn0 : 0 < mn := by positivity
  have hhk0 : 0 < hk' := by positivity
  have hA : 0 ≤ Osc * hk' ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1) * mn ^ (-(5 / 2 + d)) := by
    positivity
  have hB : 0 ≤ Sh * hk' ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1)) * mn ^ (-(2 : ℝ)) := by
    positivity
  rcases le_or_gt mn Y₀ with hle | hgt
  · -- oscillation regime
    have hfac : mn ^ ((K : ℝ) / 2 - 3 / 2 - d) ≤ Y₀ ^ ((K : ℝ) / 2 + 1) * mn ^ (-(5 / 2 + d)) := by
      have : mn ^ ((K : ℝ) / 2 - 3 / 2 - d) = mn ^ ((K : ℝ) / 2 + 1) * mn ^ (-(5 / 2 + d)) := by
        rw [← Real.rpow_add hmn0]; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hmn0.le hle (by positivity))
        (by positivity)
    calc dualOffDiagTerm d x p q η h k P
        ≤ Osc * hk' ^ ((K : ℝ) / 2 - 1 / 2 + d) * mn ^ ((K : ℝ) / 2 - 3 / 2 - d) := h1
      _ ≤ Osc * hk' ^ ((K : ℝ) / 2 - 1 / 2 + d) * (Y₀ ^ ((K : ℝ) / 2 + 1) * mn ^ (-(5 / 2 + d))) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = Osc * hk' ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1) * mn ^ (-(5 / 2 + d)) := by
          ring
      _ ≤ _ := le_add_of_nonneg_right hB
  · -- right-shift regime
    have hK1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
    have hfac : mn ^ (-(1 + (K'' : ℝ))) ≤ Y₀ ^ (-((K'' : ℝ) - 1)) * mn ^ (-(2 : ℝ)) := by
      have : mn ^ (-(1 + (K'' : ℝ))) = mn ^ (-((K'' : ℝ) - 1)) * mn ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add hmn0]; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hY₀ hgt.le (by linarith)) (by positivity)
    calc dualOffDiagTerm d x p q η h k P
        ≤ Sh * hk' ^ (-(1 / 2 - d)) * mn ^ (-(1 + (K'' : ℝ))) := h2
      _ ≤ Sh * hk' ^ (-(1 / 2 - d)) * (Y₀ ^ (-((K'' : ℝ) - 1)) * mn ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = Sh * hk' ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1)) * mn ^ (-(2 : ℝ)) := by ring
      _ ≤ _ := le_add_of_nonneg_left hA

/-! ## Summation over the pairs `(m,n)` -/

/-- **The dual off-diagonal envelope, summed over `(m,n)`.** Both external constants are those
of the oscillation and right-shift theorems; the envelope holds for every threshold `Y₀ > 0`. -/
theorem exists_tsum_dualOffDiagTerm_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (K : ℕ) {K'' : ℕ}
    (hK'' : 1 ≤ K'') :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (x p q η Y₀ : ℝ) (h k : ℕ), 0 < x → 0 < η → 4 ≤ p - η →
      p ≤ q → 0 < Y₀ → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConst K C₁ x p q η * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ ((K : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst K'' C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-((K'' : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_integral_blockWindow_dualCarrierWeight_le hd hdq K
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_dualCarrierWeight_le_rightShift hK''
  refine ⟨C₁, C₂, hC₁0, hC₂0, fun x p q η Y₀ h k hx hη hL hpq hY₀ hh hk => ?_⟩
  have hOsc := dualOffDiagOscConst_nonneg K hC₁0 hx hη hL hpq
  have hSh := dualOffDiagShiftConst_nonneg K'' (d := d) hC₂0 hx hη hL hpq
  set Osc := dualOffDiagOscConst K C₁ x p q η with hOscdef
  set Sh := dualOffDiagShiftConst K'' C₂ d x p q η with hShdef
  have hbound : ∀ P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
      ≤ Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ))) := fun P =>
    dualOffDiagTerm_le_envelope hK'' hOsc hSh hh hk hY₀ P
      (dualOffDiagTerm_le_osc K hC₁0 hC₁ hx hη hL hpq hh hk P)
      (dualOffDiagTerm_le_shift hd hdq K'' hC₂0 (fun Y τ hY => hC₂ d Y τ hd hdq hY) hx hη hL hpq
        hh hk P)
  have hr1 : (1 : ℝ) < 5 / 2 + d := by linarith
  have hr2 : (1 : ℝ) < 2 := by norm_num
  have hs1 : Summable (fun P : ℕ × ℕ =>
      Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))) :=
    (summable_prod_succ_rpow_neg hr1).mul_left _
  have hs2 : Summable (fun P : ℕ × ℕ =>
      Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)))) :=
    (summable_prod_succ_rpow_neg hr2).mul_left _
  have hterm : Summable (fun P : ℕ × ℕ => dualOffDiagTerm d x p q η h k P) :=
    Summable.of_nonneg_of_le (fun P => dualOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hbound (hs1.add hs2)
  calc ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
      ≤ ∑' P : ℕ × ℕ, (Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)))) :=
        hterm.tsum_le_tsum hbound (hs1.add hs2)
    _ = Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 := by
        rw [hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, tsum_prod_succ_rpow_neg hr1,
          tsum_prod_succ_rpow_neg hr2]

end RHTower
