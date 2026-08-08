import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionOrderLaw
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.MobiusEvenIndexPositiveRecurrence
import GaloisForLFunctions.RHTower.EvenIndexHermitianOrderLowerEdge

/-!
# The one-sided lower edge of the even additive Mertens convolution order

A global subpower bound on the **positive part** of the `2k`-fold additive Mertens convolution
forces its exponent past the zeta zero abscissa: if `Re C_k(N) ≤ C (N+1)^λ` for every `N`, then
`λ ≥ 2k(1+Θ) - 1` (`le_of_mertensEvenConvolution_subpower`).

The mechanism is the exact even Abel identity `A(z)^{2k} = (1-z)^{2k} ∑ C_k(N) z^N`, which turns a
one-sided coefficient bound into radial decay `|Φ(x)| ≤ D x^{-b}` with `b = (λ+1-2k)/(2k)`, and the
half-plane identity theorem for `Γ/ζ`, which forbids that decay below any zeta zero.  Negative
excursions of `C_k` are discarded throughout.

Consequences: the logarithmic order `Λ_k = limsup log(1 + C_k(N)^+)/log(N+1)` satisfies
`Λ_k ≥ 2k(1+Θ) - 1` (`le_mertensEvenConvolutionOrder`), and since `Θ ≥ 1/2` unconditionally, every
even convolution order has near-critical **positive** excursions
`C_k(N) ≥ (N+1)^{3k-1-ε}` at infinitely many `N`
(`frequently_rpow_le_mertensEvenConvolution`).
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

theorem moebiusProfile_eq_mobiusDiscreteLaplaceTransform :
    moebiusProfile = mobiusDiscreteLaplaceTransform := by
  funext x
  rfl

/-! ### The Abel bound from a one-sided subpower coefficient bound -/

theorem norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_subpower
    {k : ℕ} {lam C x : ℝ} (hlam : 0 ≤ lam) (hC : 0 ≤ C) (hx : 0 < x) (hx1 : x ≤ 1)
    (hupper : ∀ N : ℕ, (mobiusMertensEvenConvolution k N).re ≤ C * ((N : ℝ) + 1) ^ lam) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k)
      ≤ C * mixedSubpowerAbelConstant lam * x ^ (2 * (k : ℝ) - lam - 1) := by
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le hlam hx
  have hb : Summable (fun N : ℕ => (C * ((N : ℝ) + 1) ^ lam) * Real.exp (-((N : ℝ) * x))) := by
    refine (hmoment.1.mul_left C).congr fun N => ?_
    ring
  have hkey := norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionUpper k
    (fun N => C * ((N : ℝ) + 1) ^ lam) hupper hx hb
  have hAbel : 0 ≤ mixedSubpowerAbelConstant lam := mixedSubpowerAbelConstant_nonneg hlam
  have htsum : (∑' N : ℕ, (C * ((N : ℝ) + 1) ^ lam) * Real.exp (-((N : ℝ) * x)))
      ≤ C * (mixedSubpowerAbelConstant lam * (1 / x) ^ (lam + 1)) := by
    have heq : (∑' N : ℕ, (C * ((N : ℝ) + 1) ^ lam) * Real.exp (-((N : ℝ) * x)))
        = C * ∑' N : ℕ, ((N : ℝ) + 1) ^ lam * Real.exp (-((N : ℝ) * x)) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun N => by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (tsum_natSucc_rpow_exp_neg_le hlam hx hx1) hC
  have hexp1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp2 : 1 - Real.exp (-x) ≤ x := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hone : (0 : ℝ) ≤ 1 - Real.exp (-x) := by linarith
  have hpowle : (1 - Real.exp (-x)) ^ (2 * k) ≤ x ^ (2 * k) :=
    pow_le_pow_left₀ hone hexp2 _
  have htsum0 : (0 : ℝ) ≤ ∑' N : ℕ, (C * ((N : ℝ) + 1) ^ lam) * Real.exp (-((N : ℝ) * x)) := by
    refine tsum_nonneg fun N => ?_
    have : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ lam := Real.rpow_nonneg (by positivity) _
    positivity
  have hchain : ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k)
      ≤ x ^ (2 * k) * (C * (mixedSubpowerAbelConstant lam * (1 / x) ^ (lam + 1))) := by
    refine hkey.trans ?_
    refine le_trans (mul_le_mul_of_nonneg_right hpowle htsum0) ?_
    exact mul_le_mul_of_nonneg_left htsum (by positivity)
  refine hchain.trans (le_of_eq ?_)
  have h1 : (1 / x : ℝ) ^ (lam + 1) = x ^ (-(lam + 1)) := by
    rw [one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
  have h2 : (x : ℝ) ^ (2 * k) = x ^ (2 * (k : ℝ)) := by
    rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3 : x ^ (2 * (k : ℝ)) * x ^ (-(lam + 1)) = x ^ (2 * (k : ℝ) - lam - 1) := by
    rw [← Real.rpow_add hx]
    ring_nf
  rw [h1, h2, ← h3]
  ring_nf

/-! ### The lower edge -/

/-- **The one-sided lower edge.**  A global subpower bound on the positive part of the `2k`-fold
additive Mertens convolution forces its exponent past `2k(1+Θ) - 1`. -/
theorem le_of_mertensEvenConvolution_subpower {k : ℕ} (hk : 0 < k) {lam C : ℝ}
    (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hupper : ∀ N : ℕ, (mobiusMertensEvenConvolution k N).re ≤ C * ((N : ℝ) + 1) ^ lam) :
    2 * (k : ℝ) * (1 + zetaZeroAbscissa) - 1 ≤ lam := by
  by_contra hcon
  push Not at hcon
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  set b₀ : ℝ := (lam + 1 - 2 * (k : ℝ)) / (2 * (k : ℝ)) with hb₀def
  set b : ℝ := max b₀ 0 with hbdef
  have hb0 : 0 ≤ b := le_max_right _ _
  have hb₀Θ : b₀ < zetaZeroAbscissa := by
    rw [hb₀def, div_lt_iff₀ hkR]
    nlinarith [hcon]
  have hbΘ : b < zetaZeroAbscissa :=
    max_lt hb₀Θ zetaZeroAbscissa_pos
  have hAbel : 0 ≤ mixedSubpowerAbelConstant lam := mixedSubpowerAbelConstant_nonneg hlam
  have hconst : (0 : ℝ) ≤ C * mixedSubpowerAbelConstant lam := mul_nonneg hC hAbel
  -- radial decay of the Möbius profile
  have hO : mobiusDiscreteLaplaceTransform =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C * mixedSubpowerAbelConstant lam) ^ ((2 * (k : ℝ))⁻¹), ?_⟩
    have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hev] with x hx hx1
    have hxpos : (0 : ℝ) < x := hx
    have hbound := norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_subpower
      hlam hC hxpos hx1.le hupper
    set z : ℝ := ‖mobiusDiscreteLaplaceTransform x‖ with hzdef
    set M : ℝ := C * mixedSubpowerAbelConstant lam * x ^ (2 * (k : ℝ) - lam - 1) with hMdef
    have hM0 : 0 ≤ M := by
      rw [hMdef]
      exact mul_nonneg hconst (Real.rpow_nonneg hxpos.le _)
    have hroot : z ≤ M ^ ((2 * (k : ℝ))⁻¹) := by
      have hcast : z ^ (2 * (k : ℝ)) = z ^ (2 * k) := by
        rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      have hle : z ^ (2 * (k : ℝ)) ≤ M := by rw [hcast]; exact hbound
      have hmono := Real.rpow_le_rpow (by positivity) hle (le_of_lt (inv_pos.mpr hkR))
      rwa [← Real.rpow_mul (by positivity), mul_inv_cancel₀ (ne_of_gt hkR),
        Real.rpow_one] at hmono
    refine hroot.trans ?_
    have hMsplit : M ^ ((2 * (k : ℝ))⁻¹)
        = (C * mixedSubpowerAbelConstant lam) ^ ((2 * (k : ℝ))⁻¹) * x ^ (-b₀) := by
      rw [hMdef, Real.mul_rpow hconst (Real.rpow_nonneg hxpos.le _), ← Real.rpow_mul hxpos.le]
      congr 1
      rw [hb₀def]
      field_simp
      ring_nf
    rw [hMsplit, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hconst _)
    have hxle : x ≤ 1 := hx1.le
    have hb₀b : -b ≤ -b₀ := by
      have : b₀ ≤ b := le_max_left _ _
      linarith
    exact Real.rpow_le_rpow_of_exponent_ge hxpos hxle hb₀b
  obtain ⟨ρ, hρz, hρ1, hbρ⟩ := exists_zetaZero_mem_openStrip_lt_re hbΘ
  refine not_isBigO_moebiusProfile_rpow hb0 hρz hρ1 hbρ ?_
  rw [moebiusProfile_eq_mobiusDiscreteLaplaceTransform]
  exact hO

/-! ### The logarithmic order and its lower edge -/

/-- The one-sided logarithmic order `Λ_k` of the `2k`-fold additive Mertens convolution. -/
def mertensEvenConvolutionOrder (k : ℕ) : ℝ :=
  Filter.limsup
    (fun N : ℕ => Real.log (1 + max (mobiusMertensEvenConvolution k N).re 0)
      / Real.log ((N : ℝ) + 1)) Filter.atTop

theorem norm_mobiusMertensEvenConvolution_le {j : ℕ} (N : ℕ) :
    ‖mobiusMertensEvenConvolution (j + 1) N‖ ≤ ((N : ℝ) + 1) ^ (4 * j + 3) := by
  have h := norm_additiveConvolutionPower_succ_le mobiusAdditiveTriangleSecondCesaro
    (A := 1) (α := 3) (by norm_num) (by norm_num)
    (fun N => by simpa [Real.rpow_natCast] using norm_mobiusAdditiveTriangleSecondCesaro_le N) j N
  have hexp : ((j + 1 : ℕ) : ℝ) * 3 + (j : ℝ) = ((4 * j + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [one_pow, one_mul, hexp, Real.rpow_natCast] at h
  exact h

theorem isBoundedUnder_mertensEvenConvolutionOrderSeq (j : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => Real.log (1 + max (mobiusMertensEvenConvolution (j + 1) N).re 0)
        / Real.log ((N : ℝ) + 1)) := by
  refine isBoundedUnder_log_one_add_div_log
    (C := 1) (d := 4 * j + 3) one_pos (fun N => le_max_right _ _) fun N => ?_
  rw [one_mul]
  refine max_le ?_ (by positivity)
  exact (Complex.re_le_norm _).trans (norm_mobiusMertensEvenConvolution_le N)

theorem mertensEvenConvolutionOrder_nonneg (j : ℕ) :
    0 ≤ mertensEvenConvolutionOrder (j + 1) := by
  refine Filter.le_limsup_of_frequently_le ?_ (isBoundedUnder_mertensEvenConvolutionOrderSeq j)
  refine Filter.Eventually.frequently ?_
  filter_upwards with N
  exact GaloisForLFunctions.HTGeometry.log_one_add_max_div_log_nonneg
    (fun N => (mobiusMertensEvenConvolution (j + 1) N).re) N

/-- **The lower edge of the even Mertens convolution order.**  `Λ_k ≥ 2k(1+Θ) - 1`. -/
theorem le_mertensEvenConvolutionOrder (j : ℕ) :
    2 * ((j : ℝ) + 1) * (1 + zetaZeroAbscissa) - 1
      ≤ mertensEvenConvolutionOrder (j + 1) := by
  by_contra hcon
  push Not at hcon
  set Psi : ℝ := mertensEvenConvolutionOrder (j + 1) with hPsi
  have hPsi0 : 0 ≤ Psi := mertensEvenConvolutionOrder_nonneg j
  have hΘ := half_le_zetaZeroAbscissa
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have htarget : 0 < 2 * ((j : ℝ) + 1) * (1 + zetaZeroAbscissa) - 1 := by nlinarith
  set lam : ℝ := (Psi + (2 * ((j : ℝ) + 1) * (1 + zetaZeroAbscissa) - 1)) / 2 with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; linarith
  have hlamPsi : Psi < lam := by rw [hlamdef]; linarith
  have hlamTarget : lam < 2 * ((j : ℝ) + 1) * (1 + zetaZeroAbscissa) - 1 := by
    rw [hlamdef]; linarith
  have hev := Filter.eventually_lt_of_limsup_lt hlamPsi
    (isBoundedUnder_mertensEvenConvolutionOrderSeq j)
  obtain ⟨C, hC0, hCbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_global_subpower_of_eventually hlam0 hev
  have hkey := le_of_mertensEvenConvolution_subpower (k := j + 1) (Nat.succ_pos j)
    hlam0 hC0 hCbound
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hkey
  linarith

/-- **Unconditional near-critical positive excursions.**  Since `Θ ≥ 1/2`, every even additive
Mertens convolution order exceeds `(N+1)^{3k-1-ε}` at infinitely many `N`. -/
theorem frequently_rpow_le_mertensEvenConvolution (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ N : ℕ in atTop,
      ((N : ℝ) + 1) ^ (3 * ((j : ℝ) + 1) - 1 - ε)
        ≤ (mobiusMertensEvenConvolution (j + 1) N).re := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set α : ℝ := 3 * ((j : ℝ) + 1) - 1 - ε with hαdef
  set lam : ℝ := max α 0 with hlamdef
  have hlam0 : 0 ≤ lam := le_max_right _ _
  have hev : ∀ᶠ N : ℕ in atTop,
      (mobiusMertensEvenConvolution (j + 1) N).re ≤ ((N : ℝ) + 1) ^ lam := by
    filter_upwards [hcon] with N hN
    have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    refine le_trans (le_of_lt (not_le.mp hN)) ?_
    exact Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
  obtain ⟨C, hC0, hCbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_global_subpower_of_eventually_le hlam0 hev
  have hkey := le_of_mertensEvenConvolution_subpower (k := j + 1) (Nat.succ_pos j)
    hlam0 hC0 hCbound
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hkey
  have hΘ := half_le_zetaZeroAbscissa
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rcases le_or_gt α 0 with h | h
  · rw [hlamdef, max_eq_right h] at hkey
    nlinarith [hkey, hΘ]
  · rw [hlamdef, max_eq_left h.le, hαdef] at hkey
    nlinarith [hkey, hΘ]

end

end RHTower
