import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GrandResponse
import GaloisForLFunctions.RHTower.XiZerosInfinite
import GaloisForLFunctions.RHTower.SeamStripRamification
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# The dilation organ has a natural boundary

The depth-`j` factor of the grand response vanishes when `j(σ+u)` is a nontrivial zeta zero, so
every zero `ρ` lands at `u = ρ/j − σ`.  Those landings have real part in `(−σ, −σ + 1/j]`, so they
can accumulate only on the line `Re u = −σ`; and because the completed zeta has zeros of
arbitrarily large ordinate, the quotients `ρ/j` come arbitrarily close to every purely imaginary
number, so every point of that line is an accumulation point of zeros of the response.  Since the
response is not identically zero on any disc of the chamber, no analytic function on a
neighbourhood of a boundary point can agree with it: the line is a natural boundary.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-! ## Nontrivial zeta zeros of arbitrarily large ordinate -/

/-- The support of the global `Ξ` divisor is unbounded: an infinite closed discrete subset of the
plane cannot lie in a ball. -/
theorem exists_xi_divisor_norm_gt (R : ℝ) :
    ∃ ρ ∈ (MeromorphicOn.divisor RHTower.xi Set.univ).support, R < ‖ρ‖ := by
  by_contra h
  push Not at h
  have hsub : (MeromorphicOn.divisor RHTower.xi Set.univ).support
      ⊆ Metric.closedBall (0 : ℂ) R := by
    intro ρ hρ
    simpa [Metric.mem_closedBall, dist_eq_norm] using h ρ hρ
  have hclosed : IsClosed ((MeromorphicOn.divisor RHTower.xi Set.univ).support) :=
    (MeromorphicOn.divisor RHTower.xi Set.univ).closedSupport isClosed_univ
  have hcpt : IsCompact ((MeromorphicOn.divisor RHTower.xi Set.univ).support) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed hsub
  exact RHTower.xiDivisorSupport_infinite
    (hcpt.finite (MeromorphicOn.divisor RHTower.xi Set.univ).discreteSupport)

/-- **Nontrivial zeta zeros of arbitrarily large ordinate.** -/
theorem exists_zetaZero_abs_im_gt (T : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im| := by
  obtain ⟨ρ, hmem, hnorm⟩ := exists_xi_divisor_norm_gt (|T| + 1)
  have hstrip := RHTower.xi_divisor_support_re_mem_open_unit ⟨ρ, hmem⟩
  have hzero := RHTower.xi_eq_zero_of_mem_divisor_support ⟨ρ, hmem⟩
  have h0 : 0 < ρ.re := hstrip.1
  have h1 : ρ.re < 1 := hstrip.2
  have hre : |ρ.re| < 1 := abs_lt.mpr ⟨by linarith, h1⟩
  have hle : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := norm_le_abs_re_add_abs_im ρ
  refine ⟨ρ, (RHTower.xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hzero, h0, h1, ?_⟩
  have hTle : T ≤ |T| := le_abs_self T
  linarith

/-- The same, with the sign of the ordinate matched to a prescribed nonzero direction. -/
theorem exists_zetaZero_im_div_gt {t : ℝ} (ht : t ≠ 0) (T : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im / t := by
  obtain ⟨ρ, hz, h0, h1, him⟩ := exists_zetaZero_abs_im_gt (|T| * |t|)
  have htabs : 0 < |t| := abs_pos.mpr ht
  have hkey : |T| < |ρ.im| / |t| := by
    rw [lt_div_iff₀ htabs]
    exact him
  have hTle : T ≤ |T| := le_abs_self T
  rcases le_or_gt 0 (ρ.im / t) with hsign | hsign
  · refine ⟨ρ, hz, h0, h1, ?_⟩
    have habs : |ρ.im / t| = ρ.im / t := abs_of_nonneg hsign
    rw [abs_div] at habs
    linarith [habs ▸ hkey]
  · refine ⟨(starRingEnd ℂ) ρ, ?_, ?_, ?_, ?_⟩
    · rw [riemannZeta_conj, hz, map_zero]
    · simpa using h0
    · simpa using h1
    · have hconj : ((starRingEnd ℂ) ρ).im / t = -(ρ.im / t) := by
        simp [neg_div]
      have habs : |ρ.im / t| = -(ρ.im / t) := abs_of_neg hsign
      rw [abs_div] at habs
      rw [hconj]
      linarith [habs ▸ hkey]

/-! ## The quotients `ρ/j` reach every purely imaginary number -/

theorem norm_div_natCast_sub_mul_I_le (ρ : ℂ) (t : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ‖ρ / (j : ℂ) - (t : ℂ) * I‖ ≤ (|ρ.re| + |ρ.im - (j : ℝ) * t|) / (j : ℝ) := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjC : ((j : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : j ≠ 0)
  have hsplit : ρ / (j : ℂ) - (t : ℂ) * I
      = (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I) / (j : ℂ) := by
    field_simp
    push_cast
    ring
  have hre : (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I).re = ρ.re := by
    simp [Complex.sub_re]
  have him : (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I).im = ρ.im - (j : ℝ) * t := by
    simp [Complex.sub_im]
  have hbound := norm_le_abs_re_add_abs_im (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I)
  rw [hre, him] at hbound
  rw [hsplit, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hbound hjR.le

/-- **The landing points reach every purely imaginary number.**  For every `t` and every `ε > 0`
there are a nontrivial zeta zero `ρ` and a depth `j ≥ 1` with `‖ρ/j − it‖ < ε`. -/
theorem exists_zetaZero_depth_near (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : ℂ) (j : ℕ), riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 1 ≤ j
      ∧ ‖ρ / (j : ℂ) - (t : ℂ) * I‖ < ε := by
  rcases eq_or_ne t 0 with rfl | ht
  · obtain ⟨ρ, hz, h0, h1, _⟩ := exists_zetaZero_abs_im_gt 0
    obtain ⟨j, hj1, hjbig⟩ : ∃ j : ℕ, 1 ≤ j ∧ (|ρ.re| + |ρ.im|) / ε < (j : ℝ) := by
      refine ⟨⌊(|ρ.re| + |ρ.im|) / ε⌋₊ + 1, by omega, ?_⟩
      have := Nat.lt_floor_add_one ((|ρ.re| + |ρ.im|) / ε)
      push_cast
      linarith
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    refine ⟨ρ, j, hz, h0, h1, hj1, ?_⟩
    have hb := norm_div_natCast_sub_mul_I_le ρ 0 hj1
    have hval : (|ρ.re| + |ρ.im - (j : ℝ) * 0|) / (j : ℝ)
        = (|ρ.re| + |ρ.im|) / (j : ℝ) := by norm_num
    rw [hval] at hb
    have hlt : (|ρ.re| + |ρ.im|) / (j : ℝ) < ε := by
      rw [div_lt_iff₀ hjR]
      rw [div_lt_iff₀ hε] at hjbig
      linarith
    exact lt_of_le_of_lt hb hlt
  · set T : ℝ := (1 + |t|) / ε + 1 with hT
    obtain ⟨ρ, hz, h0, h1, him⟩ := exists_zetaZero_im_div_gt ht T
    have hTpos : 1 < T := by
      have : 0 < (1 + |t|) / ε := by positivity
      rw [hT]; linarith
    have hq : (1 : ℝ) < ρ.im / t := lt_trans hTpos him
    set j : ℕ := ⌊ρ.im / t⌋₊ with hjdef
    have hj1 : 1 ≤ j := Nat.le_floor (by exact_mod_cast hq.le)
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjle : (j : ℝ) ≤ ρ.im / t := Nat.floor_le (by linarith)
    have hjgt : ρ.im / t < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have htabs : 0 < |t| := abs_pos.mpr ht
    have hdiff : |ρ.im - (j : ℝ) * t| < |t| := by
      have hfac : ρ.im - (j : ℝ) * t = t * (ρ.im / t - (j : ℝ)) := by
        field_simp
      rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ.im / t - (j : ℝ))]
      nlinarith
    have hreabs : |ρ.re| < 1 := abs_lt.mpr ⟨by linarith, h1⟩
    have hjbig : (1 + |t|) / ε < (j : ℝ) := by
      have : T - 1 < (j : ℝ) := by linarith
      rw [hT] at this
      linarith
    refine ⟨ρ, j, hz, h0, h1, hj1, ?_⟩
    refine lt_of_le_of_lt (norm_div_natCast_sub_mul_I_le ρ t hj1) ?_
    rw [div_lt_iff₀ hjR]
    rw [div_lt_iff₀ hε] at hjbig
    nlinarith

/-! ## Every zeta zero lands at every depth -/

theorem div_natCast_re (w : ℂ) {j : ℕ} (hj : j ≠ 0) : (w / (j : ℂ)).re = w.re / (j : ℝ) := by
  have hjR : ((j : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hj
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp

/-- The landing point of a zeta zero at depth `j`. -/
def landing (σ : ℝ) (w : ℂ) (j : ℕ) : ℂ := w / (j : ℂ) - ((σ : ℝ) : ℂ)

theorem re_landing (σ : ℝ) (w : ℂ) {j : ℕ} (hj : j ≠ 0) :
    (landing σ w j).re = w.re / (j : ℝ) - σ := by
  rw [landing, Complex.sub_re, div_natCast_re w hj, Complex.ofReal_re]

/-- **The landings sit in the chamber and hug the boundary line.**  A zero of real part in `(0,1)`
lands at real part in `(−σ, −σ + 1/j]`, so depth `j` pushes the landing to within `1/j` of the
line `Re u = −σ`. -/
theorem re_landing_mem (σ : ℝ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) {j : ℕ} (hj : 1 ≤ j) :
    -σ < (landing σ w j).re ∧ (landing σ w j).re < -σ + 1 / (j : ℝ) := by
  have hjne : j ≠ 0 := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  rw [re_landing σ w hjne]
  constructor
  · have : 0 < w.re / (j : ℝ) := div_pos hw0 hjR
    linarith
  · have hstep : w.re / (j : ℝ) < 1 / (j : ℝ) := by gcongr
    linarith

/-- **The grand response vanishes at every landing.**  The depth-`j` factor of the response is
`ζ(j(σ+u))`, which at `u = w/j − σ` is `ζ(w)`. -/
theorem grandResponse_landing_eq_zero (σ : ℝ) {w : ℂ} (hw : riemannZeta w = 0)
    (hw0 : 0 < w.re) {j : ℕ} (hj : 1 ≤ j) :
    grandResponse σ 0 (landing σ w j) = 0 := by
  have hjne : j ≠ 0 := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjC : ((j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hjne
  have hre : 0 < σ + (landing σ w j).re := by
    rw [re_landing σ w hjne]
    have : 0 < w.re / (j : ℝ) := div_pos hw0 hjR
    linarith
  have harg : ((σ : ℝ) : ℂ) + landing σ w j = w / (j : ℂ) := by
    rw [landing]; ring
  have hfac : depthFactor σ 0 j (landing σ w j) = 0 := by
    rw [depthFactor, harg, mul_div_cancel₀ _ hjC, add_zero, hw]
  have hmem : j - 1 ∈ Finset.range j := Finset.mem_range.mpr (by omega)
  have hprod : depthProduct σ 0 j (landing σ w j) = 0 := by
    refine Finset.prod_eq_zero hmem ?_
    have hidx : j - 1 + 1 = j := by omega
    rw [hidx]
    exact hfac
  rw [grandResponse_split σ 0 hre j, hprod, zero_mul]

/-- **Every point of the line `Re u = −σ` is a limit of zeros of the dilation organ.** -/
theorem exists_grandResponse_zero_near (σ : ℝ) {p : ℂ} (hp : p.re = -σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℂ, ‖u - p‖ < ε ∧ -σ < u.re ∧ grandResponse σ 0 u = 0 := by
  obtain ⟨ρ, j, hz, h0, h1, hj, hnear⟩ := exists_zetaZero_depth_near p.im hε
  refine ⟨landing σ ρ j, ?_, (re_landing_mem σ h0 h1 hj).1,
    grandResponse_landing_eq_zero σ hz h0 hj⟩
  have hpform : p = -((σ : ℝ) : ℂ) + ((p.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hp]
  have hdiff : landing σ ρ j - p = ρ / (j : ℂ) - ((p.im : ℝ) : ℂ) * I := by
    rw [landing]
    conv_lhs => rw [hpform]
    ring
  rw [hdiff]
  exact hnear

end

end GaloisForLFunctions.HTGeometry
