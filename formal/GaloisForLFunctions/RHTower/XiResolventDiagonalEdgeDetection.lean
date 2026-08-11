import GaloisForLFunctions.RHTower.XiResolventHankelMatrixLadder
import GaloisForLFunctions.HTGeometry.UnitPowerSumOscillation

/-!
# Diagonal edge detection: moment positivity pins the lowest zero to the critical line

The diagonal of the resolvent Hankel criterion — nonnegativity of the moments
`R n X = sum_q u_q^(n+1)` alone, with no bilinear input — already carries zero-location
information: if every moment at a single shift `X ≥ 0` is nonnegative, then among the divisor
copies of **maximal resolvent modulus** (the zeros minimizing `‖alpha^2 + X‖`, i.e. the lowest
zeros of `xi`) at least one lies on the critical line.

Mechanism: normalize the finitely many maximal-modulus resolvent points to the unit circle.  If
none of them were real — no critical-line copy at the spectral edge — all normalized points would
avoid `1`, while the moments dominate the top power sums up to a geometrically decaying tail from
the strictly smaller remaining moduli.  Unit power sums avoiding `1` oscillate below every
decaying floor, so some moment would be negative.  A real positive maximal point forces the
shifted spectral square real, and the height gap then forces the spectral point itself real.

So the moment sequence detects the reality of the spectral edge, and — iterating in the
contrapositive — any configuration whose lowest zeros are all off-line is already refuted by a
single strictly negative diagonal moment.  This is the formal counterpart of the observed
certificate structure of the Hankel ladder: its bulk is equilibrium, its RH content is
concentrated at the edge.
-/

open Complex

namespace RHTower

noncomputable section

/-- The resolvent modulus attains its maximum on the divisor. -/
theorem exists_max_norm_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    ∃ q₀ : XiZeroCopy, ∀ q, ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q₀‖ := by
  obtain ⟨qa⟩ := nonempty_xiZeroCopy
  have hpos : 0 < ‖xiResolventPoint X qa‖ :=
    norm_pos_iff.mpr (xiResolventPoint_ne_zero hX qa)
  have hfin := finite_setOf_le_norm_xiResolventPoint hX hpos
  have hqa : qa ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    exact le_rfl
  obtain ⟨q₀, hq₀mem, hq₀max⟩ := hfin.toFinset.exists_max_image
    (fun q => ‖xiResolventPoint X q‖) ⟨qa, hqa⟩
  refine ⟨q₀, fun q => ?_⟩
  by_cases hq : q ∈ hfin.toFinset
  · exact hq₀max q hq
  · rw [Set.Finite.mem_toFinset] at hq
    have h1 : ‖xiResolventPoint X q‖ < ‖xiResolventPoint X qa‖ := not_le.mp hq
    exact le_trans h1.le (hq₀max qa hqa)

/-- **Diagonal edge detection.**  If every resolvent moment at one shift is nonnegative, then
among the divisor copies of maximal resolvent modulus — the lowest zeros — at least one lies on
the critical line. -/
theorem exists_criticalLine_copy_of_forall_moment_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ, 0 ≤ (xiResolventMoment n X).re) :
    ∃ q : XiZeroCopy, (xiSpectralPoint q).im = 0 ∧
      ∀ q', ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖ := by
  classical
  by_contra hcon
  obtain ⟨q₀, hq₀⟩ := exists_max_norm_xiResolventPoint hX
  set r : ℝ := ‖xiResolventPoint X q₀‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr (xiResolventPoint_ne_zero hX q₀)
  have hTfin : {q : XiZeroCopy | r ≤ ‖xiResolventPoint X q‖}.Finite :=
    finite_setOf_le_norm_xiResolventPoint hX hrpos
  set T : Finset XiZeroCopy := hTfin.toFinset with hT
  have hmemT : ∀ q, q ∈ T ↔ r ≤ ‖xiResolventPoint X q‖ := by
    intro q
    rw [hT, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hq₀T : q₀ ∈ T := (hmemT q₀).mpr le_rfl
  have hTne : T.Nonempty := ⟨q₀, hq₀T⟩
  have hTval : ∀ q ∈ T, ‖xiResolventPoint X q‖ = r := fun q hq =>
    le_antisymm (hq₀ q) ((hmemT q).mp hq)
  have hoff : ∀ q ∈ T, (xiSpectralPoint q).im ≠ 0 := by
    intro q hq him
    refine hcon ⟨q, him, fun q' => ?_⟩
    rw [hTval q hq]
    exact hq₀ q'
  set v : XiZeroCopy → ℂ := fun q => xiResolventPoint X q / (r : ℂ) with hv
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hvnorm : ∀ q ∈ T, ‖v q‖ = 1 := by
    intro q hq
    rw [hv]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [hTval q hq]
    exact div_self hrpos.ne'
  have hvne1 : ∀ q ∈ T, v q ≠ 1 := by
    intro q hq h1
    have hu : xiResolventPoint X q = (r : ℂ) := by
      rw [hv] at h1
      rw [div_eq_iff hrC, one_mul] at h1
      exact h1
    have hwreal : xiSpectralPoint q ^ 2 + (X : ℂ) = ((r : ℝ) : ℂ)⁻¹ := by
      have h2 : ((xiSpectralPoint q ^ 2 + (X : ℂ))⁻¹) = ((r : ℝ) : ℂ) := hu
      calc xiSpectralPoint q ^ 2 + (X : ℂ)
          = ((xiSpectralPoint q ^ 2 + (X : ℂ))⁻¹)⁻¹ := (inv_inv _).symm
        _ = ((r : ℝ) : ℂ)⁻¹ := by rw [h2]
    have himsq : (xiSpectralPoint q ^ 2).im = 0 := by
      have h3 : (xiSpectralPoint q ^ 2 + (X : ℂ)).im = 0 := by
        rw [hwreal, ← Complex.ofReal_inv]
        exact Complex.ofReal_im _
      rw [Complex.add_im, Complex.ofReal_im, add_zero] at h3
      exact h3
    have hprod : 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 := by
      have h4 : (xiSpectralPoint q ^ 2).im =
          2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
        rw [sq, Complex.mul_im]
        ring
      rw [h4] at himsq
      exact himsq
    have hrene : (xiSpectralPoint q).re ≠ 0 := by
      have h := xiZeroCopy_two_lt_im_sq q
      rw [← xiSpectralPoint_re_eq] at h
      intro h0
      rw [h0] at h
      norm_num at h
    have him0 : (xiSpectralPoint q).im = 0 := by
      rcases mul_eq_zero.mp hprod with h5 | h5
      · rcases mul_eq_zero.mp h5 with h6 | h6
        · norm_num at h6
        · exact absurd h6 hrene
      · exact h5
    exact hoff q hq him0
  obtain ⟨ρ, hρ0, hρlt, hρbound⟩ :
      ∃ ρ, 0 ≤ ρ ∧ ρ < r ∧ ∀ q, q ∉ T → ‖xiResolventPoint X q‖ ≤ ρ := by
    have hhalf : (0 : ℝ) < r / 2 := by linarith
    have hS2fin : {q : XiZeroCopy | r / 2 ≤ ‖xiResolventPoint X q‖}.Finite :=
      finite_setOf_le_norm_xiResolventPoint hX hhalf
    set D : Finset XiZeroCopy := hS2fin.toFinset \ T with hD
    rcases D.eq_empty_or_nonempty with hDe | hDne
    · refine ⟨r / 2, by linarith, by linarith, fun q hq => ?_⟩
      by_contra hgt
      rw [not_le] at hgt
      have hqD : q ∈ D := by
        rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset]
        exact ⟨le_of_lt hgt, hq⟩
      rw [hDe] at hqD
      exact absurd hqD (Finset.notMem_empty q)
    · obtain ⟨qd, hqdD, hqdmax⟩ := D.exists_max_image
        (fun q => ‖xiResolventPoint X q‖) hDne
      have hqdT : qd ∉ T := by
        rw [hD, Finset.mem_sdiff] at hqdD
        exact hqdD.2
      refine ⟨max ‖xiResolventPoint X qd‖ (r / 2),
        le_trans (by linarith) (le_max_right _ _), ?_, ?_⟩
      · rw [max_lt_iff]
        refine ⟨?_, by linarith⟩
        exact lt_of_not_ge fun hge => hqdT ((hmemT qd).mpr hge)
      · intro q hq
        by_cases hq2 : r / 2 ≤ ‖xiResolventPoint X q‖
        · have hqD : q ∈ D := by
            rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset]
            exact ⟨hq2, hq⟩
          exact le_trans (hqdmax q hqD) (le_max_left _ _)
        · exact le_trans (not_le.mp hq2).le (le_max_right _ _)
  have hsub : Summable (fun q : ↑(↑T : Set XiZeroCopy)ᶜ => ‖xiResolventPoint X ↑q‖) :=
    (summable_norm_xiResolventPoint hX).subtype _
  set S₀c : ℝ := ∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, ‖xiResolventPoint X ↑q‖ with hS₀c
  have hS₀nn : 0 ≤ S₀c := tsum_nonneg fun q => norm_nonneg _
  have htail : ∀ n : ℕ,
      ‖∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1)‖ ≤
        S₀c * ρ ^ n := by
    intro n
    have hsubpow : Summable (fun q : ↑(↑T : Set XiZeroCopy)ᶜ =>
        ‖xiResolventPoint X ↑q ^ (n + 1)‖) :=
      (summable_norm_xiResolventPoint_pow hX n).subtype _
    calc ‖∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1)‖
        ≤ ∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, ‖xiResolventPoint X ↑q ^ (n + 1)‖ :=
          norm_tsum_le_tsum_norm hsubpow
      _ ≤ ∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, ‖xiResolventPoint X ↑q‖ * ρ ^ n := by
          refine Summable.tsum_le_tsum (fun q => ?_) hsubpow (hsub.mul_right _)
          rw [norm_pow, pow_succ']
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hqnT : (↑q : XiZeroCopy) ∉ T := by
            have h := q.2
            simp only [Set.mem_compl_iff, Finset.mem_coe] at h
            exact h
          exact pow_le_pow_left₀ (norm_nonneg _) (hρbound _ hqnT) n
      _ = S₀c * ρ ^ n := by
          rw [tsum_mul_right]
  have hlow : ∀ n : ℕ, -((S₀c / r) * (ρ / r) ^ n) ≤ (∑ q ∈ T, v q ^ (n + 1)).re := by
    intro n
    have hsplit := (summable_xiResolventPoint_pow hX n).sum_add_tsum_compl (s := T)
    have hmoment : (∑ q ∈ T, xiResolventPoint X q ^ (n + 1)).re =
        (xiResolventMoment n X).re -
          (∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1)).re := by
      have h1 : (∑ q ∈ T, xiResolventPoint X q ^ (n + 1)) +
          ∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1) =
            xiResolventMoment n X := by
        rw [xiResolventMoment]
        exact hsplit
      have h2 := congrArg Complex.re h1
      rw [Complex.add_re] at h2
      linarith
    have hvsum : (∑ q ∈ T, v q ^ (n + 1)) =
        (∑ q ∈ T, xiResolventPoint X q ^ (n + 1)) / ((r : ℝ) : ℂ) ^ (n + 1) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hv, div_pow]
    have hre : (∑ q ∈ T, v q ^ (n + 1)).re =
        (∑ q ∈ T, xiResolventPoint X q ^ (n + 1)).re / r ^ (n + 1) := by
      rw [hvsum, ← Complex.ofReal_pow, div_eq_mul_inv, ← Complex.ofReal_inv,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        div_eq_mul_inv]
    have htailre : -(S₀c * ρ ^ n) ≤
        -(∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1)).re := by
      have h1 := htail n
      have h2 := Complex.abs_re_le_norm
        (∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1))
      have h3 := le_abs_self
        (∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1)).re
      linarith
    have hrpow : (0 : ℝ) < r ^ (n + 1) := pow_pos hrpos _
    have hnum : -(S₀c * ρ ^ n) ≤ (xiResolventMoment n X).re -
        (∑' q : ↑(↑T : Set XiZeroCopy)ᶜ, xiResolventPoint X ↑q ^ (n + 1)).re := by
      have := hmom n
      linarith
    have halg : -((S₀c / r) * (ρ / r) ^ n) = -(S₀c * ρ ^ n) / r ^ (n + 1) := by
      rw [div_pow, pow_succ']
      field_simp
    rw [hre, hmoment, halg, div_le_div_iff₀ hrpow hrpow]
    exact mul_le_mul_of_nonneg_right hnum hrpow.le
  have hC : 0 ≤ S₀c / r := div_nonneg hS₀nn hrpos.le
  have hκ0 : 0 ≤ ρ / r := div_nonneg hρ0 hrpos.le
  have hκ1 : ρ / r < 1 := (div_lt_one hrpos).mpr hρlt
  exact GaloisForLFunctions.HTGeometry.unitPowerSum_no_decaying_lower_bound
    hTne hvnorm hvne1 hC hκ0 hκ1 hlow

/-- **Edge negativity witness**: if every divisor copy of maximal resolvent modulus is
off-critical, some diagonal moment is strictly negative. -/
theorem exists_moment_re_neg_of_offline_edge {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ q : XiZeroCopy, (∀ q', ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖) →
      (xiSpectralPoint q).im ≠ 0) :
    ∃ n : ℕ, (xiResolventMoment n X).re < 0 := by
  by_contra hno
  simp only [not_exists, not_lt] at hno
  obtain ⟨q, hq1, hq2⟩ := exists_criticalLine_copy_of_forall_moment_re_nonneg hX hno
  exact h q hq2 hq1

end

end RHTower
