import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# The lag pole series is positive-real right of the excess

Let `G(s) = Σ_ρ (ρ(1−ρ))⁻¹/(s − (ρ − ½))` be the Mittag-Leffler series of the zeros of `ξ`, the
Laplace transform of the lag function on `Re s > ½`.  Grouping each zero copy `q` with its partner
`q* = reflect(conj q)` (zero `1 − ρ̄`, weight `conj w_q`, pole `−conj(ρ − ½)`), the real part of a
partner pair at `s = σ + it` is

`2σ [X(σ² − a² + A²) + 4a²γA] / (N D₁ D₂)`,

with `ρ = ½ + a + iγ`, `X = ¼ − a² + γ²`, `N = X² + 4a²γ²`, `A = t − γ`,
`D₁ = (σ−a)² + A²`, `D₂ = (σ+a)² + A²`.  The bracket is a quadratic in `A` with nonpositive
discriminant exactly when `4a⁴γ² ≤ X²(σ² − a²)`.  Since every zero has `|a| < ½` and `γ² > 41/2`,
this holds for every copy once `σ ≥ 13/25`: **`Re G(s) ≥ 0` on `Re s ≥ 13/25` unconditionally**, and
on `Re s > 0` under RH (`a = 0`).  Conversely a pole `p₀ = ρ₀ − ½` with `Re p₀ > σ₀` forces
`Re G(p₀ − t) → −∞` as `t → 0⁺`, so **`Re G ≥ 0` on `Re s > σ₀` bounds every real part by `½ + σ₀`**,
and `RH ⟺ Re G ≥ 0 on Re s > 0`: the lag pole series is a positive-real function exactly under RH.
On the prime side, for `Re s ≥ 13/25` the statement reads
`∫_0^∞ Φ(u) e^{−σu} cos(tu) du ≥ 0`: the damped lag function `Φ(u)e^{−σ|u|}` is positive-definite.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Partner coordinates -/

/-- The partner copy `reflect (conj q)`, whose zero is `1 − ρ̄`. -/
def lagPartner : XiZeroCopy ≃ XiZeroCopy := xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv

theorem lagPartner_coe (q : XiZeroCopy) :
    ((lagPartner q).1 : ℂ) = 1 - (starRingEnd ℂ) (q.1 : ℂ) := rfl

/-! ## The real inequality of a partner pair -/

/-- `(X(σ−a) + 2aγA)((σ+a)² + A²) + (X(σ+a) − 2aγA)((σ−a)² + A²) = 2σ(X(σ²−a²+A²) + 4a²γA) ≥ 0`
when `4a⁴γ² ≤ X²(σ² − a²)`, `X > 0`, `σ ≥ 0`. -/
theorem pairNumerator_nonneg {X a γ σ A : ℝ} (hX : 0 < X) (hσ : 0 ≤ σ)
    (hcond : 4 * a ^ 4 * γ ^ 2 ≤ X ^ 2 * (σ ^ 2 - a ^ 2)) :
    0 ≤ (X * (σ - a) + 2 * a * γ * A) * ((σ + a) ^ 2 + A ^ 2)
        + (X * (σ + a) - 2 * a * γ * A) * ((σ - a) ^ 2 + A ^ 2) := by
  have hkey : 0 ≤ X * (σ ^ 2 - a ^ 2 + A ^ 2) + 4 * a ^ 2 * γ * A := by
    have h1 : 0 ≤ X * (X * A + 2 * a ^ 2 * γ) ^ 2 := mul_nonneg hX.le (sq_nonneg _)
    have h2 : 0 ≤ X * (X ^ 2 * (σ ^ 2 - a ^ 2) - 4 * a ^ 4 * γ ^ 2) :=
      mul_nonneg hX.le (by linarith)
    have h3 : X ^ 2 * (X * (σ ^ 2 - a ^ 2 + A ^ 2) + 4 * a ^ 2 * γ * A)
        = X * (X * A + 2 * a ^ 2 * γ) ^ 2 + X * (X ^ 2 * (σ ^ 2 - a ^ 2) - 4 * a ^ 4 * γ ^ 2) := by
      ring
    have hX2 : 0 < X ^ 2 := by positivity
    have h4 : 0 ≤ X ^ 2 * (X * (σ ^ 2 - a ^ 2 + A ^ 2) + 4 * a ^ 2 * γ * A) := by
      rw [h3]; linarith
    exact (mul_nonneg_iff_of_pos_left hX2).mp h4
  have hexp : (X * (σ - a) + 2 * a * γ * A) * ((σ + a) ^ 2 + A ^ 2)
        + (X * (σ + a) - 2 * a * γ * A) * ((σ - a) ^ 2 + A ^ 2)
      = 2 * σ * (X * (σ ^ 2 - a ^ 2 + A ^ 2) + 4 * a ^ 2 * γ * A) := by ring
  rw [hexp]
  exact mul_nonneg (by linarith) hkey

/-- The partner-pair sum of real parts, in real coordinates, is nonnegative. -/
theorem pairRatio_nonneg {X a γ σ A N : ℝ} (hX : 0 < X) (hN : 0 < N) (hσ : 0 ≤ σ) (ha : |a| < σ)
    (hcond : 4 * a ^ 4 * γ ^ 2 ≤ X ^ 2 * (σ ^ 2 - a ^ 2)) :
    0 ≤ (X * (σ - a) + 2 * a * γ * A) / (N * ((σ - a) ^ 2 + A ^ 2))
        + (X * (σ + a) - 2 * a * γ * A) / (N * ((σ + a) ^ 2 + A ^ 2)) := by
  have ha' := abs_lt.mp ha
  have hD1 : 0 < (σ - a) ^ 2 + A ^ 2 := by nlinarith [sq_nonneg A]
  have hD2 : 0 < (σ + a) ^ 2 + A ^ 2 := by nlinarith [sq_nonneg A]
  have hden1 : N * ((σ - a) ^ 2 + A ^ 2) ≠ 0 := (mul_pos hN hD1).ne'
  have hden2 : N * ((σ + a) ^ 2 + A ^ 2) ≠ 0 := (mul_pos hN hD2).ne'
  rw [div_add_div _ _ hden1 hden2]
  apply div_nonneg
  · have := pairNumerator_nonneg (A := A) hX hσ hcond
    have e : (X * (σ - a) + 2 * a * γ * A) * (N * ((σ + a) ^ 2 + A ^ 2))
        + N * ((σ - a) ^ 2 + A ^ 2) * (X * (σ + a) - 2 * a * γ * A)
        = N * ((X * (σ - a) + 2 * a * γ * A) * ((σ + a) ^ 2 + A ^ 2)
            + (X * (σ + a) - 2 * a * γ * A) * ((σ - a) ^ 2 + A ^ 2)) := by ring
    rw [e]
    exact mul_nonneg hN.le this
  · exact (mul_pos (mul_pos hN hD1) (mul_pos hN hD2)).le

/-! ## Real coordinates of a lag term -/

/-- The real part of a lag term is `Re Z / |Z|²` with `Z = ρ(1−ρ)(s − (ρ − ½))`. -/
theorem re_lagTerm_eq (q : XiZeroCopy) (s : ℂ) :
    (lagWeight q / (s - lagPole q)).re =
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)) * (s - ((q.1 : ℂ) - 1 / 2))).re /
        Complex.normSq ((q.1 : ℂ) * (1 - (q.1 : ℂ)) * (s - ((q.1 : ℂ) - 1 / 2))) := by
  unfold lagWeight lagPole
  rw [div_div, Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, add_zero]

theorem lagZ_re (ρ s : ℂ) :
    (ρ * (1 - ρ) * (s - (ρ - 1 / 2))).re =
      (ρ.re * (1 - ρ.re) + ρ.im ^ 2) * (s.re - (ρ.re - 1 / 2))
        + 2 * (ρ.re - 1 / 2) * ρ.im * (s.im - ρ.im) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

theorem lagZ_normSq (ρ s : ℂ) :
    Complex.normSq (ρ * (1 - ρ) * (s - (ρ - 1 / 2))) =
      ((ρ.re * (1 - ρ.re) + ρ.im ^ 2) ^ 2 + 4 * (ρ.re - 1 / 2) ^ 2 * ρ.im ^ 2)
        * ((s.re - (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) := by
  rw [Complex.normSq_mul, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-- **Partner pair positivity.** With `ρ = ½ + a + iγ` the copy's zero, `X = ρ.re(1−ρ.re) + γ²`,
`σ = Re s`: if `|a| < σ` and `4a⁴γ² ≤ X²(σ² − a²)`, the real parts of the lag terms of `q` and of its
partner add to a nonnegative number. -/
theorem re_lagTerm_add_partner_nonneg (q : XiZeroCopy) {s : ℂ}
    (ha : |(q.1 : ℂ).re - 1 / 2| < s.re)
    (hcond : 4 * ((q.1 : ℂ).re - 1 / 2) ^ 4 * (q.1 : ℂ).im ^ 2
        ≤ ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re) + (q.1 : ℂ).im ^ 2) ^ 2
            * (s.re ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2)) :
    0 ≤ (lagWeight q / (s - lagPole q)).re
        + (lagWeight (lagPartner q) / (s - lagPole (lagPartner q))).re := by
  have hu0 := xiZeroCopy_re_pos q
  have hu1 := xiZeroCopy_re_lt_one q
  rw [re_lagTerm_eq, re_lagTerm_eq, lagZ_re, lagZ_normSq, lagZ_re, lagZ_normSq,
    lagPartner_coe]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im, zero_sub, neg_neg]
  set u : ℝ := (q.1 : ℂ).re with hu
  set γ : ℝ := (q.1 : ℂ).im with hγ
  set σ : ℝ := s.re with hσ
  set t : ℝ := s.im with ht
  have hX : 0 < u * (1 - u) + γ ^ 2 := by
    have := mul_pos hu0 (by linarith : (0:ℝ) < 1 - u)
    positivity
  have hN : 0 < (u * (1 - u) + γ ^ 2) ^ 2 + 4 * (u - 1 / 2) ^ 2 * γ ^ 2 := by positivity
  have hσ0 : 0 ≤ σ := le_trans (abs_nonneg _) ha.le
  have key := pairRatio_nonneg (X := u * (1 - u) + γ ^ 2) (a := u - 1 / 2) (γ := γ) (σ := σ)
    (A := t - γ) (N := (u * (1 - u) + γ ^ 2) ^ 2 + 4 * (u - 1 / 2) ^ 2 * γ ^ 2) hX hN hσ0 ha hcond
  convert key using 1
  ring

/-! ## Summability of the terms -/

theorem summable_lagTerm_of_lt_re {s : ℂ} {c : ℝ} (hc : ∀ q : XiZeroCopy, (lagPole q).re ≤ c)
    (hs : c < s.re) : Summable (fun q : XiZeroCopy => lagWeight q / (s - lagPole q)) := by
  refine Summable.of_norm_bounded (g := fun q => ‖lagWeight q‖ * (1 / (s.re - c)))
    (summable_norm_lagWeight.mul_right _) fun q => ?_
  have hpos : 0 < s.re - c := by linarith
  have hnorm : s.re - c ≤ ‖s - lagPole q‖ := by
    have h1 := Complex.re_le_norm (s - lagPole q)
    rw [Complex.sub_re] at h1
    linarith [hc q]
  rw [norm_div, div_eq_mul_one_div]
  gcongr

/-! ## Assembly over partner pairs -/

theorem re_lagPoleSeries_nonneg_of_pairs {s : ℂ}
    (hsumm : Summable (fun q : XiZeroCopy => lagWeight q / (s - lagPole q)))
    (hpair : ∀ q : XiZeroCopy, 0 ≤ (lagWeight q / (s - lagPole q)).re
        + (lagWeight (lagPartner q) / (s - lagPole (lagPartner q))).re) :
    0 ≤ (lagPoleSeries s).re := by
  unfold lagPoleSeries
  rw [Complex.re_tsum hsumm]
  have hre : Summable (fun q : XiZeroCopy => (lagWeight q / (s - lagPole q)).re) := by
    have := (hsumm.hasSum.mapL Complex.reCLM).summable
    simpa only [Complex.reCLM_apply] using this
  have hre' : Summable (fun q : XiZeroCopy =>
      (lagWeight (lagPartner q) / (s - lagPole (lagPartner q))).re) :=
    (lagPartner.summable_iff (f := fun q => (lagWeight q / (s - lagPole q)).re)).mpr hre
  have e1 := Equiv.tsum_eq lagPartner (fun q : XiZeroCopy => (lagWeight q / (s - lagPole q)).re)
  have h2 : ∑' q : XiZeroCopy, ((lagWeight q / (s - lagPole q)).re
      + (lagWeight (lagPartner q) / (s - lagPole (lagPartner q))).re)
      = 2 * ∑' q : XiZeroCopy, (lagWeight q / (s - lagPole q)).re := by
    rw [hre.tsum_add hre']
    have e1' : ∑' q : XiZeroCopy, (lagWeight (lagPartner q) /
        (s - lagPole (lagPartner q))).re = ∑' q : XiZeroCopy, (lagWeight q / (s - lagPole q)).re :=
      e1
    rw [e1']; ring
  have h3 : 0 ≤ ∑' q : XiZeroCopy, ((lagWeight q / (s - lagPole q)).re
      + (lagWeight (lagPartner q) / (s - lagPole (lagPartner q))).re) := tsum_nonneg hpair
  linarith

/-! ## The unconditional positive-real half-plane -/

/-- **Unconditional positivity.**  `Re G(s) ≥ 0` whenever `Re s ≥ 13/25`. -/
theorem re_lagPoleSeries_nonneg {s : ℂ} (hs : 13 / 25 ≤ s.re) : 0 ≤ (lagPoleSeries s).re := by
  refine re_lagPoleSeries_nonneg_of_pairs
    (summable_lagTerm_of_lt_re (c := 1 / 2) (fun q => (lagPole_re_lt_half q).le) (by linarith))
    fun q => ?_
  have hu0 := xiZeroCopy_re_pos q
  have hu1 := xiZeroCopy_re_lt_one q
  have hγ := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  set u : ℝ := (q.1 : ℂ).re with hu
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  set σ : ℝ := s.re with hσ
  have ha : |u - 1 / 2| < σ := by
    rw [abs_lt]; constructor <;> linarith
  refine re_lagTerm_add_partner_nonneg q ha ?_
  have hA : (u - 1 / 2) ^ 2 < 1 / 4 := by nlinarith
  have hA4 : 4 * (u - 1 / 2) ^ 4 ≤ 1 / 4 := by nlinarith [sq_nonneg ((u - 1 / 2) ^ 2)]
  have hXg : γ ^ 2 ≤ u * (1 - u) + γ ^ 2 := by nlinarith
  have hX2 : γ ^ 2 * γ ^ 2 ≤ (u * (1 - u) + γ ^ 2) ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg γ) hXg 2
    nlinarith [this]
  have hsa : 51 / 2500 ≤ σ ^ 2 - (u - 1 / 2) ^ 2 := by nlinarith
  have h1 : γ ^ 2 * γ ^ 2 * (51 / 2500) ≤ (u * (1 - u) + γ ^ 2) ^ 2 * (σ ^ 2 - (u - 1 / 2) ^ 2) :=
    mul_le_mul hX2 hsa (by norm_num) (by positivity)
  have h2 : 4 * (u - 1 / 2) ^ 4 * γ ^ 2 ≤ γ ^ 2 * γ ^ 2 * (51 / 2500) := by
    have hg0 : 0 ≤ γ ^ 2 := sq_nonneg γ
    have h21 : 4 * (u - 1 / 2) ^ 4 * γ ^ 2 ≤ 1 / 4 * γ ^ 2 := mul_le_mul_of_nonneg_right hA4 hg0
    have h22 : (41 / 2) * γ ^ 2 * (51 / 2500) ≤ γ ^ 2 * γ ^ 2 * (51 / 2500) := by
      have := mul_le_mul_of_nonneg_right hγ.le hg0
      nlinarith [this]
    nlinarith [h21, h22]
  linarith

/-- Under RH every zero copy is on the line and `Re G(s) ≥ 0` on the whole half-plane `Re s > 0`. -/
theorem re_lagPoleSeries_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 0 < s.re) : 0 ≤ (lagPoleSeries s).re := by
  have hc : ∀ q : XiZeroCopy, (lagPole q).re ≤ 0 := by
    intro q
    unfold lagPole
    rw [Complex.sub_re, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
    norm_num
  refine re_lagPoleSeries_nonneg_of_pairs (summable_lagTerm_of_lt_re hc hs) fun q => ?_
  have hq := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  refine re_lagTerm_add_partner_nonneg q ?_ ?_
  · rw [hq]; simpa using hs
  · rw [hq]
    norm_num
    positivity

/-! ## The converse: a pole forces the real part below every bound -/

/-- Near a pole from the left the real part is unbounded below:
`Re G(p₀ − t) ≤ −Re w₀/t + C` for small `t > 0`, with `C` independent of `t`. -/
theorem re_lagPoleSeries_le_of_lt_pole (q₀ : XiZeroCopy) :
    ∃ ε > 0, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < ε →
      (lagPoleSeries (lagPole q₀ - t)).re ≤ -((lagWeight q₀).re / t) + C := by
  obtain ⟨ε, hε, hiso⟩ := xi_zero_isolated (xi_xiZeroCopy_eq_zero q₀)
  refine ⟨ε / 2, by positivity, (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖, fun t ht htε => ?_⟩
  set S : Set XiZeroCopy := {q | q.1 = q₀.1} with hS
  have hoff : ∀ q : XiZeroCopy, q ∉ S → ε / 2 ≤ ‖lagPole q₀ - t - lagPole q‖ := by
    intro q hq
    have hne : (q.1 : ℂ) ≠ (q₀.1 : ℂ) := fun h => hq (Subtype.ext h)
    have hdist : ε ≤ dist (q.1 : ℂ) (q₀.1 : ℂ) := by
      by_contra hlt
      exact hne (hiso _ (xi_xiZeroCopy_eq_zero q) (not_le.mp hlt))
    rw [Complex.dist_eq] at hdist
    have e : lagPole q₀ - t - lagPole q = -((q.1 : ℂ) - (q₀.1 : ℂ)) - t := by unfold lagPole; ring
    rw [e]
    have h2 := norm_sub_norm_le (-((q.1 : ℂ) - (q₀.1 : ℂ))) (t : ℂ)
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h2
    linarith
  have hsumm : Summable (fun q : XiZeroCopy => lagWeight q / (lagPole q₀ - t - lagPole q)) := by
    refine Summable.of_norm_bounded
      (g := fun q => ‖lagWeight q‖ * max (1 / t) (2 / ε)) (summable_norm_lagWeight.mul_right _)
      fun q => ?_
    rw [norm_div]
    by_cases hq : q ∈ S
    · have hq' : (q.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) hq
      have e : lagPole q₀ - t - lagPole q = -t := by unfold lagPole; rw [hq']; ring
      rw [e, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, div_eq_mul_one_div]
      gcongr
      exact le_max_left _ _
    · have := hoff q hq
      have hpos : 0 < ‖lagPole q₀ - t - lagPole q‖ := by linarith
      rw [div_le_iff₀ hpos]
      calc ‖lagWeight q‖ = ‖lagWeight q‖ * (2 / ε) * (ε / 2) := by field_simp
        _ ≤ ‖lagWeight q‖ * max (1 / t) (2 / ε) * ‖lagPole q₀ - t - lagPole q‖ := by
            gcongr
            exact le_max_right _ _
  unfold lagPoleSeries
  rw [← hsumm.tsum_subtype_add_tsum_subtype_compl S, Complex.add_re]
  have hfib : ∀ q : S, lagWeight q.1 / (lagPole q₀ - t - lagPole q.1) = -(lagWeight q₀ / t) := by
    intro q
    have hq' : (q.1.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) q.2
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    unfold lagWeight lagPole
    rw [hq']
    field_simp
    ring
  rw [tsum_congr hfib, tsum_const]
  have hfin : Finite S := by
    refine Finite.of_injective
      (fun x : S => (⟨(x.1.2 : ℕ), lt_of_lt_of_eq x.1.2.isLt (by
        rw [show x.1.1 = q₀.1 from x.2])⟩ :
          Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)))))
      fun x y hxy => ?_
    have hv : (x.1.2 : ℕ) = (y.1.2 : ℕ) := by
      have := congrArg Fin.val hxy
      simpa using this
    apply Subtype.ext
    apply Sigma.ext
    · exact x.2.trans y.2.symm
    · have hx : x.1.1 = q₀.1 := x.2
      have hy : y.1.1 = q₀.1 := y.2
      exact (Fin.heq_ext_iff (by rw [hx, hy])).mpr hv
  have hne : Nonempty S := ⟨⟨q₀, rfl⟩⟩
  have hcard : 1 ≤ Nat.card S := Nat.card_pos
  have hcompl : ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ - t - lagPole q.1)‖ ≤
      (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
    have hb : ∀ q : ↑Sᶜ, ‖lagWeight q.1 / (lagPole q₀ - t - lagPole q.1)‖ ≤
        (2 / ε) * ‖lagWeight q.1‖ := by
      intro q
      have := hoff q.1 q.2
      have hpos : 0 < ‖lagPole q₀ - t - lagPole q.1‖ := by linarith
      rw [norm_div, div_le_iff₀ hpos]
      calc ‖lagWeight q.1‖ = (2 / ε) * ‖lagWeight q.1‖ * (ε / 2) := by field_simp
        _ ≤ (2 / ε) * ‖lagWeight q.1‖ * ‖lagPole q₀ - t - lagPole q.1‖ := by gcongr
    have hs1 : Summable (fun q : ↑Sᶜ => ‖lagWeight q.1 / (lagPole q₀ - t - lagPole q.1)‖) :=
      (hsumm.norm.subtype _)
    have hs2 : Summable (fun q : ↑Sᶜ => (2 / ε) * ‖lagWeight q.1‖) :=
      (summable_norm_lagWeight.mul_left _).subtype _
    calc ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ - t - lagPole q.1)‖
        ≤ ∑' q : ↑Sᶜ, ‖lagWeight q.1 / (lagPole q₀ - t - lagPole q.1)‖ :=
          norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : ↑Sᶜ, (2 / ε) * ‖lagWeight q.1‖ := hs1.tsum_le_tsum hb hs2
      _ = (2 / ε) * ∑' q : ↑Sᶜ, ‖lagWeight q.1‖ := tsum_mul_left
      _ ≤ (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
          gcongr
          exact Summable.tsum_subtype_le (fun q : XiZeroCopy => ‖lagWeight q‖) Sᶜ
            (fun _ => norm_nonneg _) summable_norm_lagWeight
  have hre_compl : (∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ - t - lagPole q.1)).re ≤
      (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ :=
    le_trans (Complex.re_le_norm _) hcompl
  have hfibre : (Nat.card S • -(lagWeight q₀ / (t : ℂ))).re =
      -((Nat.card S : ℝ) * ((lagWeight q₀).re / t)) := by
    rw [nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.neg_re,
      Complex.neg_im, Complex.div_ofReal_re]
    ring
  have hw := lagWeight_re_pos q₀
  have hmain : -((Nat.card S : ℝ) * ((lagWeight q₀).re / t)) ≤ -((lagWeight q₀).re / t) := by
    have h1 : (1 : ℝ) ≤ Nat.card S := by exact_mod_cast hcard
    have h2 : 0 ≤ (lagWeight q₀).re / t := div_nonneg hw.le ht.le
    nlinarith
  rw [hfibre]
  linarith

/-- **Positive-real on a half-plane bounds the real parts.**  If `Re G(s) ≥ 0` for every `s` with
`Re s > σ₀`, every zero copy has real part at most `½ + σ₀`. -/
theorem re_le_half_add_of_lagPoleSeries_re_nonneg {σ₀ : ℝ}
    (h : ∀ s : ℂ, σ₀ < s.re → 0 ≤ (lagPoleSeries s).re) (q₀ : XiZeroCopy) :
    (q₀.1 : ℂ).re ≤ 1 / 2 + σ₀ := by
  by_contra hlt
  have hlt' : 1 / 2 + σ₀ < (q₀.1 : ℂ).re := not_le.mp hlt
  have hp : σ₀ < (lagPole q₀).re := by
    unfold lagPole
    rw [Complex.sub_re]
    norm_num
    linarith
  obtain ⟨ε, hε, C, hC⟩ := re_lagPoleSeries_le_of_lt_pole q₀
  have hw := lagWeight_re_pos q₀
  set δ : ℝ := (lagPole q₀).re - σ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hCpos : 0 < 2 * (|C| + 1) := by positivity
  set t : ℝ := min (ε / 2) (min (δ / 2) ((lagWeight q₀).re / (2 * (|C| + 1)))) with htdef
  have ht : 0 < t := lt_min (half_pos hε) (lt_min (half_pos hδ0) (div_pos hw hCpos))
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htδ : t ≤ δ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have htC : t ≤ (lagWeight q₀).re / (2 * (|C| + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hs : σ₀ < (lagPole q₀ - t).re := by
    rw [Complex.sub_re, Complex.ofReal_re]; linarith
  have h1 := h _ hs
  have h2 := hC t ht htε
  have h3 : 2 * (|C| + 1) ≤ (lagWeight q₀).re / t := by
    rw [le_div_iff₀ ht]
    calc 2 * (|C| + 1) * t ≤ 2 * (|C| + 1) * ((lagWeight q₀).re / (2 * (|C| + 1))) := by gcongr
      _ = (lagWeight q₀).re := by field_simp
  have h4 := le_abs_self C
  linarith

/-- **The positive-real criterion.**  `RH ⟺ Re G(s) ≥ 0 on Re s > 0`: the lag pole series is a
positive-real function exactly under RH. -/
theorem riemannHypothesis_iff_lagPoleSeries_re_nonneg :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → 0 ≤ (lagPoleSeries s).re := by
  constructor
  · intro hRH s hs
    exact re_lagPoleSeries_nonneg_of_riemannHypothesis hRH hs
  · intro h
    have hre : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := fun q => by
      have := re_le_half_add_of_lagPoleSeries_re_nonneg h q
      linarith
    refine riemannHypothesis_of_lagPoleSeries_extension (F := lagPoleSeries) ?_ fun _ _ => rfl
    intro z hz0 _
    refine differentiableAt_lagPoleSeries ?_
    intro hxi
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have := hre q
    rw [hq, Complex.add_re] at this
    norm_num at this
    linarith

/-! ## The prime side: the damped lag function is positive-definite -/

/-- For `Re s ≥ 13/25` the cosine transform of the damped lag function is nonnegative:
`∫_0^∞ Φ(u) e^{−σu} cos(tu) du ≥ 0`. -/
theorem integral_weilLagFunctionReal_damped_cos_nonneg {σ t : ℝ} (hσ : 13 / 25 ≤ σ) :
    0 ≤ ∫ u in Ioi (0:ℝ), weilLagFunctionReal u * (Real.exp (-σ * u) * Real.cos (t * u)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs12 : 1 / 2 < s.re := by rw [hsre]; linarith
  have hint := integrable_weilLag_mul_cexp hs12
  have hG := integral_weilLagFunction_mul_cexp hs12
  have hpos : 0 ≤ (lagPoleSeries s).re := re_lagPoleSeries_nonneg (by rw [hsre]; exact hσ)
  have hpt : ∀ u : ℝ, ((weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))).re
      = weilLagFunctionReal u * (Real.exp (-σ * u) * Real.cos (t * u)) := by
    intro u
    rw [Complex.re_ofReal_mul, Complex.exp_re]
    congr 2
    · simp [hs, Complex.mul_re]
    · rw [show (-s * (u : ℂ)).im = -(t * u) by simp [hs, Complex.mul_im]]
      rw [Real.cos_neg]
  have hre : (∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))).re
      = ∫ u in Ioi (0:ℝ), weilLagFunctionReal u * (Real.exp (-σ * u) * Real.cos (t * u)) := by
    have h := integral_re (𝕜 := ℂ) hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => hpt u)
  rw [← hre]
  have hΦ : ∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      lagPoleSeries s := by
    rw [← hG]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [weilLagFunction_eq_ofReal])
  rw [hΦ]
  exact hpos

end

end RHTower
