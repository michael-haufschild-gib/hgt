import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheBalanceLawOfTwoSidedEdits

/-!
# A fake zero on the top line costs logarithmic density

Let `G` continue `(s − 1) ζ_B(s)` of an edit to `Re s > 1/2`, and let `ρ` be a zero of `G` with
`ζ(ρ) ≠ 0` on the line `Re s = κ` right of which both the doubled and the deleted primes are
summable.  Write `P_T(σ) = Σ_{p ∈ T} p^{−σ}` (`primeSum`).

* **The edited primes** (`exists_order_mul_log_le_primeSum_add`).  If `ρ` is a zero of order
  `m`, then `P₊(σ) + P₋(σ) ≥ m log(1/(σ − κ)) − C` as `σ ↓ κ`.  Right of `κ`,
  `G = (s − 1) ζ(s) · exp(D₊ − D₋ + Q)`; at `s = ρ + (σ − κ)` the left side is `O((σ − κ)^m)`,
  and `Re(D₊ − D₋)(s) ≥ −(P₊(σ) + P₋(σ))`.
* **Half on each side** (`exists_order_half_log_le_primeSum`).  If moreover `G` does not vanish
  at the real point `κ`, then `P₊(σ) − P₋(σ)` stays bounded, so
  `P₊(σ), P₋(σ) ≥ (m/2) log(1/(σ − κ)) − C`.
* **The greedy edit** (`exists_half_log_le_primeSum_edit`).  At a non-real `ρ` with `ζ(ρ) ≠ 0`,
  `1/2 < Re ρ < 14/15`, the doubled and the deleted primes of the greedy edit each have
  `Σ p^{−σ} ≥ (1/2) log(1/(σ − Re ρ)) − C`.

The balance law says that the two exponents agree; this is its logarithmic scale: each side
carries at least half of the density of `m` copies of the primes at the scale `κ`, and both
series diverge at `κ`.  For a deletion whose count beats its thickness the bound is attained:
the deleted primes have density exactly the order of Landau's zero.
-/

open Complex Metric Filter Topology
open RHTower RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.RigidArithmeticOfCuts GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw

open PrimeEdits TwoSidedEdits

/-- `Σ_{p ∈ T} p^{−σ}`. -/
def primeSum (T : Set ℕ) (σ : ℝ) : ℝ := ∑' p, gdTwistTerm (wt T) freq σ 0 p

theorem norm_gdSeries_le {T : Set ℕ} {s : ℂ} (h : SummableAt T s.re) :
    ‖gdSeries (wt T) freq s‖ ≤ primeSum T s.re := by
  have hn : Summable fun p : ℕ => ‖(wt T p : ℂ) * cexp (-(s * (freq p : ℂ)))‖ :=
    (show Summable (gdTwistTerm (wt T) freq s.re 0) from h).congr fun p =>
      (norm_gd_term T s p).symm
  rw [gdSeries, primeSum]
  exact (norm_tsum_le_tsum_norm hn).trans (le_of_eq (tsum_congr fun p => norm_gd_term T s p))

theorem gdSeries_ofReal (T : Set ℕ) (σ : ℝ) :
    gdSeries (wt T) freq (σ : ℂ) = ((primeSum T σ : ℝ) : ℂ) := by
  rw [gdSeries, primeSum, Complex.ofReal_tsum]
  refine tsum_congr fun p => ?_
  rw [gdTwistTerm_wt]
  simp [Complex.ofReal_exp]

variable {e : ℕ → ℤ} {G : ℂ → ℂ}

/-- If `G` is `O(|s − ρ|^m)` at a point `ρ` of the top line with `ζ(ρ) ≠ 0`, the edited primes
have `Σ p^{−σ} ≥ m log(1/(σ − κ)) − C` as `σ ↓ κ = Re ρ`. -/
theorem exists_mul_log_le_primeSum_add_of_bound (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re ≤ 1)
    (hp : ∀ σ, ρ.re < σ → SummableAt (plusSet e) σ)
    (hm : ∀ σ, ρ.re < σ → SummableAt (minusSet e) σ)
    (hζ : riemannZeta ρ ≠ 0) (hne1 : ρ ≠ 1) {M : ℝ} (hMpos : 0 < M) {m : ℕ}
    (hM : ∀ᶠ s in 𝓝 ρ, ‖G s‖ ≤ M * ‖s - ρ‖ ^ m) :
    ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      m * Real.log (1 / (σ - ρ.re)) - C ≤
        primeSum (plusSet e) σ + primeSum (minusSet e) σ := by
  have hUo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hρmem : ρ ∈ {s : ℂ | 1 / 2 < s.re} := hρ
  -- the regular factor is bounded below near `ρ`
  have hfc : ContinuousAt (fun s => zetaResidueUnit s * cexp (editRem e s)) ρ :=
    differentiable_zetaResidueUnit.continuous.continuousAt.mul
      ((differentiableOn_editRem he).continuousOn.continuousAt (hUo.mem_nhds hρmem)).cexp
  have hf0 : 0 < ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖ := by
    refine norm_pos_iff.mpr (mul_ne_zero ?_ (Complex.exp_ne_zero _))
    rw [zetaResidueUnit_of_ne hne1]
    exact mul_ne_zero (sub_ne_zero.mpr hne1) hζ
  have hlow : ∀ᶠ s in 𝓝 ρ, ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖ / 2 <
      ‖zetaResidueUnit s * cexp (editRem e s)‖ :=
    Filter.Tendsto.eventually_const_lt (half_lt_self hf0) hfc.norm
  -- the horizontal path into `ρ`
  have hpath : Tendsto (fun σ : ℝ => ρ + ((σ - ρ.re : ℝ) : ℂ)) (𝓝[>] ρ.re) (𝓝 ρ) := by
    have hc : Continuous fun σ : ℝ => ρ + ((σ - ρ.re : ℝ) : ℂ) :=
      continuous_const.add (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const))
    have h0 := hc.tendsto ρ.re
    simp only [sub_self, Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine ⟨Real.log (2 * M / ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖), ?_⟩
  filter_upwards [hpath.eventually hM, hpath.eventually hlow, self_mem_nhdsWithin]
    with σ hGσ hfσ hσ
  have hσ' : ρ.re < σ := hσ
  have hsre : (ρ + ((σ - ρ.re : ℝ) : ℂ)).re = σ := by
    rw [Complex.add_re, Complex.ofReal_re]
    ring
  have hnorm : ‖ρ + ((σ - ρ.re : ℝ) : ℂ) - ρ‖ = σ - ρ.re := by
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hnorm] at hGσ
  -- the continuation right of `Re ρ`
  have hcont := continuation_eq he hG hGeq (differentiableOn_editRem he) hρ.le hρ1 hp hm
    (show ρ.re < (ρ + ((σ - ρ.re : ℝ) : ℂ)).re by rw [hsre]; exact hσ')
  have hsplit : cexp (gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
      gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) +
      editRem e (ρ + ((σ - ρ.re : ℝ) : ℂ))) =
      cexp (editRem e (ρ + ((σ - ρ.re : ℝ) : ℂ))) *
        cexp (gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
          gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hGnorm : ‖G (ρ + ((σ - ρ.re : ℝ) : ℂ))‖ =
      ‖zetaResidueUnit (ρ + ((σ - ρ.re : ℝ) : ℂ)) *
        cexp (editRem e (ρ + ((σ - ρ.re : ℝ) : ℂ)))‖ *
      Real.exp ((gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
        gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ))).re) := by
    rw [hcont, hsplit, ← mul_assoc, norm_mul, Complex.norm_exp]
  -- the real part of `D₊ − D₋` is at least minus the sum of the two prime sums
  have hre : -(primeSum (plusSet e) σ + primeSum (minusSet e) σ) ≤
      (gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
        gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ))).re := by
    have h1 := norm_gdSeries_le (T := plusSet e) (s := ρ + ((σ - ρ.re : ℝ) : ℂ))
      (by rw [hsre]; exact hp σ hσ')
    have h2 := norm_gdSeries_le (T := minusSet e) (s := ρ + ((σ - ρ.re : ℝ) : ℂ))
      (by rw [hsre]; exact hm σ hσ')
    rw [hsre] at h1 h2
    have h3 := Complex.abs_re_le_norm (gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
      gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)))
    have h4 := norm_sub_le (gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)))
      (gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)))
    have h5 := neg_abs_le ((gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
      gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ))).re)
    linarith
  have hexp : Real.exp (-(primeSum (plusSet e) σ + primeSum (minusSet e) σ)) ≤
      Real.exp ((gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
        gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ))).re) :=
    Real.exp_le_exp.mpr hre
  -- compare the two sizes of `G`
  have hc0 : 0 < ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖ / 2 := by linarith
  have hchain : ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖ / 2 *
      Real.exp (-(primeSum (plusSet e) σ + primeSum (minusSet e) σ)) ≤ M * (σ - ρ.re) ^ m := by
    calc ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖ / 2 *
          Real.exp (-(primeSum (plusSet e) σ + primeSum (minusSet e) σ))
        ≤ ‖zetaResidueUnit (ρ + ((σ - ρ.re : ℝ) : ℂ)) *
            cexp (editRem e (ρ + ((σ - ρ.re : ℝ) : ℂ)))‖ *
          Real.exp ((gdSeries (wt (plusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ)) -
            gdSeries (wt (minusSet e)) freq (ρ + ((σ - ρ.re : ℝ) : ℂ))).re) :=
          mul_le_mul hfσ.le hexp (Real.exp_pos _).le (norm_nonneg _)
      _ = ‖G (ρ + ((σ - ρ.re : ℝ) : ℂ))‖ := hGnorm.symm
      _ ≤ M * (σ - ρ.re) ^ m := hGσ
  have hd : 0 < σ - ρ.re := by linarith
  have hdm : 0 < (σ - ρ.re) ^ m := pow_pos hd m
  have hbound : Real.exp (-(primeSum (plusSet e) σ + primeSum (minusSet e) σ)) ≤
      2 * M / ‖zetaResidueUnit ρ * cexp (editRem e ρ)‖ * (σ - ρ.re) ^ m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hf0]
    linarith
  have hlog := (Real.le_log_iff_exp_le (mul_pos (div_pos (by linarith) hf0) hdm)).mpr hbound
  rw [Real.log_mul (div_pos (by linarith) hf0).ne' hdm.ne', Real.log_pow] at hlog
  rw [one_div, Real.log_inv]
  linarith

/-- **A fake zero on the top line costs logarithmic density**: the edited primes have
`Σ p^{−σ} ≥ log(1/(σ − κ)) − C` as `σ ↓ κ = Re ρ`. -/
theorem exists_log_le_primeSum_add (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re ≤ 1)
    (hp : ∀ σ, ρ.re < σ → SummableAt (plusSet e) σ)
    (hm : ∀ σ, ρ.re < σ → SummableAt (minusSet e) σ)
    (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) (hne1 : ρ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (plusSet e) σ + primeSum (minusSet e) σ := by
  have hUo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hρmem : ρ ∈ {s : ℂ | 1 / 2 < s.re} := hρ
  -- `G` vanishes to first order at `ρ`
  obtain ⟨M, hMpos, hMw⟩ :=
    (hG.differentiableAt (hUo.mem_nhds hρmem)).hasFDerivAt.isBigO_sub.exists_pos
  have hM : ∀ᶠ s in 𝓝 ρ, ‖G s‖ ≤ M * ‖s - ρ‖ ^ 1 := hMw.bound.mono fun s hs => by
    rw [pow_one]
    rwa [hzero, sub_zero] at hs
  obtain ⟨C, hC⟩ := exists_mul_log_le_primeSum_add_of_bound he hG hGeq hρ hρ1 hp hm hζ hne1
    hMpos hM
  exact ⟨C, hC.mono fun σ h => by rwa [Nat.cast_one, one_mul] at h⟩

/-- **A zero of order `m` on the top line costs logarithmic density `m`.** -/
theorem exists_order_mul_log_le_primeSum_add (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re ≤ 1)
    (hp : ∀ σ, ρ.re < σ → SummableAt (plusSet e) σ)
    (hm : ∀ σ, ρ.re < σ → SummableAt (minusSet e) σ)
    (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) (hne1 : ρ ≠ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ analyticOrderAt G ρ = m ∧ ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      m * Real.log (1 / (σ - ρ.re)) - C ≤
        primeSum (plusSet e) σ + primeSum (minusSet e) σ := by
  have hUo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hρmem : ρ ∈ {s : ℂ | 1 / 2 < s.re} := hρ
  have hGan : AnalyticAt ℂ G ρ := hG.analyticAt (hUo.mem_nhds hρmem)
  -- `G` is not identically zero: at `s = 2` it is `ζ(2)` times an exponential
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, G z = 0 := by
    intro hev
    have hglob := (hG.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt (1 / 2)).isPreconnected hρmem hev
    have h2re : (2 : ℂ).re = 2 := by norm_num
    have h2 : G 2 = 0 := hglob (show (1 : ℝ) / 2 < (2 : ℂ).re by rw [h2re]; norm_num)
    rw [continuation_eq he hG hGeq (differentiableOn_editRem he) hρ.le hρ1 hp hm
      (show ρ.re < (2 : ℂ).re by rw [h2re]; linarith)] at h2
    have hu2 : zetaResidueUnit 2 ≠ 0 := by
      rw [zetaResidueUnit_of_ne (by norm_num)]
      exact mul_ne_zero (by norm_num)
        (riemannZeta_ne_zero_of_one_lt_re (by rw [h2re]; norm_num))
    exact mul_ne_zero hu2 (Complex.exp_ne_zero _) h2
  obtain ⟨m, g, hgan, hg0, hgeq⟩ := hGan.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hself := hgeq.self_of_nhds
    rw [hm0', pow_zero, one_smul, hzero] at hself
    exact hg0 hself.symm
  have hord : analyticOrderAt G ρ = m :=
    hGan.analyticOrderAt_eq_natCast.mpr ⟨g, hgan, hg0, hgeq⟩
  -- `|G(s)| ≤ (|g(ρ)| + 1) |s − ρ|^m` near `ρ`
  have hgb : ∀ᶠ s in 𝓝 ρ, ‖g s‖ < ‖g ρ‖ + 1 :=
    Filter.Tendsto.eventually_lt_const (lt_add_one _) hgan.continuousAt.norm
  have hM : ∀ᶠ s in 𝓝 ρ, ‖G s‖ ≤ (‖g ρ‖ + 1) * ‖s - ρ‖ ^ m := by
    filter_upwards [hgeq, hgb] with s hs hgs
    calc ‖G s‖ = ‖s - ρ‖ ^ m * ‖g s‖ := by rw [hs, norm_smul, norm_pow]
      _ ≤ ‖s - ρ‖ ^ m * (‖g ρ‖ + 1) :=
          mul_le_mul_of_nonneg_left hgs.le (pow_nonneg (norm_nonneg _) _)
      _ = (‖g ρ‖ + 1) * ‖s - ρ‖ ^ m := mul_comm _ _
  obtain ⟨C, hC⟩ := exists_mul_log_le_primeSum_add_of_bound he hG hGeq hρ hρ1 hp hm hζ hne1
    (M := ‖g ρ‖ + 1) (by positivity) hM
  exact ⟨m, hm1, hord, C, hC⟩

/-- If the edited primes have `Σ p^{−σ} ≥ c log(1/(σ − κ)) − C₁` and the continuation does not
vanish at the real point `κ`, each side has at least half of it. -/
theorem exists_half_of_sum (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re ≤ 1)
    (hp : ∀ σ, ρ.re < σ → SummableAt (plusSet e) σ)
    (hm : ∀ σ, ρ.re < σ → SummableAt (minusSet e) σ)
    (hreal : G ((ρ.re : ℝ) : ℂ) ≠ 0) {c C₁ : ℝ}
    (hsum : ∀ᶠ σ in 𝓝[>] ρ.re, c * Real.log (1 / (σ - ρ.re)) - C₁ ≤
      primeSum (plusSet e) σ + primeSum (minusSet e) σ) :
    ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      c / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (plusSet e) σ ∧
        c / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (minusSet e) σ := by
  have hUo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hκmem : ((ρ.re : ℝ) : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show 1 / 2 < ((ρ.re : ℝ) : ℂ).re
    rw [Complex.ofReal_re]; exact hρ
  -- `G` and the regular factor are bounded above and below near the real point
  have hGc : ContinuousAt G ((ρ.re : ℝ) : ℂ) :=
    hG.continuousOn.continuousAt (hUo.mem_nhds hκmem)
  have hfc : ContinuousAt (fun s => zetaResidueUnit s * cexp (editRem e s)) ((ρ.re : ℝ) : ℂ) :=
    differentiable_zetaResidueUnit.continuous.continuousAt.mul
      ((differentiableOn_editRem he).continuousOn.continuousAt (hUo.mem_nhds hκmem)).cexp
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ‖G ((ρ.re : ℝ) : ℂ)‖ := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = ‖zetaResidueUnit ((ρ.re : ℝ) : ℂ) *
      cexp (editRem e ((ρ.re : ℝ) : ℂ))‖ := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact norm_pos_iff.mpr hreal
  have hφ0 : 0 < φ := by
    rw [hφ]
    exact norm_pos_iff.mpr (mul_ne_zero (zetaResidueUnit_ofReal_ne_zero hρ)
      (Complex.exp_ne_zero _))
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] ρ.re) (𝓝 ((ρ.re : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto ρ.re).mono_left nhdsWithin_le_nhds
  have hgg1 : g / 2 < ‖G ((ρ.re : ℝ) : ℂ)‖ := by rw [← hg]; linarith
  have hgg2 : ‖G ((ρ.re : ℝ) : ℂ)‖ < 2 * g := by rw [← hg]; linarith
  have hφφ1 : φ / 2 < ‖zetaResidueUnit ((ρ.re : ℝ) : ℂ) * cexp (editRem e ((ρ.re : ℝ) : ℂ))‖ := by
    rw [← hφ]; linarith
  have hφφ2 : ‖zetaResidueUnit ((ρ.re : ℝ) : ℂ) * cexp (editRem e ((ρ.re : ℝ) : ℂ))‖ < 2 * φ := by
    rw [← hφ]; linarith
  have hG1 : ∀ᶠ s in 𝓝 ((ρ.re : ℝ) : ℂ), g / 2 < ‖G s‖ :=
    Filter.Tendsto.eventually_const_lt hgg1 hGc.norm
  have hG2 : ∀ᶠ s in 𝓝 ((ρ.re : ℝ) : ℂ), ‖G s‖ < 2 * g :=
    Filter.Tendsto.eventually_lt_const hgg2 hGc.norm
  have hf1 : ∀ᶠ s in 𝓝 ((ρ.re : ℝ) : ℂ), φ / 2 < ‖zetaResidueUnit s * cexp (editRem e s)‖ :=
    Filter.Tendsto.eventually_const_lt hφφ1 hfc.norm
  have hf2 : ∀ᶠ s in 𝓝 ((ρ.re : ℝ) : ℂ), ‖zetaResidueUnit s * cexp (editRem e s)‖ < 2 * φ :=
    Filter.Tendsto.eventually_lt_const hφφ2 hfc.norm
  refine ⟨(|C₁| + |Real.log (4 * g / φ)| + |Real.log (g / (4 * φ))|) / 2, ?_⟩
  filter_upwards [hsum, hpath.eventually hG1, hpath.eventually hG2, hpath.eventually hf1,
    hpath.eventually hf2, self_mem_nhdsWithin] with σ hS hGlo hGhi hflo hfhi hσ
  have hσ' : ρ.re < σ := hσ
  -- on the real axis `|G| = |regular factor| · exp(P₊ − P₋)`
  have hcont := continuation_eq he hG hGeq (differentiableOn_editRem he) hρ.le hρ1 hp hm
    (show ρ.re < ((σ : ℝ) : ℂ).re by rw [Complex.ofReal_re]; exact hσ')
  rw [gdSeries_ofReal, gdSeries_ofReal] at hcont
  have hsplit : cexp (((primeSum (plusSet e) σ : ℝ) : ℂ) - ((primeSum (minusSet e) σ : ℝ) : ℂ) +
      editRem e (σ : ℂ)) = cexp (editRem e (σ : ℂ)) *
        cexp (((primeSum (plusSet e) σ - primeSum (minusSet e) σ : ℝ)) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hGnorm : ‖G (σ : ℂ)‖ = ‖zetaResidueUnit (σ : ℂ) * cexp (editRem e (σ : ℂ))‖ *
      Real.exp (primeSum (plusSet e) σ - primeSum (minusSet e) σ) := by
    rw [hcont, hsplit, ← mul_assoc, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  have hE := Real.exp_pos (primeSum (plusSet e) σ - primeSum (minusSet e) σ)
  -- `exp(P₊ − P₋)` lies between `g/(4φ)` and `4g/φ`
  have hup : Real.exp (primeSum (plusSet e) σ - primeSum (minusSet e) σ) < 4 * g / φ := by
    rw [lt_div_iff₀ hφ0]
    have h1 := mul_lt_mul_of_pos_right hflo hE
    linarith
  have hdn : g / (4 * φ) < Real.exp (primeSum (plusSet e) σ - primeSum (minusSet e) σ) := by
    rw [div_lt_iff₀ (by linarith)]
    have h1 := mul_lt_mul_of_pos_right hfhi hE
    linarith
  have h4 : primeSum (plusSet e) σ - primeSum (minusSet e) σ < Real.log (4 * g / φ) :=
    (Real.lt_log_iff_exp_lt (div_pos (by linarith) hφ0)).mpr hup
  have h5 : Real.log (g / (4 * φ)) < primeSum (plusSet e) σ - primeSum (minusSet e) σ :=
    (Real.log_lt_iff_lt_exp (div_pos hg0 (by linarith))).mpr hdn
  have ha1 := le_abs_self C₁
  have ha2 := le_abs_self (Real.log (4 * g / φ))
  have ha3 := neg_abs_le (Real.log (g / (4 * φ)))
  have ha4 := abs_nonneg (Real.log (4 * g / φ))
  have ha5 := abs_nonneg (Real.log (g / (4 * φ)))
  have ha6 := abs_nonneg C₁
  constructor <;> linarith

/-- **Half of the density on each side.**  If moreover the continuation does not vanish at the
real point `Re ρ`, the doubled and the deleted primes each have
`Σ p^{−σ} ≥ (1/2) log(1/(σ − κ)) − C` as `σ ↓ κ = Re ρ`. -/
theorem exists_half_log_le_primeSum (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re ≤ 1)
    (hp : ∀ σ, ρ.re < σ → SummableAt (plusSet e) σ)
    (hm : ∀ σ, ρ.re < σ → SummableAt (minusSet e) σ)
    (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) (hne1 : ρ ≠ 1)
    (hreal : G ((ρ.re : ℝ) : ℂ) ≠ 0) :
    ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      1 / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (plusSet e) σ ∧
        1 / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (minusSet e) σ := by
  obtain ⟨C₁, hsum⟩ := exists_log_le_primeSum_add he hG hGeq hρ hρ1 hp hm hzero hζ hne1
  exact exists_half_of_sum he hG hGeq hρ hρ1 hp hm hreal (c := 1) (C₁ := C₁)
    (hsum.mono fun σ h => by rwa [one_mul])

/-- **A zero of order `m` on the top line without a real zero costs each side the density
`m/2`.** -/
theorem exists_order_half_log_le_primeSum (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re ≤ 1)
    (hp : ∀ σ, ρ.re < σ → SummableAt (plusSet e) σ)
    (hm : ∀ σ, ρ.re < σ → SummableAt (minusSet e) σ)
    (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) (hne1 : ρ ≠ 1)
    (hreal : G ((ρ.re : ℝ) : ℂ) ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ analyticOrderAt G ρ = m ∧ ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      (m : ℝ) / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (plusSet e) σ ∧
        (m : ℝ) / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (minusSet e) σ := by
  obtain ⟨m, hm1, hord, C₁, hsum⟩ :=
    exists_order_mul_log_le_primeSum_add he hG hGeq hρ hρ1 hp hm hzero hζ hne1
  obtain ⟨C, hC⟩ := exists_half_of_sum he hG hGeq hρ hρ1 hp hm hreal (c := (m : ℝ))
    (C₁ := C₁) hsum
  exact ⟨m, hm1, hord, C, hC⟩

/-- **The greedy edit carries half of the density on each side.**  At a non-real `ρ` with
`1/2 < Re ρ < 14/15` and `ζ(ρ) ≠ 0`, the doubled and the deleted primes of the greedy edit each
have `Σ p^{−σ} ≥ (1/2) log(1/(σ − Re ρ)) − C` as `σ ↓ Re ρ`. -/
theorem exists_half_log_le_primeSum_edit {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15)
    (him : ρ.im ≠ 0) (hζ : riemannZeta ρ ≠ 0) :
    ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] ρ.re,
      1 / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (plusSet (edit ρ)) σ ∧
        1 / 2 * Real.log (1 / (σ - ρ.re)) - C ≤ primeSum (minusSet (edit ρ)) σ := by
  have he := isEdit_edit ρ
  obtain ⟨C, H, hC, hdiff, hfac⟩ := (isPairTwin_editSystem hρ hρ1).exists_continuation
  have hρne : ρ ≠ 1 := fun h => by rw [h] at hρ1; norm_num at hρ1
  have hsum : ∀ σ, ρ.re < σ →
      SummableAt (plusSet (edit ρ)) σ ∧ SummableAt (minusSet (edit ρ)) σ := fun σ hσ =>
    summableAt_of_edit he (summable_abs_edit_rpow (by linarith) (by linarith) hσ)
  have h1 : ((ρ.re : ℝ) : ℂ) - ρ ≠ 0 := fun h0 => him (by
    have h' := congrArg Complex.im h0
    simpa using h')
  have h2 : ((ρ.re : ℝ) : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := fun h0 => him (by
    have h' := congrArg Complex.im h0
    simpa using h')
  exact exists_half_log_le_primeSum he hdiff (fun s hs => (hfac s hs).symm) hρ (by linarith)
    (fun σ hσ => (hsum σ hσ).1) (fun σ hσ => (hsum σ hσ).2) (by simp) hζ hρne
    (mul_ne_zero (zetaResidueUnit_ofReal_ne_zero hρ)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hC h1) h2) (Complex.exp_ne_zero _)))

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw
