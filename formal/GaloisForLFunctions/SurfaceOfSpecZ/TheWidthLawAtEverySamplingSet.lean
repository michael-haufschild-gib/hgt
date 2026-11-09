import GaloisForLFunctions.SurfaceOfSpecZ.StepanovBoundsProduceTheAbscissaLaw

/-!
# The width law at every sampling set

At a degree set with power-saving gaps the growth exponent of a one-sided bound is the zero width
(`TheWidthLawAtEveryGapSet`). At a sampling set the same holds for attained tops, and hence modulo
the approach of the zeros to the line.

* `re_mem_of_bddBelow_rpow_of_samplingWeight`: if a sampling weight bounds the spline traces below
  by `−K n^s` and `ρ₀` is a zero of maximal real part with `Re ρ₀ > ½ + s`, the top layer contains
  the real zero `Re ρ₀`. The normalized trace `F = 2 Re S(log n) n^{−b}`, `b = Re ρ₀ − ½`, satisfies
  `F ≥ −|K| n^{−(b−s)}`, and `Σ w(n) n^{−σ−(b−s)} = o(Σ w(n) n^{−σ})` because `b > s`.
* For `ζ`, which has no real zeros in the strip, a bound `−K p^s` at the primes `p ≡ a (mod q)`, at
  the primes off a set of relative density zero, or `−K e^{sλ}` at the degrees `λ = a log p + b log q`
  of two primes, leaves no deepest zero right of `½ + s`. So finitely many zeros right of `½ + h`,
  `h ≥ s`, means none (`re_le_of_finite_of_noDeeper`).
* **The width law modulo the approach to the line**
  (`zetaZeroWidth_le_iff_bddBelow_rpow_primes_mod_of_zerosApproachLine`, and the same at the primes
  off a null set and at the `pᵃqᵇ`): if `ZerosApproachLine`, then `zetaZeroWidth ≤ s` iff the traces
  are `≥ −K p^s` at the sampled degrees.
* **The tensor power trick at a residue class** (`asymptoticAbscissaLaw_of_moments_primes_mod`,
  `riemannHypothesis_iff_zerosApproachLine_and_moments_primes_mod`): moments
  `Σ_{p ≤ N, p ≡ a} log p · (2 Re S(log p))^{2k} ≤ C_k N^{1+A}`, uniform in `k`, give the asymptotic
  abscissa law, and RH together with `ZerosApproachLine`. One term gives the width `(1 + A)/(2k)`
  at the class, and `k → ∞` leaves no deepest off-line zero.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-! ### A lower bound of growth `n^s` at a sampling set -/

section Means

variable {w : ℕ → ℝ} (hw : SamplingWeight w) {Z : ZeroConfig} {b : ℝ}
include hw

/-- **At the sampled degrees, `F² ≤ E(F + 2|K| n^{−(b−s)})`.** -/
theorem wSqMean_le_rpow (hZ : TemperedConfig Z) (h : TopDepth Z b) {K s : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 →
      -(K * ((j : ℝ) + 1) ^ s) ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re)
    {σ : ℝ} (hσ : 1 < σ) (hsb : s ≤ b) :
    wSqMean w Z b σ ≤ (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * wMean w Z b σ +
      2 * (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * |K| * wSum w (σ + (b - s)) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  have hεsum := hw.summable (show 1 < σ + (b - s) by linarith)
  have hS₁sum := summable_wMean hw hZ h hσ
  have hrhs : Summable fun j : ℕ =>
      E * (w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) +
        2 * E * |K| * (w j * ((j : ℝ) + 1) ^ (-(σ + (b - s)))) :=
    (hS₁sum.mul_left E).add (hεsum.mul_left _)
  calc wSqMean w Z b σ
      ≤ ∑' j : ℕ, (E * (w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) +
          2 * E * |K| * (w j * ((j : ℝ) + 1) ^ (-(σ + (b - s))))) := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_wSqMean hw hZ h hσ) hrhs
        have hw0 := hw.nonneg j
        have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
        have hsplit : ((j : ℝ) + 1) ^ (-(σ + (b - s))) =
            ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-(b - s)) := by
          rw [← Real.rpow_add hj0]; ring_nf
        rw [hsplit]
        by_cases hw00 : w j = 0
        · rw [hw00]; simp
        have h1 := hK j hw00
        have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
          rw [Real.rpow_def_of_pos hj0]; ring_nf
        have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
        have hpc : 0 < ((j : ℝ) + 1) ^ (-(b - s)) := by positivity
        have hsc : ((j : ℝ) + 1) ^ s * ((j : ℝ) + 1) ^ (-b) = ((j : ℝ) + 1) ^ (-(b - s)) := by
          rw [← Real.rpow_add hj0]; ring_nf
        have hlow : -(|K| * ((j : ℝ) + 1) ^ (-(b - s))) ≤
            normTrace Z b (Real.log ((j : ℝ) + 1)) := by
          rw [normTrace, hexp]
          have h3 := mul_le_mul_of_nonneg_right h1 hpb.le
          have h4 : K * ((j : ℝ) + 1) ^ (-(b - s)) ≤ |K| * ((j : ℝ) + 1) ^ (-(b - s)) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) hpc.le
          have h5 : -(K * ((j : ℝ) + 1) ^ s) * ((j : ℝ) + 1) ^ (-b) =
              -(K * ((j : ℝ) + 1) ^ (-(b - s))) := by
            rw [← hsc]; ring
          linarith
        have hFb := abs_normTrace_le hZ h (log_add_one_nonneg j)
        set f := normTrace Z b (Real.log ((j : ℝ) + 1))
        have hKc : 0 ≤ |K| * ((j : ℝ) + 1) ^ (-(b - s)) := mul_nonneg (abs_nonneg K) hpc.le
        have habs : |f| ≤ f + 2 * (|K| * ((j : ℝ) + 1) ^ (-(b - s))) := by
          rcases le_total 0 f with h0 | h0
          · rw [abs_of_nonneg h0]; linarith
          · rw [abs_of_nonpos h0]; linarith
        have hsq : f ^ 2 ≤ E * (f + 2 * (|K| * ((j : ℝ) + 1) ^ (-(b - s)))) := by
          calc f ^ 2 = |f| * |f| := by rw [← sq_abs, sq]
            _ ≤ E * |f| := mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left habs hE0
        have hwp : 0 ≤ w j * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hw0 hp.le
        have h5 := mul_le_mul_of_nonneg_right hsq hwp
        calc w j * f ^ 2 * ((j : ℝ) + 1) ^ (-σ) = f ^ 2 * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
          _ ≤ E * (f + 2 * (|K| * ((j : ℝ) + 1) ^ (-(b - s)))) *
              (w j * ((j : ℝ) + 1) ^ (-σ)) := h5
          _ = _ := by ring
    _ = E * wMean w Z b σ + 2 * E * |K| * wSum w (σ + (b - s)) := by
        rw [(hS₁sum.mul_left E).tsum_add (hεsum.mul_left _), tsum_mul_left, tsum_mul_left]
        rfl

end Means

/-- **A lower bound `−K n^s` sees every attained top deeper than `s`.** If a sampling weight bounds
the spline traces below by `−K n^s` and `ρ₀` is a zero of maximal real part with `Re ρ₀ > ½ + s`,
then `Re ρ₀` is itself a zero. -/
theorem re_mem_of_bddBelow_rpow_of_samplingWeight {w : ℕ → ℝ} (hw : SamplingWeight w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hoff : 1 / 2 < ρ₀.re) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K s : ℝ}
    (hs : s < ρ₀.re - 1 / 2)
    (hK : ∀ j : ℕ, w j ≠ 0 →
      -(K * ((j : ℝ) + 1) ^ s) ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) :
    (ρ₀.re : ℂ) ∈ Z.carrier := by
  by_contra hnot
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hc0 : 0 < b - s := by linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
  have hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0 := by
    intro z hz hzre hzim
    have hzb : z = (b : ℂ) := Complex.ext (by simpa using hzre) (by simpa using hzim)
    have hpt : (1 / 2 : ℂ) + (b : ℂ) = (ρ₀.re : ℂ) := by rw [hbdef]; push_cast; ring
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · rw [hzb, hpt] at h; exact hnot h
    · rw [hzb, Complex.conj_ofReal, hpt] at h; exact hnot h
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hpos := re_tsum_diagWeight_pos hZ htop hz₀ (by simp [hbdef])
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hlimε : Tendsto (fun σ => wSum w (σ + (b - s)) / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := wSum w (1 + (b - s)))).div_atTop hw.tendsto_atTop) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_nonneg (hw.wSum_nonneg _) (hw.wSum_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      exact div_le_div_of_nonneg_right (hw.antitone (by linarith) (by linarith))
        (hw.wSum_nonneg _)
  have hrhs : Tendsto (fun σ => E * (wMean w Z b σ / wSum w σ) +
      2 * E * |K| * (wSum w (σ + (b - s)) / wSum w σ)) (𝓝[>] 1) (𝓝 0) := by
    simpa using ((tendsto_wMean hw hZ htop hreal).const_mul E).add (hlimε.const_mul (2 * E * |K|))
  have hle : (∑' q, diagWeight Z b q).re ≤ 0 := by
    refine le_of_tendsto_of_tendsto (tendsto_wSqMean hw hZ htop) hrhs ?_
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
    have hσ1 : 1 < σ := hσ
    have h := wSqMean_le_rpow hw hZ htop hK hσ1 (by linarith)
    rw [div_le_iff₀ hV]
    have : (E * (wMean w Z b σ / wSum w σ) + 2 * E * |K| * (wSum w (σ + (b - s)) / wSum w σ)) *
        wSum w σ = E * wMean w Z b σ + 2 * E * |K| * wSum w (σ + (b - s)) := by field_simp
    rw [this]; exact h
  linarith

/-! ### `ζ`: no deepest zero right of `½ + s` -/

/-- **No deeper zero right of `½ + s` gives the abscissa law above `s`.** -/
theorem re_le_of_finite_of_noDeeper {s : ℝ}
    (hno : ∀ ρ₀ ∈ zetaZeroConfig.carrier, 1 / 2 + s < ρ₀.re →
      ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re)
    {h : ℝ} (hsh : s ≤ h)
    (hF : {q : _root_.RHTower.XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite) :
    ∀ q : _root_.RHTower.XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h := by
  intro q₀
  by_contra hlt
  push Not at hlt
  obtain ⟨q₁, hq₁F, hmax⟩ := Set.exists_max_image _
    (fun q : _root_.RHTower.XiZeroCopy => (q.1 : ℂ).re) hF ⟨q₀, hlt⟩
  have hq₁ : 1 / 2 + h < (q₁.1 : ℂ).re := hq₁F
  obtain ⟨ρ, hρ, hgt⟩ := hno _
    (_root_.RHTower.CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q₁)
    (by linarith)
  have hxi :=
    (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
      hρ).1
  obtain ⟨q, hq⟩ := _root_.RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
  have hqF : q ∈ {q : _root_.RHTower.XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} := by
    show 1 / 2 + h < (q.1 : ℂ).re
    rw [hq]; linarith
  have hle : (q.1 : ℂ).re ≤ (q₁.1 : ℂ).re := hmax q hqF
  rw [hq] at hle
  linarith

/-- **Modulo the approach to the line, no deeper zero right of `½ + s` is the width `≤ s`.** -/
theorem zetaZeroWidth_le_of_zerosApproachLine_of_noDeeper
    (hZ : _root_.RHTower.BacklundConverse.ZerosApproachLine) {s : ℝ} (hs0 : 0 ≤ s)
    (hno : ∀ ρ₀ ∈ zetaZeroConfig.carrier, 1 / 2 + s < ρ₀.re →
      ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re) :
    zetaZeroWidth ≤ s := by
  rw [zetaZeroWidth_le_iff_re_le hs0]
  intro ρ hρ
  by_contra hlt
  push Not at hlt
  set h : ℝ := (ρ.re - 1 / 2 + s) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hxi :=
    (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
      hρ).1
  obtain ⟨q, hq⟩ := _root_.RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
  have hle := re_le_of_finite_of_noDeeper hno (by rw [hh]; linarith)
    (_root_.RHTower.finite_re_gt_of_zerosApproachLine hZ hh0) q
  rw [hq, hh] at hle
  linarith

/-- **From below at the primes `p ≡ a (mod q)`, with growth `p^s`.** -/
theorem exists_re_gt_of_bddBelow_rpow_primes_mod {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {K s : ℝ}
    (hK : ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      -(K * (p : ℝ) ^ s) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hs0 : 0 ≤ s) (hρs : 1 / 2 + s < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hmem := re_mem_of_bddBelow_rpow_of_samplingWeight (samplingWeight_primeResidue ha)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ (by linarith) hno (K := K) (s := s)
    (by linarith) fun j hj => by
      obtain ⟨hp, hmod⟩ := prime_and_mod_of_primeResidueWeight_ne_zero hj
      have := hK (j + 1) hp hmod
      push_cast at this
      exact this
  exact zetaZeroConfig_im_ne_zero' _ hmem (Complex.ofReal_im _)

/-- **From below at the primes off a set of relative density zero, with growth `p^s`.** -/
theorem exists_re_gt_of_bddBelow_rpow_primes_off_null (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0)) {K s : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E →
      -(K * (p : ℝ) ^ s) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hs0 : 0 ≤ s) (hρs : 1 / 2 + s < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hmem := re_mem_of_bddBelow_rpow_of_samplingWeight (samplingWeight_primeOff E hE)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ (by linarith) hno (K := K) (s := s)
    (by linarith) fun j hj => by
      unfold primeOffWeight at hj
      split_ifs at hj with h
      · have := hK (j + 1) h.1 h.2
        push_cast at this
        exact this
      · exact absurd rfl hj
  exact zetaZeroConfig_im_ne_zero' _ hmem (Complex.ofReal_im _)

/-- **From below at the degrees of two primes, with growth `e^{sλ}`.** -/
theorem exists_re_gt_of_bddBelow_exp_twoPrimes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {K s : ℝ}
    (hK : ∀ a b : ℕ, -(K * Real.exp (s * (a * Real.log p + b * Real.log q))) ≤
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hs0 : 0 ≤ s) (hρs : 1 / 2 + s < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hmem := re_mem_of_bddBelow_rpow_of_samplingWeight (samplingWeight_unitWeight hp hq hpq)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ (by linarith) hno (K := K) (s := s)
    (by linarith) fun j hj => by
      obtain ⟨ab, rfl⟩ := unitWeight_ne_zero hj
      have hpos : (0 : ℝ) < (unitIndex p q ab : ℝ) + 1 := by positivity
      rw [Real.rpow_def_of_pos hpos, log_unitIndex_add_one hp hq ab, mul_comm _ s]
      exact hK ab.1 ab.2
  exact zetaZeroConfig_im_ne_zero' _ hmem (Complex.ofReal_im _)

/-! ### The width law modulo the approach to the line -/

/-- **At a residue class.** -/
theorem zetaZeroWidth_le_iff_bddBelow_rpow_primes_mod_of_zerosApproachLine
    (hZ : _root_.RHTower.BacklundConverse.ZerosApproachLine) {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {s : ℝ} (hs0 : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      -(K * (p : ℝ) ^ s) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hwid
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun p hp _ => ?_⟩
    have h := abs_two_re_lagStructure_le_exp_of_width temperedConfig_zetaZeroConfig (a := s)
      ((zetaZeroWidth_le_iff_re_le hs0).mp hwid) (log_nonneg_of_prime hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [show Real.exp (s * Real.log p) = (p : ℝ) ^ s by
      rw [Real.rpow_def_of_pos hp0, mul_comm]] at h
    exact neg_le_of_abs_le h
  · rintro ⟨K, hK⟩
    exact zetaZeroWidth_le_of_zerosApproachLine_of_noDeeper hZ hs0
      fun ρ₀ hρ₀ hρs => exists_re_gt_of_bddBelow_rpow_primes_mod ha hK hρ₀ hs0 hρs

/-- **At the primes off a set of relative density zero.** -/
theorem zetaZeroWidth_le_iff_bddBelow_rpow_primes_off_null_of_zerosApproachLine
    (hZ : _root_.RHTower.BacklundConverse.ZerosApproachLine) (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0)) {s : ℝ} (hs0 : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime → p ∉ E →
      -(K * (p : ℝ) ^ s) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hwid
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun p hp _ => ?_⟩
    have h := abs_two_re_lagStructure_le_exp_of_width temperedConfig_zetaZeroConfig (a := s)
      ((zetaZeroWidth_le_iff_re_le hs0).mp hwid) (log_nonneg_of_prime hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [show Real.exp (s * Real.log p) = (p : ℝ) ^ s by
      rw [Real.rpow_def_of_pos hp0, mul_comm]] at h
    exact neg_le_of_abs_le h
  · rintro ⟨K, hK⟩
    exact zetaZeroWidth_le_of_zerosApproachLine_of_noDeeper hZ hs0
      fun ρ₀ hρ₀ hρs => exists_re_gt_of_bddBelow_rpow_primes_off_null E hE hK hρ₀ hs0 hρs

/-- **At the degrees of two primes.** -/
theorem zetaZeroWidth_le_iff_bddBelow_exp_twoPrimes_of_zerosApproachLine
    (hZ : _root_.RHTower.BacklundConverse.ZerosApproachLine) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {s : ℝ} (hs0 : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ K : ℝ, ∀ a b : ℕ, -(K * Real.exp (s * (a * Real.log p + b * Real.log q))) ≤
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re := by
  constructor
  · intro hwid
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun a b => ?_⟩
    have hu : 0 ≤ a * Real.log p + b * Real.log q := by
      have := log_nonneg_of_prime hp; have := log_nonneg_of_prime hq; positivity
    exact neg_le_of_abs_le (abs_two_re_lagStructure_le_exp_of_width temperedConfig_zetaZeroConfig
      (a := s) ((zetaZeroWidth_le_iff_re_le hs0).mp hwid) hu)
  · rintro ⟨K, hK⟩
    exact zetaZeroWidth_le_of_zerosApproachLine_of_noDeeper hZ hs0
      fun ρ₀ hρ₀ hρs => exists_re_gt_of_bddBelow_exp_twoPrimes hp hq hpq hK hρ₀ hs0 hρs

/-! ### The tensor power trick at a residue class -/

/-- The `k`-th moment of the traces at the primes `p ≡ a (mod q)` up to `N`. -/
def primeTraceMomentMod {q : ℕ} (a : ZMod q) (k N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
    Real.log p * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k)

/-- **One term of a moment bounds the trace.** -/
theorem abs_trace_le_of_moment {q : ℕ} {a : ZMod q} {A C : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hC : ∀ N : ℕ, primeTraceMomentMod a k N ≤ C * (N : ℝ) ^ (1 + A)) {p : ℕ} (hp : p.Prime)
    (hpa : (p : ZMod q) = a) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤
      (|C| / Real.log 2) ^ ((1 : ℝ) / (2 * k)) * (p : ℝ) ^ ((1 + |A|) / (2 * k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := |C| / Real.log 2 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  set c := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re with hc
  -- one term of the moment at `N = p`
  have hone : Real.log p * c ^ (2 * k) ≤ C * (p : ℝ) ^ (1 + A) := by
    have hmem : p ∈ (Finset.range (p + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp, hpa⟩
    have h := hC p
    unfold primeTraceMomentMod at h
    refine le_trans (Finset.single_le_sum (f := fun r : ℕ => Real.log r *
      (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log r)).re) ^ (2 * k))
      (fun r hr => mul_nonneg (Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hr).2.1.one_lt.le)) (by
          rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)) hmem) h
  have hpA : (p : ℝ) ^ (1 + A) ≤ (p : ℝ) ^ (1 + |A|) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [le_abs_self A])
  have hc2k : |c| ^ (2 * k) ≤ B * (p : ℝ) ^ (1 + |A|) := by
    rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
    have h1 : Real.log 2 * c ^ (2 * k) ≤ Real.log p * c ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hlogp (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
    have h2 : C * (p : ℝ) ^ (1 + A) ≤ |C| * (p : ℝ) ^ (1 + |A|) :=
      mul_le_mul (le_abs_self C) hpA (by positivity) (abs_nonneg C)
    rw [hB, div_mul_eq_mul_div, le_div_iff₀ hlog2]
    linarith
  -- take the `2k`-th root
  have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
    show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
    Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hp0.le] at h1
  convert h1 using 3
  ring

/-- **Deligne's argument at a residue class gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_moments_primes_mod {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {A : ℝ}
    (hA : ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ N : ℕ, primeTraceMomentMod a k N ≤ C * (N : ℝ) ^ (1 + A)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_noDeepest fun ρ₀ hρ₀ hoff => ?_
  have hd : 0 < ρ₀.re - 1 / 2 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((1 + |A|) / (2 * (ρ₀.re - 1 / 2)))
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  have hk1 : 1 ≤ k := by
    have : 0 < k := by exact_mod_cast hk0
    omega
  obtain ⟨C, hC⟩ := hA k hk1
  have hs0 : 0 ≤ (1 + |A|) / (2 * (k : ℝ)) := by positivity
  have hsρ : 1 / 2 + (1 + |A|) / (2 * (k : ℝ)) < ρ₀.re := by
    rw [div_lt_iff₀ (by positivity)] at hk
    have : (1 + |A|) / (2 * (k : ℝ)) < ρ₀.re - 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  exact exists_re_gt_of_bddBelow_rpow_primes_mod ha
    (K := (|C| / Real.log 2) ^ ((1 : ℝ) / (2 * k)))
    (fun p hp hpa => neg_le_of_abs_le (abs_trace_le_of_moment hk1 hC hp hpa)) hρ₀ hs0 hsρ

/-- **RH is the approach to the line plus moment growth uniform in `k` at a residue class.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_moments_primes_mod {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    RiemannHypothesis ↔ _root_.RHTower.BacklundConverse.ZerosApproachLine ∧ ∃ A : ℝ,
      ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ N : ℕ, primeTraceMomentMod a k N ≤ C * (N : ℝ) ^ (1 + A) := by
  rw [_root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw]
  refine ⟨fun ⟨hZ, hAAL⟩ => ⟨hZ, ?_⟩, fun ⟨hZ, A, hA⟩ =>
    ⟨hZ, asymptoticAbscissaLaw_of_moments_primes_mod ha hA⟩⟩
  have hRH :=
    _root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZ, hAAL⟩
  obtain ⟨A, hA⟩ := riemannHypothesis_iff_moments_primeTraces.mp hRH
  refine ⟨A, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := hA k hk
  refine ⟨C, fun N => le_trans (?_ : primeTraceMomentMod a k N ≤ primeTraceMoment k N) (hC N)⟩
  -- the residue-class moment is a sub-sum of the full moment
  unfold primeTraceMomentMod primeTraceMoment
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
  · rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · have hpp := (Finset.mem_filter.mp hp).2
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

end GaloisForLFunctions.SurfaceOfSpecZ
