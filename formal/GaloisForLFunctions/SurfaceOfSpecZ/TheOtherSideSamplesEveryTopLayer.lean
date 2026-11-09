import GaloisForLFunctions.SurfaceOfSpecZ.TheRankinSquareDivergesAtTwiceTheTopWeight
import GaloisForLFunctions.SquareRootThreshold.DirichletLFunctionTwoBumpCriterion

/-!
# The other side samples every top layer

`ThePrimesSampleEveryTopLayer` needs configurations without real zeros: a real zero at the top
contributes a positive constant to the normalized trace `F = 2 Re S e^{−bu}` and masks. An upper
bound sees it.

* `tendsto_normTraceMean_real`: the relative mean of `F` along the prime powers tends to the
  coefficient `e_b ≥ 0` of the real top exponent.
* `onLine_of_bddAbove_primePowers_of_max`: for every tempered configuration whose maximal real part
  is attained, `2 Re S_Z(log n) ≤ K` at the prime powers puts every zero on the critical line. From
  `F ≤ |K| n^{−b}`, the mean of `F` gives `e_b ≤ 0`, so `e_b = 0`, and then `F² ≤ E(2|K|n^{−b} − F)`
  forces `Σ_{Re z = b}|e_z|² ≤ 0`.
* `grh_of_bddAbove_primePowers_of_max`: for a primitive Dirichlet character, if some zero of
  `L(s, χ)` has maximal real part, an upper bound on the traces of its zeros at the prime powers of
  `ℤ` is GRH, with no hypothesis on real (Siegel) zeros.
* `exists_prime_lt_and_gt_of_lt_zetaZeroWidth`: the oscillation theorem at the primes. If some zero
  of `ζ` has `|Re ρ − ½| > a`, `0 ≤ a < ½`, then for every `K` there are primes with
  `2 Re S(log p) < −K p^a` and primes with `2 Re S(log p) > K p^a`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

section TopLayer

variable {Z : ZeroConfig} {b : ℝ}

/-- **The relative mean of `F` is the real top coefficient.** -/
theorem tendsto_normTraceMean_real (hZ : TemperedConfig Z) (h : TopDepth Z b) :
    Tendsto (fun σ => normTraceMean Z b σ / vmSum σ) (𝓝[>] 1)
      (𝓝 (evenCoeff Z (boxSpline 1 3) b).re) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hc : Tendsto (fun σ : ℝ => ∑' z, e z * (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) /
      (vmSum σ : ℂ)) (𝓝[>] 1) (𝓝 (∑' z : ℂ, if z = (b : ℂ) then e z else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hzb : z = (b : ℂ)
      · have hconst : ∀ σ : ℝ, 1 < σ →
            e z * (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) / (vmSum σ : ℂ) = e z := by
          intro σ hσ
          rw [hzb, sub_self, add_zero, ← ofReal_vmSum hσ, mul_div_assoc,
            div_self (by exact_mod_cast (vmSum_pos hσ).ne'), mul_one]
        simp only [if_pos hzb]
        exact tendsto_const_nhds.congr' (by
          filter_upwards [self_mem_nhdsWithin] with σ hσ
          exact (hconst σ hσ).symm)
      · simp only [if_neg hzb]
        by_cases hz : e z = 0
        · simp [hz]
        have h1 := h z hz
        have hne : (b : ℂ) - z ≠ 0 := fun h0 => hzb (by linear_combination -h0)
        have := (tendsto_logDeriv_div_vmSum (c₀ := (b : ℂ) - z) (by simp; linarith) hne).const_mul
          (-e z)
        simpa [mul_div_assoc, neg_div, mul_neg, neg_mul] using this
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro z
      have hσ1 : 1 < σ := hσ
      by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have hres : 1 < ((σ : ℂ) + (b - z)).re := by simp; linarith
      have hV : 0 < vmSum σ := vmSum_pos hσ1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, norm_neg,
        div_le_iff₀ hV]
      have hb1 := norm_logDeriv_le_vmSum hres
      have hb2 : vmSum ((σ : ℂ) + (b - z)).re ≤ vmSum σ := vmSum_antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (norm_nonneg _)
  rw [tsum_ite_eq] at hc
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  refine (hc'.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hrat : ((normTraceMean Z b σ / vmSum σ : ℝ) : ℂ) =
      ∑' z, e z * (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) / (vmSum σ : ℂ) := by
    rw [Complex.ofReal_div, ofReal_normTraceMean hZ h hσ, tsum_div_const]
  simp only [Function.comp_def]
  rw [← hrat, Complex.ofReal_re]

/-- At a prime power an upper bound `2 Re S(log n) ≤ K` gives `F(log n) ≤ |K| n^{−b}`. -/
theorem normTrace_le_of_upper {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re ≤ K)
    {j : ℕ} (hj : IsPrimePow (j + 1)) :
    normTrace Z b (Real.log ((j : ℝ) + 1)) ≤ |K| * ((j : ℝ) + 1) ^ (-b) := by
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 := hK (j + 1) hj
  push_cast at h1
  have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
  rw [normTrace, hexp]
  have h3 := mul_le_mul_of_nonneg_right h1 hpb.le
  have h4 : K * ((j : ℝ) + 1) ^ (-b) ≤ |K| * ((j : ℝ) + 1) ^ (-b) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hpb.le
  linarith

theorem normTraceMean_le_of_upper (hZ : TemperedConfig Z) (h : TopDepth Z b) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re ≤ K)
    {σ : ℝ} (hσ : 1 < σ) (hb0 : 0 ≤ b) :
    normTraceMean Z b σ ≤ |K| * vmSum (σ + b) := by
  have hεsum := summable_vonMangoldt_rpow (show 1 < σ + b by linarith)
  rw [vmSum, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_normTraceMean hZ h hσ) (hεsum.mul_left _)
  have hΛ := vonMangoldt_nonneg (n := j + 1)
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
  have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
    rw [← Real.rpow_add hj0]; ring_nf
  rw [hsplit]
  by_cases hΛ0 : Λ (j + 1) = 0
  · rw [hΛ0]; simp
  have hle := normTrace_le_of_upper (b := b) hK (vonMangoldt_ne_zero_iff.mp hΛ0)
  have hw : 0 ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hΛ hp.le
  have := mul_le_mul_of_nonneg_right hle hw
  calc Λ (j + 1) * normTrace Z b (Real.log ((j : ℝ) + 1)) * ((j : ℝ) + 1) ^ (-σ) =
        normTrace Z b (Real.log ((j : ℝ) + 1)) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := by ring
    _ ≤ |K| * ((j : ℝ) + 1) ^ (-b) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := this
    _ = _ := by ring

/-- **From above, `F² ≤ E(2|K|n^{−b} − F)`**, summed with the weights `Λ(n) n^{−σ}`. -/
theorem normTraceSqMean_le_of_upper (hZ : TemperedConfig Z) (h : TopDepth Z b) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re ≤ K)
    {σ : ℝ} (hσ : 1 < σ) (hb0 : 0 ≤ b) :
    normTraceSqMean Z b σ ≤ 2 * (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * |K| * vmSum (σ + b) -
      (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * normTraceMean Z b σ := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  have hεsum := summable_vonMangoldt_rpow (show 1 < σ + b by linarith)
  have hS₁sum := summable_normTraceMean hZ h hσ
  have hrhs : Summable fun j : ℕ =>
      2 * E * |K| * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(σ + b))) -
        E * (Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) :=
    (hεsum.mul_left _).sub (hS₁sum.mul_left E)
  calc normTraceSqMean Z b σ
      ≤ ∑' j : ℕ, (2 * E * |K| * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(σ + b))) -
          E * (Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ))) := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_normTraceSqMean hZ h hσ) hrhs
        have hΛ := vonMangoldt_nonneg (n := j + 1)
        have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
        have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
          rw [← Real.rpow_add hj0]; ring_nf
        rw [hsplit]
        by_cases hΛ0 : Λ (j + 1) = 0
        · rw [hΛ0]; simp
        have hup := normTrace_le_of_upper (b := b) hK (vonMangoldt_ne_zero_iff.mp hΛ0)
        have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
        have hFb := abs_normTrace_le hZ h (log_add_one_nonneg j)
        set f := normTrace Z b (Real.log ((j : ℝ) + 1))
        have habs : |f| ≤ 2 * (|K| * ((j : ℝ) + 1) ^ (-b)) - f := by
          rcases le_total 0 f with h0 | h0
          · rw [abs_of_nonneg h0]; linarith
          · rw [abs_of_nonpos h0]; nlinarith [abs_nonneg K]
        have hsq : f ^ 2 ≤ E * (2 * (|K| * ((j : ℝ) + 1) ^ (-b)) - f) := by
          calc f ^ 2 = |f| * |f| := by rw [← sq_abs, sq]
            _ ≤ E * |f| := mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left habs hE0
        have hw : 0 ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hΛ hp.le
        have h5 := mul_le_mul_of_nonneg_right hsq hw
        calc Λ (j + 1) * f ^ 2 * ((j : ℝ) + 1) ^ (-σ) =
              f ^ 2 * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := by ring
          _ ≤ E * (2 * (|K| * ((j : ℝ) + 1) ^ (-b)) - f) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := h5
          _ = _ := by ring
    _ = 2 * E * |K| * vmSum (σ + b) - E * normTraceMean Z b σ := by
        rw [(hεsum.mul_left _).tsum_sub (hS₁sum.mul_left E), tsum_mul_left, tsum_mul_left]
        rfl

end TopLayer

/-- **The other side at the prime powers sees every attained top layer.** For a tempered
configuration whose maximal real part is attained, an upper bound on the spline traces at the
prime powers puts every zero on the critical line, real zeros included. -/
theorem onLine_of_bddAbove_primePowers_of_max (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have hhalf : 1 / 2 ≤ ρ₀.re := by
    have h := hmax _ (Z.reflect_mem ρ₀ hρ₀)
    have hrefl : (Zeta23.reflect ρ₀).re = 1 - ρ₀.re := by simp [Zeta23.reflect]
    rw [hrefl] at h; linarith
  suffices hb : ρ₀.re = 1 / 2 by
    intro ρ hρ
    have h1 := hmax ρ hρ
    have h2 := hmax _ (Z.reflect_mem ρ hρ)
    have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
    rw [hrefl] at h2; linarith
  by_contra hne
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; exact sub_pos.mpr (lt_of_le_of_ne hhalf (Ne.symm hne))
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hpos := re_tsum_diagWeight_pos hZ htop hz₀ (by simp [hbdef])
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  -- the real top coefficient is `≥ 0`
  set R := (evenCoeff Z (boxSpline 1 3) b).re with hRdef
  have hR0 : 0 ≤ R := by
    by_cases hmem : (1 / 2 + (b : ℂ)) ∈ Z.carrier
    · exact (evenCoeff_spline_pos_of_real Z hmem (by simpa using hb0) (by simp)).le
    · have hzero : evenCoeff Z (boxSpline 1 3) b = 0 := by
        by_contra hz
        rcases mem_of_evenCoeff_ne_zero hz with h | h
        · exact hmem h
        · exact hmem (by simpa using h)
      rw [hRdef, hzero, Complex.zero_re]
  have hlimε : Tendsto (fun σ => vmSum (σ + b) / vmSum σ) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := vmSum (1 + b))).div_atTop tendsto_vmSum_atTop) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_nonneg (vmSum_nonneg _) (vmSum_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      exact div_le_div_of_nonneg_right (vmSum_antitone (by linarith) (by linarith))
        (vmSum_nonneg _)
  have hlim₁ := tendsto_normTraceMean_real hZ htop
  -- the upper bound gives `R ≤ 0`
  have hRle : R ≤ 0 := by
    have hup : Tendsto (fun σ => |K| * (vmSum (σ + b) / vmSum σ)) (𝓝[>] 1) (𝓝 0) := by
      simpa using hlimε.const_mul |K|
    refine le_of_tendsto_of_tendsto hlim₁ hup ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := hσ
    have hV := vmSum_pos hσ1
    rw [div_le_iff₀ hV, mul_div_assoc', div_mul_cancel₀ _ hV.ne']
    exact normTraceMean_le_of_upper hZ htop hK hσ1 hb0.le
  have hR : R = 0 := le_antisymm hRle hR0
  -- and then the mean of `F²` vanishes
  have hrhs : Tendsto (fun σ => 2 * E * |K| * (vmSum (σ + b) / vmSum σ) -
      E * (normTraceMean Z b σ / vmSum σ)) (𝓝[>] 1) (𝓝 0) := by
    have := (hlimε.const_mul (2 * E * |K|)).sub (hlim₁.const_mul E)
    rw [← hRdef, hR] at this
    simpa using this
  have hle : (∑' q, diagWeight Z b q).re ≤ 0 := by
    refine le_of_tendsto_of_tendsto (tendsto_normTraceSqMean hZ htop) hrhs ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := hσ
    have hV := vmSum_pos hσ1
    have h := normTraceSqMean_le_of_upper hZ htop hK hσ1 hb0.le
    rw [div_le_iff₀ hV]
    have : (2 * E * |K| * (vmSum (σ + b) / vmSum σ) - E * (normTraceMean Z b σ / vmSum σ)) *
        vmSum σ = 2 * E * |K| * vmSum (σ + b) - E * normTraceMean Z b σ := by field_simp
    rw [this]; exact h
  linarith

/-- **GRH from above at the prime powers.** For a primitive character, if some zero of `L(s, χ)`
has maximal real part, an upper bound on the spline traces of its zeros at the prime powers is
GRH. -/
theorem grh_of_bddAbove_primePowers_of_max {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier)
    (hmax : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n →
      2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hq hprim)) (boxSpline 1 3) (Real.log n)).re ≤ K) :
    ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2 :=
  onLine_of_bddAbove_primePowers_of_max _ (temperedConfig_LZeros hq hprim) hρ₀ hmax hK

/-- **The oscillation theorem at the primes.** If some zero of `ζ` lies at depth `> a`,
`0 ≤ a < ½`, then for every `K` some prime has `2 Re S(log p) < −K p^a` and some prime has
`2 Re S(log p) > K p^a`. -/
theorem exists_prime_lt_and_gt_of_lt_zetaZeroWidth {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hw : a < zetaZeroWidth) (K : ℝ) :
    (∃ p : ℕ, p.Prime ∧
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re < -(K * (p : ℝ) ^ a)) ∧
    (∃ p : ℕ, p.Prime ∧
      K * (p : ℝ) ^ a < 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) := by
  constructor
  · by_contra h
    push Not at h
    exact (not_le.mpr hw) ((zetaZeroWidth_le_iff_bddBelow_primeDegrees ha0 ha).mpr ⟨K, h⟩)
  · by_contra h
    push Not at h
    exact (not_le.mpr hw) ((zetaZeroWidth_le_iff_bddAbove_primeDegrees ha0 ha).mpr ⟨K, h⟩)

end GaloisForLFunctions.SurfaceOfSpecZ
