import GaloisForLFunctions.SurfaceOfSpecZ.SeparatedOrdinatesAreSeenInEveryWindow
import GaloisForLFunctions.RHTower.ErrorExponentAbscissaExcessLaw

/-!
# Short windows miss separated configurations

Windows of length `80/δ` decide configurations with `δ`-separated ordinates
(`onLine_of_bddBelow_windows_of_separatedOrdinates`). The length is sharp up to the constant:
for every `δ > 0` the off-line pair `{¾ + iδ/2, ¼ + iδ/2}` is tempered, has no real zeros and
`δ`-separated ordinates, and its trace is bounded below on windows of length `2π/δ` beyond every
bound (`exists_separatedOrdinates_bddBelow_on_short_windows`).

If the only exponents of positive depth are `z₁, z̄₁`, then for `u ≥ 0`
`2 Re S(u) ≥ 2 Re(D_{z₁} e^{z₁u}) − Σ |D_z|` (`two_re_lagStructure_ge_of_single_pair`), and
`Re(D_{z₁} e^{z₁u}) = |D_{z₁}| e^{Re z₁ u} cos(arg D_{z₁} + Im z₁ · u) ≥ 0` on the windows of
length `π/Im z₁` around `u_n = (2πn − arg D_{z₁})/Im z₁`. So the decisive window length of
`δ`-separated configurations lies between `2π/δ` and `80/δ`.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **One pair of positive depth.** If the exponents of positive depth are `z₁, z̄₁` only, then for
`u ≥ 0` the trace is at least `2 Re(D_{z₁} e^{z₁u}) − Σ |D_z|`: every other exponent has
`|e^{zu}| ≤ 1`. -/
theorem two_re_lagStructure_ge_of_single_pair {Z : ZeroConfig} (hZ : TemperedConfig Z) {z₁ : ℂ}
    (hz₁ : z₁.im ≠ 0)
    (hpos : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → 0 < z.re → z = z₁ ∨ z = conj z₁) {u : ℝ}
    (hu : 0 ≤ u) :
    2 * (evenCoeff Z (boxSpline 1 3) z₁ * cexp (z₁ * u)).re -
        ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ ≤
      2 * (lagStructure Z (boxSpline 1 3) u).re := by
  classical
  obtain ⟨hsum, heq⟩ := two_re_lagStructure_eq Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
    (boxSpline_support (r := 1) one_pos 3) u
  have hs := summable_norm_evenCoeff_spline hZ
  have hne : z₁ ≠ conj z₁ := fun h => hz₁ (by
    have := congrArg Complex.im h; simp at this; linarith)
  have hsplit := hsum.sum_add_tsum_subtype_compl {z₁, conj z₁}
  rw [Finset.sum_pair hne] at hsplit
  have hc : evenCoeff Z (boxSpline 1 3) (conj z₁) * cexp (conj z₁ * u) =
      conj (evenCoeff Z (boxSpline 1 3) z₁ * cexp (z₁ * u)) := by
    rw [evenCoeff_conj, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have hterm : ∀ z : {x // x ∉ ({z₁, conj z₁} : Finset ℂ)},
      ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ := by
    rintro ⟨z, hz⟩
    simp only
    rw [norm_mul, norm_cexp_mul_ofReal]
    by_cases h0 : evenCoeff Z (boxSpline 1 3) z = 0
    · simp [h0]
    have hre : z.re ≤ 0 := by
      by_contra h
      push Not at h
      rcases hpos z h0 h with h' | h' <;> exact hz (by simp [h'])
    calc ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (z.re * u)
        ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hre hu))
            (norm_nonneg _)
      _ = _ := mul_one _
  have hsn : Summable fun z : {x // x ∉ ({z₁, conj z₁} : Finset ℂ)} =>
      ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.subtype _)
  have htail : ‖∑' z : {x // x ∉ ({z₁, conj z₁} : Finset ℂ)},
      evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ ≤ ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ :=
    calc _ ≤ ∑' z : {x // x ∉ ({z₁, conj z₁} : Finset ℂ)},
          ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' z : {x // x ∉ ({z₁, conj z₁} : Finset ℂ)}, ‖evenCoeff Z (boxSpline 1 3) z‖ :=
          Summable.tsum_le_tsum hterm hsn (hs.subtype _)
      _ ≤ ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ := by
          have h := hs.sum_add_tsum_subtype_compl {z₁, conj z₁}
          have h0 : 0 ≤ ∑ z ∈ ({z₁, conj z₁} : Finset ℂ), ‖evenCoeff Z (boxSpline 1 3) z‖ :=
            Finset.sum_nonneg fun _ _ => norm_nonneg _
          linarith
  have hre := congrArg Complex.re (heq.trans hsplit.symm)
  rw [Complex.ofReal_re, hc, Complex.add_re, Complex.add_re, Complex.conj_re] at hre
  have hneg := (abs_le.mp ((Complex.abs_re_le_norm _).trans htail)).1
  linarith

theorem temperedConfig_offLinePairConfig (T : ℝ) : TemperedConfig (RHTower.offLinePairConfig T) := by
  haveI : Finite (RHTower.offLinePairConfig T).carrier :=
    (Set.toFinite ({⟨3 / 4, T⟩, ⟨1 / 4, T⟩} : Set ℂ)).to_subtype
  exact Summable.of_finite

/-- The exponents of the off-line pair: ordinate `±T`, depth `±¼`, and positive depth only at
`¼ ± iT`. -/
theorem mem_zeroExps_offLinePairConfig {T : ℝ} {z : ℂ}
    (hz : z ∈ zeroExps (RHTower.offLinePairConfig T)) :
    (z.im = T ∨ z.im = -T) ∧ (z.re = 1 / 4 ∨ z.re = -(1 / 4)) ∧
      (0 < z.re → z = ⟨1 / 4, T⟩ ∨ z = conj (⟨1 / 4, T⟩ : ℂ)) := by
  have key : ∀ w : ℂ, (1 / 2 + w : ℂ) ∈ (RHTower.offLinePairConfig T).carrier →
      w.im = T ∧ (w.re = 1 / 4 ∨ w.re = -(1 / 4)) := by
    intro w hw
    rcases hw with h | h
    · have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp at h1 h2
      exact ⟨h2, Or.inl (by linarith)⟩
    · have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp at h1 h2
      exact ⟨h2, Or.inr (by linarith)⟩
  rcases hz with h | h
  · obtain ⟨hi, hr⟩ := key z h
    refine ⟨Or.inl hi, hr, fun hp => Or.inl ?_⟩
    rcases hr with hr | hr
    · exact Complex.ext hr hi
    · linarith
  · obtain ⟨hi, hr⟩ := key (conj z) h
    rw [Complex.conj_im] at hi
    rw [Complex.conj_re] at hr
    refine ⟨Or.inr (by linarith), hr, fun hp => Or.inr ?_⟩
    rcases hr with hr | hr
    · exact Complex.ext (by simpa using hr) (by simp; linarith)
    · linarith

theorem separatedOrdinates_offLinePairConfig {T : ℝ} (hT : 0 < T) :
    SeparatedOrdinates (RHTower.offLinePairConfig T) (2 * T) := by
  intro z hz z' hz' hne hne'
  obtain ⟨hi, hr, -⟩ := mem_zeroExps_offLinePairConfig hz
  obtain ⟨hi', hr', -⟩ := mem_zeroExps_offLinePairConfig hz'
  by_cases him : z.im = z'.im
  · exfalso
    by_cases hre : z.re = z'.re
    · exact hne (Complex.ext hre.symm him.symm)
    · refine hne' (Complex.ext ?_ (by simp [him]))
      rw [Complex.neg_re, Complex.conj_re]
      rcases hr with h | h <;> rcases hr' with h' | h' <;>
        first | linarith | exact absurd (by linarith) hre
  · rcases hi with h | h <;> rcases hi' with h' | h'
    · exact absurd (h.trans h'.symm) him
    · rw [h, h', sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
    · rw [h, h', show -T - T = -(2 * T) by ring, abs_neg, abs_of_pos (by linarith)]
    · exact absurd (h.trans h'.symm) him

/-- **Short windows miss separated configurations.** For every `δ > 0` there is a tempered
configuration without real zeros, with `δ`-separated ordinates and a zero off the line, whose trace
is bounded below on windows of length `2π/δ` beyond every bound. -/
theorem exists_separatedOrdinates_bddBelow_on_short_windows {δ : ℝ} (hδ : 0 < δ) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧ SeparatedOrdinates Z δ ∧
      (∃ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2) ∧ ∃ K : ℝ, ∀ U : ℝ, ∃ u₀, U ≤ u₀ ∧
        ∀ u ∈ Icc (u₀ - π / δ) (u₀ + π / δ),
          -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  set T : ℝ := δ / 2 with hTdef
  have hT : 0 < T := by positivity
  set Z := RHTower.offLinePairConfig T with hZdef
  have hZ : TemperedConfig Z := temperedConfig_offLinePairConfig T
  set z₁ : ℂ := ⟨1 / 4, T⟩ with hz₁def
  set D₁ := evenCoeff Z (boxSpline 1 3) z₁ with hD₁
  set A := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hA
  have hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0 := by
    rintro ρ (rfl | rfl) <;> exact hT.ne'
  refine ⟨Z, hZ, hnoreal, ?_, ⟨⟨3 / 4, T⟩, Or.inl rfl, by norm_num⟩, A, fun U => ?_⟩
  · have := separatedOrdinates_offLinePairConfig hT
    rwa [show 2 * T = δ by rw [hTdef]; ring] at this
  -- window centre `u₀ = (2πn − arg D₁)/T`
  obtain ⟨n, hn⟩ := exists_nat_ge ((T * (max U 0 + π / δ) + D₁.arg) / (2 * π))
  set u₀ : ℝ := (2 * π * n - D₁.arg) / T with hu₀
  have hu₀T : T * u₀ = 2 * π * n - D₁.arg := by rw [hu₀]; field_simp
  have hbig : max U 0 + π / δ ≤ u₀ := by
    rw [div_le_iff₀ (by positivity)] at hn
    rw [hu₀, le_div_iff₀ hT]; linarith
  have hπδ : T * (π / δ) = π / 2 := by rw [hTdef]; field_simp
  refine ⟨u₀, by linarith [le_max_left U 0, div_pos Real.pi_pos hδ], fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith [hu.1, le_max_right U 0]
  have hmain := two_re_lagStructure_ge_of_single_pair hZ (z₁ := z₁) (by simpa [hz₁def] using hT.ne')
    (fun z hz hp => (mem_zeroExps_offLinePairConfig (mem_of_evenCoeff_ne_zero hz)).2.2 hp) hu0
  -- the pair term is nonnegative on the window
  have hpair : 0 ≤ (D₁ * cexp (z₁ * u)).re := by
    have e : D₁ * cexp (z₁ * u) =
        ((‖D₁‖ * Real.exp (u / 4) : ℝ) : ℂ) * cexp (((D₁.arg + T * u : ℝ) : ℂ) * I) := by
      have hz : z₁ * (u : ℂ) = ((u / 4 : ℝ) : ℂ) + ((T * u : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [hz₁def]; ring
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I D₁, hz, Complex.exp_add]
      push_cast
      rw [add_mul, Complex.exp_add]
      ring
    rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    refine mul_nonneg (by positivity) ?_
    have hcos : Real.cos (D₁.arg + T * u) = Real.cos (D₁.arg + T * u - n * (2 * π)) :=
      (Real.cos_sub_nat_mul_two_pi _ n).symm
    rw [hcos]
    have h1 : T * (u₀ - π / δ) ≤ T * u := mul_le_mul_of_nonneg_left hu.1 hT.le
    have h2 : T * u ≤ T * (u₀ + π / δ) := mul_le_mul_of_nonneg_left hu.2 hT.le
    rw [mul_sub, hu₀T, hπδ] at h1
    rw [mul_add, hu₀T, hπδ] at h2
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
