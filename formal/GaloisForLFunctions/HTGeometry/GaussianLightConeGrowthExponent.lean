import GaloisForLFunctions.HTGeometry.GaussianLightConeAmplification

/-!
# The growth exponent of a light-cone exponential sum

Let `S(ε) = Σ_i c_i exp(-ε w_i)` be as in `GaussianLightConeAmplification`: absolutely convergent
for `ε ≥ ε₀ ≥ 0`, with coefficients depending only on the exponent, a finite light cone
`{i | Re w_i < 0}` with nonzero coefficients, and a summable majorant `m` outside it.  Let `-M` be
the most negative real part in the light cone.

* **Upper bound** (`exists_norm_tsum_mul_exp_neg_le_exp`): `‖S(ε)‖ ≤ K e^{εM} + Σ m` for
  `ε ≥ ε₀`, with `K = Σ_{light cone} ‖c_i‖`.
* **Lower bound** (`exists_exp_le_norm_tsum_mul_exp_neg`): for every `δ > 0`, `‖S(ε)‖ ≥ e^{ε(M-δ)}`
  at arbitrarily large `ε`.

So `limsup_{ε→∞} ε⁻¹ log ‖S(ε)‖ = M`: the growth exponent of `S` is the depth of its light cone.
The lower bound averages the normalized light-cone sum `g(ε) = e^{-εM} Σ_{cone} c_i e^{-ε w_i}` over
windows of fixed length `T`.  The exponents attaining `-M` keep their full mass `A > 0`, and the
others contribute `O(1)`, so every window contains a point with `‖g‖ > A/4`.  There,
`‖S‖ ≥ e^{εM} A/4 − Σ m ≥ e^{ε(M−δ)}` once `ε` is large.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Window lemma.**  Finitely many exponents `b_i` with `Re b_i ≤ 0`, those with `b_i = 0` sharing
the nonzero coefficient `c₀`: some point of every window of length `T` carries
`‖Σ c_i e^{b_i x}‖ > A/4`, where `A = #{b_i = 0} ‖c₀‖`. -/
theorem exists_window_norm_finsum_exp_gt {ι : Type*} (P : Finset ι) (b c : ι → ℂ) (c₀ : ℂ)
    (hc₀ : c₀ ≠ 0) (hbre : ∀ i ∈ P, (b i).re ≤ 0) (hcZ : ∀ i ∈ P, b i = 0 → c i = c₀)
    (hZ : ∃ i ∈ P, b i = 0) :
    ∃ A > 0, ∃ T > 0, ∀ S : ℝ, 0 ≤ S →
      ∃ x ∈ Ioc S (S + T), A / 4 < ‖∑ i ∈ P, c i * Complex.exp (b i * x)‖ := by
  classical
  set g : ℝ → ℂ := fun x => ∑ i ∈ P, c i * Complex.exp (b i * x) with hg
  set Z := P.filter (fun i => b i = 0) with hZdef
  set N := P.filter (fun i => ¬ b i = 0) with hNdef
  obtain ⟨i₀, hi₀P, hi₀⟩ := hZ
  have hi₀Z : i₀ ∈ Z := by rw [hZdef, Finset.mem_filter]; exact ⟨hi₀P, hi₀⟩
  set A : ℝ := (Z.card : ℝ) * ‖c₀‖ with hAdef
  have hA : 0 < A := by
    have hcard : (0 : ℝ) < Z.card := by exact_mod_cast Finset.card_pos.2 ⟨i₀, hi₀Z⟩
    exact mul_pos hcard (norm_pos_iff.2 hc₀)
  set K : ℝ := ∑ i ∈ N, ‖c i‖ * (2 / ‖b i‖) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  have hint : ∀ S T : ℝ, 0 ≤ S → 0 ≤ T → T * A - K ≤ ‖∫ x in S..S + T, g x‖ := by
    intro S T hS hT
    have hsplit : ∫ x in S..S + T, g x =
        ∑ i ∈ P, c i * ∫ x in S..S + T, Complex.exp (b i * x) := by
      simp_rw [hg]
      rw [intervalIntegral.integral_finsetSum (f := fun i x => c i * Complex.exp (b i * x))
        fun i _ => ((continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)]
      exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
    have hZsum : ∑ i ∈ Z, c i * ∫ x in S..S + T, Complex.exp (b i * x) =
        (Z.card : ℂ) * c₀ * T := by
      have : ∀ i ∈ Z, c i * ∫ x in S..S + T, Complex.exp (b i * x) = c₀ * T := by
        intro i hi
        rw [hZdef, Finset.mem_filter] at hi
        rw [hcZ i hi.1 hi.2, hi.2]
        simp
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      ring
    have hNsum : ‖∑ i ∈ N, c i * ∫ x in S..S + T, Complex.exp (b i * x)‖ ≤ K := by
      rw [hKdef]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [hNdef, Finset.mem_filter] at hi
      rw [norm_mul]
      gcongr
      exact norm_integral_exp_mul_le_two_div hi.2 (hbre i hi.1) hS hT
    have hfilt := Finset.sum_filter_add_sum_filter_not P (fun i => b i = 0)
      (fun i => c i * ∫ x in S..S + T, Complex.exp (b i * x))
    rw [← hZdef, ← hNdef, hZsum] at hfilt
    rw [hsplit, ← hfilt]
    have hmain : ‖(Z.card : ℂ) * c₀ * (T : ℂ)‖ = T * A := by
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hT, hAdef]
      ring
    have := norm_sub_norm_le ((Z.card : ℂ) * c₀ * (T : ℂ))
      (-(∑ i ∈ N, c i * ∫ x in S..S + T, Complex.exp (b i * x)))
    rw [sub_neg_eq_add, norm_neg, hmain] at this
    linarith
  set T : ℝ := 2 * (K + 1) / A with hTdef
  have hT : 0 < T := by positivity
  have hTA : T * A = 2 * (K + 1) := by rw [hTdef]; field_simp
  refine ⟨A, hA, T, hT, fun S hS => ?_⟩
  by_contra hcon
  push Not at hcon
  have hbound : ‖∫ x in S..S + T, g x‖ ≤ A / 4 * |S + T - S| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact hcon x hx
  have hlow := hint S T hS hT.le
  rw [show S + T - S = T by ring, abs_of_pos hT] at hbound
  nlinarith

/-- The light cone `P`, the remainder bound, and the decomposition of the sum. -/
theorem norm_tsum_compl_le_of_majorant {ι : Type*} {w c : ι → ℂ} {ε₀ : ℝ} (P : Finset ι)
    (hP : ∀ i, i ∈ P ↔ (w i).re < 0)
    {m : ι → ℝ} (hm0 : ∀ i, 0 ≤ m i) (hm : Summable m)
    (hmaj : ∀ i, 0 ≤ (w i).re → ∀ ε, ε₀ ≤ ε → ‖c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ m i)
    (hsum : ∀ ε, ε₀ ≤ ε → Summable (fun i => ‖c i * Complex.exp (-(ε : ℂ) * w i)‖))
    {ε : ℝ} (hε : ε₀ ≤ ε) :
    ‖∑' i, c i * Complex.exp (-(ε : ℂ) * w i) -
        ∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ ∑' i, m i := by
  have hsumm : Summable (fun i => c i * Complex.exp (-(ε : ℂ) * w i)) := (hsum ε hε).of_norm
  rw [← hsumm.sum_add_tsum_compl (s := P), add_sub_cancel_left]
  have hnormsub : Summable (fun x : ↥((↑P : Set ι)ᶜ) =>
      ‖c x * Complex.exp (-(ε : ℂ) * w x)‖) := (hsum ε hε).subtype _
  refine (norm_tsum_le_tsum_norm hnormsub).trans ?_
  refine (hnormsub.tsum_le_tsum (g := fun x : ↥((↑P : Set ι)ᶜ) => m x)
    (fun x => ?_) (hm.subtype _)).trans ?_
  · have hx : (x : ι) ∉ P := x.2
    rw [hP, not_lt] at hx
    exact hmaj x hx ε hε
  · exact Summable.tsum_subtype_le m _ hm0 hm

/-- **Upper bound by the light-cone depth.**  `‖S(ε)‖ ≤ K e^{εM} + Σ m` for all `ε ≥ ε₀`. -/
theorem exists_norm_tsum_mul_exp_neg_le_exp {ι : Type*} {w c : ι → ℂ} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀)
    (hfin : {i | (w i).re < 0}.Finite)
    {m : ι → ℝ} (hm0 : ∀ i, 0 ≤ m i) (hm : Summable m)
    (hmaj : ∀ i, 0 ≤ (w i).re → ∀ ε, ε₀ ≤ ε → ‖c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ m i)
    (hsum : ∀ ε, ε₀ ≤ ε → Summable (fun i => ‖c i * Complex.exp (-(ε : ℂ) * w i)‖))
    (M : ℝ) (hMmax : ∀ i, (w i).re < 0 → -(w i).re ≤ M) :
    ∃ K : ℝ, ∀ ε : ℝ, ε₀ ≤ ε →
      ‖∑' i, c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ K * Real.exp (ε * M) + ∑' i, m i := by
  classical
  set P := hfin.toFinset with hPdef
  have hP : ∀ i, i ∈ P ↔ (w i).re < 0 := fun i => by
    rw [hPdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  refine ⟨∑ i ∈ P, ‖c i‖, fun ε hε => ?_⟩
  have hε0 : 0 ≤ ε := hε₀.trans hε
  have hrem := norm_tsum_compl_le_of_majorant P hP hm0 hm hmaj hsum hε
  have hcone : ‖∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤
      (∑ i ∈ P, ‖c i‖) * Real.exp (ε * M) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, Complex.norm_exp]
    gcongr
    rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
    have := hMmax i ((hP i).1 hi)
    nlinarith
  have htri := norm_add_le (∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i))
    (∑' i, c i * Complex.exp (-(ε : ℂ) * w i) - ∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i))
  rw [add_sub_cancel] at htri
  linarith

/-- **Lower bound by the light-cone depth.**  For every `δ > 0`, `‖S(ε)‖ ≥ e^{ε(M−δ)}` at
arbitrarily large `ε`. -/
theorem exists_exp_le_norm_tsum_mul_exp_neg {ι : Type*} {w c : ι → ℂ} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀)
    (hcoef : ∀ i j, w i = w j → c i = c j)
    (hc : ∀ i, (w i).re < 0 → c i ≠ 0)
    (hfin : {i | (w i).re < 0}.Finite)
    {m : ι → ℝ} (hm0 : ∀ i, 0 ≤ m i) (hm : Summable m)
    (hmaj : ∀ i, 0 ≤ (w i).re → ∀ ε, ε₀ ≤ ε → ‖c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ m i)
    (hsum : ∀ ε, ε₀ ≤ ε → Summable (fun i => ‖c i * Complex.exp (-(ε : ℂ) * w i)‖))
    (M : ℝ) (hMatt : ∃ i, (w i).re = -M ∧ (w i).re < 0)
    (hMmax : ∀ i, (w i).re < 0 → -(w i).re ≤ M) :
    ∀ δ : ℝ, 0 < δ → ∀ S : ℝ, ∃ ε : ℝ, S ≤ ε ∧ ε₀ ≤ ε ∧
      Real.exp (ε * (M - δ)) ≤ ‖∑' i, c i * Complex.exp (-(ε : ℂ) * w i)‖ := by
  classical
  intro δ hδ S
  set P := hfin.toFinset with hPdef
  have hP : ∀ i, i ∈ P ↔ (w i).re < 0 := fun i => by
    rw [hPdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨is, hisM, hisneg⟩ := hMatt
  have hisP : is ∈ P := (hP is).2 hisneg
  have hM : 0 < M := by linarith
  set b : ι → ℂ := fun i => -(w i - w is) with hb
  have hbre : ∀ i ∈ P, (b i).re ≤ 0 := fun i hi => by
    have := hMmax i ((hP i).1 hi)
    simp only [hb, Complex.neg_re, Complex.sub_re]
    linarith
  have hcZ : ∀ i ∈ P, b i = 0 → c i = c is := fun i _ h => by
    simp only [hb, neg_eq_zero, sub_eq_zero] at h
    exact hcoef i is h
  obtain ⟨A, hA, T, hT, hwin⟩ := exists_window_norm_finsum_exp_gt P b c (c is) (hc is hisneg)
    hbre hcZ ⟨is, hisP, by simp [hb]⟩
  set H := ∑' i, m i with hHdef
  have hH : 0 ≤ H := tsum_nonneg hm0
  set S' : ℝ := max (max S ε₀) (8 / (A * δ) + 8 * H / (A * M)) with hS'def
  have hS'S : S ≤ S' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS'ε₀ : ε₀ ≤ S' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hS'big : 8 / (A * δ) + 8 * H / (A * M) ≤ S' := le_max_right _ _
  obtain ⟨ε, hεmem, hεg⟩ := hwin S' (hε₀.trans hS'ε₀)
  have hεS' : S' ≤ ε := hεmem.1.le
  have hε₀ε : ε₀ ≤ ε := hS'ε₀.trans hεS'
  refine ⟨ε, hS'S.trans hεS', hε₀ε, ?_⟩
  -- the light cone is `e^{-ε w_is}` times the normalized sum
  have hPsum : ∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i) =
      Complex.exp (-(ε : ℂ) * w is) * ∑ i ∈ P, c i * Complex.exp (b i * ε) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  have hnormWs : ‖Complex.exp (-(ε : ℂ) * w is)‖ = Real.exp (ε * M) := by
    rw [Complex.norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul, hisM]
    ring_nf
  have hcone : Real.exp (ε * M) * (A / 4) <
      ‖∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i)‖ := by
    rw [hPsum, norm_mul, hnormWs]
    exact mul_lt_mul_of_pos_left hεg (Real.exp_pos _)
  have hrem := norm_tsum_compl_le_of_majorant P hP hm0 hm hmaj hsum hε₀ε
  have htri := norm_sub_norm_le (∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i))
    (∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i) - ∑' i, c i * Complex.exp (-(ε : ℂ) * w i))
  rw [sub_sub_cancel, norm_sub_rev] at htri
  -- the two thresholds
  have hε0 : 0 ≤ ε := hε₀.trans hε₀ε
  have h1 : 8 / (A * δ) ≤ ε := by
    have : 0 ≤ 8 * H / (A * M) := by positivity
    linarith
  have h2 : 8 * H / (A * M) ≤ ε := by
    have : 0 ≤ 8 / (A * δ) := by positivity
    linarith
  have hdecay : Real.exp (-(ε * δ)) ≤ A / 8 := by
    have hpos : 0 < 1 + ε * δ := by positivity
    have hle : 1 + ε * δ ≤ Real.exp (ε * δ) := by
      have := Real.add_one_le_exp (ε * δ); linarith
    rw [Real.exp_neg]
    have h8 : 8 / A ≤ 1 + ε * δ := by
      have := mul_le_mul_of_nonneg_right h1 hδ.le
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hδ.ne'] at this
      linarith
    calc (Real.exp (ε * δ))⁻¹ ≤ (8 / A)⁻¹ :=
          inv_anti₀ (by positivity) (h8.trans hle)
      _ = A / 8 := by rw [inv_div]
  have hgrow : H ≤ Real.exp (ε * M) * (A / 8) := by
    have hle : 1 + ε * M ≤ Real.exp (ε * M) := by
      have := Real.add_one_le_exp (ε * M); linarith
    have hεM : 8 * H / A ≤ ε * M := by
      have := mul_le_mul_of_nonneg_right h2 hM.le
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hM.ne'] at this
      exact this
    have : H ≤ ε * M * (A / 8) := by
      have h := mul_le_mul_of_nonneg_right hεM (by positivity : (0 : ℝ) ≤ A / 8)
      have e : 8 * H / A * (A / 8) = H := by field_simp
      linarith
    nlinarith [Real.exp_pos (ε * M)]
  have hsplitexp : Real.exp (ε * (M - δ)) = Real.exp (ε * M) * Real.exp (-(ε * δ)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplitexp]
  have hEM := Real.exp_pos (ε * M)
  have : Real.exp (ε * M) * Real.exp (-(ε * δ)) ≤ Real.exp (ε * M) * (A / 8) :=
    mul_le_mul_of_nonneg_left hdecay hEM.le
  nlinarith

end

end GaloisForLFunctions.HTGeometry
