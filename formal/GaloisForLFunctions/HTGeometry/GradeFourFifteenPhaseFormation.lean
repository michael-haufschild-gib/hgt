import GaloisForLFunctions.HTGeometry.GradeFourHurwitzNumerator
import GaloisForLFunctions.HTGeometry.StableCausalExactification

/-!
# Grade-four causal Green kernel and fifteen-phase formation

For four positive grades the time polynomial `P_4(z) = (2z + e_1) Q_4(z)` has positive degree and,
by the Hurwitz theorem, no zero in `Re z ≥ 0`.  Its causal Green kernel `g_4` (Laplace transform
`1/P_4`) is a finite sum of polynomial–exponential terms with exponents in `Re μ < 0`, lies in
`L¹ ∩ L²` of the half-line, and convolution by it is bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`
(Corollary 4.2).  The fifteen-phase law `H_4` of `Σ_{S ≠ ∅} X_{λ_S}` satisfies
`W_4 F_4 = Δ_4 P_4(∂_t) H_4` `(GFH.23)` and, for distinct grades, `H_4 = W_4 g_4 ∗ Δ_4⁻¹ F_4`
`(GFH.24)`.  For grades at least `log 2` the law dominates the Erlang-fifteen law `(GFH.26)`, which
gives the all-prime quadruple frame `(GFH.29)`.
-/

open MeasureTheory Set Filter Topology Polynomial
open MvPolynomial (aeval)

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

variable {lam : Fin 4 → ℝ}

/-- The time polynomial `P_4 = (2z + e_1) Q_4` over `ℝ`. -/
theorem formPoly_four (lam : Fin 4 → ℝ) :
    formPoly lam = (C 2 * X + C (esymm1 lam)) * (C 6 * X ^ 4 + C (12 * esymm1 lam) * X ^ 3 +
      C (8 * esymm1 lam ^ 2 + 2 * esymm2 lam) * X ^ 2 +
      C (2 * esymm1 lam ^ 3 + 2 * esymm1 lam * esymm2 lam) * X +
      C (esymm1 lam ^ 2 * esymm2 lam - esymm1 lam * esymm3 lam + esymm4 lam)) := by
  rw [formPoly, formNumer_four]
  simp only [quartic, esymm1, esymm2, esymm3, esymm4, lamVar, map_add, map_mul, map_sub, map_pow,
    MvPolynomial.aeval_X, Option.elim_none, Option.elim_some, map_ofNat]

theorem natDegree_formPolyC_four_pos (hlam : ∀ i, 0 < lam i) : 0 < (formPolyC lam).natDegree := by
  rw [formPolyC, natDegree_map_eq_of_injective Complex.ofReal_injective, formPoly_four]
  have hQ : (C 6 * X ^ 4 + C (12 * esymm1 lam) * X ^ 3 +
      C (8 * esymm1 lam ^ 2 + 2 * esymm2 lam) * X ^ 2 +
      C (2 * esymm1 lam ^ 3 + 2 * esymm1 lam * esymm2 lam) * X +
      C (esymm1 lam ^ 2 * esymm2 lam - esymm1 lam * esymm3 lam + esymm4 lam) : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (eval 0) h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero] at this
    have h0 := hlam 0; have h1 := hlam 1; have h2 := hlam 2; have h3 := hlam 3
    have hpos : 0 < esymm1 lam ^ 2 * esymm2 lam - esymm1 lam * esymm3 lam + esymm4 lam := by
      have := esymm_mul_sub_pos hlam
      have he1 : 0 < esymm1 lam := by simp only [esymm1]; positivity
      have he4 : 0 < esymm4 lam := by simp only [esymm4]; positivity
      nlinarith
    norm_num at this
    linarith
  have hL : (C 2 * X + C (esymm1 lam) : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.natDegree) h
    simp only [natDegree_linear (two_ne_zero : (2 : ℝ) ≠ 0), natDegree_zero] at this
    exact one_ne_zero this
  rw [natDegree_mul hL hQ, natDegree_linear two_ne_zero]
  omega

/-- **Theorem 4.1** in polynomial form: `P_4` has no zero in `Re z ≥ 0`. -/
theorem formPolyC_four_ne_zero (hlam : ∀ i, 0 < lam i) {z : ℂ} (hz : 0 ≤ z.re) :
    (formPolyC lam).eval z ≠ 0 := by
  rw [eval_formPolyC]
  exact formNumer_four_ne_zero hlam hz

/-- **Corollary 4.2 (a)**: `1/P_4` is the Laplace transform of the causal kernel `g_4`. -/
theorem laplace_formKernel_four (hlam : ∀ i, 0 < lam i) {q : ℂ} (hq : 0 < q.re) :
    (formKernel lam).laplace q = ((formPolyC lam).eval q)⁻¹ ∧
      ∫ t in Ioi (0 : ℝ), (formKernel lam).eval t * Complex.exp (-(q * t)) =
        ((formPolyC lam).eval q)⁻¹ := by
  have hstab := formKernel_stable fun z hz => formPolyC_four_ne_zero hlam hz
  have hL := QuasiPolynomial.laplace_ratKernel (natDegree_formPolyC_four_pos hlam)
    (q := q) fun μ hμ =>
      (roots_formPolyC_re_neg (fun z hz => formPolyC_four_ne_zero hlam hz) μ hμ).trans hq
  refine ⟨hL, ?_⟩
  rw [(QuasiPolynomial.integral_eval_mul_cexp _ fun μ hμ => (hstab μ hμ).trans hq).2]
  exact hL

/-- **Corollary 4.2 (b)**: the exponents of `g_4` lie in `Re μ < 0`, so `g_4 ∈ L¹ ∩ L²` of the
half-line. -/
theorem formKernel_four_mem (hlam : ∀ i, 0 < lam i) :
    (∀ μ ∈ (formKernel lam).support, μ.re < 0) ∧
      Integrable (causalExt (formKernel lam).eval) ∧ MemLp (causalExt (formKernel lam).eval) 2 := by
  have hstab := formKernel_stable fun _ hz => formPolyC_four_ne_zero hlam hz
  exact ⟨hstab, integrable_causalExt (QuasiPolynomial.integrableOn_eval_of_stable hstab),
    memLp_two_causalExt hstab⟩

/-- **Corollary 4.2 (c)**: convolution by `g_4` is bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_formKernel_four_conv_le (hlam : ∀ i, 0 < lam i) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) {p : ENNReal} (hp : 1 ≤ p) :
    eLpNorm (lineConv (causalExt (formKernel lam).eval) f) p volume ≤
        eLpNorm (causalExt (formKernel lam).eval) 1 volume * eLpNorm f p volume ∧
      eLpNorm (causalExt (formKernel lam).eval) 1 volume < ⊤ :=
  eLpNorm_lineConv_causal_le (formKernel_stable fun _ hz => formPolyC_four_ne_zero hlam hz) hf hp

/-- **Theorem 5.1, `(GFH.24)`**: for distinct positive grades,
`H_4 = W_4 g_4 ∗ Δ_4⁻¹ F_4` on `[0, ∞)`. -/
theorem subsetCDF_four_eq_conv (hlam : ∀ i, 0 < lam i) (hinj : Function.Injective lam) {t : ℝ}
    (ht : 0 ≤ t) :
    (subsetCDF lam t : ℂ) = (subsetIncidence lam : ℂ) *
      causalConv (formKernel lam).eval
        (fun s => ((delta lam : ℝ) : ℂ)⁻¹ * scheduleAlternant lam s) t := by
  have hΔ : delta lam ≠ 0 := by
    rw [delta]
    refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun b hb =>
      sub_ne_zero.2 fun h => ?_
    exact (ne_of_lt (Finset.mem_Ioi.1 hb)) (hinj h)
  exact subsetCDF_eq_formKernel_conv hlam hΔ (natDegree_formPolyC_four_pos hlam)
    (fun z hz => formPolyC_four_ne_zero hlam hz) ht

/-- **`(GFH.26)`**: for grades at least `log 2`, `H_4 ≥ G_15`. -/
theorem erlangFifteen_le_subsetCDF (hlam : ∀ i, Real.log 2 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) :
    erlangCDF 15 (Real.log 2) t ≤ subsetCDF lam t := by
  have hl := Real.log_pos one_lt_two
  have h := erlangCDF_le_subsetCDF hl (fun i => hl.trans_le (hlam i)) hlam ht
  simpa using h

/-- **`(GFH.27)`**: `c_{T,15}² > 0`. -/
theorem erlangFloor_fifteen_pos {T : ℝ} (hT : 0 < T) : 0 < erlangFloor 15 T :=
  erlangFloor_pos 15 hT

/-- **Theorem 6.1, `(GFH.29)`: the global grade-four frame.** -/
theorem quadrupleFrame {T : ℝ} (hT : 0 ≤ T) (d : HistoryFamily.Controls (PrimeTuple 4)) :
    erlangFloor 15 T * ‖d‖ ^ 2 ≤ ‖(formationFamily 4).response T d‖ ^ 2 ∧
      ‖(formationFamily 4).response T d‖ ^ 2 ≤ T * ‖d‖ ^ 2 := by
  simpa using formation_frame (r := 4) hT d


/-! ### The Hurwitz minors `(GFH.17)`–`(GFH.18)` -/

/-- **`(GFH.17)`**: `a_3 a_2 - a_4 a_1 = 12 e_1 (7e_1² + e_2)`. -/
theorem hurwitzMinorOne_four (l : Fin 4 → ℝ) :
    12 * esymm1 l * (8 * esymm1 l ^ 2 + 2 * esymm2 l) -
        6 * (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) =
      12 * esymm1 l * (7 * esymm1 l ^ 2 + esymm2 l) := by ring

/-- **`(GFH.18)`**: `a_3 a_2 a_1 - a_4 a_1² - a_3² a_0 =
24 e_1² (7e_1⁴ + 2e_1²e_2 + e_2² + 6e_1e_3 - 6e_4)`. -/
theorem hurwitzMinorTwo_four (l : Fin 4 → ℝ) :
    12 * esymm1 l * (8 * esymm1 l ^ 2 + 2 * esymm2 l) *
        (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) -
      6 * (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) ^ 2 -
      (12 * esymm1 l) ^ 2 * (esymm1 l ^ 2 * esymm2 l - esymm1 l * esymm3 l + esymm4 l) =
      24 * esymm1 l ^ 2 * (7 * esymm1 l ^ 4 + 2 * esymm1 l ^ 2 * esymm2 l + esymm2 l ^ 2 +
        6 * esymm1 l * esymm3 l - 6 * esymm4 l) := by ring

theorem hurwitzMinors_pos (hlam : ∀ i, 0 < lam i) :
    0 < 12 * esymm1 lam * (7 * esymm1 lam ^ 2 + esymm2 lam) ∧
      0 < 7 * esymm1 lam ^ 4 + 2 * esymm1 lam ^ 2 * esymm2 lam + esymm2 lam ^ 2 +
        6 * esymm1 lam * esymm3 lam - 6 * esymm4 lam := by
  have h0 := hlam 0; have h1 := hlam 1; have h2 := hlam 2; have h3 := hlam 3
  have he1 : 0 < esymm1 lam := by simp only [esymm1]; positivity
  have he2 : 0 < esymm2 lam := by simp only [esymm2]; positivity
  have he3 : 0 < esymm3 lam := by simp only [esymm3]; positivity
  have hsq := six_esymm4_le_sq hlam
  exact ⟨by positivity, by nlinarith [pow_pos he1 4]⟩

/-! ### The ambient Vandermonde inverse over prime quadruples -/

/-- **Hostile correction 5**: `Δ_4⁻¹` is unbounded on prime quadruples, because prime-log crowding
makes `Δ_4(log 2, log 3, log p, log q)` arbitrarily small. -/
theorem not_bddAbove_inv_delta_primeQuadruples :
    ¬ BddAbove (Set.range fun x : {v : Fin 4 → ℕ // (∀ i, (v i).Prime) ∧ StrictMono v} =>
      |delta fun i => Real.log (x.1 i)|⁻¹) := by
  rintro ⟨M, hM⟩
  obtain ⟨P⟩ := CrowdedPairs.nonempty
  have hl1 : Real.log 3 < 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hl2 : Real.log 2 < Real.log 3 := Real.log_lt_log two_pos (by norm_num)
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hla : ∀ j, Real.log 3 < P.a j := fun j => by
    have := P.a_ge j; have := P.base_ge j; linarith
  have hp3 : ∀ j, 3 < P.p j := fun j => by
    have h := hla j
    unfold CrowdedPairs.a at h
    exact_mod_cast (Real.log_lt_log_iff (by norm_num) (by exact_mod_cast (P.p_prime j).pos)).mp h
  have hpq : ∀ j, P.p j < P.q j := fun j => by
    have h := P.a_lt_b j
    unfold CrowdedPairs.a CrowdedPairs.b at h
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (P.p_prime j).pos)
      (by exact_mod_cast (P.q_prime j).pos)).mp h
  have hmem : ∀ j, |delta ![Real.log 2, Real.log 3, P.a j, P.b j]|⁻¹ ≤ M := fun j => by
    have hsm : StrictMono ![2, 3, P.p j, P.q j] := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i
      · show (2 : ℕ) < 3; norm_num
      · show 3 < P.p j; exact hp3 j
      · show P.p j < P.q j; exact hpq j
    have hpr : ∀ i, (![2, 3, P.p j, P.q j] i).Prime := fun i => by
      fin_cases i
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact P.p_prime j
      · exact P.q_prime j
    have := hM ⟨⟨_, hpr, hsm⟩, rfl⟩
    convert this using 4
    funext i
    fin_cases i <;> rfl
  have hval : ∀ j, |delta ![Real.log 2, Real.log 3, P.a j, P.b j]| =
      (Real.log 3 - Real.log 2) * (P.a j - Real.log 2) * (P.b j - Real.log 2) *
        (P.a j - Real.log 3) * (P.b j - Real.log 3) * (P.b j - P.a j) := fun j => by
    rw [delta_fin_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have h1 := hla j; have h2 := P.a_lt_b j
    rw [show (Real.log 2 - Real.log 3) * (Real.log 2 - P.a j) * (Real.log 2 - P.b j) *
        (Real.log 3 - P.a j) * (Real.log 3 - P.b j) * (P.a j - P.b j) =
      (Real.log 3 - Real.log 2) * (P.a j - Real.log 2) * (P.b j - Real.log 2) *
        (P.a j - Real.log 3) * (P.b j - Real.log 3) * (P.b j - P.a j) by ring]
    exact abs_of_pos (by
      have := sub_pos.2 hl2; have := sub_pos.2 h2
      have : 0 < P.a j - Real.log 2 := by linarith
      have : 0 < P.b j - Real.log 2 := by linarith
      have : 0 < P.a j - Real.log 3 := by linarith
      have : 0 < P.b j - Real.log 3 := by linarith
      positivity)
  have hpos : ∀ j, 0 < |delta ![Real.log 2, Real.log 3, P.a j, P.b j]| := fun j => by
    rw [hval]
    have h1 := hla j; have h2 := P.a_lt_b j
    have := sub_pos.2 hl2; have := sub_pos.2 h2
    have : 0 < P.a j - Real.log 2 := by linarith
    have : 0 < P.b j - Real.log 2 := by linarith
    have : 0 < P.a j - Real.log 3 := by linarith
    have : 0 < P.b j - Real.log 3 := by linarith
    positivity
  have hbound : ∀ j, |delta ![Real.log 2, Real.log 3, P.a j, P.b j]| ≤
      (P.base j + 3) ^ 5 * (3 * P.η j) := fun j => by
    rw [hval]
    have h1 := hla j; have h2 := P.a_lt_b j; have h3 := P.b_le j; have h4 := P.b_sub_a_le j
    have hb3 := P.base_ge j
    have e1 : Real.log 3 - Real.log 2 ≤ P.base j + 3 := by linarith
    have e2 : P.a j - Real.log 2 ≤ P.base j + 3 := by linarith
    have e3 : P.b j - Real.log 2 ≤ P.base j + 3 := by linarith
    have e4 : P.a j - Real.log 3 ≤ P.base j + 3 := by linarith
    have e5 : P.b j - Real.log 3 ≤ P.base j + 3 := by linarith
    have p1 : 0 ≤ Real.log 3 - Real.log 2 := by linarith
    have p2 : 0 ≤ P.a j - Real.log 2 := by linarith
    have p3 : 0 ≤ P.b j - Real.log 2 := by linarith
    have p4 : 0 ≤ P.a j - Real.log 3 := by linarith
    have p5 : 0 ≤ P.b j - Real.log 3 := by linarith
    have p6 : 0 ≤ P.b j - P.a j := by linarith
    calc (Real.log 3 - Real.log 2) * (P.a j - Real.log 2) * (P.b j - Real.log 2) *
          (P.a j - Real.log 3) * (P.b j - Real.log 3) * (P.b j - P.a j)
        ≤ (P.base j + 3) * (P.base j + 3) * (P.base j + 3) * (P.base j + 3) *
          (P.base j + 3) * (3 * P.η j) := by gcongr
      _ = (P.base j + 3) ^ 5 * (3 * P.η j) := by ring
  have hbase : Tendsto P.base atTop atTop := by
    rw [show P.base = fun j : ℕ => P.R₀ + 4 * (j : ℝ) from funext P.base_eq]
    exact tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hlim : Tendsto (fun j => (P.base j + 3) ^ 5 * (3 * P.η j)) atTop (𝓝 0) := by
    have h1 := ((tendsto_zpow_mul_crowdWidth P.hc P.hK 5).comp hbase).const_mul (3 * 2 ^ 5)
    rw [mul_zero] at h1
    refine squeeze_zero (fun j => by have := (P.η_pos j).le; have := P.base_ge j; positivity)
      (fun j => ?_) h1
    have hb3 := P.base_ge j
    have hη := (P.η_pos j).le
    simp only [Function.comp_apply, zpow_ofNat]
    unfold CrowdedPairs.η
    have h5 : (P.base j + 3) ^ 5 ≤ 2 ^ 5 * P.base j ^ 5 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) 5
    have hw := crowdWidth_pos (c := P.c) P.hK (P.base j)
    nlinarith
  have hM0 : 0 < M := (inv_pos.mpr (hpos 0)).trans_le (hmem 0)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (inv_pos.mpr hM0))).exists
  have := hmem j
  rw [inv_le_comm₀ (hpos j) hM0] at this
  linarith [hbound j]

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
