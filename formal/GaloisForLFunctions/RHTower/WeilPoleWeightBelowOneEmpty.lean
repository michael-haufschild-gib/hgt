import GaloisForLFunctions.RHTower.WeilConePoleWeightRigidity
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy

/-!
# Below the residue of `ζ` the Weil cone is empty

The Weil functional with pole weight `β` (`weilPoleWeightFunctional β lam`) replaces the pole term
`k̂(i/2) + k̂(−i/2)` of `ζ` by `β` times it.

**Theorem** (`not_forall_re_weilPoleWeightFunctional_nonneg`).  Let `β < 1` and let `lam` have
linearly bounded deviation partial sums: `|Σ_{n≤N} (lam(n) − Λ(n))| ≤ A(N + 1)`.  Then the
functional with pole weight `β` is negative on the autocorrelation of some real `C²` compactly
supported test.  In particular (`β = 0`) the Gamma factor of `ζ` alone admits no Weil-positive
weights of this kind.

Proof.  The twisted arc minimum principle gives weights `w_j ≥ 0`, `w_0 > 0`, for which the
shifted-Gamma tests `F_j` (`F̂_j = Ξ·Q_j`, `Q_j(z) = ∏_{k<j}(k + ¼ + iz/2)`) are jointly
prime-blind, and every `F̂_j` vanishes at every zero of `ζ`.  On the truncations `F_{j,L}` the
functional splits as

`Re W_ζ(F_{j,L}) − (prime pairing of lam − Λ) + (β − 1)·2(∫F_{j,L}e^{−u/2})(∫F_{j,L}e^{u/2})`.

As `L → ∞` the weighted zeta sides and prime sides tend to `0` (`tendsto_tsum_W_truncTest`,
`tendsto_tsum_atomPairing_truncTest`).  The weighted pole terms tend to
`Σ_j w_j·2 F̂_j(i/2) F̂_j(−i/2) = w_0·2ξ(0)ξ(1) = w_0/2`, since `Q_j(i/2) = 0` for `j ≥ 1`.  So the
weighted sum of nonnegative values tends to `(β − 1)w_0/2 < 0`, a contradiction.

So the null tests of the twisted arc have a strictly positive pole term: the pole is what balances
them.  Together with the cone uniqueness at `β = 1` (`eq_vonMangoldt_of_weilPositiveFull`), the true
residue is the least pole weight for which positivity is possible at all.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat
open Zeta23

noncomputable section

namespace RHTower.WeilPoleWeight

open WeilSpectral

/-- The pole term of a real autocorrelation:
`Re(k̂(i/2) + k̂(−i/2)) = 2 (∫ F e^{−u/2}) (∫ F e^{u/2})`. -/
theorem re_pole_weilTest_ofReal {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    (paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (I / 2) +
      paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (-I / 2)).re =
      2 * ((∫ u, F u * Real.exp (-u / 2)) * ∫ u, F u * Real.exp (u / 2)) := by
  have hc : Continuous (fun u => (F u : ℂ)) := Complex.continuous_ofReal.comp hF
  have hcc : HasCompactSupport (fun u => (F u : ℂ)) := hFc.comp_left Complex.ofReal_zero
  rw [EF.paperFT_weilTest hc hc hcc hcc, EF.paperFT_weilTest hc hc hcc hcc, conj_I_div_two,
    conj_neg_I_div_two, paperFT_ofRealFun_I_div_two, paperFT_ofRealFun_neg_I_div_two]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The functional with pole weight `β` on a real autocorrelation splits into the zeta side, the
prime pairing of the deviation, and the pole term. -/
theorem re_weilPoleWeightFunctional_ofReal (β : ℝ) (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFr : Continuous F) (hFc : HasCompactSupport F) :
    (weilPoleWeightFunctional β lam (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re =
      (zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)).re -
        atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) (crossCorr F F) +
        (β - 1) * (2 * ((∫ u, F u * Real.exp (-u / 2)) * ∫ u, F u * Real.exp (u / 2))) := by
  have h := re_weilFullFunctional_add_eq (fun n => lam n - ArithmeticFunction.vonMangoldt n) hF hFc
  have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
      (lam n - ArithmeticFunction.vonMangoldt n)) = lam := funext fun n => by ring
  rw [hfun] at h
  rw [weilPoleWeightFunctional, Complex.add_re, h,
    show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
    re_pole_weilTest_ofReal hFr hFc]

/-! ### Exponential moments of the truncations -/

theorem abs_mul_exp_le_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hF : DecayBound F δ C) {c : ℝ}
    (hc : |c| ≤ 1 / 2) (u : ℝ) :
    |F u * Real.exp (c * u)| ≤ C * Real.exp (-(δ * |u|)) := by
  have h1 := (hF.2.2 u).1
  have hcu : c * u ≤ |u| / 2 := by
    have := neg_abs_le c
    calc c * u ≤ |c * u| := le_abs_self _
      _ = |c| * |u| := abs_mul _ _
      _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = |u| / 2 := by ring
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |F u| * Real.exp (c * u) ≤ C * Real.exp (-((1 / 2 + δ) * |u|)) * Real.exp (|u| / 2) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr hcu) (Real.exp_pos _).le
          (le_trans (abs_nonneg _) h1)
    _ = C * Real.exp (-(δ * |u|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem integrable_truncTest_mul_exp {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C)
    {c : ℝ} (hc : |c| ≤ 1 / 2) (L : ℝ) :
    Integrable fun u => truncTest F L u * Real.exp (c * u) := by
  have hcont : Continuous fun u => truncTest F L u * Real.exp (c * u) :=
    ((contDiff_truncTest hF.1 L).continuous).mul (by fun_prop)
  refine ((integrable_exp_neg_mul_abs_fam hδ).const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := abs_mul_exp_le_of_decayBound hF hc u
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h
  exact (mul_le_mul_of_nonneg_right (abs_truncTest_le F L u) (Real.exp_pos _).le).trans h

theorem abs_integral_truncTest_mul_exp_le {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) {c : ℝ} (hc : |c| ≤ 1 / 2) (L : ℝ) :
    |∫ u, truncTest F L u * Real.exp (c * u)| ≤ C * ∫ u, Real.exp (-(δ * |u|)) := by
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => abs_nonneg _)
    ((integrable_exp_neg_mul_abs_fam hδ).const_mul C) (Eventually.of_forall fun u => ?_))
  show |truncTest F L u * Real.exp (c * u)| ≤ C * Real.exp (-(δ * |u|))
  have h := abs_mul_exp_le_of_decayBound hF hc u
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h ⊢
  exact (mul_le_mul_of_nonneg_right (abs_truncTest_le F L u) (Real.exp_pos _).le).trans h

theorem tendsto_integral_truncTest_mul_exp {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) {c : ℝ} (hc : |c| ≤ 1 / 2) :
    Tendsto (fun L => ∫ u, truncTest F L u * Real.exp (c * u)) atTop
      (𝓝 (∫ u, F u * Real.exp (c * u))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u => C * Real.exp (-(δ * |u|)))
    (Eventually.of_forall fun L => ?_) (Eventually.of_forall fun L => ?_)
    ((integrable_exp_neg_mul_abs_fam hδ).const_mul C) (Eventually.of_forall fun u => ?_)
  · exact (((contDiff_truncTest hF.1 L).continuous).mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs]
    have h := abs_mul_exp_le_of_decayBound hF hc u
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h ⊢
    exact (mul_le_mul_of_nonneg_right (abs_truncTest_le F L u) (Real.exp_pos _).le).trans h
  · refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨|u| + 1, fun L hL => ?_⟩)
    show F u * Real.exp (c * u) = truncTest F L u * Real.exp (c * u)
    rw [truncTest_eq_self (by linarith)]

/-! ### The pole term of the shifted-Gamma family -/

theorem shiftedGammaPoly_I_div_two {j : ℕ} (hj : 1 ≤ j) : shiftedGammaPoly j (I / 2) = 0 := by
  unfold shiftedGammaPoly
  refine Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (by omega)) ?_
  have : I * (I / 2) / 2 = -(1 / 4 : ℂ) := by rw [← mul_div_assoc, Complex.I_mul_I]; ring
  rw [this]; push_cast; ring

theorem integral_xiShiftedGammaTest_mul_exp_neg_half (j : ℕ) :
    ((∫ u, xiShiftedGammaTest j u * Real.exp (-u / 2) : ℝ) : ℂ) = xiShiftedGamma j (I / 2) := by
  rw [← paperFT_ofRealFun_I_div_two, paperFT_xiShiftedGammaTest j (by simp; norm_num)]

theorem integral_xiShiftedGammaTest_mul_exp_half (j : ℕ) :
    ((∫ u, xiShiftedGammaTest j u * Real.exp (u / 2) : ℝ) : ℂ) = xiShiftedGamma j (-I / 2) := by
  rw [← paperFT_ofRealFun_neg_I_div_two, paperFT_xiShiftedGammaTest j (by simp; norm_num)]

theorem integral_xiShiftedGammaTest_mul_exp_neg_half_of_pos {j : ℕ} (hj : 1 ≤ j) :
    ∫ u, xiShiftedGammaTest j u * Real.exp (-u / 2) = 0 := by
  have h := integral_xiShiftedGammaTest_mul_exp_neg_half j
  rw [xiShiftedGamma, shiftedGammaPoly_I_div_two hj, mul_zero] at h
  exact_mod_cast h

theorem xi_zero_eq_half : xi 0 = 1 / 2 := by
  rw [← xi_one, ← xi_one_sub 1, sub_self]

theorem pole_xiShiftedGammaTest_zero :
    2 * ((∫ u, xiShiftedGammaTest 0 u * Real.exp (-u / 2)) *
      ∫ u, xiShiftedGammaTest 0 u * Real.exp (u / 2)) = 1 / 2 := by
  have h1 := integral_xiShiftedGammaTest_mul_exp_neg_half 0
  have h2 := integral_xiShiftedGammaTest_mul_exp_half 0
  simp only [xiShiftedGamma, shiftedGammaPoly, Finset.range_zero, Finset.prod_empty, mul_one,
    RHTower.XiC] at h1 h2
  rw [show (1 / 2 : ℂ) + I / 2 * I = 0 by rw [mul_comm, ← mul_div_assoc, Complex.I_mul_I]; ring,
    xi_zero_eq_half] at h1
  rw [show (1 / 2 : ℂ) + -I / 2 * I = 1 by
    rw [mul_comm, ← mul_div_assoc, mul_neg, Complex.I_mul_I]; ring, xi_one] at h2
  have e1 : ∫ u, xiShiftedGammaTest 0 u * Real.exp (-u / 2) = 1 / 2 := by
    have := congrArg Complex.re h1
    simpa using this
  have e2 : ∫ u, xiShiftedGammaTest 0 u * Real.exp (u / 2) = 1 / 2 := by
    have := congrArg Complex.re h2
    simpa using this
  rw [e1, e2]; norm_num

/-! ### The theorem -/

/-- **Below the residue the cone is empty.**  For `β < 1` and weights with linearly bounded
deviation partial sums, the Weil functional with pole weight `β` is negative on some real
autocorrelation. -/
theorem not_forall_re_weilPoleWeightFunctional_nonneg {β : ℝ} (hβ : β < 1) {lam : ℕ → ℝ} {A : ℝ}
    (hA : ∀ N : ℕ, |primeWeightPartialSum (fun n => lam n - ArithmeticFunction.vonMangoldt n) N|
      ≤ A * (N + 1)) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleWeightFunctional β lam
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re := by
  intro hpos
  -- the twisted arc weights
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν : Measure ArcParam := (μ : Measure ArcParam) with hν
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsumw : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblindInt := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  -- the shifted-Gamma family
  obtain ⟨C, hC, hF⟩ := exists_decayBound_xiShiftedGammaTest
  set F : ℕ → ℝ → ℝ := xiShiftedGammaTest with hFdef
  set Cj : ℕ → ℝ := fun j => C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) with hCj
  have hsum : Summable fun j => w j * Cj j ^ 2 :=
    (hsumw.mul_left (C ^ 2)).congr fun j => by simp only [hCj]; ring
  have hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0 := by
    intro n hn
    simp_rw [hFdef, crossCorr_xiShiftedGammaTest]
    have e : ∀ j, w j * (1 / (2 * Real.pi) *
        ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
        1 / (2 * Real.pi) * (w j *
          ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
    simp_rw [e]
    rw [tsum_mul_left, hblindInt n hn, mul_zero]
  have hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier,
      paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0 := fun j ρ =>
    paperFT_xiShiftedGammaTest_gammaOf j ρ
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  set K : ℝ := ∫ u, Real.exp (-((1 / 4 : ℝ) * |u|)) with hK
  have hK0 : 0 ≤ K := integral_nonneg fun _ => (Real.exp_pos _).le
  -- notation for the pieces
  set a : ℕ → ℝ → ℝ := fun j L => ∫ u, truncTest (F j) L u * Real.exp (-u / 2) with ha
  set b : ℕ → ℝ → ℝ := fun j L => ∫ u, truncTest (F j) L u * Real.exp (u / 2) with hb
  have hneg : ∀ u : ℝ, -u / 2 = (-1 / 2 : ℝ) * u := fun u => by ring
  have hpos2 : ∀ u : ℝ, u / 2 = (1 / 2 : ℝ) * u := fun u => by ring
  have habs_neg : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num [abs_of_neg]
  have habs_pos : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have ha_le : ∀ j L, |a j L| ≤ Cj j * K := fun j L => by
    have h := abs_integral_truncTest_mul_exp_le hδ (hF j) habs_neg L
    simp_rw [← hneg] at h
    exact h
  have hb_le : ∀ j L, |b j L| ≤ Cj j * K := fun j L => by
    have h := abs_integral_truncTest_mul_exp_le hδ (hF j) habs_pos L
    simp_rw [← hpos2] at h
    exact h
  have hpole_le : ∀ j L, ‖w j * (2 * (a j L * b j L))‖ ≤ w j * Cj j ^ 2 * (2 * K ^ 2) := by
    intro j L
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
    have hab : |a j L| * |b j L| ≤ (Cj j * K) * (Cj j * K) :=
      mul_le_mul (ha_le j L) (hb_le j L) (abs_nonneg _) ((abs_nonneg _).trans (ha_le j L))
    calc w j * (2 * (|a j L| * |b j L|)) ≤ w j * (2 * (Cj j * K * (Cj j * K))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab (by norm_num)) (hw j)
      _ = w j * Cj j ^ 2 * (2 * K ^ 2) := by ring
  -- limits of the three weighted sums
  have h1 := tendsto_tsum_W_truncTest hδ hF hw hsum hΛ0 hΛ hzero
  have h2 := tendsto_tsum_atomPairing_truncTest hδ hF hw hsum hΛ0 hΛ hA hblind
  have h3 : Tendsto (fun L => ∑' j, w j * (2 * (a j L * b j L))) atTop
      (𝓝 (∑' j, w j * (2 * ((∫ u, F j u * Real.exp (-u / 2)) *
        ∫ u, F j u * Real.exp (u / 2))))) := by
    refine tendsto_tsum_of_dominated_convergence (hsum.mul_right (2 * K ^ 2)) (fun j => ?_)
      (Eventually.of_forall fun L j => hpole_le j L)
    have ta := tendsto_integral_truncTest_mul_exp hδ (hF j) habs_neg
    have tb := tendsto_integral_truncTest_mul_exp hδ (hF j) habs_pos
    simp_rw [← hneg] at ta
    simp_rw [← hpos2] at tb
    exact ((ta.mul tb).const_mul 2).const_mul (w j)
  have hval : ∑' j, w j * (2 * ((∫ u, F j u * Real.exp (-u / 2)) *
      ∫ u, F j u * Real.exp (u / 2))) = w 0 * (1 / 2) := by
    rw [tsum_eq_single 0 fun j hj => ?_]
    · rw [hFdef, pole_xiShiftedGammaTest_zero]
    · rw [hFdef, integral_xiShiftedGammaTest_mul_exp_neg_half_of_pos (by omega)]; ring
  -- the weighted functional
  set S : ℝ → ℝ := fun L => ∑' j, w j * (weilPoleWeightFunctional β lam
    (EF.weilTest (fun u => (truncTest (F j) L u : ℂ)) fun u => (truncTest (F j) L u : ℂ))).re
    with hS
  have hSnn : ∀ L, 0 ≤ S L := fun L => tsum_nonneg fun j =>
    mul_nonneg (hw j) (hpos _ (contDiff_ofReal_truncTest (hF j).1 L)
      (hasCompactSupport_truncTest (F j) L))
  have hsplit : ∀ L, S L =
      (∑' j, w j * (zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
        (fun u => (truncTest (F j) L u : ℂ))).re) -
      (∑' j, w j * atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
        (crossCorr (truncTest (F j) L) (truncTest (F j) L))) +
      (β - 1) * ∑' j, w j * (2 * (a j L * b j L)) := by
    intro L
    have sW : Summable fun j => w j * (zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
        (fun u => (truncTest (F j) L u : ℂ))).re :=
      Summable.of_norm_bounded (hsum.mul_right _) fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j), mul_assoc]
        exact mul_le_mul_of_nonneg_left (abs_re_W_truncTest_le hδ (hF j) hΛ hΛ0 (hzero j) L)
          (hw j)
    have sP : Summable fun j => w j *
        atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
          (crossCorr (truncTest (F j) L) (truncTest (F j) L)) :=
      Summable.of_norm_bounded (hsum.mul_right (primeSideConst (1 / 4) Λc A)) fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j), mul_assoc]
        exact mul_le_mul_of_nonneg_left (abs_atomPairing_truncTest_le hδ (hF j) hΛ0 hΛ hA L)
          (hw j)
    have sQ : Summable fun j => w j * (2 * (a j L * b j L)) :=
      Summable.of_norm_bounded (hsum.mul_right (2 * K ^ 2)) fun j => hpole_le j L
    rw [hS, ← sQ.tsum_mul_left, ← sW.tsum_sub sP, ← (sW.sub sP).tsum_add (sQ.mul_left _)]
    refine tsum_congr fun j => ?_
    rw [re_weilPoleWeightFunctional_ofReal β lam (contDiff_ofReal_truncTest (hF j).1 L)
      (contDiff_truncTest (hF j).1 L).continuous (hasCompactSupport_truncTest (F j) L)]
    simp only [ha, hb]
    ring
  have hlim : Tendsto S atTop (𝓝 (0 - 0 + (β - 1) * (w 0 * (1 / 2)))) := by
    have := (h1.sub h2).add (h3.const_mul (β - 1))
    rw [hval] at this
    exact this.congr fun L => (hsplit L).symm
  have hge := ge_of_tendsto hlim (Eventually.of_forall hSnn)
  nlinarith

end RHTower.WeilPoleWeight
