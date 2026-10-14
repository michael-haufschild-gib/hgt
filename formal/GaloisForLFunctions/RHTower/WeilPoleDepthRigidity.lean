import GaloisForLFunctions.RHTower.WeilPoleWeightAboveOneVonMangoldt

/-!
# The pole of the explicit formula is rigid in location and weight

The Weil functional of `ζ` contains the pole term `k̂(i/2) + k̂(−i/2)`, the pole of `ζ` at `s = 1`
seen at depth `½` from the critical line.  The functional with depth `c` and weight `β`
(`weilPoleDepthFunctional β c lam`) removes it and puts `β(k̂(ic) + k̂(−ic))` in its place.

**Theorem** (`not_forall_re_weilPoleDepthFunctional_vonMangoldt_nonneg`).  If `|c| < 3/4` and
`c² ≠ ¼`, then for every `β` the functional with weights `Λ` is negative on the autocorrelation of
some real `C²` compactly supported test.  Unconditional.

**Corollary** (`sq_eq_and_eq_one_of_forall_re_weilPoleDepthFunctional_vonMangoldt_nonneg`).  If the
functional with weights `Λ`, depth `c` (`|c| < 3/4`) and weight `β` is nonnegative on every such
autocorrelation, then `c² = ¼` and `β = 1`: the true pole is the only one compatible with Weil
positivity of `Λ`.

Proof.  Take the strip test `F` with transform `Ξ(z)(z² + c²)` (`depthNullSymbol`), in the
shifted-Gamma basis `z² + c² = −4Q₂(z) + 6Q₁(z) + (c² − ¼)`.
* `F̂` vanishes at every zero of `ζ`, so the zeta sides of its truncations tend to `0`, and the prime
  deviation of `Λ` from itself is `0`.
* `F̂(ic) = Ξ(ic)·0 = 0`, so the new pole term `2F̂(ic)F̂(−ic)` tends to `0` for every `β`.
* `F̂(±i/2) = Ξ(±i/2)(c² − ¼) = ½(c² − ¼)`, so the removed pole term tends to `½(c² − ¼)² > 0`.
So the functionals of the truncations tend to `−½(c² − ¼)² < 0`.  At `c = ±½` the functional is the
pole-weight functional, and `β = 1` is forced by the cases `β < 1` and `β > 1`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.WeilPoleWeight

open WeilSpectral

/-- The Weil functional with the pole of `ζ` removed and a pole of weight `β` placed at depth `c`. -/
def weilPoleDepthFunctional (β c : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  weilPoleWeightFunctional 0 lam k + (β : ℂ) * (paperFT k ((c : ℂ) * I) + paperFT k (-((c : ℂ) * I)))

theorem paperFT_ofRealFun_mul_I (f : ℝ → ℝ) (c : ℝ) :
    paperFT (fun u => (f u : ℂ)) ((c : ℂ) * I) = ((∫ u, f u * Real.exp (-(c * u)) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : I * ((c : ℂ) * I) * (u : ℂ) = ((-(c * u) : ℝ) : ℂ) := by
    rw [mul_comm (c : ℂ) I, ← mul_assoc, Complex.I_mul_I]; push_cast; ring
  simp only [e, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

theorem paperFT_ofRealFun_neg_mul_I (f : ℝ → ℝ) (c : ℝ) :
    paperFT (fun u => (f u : ℂ)) (-((c : ℂ) * I)) = ((∫ u, f u * Real.exp (c * u) : ℝ) : ℂ) := by
  have h := paperFT_ofRealFun_mul_I f (-c)
  rw [show ((-c : ℝ) : ℂ) * I = -((c : ℂ) * I) by push_cast; ring] at h
  rw [h]
  simp only [neg_mul, neg_neg]

/-- The pole term at depth `c` of a real autocorrelation:
`Re(k̂(ic) + k̂(−ic)) = 2 (∫ F e^{−cu}) (∫ F e^{cu})`. -/
theorem re_poleDepth_weilTest_ofReal {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (c : ℝ) :
    (paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) ((c : ℂ) * I) +
      paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (-((c : ℂ) * I))).re =
      2 * ((∫ u, F u * Real.exp (-(c * u))) * ∫ u, F u * Real.exp (c * u)) := by
  have hc : Continuous (fun u => (F u : ℂ)) := Complex.continuous_ofReal.comp hF
  have hcc : HasCompactSupport (fun u => (F u : ℂ)) := hFc.comp_left Complex.ofReal_zero
  have e1 : (starRingEnd ℂ) ((c : ℂ) * I) = -((c : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have e2 : (starRingEnd ℂ) (-((c : ℂ) * I)) = (c : ℂ) * I := by
    rw [map_neg, e1, neg_neg]
  rw [EF.paperFT_weilTest hc hc hcc hcc, EF.paperFT_weilTest hc hc hcc hcc, e1, e2,
    paperFT_ofRealFun_mul_I, paperFT_ofRealFun_neg_mul_I]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The depth functional on a real autocorrelation: zeta side, prime deviation, removed pole of `ζ`
and the new pole. -/
theorem re_weilPoleDepthFunctional_ofReal (β c : ℝ) (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFr : Continuous F) (hFc : HasCompactSupport F) :
    (weilPoleDepthFunctional β c lam (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re =
      (zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)).re -
        atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) (crossCorr F F) -
        2 * ((∫ u, F u * Real.exp (-u / 2)) * ∫ u, F u * Real.exp (u / 2)) +
        β * (2 * ((∫ u, F u * Real.exp (-(c * u))) * ∫ u, F u * Real.exp (c * u))) := by
  rw [weilPoleDepthFunctional, Complex.add_re, re_weilPoleWeightFunctional_ofReal 0 lam hF hFr hFc,
    Complex.re_ofReal_mul, re_poleDepth_weilTest_ofReal hFr hFc]
  ring

/-- At depth `±½` the depth functional is the pole-weight functional. -/
theorem weilPoleDepthFunctional_eq_of_sq_eq (β : ℝ) {c : ℝ} (hc : c ^ 2 = 1 / 4) (lam : ℕ → ℝ)
    (k : ℝ → ℂ) : weilPoleDepthFunctional β c lam k = weilPoleWeightFunctional β lam k := by
  have hpole : paperFT k ((c : ℂ) * I) + paperFT k (-((c : ℂ) * I)) =
      paperFT k (I / 2) + paperFT k (-I / 2) := by
    have h' : (c - 1 / 2) * (c + 1 / 2) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp h' with h | h
    · rw [show c = 1 / 2 by linarith]
      congr 2 <;> push_cast <;> ring
    · rw [show c = -(1 / 2) by linarith, add_comm]
      congr 2 <;> push_cast <;> ring
  unfold weilPoleDepthFunctional weilPoleWeightFunctional
  rw [hpole]
  push_cast
  ring

/-! ### Exponential moments of the truncations at every depth below the decay rate -/

theorem abs_mul_exp_le_of_decayBound_rate {F : ℝ → ℝ} {δ C : ℝ} (hF : DecayBound F δ C) (c u : ℝ) :
    |F u * Real.exp (c * u)| ≤ C * Real.exp (-((1 / 2 + δ - |c|) * |u|)) := by
  have h1 := (hF.2.2 u).1
  have hcu : c * u ≤ |c| * |u| := (le_abs_self _).trans (abs_mul c u).le
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |F u| * Real.exp (c * u) ≤ C * Real.exp (-((1 / 2 + δ) * |u|)) * Real.exp (|c| * |u|) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr hcu) (Real.exp_pos _).le (le_trans (abs_nonneg _) h1)
    _ = C * Real.exp (-((1 / 2 + δ - |c|) * |u|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem tendsto_integral_truncTest_mul_exp_of_lt {F : ℝ → ℝ} {δ C : ℝ} (hF : DecayBound F δ C)
    {c : ℝ} (hc : |c| < 1 / 2 + δ) :
    Tendsto (fun L => ∫ u, truncTest F L u * Real.exp (c * u)) atTop
      (𝓝 (∫ u, F u * Real.exp (c * u))) := by
  have hη : 0 < 1 / 2 + δ - |c| := by linarith
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => C * Real.exp (-((1 / 2 + δ - |c|) * |u|)))
    (Eventually.of_forall fun L => ?_) (Eventually.of_forall fun L => ?_)
    ((integrable_exp_neg_mul_abs_fam hη).const_mul C) (Eventually.of_forall fun u => ?_)
  · exact (((contDiff_truncTest hF.1 L).continuous).mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs]
    have h := abs_mul_exp_le_of_decayBound_rate hF c u
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h ⊢
    exact (mul_le_mul_of_nonneg_right (abs_truncTest_le F L u) (Real.exp_pos _).le).trans h
  · refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨|u| + 1, fun L hL => ?_⟩)
    show F u * Real.exp (c * u) = truncTest F L u * Real.exp (c * u)
    rw [truncTest_eq_self (by linarith)]

/-! ### The depth null test -/

/-- The null multiplier `Ξ(z)(z² + c²)` in the shifted-Gamma basis. -/
def depthNullSymbol (c : ℝ) (z : ℂ) : ℂ :=
  -4 * xiShiftedGamma 2 z + 6 * xiShiftedGamma 1 z + ((c ^ 2 - 1 / 4 : ℝ) : ℂ) * xiShiftedGamma 0 z

/-- The depth null test, the strip test of `depthNullSymbol c`. -/
def depthNullTest (c : ℝ) : ℝ → ℝ := stripTest (depthNullSymbol c)

theorem depthNullSymbol_eq (c : ℝ) (z : ℂ) :
    depthNullSymbol c z = RHTower.XiC z * (z ^ 2 + (c : ℂ) ^ 2) := by
  simp only [depthNullSymbol, xiShiftedGamma, shiftedGammaPoly, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, Nat.cast_zero, Nat.cast_one]
  push_cast
  linear_combination (-(RHTower.XiC z * z ^ 2)) * Complex.I_sq

theorem exists_stripDecay_depthNullSymbol (c : ℝ) :
    ∃ C : ℝ, StripDecay (depthNullSymbol c) (3 / 4) xiShiftedGammaRate C := by
  obtain ⟨C, hC, hj⟩ := exists_stripDecay_xiShiftedGamma
  set C₂ := C * ((2 ! : ℝ) * (3 / 2 : ℝ) ^ 2) with hC₂
  set C₁ := C * ((1 ! : ℝ) * (3 / 2 : ℝ) ^ 1) with hC₁
  set C₀ := C * ((0 ! : ℝ) * (3 / 2 : ℝ) ^ 0) with hC₀
  set t : ℝ := c ^ 2 - 1 / 4 with ht
  refine ⟨4 * C₂ + 6 * C₁ + |t| * C₀, fun z hz => ?_, fun z hz => ?_⟩
  · exact (((differentiableAt_const _).mul ((hj 2).diff z hz)).add
      ((differentiableAt_const _).mul ((hj 1).diff z hz))).add
      ((differentiableAt_const _).mul ((hj 0).diff z hz))
  · have h2 := (hj 2).bound z hz
    have h1 := (hj 1).bound z hz
    have h0 := (hj 0).bound z hz
    set E := Real.exp (-(xiShiftedGammaRate * |z.re|)) with hE
    unfold depthNullSymbol
    calc ‖-4 * xiShiftedGamma 2 z + 6 * xiShiftedGamma 1 z + (t : ℂ) * xiShiftedGamma 0 z‖
        ≤ ‖-4 * xiShiftedGamma 2 z‖ + ‖6 * xiShiftedGamma 1 z‖ +
            ‖(t : ℂ) * xiShiftedGamma 0 z‖ := norm_add₃_le
      _ = 4 * ‖xiShiftedGamma 2 z‖ + 6 * ‖xiShiftedGamma 1 z‖ + |t| * ‖xiShiftedGamma 0 z‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
          norm_num
      _ ≤ 4 * (C₂ * E) + 6 * (C₁ * E) + |t| * (C₀ * E) := by gcongr
      _ = (4 * C₂ + 6 * C₁ + |t| * C₀) * E := by ring

theorem depthNullSymbol_neg_ofReal (c r : ℝ) :
    depthNullSymbol c (-(r : ℂ)) = conj (depthNullSymbol c r) := by
  unfold depthNullSymbol
  rw [xiShiftedGamma_neg_ofReal 2, xiShiftedGamma_neg_ofReal 1, xiShiftedGamma_neg_ofReal 0]
  simp only [map_add, map_mul, map_neg, Complex.conj_ofReal, map_ofNat]

theorem exists_decayBound_depthNullTest (c : ℝ) :
    ∃ C : ℝ, DecayBound (depthNullTest c) (1 / 4) C := by
  obtain ⟨C, hC⟩ := exists_stripDecay_depthNullSymbol c
  have h := decayBound_stripTest (by norm_num : (1 / 2 : ℝ) < 3 / 4) xiShiftedGammaRate_pos hC
  rw [show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num] at h
  exact ⟨_, h⟩

theorem paperFT_depthNullTest (c : ℝ) {z : ℂ} (hz : |z.im| < 3 / 4) :
    paperFT (fun u => (depthNullTest c u : ℂ)) z = depthNullSymbol c z := by
  obtain ⟨C, hC⟩ := exists_stripDecay_depthNullSymbol c
  exact paperFT_stripTest (by norm_num) xiShiftedGammaRate_pos hC (depthNullSymbol_neg_ofReal c) hz

/-- The depth null test vanishes at every zero of `ζ`. -/
theorem paperFT_depthNullTest_gammaOf (c : ℝ) (ρ : zetaZeroConfig.carrier) :
    paperFT (fun u => (depthNullTest c u : ℂ)) (gammaOf ρ) = 0 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(gammaOf (ρ : ℂ)).im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have h34 : |(gammaOf (ρ : ℂ)).im| < 3 / 4 := by linarith
  rw [paperFT_depthNullTest c h34]
  unfold depthNullSymbol
  rw [← paperFT_xiShiftedGammaTest 2 h34, ← paperFT_xiShiftedGammaTest 1 h34,
    ← paperFT_xiShiftedGammaTest 0 h34, paperFT_xiShiftedGammaTest_gammaOf 2 ρ,
    paperFT_xiShiftedGammaTest_gammaOf 1 ρ, paperFT_xiShiftedGammaTest_gammaOf 0 ρ]
  ring

/-- The new pole is invisible to the depth null test: `F̂(ic) = 0`. -/
theorem integral_depthNullTest_mul_exp_neg {c : ℝ} (hc : |c| < 3 / 4) :
    ∫ u, depthNullTest c u * Real.exp (-(c * u)) = 0 := by
  have h := paperFT_ofRealFun_mul_I (depthNullTest c) c
  rw [paperFT_depthNullTest c (by simpa using hc), depthNullSymbol_eq] at h
  have e : ((c : ℂ) * I) ^ 2 + (c : ℂ) ^ 2 = 0 := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [e, mul_zero] at h
  exact_mod_cast h.symm

theorem integral_depthNullTest_mul_exp_neg_half (c : ℝ) :
    ∫ u, depthNullTest c u * Real.exp (-u / 2) = (c ^ 2 - 1 / 4) / 2 := by
  have h := paperFT_ofRealFun_I_div_two (depthNullTest c)
  rw [paperFT_depthNullTest c (by simp; norm_num), depthNullSymbol_eq, RHTower.XiC,
    show (1 / 2 : ℂ) + I / 2 * I = 0 by rw [mul_comm, ← mul_div_assoc, Complex.I_mul_I]; ring,
    xi_zero_eq_half, div_pow, Complex.I_sq] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re] at this
  rw [← this]
  simp only [Complex.mul_re, Complex.add_re, Complex.div_re, Complex.neg_re, Complex.one_re]
  norm_num [← Complex.ofReal_pow]
  ring

theorem integral_depthNullTest_mul_exp_half (c : ℝ) :
    ∫ u, depthNullTest c u * Real.exp (u / 2) = (c ^ 2 - 1 / 4) / 2 := by
  have h := paperFT_ofRealFun_neg_I_div_two (depthNullTest c)
  rw [paperFT_depthNullTest c (by simp; norm_num), depthNullSymbol_eq, RHTower.XiC,
    show (1 / 2 : ℂ) + -I / 2 * I = 1 by
      rw [mul_comm, ← mul_div_assoc, mul_neg, Complex.I_mul_I]; ring, xi_one, div_pow, neg_sq,
    Complex.I_sq] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re] at this
  rw [← this]
  simp only [Complex.mul_re, Complex.add_re, Complex.div_re, Complex.neg_re, Complex.one_re]
  norm_num [← Complex.ofReal_pow]
  ring

/-! ### The theorems -/

/-- **Off depth `½` the pole is never compatible with `Λ`.**  For `|c| < 3/4` with `c² ≠ ¼` and
every weight `β`, the functional with the pole moved to depth `c` and weights `Λ` is negative on
some real autocorrelation. -/
theorem not_forall_re_weilPoleDepthFunctional_vonMangoldt_nonneg {β c : ℝ} (hc : |c| < 3 / 4)
    (hc2 : c ^ 2 ≠ 1 / 4) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleDepthFunctional β c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re := by
  intro hpos
  obtain ⟨C, hF⟩ := exists_decayBound_depthNullTest c
  set F := depthNullTest c with hFdef
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  -- the zeta side of the truncations tends to `0` (one-member family)
  set w : ℕ → ℝ := fun j => if j = 0 then 1 else 0 with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => by simp only [hw]; split_ifs <;> norm_num
  have hsum : Summable fun j => w j * C ^ 2 :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hw, hj]
  have h1 := tendsto_tsum_W_truncTest (F := fun _ => F) (C := fun _ => C) hδ (fun _ => hF) hw0
    hsum hΛ0 hΛ (fun _ ρ => paperFT_depthNullTest_gammaOf c ρ)
  have hsingle : ∀ L : ℝ, (∑' j, w j * (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ))
      (fun u => (truncTest F L u : ℂ))).re) =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re := by
    intro L
    rw [tsum_eq_single 0 fun j hj => by simp [hw, hj]]
    simp [hw]
  simp_rw [hsingle] at h1
  -- the removed pole of `ζ`
  have hneg : ∀ u : ℝ, -u / 2 = (-1 / 2 : ℝ) * u := fun u => by ring
  have hpos2 : ∀ u : ℝ, u / 2 = (1 / 2 : ℝ) * u := fun u => by ring
  have ta := tendsto_integral_truncTest_mul_exp hδ hF (c := -1 / 2) (by norm_num [abs_of_neg])
  have tb := tendsto_integral_truncTest_mul_exp hδ hF (c := 1 / 2) (by norm_num)
  simp_rw [← hneg] at ta
  simp_rw [← hpos2] at tb
  have h3 := (ta.mul tb).const_mul 2
  rw [integral_depthNullTest_mul_exp_neg_half, integral_depthNullTest_mul_exp_half] at h3
  -- the new pole at depth `c`
  have hc' : |c| < 1 / 2 + 1 / 4 := by linarith
  have tc := tendsto_integral_truncTest_mul_exp_of_lt hF (c := -c) (by rwa [abs_neg])
  have td := tendsto_integral_truncTest_mul_exp_of_lt hF hc'
  simp_rw [neg_mul] at tc
  have h4 := ((tc.mul td).const_mul 2).const_mul β
  rw [integral_depthNullTest_mul_exp_neg hc] at h4
  -- the functional on the truncations
  set S : ℝ → ℝ := fun L => (weilPoleDepthFunctional β c
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re with hS
  have hSnn : ∀ L, 0 ≤ S L := fun L =>
    hpos _ (contDiff_ofReal_truncTest hF.1 L) (hasCompactSupport_truncTest F L)
  have hsplit : ∀ L, S L =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re -
        2 * ((∫ u, truncTest F L u * Real.exp (-u / 2)) * ∫ u, truncTest F L u * Real.exp (u / 2)) +
        β * (2 * ((∫ u, truncTest F L u * Real.exp (-(c * u))) *
          ∫ u, truncTest F L u * Real.exp (c * u))) := by
    intro L
    show (weilPoleDepthFunctional β c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re = _
    rw [re_weilPoleDepthFunctional_ofReal β c _ (contDiff_ofReal_truncTest hF.1 L)
      (contDiff_truncTest hF.1 L).continuous (hasCompactSupport_truncTest F L)]
    simp only [sub_self, atomPairing_zero, sub_zero]
  have hlim : Tendsto S atTop (𝓝 (0 - 2 * ((c ^ 2 - 1 / 4) / 2 * ((c ^ 2 - 1 / 4) / 2)) +
      β * (2 * (0 * ∫ u, F u * Real.exp (c * u))))) :=
    ((h1.sub h3).add h4).congr fun L => (hsplit L).symm
  have hge := ge_of_tendsto hlim (Eventually.of_forall hSnn)
  have ht : c ^ 2 - 1 / 4 ≠ 0 := sub_ne_zero.mpr hc2
  have htt : 0 < (c ^ 2 - 1 / 4) ^ 2 := by positivity
  nlinarith

/-- **Rigidity of the pole.**  If the functional with weights `Λ`, the pole of `ζ` replaced by a
pole of weight `β` at depth `c`, `|c| < 3/4`, is nonnegative on every real `C²` compactly supported
autocorrelation, then `c = ±½` and `β = 1`. -/
theorem sq_eq_and_eq_one_of_forall_re_weilPoleDepthFunctional_vonMangoldt_nonneg {β c : ℝ}
    (hc : |c| < 3 / 4)
    (hpos : ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleDepthFunctional β c (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re) :
    c ^ 2 = 1 / 4 ∧ β = 1 := by
  by_contra hne
  have hc2 : c ^ 2 = 1 / 4 := by
    by_contra h2
    exact not_forall_re_weilPoleDepthFunctional_vonMangoldt_nonneg hc h2 hpos
  have hβ : β ≠ 1 := fun h => hne ⟨hc2, h⟩
  simp_rw [weilPoleDepthFunctional_eq_of_sq_eq β hc2] at hpos
  rcases lt_or_gt_of_ne hβ with h | h
  · refine not_forall_re_weilPoleWeightFunctional_nonneg h (A := 0) (fun N => ?_) hpos
    simp [primeWeightPartialSum]
  · exact not_forall_re_weilPoleWeightFunctional_vonMangoldt_nonneg_of_one_lt h hpos

end RHTower.WeilPoleWeight
