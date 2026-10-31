import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.STruncatedExplicitTowers
import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.InterTowerCouplingRigidity
import GaloisForLFunctions.AdelicKreinGeometry.TheGluingSquareIsSharp
import GaloisForLFunctions.ArithmeticPositiveDuality.PositivityOnBothSidesOfTheExplicitFormula

/-!
# Coupled `S`-tower signature formulas and window-coupled explicit-formula exhaustion

Separable `S`-truncated explicit-formula prime-tower assemblies `K_S = Σ_{p ∈ S} k_p^{(S)}(v_p(·))`
fail unconditionally to compute `κ(K_ζ) + 1` (`STruncatedExplicitTowers`), and arbitrary separable
prime-tower assemblies cannot even converge pointwise to `ratCorr` (`InterTowerCouplingRigidity`).
Retaining non-separable inter-tower coupling restores exact local-to-global signature formulas in
both the valuation-retraction sense and the `S`-truncated explicit-formula sense:

* **Coupled `S`-tower signature formula** (`negIndex_coupledAssembly_orbitCorr`,
  `negIndex_archGlue_coupledAssembly_orbitCorr`, `negIndex_archGlue_coupledAssembly_ratCorr`,
  `tendsto_coupledAssembly_atTop`): for every `S : Finset Nat.Primes` with `2 ≤ S.card` and every
  `c > 0`, `coupledAssembly S ratCorr = ratCorr ∘ projS S` converges pointwise to `ratCorr` along
  `atTop` and already has exact glued index
    `κ(archGlue(coupledAssembly S ratCorr, c)) = κ(K_ζ) + 1 = κ(weilArchState c)`.
* **Global fixed-`S` explicit-formula dichotomy** (`negIndex_archGlue_sTruncatedCorr_mem`,
  `not_tendsto_negIndex_archGlue_sTruncatedCorr_of_finite_pos`): evaluating the `S`-truncated
  explicit formula (primes in `S`, Gamma, pole, zero counterterm) on all of `ℚ_{>0}` gives
  `sTruncatedCorr S`. At unbounded slope height for fixed `S`, its non-pole part mixes to `0` along
  `2^ℕ` while its pole part is absorbed by `negIndex_archGlue_add_polePair`, forcing
  `κ(archGlue(sTruncatedCorr S, c)) ∈ {1, ⊤}`.
* **Window-coupled zero-counterterm explicit-formula signature formula**
  (`sTruncatedCorr_eq_ratCorr_of_abs_logPos_le`, `gram_archGlue_sTruncatedCorr_eq_weilArchState`,
  `tendsto_archGlue_sTruncatedCorr_atTop`, `negIndex_weilArchState_eq_iSup_windowPrimes`):
  because the cubic-spline test autocorrelation has support in `[-8, 8]`, whenever a finite family
  `g : Fin n → AffineGroupQ` has slope heights `|log |slope(g_i)|| ≤ L` and `S` contains
  `windowPrimes L` (all primes `≤ ⌊exp(2L + 8)⌋₊`), the glued Gram matrix of `sTruncatedCorr S`
  equals `gram (weilArchState c) g` entrywise. Consequently `archGlue (sTruncatedCorr S) c`
  converges pointwise to `weilArchState c` along `atTop` and the window-coupled supremum over
  `(L, S_L)` equals `κ(K_ζ) + 1` unconditionally.
-/

open Complex Finset Filter Topology MeasureTheory
open scoped ComplexConjugate Real
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx cx_contDiff cx_hasCompactSupport
  DenseShifts realTests rightZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros seenRightZeros_cubicSpline)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

/-! ### Positive Survivor 1: Coupled `S`-valuation assembly -/

theorem denseShifts_projS {S : Finset Nat.Primes} (hS : 2 ≤ S.card) :
    DenseShifts (Set.range fun u : posUnits =>
      scale heckeLogScale (posUnitsToHecke (projS S u))) := by
  classical
  obtain ⟨p, hp⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq_er⟩ : (S.erase p).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hp]; omega)
  obtain ⟨hqp, hq⟩ := mem_erase.mp hq_er
  have hpq_nat : (p : ℕ) ≠ (q : ℕ) := fun h => hqp (Subtype.ext h).symm
  have hd2 := denseShifts_twoPrimeLattice p.2 q.2 hpq_nat
  intro v hv ε hε
  obtain ⟨d, ⟨h, rfl⟩, hdv⟩ := hd2 v hv ε hε
  obtain ⟨m, n, hmn⟩ := Subgroup.mem_closure_pair.mp h.2
  refine ⟨scale heckeLogScale ((twoPrimeLattice p.2 q.2).subtype h), ?_, hdv⟩
  refine ⟨primeUnit p ^ m * primeUnit q ^ n, ?_⟩
  have hproj : projS S (primeUnit p ^ m * primeUnit q ^ n) = primeUnit p ^ m * primeUnit q ^ n := by
    rw [map_mul, projS_primeUnit_zpow hp, projS_primeUnit_zpow hq]
  have hhecke : posUnitsToHecke (primeUnit p ^ m * primeUnit q ^ n) =
      (twoPrimeLattice p.2 q.2).subtype h := by
    rw [map_mul, map_zpow, map_zpow, posUnitsToHecke_primeUnit, posUnitsToHecke_primeUnit]
    exact hmn
  rw [hproj, hhecke]

/-- **Coupled `S`-tower index of any tempered orbit kernel.** Every finite prime set of cardinality
at least `2` carries the full negative index of `orbitCorr Z f`. -/
theorem negIndex_coupledAssembly_orbitCorr (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {S : Finset Nat.Primes} (hS : 2 ≤ S.card) :
    negIndex (coupledAssembly S (orbitCorr Z f)) = (seenRightZeros Z f).encard := by
  have heq : coupledAssembly S (orbitCorr Z f) =
      orbitKernel Z f ∘ (posUnitsToHecke.comp (projS S)) := rfl
  rw [heq]
  exact negIndex_orbitKernel_comp Z hZ hf (posUnitsToHecke.comp (projS S)) (denseShifts_projS hS)

/-- **Glued coupled `S`-tower signature formula for tempered orbit kernels.** Because `projS S` is
invariant under any prime outside `S`, gluing `coupledAssembly S (orbitCorr Z f)` to the
archimedean successor costs exactly one square for every `S` with `2 ≤ S.card` and `c > 0`. -/
theorem negIndex_archGlue_coupledAssembly_orbitCorr (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {f : ℝ → ℝ} (hf : f ∈ realTests) {S : Finset Nat.Primes} (hS : 2 ≤ S.card) {c : ℝ}
    (hc : 0 < c) :
    negIndex (archGlue (coupledAssembly S (orbitCorr Z f)) c) =
      (seenRightZeros Z f).encard + 1 := by
  have hK : IsHermKernel (coupledAssembly S (orbitCorr Z f)) :=
    isHermKernel_coupledAssembly S ((isHermKernel_orbitKernel Z f).comp _)
  obtain ⟨v₀, hv₀, hper_proj⟩ := projS_periodic S
  have hper : ∀ u, coupledAssembly S (orbitCorr Z f) (v₀ * u) =
      coupledAssembly S (orbitCorr Z f) u := fun u => by
    simp only [coupledAssembly, Function.comp_apply, hper_proj]
  rw [negIndex_archGlue_eq_of_periodic hK hv₀ hper hc,
    negIndex_coupledAssembly_orbitCorr Z hZ hf hS]

/-- **Exact coupled `S`-tower signature formula for `ζ`.** For every `S : Finset Nat.Primes` with
`2 ≤ S.card` and `c > 0`, `coupledAssembly S ratCorr` has exact glued negative index
`κ(K_ζ) + 1 = κ(weilArchState c)`. -/
theorem negIndex_archGlue_coupledAssembly_ratCorr {S : Finset Nat.Primes} (hS : 2 ≤ S.card)
    {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (coupledAssembly S ratCorr) c) = negIndex zetaKernel + 1 ∧
      negIndex (archGlue (coupledAssembly S ratCorr) c) = negIndex (weilArchState c) := by
  have h1 : negIndex (archGlue (coupledAssembly S ratCorr) c) = negIndex zetaKernel + 1 := by
    rw [ratCorr_eq_orbitCorr,
      negIndex_archGlue_coupledAssembly_orbitCorr zetaZeroConfig temperedConfig_zetaZeroConfig
        cubicSpline_mem_realTests hS hc,
      zetaKernel, negIndex_orbitKernel _ temperedConfig_zetaZeroConfig cubicSpline_mem_realTests]
  exact ⟨h1, h1.trans (negIndex_weilArchState_eq_add_one hc).symm⟩

/-- **Exact coupled `S`-tower signature formula for primitive Dirichlet `L`-functions.** -/
theorem negIndex_archGlue_coupledAssembly_dirichlet {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) {S : Finset Nat.Primes} (hS : 2 ≤ S.card) {c : ℝ}
    (hc : 0 < c) :
    negIndex (archGlue
      (coupledAssembly S (orbitCorr (ThmE.LZeros (ThmE.LSeam_of hq hprim)) cubicSpline)) c) =
      {ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier | 1 / 2 < ρ.re}.encard + 1 := by
  rw [negIndex_archGlue_coupledAssembly_orbitCorr _
    (SquareRootThreshold.temperedConfig_LZeros hq hprim) cubicSpline_mem_realTests hS hc,
    seenRightZeros_cubicSpline]

/-- Every `coupledAssembly S K` is eventually constant at each `u ∈ ℚ_{>0}`, hence converges
pointwise to `K` along `atTop`. -/
theorem tendsto_coupledAssembly_atTop (K : posUnits → ℂ) (u : posUnits) :
    Tendsto (fun S : Finset Nat.Primes => coupledAssembly S K u) atTop (𝓝 (K u)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (primeSupp ((u : ℚˣ) : ℚ))] with S hS
  simp only [coupledAssembly, Function.comp_apply, projS_eq_self_of_primeSupp_subset hS]

theorem tendsto_archGlue_coupledAssembly_atTop (K : posUnits → ℂ) (c : ℝ) (g : AffineGroupQ) :
    Tendsto (fun S : Finset Nat.Primes => archGlue (coupledAssembly S K) c g)
      atTop (𝓝 (archGlue K c g)) :=
  (tendsto_coupledAssembly_atTop K (slopeAbs g)).add tendsto_const_nhds

/-! ### Global fixed-`S` non-separable explicit-formula correlation and `{1, ⊤}` dichotomy -/

/-- The global `S`-truncated explicit-formula correlation on `ℚ_{>0}` (primes in `S`, Gamma, pole,
zero counterterm) for the cubic spline. -/
def sTruncatedCorr (S : Finset Nat.Primes) (u : posUnits) : ℂ :=
  RHTower.weilFullFunctional (vonMangoldtS S)
    (EF.weilTest (ArithmeticCastelnuovoSeveri.translate (-logPos u) (cx cubicSpline))
      (cx cubicSpline))

/-- The non-pole part (`−primePart_S + archPart`) of `sTruncatedCorr S` on `ℚ_{>0}`. -/
def sTruncatedCorrNonPole (S : Finset Nat.Primes) (u : posUnits) : ℂ :=
  -RHTower.WeilSpectral.primePart (vonMangoldtS S)
      (RHTower.WeilSpectral.transl (-logPos u) (EF.weilTest (cx cubicSpline) (cx cubicSpline))) +
    RHTower.WeilSpectral.archPart
      (RHTower.WeilSpectral.transl (-logPos u) (EF.weilTest (cx cubicSpline) (cx cubicSpline)))

private theorem poleWeight_cx_im_eq_zero (f : ℝ → ℝ) :
    (poleWeight (cx f)).im = 0 := by
  have hreal : ∀ x : ℝ, EF.weilTest (cx f) (cx f) x = ((∫ t : ℝ, f t * f (t - x) : ℝ) : ℂ) := by
    intro x
    rw [RHTower.WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [cx]
  have hft : poleWeight (cx f) =
      ((∫ x : ℝ, (∫ t : ℝ, f t * f (t - x)) * Real.exp (-x / 2) : ℝ) : ℂ) := by
    rw [poleWeight, paperFT, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hexp : I * (I / 2) * (x : ℂ) = ((-x / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [hreal x, hexp, ← Complex.ofReal_exp, Complex.ofReal_mul]
  rw [hft, Complex.ofReal_im]

private theorem polePart_transl_weilTest_cx (f : ℝ → ℝ) (u : posUnits) :
    RHTower.WeilSpectral.polePart
        (RHTower.WeilSpectral.transl (-logPos u) (EF.weilTest (cx f) (cx f))) =
      ((poleWeight (cx f)).re : ℂ) * polePair u := by
  have him := poleWeight_cx_im_eq_zero f
  have hpw : poleWeight (cx f) = ((poleWeight (cx f)).re : ℂ) :=
    Complex.ext rfl (by simp [him])
  have htilde : paperFT (EF.weilTest (cx f) (cx f)) (-I / 2) = ((poleWeight (cx f)).re : ℂ) := by
    have hc : conj (-I / 2) = I / 2 := by rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
    conv_lhs => rw [← RHTower.WeilSpectral.tilde_weilTest_self (cx f)]
    rw [EF.paperFT_tilde, hc, ← poleWeight, hpw, Complex.conj_ofReal]
  have he1 : I * (I / 2) * ((-logPos u : ℝ) : ℂ) = ((logPos u / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have he2 : I * (-I / 2) * ((-logPos u : ℝ) : ℂ) = ((-logPos u / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hpp : polePair u =
      ((Real.exp (logPos u / 2) + Real.exp (-logPos u / 2) : ℝ) : ℂ) := by
    have hu := posUnits_val_pos u
    have hrp : ((((u : ℚˣ) : ℚ) : ℝ)) ^ (1 / 2 : ℝ) = Real.exp (logPos u / 2) := by
      rw [Real.rpow_def_of_pos hu, logPos]; congr 1; ring
    rw [polePair, hrp, ← Real.exp_neg]
  rw [RHTower.WeilSpectral.polePart, RHTower.WeilSpectral.paperFT_transl,
    RHTower.WeilSpectral.paperFT_transl, ← poleWeight, hpw, htilde, he1, he2,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp, hpp]
  push_cast
  ring

theorem sTruncatedCorr_eq_nonPole_add_polePair (S : Finset Nat.Primes) (u : posUnits) :
    sTruncatedCorr S u =
      sTruncatedCorrNonPole S u + ((poleWeight (cx cubicSpline)).re : ℂ) * polePair u := by
  rw [sTruncatedCorr, weilTest_translate_eq_transl, RHTower.WeilSpectral.weilFullFunctional_eq_parts,
    polePart_transl_weilTest_cx, sTruncatedCorrNonPole]
  ring

theorem logPos_inv (u : posUnits) : logPos u⁻¹ = -logPos u := by
  simp only [logPos, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  push_cast
  exact Real.log_inv _

theorem isHermKernel_sTruncatedCorr (S : Finset Nat.Primes) :
    IsHermKernel (sTruncatedCorr S) := fun u => by
  show sTruncatedCorr S u⁻¹ = conj (sTruncatedCorr S u)
  set K : ℝ → ℂ := EF.weilTest (cx cubicSpline) (cx cubicSpline)
  have htilde : EF.tilde (RHTower.WeilSpectral.transl (-logPos u) K) =
      RHTower.WeilSpectral.transl (logPos u) K := by
    funext x
    have h := congrFun (RHTower.WeilSpectral.tilde_weilTest_self (cx cubicSpline)) (x - logPos u)
    simp only [EF.tilde, RHTower.WeilSpectral.transl, K] at h ⊢
    rw [show -x - -logPos u = -(x - logPos u) by ring, h]
  rw [sTruncatedCorr, sTruncatedCorr, weilTest_translate_eq_transl, weilTest_translate_eq_transl,
    logPos_inv, neg_neg, ← RHTower.WeilSpectral.weilFullFunctional_tilde, htilde]

theorem isHermKernel_sTruncatedCorrNonPole (S : Finset Nat.Primes) :
    IsHermKernel (sTruncatedCorrNonPole S) := fun u => by
  show sTruncatedCorrNonPole S u⁻¹ = conj (sTruncatedCorrNonPole S u)
  have h1 := isHermKernel_sTruncatedCorr S u
  have h2 := isHermKernel_polePair u
  rw [sTruncatedCorr_eq_nonPole_add_polePair, sTruncatedCorr_eq_nonPole_add_polePair,
    map_add, map_mul, Complex.conj_ofReal, ← h2] at h1
  linear_combination h1

private theorem tendsto_sTruncatedCorrNonPole_logPos_atTop (S : Finset Nat.Primes) :
    Tendsto (fun y : ℝ =>
      -RHTower.WeilSpectral.primePart (vonMangoldtS S)
          (RHTower.WeilSpectral.transl (-y) (EF.weilTest (cx cubicSpline) (cx cubicSpline))) +
        RHTower.WeilSpectral.archPart
          (RHTower.WeilSpectral.transl (-y) (EF.weilTest (cx cubicSpline) (cx cubicSpline))))
      atTop (𝓝 0) := by
  set K : ℝ → ℂ := EF.weilTest (cx cubicSpline) (cx cubicSpline)
  have hg := cx_contDiff contDiff_cubicSpline
  have hgc := cx_hasCompactSupport hasCompactSupport_cubicSpline
  have hKc : Continuous K := (EF.weilTest_contDiff hg hg.continuous hgc).continuous
  have hKs : HasCompactSupport K := EF.weilTest_hasCompactSupport hgc hgc
  obtain ⟨R, hR⟩ := RHTower.WeilSpectral.exists_abs_bound_of_hasCompactSupport hKs
  obtain ⟨x₀, hx₀⟩ := hKc.norm.exists_forall_ge_of_hasCompactSupport hKs.norm
  set M : ℝ := ‖K x₀‖
  set b : ℕ → ℝ := fun k => (if 2 ≤ k then |vonMangoldtS S k| / Real.sqrt k else 0) * (2 * M)
  have hb : Summable b := (summable_vonMangoldtS_div_sqrt S).mul_right (2 * M)
  set F : ℝ → ℕ → ℂ := fun y k =>
    ((if 2 ≤ k then vonMangoldtS S k / Real.sqrt k else 0 : ℝ) : ℂ) *
      (RHTower.WeilSpectral.transl (-y) K (Real.log k) +
        RHTower.WeilSpectral.transl (-y) K (-Real.log k))
  have hbd : ∀ y k, ‖F y k‖ ≤ b k := fun y k => by
    simp only [F, b, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcoeff : |if 2 ≤ k then vonMangoldtS S k / Real.sqrt k else 0| =
        if 2 ≤ k then |vonMangoldtS S k| / Real.sqrt k else 0 := by
      split_ifs with hk
      · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      · simp
    rw [hcoeff]
    refine mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> positivity)
    have ht1 : ‖RHTower.WeilSpectral.transl (-y) K (Real.log k)‖ ≤ M := hx₀ _
    have ht2 : ‖RHTower.WeilSpectral.transl (-y) K (-Real.log k)‖ ≤ M := hx₀ _
    exact (norm_add_le _ _).trans (by linarith)
  have hlim : ∀ k : ℕ, Tendsto (fun y : ℝ => F y k) atTop (𝓝 0) := fun k => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (|R| + |Real.log k|)] with y hy
    have hzero : ∀ x : ℝ, |R| < |x| → K x = 0 := fun x hx => by
      by_contra hne; linarith [hR x hne, le_abs_self R]
    have h1 : RHTower.WeilSpectral.transl (-y) K (Real.log k) = 0 := by
      refine hzero _ ?_
      have htri := abs_sub_abs_le_abs_sub y (-Real.log k)
      rw [abs_of_pos (by linarith [abs_nonneg R, abs_nonneg (Real.log k)]), abs_neg] at htri
      dsimp only [RHTower.WeilSpectral.transl]
      rw [show Real.log k - -y = y - (-Real.log k) by ring]
      linarith
    have h2 : RHTower.WeilSpectral.transl (-y) K (-Real.log k) = 0 := by
      refine hzero _ ?_
      have htri := abs_sub_abs_le_abs_sub y (Real.log k)
      rw [abs_of_pos (by linarith [abs_nonneg R, abs_nonneg (Real.log k)])] at htri
      dsimp only [RHTower.WeilSpectral.transl]
      rw [show -Real.log k - -y = y - Real.log k by ring]
      linarith
    simp only [F, h1, h2, add_zero, mul_zero]
  have hp_lim : Tendsto (fun y : ℝ => RHTower.WeilSpectral.primePart (vonMangoldtS S)
      (RHTower.WeilSpectral.transl (-y) K)) atTop (𝓝 0) := by
    simpa [F, RHTower.WeilSpectral.primePart] using
      tendsto_tsum_of_dominated_convergence hb hlim (Eventually.of_forall hbd)
  have ha_lim : Tendsto (fun y : ℝ => RHTower.WeilSpectral.archPart
      (RHTower.WeilSpectral.transl (-y) K)) atTop (𝓝 0) := by
    have hconj := (continuous_conj.tendsto 0).comp
      (RHTower.WeilSpectral.tendsto_archPart_transl (k := K))
    rw [map_zero] at hconj
    refine hconj.congr fun y => ?_
    simp only [Function.comp_apply]
    have htilde : EF.tilde (RHTower.WeilSpectral.transl y K) =
        RHTower.WeilSpectral.transl (-y) K := by
      funext x
      have h := congrFun (RHTower.WeilSpectral.tilde_weilTest_self (cx cubicSpline)) (x + y)
      simp only [EF.tilde, RHTower.WeilSpectral.transl, K] at h ⊢
      rw [show -x - y = -(x + y) by ring, show x - -y = x + y by ring, h]
    rw [← htilde]
    unfold RHTower.WeilSpectral.archPart
    have hint : (∫ r : ℝ, paperFT (EF.tilde (RHTower.WeilSpectral.transl y K)) r *
        (EF.gammaBracket r : ℂ)) =
        conj (∫ r : ℝ, paperFT (RHTower.WeilSpectral.transl y K) r *
          (EF.gammaBracket r : ℂ)) := by
      rw [← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [EF.paperFT_tilde, Complex.conj_ofReal, map_mul]
    rw [hint, map_mul, map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
  simpa using hp_lim.neg.add ha_lim

private theorem tendsto_sTruncatedCorrNonPole_twoPos (S : Finset Nat.Primes) (g h : posUnits) :
    Tendsto (fun j : ℕ => sTruncatedCorrNonPole S (g * twoPos ^ j * h)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy : Tendsto (fun j : ℕ => logPos (g * twoPos ^ j * h)) atTop atTop := by
    have heq : (fun j : ℕ => logPos (g * twoPos ^ j * h)) =
        fun j : ℕ => (j : ℝ) * Real.log 2 + (logPos g + logPos h) := funext fun j => by
      have h2 : logPos (twoPos ^ j) = (j : ℝ) * Real.log 2 := by
        simp only [logPos, twoPos_pow_val, Real.log_pow]
      rw [logPos_mul, logPos_mul, h2]; ring
    rw [heq]
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hlog2)
  exact (tendsto_sTruncatedCorrNonPole_logPos_atTop S).comp hy

/-- **Global fixed-`S` explicit-formula `{1, ⊤}` dichotomy.** At unbounded slope height for any
fixed finite prime set `S` and `c > 0`, `κ(archGlue(sTruncatedCorr S, c)) ∈ {1, ⊤}`. -/
theorem negIndex_archGlue_sTruncatedCorr_mem (S : Finset Nat.Primes) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (sTruncatedCorr S) c) ∈ ({1, ⊤} : Set ℕ∞) := by
  have hK := isHermKernel_sTruncatedCorrNonPole S
  have hpole : sTruncatedCorr S = fun u =>
      sTruncatedCorrNonPole S u + ((poleWeight (cx cubicSpline)).re : ℂ) * polePair u :=
    funext (sTruncatedCorr_eq_nonPole_add_polePair S)
  rw [hpole, negIndex_archGlue_add_polePair hK _ hc]
  have hsub : ∀ u : posUnits, Tendsto (fun N : ℕ => sTruncatedCorrNonPole S (twoPos ^ N * u) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    intro u
    have h1 := tendsto_sTruncatedCorrNonPole_twoPos S 1 u
    simp only [one_mul] at h1
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp tendsto_twoPos_pow_rpow
    simpa using h1.mul h2
  rw [negIndex_archGlue_eq hK hc,
    boostPolarIndex_eq_negIndex_of_subBoost hK (fun N => twoPos ^ N) tendsto_twoPos_pow_rpow hsub]
  rcases negIndex_eq_zero_or_top_of_mixing hK (tendsto_sTruncatedCorrNonPole_twoPos S) with h0 | htop
  · rw [h0, zero_add]; simp
  · rw [htop]; simp

/-- On the non-RH finite stratum `0 < κ(K_ζ) < ⊤`, no net of fixed-`S` global explicit-formula
correlations converges in glued negative index to `κ(weilArchState c)`. -/
theorem not_tendsto_negIndex_archGlue_sTruncatedCorr_of_finite_pos {ι : Type*} {l : Filter ι}
    [l.NeBot] (S : ι → Finset Nat.Primes) {c : ℝ} (hc : 0 < c)
    (hpos : 0 < negIndex zetaKernel) (hfin : negIndex zetaKernel < ⊤) :
    ¬ Tendsto (fun i => negIndex (archGlue (sTruncatedCorr (S i)) c))
      l (𝓝 (negIndex (weilArchState c))) := by
  intro htend
  obtain ⟨m, hm_eq⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hle1 : negIndex zetaKernel ≤ 1 := by
      rw [← hm_eq]; exact Nat.cast_le.mpr (by omega)
    exact hpos.ne' (negIndex_zetaKernel_le_one_iff.mp hle1)
  have hstate : negIndex (weilArchState c) = ((m + 1 : ℕ) : ℕ∞) := by
    rw [negIndex_weilArchState_eq_add_one hc, ← hm_eq]; rfl
  rw [hstate] at htend
  have hnhds : ({((m + 1 : ℕ) : ℕ∞)} : Set ℕ∞) ∈ 𝓝 ((m + 1 : ℕ) : ℕ∞) :=
    (ENat.isOpen_singleton (ENat.coe_ne_top (m + 1))).mem_nhds rfl
  obtain ⟨i, hi⟩ := (htend.eventually hnhds).exists
  have hmem := negIndex_archGlue_sTruncatedCorr_mem (S i) hc
  rw [Set.mem_singleton_iff.mp hi] at hmem
  rcases hmem with h1 | htop
  · have : m + 1 = 1 := Nat.cast_injective h1; omega
  · exact ENat.coe_ne_top (m + 1) htop

/-! ### Positive Survivor 2: Window-coupled zero-counterterm `S`-truncated exhaustion -/

/-- The finite prime set `{p ≤ ⌊exp(2L + 8)⌋₊}` needed to make the cubic-spline `S`-truncated
explicit formula exact on all slope families of log-height at most `L`. -/
def windowPrimes (L : ℝ) : Finset Nat.Primes :=
  primeBox (⌊Real.exp (2 * L + 8)⌋₊ + 1)

/-- **Exact finite-`S` explicit-formula stabilization on bounded log-height.** Whenever
`primeBox (⌊exp(B + 8)⌋₊ + 1) ⊆ S` and `|log u| ≤ B`, `sTruncatedCorr S u = ratCorr u` with zero
counterterm. -/
theorem sTruncatedCorr_eq_ratCorr_of_abs_logPos_le {B : ℝ} {S : Finset Nat.Primes}
    (hS : primeBox (⌊Real.exp (B + 8)⌋₊ + 1) ⊆ S) {u : posUnits} (hu : |logPos u| ≤ B) :
    sTruncatedCorr S u = ratCorr u := by
  unfold sTruncatedCorr ratCorr splineCorr
  rw [RHTower.WeilSpectral.weilFullFunctional_eq_parts,
    RHTower.WeilSpectral.weilFullFunctional_eq_parts]
  congr 2
  unfold RHTower.WeilSpectral.primePart
  refine tsum_congr fun n => ?_
  by_cases hn2 : 2 ≤ n
  · rw [if_pos hn2, if_pos hn2]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [vonMangoldtS, truncWeight, vonMangoldtWeight, hΛ]
    · by_cases hs : IsSPrimePow S n
      · simp [vonMangoldtS, truncWeight, hs, vonMangoldtWeight]
      · obtain ⟨k, _, hk_pos, p, hp_le, hnp, hp⟩ :=
          (isPrimePow_nat_iff_bounded_log n).mp
            (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
        have hp_not_S : (⟨p, hp⟩ : Nat.Primes) ∉ S := fun hmem =>
          hs ⟨⟨p, hp⟩, hmem, k, hk_pos, hnp⟩
        have hp_not_box : (⟨p, hp⟩ : Nat.Primes) ∉ primeBox (⌊Real.exp (B + 8)⌋₊ + 1) :=
          fun hmem => hp_not_S (hS hmem)
        rw [mem_primeBox, not_lt] at hp_not_box
        have hexp_lt : Real.exp (B + 8) < (n : ℝ) :=
          (Nat.lt_floor_add_one (Real.exp (B + 8))).trans_le
            (by exact_mod_cast hp_not_box.trans hp_le)
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog_gt : B + 8 < Real.log n := (Real.lt_log_iff_exp_lt hn_pos).mpr hexp_lt
        obtain ⟨hu_lo, hu_hi⟩ := abs_le.mp hu
        have h1 : 8 < |Real.log n - (-logPos u)| :=
          lt_of_lt_of_le (by linarith) (le_abs_self _)
        have h2 : 8 < |Real.log n + (-logPos u)| :=
          lt_of_lt_of_le (by linarith) (le_abs_self _)
        rw [splineCorr_prime_term_eq_zero h1 h2, mul_zero, mul_zero]
  · simp [hn2]

/-- Pointwise convergence of `sTruncatedCorr S` to `ratCorr` along `atTop`. -/
theorem tendsto_sTruncatedCorr_atTop (u : posUnits) :
    Tendsto (fun S : Finset Nat.Primes => sTruncatedCorr S u) atTop (𝓝 (ratCorr u)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (primeBox (⌊Real.exp (|logPos u| + 8)⌋₊ + 1))] with S hS
  exact (sTruncatedCorr_eq_ratCorr_of_abs_logPos_le hS le_rfl).symm

/-- Pointwise convergence of `archGlue (sTruncatedCorr S) c` to `weilArchState c` along `atTop`. -/
theorem tendsto_archGlue_sTruncatedCorr_atTop (c : ℝ) (g : AffineGroupQ) :
    Tendsto (fun S : Finset Nat.Primes => archGlue (sTruncatedCorr S) c g)
      atTop (𝓝 (weilArchState c g)) := by
  rw [weilArchState_eq_archGlue]
  exact (tendsto_sTruncatedCorr_atTop (slopeAbs g)).add tendsto_const_nhds

/-- **Exact window-coupled Gram identity.** On any finite family `g : Fin n → AffineGroupQ` with
`|log |slope(g_i)|| ≤ L` and any prime set `S ⊇ windowPrimes L`, the glued Gram matrix of
`sTruncatedCorr S` equals `gram (weilArchState c) g` entrywise. -/
theorem gram_archGlue_sTruncatedCorr_eq_weilArchState {L : ℝ} {S : Finset Nat.Primes}
    (hS : windowPrimes L ⊆ S) (c : ℝ) {n : ℕ} (g : Fin n → AffineGroupQ)
    (hg : ∀ i, |logPos (slopeAbs (g i))| ≤ L) :
    gram (archGlue (sTruncatedCorr S) c) g = gram (weilArchState c) g := by
  ext i j
  rw [weilArchState_eq_archGlue]
  simp only [gram, archGlue_inv_mul]
  congr 1
  refine sTruncatedCorr_eq_ratCorr_of_abs_logPos_le hS ?_
  rw [logPos_inv_mul]
  exact (abs_sub _ _).trans (by linarith [hg i, hg j])

/-- **Unconditional window-coupled `S`-truncated explicit-formula signature formula.** For every
`c > 0` and every prime schedule `S : ℕ → Finset Nat.Primes` with `windowPrimes L ⊆ S L`, the
supremum of the negative indices of `gram (archGlue (sTruncatedCorr (S L)) c) g` over slope-height
windows `|log |slope(g_i)|| ≤ L` equals `κ(weilArchState c) = κ(K_ζ) + 1` unconditionally. -/
theorem negIndex_weilArchState_eq_iSup_windowPrimes {S : ℕ → Finset Nat.Primes}
    (hS : ∀ L : ℕ, windowPrimes (L : ℝ) ⊆ S L) {c : ℝ} (hc : 0 < c) :
    (⨆ (L : ℕ) (n : ℕ) (g : {x : Fin n → AffineGroupQ // ∀ i, |logPos (slopeAbs (x i))| ≤ L}),
      (hermNegIndex (gram (archGlue (sTruncatedCorr (S L)) c) g.1) : ℕ∞)) =
        negIndex (weilArchState c) ∧
    (⨆ (L : ℕ) (n : ℕ) (g : {x : Fin n → AffineGroupQ // ∀ i, |logPos (slopeAbs (x i))| ≤ L}),
      (hermNegIndex (gram (archGlue (sTruncatedCorr (S L)) c) g.1) : ℕ∞)) =
        negIndex zetaKernel + 1 := by
  have heq : (⨆ (L : ℕ) (n : ℕ)
      (g : {x : Fin n → AffineGroupQ // ∀ i, |logPos (slopeAbs (x i))| ≤ L}),
      (hermNegIndex (gram (archGlue (sTruncatedCorr (S L)) c) g.1) : ℕ∞)) =
      negIndex (weilArchState c) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun L => iSup_le fun n => iSup_le fun g => ?_
      rw [gram_archGlue_sTruncatedCorr_eq_weilArchState (hS L) c g.1 g.2]
      exact hermNegIndex_gram_le_negIndex (weilArchState c) g.1
    · refine negIndex_le_iff.mpr fun n x => ?_
      set L : ℕ := univ.sup fun i : Fin n => ⌈|logPos (slopeAbs (x i))|⌉₊
      have hx : ∀ i : Fin n, |logPos (slopeAbs (x i))| ≤ (L : ℝ) := fun i =>
        (Nat.le_ceil _).trans
          (Nat.cast_le.mpr (Finset.le_sup (f := fun j => ⌈|logPos (slopeAbs (x j))|⌉₊) (mem_univ i)))
      let g : {y : Fin n → AffineGroupQ // ∀ i, |logPos (slopeAbs (y i))| ≤ L} := ⟨x, hx⟩
      rw [← gram_archGlue_sTruncatedCorr_eq_weilArchState (hS L) c g.1 g.2]
      exact le_iSup_of_le L (le_iSup_of_le n
        (le_iSup (fun y : {y : Fin n → AffineGroupQ // ∀ i, |logPos (slopeAbs (y i))| ≤ L} =>
          (hermNegIndex (gram (archGlue (sTruncatedCorr (S L)) c) y.1) : ℕ∞)) g))
  exact ⟨heq, heq.trans (negIndex_weilArchState_eq_add_one hc)⟩

end GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.polarIndex_pairKernel_add_of_secondDiff_tendsto
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.negIndex_archGlue_sTruncatedAssembly
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.tendsto_negIndex_archGlue_poleRetaining_atTop
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.not_tendsto_negIndex_archGlue_poleFree_of_finite_pos
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.exists_prime_flip_obstruction
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.coupledAssembly_eq_axial_add_interTower
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.towerAssembly_eq_axialAssembly_of_agrees
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.exists_coprimeCrossDiff_ratCorr_ne_zero
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.not_tendsto_towerAssembly_ratCorr
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.tendsto_negIndex_archGlue_axialAssembly_ratCorr_atTop
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.negIndex_archGlue_coupledAssembly_ratCorr
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.negIndex_archGlue_sTruncatedCorr_mem
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.gram_archGlue_sTruncatedCorr_eq_weilArchState
#print axioms GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.negIndex_weilArchState_eq_iSup_windowPrimes
