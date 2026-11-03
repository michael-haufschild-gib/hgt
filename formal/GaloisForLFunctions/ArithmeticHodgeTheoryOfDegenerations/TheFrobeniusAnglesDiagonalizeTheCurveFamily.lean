import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfATwistIsItsSpectrum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface

/-!
# The Frobenius angles diagonalize the curve family

The `𝔽_q` calibration of the complete family. Over a curve with normalized Frobenius eigenvalues
`β_i`, the atoms sit on the norm lattice `k log q`; the family of lattice tests
`T_x = Σ_{k<n} x_k g_w(· − k log q)`, `g_w = φ(·/w)`, has a free resolution parameter, the atom
width `w` (overlap `a = w/log q`). At narrow width (`a < 1`) its Gram matrix is
`log q ‖g‖² · spanGram` (ACS `curve_towerGram_eq_smul_spanGram`): finite monodromy. At every width:

* **Weil's form of a lattice test** (`W_curveLatticeTest`): for a pure curve (`|β_i| = 1`,
  `β_i = e(θ_i)`),

  `W(T_x, T_x) = w² Σ_i S_{θ_i}(w/log q) |Σ_k x_k β_i^k|²`,  `S_θ(a) = Σ_{j∈ℤ} |φ̂(2πa(j + θ))|²`,

  by the explicit formula of the curve (lags `m log q` weighted by `β_i^m`), the cross-correlations
  of the lattice atoms, and Poisson summation on the shifted lattice `j + θ_i`
  (`hasSum_shellSpectrum_shift`).
* **Positivity at every resolution** (`re_W_curveLatticeTest_nonneg`): for a pure curve the form is
  a sum of squares, with weights the shifted lattice spectra at the Frobenius angles.

So a curve is read by its complete family exactly as a periodic twist is read over `ℤ`
(`abs_twistEnergy_sub_le`): the Frobenius angle `θ_i` plays the role of the mode `k/M`, and the
degeneration under dilation (`a → ∞`) is governed by the same shifted densities
`S_θ = D_θ + D_{1−θ}`, whose rescaled limits are Hurwitz constants (`tendsto_rpow_mul_twistBulk`).
A real eigenvalue `β = 1` (`θ = 0`) contributes the main term `(∫φ)²/a` of the conductor-one
direction; every other angle is aliasing only.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) {φ : ℝ → ℝ}

/-- The lattice test `T_x = Σ_{k<n} x_k g_w(· − k log q)` of a curve. -/
def curveLatticeTest (φ : ℝ → ℝ) (w : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ → ℂ :=
  fun u => ∑ k ∈ range n, (x k : ℂ) * ArithmeticCastelnuovoSeveri.translate (k * Real.log D.q) (cx (atomDilate φ w)) u

theorem contDiff_curveLatticeTest (hφ : ContDiff ℝ 2 φ) (w : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    ContDiff ℝ 2 (curveLatticeTest D φ w n x) := by
  unfold curveLatticeTest
  refine ContDiff.sum fun k _ => contDiff_const.mul (translate_contDiff ?_ _)
  exact Complex.ofRealCLM.contDiff.comp (hφ.comp (contDiff_id.div_const w))

theorem hasCompactSupport_curveLatticeTest (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ}
    (hw : 0 < w) (n : ℕ) (x : ℕ → ℝ) : HasCompactSupport (curveLatticeTest D φ w n x) := by
  have hL : 0 < Real.log D.q := D.log_q_pos
  refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := n * Real.log D.q + w))
    fun u hu => ?_
  unfold curveLatticeTest
  refine sum_eq_zero fun k hk => ?_
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
  simp only [ArithmeticCastelnuovoSeveri.translate, cx, atomDilate]
  rw [hφsupp _ ?_, Complex.ofReal_zero, mul_zero]
  intro hm
  apply hu
  obtain ⟨h0, h1⟩ := hm
  rw [le_div_iff₀ hw, zero_mul] at h0
  rw [div_le_one hw] at h1
  have hk0 : (0 : ℝ) ≤ k * Real.log D.q := by positivity
  constructor
  · linarith
  · nlinarith

/-- The cross-correlation of an atom with itself: `(g_w ⋆ g̃_w)(t) = w G(t/w)`. -/
theorem weilTest_atom {w : ℝ} (hw : 0 < w) (t : ℝ) :
    EF.weilTest (cx (atomDilate φ w)) (cx (atomDilate φ w)) t =
      ((w * shellAutocorr φ (t / w) : ℝ) : ℂ) := by
  rw [RHTower.weilTest_apply]
  have e : ∀ s : ℝ, cx (atomDilate φ w) s * conj (cx (atomDilate φ w) (s - t)) =
      ((atomDilate φ w s * atomDilate φ w (s + -t) : ℝ) : ℂ) := fun s => by
    simp [cx, sub_eq_add_neg]
  simp_rw [e]
  rw [integral_complex_ofReal]
  congr 1
  have h := bumpCorr_atomDilate_eq' (φ := φ) hw (-t)
  unfold bumpCorr at h
  rw [h, neg_div, shellAutocorr_neg]

/-- **The lags of a lattice test**:
`(T_x ⋆ T̃_x)(t) = Σ_{k,l} x_k x_l w G((t − (k − l) log q)/w)`. -/
theorem weilTest_curveLatticeTest (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) (n : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    EF.weilTest (curveLatticeTest D φ w n x) (curveLatticeTest D φ w n x) t =
      ∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l *
        (w * shellAutocorr φ ((t - ((k : ℝ) - l) * Real.log D.q) / w)) : ℝ) : ℂ) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hgc : Continuous (cx (atomDilate φ w)) := by unfold cx atomDilate; fun_prop
  have hgs : HasCompactSupport (cx (atomDilate φ w)) :=
    (hasCompactSupport_atomDilate hw.ne' hφc).comp_left Complex.ofReal_zero
  have hint : ∀ k l : ℕ, Integrable fun s : ℝ =>
      ArithmeticCastelnuovoSeveri.translate (k * Real.log D.q) (cx (atomDilate φ w)) s *
        conj (ArithmeticCastelnuovoSeveri.translate (l * Real.log D.q) (cx (atomDilate φ w)) (s - t)) := by
    intro k l
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold ArithmeticCastelnuovoSeveri.translate
      exact (hgc.comp (continuous_id.sub continuous_const)).mul
        (Complex.continuous_conj.comp (hgc.comp ((continuous_id.sub continuous_const).sub
          continuous_const)))
    · exact (translate_hasCompactSupport hgs _).mul_right
  rw [RHTower.weilTest_apply]
  unfold curveLatticeTest
  have hexp : ∀ s : ℝ, (∑ k ∈ range n, (x k : ℂ) * ArithmeticCastelnuovoSeveri.translate (k * Real.log D.q)
      (cx (atomDilate φ w)) s) * conj (∑ l ∈ range n, (x l : ℂ) * ArithmeticCastelnuovoSeveri.translate (l * Real.log D.q)
        (cx (atomDilate φ w)) (s - t)) =
      ∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l : ℝ) : ℂ) *
        (ArithmeticCastelnuovoSeveri.translate (k * Real.log D.q) (cx (atomDilate φ w)) s *
          conj (ArithmeticCastelnuovoSeveri.translate (l * Real.log D.q) (cx (atomDilate φ w)) (s - t))) := by
    intro s
    rw [map_sum, Finset.sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint k l).const_mul _]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hint k l).const_mul _]
  refine sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  have hw' := weilTest_translate (k * Real.log D.q) (l * Real.log D.q) (cx (atomDilate φ w))
    (cx (atomDilate φ w)) t
  rw [RHTower.weilTest_apply, RHTower.weilTest_apply] at hw'
  rw [hw', ← RHTower.weilTest_apply, weilTest_atom hw]
  push_cast
  ring_nf

/-- The lag series of one eigenvalue on the unit circle: with `β = e(θ)`, `a = w/log q`,
`Σ_m w G((m − d) log q/w) β^m = β^d w a S_θ(a)`. -/
theorem hasSum_lag_unitCircle (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {w L : ℝ} (hw : 0 < w) (hL : 0 < L) (θ : ℝ) (d : ℤ) :
    HasSum (fun m : ℤ => ((w * shellAutocorr φ (((m : ℝ) - d) * L / w) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (θ * m)))
      (Complex.exp (2 * Real.pi * Complex.I * (θ * d)) * ((w * (w / L)) : ℝ) *
        ∑' j : ℤ, ((shellSpectrum φ (w / L * (j + θ)) : ℝ) : ℂ)) := by
  have ha : 0 < w / L := div_pos hw hL
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  -- the unshifted lattice series has finite support
  set K : ℕ := ⌈w / L⌉₊ with hK
  have hfin : ∀ j ∉ Finset.Icc (-(K : ℤ)) K,
      Complex.exp (2 * Real.pi * Complex.I * (θ * j)) *
        ((shellAutocorr φ (j * (w / L)⁻¹) : ℝ) : ℂ) = 0 := by
    intro j hj
    rw [hG1 _ ?_, Complex.ofReal_zero, mul_zero]
    rw [abs_mul, abs_inv, abs_of_pos ha, le_mul_inv_iff₀ ha, one_mul]
    have hKw : w / L ≤ K := Nat.le_ceil _
    rw [Finset.mem_Icc, not_and_or] at hj
    rcases hj with hj | hj
    · push Not at hj
      have : (j : ℝ) < -K := by exact_mod_cast hj
      rw [abs_of_neg (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]; linarith
    · push Not at hj
      have : (K : ℝ) < j := by exact_mod_cast hj
      rw [abs_of_pos (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]; linarith
  have hP := hasSum_shellSpectrum_shift hφ hφsupp ha θ
  have hX : ∑' m : ℤ, Complex.exp (2 * Real.pi * Complex.I * (θ * m)) *
      ((shellAutocorr φ (m * (w / L)⁻¹) : ℝ) : ℂ) =
      ((w / L : ℝ) : ℂ) * ∑' j : ℤ, ((shellSpectrum φ (w / L * (j + θ)) : ℝ) : ℂ) := by
    rw [hP.tsum_eq, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne',
      Complex.ofReal_one, one_mul]
  have hS0 : HasSum (fun j : ℤ => Complex.exp (2 * Real.pi * Complex.I * (θ * j)) *
      ((shellAutocorr φ (j * (w / L)⁻¹) : ℝ) : ℂ))
      (((w / L : ℝ) : ℂ) * ∑' j : ℤ, ((shellSpectrum φ (w / L * (j + θ)) : ℝ) : ℂ)) := by
    have hsm : Summable fun j : ℤ => Complex.exp (2 * Real.pi * Complex.I * (θ * j)) *
        ((shellAutocorr φ (j * (w / L)⁻¹) : ℝ) : ℂ) :=
      summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K) hfin
    have hS0' := hsm.hasSum
    rw [hX] at hS0'
    exact hS0'
  have hS := hS0.mul_left (Complex.exp (2 * Real.pi * Complex.I * (θ * d)) * (w : ℂ))
  have hshift := (Equiv.subRight d).hasSum_iff.mpr hS
  have hfun : (fun m : ℤ => ((w * shellAutocorr φ (((m : ℝ) - d) * L / w) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (θ * m))) =
      fun m : ℤ => Complex.exp (2 * Real.pi * Complex.I * (θ * d)) * (w : ℂ) *
        (Complex.exp (2 * Real.pi * Complex.I * (θ * ((m - d : ℤ) : ℤ))) *
          ((shellAutocorr φ (((m - d : ℤ) : ℤ) * (w / L)⁻¹) : ℝ) : ℂ)) := by
    funext m
    have harg : ((m : ℝ) - d) * L / w = (((m - d : ℤ) : ℤ) : ℝ) * (w / L)⁻¹ := by
      push_cast; field_simp
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (θ * m)) =
        Complex.exp (2 * Real.pi * Complex.I * (θ * d)) *
          Complex.exp (2 * Real.pi * Complex.I * (θ * ((m - d : ℤ) : ℤ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [harg, hexp]
    push_cast
    ring
  have hval : Complex.exp (2 * Real.pi * Complex.I * (θ * d)) * ((w * (w / L)) : ℝ) *
      ∑' j : ℤ, ((shellSpectrum φ (w / L * (j + θ)) : ℝ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (θ * d)) * (w : ℂ) *
        (((w / L : ℝ) : ℂ) * ∑' j : ℤ, ((shellSpectrum φ (w / L * (j + θ)) : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hfun, hval]
  exact hshift

/-- **Weil's form of a curve on lattice tests.** For a pure curve (`|β_i| = 1`, `β_i = e(θ_i)`,
`θ_i = arg β_i/2π`) and every atom width `w > 0`:
`W(T_x, T_x) = w² Σ_i S_{θ_i}(w/log q) |Σ_k x_k β_i^k|²`, `S_θ(a) = Σ_{j∈ℤ} |φ̂(2πa(j + θ))|²`. -/
theorem W_curveLatticeTest (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hpure : ∀ i, ‖D.β i‖ = 1)
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w)
    (n : ℕ) (x : ℕ → ℝ) :
    (D.curveConfig hD).W (curveLatticeTest D φ w n x) (curveLatticeTest D φ w n x) =
      ∑ i, ((w ^ 2 * ∑' j : ℤ, shellSpectrum φ (w / Real.log D.q *
          (j + Complex.arg (D.β i) / (2 * Real.pi))) : ℝ) : ℂ) *
        ((‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 : ℝ) : ℂ) := by
  have hL : 0 < Real.log D.q := D.log_q_pos
  have hT2 := contDiff_curveLatticeTest D hφ w n x
  have hTc := hasCompactSupport_curveLatticeTest D hφsupp hw n x
  rw [D.W_curveConfig hD hT2 hTc hT2.continuous hTc]
  refine sum_congr rfl fun i _ => ?_
  set θ := Complex.arg (D.β i) / (2 * Real.pi) with hθ
  have hβ : D.β i = Complex.exp (2 * Real.pi * Complex.I * θ) := by
    have h := Complex.norm_mul_exp_arg_mul_I (D.β i)
    rw [hpure i, Complex.ofReal_one, one_mul] at h
    rw [← h, hθ]
    congr 1
    push_cast
    field_simp
  have hβm : ∀ m : ℤ, D.β i ^ m = Complex.exp (2 * Real.pi * Complex.I * (θ * m)) := by
    intro m
    rw [hβ, ← Complex.exp_int_mul]
    congr 1; ring
  have hβk : ∀ k : ℕ, D.β i ^ k = Complex.exp (2 * Real.pi * Complex.I * (θ * k)) := by
    intro k
    have := hβm k
    rwa [zpow_natCast, Int.cast_natCast] at this
  simp_rw [weilTest_curveLatticeTest D hφ.continuous hφsupp hw, hβm]
  -- each pair of atoms
  set S := ∑' j : ℤ, ((shellSpectrum φ (w / Real.log D.q * (j + θ)) : ℝ) : ℂ) with hSdef
  have hkl : ∀ k ∈ range n, ∀ l ∈ range n, HasSum (fun m : ℤ =>
      ((x k * x l * (w * shellAutocorr φ (((m : ℝ) * Real.log D.q -
        ((k : ℝ) - l) * Real.log D.q) / w)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (θ * m)))
      (((x k * x l : ℝ) : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (θ * (((k : ℤ) - l : ℤ) : ℂ))) *
        ((w * (w / Real.log D.q)) : ℝ) * S)) := by
    intro k _ l _
    have h := (hasSum_lag_unitCircle hφ hφsupp hw hL θ ((k : ℤ) - l)).mul_left ((x k * x l : ℝ) : ℂ)
    have hfk : (fun m : ℤ => ((x k * x l * (w * shellAutocorr φ (((m : ℝ) * Real.log D.q -
        ((k : ℝ) - l) * Real.log D.q) / w)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (θ * m))) =
        fun m : ℤ => ((x k * x l : ℝ) : ℂ) * (((w * shellAutocorr φ (((m : ℝ) -
          (((k : ℤ) - l : ℤ) : ℝ)) * Real.log D.q / w) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (θ * m))) := by
      funext m
      have harg : ((m : ℝ) * Real.log D.q - ((k : ℝ) - l) * Real.log D.q) / w =
          ((m : ℝ) - (((k : ℤ) - l : ℤ) : ℝ)) * Real.log D.q / w := by push_cast; ring
      rw [harg]
      push_cast
      ring
    rw [hfk]
    exact h
  have hsum := hasSum_sum fun k hk => hasSum_sum fun l hl => hkl k hk l hl
  have hfun : (fun m : ℤ => (∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l * (w * shellAutocorr φ
      (((m : ℝ) * Real.log D.q - ((k : ℝ) - l) * Real.log D.q) / w)) : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (θ * m))) =
      fun m : ℤ => ∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l * (w * shellAutocorr φ
        (((m : ℝ) * Real.log D.q - ((k : ℝ) - l) * Real.log D.q) / w)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (θ * m)) := by
    funext m
    rw [Finset.sum_mul]
    exact sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  rw [hfun, hsum.tsum_eq]
  -- the quadratic form of the angle
  have hquad : ∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (θ * (((k : ℤ) - l : ℤ) : ℂ))) =
      ((‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [hβk, hβk, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have he : Complex.exp (2 * Real.pi * Complex.I * (θ * (((k : ℤ) - l : ℤ) : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I * (θ * k)) *
          Complex.exp ((starRingEnd ℂ) (2 * Real.pi * Complex.I * (θ * l))) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
      push_cast
      ring
    rw [he]
    push_cast
    ring
  have hL' : ((Real.log D.q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  calc ((Real.log D.q : ℝ) : ℂ) * ∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l : ℝ) : ℂ) *
        (Complex.exp (2 * Real.pi * Complex.I * (θ * (((k : ℤ) - l : ℤ) : ℂ))) *
          ((w * (w / Real.log D.q)) : ℝ) * S) =
      ((Real.log D.q : ℝ) : ℂ) * (((w * (w / Real.log D.q)) : ℝ) * S) *
        ∑ k ∈ range n, ∑ l ∈ range n, ((x k * x l : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (θ * (((k : ℤ) - l : ℤ) : ℂ))) := by
        simp only [Finset.mul_sum]
        exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [hquad, hSdef, Complex.ofReal_mul, ← Complex.ofReal_tsum]
        push_cast
        field_simp

/-- **Positivity at every resolution**: for a pure curve, Weil's form is nonnegative on every
lattice test, at every atom width. -/
theorem re_W_curveLatticeTest_nonneg (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hpure : ∀ i, ‖D.β i‖ = 1)
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w)
    (n : ℕ) (x : ℕ → ℝ) :
    0 ≤ ((D.curveConfig hD).W (curveLatticeTest D φ w n x) (curveLatticeTest D φ w n x)).re := by
  rw [W_curveLatticeTest D hD hpure hφ hφsupp hw n x, Complex.re_sum]
  refine sum_nonneg fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (tsum_nonneg fun j => shellSpectrum_nonneg _))
    (sq_nonneg _)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
