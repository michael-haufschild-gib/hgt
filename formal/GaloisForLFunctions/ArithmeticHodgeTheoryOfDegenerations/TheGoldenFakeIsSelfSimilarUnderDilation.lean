import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.DegenerationSelectsThePureCurves

/-!
# The golden fake is self-similar under dilation

The limiting structure of a fake curve along the dilation of its atoms. For a curve datum the
lattice atoms `f_k = g_w(· − k log q)` of width `w` have the Gram matrix

`W(f_k, f_l) = log q Σ_i β_i^{k−l} Φ_{β_i}(w)`,   `Φ_β(w) = Σ_{j∈ℤ} w G(j log q/w) β^j`

(`W_curveConfig_translate_atom`): the eigenvalue `β_i` acts on the lattice index, the width only
through the lag series `Φ_{β_i}`, and `Φ_{β⁻¹} = Φ_β` since the autocorrelation `G` is even
(`lagSeries_inv`). Hence:

* **One orbit, scalar dilation** (`towerGram_eq_smul_spanGram_of_orbit`): for a datum with the two
  eigenvalues `β, β⁻¹` (an elliptic curve, or a fake of genus one) the Gram matrix of the lattice
  atoms at every width is `E(w)/2` times the span Gram matrix `(t_{|k−l|})` of the narrow tower,
  `E(w)` the energy of one atom: the dilation acts by a scalar on one fixed form.
* **Self-similarity of the golden fake** (`goldenDatum_towerGram_eq_smul_spanGram`): `β = φ, φ⁻¹`
  over `𝔽₅`.
* **Stationarity along the horizon** (`W_curveConfig_translate_translate`): Weil's form of a curve
  is translation invariant, so a lattice window reads the same form at every horizon.
* **The limiting structure is a hyperbolic plane** (`goldenDatum_negIndex_dilation`): for a
  nonnegative nonzero profile the family has exactly one negative square from window `2` on, at
  every width, while its scale `E(w) ≥ c w e^{εw}` explodes (`goldenDatum_curveAtomEnergy_ge`).

This is the `𝔽_q` counterpart of a prime flip over `ℤ`, whose residue is an overlap-independent
indefinite form (ADT `primeFlip_degenerates_indefinitely`): the fake does not degenerate, it keeps
its indefinite structure at every resolution.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) {φ : ℝ → ℝ}

/-- The lag series `Φ_β(w) = Σ_{j∈ℤ} w G(j log q/w) β^j` of one eigenvalue. -/
def lagSeries (φ : ℝ → ℝ) (w : ℝ) (β : ℂ) : ℂ :=
  ∑' j : ℤ, ((w * shellAutocorr φ (j * Real.log D.q / w) : ℝ) : ℂ) * β ^ j

theorem curveDatum_β_ne_zero (i : ι) : D.β i ≠ 0 := fun h => by
  have := D.β_fePerm i
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- **The lattice Gram matrix of a curve at every width**:
`W(f_k, f_l) = log q Σ_i β_i^{k−l} Φ_{β_i}(w)`. -/
theorem W_curveConfig_translate_atom (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) (k l : ℕ) :
    (D.curveConfig hD).W
        (ArithmeticCastelnuovoSeveri.translate (k * Real.log D.q) (cx (atomDilate φ w)))
        (ArithmeticCastelnuovoSeveri.translate (l * Real.log D.q) (cx (atomDilate φ w))) =
      ∑ i, Real.log D.q * (D.β i ^ ((k : ℤ) - l) * lagSeries D φ w (D.β i)) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hg2 : ContDiff ℝ 2 (cx (atomDilate φ w)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (contDiff_id.div_const w))
  have hgc : HasCompactSupport (cx (atomDilate φ w)) :=
    (hasCompactSupport_atomDilate hw.ne' hφc).comp_left Complex.ofReal_zero
  rw [D.W_curveConfig hD (translate_contDiff hg2 _) (translate_hasCompactSupport hgc _)
    (translate_contDiff hg2 _).continuous (translate_hasCompactSupport hgc _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold lagSeries
  rw [← tsum_mul_left, ← (Equiv.addRight ((k : ℤ) - l)).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.coe_addRight]
  rw [weilTest_translate, weilTest_atom hw, zpow_add₀ (curveDatum_β_ne_zero D i)]
  push_cast
  ring_nf

/-- **The curve family is stationary along the horizon**: Weil's form of a curve is invariant under
translating both tests, so the horizon of a lattice window does not enter; over a curve the only
degeneration is in the atom width. -/
theorem W_curveConfig_translate_translate (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (t : ℝ) :
    (D.curveConfig hD).W (ArithmeticCastelnuovoSeveri.translate t f)
        (ArithmeticCastelnuovoSeveri.translate t g) = (D.curveConfig hD).W f g := by
  rw [D.W_curveConfig hD (translate_contDiff hf t) (translate_hasCompactSupport hfc t)
    (translate_contDiff hg t).continuous (translate_hasCompactSupport hgc t),
    D.W_curveConfig hD hf hfc hg.continuous hgc]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine tsum_congr fun m => ?_
  rw [weilTest_translate, sub_self, sub_zero]

/-- `t_{k−l}` as a two-sided power sum: `z^{k−l} + z^{−(k−l)} = z^{|k−l|} + z^{−|k−l|}`. -/
theorem zpow_add_inv_zpow_eq_dist (z : ℂ) (k l : ℕ) :
    z ^ ((k : ℤ) - l) + z⁻¹ ^ ((k : ℤ) - l) = z ^ (Nat.dist k l) + z⁻¹ ^ (Nat.dist k l) := by
  rcases le_total l k with h | h
  · have e : ((k : ℤ) - l) = ((Nat.dist k l : ℕ) : ℤ) := by unfold Nat.dist; omega
    rw [e, zpow_natCast, zpow_natCast]
  · have e : ((k : ℤ) - l) = -((Nat.dist k l : ℕ) : ℤ) := by unfold Nat.dist; omega
    rw [e, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow, inv_inv, ← inv_pow, add_comm]

/-- The lag series of `β⁻¹` is that of `β`: `Φ_{β⁻¹} = Φ_β`, since `G` is even. -/
theorem lagSeries_inv (φ : ℝ → ℝ) (w : ℝ) (β : ℂ) :
    lagSeries D φ w β⁻¹ = lagSeries D φ w β := by
  unfold lagSeries
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply, Int.cast_neg, neg_mul, neg_div, shellAutocorr_neg]
  rw [inv_zpow', neg_neg]

/-- **A single Frobenius orbit makes the dilation scalar.** For a datum with the two eigenvalues
`β, β⁻¹` (an elliptic curve, or a fake of genus one), at every width the Gram matrix of the lattice
atoms is `E(w)/2` times the span Gram matrix of the narrow tower. -/
theorem towerGram_eq_smul_spanGram_of_orbit (D : CurveDatum (Fin 2))
    (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hinv : D.β 1 = (D.β 0)⁻¹) (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) (n : ℕ) :
    zeroGram (D.curveConfig hD) (fun k : Fin n => ArithmeticCastelnuovoSeveri.translate
        (((k : ℕ) : ℝ) * Real.log D.q) (cx (atomDilate φ w))) =
      ((curveAtomEnergy D φ w / 2 : ℝ) : ℂ) • D.spanGram n := by
  -- every Gram entry is `log q Φ t_{|k−l|}`
  have hW : ∀ k l : ℕ, (D.curveConfig hD).W
      (ArithmeticCastelnuovoSeveri.translate (k * Real.log D.q) (cx (atomDilate φ w)))
      (ArithmeticCastelnuovoSeveri.translate (l * Real.log D.q) (cx (atomDilate φ w))) =
      Real.log D.q * lagSeries D φ w (D.β 0) * (D.trace (Nat.dist k l) : ℂ) := by
    intro k l
    rw [W_curveConfig_translate_atom D hD hφ hφsupp hw, Fin.sum_univ_two, hinv, lagSeries_inv,
      ← D.powerSum_eq_trace, CurveDatum.powerSum, Fin.sum_univ_two, hinv]
    have hz := zpow_add_inv_zpow_eq_dist (D.β 0) k l
    linear_combination ((Real.log D.q : ℂ) * lagSeries D φ w (D.β 0)) * hz
  have hE : (curveAtomEnergy D φ w : ℂ) = 2 * (Real.log D.q * lagSeries D φ w (D.β 0)) := by
    rw [← W_curveConfig_atom D hD hφ hφsupp hw]
    have h := hW 0 0
    have ht0 : ArithmeticCastelnuovoSeveri.translate 0 (cx (atomDilate φ w)) =
        cx (atomDilate φ w) :=
      funext fun u => by simp only [ArithmeticCastelnuovoSeveri.translate, sub_zero]
    simp only [Nat.cast_zero, zero_mul, Nat.dist_self, D.trace_zero, Fintype.card_fin, ht0] at h
    rw [h]
    push_cast
    ring
  ext k l
  simp only [zeroGram, Matrix.smul_apply, CurveDatum.spanGram, smul_eq_mul]
  rw [hW (k : ℕ) (l : ℕ), Complex.ofReal_div (curveAtomEnergy D φ w) 2, hE]
  push_cast
  ring

open Real in
/-- **The golden fake is self-similar under dilation**: at every width the Gram matrix of the
lattice atoms is `E(w)/2` times the span Gram matrix of the narrow tower. -/
theorem goldenDatum_towerGram_eq_smul_spanGram (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) (n : ℕ) :
    zeroGram (goldenDatum.curveConfig goldenDatum_strip)
        (fun k : Fin n => ArithmeticCastelnuovoSeveri.translate
          (((k : ℕ) : ℝ) * Real.log goldenDatum.q) (cx (atomDilate φ w))) =
      ((curveAtomEnergy goldenDatum φ w / 2 : ℝ) : ℂ) • goldenDatum.spanGram n :=
  towerGram_eq_smul_spanGram_of_orbit goldenDatum goldenDatum_strip
    (Complex.ofReal_inv goldenRatio) hφ hφsupp hw n

/-- **The limiting structure of the golden fake is a hyperbolic plane**: for a nonnegative nonzero
profile the lattice atoms have exactly one negative square from window `2` on, at every width. -/
theorem goldenDatum_negIndex_dilation (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hM : 0 < ∫ u, φ u ^ 2)
    {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 2 ≤ n) :
    hermNegIndex (zeroGram (goldenDatum.curveConfig goldenDatum_strip)
      (fun k : Fin n => ArithmeticCastelnuovoSeveri.translate
        (((k : ℕ) : ℝ) * Real.log goldenDatum.q) (cx (atomDilate φ w)))) = 1 := by
  obtain ⟨c, ε, hc, hε, hge⟩ := goldenDatum_curveAtomEnergy_ge hφ hφsupp hφ0 hM
  have hE : 0 < curveAtomEnergy goldenDatum φ w / 2 := by
    have h1 := hge w hw
    have h2 : 0 < c * w * Real.exp (ε * w) := by positivity
    linarith
  rw [goldenDatum_towerGram_eq_smul_spanGram hφ hφsupp hw n, hermNegIndex_ofReal_smul hE]
  exact goldenDatum_negIndex_spanGram hn

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
