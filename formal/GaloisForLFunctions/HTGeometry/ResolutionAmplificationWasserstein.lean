import GaloisForLFunctions.HTGeometry.ResolutionAmplification
import GaloisForLFunctions.HTGeometry.KantorovichRubinsteinDuality

/-!
# Resolution amplification as a Wasserstein Lipschitz constant

For a Markov kernel `K : X ⇝ Z` into a compact metric space, the extended operator seminorm
`α(K) = sup_{0 < Lip f < ∞} Lip(K^* f) / Lip f` of the effect pullback equals

`α(K) = sup_{x ≠ x'} W₁(K(x, ·), K(x', ·)) / d(x, x')`.

The proof writes `Lip g` as the supremum of difference quotients and uses the
Kantorovich–Rubinstein duality `W₁ = sup_{Lip f ≤ 1} (∫ f dμ - ∫ f dν)`.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section LipNormQuotient

variable {X : Type*} [MetricSpace X]

/-- `Lip f` is the supremum of the difference quotients `|f x - f y| / d(x, y)`. -/
theorem lipNorm_eq_iSup_quotient (f : X → ℝ) :
    lipNorm f = ⨆ (x : X) (y : X) (_ : x ≠ y), ENNReal.ofReal (|f x - f y| / dist x y) := by
  refine le_antisymm ?_ ?_
  · set S := ⨆ (x : X) (y : X) (_ : x ≠ y), ENNReal.ofReal (|f x - f y| / dist x y)
    rcases eq_or_ne S ⊤ with hS | hS
    · rw [hS]
      exact le_top
    have hq : ∀ x y, x ≠ y → |f x - f y| / dist x y ≤ S.toReal := fun x y h =>
      (ENNReal.ofReal_le_iff_le_toReal hS).mp (le_iSup₂_of_le x y (le_iSup_of_le h le_rfl))
    have hL : LipschitzWith S.toNNReal f := LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, ENNReal.coe_toNNReal_eq_toReal]
      rcases eq_or_ne x y with rfl | h
      · simp
      · rw [← div_le_iff₀ (dist_pos.mpr h)]
        exact hq x y h
    exact (lipNorm_le hL).trans (by rw [ENNReal.coe_toNNReal hS])
  · refine iSup₂_le fun x y => iSup_le fun h => ?_
    rcases eq_or_ne (lipNorm f) ⊤ with hL | hL
    · rw [hL]
      exact le_top
    rw [← ENNReal.ofReal_toReal hL]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (dist_pos.mpr h)]
    exact abs_sub_le_lipNorm_mul (lt_top_iff_ne_top.mpr hL) x y

end LipNormQuotient

section Wasserstein

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace X] [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z]

/-- **(RP.9).**  `α(K) = sup_{x ≠ x'} W₁(K(x, ·), K(x', ·)) / d(x, x')`. -/
theorem resolutionAmplification_eq_iSup_wassersteinOne (K : Kernel X Z) [IsMarkovKernel K] :
    resolutionAmplification K
      = ⨆ (x : X) (x' : X) (_ : x ≠ x'),
          ENNReal.ofReal (wassersteinOne (K x) (K x') / dist x x') := by
  set T := ⨆ (x : X) (x' : X) (_ : x ≠ x'),
    ENNReal.ofReal (wassersteinOne (K x) (K x') / dist x x')
  refine le_antisymm ?_ ?_
  · refine iSup_le fun f => iSup_le fun hpos => iSup_le fun hfin => ?_
    refine ENNReal.div_le_of_le_mul ?_
    rw [lipNorm_eq_iSup_quotient]
    refine iSup₂_le fun x y => iSup_le fun hne => ?_
    have hxy : 0 < dist x y := dist_pos.mpr hne
    have hLf := lipschitzWith_of_lipNorm_lt_top hfin
    have hgap := abs_integral_sub_le_mul_wassersteinOne (μ := K x) (ν := K y) hLf
    rw [ENNReal.coe_toNNReal_eq_toReal] at hgap
    have hW : 0 ≤ wassersteinOne (K x) (K y) := by
      rw [wassersteinOne_eq_lipschitzDual]
      have := le_lipschitzDual (μ := K x) (ν := K y) ((LipschitzWith.const 0).weaken zero_le_one)
      simpa using this
    calc ENNReal.ofReal (|kernelPullback K f x - kernelPullback K f y| / dist x y)
        ≤ ENNReal.ofReal ((lipNorm f).toReal * (wassersteinOne (K x) (K y) / dist x y)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right hgap hxy.le
      _ = lipNorm f * ENNReal.ofReal (wassersteinOne (K x) (K y) / dist x y) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
      _ ≤ lipNorm f * T := by
          gcongr
          exact le_iSup₂_of_le x y (le_iSup_of_le hne le_rfl)
      _ = T * lipNorm f := mul_comm _ _
  · refine iSup₂_le fun x x' => iSup_le fun hne => ?_
    rcases eq_or_ne (resolutionAmplification K) ⊤ with htop | hfin
    · rw [htop]
      exact le_top
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal ?_
    have hd : 0 < dist x x' := dist_pos.mpr hne
    rw [div_le_iff₀ hd, wassersteinOne_eq_lipschitzDual]
    haveI : Nonempty {f : Z → ℝ // LipschitzWith 1 f} :=
      ⟨⟨fun _ => 0, (LipschitzWith.const 0).weaken zero_le_one⟩⟩
    refine ciSup_le fun g => ?_
    have hg1 : lipNorm (g : Z → ℝ) ≤ 1 := by simpa using lipNorm_le g.2
    have hgfin : lipNorm (g : Z → ℝ) < ⊤ := hg1.trans_lt ENNReal.one_lt_top
    have hpull := lipNorm_kernelPullback_le K hgfin
    have hle : lipNorm (kernelPullback K g) ≤ resolutionAmplification K :=
      hpull.trans (mul_le_of_le_one_right' hg1)
    have hpfin : lipNorm (kernelPullback K g) < ⊤ := hle.trans_lt (lt_top_iff_ne_top.mpr hfin)
    have h := abs_sub_le_lipNorm_mul hpfin x x'
    have hle' : (lipNorm (kernelPullback K g)).toReal ≤ (resolutionAmplification K).toReal :=
      ENNReal.toReal_mono hfin hle
    have : kernelPullback K g x - kernelPullback K g x' ≤ (resolutionAmplification K).toReal
        * dist x x' :=
      (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_right hle' hd.le))
    exact this

end Wasserstein

end GaloisForLFunctions.HTGeometry
