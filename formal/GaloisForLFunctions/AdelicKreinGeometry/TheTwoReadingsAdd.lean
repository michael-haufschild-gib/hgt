import GaloisForLFunctions.AdelicKreinGeometry.TheGluingSquareIsSharp

/-!
# The two readings add

An archimedean glued state `Φ = K(|a|) − c|a|^{−1/2}|b|` has two readings: the multiplicative one on
the dilations, `Φ(x ↦ ux) = K(u)`, and the additive one on the translations,
`Φ(x ↦ x + b) = K(1) − c|b|`.

* **The additive reading is zero-blind** (`negIndex_archGlue_translation`): for every Hermitian `K`
  and `c > 0` the successor `K(1) − c|b|` has exactly one negative square. On mass-zero weights the
  constant drops and `−|b|` is conditionally positive; two far translates give `4K(1) − 2cL < 0`.
* **The readings add** (`negIndex_archGlue_eq_add_readings`): `κ(Φ) = κ^{(½)}(K) + κ(Φ|_+)`, and for
  sub-boost data `κ(Φ) = κ(Φ|_×) + κ(Φ|_+)`.
* **Weil's archimedean state** (`negIndex_weilArchState_eq_add_readings`,
  `negIndex_weilArchState_sub_translation`): its affine index is the sum of the index of its dilation
  reading, Weil's correlation with `κ = #{zeros right of the line}`, and of its translation reading,
  with `κ = 1`.

So no additive reading of the archimedean state sees the zeros; the affine index exceeds the additive
index by exactly the number of zeros right of the critical line, and that excess is carried by the
multiplicative reading.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- **A constant successor `A − c|b|` has one negative square.** -/
theorem negIndex_const_add_negAbsRat (A : ℝ) {c : ℝ} (hc : 0 < c) :
    negIndex (fun m : Multiplicative ℚ => (A : ℂ) + c * negAbsRat m) = 1 := by
  refine le_antisymm ?_ ?_
  · -- on mass-zero weights the constant drops and `−c|b|` is conditionally positive
    have hpol : polarIndex (fun m : Multiplicative ℚ => (A : ℂ) + c * negAbsRat m) = 0 :=
      nonpos_iff_eq_zero.mp (iSup₂_le fun n x => by
        rw [negIndexOn_eq_zero_of_nonneg fun w hw => by
          have hw0 : ∑ a, w a = 0 := LinearMap.mem_ker.mp hw
          rw [hermQuad_gram_add]
          have h0 : hermQuad (gram (fun _ : Multiplicative ℚ => (A : ℂ)) x) w = 0 := by
            rw [hermQuad_gram]
            have : ∀ a, ∑ b, conj (w a) * (A : ℂ) * w b = 0 := fun a => by
              rw [← Finset.mul_sum, hw0, mul_zero]
            simp [this]
          rw [h0, zero_add]
          exact hermQuad_gram_ofReal_mul_nonneg hc.le x w (hermQuad_gram_negAbsRat_nonneg x w hw0)]
        rfl)
    simpa [hpol] using negIndex_le_polarIndex_add_one
      (fun m : Multiplicative ℚ => (A : ℂ) + c * negAbsRat m)
  · -- the translates `0, L` with weights `1, 1`: `4A − 2cL < 0`
    obtain ⟨L, hL⟩ := exists_nat_gt (2 * |A| / c)
    have hL' : 4 * A < 2 * c * L := by
      have := (div_lt_iff₀ hc).mp hL
      linarith [le_abs_self A]
    have hneg : hermQuad (gram (fun m : Multiplicative ℚ => (A : ℂ) + c * negAbsRat m)
        ![1, Multiplicative.ofAdd (L : ℚ)]) ![1, 1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, negAbsRat, absRat]
      linarith
    have h1 := one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg
    exact le_trans (by exact_mod_cast h1.trans (negIndexOn_le_hermNegIndex _ ⊤))
      (hermNegIndex_gram_le_negIndex _ _)

/-- The translation reading of the glued state. -/
theorem archGlue_translationHomQ (K : posUnits → ℂ) (c : ℝ) (m : Multiplicative ℚ) :
    (archGlue K c ∘ translationHomQ) m = K 1 + c * negAbsRat m := by
  have h1 : slopePow Rat.AbsoluteValue.real 1 (translation (Multiplicative.toAdd m)) = 1 :=
    slopePow_translation _ _ _
  have h2 : shiftOf (translation (Multiplicative.toAdd m)) = Multiplicative.toAdd m :=
    affShift_translation _
  simp only [Function.comp_apply, translationHomQ, MonoidHom.coe_mk, OneHom.coe_mk, archGlue,
    slopeAbs_translation, conformalInduction, h1, h2, inv_one, Complex.ofReal_one, one_mul,
    ofAdd_toAdd]

/-- **The additive reading is zero-blind**: the translation reading of every glued state has
exactly one negative square. -/
theorem negIndex_archGlue_translation {K : posUnits → ℂ} (hK : IsHermKernel K) {c : ℝ}
    (hc : 0 < c) : negIndex (archGlue K c ∘ translationHomQ) = 1 := by
  have hreal : K 1 = ((K 1).re : ℂ) := by
    have h := hK 1
    rw [inv_one] at h
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  rw [show archGlue K c ∘ translationHomQ = fun m => ((K 1).re : ℂ) + c * negAbsRat m from
    funext fun m => by rw [archGlue_translationHomQ, ← hreal]]
  exact negIndex_const_add_negAbsRat _ hc

/-- **The readings add**: `κ(Φ) = κ^{(½)}(K) + κ(Φ|_+)`. -/
theorem negIndex_archGlue_eq_add_readings {K : posUnits → ℂ} (hK : IsHermKernel K) {c : ℝ}
    (hc : 0 < c) :
    negIndex (archGlue K c) = boostPolarIndex K + negIndex (archGlue K c ∘ translationHomQ) := by
  rw [negIndex_archGlue_eq hK hc, negIndex_archGlue_translation hK hc]

theorem archGlue_comp_dilation (K : posUnits → ℂ) (c : ℝ) :
    archGlue K c ∘ (dilation.comp posUnits.subtype) = K :=
  funext fun u => archGlue_dilation K c u

/-- For sub-boost data the multiplicative and the additive readings add: `κ(Φ) = κ(Φ|_×) + κ(Φ|_+)`. -/
theorem negIndex_archGlue_eq_add_readings_of_subBoost {K : posUnits → ℂ} (hK : IsHermKernel K)
    {c : ℝ} (hc : 0 < c) (hfree : boostPolarIndex K = negIndex K) :
    negIndex (archGlue K c) = negIndex (archGlue K c ∘ (dilation.comp posUnits.subtype)) +
      negIndex (archGlue K c ∘ translationHomQ) := by
  rw [negIndex_archGlue_eq_add_readings hK hc, archGlue_comp_dilation, hfree]

/-- **Weil's archimedean state: the readings add.** Its index is the index of Weil's correlation on
the dilations plus the index `1` of its successor on the translations. -/
theorem negIndex_weilArchState_eq_add_readings {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) =
      negIndex (weilArchState c ∘ (dilation.comp posUnits.subtype)) +
        negIndex (weilArchState c ∘ translationHomQ) := by
  rw [weilArchState_eq_archGlue, archGlue_comp_dilation,
    negIndex_archGlue_translation isHermKernel_ratCorr hc, ← weilArchState_eq_archGlue,
    negIndex_weilArchState_eq_add_one hc, negIndex_ratCorr]

/-- **The excess of the affine index over the additive index is the number of zeros right of the
critical line.** -/
theorem negIndex_weilArchState_sub_translation {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) =
      (ArithmeticCastelnuovoSeveri.rightZeros Zeta23.zetaZeroConfig).encard +
        negIndex (weilArchState c ∘ translationHomQ) := by
  rw [weilArchState_eq_archGlue, negIndex_archGlue_translation isHermKernel_ratCorr hc,
    ← weilArchState_eq_archGlue, negIndex_weilArchState_eq_rightZeros hc]

end GaloisForLFunctions.AdelicKreinGeometry
