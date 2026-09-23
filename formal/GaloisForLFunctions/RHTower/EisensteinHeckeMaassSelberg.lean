import GaloisForLFunctions.RHTower.EisensteinHeckeOperator
import GaloisForLFunctions.RHTower.EisensteinMaassSelbergLineModel
import GaloisForLFunctions.RHTower.EisensteinTruncatedPairingHolomorphic

/-!
# The Hecke operator on the truncated Eisenstein line model

Truncating the Eisenstein line model at height `Y` removes its constant term above `Y`.  Since the
Hecke operator `T_p` rescales heights by `p^{±1}`, it does not commute with the truncation: the
exact identity is

`T_p Λ^Y E_u = (p^u + p^{-u}) Λ^Y E_u + R_p(u, Y, y)`

with an explicit `x`-independent remainder `R_p` built from the two Weyl powers and the three
indicators `1_{y > Y}`, `1_{y > Y/p}`, `1_{y > pY}`.  Above height `pY` the remainder vanishes,
because `p^{-1/2}(p^{w} + p^{1-w}) = p^u + p^{-u}` for both Weyl exponents `w = ½ ± u`.
-/

open Complex Finset MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The truncation in coordinates -/

/-- The truncated line model `Λ^Y E_u` in coordinates. -/
def truncatedLeg (u : ℂ) (Y x y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspLeg .scalar u x y -
    (if Y < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0)

theorem truncatedLineModel_eq_truncatedLeg (u : ℂ) (Y : ℝ) (z : ℍ) :
    truncatedLineModel u Y z = truncatedLeg u Y z.re z.im := rfl

theorem heckeOp_sub (p : ℕ) (F G : ℝ → ℝ → ℂ) (x y : ℝ) :
    heckeOp p (fun x y => F x y - G x y) x y = heckeOp p F x y - heckeOp p G x y := by
  unfold heckeOp
  rw [Finset.sum_sub_distrib]
  ring

theorem natCast_mul_ofReal_cpow (p : ℕ) {y : ℝ} (hy : 0 ≤ y) (w : ℂ) :
    ((p : ℂ) * (y : ℂ)) ^ w = (p : ℂ) ^ w * (y : ℂ) ^ w := by
  have := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) hy w
  simpa using this

theorem ofReal_div_natCast_cpow_eisensteinHeckeMaassSelberg (p : ℕ) {y : ℝ} (hy : 0 ≤ y) (w : ℂ) :
    ((y : ℂ) / (p : ℂ)) ^ w = (y : ℂ) ^ w * ((p : ℂ) ^ w)⁻¹ := by
  have := Complex.mul_cpow_ofReal_nonneg hy (inv_nonneg.mpr (Nat.cast_nonneg p)) w
  push_cast at this
  rw [div_eq_mul_inv, this]
  congr 1
  exact Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)

/-- The Hecke operator on the indicator Weyl power `1_{Y < y} c y^w`. -/
theorem heckeOp_indicator_cpow {p : ℕ} (hp : 0 < p) (c w : ℂ) (Y x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeOp p (fun _ y => if Y < y then c * (y : ℂ) ^ w else 0) x y =
      c * (y : ℂ) ^ w *
        ((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ w * (if Y / p < y then 1 else 0) +
          (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) * ((p : ℂ) ^ w)⁻¹ *
            (if Y * p < y then 1 else 0)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold heckeOp
  beta_reduce
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hc1 : (Y < (p : ℝ) * y) ↔ (Y / p < y) := by rw [div_lt_iff₀ hpR, mul_comm]
  have hc2 : (Y < y / p) ↔ (Y * p < y) := (lt_div_iff₀ hpR)
  simp only [hc1, hc2]
  push_cast
  rw [natCast_mul_ofReal_cpow p hy.le w, ofReal_div_natCast_cpow_eisensteinHeckeMaassSelberg p hy.le w]
  split_ifs <;> ring

/-! ## The remainder -/

/-- One Weyl term of the Hecke remainder. -/
def weylRemainderTerm (p : ℕ) (u : ℂ) (epsilon : Bool) (Y y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
    (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon) *
    ((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon) *
        (if Y / p < y then 1 else 0) +
      (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) *
        ((p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon))⁻¹ *
        (if Y * p < y then 1 else 0))

/-- The remainder `T_p Λ^Y E_u − (p^u + p^{-u}) Λ^Y E_u`; it depends only on the height. -/
def heckeRemainder (p : ℕ) (u : ℂ) (Y y : ℝ) : ℂ :=
  ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) *
      (if Y < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0) -
    (weylRemainderTerm p u false Y y + weylRemainderTerm p u true Y y)

theorem constantTerm_scalar_eq (u : ℂ) (epsilon : Bool) (y : ℝ) :
    d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon y =
      d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
        (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon) := by
  simp only [d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one]

/-- **The Hecke operator on the truncation.** -/
theorem heckeOp_truncatedLeg {p : ℕ} (hp : p.Prime) (u : ℂ) (Y x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeOp p (fun x y => truncatedLeg u Y x y) x y =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * truncatedLeg u Y x y + heckeRemainder p u Y y := by
  have hp0 : 0 < p := hp.pos
  have hsplit : (fun x y : ℝ => truncatedLeg u Y x y) = fun x y : ℝ =>
      d4BMCompletedEisensteinCuspLeg .scalar u x y -
        ((if Y < y then d4BMCompletedEisensteinCuspConstantCoefficient u false *
            (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u false) else 0) +
          (if Y < y then d4BMCompletedEisensteinCuspConstantCoefficient u true *
            (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u true) else 0)) := by
    funext x y
    unfold truncatedLeg d4BMCompletedEisensteinCuspConstantPart
    rw [constantTerm_scalar_eq, constantTerm_scalar_eq]
    split_ifs <;> ring
  rw [hsplit, heckeOp_sub, heckeOp_add, heckeOp_cuspLeg hp u x hy,
    heckeOp_indicator_cpow hp0 _ _ Y x hy, heckeOp_indicator_cpow hp0 _ _ Y x hy]
  unfold heckeRemainder weylRemainderTerm truncatedLeg d4BMCompletedEisensteinCuspConstantPart
  rw [constantTerm_scalar_eq, constantTerm_scalar_eq]
  split_ifs <;> ring

/-- The Weyl scalar identity `p^{-1/2}(p^{w} + p·p^{-w}) = p^u + p^{-u}` for `w = ½ ± u`. -/
theorem weyl_scalar_identity {p : ℕ} (hp : 0 < p) (u : ℂ) (epsilon : Bool) :
    (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon) +
      (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) *
        ((p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon))⁻¹ =
      (p : ℂ) ^ u + (p : ℂ) ^ (-u) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
    exact_mod_cast this.ne'
  have hsqsq : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    exact Complex.ofReal_natCast p
  have hPu : (p : ℂ) ^ u ≠ 0 := by
    intro h
    exact hpC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hpw : (p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u epsilon) =
      (Real.sqrt p : ℂ) * (p : ℂ) ^ ((d4BMCuspSign epsilon : ℂ) * u) := by
    rw [d4BMCompletedEisensteinCuspWeylExponent, Complex.cpow_add _ _ hpC, sqrt_eq_cpow_half p]
  rw [hpw]
  cases epsilon
  · simp only [d4BMCuspSign, Bool.false_eq_true, if_false, Int.cast_neg, Int.cast_one, neg_mul,
      one_mul]
    rw [Complex.cpow_neg]
    push_cast
    generalize hPdef : (p : ℂ) ^ u = P at hPu ⊢
    rw [← hsqsq]
    have := hecke_weyl_scalar_neg hsq hPu
    rw [← this]
    ring
  · simp only [d4BMCuspSign, if_true, Int.cast_one, one_mul]
    rw [Complex.cpow_neg]
    push_cast
    generalize hPdef : (p : ℂ) ^ u = P at hPu ⊢
    rw [← hsqsq]
    have := hecke_weyl_scalar_pos hsq hPu
    rw [← this]
    ring

/-- Above height `pY` the remainder vanishes. -/
theorem heckeRemainder_eq_zero_of_gt {p : ℕ} (hp : 0 < p) (u : ℂ) {Y y : ℝ} (hY : 0 < Y)
    (hy : Y * p < y) : heckeRemainder p u Y y = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : Y < y := by
    have : Y ≤ Y * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    linarith
  have h2 : Y / p < y := by
    have : Y / p ≤ Y := by
      rw [div_le_iff₀ hpR]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    linarith
  unfold heckeRemainder weylRemainderTerm d4BMCompletedEisensteinCuspConstantPart
  rw [if_pos h1, if_pos h2, if_pos hy, constantTerm_scalar_eq, constantTerm_scalar_eq]
  have hf := weyl_scalar_identity hp u false
  have ht := weyl_scalar_identity hp u true
  linear_combination
    (-(d4BMCompletedEisensteinCuspConstantCoefficient u false *
      (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u false))) * hf +
    (-(d4BMCompletedEisensteinCuspConstantCoefficient u true *
      (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u true))) * ht

/-- Below height `Y/p` the remainder vanishes. -/
theorem heckeRemainder_eq_zero_of_le {p : ℕ} (hp : 0 < p) (u : ℂ) {Y y : ℝ} (hY : 0 < Y)
    (hy : y ≤ Y / p) : heckeRemainder p u Y y = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : ¬ Y < y := by
    have : Y / p ≤ Y := by
      rw [div_le_iff₀ hpR]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    linarith
  have h2 : ¬ Y / p < y := by linarith
  have h3 : ¬ Y * p < y := by
    have : Y ≤ Y * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    have : Y / p ≤ Y := by
      rw [div_le_iff₀ hpR]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    linarith
  unfold heckeRemainder weylRemainderTerm
  rw [if_neg h1, if_neg h2, if_neg h3]
  ring

/-- On the lower band `Y/p < y ≤ Y` the remainder is `−Σ_ε C_ε p^{-1/2} p^{w_ε} y^{w_ε}`. -/
def lowerBandRemainder (p : ℕ) (u : ℂ) (y : ℝ) : ℂ :=
  -(d4BMCompletedEisensteinCuspConstantCoefficient u false *
      (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u false) *
      ((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u false)) +
    d4BMCompletedEisensteinCuspConstantCoefficient u true *
      (y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u true) *
      ((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u true)))

theorem heckeRemainder_eq_lowerBand {p : ℕ} (hp : 0 < p) (u : ℂ) {Y y : ℝ} (hY : 0 < Y)
    (hy1 : Y / p < y) (hy2 : y ≤ Y) : heckeRemainder p u Y y = lowerBandRemainder p u y := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hYnn : 0 ≤ Y := hY.le
  have h1 : ¬ Y < y := by linarith
  have h3 : ¬ Y * p < y := by
    have : Y ≤ Y * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith [hYnn]
    linarith
  unfold heckeRemainder weylRemainderTerm lowerBandRemainder
  rw [if_neg h1, if_pos hy1, if_neg h3]
  ring

/-- On the upper band `Y < y ≤ pY` the remainder is `(p^u+p^{-u}) c_u(y) − Σ_ε C_ε p^{-1/2} p^{w_ε} y^{w_ε}`. -/
def upperBandRemainder (p : ℕ) (u : ℂ) (y : ℝ) : ℂ :=
  ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * d4BMCompletedEisensteinCuspConstantPart .scalar u y +
    lowerBandRemainder p u y

theorem heckeRemainder_eq_upperBand {p : ℕ} (hp : 0 < p) (u : ℂ) {Y y : ℝ} (hY : 0 < Y)
    (hy1 : Y < y) (hy2 : y ≤ Y * p) : heckeRemainder p u Y y = upperBandRemainder p u y := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hYnn : 0 ≤ Y := hY.le
  have h2 : Y / p < y := by
    have : Y / p ≤ Y := by
      rw [div_le_iff₀ hpR]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith [hYnn]
    linarith
  have h3 : ¬ Y * p < y := by linarith
  unfold heckeRemainder weylRemainderTerm upperBandRemainder lowerBandRemainder
  rw [if_pos hy1, if_pos h2, if_neg h3]
  ring

/-! ## Bands of the fundamental domain in coordinates -/

/-- The band rectangle `[−½, ½] × (Y₁, Y₂]`. -/
def bandRect (Y₁ Y₂ : ℝ) : Set (ℝ × ℝ) := unitIcc ×ˢ Ioc Y₁ Y₂

theorem measurableSet_bandRect (Y₁ Y₂ : ℝ) : MeasurableSet (bandRect Y₁ Y₂) :=
  measurableSet_Icc.prod measurableSet_Ioc

theorem volume_bandRect_ne_top (Y₁ Y₂ : ℝ) : volume (bandRect Y₁ Y₂) ≠ ⊤ := by
  rw [bandRect, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Ioc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem bandRect_subset_closed (Y₁ Y₂ : ℝ) : bandRect Y₁ Y₂ ⊆ unitIcc ×ˢ Icc Y₁ Y₂ :=
  Set.prod_mono subset_rfl Set.Ioc_subset_Icc_self

theorem closedRect_subset_pos {Y₁ Y₂ : ℝ} (hY : 0 < Y₁) :
    unitIcc ×ˢ Icc Y₁ Y₂ ⊆ {p : ℝ × ℝ | 0 < p.2} := by
  intro q hq
  exact lt_of_lt_of_le hY hq.2.1

/-- Between heights `1 ≤ Y₁ < Y₂` the fundamental domain is the band rectangle. -/
theorem coord_mem_bandRect_iff {Y₁ Y₂ : ℝ} (hY : 1 ≤ Y₁) (z : ℍ) :
    (z.re, z.im) ∈ bandRect Y₁ Y₂ ↔ z ∈ fd ∧ (Y₁ < z.im ∧ z.im ≤ Y₂) := by
  constructor
  · rintro ⟨hx, hy⟩
    simp only [unitIcc, Set.mem_Icc] at hx
    simp only [Set.mem_Ioc] at hy
    refine ⟨⟨?_, ?_⟩, hy⟩
    · rw [Complex.normSq_apply]
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      nlinarith [hx.1, hx.2, hy.1]
    · rw [abs_le]; exact hx
  · rintro ⟨hz, hy⟩
    refine ⟨?_, hy⟩
    have := hz.2
    rw [abs_le] at this
    exact this

theorem setOf_coord_bandRect {Y₁ Y₂ : ℝ} (hY : 1 ≤ Y₁) :
    {z : ℍ | (z.re, z.im) ∈ bandRect Y₁ Y₂} = fd ∩ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} := by
  ext z
  simp only [mem_setOf_eq, mem_inter_iff]
  exact coord_mem_bandRect_iff hY z

theorem measurableSet_band (Y₁ Y₂ : ℝ) : MeasurableSet {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} :=
  (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable).inter
    (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)

/-- **The band of the fundamental domain in coordinates.** -/
theorem setIntegral_fd_band_eq {Y₁ Y₂ : ℝ} (hY : 1 ≤ Y₁) (F : ℝ × ℝ → ℂ) :
    ∫ z in fd ∩ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂}, F (z.re, z.im) =
      ∫ q in bandRect Y₁ Y₂, F q / ((q.2 : ℝ) : ℂ) ^ 2 := by
  rw [← setOf_coord_bandRect hY]
  exact setIntegral_coord_eq (measurableSet_bandRect Y₁ Y₂)
    (fun q hq => lt_trans (by linarith : (0 : ℝ) < Y₁) hq.2.1) F

/-- Fubini on a band for a function continuous on the closed rectangle. -/
theorem setIntegral_bandRect_eq_iterated {Y₁ Y₂ : ℝ} {G : ℝ × ℝ → ℂ}
    (hG : ContinuousOn G (unitIcc ×ˢ Icc Y₁ Y₂)) :
    ∫ q in bandRect Y₁ Y₂, G q = ∫ y in Ioc Y₁ Y₂, ∫ x in unitIcc, G (x, y) := by
  have hint : IntegrableOn G (bandRect Y₁ Y₂) :=
    (hG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (bandRect_subset_closed Y₁ Y₂)
  exact setIntegral_prod_eq_iterated hint

/-! ## Band integrals against the line model and against the tail -/

/-- Integrating a height function against the line model over a band gives the constant term. -/
theorem setIntegral_band_mul_line (v : ℂ) {Y₁ Y₂ : ℝ} (hY : 1 ≤ Y₁) (h : ℝ → ℂ)
    (hh : ContinuousOn h (Icc Y₁ Y₂)) :
    ∫ z in fd, (if Y₁ < z.im ∧ z.im ≤ Y₂ then h z.im * eisensteinLineModel v z else 0) =
      ∫ y in Ioc Y₁ Y₂,
        h y * d4BMCompletedEisensteinCuspConstantPart .scalar v y / ((y : ℝ) : ℂ) ^ 2 := by
  have hY0 : 0 < Y₁ := by linarith
  have hind : (fun z : ℍ => if Y₁ < z.im ∧ z.im ≤ Y₂ then h z.im * eisensteinLineModel v z else 0) =
      {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂}.indicator
        (fun z => (fun q : ℝ × ℝ => h q.2 * d4BMCompletedEisensteinCuspLeg .scalar v q.1 q.2)
          (z.re, z.im)) := by
    funext z
    by_cases hz : Y₁ < z.im ∧ z.im ≤ Y₂
    · rw [if_pos hz, Set.indicator_of_mem (show z ∈ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} from hz)]
      rfl
    · rw [if_neg hz, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} from hz)]
  rw [hind, setIntegral_indicator (measurableSet_band Y₁ Y₂), setIntegral_fd_band_eq hY
    (fun q : ℝ × ℝ => h q.2 * d4BMCompletedEisensteinCuspLeg .scalar v q.1 q.2)]
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ => h q.2 * d4BMCompletedEisensteinCuspLeg .scalar v q.1 q.2 /
        ((q.2 : ℝ) : ℂ) ^ 2) (unitIcc ×ˢ Icc Y₁ Y₂) := by
    have hc : ContinuousOn (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) (unitIcc ×ˢ Icc Y₁ Y₂) :=
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn
    have hh' : ContinuousOn (fun q : ℝ × ℝ => h q.2) (unitIcc ×ˢ Icc Y₁ Y₂) :=
      hh.comp continuous_snd.continuousOn (fun q hq => hq.2)
    refine (hh'.mul ((continuousOn_cuspLeg_pair v).mono (closedRect_subset_pos hY0))).div
      (hc.pow 2) ?_
    intro q hq
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hY0 hq.2.1)))
  rw [setIntegral_bandRect_eq_iterated hcont]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1.le
  have : (fun x : ℝ => h y * d4BMCompletedEisensteinCuspLeg .scalar v x y / ((y : ℝ) : ℂ) ^ 2) =
      fun x : ℝ => (h y / ((y : ℝ) : ℂ) ^ 2) * d4BMCompletedEisensteinCuspLeg .scalar v x y := by
    funext x; ring
  simp only
  rw [this, integral_const_mul, setIntegral_unitIcc_cuspLeg hy0 v]
  ring

/-- Integrating a height function against the tail over a band gives zero. -/
theorem setIntegral_band_mul_tail_eq_zero (v : ℂ) {Y₁ Y₂ : ℝ} (hY : 1 ≤ Y₁) (h : ℝ → ℂ)
    (hh : ContinuousOn h (Icc Y₁ Y₂)) :
    ∫ z in fd, (if Y₁ < z.im ∧ z.im ≤ Y₂ then
      h z.im * d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im else 0) = 0 := by
  have hY0 : 0 < Y₁ := by linarith
  have hind : (fun z : ℍ => if Y₁ < z.im ∧ z.im ≤ Y₂ then
      h z.im * d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im else 0) =
      {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂}.indicator
        (fun z => (fun q : ℝ × ℝ => h q.2 * d4BMCompletedEisensteinCuspTailPart .scalar v q.1 q.2)
          (z.re, z.im)) := by
    funext z
    by_cases hz : Y₁ < z.im ∧ z.im ≤ Y₂
    · rw [if_pos hz, Set.indicator_of_mem (show z ∈ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} from hz)]
    · rw [if_neg hz, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} from hz)]
  rw [hind, setIntegral_indicator (measurableSet_band Y₁ Y₂), setIntegral_fd_band_eq hY
    (fun q : ℝ × ℝ => h q.2 * d4BMCompletedEisensteinCuspTailPart .scalar v q.1 q.2)]
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ => h q.2 * d4BMCompletedEisensteinCuspTailPart .scalar v q.1 q.2 /
        ((q.2 : ℝ) : ℂ) ^ 2) (unitIcc ×ˢ Icc Y₁ Y₂) := by
    have hc : ContinuousOn (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) (unitIcc ×ˢ Icc Y₁ Y₂) :=
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn
    have hh' : ContinuousOn (fun q : ℝ × ℝ => h q.2) (unitIcc ×ˢ Icc Y₁ Y₂) :=
      hh.comp continuous_snd.continuousOn (fun q hq => hq.2)
    refine (hh'.mul ((continuousOn_cuspTailPart_pair v).mono (closedRect_subset_pos hY0))).div
      (hc.pow 2) ?_
    intro q hq
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hY0 hq.2.1)))
  rw [setIntegral_bandRect_eq_iterated hcont]
  have hinner : ∀ y ∈ Ioc Y₁ Y₂,
      (∫ x in unitIcc, h y * d4BMCompletedEisensteinCuspTailPart .scalar v x y /
        ((y : ℝ) : ℂ) ^ 2) = 0 := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1.le
    have : (fun x : ℝ => h y * d4BMCompletedEisensteinCuspTailPart .scalar v x y /
        ((y : ℝ) : ℂ) ^ 2) =
        fun x : ℝ => (h y / ((y : ℝ) : ℂ) ^ 2) * d4BMCompletedEisensteinCuspTailPart .scalar v x y := by
      funext x; ring
    rw [this, integral_const_mul, setIntegral_unitIcc_cuspTailPart hy0 v, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioc hinner]
  simp

/-! ## Continuity and bounds of the band remainders -/

theorem continuousOn_ofReal_cpow_const {a b : ℝ} (ha : 0 < a) (w : ℂ) :
    ContinuousOn (fun y : ℝ => ((y : ℝ) : ℂ) ^ w) (Icc a b) := by
  have hc : ContinuousOn (fun y : ℝ => ((y : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn
  exact hc.cpow_const fun y hy => Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le ha hy.1)

theorem continuousOn_lowerBandRemainder (p : ℕ) (u : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (lowerBandRemainder p u) (Icc a b) := by
  unfold lowerBandRemainder
  exact (((continuousOn_const.mul (continuousOn_ofReal_cpow_const ha _)).mul continuousOn_const).add
    ((continuousOn_const.mul (continuousOn_ofReal_cpow_const ha _)).mul continuousOn_const)).neg

theorem continuousOn_cuspConstantPart_height (u : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => d4BMCompletedEisensteinCuspConstantPart .scalar u y) (Icc a b) := by
  simp_rw [cuspConstantPart_eq_msAB]
  exact (continuousOn_const.mul (continuousOn_ofReal_cpow_const ha _)).add
    (continuousOn_const.mul (continuousOn_ofReal_cpow_const ha _))

theorem continuousOn_upperBandRemainder (p : ℕ) (u : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (upperBandRemainder p u) (Icc a b) := by
  unfold upperBandRemainder
  exact (continuousOn_const.mul (continuousOn_cuspConstantPart_height u ha)).add
    (continuousOn_lowerBandRemainder p u ha)

theorem measurable_lowerBandRemainder_im (p : ℕ) (u : ℂ) :
    Measurable (fun z : ℍ => lowerBandRemainder p u z.im) := by
  have hm : Measurable (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable
  unfold lowerBandRemainder
  exact (((measurable_const.mul (hm.pow_const _)).mul measurable_const).add
    ((measurable_const.mul (hm.pow_const _)).mul measurable_const)).neg

theorem measurable_upperBandRemainder_im (p : ℕ) (u : ℂ) :
    Measurable (fun z : ℍ => upperBandRemainder p u z.im) := by
  unfold upperBandRemainder
  exact (measurable_const.mul (measurable_cuspConstantPart_im u)).add
    (measurable_lowerBandRemainder_im p u)

theorem measurable_cuspTailPart_coord (v : ℂ) :
    Measurable (fun z : ℍ => d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im) := by
  have : (fun z : ℍ => d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im) =
      fun z : ℍ => eisensteinLineModel v z -
        d4BMCompletedEisensteinCuspConstantPart .scalar v z.im := by
    funext z
    unfold eisensteinLineModel d4BMCompletedEisensteinCuspLeg
    ring
  rw [this]
  exact (continuous_eisensteinLineModel v).measurable.sub (measurable_cuspConstantPart_im v)

theorem measurable_heckeRemainder_im (p : ℕ) (u : ℂ) (Y : ℝ) :
    Measurable (fun z : ℍ => heckeRemainder p u Y z.im) := by
  have hm : Measurable (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable
  have him : Measurable (fun z : ℍ => z.im) := UpperHalfPlane.continuous_im.measurable
  unfold heckeRemainder weylRemainderTerm
  refine (measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const him)
    (measurable_cuspConstantPart_im u) measurable_const)).sub ?_
  refine Measurable.add ?_ ?_
  · refine ((measurable_const.mul (hm.pow_const _)).mul ?_)
    refine Measurable.add ?_ ?_
    · exact measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const him)
        measurable_const measurable_const)
    · exact measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const him)
        measurable_const measurable_const)
  · refine ((measurable_const.mul (hm.pow_const _)).mul ?_)
    refine Measurable.add ?_ ?_
    · exact measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const him)
        measurable_const measurable_const)
    · exact measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const him)
        measurable_const measurable_const)

/-- The remainder is bounded on the whole height axis. -/
theorem exists_bound_heckeRemainder {p : ℕ} (hp : 0 < p) (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, ‖heckeRemainder p u Y y‖ ≤ M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hYp : 0 < Y / p := by positivity
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_lowerBandRemainder p u (a := Y / p) (b := Y) hYp)
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_upperBandRemainder p u (a := Y) (b := Y * p) hY)
  refine ⟨max (max M₁ M₂) 0, le_max_right _ _, fun y => ?_⟩
  by_cases h1 : y ≤ Y / p
  · rw [heckeRemainder_eq_zero_of_le hp u hY h1, norm_zero]
    exact le_max_right _ _
  by_cases h2 : y ≤ Y
  · rw [heckeRemainder_eq_lowerBand hp u hY (lt_of_not_ge h1) h2]
    exact (hM₁ y ⟨(lt_of_not_ge h1).le, h2⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  by_cases h3 : y ≤ Y * p
  · rw [heckeRemainder_eq_upperBand hp u hY (lt_of_not_ge h2) h3]
    exact (hM₂ y ⟨(lt_of_not_ge h2).le, h3⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  · rw [heckeRemainder_eq_zero_of_gt hp u hY (lt_of_not_ge h3), norm_zero]
    exact le_max_right _ _

/-! ## The remainder pairing -/

theorem heckeRemainder_mul_trunc_eq {p : ℕ} (hp : 0 < p) (u v : ℂ) {Y : ℝ} (hY : 0 < Y) (z : ℍ) :
    heckeRemainder p u Y z.im * truncatedLineModel v Y z =
      (if Y / p < z.im ∧ z.im ≤ Y then lowerBandRemainder p u z.im * eisensteinLineModel v z
        else 0) +
      (if Y < z.im ∧ z.im ≤ Y * p then
        upperBandRemainder p u z.im * d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im
        else 0) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hYp : Y / p ≤ Y := by
    rw [div_le_iff₀ hpR]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hYpY : Y ≤ Y * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  by_cases h1 : z.im ≤ Y / p
  · rw [heckeRemainder_eq_zero_of_le hp u hY h1, zero_mul, if_neg (by intro h; linarith [h.1]),
      if_neg (by intro h; linarith [h.1])]
    simp
  by_cases h2 : z.im ≤ Y
  · have hnot : ¬ Y < z.im := not_lt.mpr h2
    rw [heckeRemainder_eq_lowerBand hp u hY (lt_of_not_ge h1) h2,
      if_pos ⟨lt_of_not_ge h1, h2⟩, if_neg (by intro h; linarith [h.1])]
    unfold truncatedLineModel
    rw [if_neg hnot, sub_zero, add_zero]
  by_cases h3 : z.im ≤ Y * p
  · have hlt : Y < z.im := lt_of_not_ge h2
    rw [heckeRemainder_eq_upperBand hp u hY hlt h3, if_neg (by intro h; linarith [h.2]),
      if_pos ⟨hlt, h3⟩]
    unfold truncatedLineModel eisensteinLineModel d4BMCompletedEisensteinCuspLeg
    rw [if_pos hlt, add_sub_cancel_left, zero_add]
  · rw [heckeRemainder_eq_zero_of_gt hp u hY (lt_of_not_ge h3), zero_mul,
      if_neg (by intro h; linarith [h.2]), if_neg (by intro h; linarith [h.2])]
    simp

/-- **The remainder pairing is a lower-band integral.**  For `Y ≥ p`,
`∫_𝒟 R_p(u,Y,y)·Λ^Y E_v = ∫_{Y/p}^{Y} ρ_p(u,y) c_v(y) dy/y²` with `ρ_p` the lower-band remainder. -/
theorem setIntegral_heckeRemainder_mul_trunc {p : ℕ} (hp : 0 < p) (u v : ℂ) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    ∫ z in fd, heckeRemainder p u Y z.im * truncatedLineModel v Y z =
      ∫ y in Ioc (Y / p) Y,
        lowerBandRemainder p u y * d4BMCompletedEisensteinCuspConstantPart .scalar v y /
          ((y : ℝ) : ℂ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hY0 : 0 < Y := lt_of_lt_of_le hpR hY
  have hYp1 : 1 ≤ Y / p := by rw [le_div_iff₀ hpR]; linarith
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y / p := by positivity
  rw [setIntegral_congr_fun isClosed_fd.measurableSet
    (fun z _ => heckeRemainder_mul_trunc_eq hp u v hY0 z)]
  -- integrability of the two brackets on `𝒟`
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun q : ℝ × ℝ => lowerBandRemainder p u q.2 * d4BMCompletedEisensteinCuspLeg .scalar v q.1 q.2)
    (s := unitIcc ×ˢ Icc (Y / p) Y)
    (((continuousOn_lowerBandRemainder p u hYp).comp continuous_snd.continuousOn
      (fun q hq => hq.2)).mul ((continuousOn_cuspLeg_pair v).mono (closedRect_subset_pos hYp)))
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun q : ℝ × ℝ => upperBandRemainder p u q.2 *
      d4BMCompletedEisensteinCuspTailPart .scalar v q.1 q.2)
    (s := unitIcc ×ˢ Icc Y (Y * p))
    (((continuousOn_upperBandRemainder p u hY0).comp continuous_snd.continuousOn
      (fun q hq => hq.2)).mul ((continuousOn_cuspTailPart_pair v).mono (closedRect_subset_pos hY0)))
  have hm1 : Measurable (fun z : ℍ => if Y / p < z.im ∧ z.im ≤ Y then
      lowerBandRemainder p u z.im * eisensteinLineModel v z else 0) :=
    Measurable.ite (measurableSet_band _ _)
      ((measurable_lowerBandRemainder_im p u).mul (continuous_eisensteinLineModel v).measurable)
      measurable_const
  have hm2 : Measurable (fun z : ℍ => if Y < z.im ∧ z.im ≤ Y * p then
      upperBandRemainder p u z.im * d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im
      else 0) :=
    Measurable.ite (measurableSet_band _ _)
      ((measurable_upperBandRemainder_im p u).mul (measurable_cuspTailPart_coord v))
      measurable_const
  have hi1 : IntegrableOn (fun z : ℍ => if Y / p < z.im ∧ z.im ≤ Y then
      lowerBandRemainder p u z.im * eisensteinLineModel v z else 0) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hm1.aestronglyMeasurable
      (M := max C₁ 0) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hzfd => ?_)
    by_cases hz : Y / p < z.im ∧ z.im ≤ Y
    · rw [if_pos hz]
      have hq : (z.re, z.im) ∈ unitIcc ×ˢ Icc (Y / p) Y :=
        ⟨((coord_mem_bandRect_iff hYp1 z).mpr ⟨hzfd, hz⟩).1, ⟨hz.1.le, hz.2⟩⟩
      exact (hC₁ _ hq).trans (le_max_left _ _)
    · rw [if_neg hz, norm_zero]; exact le_max_right _ _
  have hi2 : IntegrableOn (fun z : ℍ => if Y < z.im ∧ z.im ≤ Y * p then
      upperBandRemainder p u z.im * d4BMCompletedEisensteinCuspTailPart .scalar v z.re z.im
      else 0) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hm2.aestronglyMeasurable
      (M := max C₂ 0) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hzfd => ?_)
    by_cases hz : Y < z.im ∧ z.im ≤ Y * p
    · rw [if_pos hz]
      have hq : (z.re, z.im) ∈ unitIcc ×ˢ Icc Y (Y * p) :=
        ⟨((coord_mem_bandRect_iff hY1 z).mpr ⟨hzfd, hz⟩).1, ⟨hz.1.le, hz.2⟩⟩
      exact (hC₂ _ hq).trans (le_max_left _ _)
    · rw [if_neg hz, norm_zero]; exact le_max_right _ _
  rw [integral_add hi1 hi2, setIntegral_band_mul_line v hYp1 _ (continuousOn_lowerBandRemainder p u hYp),
    setIntegral_band_mul_tail_eq_zero v hY1 _ (continuousOn_upperBandRemainder p u hY0), add_zero]

/-! ## The Hecke–Maass–Selberg relation -/

/-- The Hecke transform of the truncated line model as a function on `ℍ`. -/
def heckeTruncated (p : ℕ) (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  heckeOp p (fun x y => truncatedLeg u Y x y) z.re z.im

theorem heckeTruncated_eq {p : ℕ} (hp : p.Prime) (u : ℂ) (Y : ℝ) (z : ℍ) :
    heckeTruncated p u Y z =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * truncatedLineModel u Y z + heckeRemainder p u Y z.im := by
  unfold heckeTruncated
  rw [heckeOp_truncatedLeg hp u Y z.re z.im_pos, truncatedLineModel_eq_truncatedLeg]

/-- **Hecke–Maass–Selberg relation.**  For every prime `p`, all parameters `u, v` and every height
`Y ≥ p`,
`∫_𝒟 (T_pΛ^Y E_u)·Λ^Y E_v = (p^u + p^{-u})·∫_𝒟 Λ^Y E_u·Λ^Y E_v + ∫_{Y/p}^{Y} ρ_p(u,y) c_v(y) dy/y²`,
where `ρ_p(u,y) = −p^{-1/2}(Λ(2u) p^{½+u} y^{½+u} + Λ(1+2u) p^{½−u} y^{½−u})`. -/
theorem heckeMaassSelberg {p : ℕ} (hp : p.Prime) (u v : ℂ) {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    ∫ z in fd, heckeTruncated p u Y z * truncatedLineModel v Y z =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * truncatedPairing Y u v +
        ∫ y in Ioc (Y / p) Y,
          lowerBandRemainder p u y * d4BMCompletedEisensteinCuspConstantPart .scalar v y /
            ((y : ℝ) : ℂ) ^ 2 := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hY0 : 0 < Y := lt_of_lt_of_le hpR hY
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    linarith
  have hpt : ∀ z : ℍ, heckeTruncated p u Y z * truncatedLineModel v Y z =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * (truncatedLineModel u Y z * truncatedLineModel v Y z) +
        heckeRemainder p u Y z.im * truncatedLineModel v Y z := by
    intro z
    rw [heckeTruncated_eq hp u Y z]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hi1 : IntegrableOn (fun z : ℍ => ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) *
      (truncatedLineModel u Y z * truncatedLineModel v Y z)) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      (measurable_const.mul ((measurable_truncatedLineModel u Y).mul
        (measurable_truncatedLineModel v Y))).aestronglyMeasurable
      (M := ‖(p : ℂ) ^ u + (p : ℂ) ^ (-u)‖ * (truncBound' u Y * truncBound' v Y)) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz => ?_)
    rw [norm_mul, norm_mul]
    have h1 := norm_truncatedLineModel_le_truncBound' u hY1 hz
    have h2 := norm_truncatedLineModel_le_truncBound' v hY1 hz
    have hBu : 0 ≤ truncBound' u Y := (norm_nonneg _).trans h1
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hBu) (norm_nonneg _)
  have hi2 : IntegrableOn (fun z : ℍ => heckeRemainder p u Y z.im * truncatedLineModel v Y z) fd := by
    obtain ⟨M, hM0, hM⟩ := exists_bound_heckeRemainder hp0 u hY0
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      ((measurable_heckeRemainder_im p u Y).mul (measurable_truncatedLineModel v Y)).aestronglyMeasurable
      (M := M * truncBound' v Y) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz => ?_)
    rw [norm_mul]
    exact mul_le_mul (hM z.im) (norm_truncatedLineModel_le_truncBound' v hY1 hz) (norm_nonneg _) hM0
  rw [integral_add hi1 hi2, integral_const_mul, setIntegral_heckeRemainder_mul_trunc hp0 u v hY]
  rfl

end

end RHTower
