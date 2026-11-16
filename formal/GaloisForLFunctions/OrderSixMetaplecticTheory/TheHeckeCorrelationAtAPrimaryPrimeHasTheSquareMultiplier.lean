import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicTwistAtTwoOfTheThetaSquareHasADoublePole

/-!
# The Hecke correlation at a primary prime has the square multiplier

The Hecke-at-four correlation for an arbitrary primary prime `p` of `ℤ[ω]` (`p` prime, `p ≡ 1 mod λ²`). With
`A_p = diag(√p, 1/√p)` (`z ↦ pz`, `v ↦ |p|v`) and any `Θ` of multiplier `κ` on `Γ(3)`, the correlation
`F_Θ(w) = Θ(A_pw) Θ(A_p⁻¹w)` transforms under

`Γ_p = Γ(3) ∩ {p ∣ b, p ∣ c}`   (`PrimaryPrime.heckeGroup`)

with the multiplier `κ²` (`PrimaryPrime.heckeCorrelation_automorphy`): for `γ = [[a, pb], [pc, d]]`,
`A_pγA_p⁻¹ = [[a, p²b], [c, d]]` and `A_p⁻¹γA_p = [[a, b], [p²c, d]]` lie in `Γ(3)` and
`(c/a)₃(p²c/a)₃ = (pc/a)₃²`: the `p`-adic nebentypus `(p/a)₃^{∓1}` of the two dilates cancels.

The constant term of `S_a(pu)S_b(u)` over the period parallelogram is `|P| Σ_h a_h b_{−ph}`
(`integral_cuspCharacterSeries_mul_dilate`), for any nonzero multiplier.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

/-- `κ(M) = (c/a)₃`. -/
theorem complexCharacter_eq_symbol (M : levelThree) :
    complexCharacter M = ringComplex (symbol ((M : SL(2, O)) 1 0) ((M : SL(2, O)) 0 0)) := rfl

/-- A primary prime of `ℤ[ω]`. -/
structure PrimaryPrime where
  p : O
  prime : Prime p
  primary : lambda ^ 2 ∣ p - 1

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem ne_zero : P.p ≠ 0 := P.prime.ne_zero

theorem three_dvd_sub_one : (3 : O) ∣ P.p - 1 := three_dvd_primary_sub_one _ P.primary

theorem isCoprime_three : IsCoprime (3 : O) P.p := by
  obtain ⟨k, hk⟩ := P.three_dvd_sub_one
  exact ⟨-k, 1, by linear_combination hk⟩

theorem ringComplex_ne_zero : ringComplex P.p ≠ 0 := MetaplecticMobiusDescent.CubicEisenstein.ringComplex_ne_zero P.ne_zero

theorem norm_pos : 0 < ‖ringComplex P.p‖ := norm_pos_iff.mpr P.ringComplex_ne_zero

/-- A square root `√p` of `p` in `ℂ`. -/
def root : ℂ := ringComplex P.p ^ (1 / 2 : ℂ)

theorem root_sq : P.root ^ 2 = ringComplex P.p := by
  rw [root, ← Complex.cpow_nat_mul]
  norm_num

theorem root_ne_zero : P.root ≠ 0 := by
  intro h
  have h2 := P.root_sq
  rw [h, zero_pow two_ne_zero] at h2
  exact P.ringComplex_ne_zero h2.symm

theorem root_inv : P.root⁻¹ = P.root / ringComplex P.p := by
  rw [← P.root_sq]
  field_simp [P.root_ne_zero]

theorem normSq_root : Complex.normSq P.root = ‖ringComplex P.p‖ := by
  rw [Complex.normSq_eq_norm_sq, ← norm_pow, P.root_sq]

/-- `A_p = diag(√p, 1/√p)`. -/
def dilation : SL(2, ℂ) := complexDiagonal P.root P.root_ne_zero

/-- `A_p⁻¹ = diag(1/√p, √p)`. -/
def contraction : SL(2, ℂ) := complexDiagonal P.root⁻¹ (inv_ne_zero P.root_ne_zero)

/-- `A_p·(z, v) = (pz, |p|v)`. -/
theorem dilation_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.dilation • upperPoint z v hv =
      upperPoint (ringComplex P.p * z) (‖ringComplex P.p‖ * v) (mul_pos P.norm_pos hv) := by
  rw [dilation, complexDiagonal_action]
  apply upperPoint_congr
  · rw [P.root_sq]
  · rw [P.normSq_root]

/-- `A_p⁻¹·(z, v) = (z/p, v/|p|)`. -/
theorem contraction_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.contraction • upperPoint z v hv =
      upperPoint (z / ringComplex P.p) (v / ‖ringComplex P.p‖) (div_pos hv P.norm_pos) := by
  rw [contraction, complexDiagonal_action]
  apply upperPoint_congr
  · rw [inv_pow, P.root_sq]
    ring
  · rw [map_inv₀, P.normSq_root]
    ring

/-- `Γ_p = Γ(3) ∩ {p ∣ b, p ∣ c}`. -/
def heckeGroup : Subgroup levelThree where
  carrier := {γ | P.p ∣ (γ : SL(2, O)) 0 1 ∧ P.p ∣ (γ : SL(2, O)) 1 0}
  one_mem' := by simp
  mul_mem' := by
    rintro γ δ ⟨hb, hc⟩ ⟨hb', hc'⟩
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    exact ⟨dvd_add (hb'.mul_left _) (hb.mul_right _), dvd_add (hc.mul_right _) (hc'.mul_left _)⟩
  inv_mem' := by
    rintro γ ⟨hb, hc⟩
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨hb.neg_right, hc.neg_right⟩

end PrimaryPrime

/-- The level-three matrix `[[a, pb], [pc, d]]` of `Γ_p`. -/
structure HeckeEntries (P : PrimaryPrime) where
  a : O
  b : O
  c : O
  d : O
  det : a * d - P.p ^ 2 * (b * c) = 1
  ha : (3 : O) ∣ a - 1
  hb : (3 : O) ∣ b
  hc : (3 : O) ∣ c
  hd : (3 : O) ∣ d - 1

namespace HeckeEntries

variable {P : PrimaryPrime} (e : HeckeEntries P)

/-- `γ = [[a, pb], [pc, d]]`. -/
def mat : levelThree :=
  ⟨⟨!![e.a, P.p * e.b; P.p * e.c, e.d], by rw [Matrix.det_fin_two_of]; linear_combination e.det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using e.ha
      · simpa using e.hb.mul_left P.p
      · simpa using e.hc.mul_left P.p
      · simpa using e.hd)⟩

/-- `A_pγA_p⁻¹ = [[a, p²b], [c, d]]`. -/
def up : levelThree :=
  ⟨⟨!![e.a, P.p ^ 2 * e.b; e.c, e.d], by rw [Matrix.det_fin_two_of]; linear_combination e.det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using e.ha
      · simpa using e.hb.mul_left (P.p ^ 2)
      · simpa using e.hc
      · simpa using e.hd)⟩

/-- `A_p⁻¹γA_p = [[a, b], [p²c, d]]`. -/
def down : levelThree :=
  ⟨⟨!![e.a, e.b; P.p ^ 2 * e.c, e.d], by rw [Matrix.det_fin_two_of]; linear_combination e.det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using e.ha
      · simpa using e.hb
      · simpa using e.hc.mul_left (P.p ^ 2)
      · simpa using e.hd)⟩

theorem dilation_mul : P.dilation * complexMatrix e.mat = complexMatrix e.up * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, mat, up,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [P.root_inv])
  all_goals (try field_simp)

theorem contraction_mul : P.contraction * complexMatrix e.mat = complexMatrix e.down * P.contraction := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, complexDiagonal, complexMatrix_apply, mat, down,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [P.root_inv])
  all_goals (try field_simp)

/-- The `p`-adic nebentypus cancels: `κ(A_pγA_p⁻¹) κ(A_p⁻¹γA_p) = κ(γ)²`. -/
theorem character_up_mul_down :
    complexCharacter e.up * complexCharacter e.down = complexCharacter e.mat ^ 2 := by
  have h1 : ((e.up : levelThree) : SL(2, O)) 1 0 = e.c := rfl
  have h2 : ((e.up : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  have h3 : ((e.down : levelThree) : SL(2, O)) 1 0 = P.p ^ 2 * e.c := rfl
  have h4 : ((e.down : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  have h5 : ((e.mat : levelThree) : SL(2, O)) 1 0 = P.p * e.c := rfl
  have h6 : ((e.mat : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, complexCharacter_eq_symbol, h1, h2, h3, h4, h5, h6]
  rw [← map_mul, ← map_pow, ← symbol_mul_numerator, pow_two (symbol (P.p * e.c) e.a), ← symbol_mul_numerator]
  congr 2
  ring

end HeckeEntries

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- Every element of `Γ_p` has the form `[[a, pb], [pc, d]]`. -/
theorem exists_entries_of_mem (γ : levelThree) (hγ : γ ∈ P.heckeGroup) :
    ∃ e : HeckeEntries P, e.mat = γ := by
  obtain ⟨b, hb⟩ := hγ.1
  obtain ⟨c, hc⟩ := hγ.2
  have hdet : (γ : SL(2, O)) 0 0 * (γ : SL(2, O)) 1 1 - (γ : SL(2, O)) 0 1 * (γ : SL(2, O)) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (γ : SL(2, O)).det_coe
  have h01 := levelThree_entry γ 0 1
  have h10 := levelThree_entry γ 1 0
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_false, sub_zero] at h01 h10
  rw [hb] at h01
  rw [hc] at h10
  refine ⟨⟨(γ : SL(2, O)) 0 0, b, c, (γ : SL(2, O)) 1 1, ?_, by simpa using levelThree_entry γ 0 0,
    P.isCoprime_three.dvd_of_dvd_mul_left h01, P.isCoprime_three.dvd_of_dvd_mul_left h10,
    by simpa using levelThree_entry γ 1 1⟩, ?_⟩
  · rw [hb, hc] at hdet
    linear_combination hdet
  · apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [HeckeEntries.mat, hb, hc]

/-- The Hecke correlation `F_Θ(w) = Θ(A_pw) Θ(A_p⁻¹w)`. -/
def heckeCorrelation (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  Θ (P.dilation • w) * Θ (P.contraction • w)

/-- **The Hecke correlation at `p` has the multiplier `κ²` on `Γ_p`.** -/
theorem heckeCorrelation_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (γ : levelThree) (hγ : γ ∈ P.heckeGroup) (w : HyperbolicSpace) :
    P.heckeCorrelation Θ (complexMatrix γ • w) = complexCharacter γ ^ 2 * P.heckeCorrelation Θ w := by
  obtain ⟨e, rfl⟩ := P.exists_entries_of_mem γ hγ
  unfold heckeCorrelation
  rw [← mul_smul, e.dilation_mul, mul_smul, hΘ, ← mul_smul, e.contraction_mul, mul_smul, hΘ,
    ← e.character_up_mul_down]
  ring

end PrimaryPrime

/-- **Cross-Parseval for a dilate.** `∫_P S_a(m u) S_b(u) du = |P| Σ_h a_h b_{−hm}` for `m ∈ O`. -/
theorem integral_cuspCharacterSeries_mul_dilate (m : O) (a b : O → ℂ) (ha : Summable (fun h => ‖a h‖))
    (hb : Summable (fun h => ‖b h‖)) :
    ∫ u in periodDomain, cuspCharacterSeries a (ringComplex m * u) * cuspCharacterSeries b u =
      periodArea * ∑' h : O, a h * b (-(h * m)) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hSc : Continuous (cuspCharacterSeries b) := cuspCharacterSeries_continuous b hb
  have hfin : volume periodDomain ≠ ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top
  have hi : ∀ h : O, Integrable (fun u : ℂ => a h *
      (cuspCharacterSeries b u * tracePhase (cuspFrequency (h * m) * u))) (volume.restrict periodDomain) :=
    fun h => integrableOn_periodDomain_of_continuous _
      (continuous_const.mul (hSc.mul (tracePhase_continuous (h * m))))
  have hpt : ∀ (h : O) (u : ℂ), ‖a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (h * m) * u))‖ ≤
      ‖a h‖ * ∑' k : O, ‖b k‖ := by
    intro h u
    rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_cuspCharacterSeries_le b hb u) (norm_nonneg _)
  have hint_le : ∀ h : O, ∫ u in periodDomain,
      ‖a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (h * m) * u))‖ ≤
        ‖a h‖ * (∑' k : O, ‖b k‖) * (volume periodDomain).toReal := by
    intro h
    have hc : IntegrableOn (fun _ : ℂ => ‖a h‖ * ∑' k : O, ‖b k‖) periodDomain :=
      integrableOn_const (μ := volume) hfin
    calc _ ≤ ∫ _ in periodDomain, ‖a h‖ * ∑' k : O, ‖b k‖ :=
          setIntegral_mono_on (hi h).norm hc periodDomain_measurable (fun u _ => hpt h u)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  have hsum : Summable (fun h : O => ∫ u in periodDomain,
      ‖a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (h * m) * u))‖) :=
    Summable.of_nonneg_of_le (fun h => integral_nonneg fun u => norm_nonneg _) hint_le
      ((ha.mul_right _).mul_right _)
  have hprod : ∀ u : ℂ, cuspCharacterSeries a (ringComplex m * u) * cuspCharacterSeries b u =
      ∑' h : O, a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (h * m) * u)) := by
    intro u
    rw [cuspCharacterSeries, ← tsum_mul_right]
    refine tsum_congr fun h => ?_
    rw [cuspFrequency_mul_right, show cuspFrequency h * ringComplex m * u = cuspFrequency h * (ringComplex m * u) by
      ring]
    ring
  simp_rw [hprod]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  calc ∑' h : O, ∫ u in periodDomain, a h *
        (cuspCharacterSeries b u * tracePhase (cuspFrequency (h * m) * u))
      = ∑' h : O, periodArea * (a h * b (-(h * m))) :=
        tsum_congr fun h => by
          have hk := cuspCharacterSeries_fourier b hb (-(h * m))
          rw [cuspFrequency_neg, neg_neg] at hk
          rw [integral_const_mul, hk]
          ring
    _ = _ := tsum_mul_left

end GaloisForLFunctions.OrderSixMetaplecticTheory
