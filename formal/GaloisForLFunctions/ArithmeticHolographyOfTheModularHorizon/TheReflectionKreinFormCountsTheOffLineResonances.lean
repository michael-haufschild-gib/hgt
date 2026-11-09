import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheOddCavitySeesEveryResonance
import GaloisForLFunctions.HTGeometry.HermitianInertia
import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureAsymptoticFiniteRank
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The reflection Krein form counts the off-line resonances

The resonances `s = ρ/2` of the mirror-even channel come in reflection pairs `s ↔ s* = ½ − s̄`, the image of the
functional-equation pairing `ρ ↔ ρ* = 1 − ρ̄` of the zeros; the fixed line of the reflection is the line of
universal damping `Re s = ¼`. Evaluating the energies of the cavity at both members of a pair gives the
**reflection Krein form** of the horizon,

  `𝒦_ρ(F, G) = Λ_F(s) conj Λ_G(s*) + Λ_F(s*) conj Λ_G(s)`,

on the tent energies `F = Σ_a x_a G_{t_a}²`; its Gram matrix is `v w* + w v*` with `v_a = d_{t_a}(s)`,
`w_a = d_{t_a}(s*)` (`tentReflectionKrein`).

**The Krein index law** (`tentReflectionKrein_index`). The form has at most one negative square
(`v w* + w v* = ½(v + w)(v + w)* − ½(v − w)(v − w)*`). At a critical zero `s* = s`, so it is positive
semidefinite. Off the line it has exactly one negative square: by the phase law and the size bound the tent
energies satisfy `|d_j(s)| ≍ (j + 3)^{−1−Re s}` (`exists_tentEnergy_ge`, `exists_tentEnergy_le`), and
`Re s ≠ Re s*` makes `v` and `w` independent on two tents (`exists_tent_independent`). Hence

  **RH ⟺ every reflection Krein form of the cavity is positive semidefinite**
  (`riemannHypothesis_iff_tentReflectionKrein`).

The horizon's own Krein form at one resonance cannot see the line
(`TheCavityKreinFormIsBlindToTheCriticalLine`); the reflection of resonances can. Off the line, the damping
`½ − Re s` and its reflection `½ − Re s*` are read off the decay exponents `1 + Re s` and `1 + Re s*` of the
tent energies, and the mismatch of the exponents is the negative square.
-/

open Complex MeasureTheory Set Filter Topology Matrix
open scoped MatrixGroups UpperHalfPlane ComplexOrder

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry

/-! ### The reflection matrix `v w* + w v*` -/

/-- The reflection Krein matrix `v w* + w v*`. -/
def reflectionMatrix {n : ℕ} (v w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  vecMulVec v (star w) + vecMulVec w (star v)

variable {n : ℕ}

/-- `v w* + w v* + ½(v − w)(v − w)* = ½(v + w)(v + w)*`. -/
theorem reflectionMatrix_add (v w : Fin n → ℂ) :
    reflectionMatrix v w + vecMulVec (((Real.sqrt (1 / 2) : ℝ) : ℂ) • (v - w))
        (star (((Real.sqrt (1 / 2) : ℝ) : ℂ) • (v - w))) =
      vecMulVec (((Real.sqrt (1 / 2) : ℝ) : ℂ) • (v + w)) (star (((Real.sqrt (1 / 2) : ℝ) : ℂ) • (v + w))) := by
  set c : ℂ := ((Real.sqrt (1 / 2) : ℝ) : ℂ)
  have hcc : c * star c = 1 / 2 := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  ext a b
  simp only [reflectionMatrix, Matrix.add_apply, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, Pi.sub_apply,
    Pi.add_apply, smul_eq_mul, star_mul', star_sub, star_add]
  linear_combination (-2 * (v a * star (w b) + w a * star (v b))) * hcc

/-- **At most one negative square.** -/
theorem negIndex_reflectionMatrix_le_one (v w : Fin n → ℂ) : hermNegIndex (reflectionMatrix v w) ≤ 1 := by
  have h := hermNegIndex_le_finrank_correctionRange_of_add_posSemidef (reflectionMatrix v w)
    (vecMulVec (((Real.sqrt (1 / 2) : ℝ) : ℂ) • (v - w)) (star (((Real.sqrt (1 / 2) : ℝ) : ℂ) • (v - w))))
    (by rw [reflectionMatrix_add]; exact posSemidef_vecMulVec_self_star _)
  exact h.trans (rank_vecMulVec_le _ _)

/-- **Equal vectors give a positive form.** -/
theorem negIndex_reflectionMatrix_self (v : Fin n → ℂ) : hermNegIndex (reflectionMatrix v v) = 0 := by
  have h := hermNegIndex_le_finrank_correctionRange_of_add_posSemidef (reflectionMatrix v v) 0
    (by rw [add_zero]; exact (posSemidef_vecMulVec_self_star v).add (posSemidef_vecMulVec_self_star v))
  have h0 : Module.finrank ℂ (LinearMap.range (0 : Matrix (Fin n) (Fin n) ℂ).mulVecLin) = 0 := by simp
  omega

theorem star_dotProduct_vecMulVec (v w x : Fin n → ℂ) :
    star x ⬝ᵥ vecMulVec v (star w) *ᵥ x = (star x ⬝ᵥ v) * (star w ⬝ᵥ x) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- The form of `v w* + w v*` is `2 Re(⟨x, v⟩ conj ⟨x, w⟩)`. -/
theorem hermQuad_reflectionMatrix (v w x : Fin n → ℂ) :
    hermQuad (reflectionMatrix v w) x = 2 * ((star x ⬝ᵥ v) * starRingEnd ℂ (star x ⬝ᵥ w)).re := by
  unfold hermQuad reflectionMatrix
  rw [add_mulVec, dotProduct_add, star_dotProduct_vecMulVec, star_dotProduct_vecMulVec,
    star_dotProduct w x, star_dotProduct v x]
  simp only [Complex.add_re, Complex.star_def]
  have : ((star x ⬝ᵥ w) * starRingEnd ℂ (star x ⬝ᵥ v)).re = ((star x ⬝ᵥ v) * starRingEnd ℂ (star x ⬝ᵥ w)).re := by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  rw [this]; ring

/-- **A negative square.** If some `x` has `⟨x, v⟩ = 1` and `⟨x, w⟩ = −1`, the form is negative on `x`. -/
theorem one_le_negIndex_reflectionMatrix {v w x : Fin n → ℂ} (hP : star x ⬝ᵥ v = 1)
    (hQ : star x ⬝ᵥ w = -1) : 1 ≤ hermNegIndex (reflectionMatrix v w) := by
  have hx : x ≠ 0 := by rintro rfl; simp at hP
  have hW : IsPosDefOn (-(reflectionMatrix v w)) (ℂ ∙ x) := by
    intro y hy hy0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hc : c ≠ 0 := by rintro rfl; simp at hy0
    rw [hermQuad_neg, hermQuad_reflectionMatrix, star_smul, smul_dotProduct, smul_dotProduct, hP, hQ,
      smul_eq_mul, smul_eq_mul]
    have e : (star c * 1 * starRingEnd ℂ (star c * -1)).re = -Complex.normSq c := by
      rw [Complex.star_def, map_mul, Complex.conj_conj, show starRingEnd ℂ c * 1 * (c * starRingEnd ℂ (-1)) =
        -(c * starRingEnd ℂ c) by simp; ring, Complex.mul_conj]
      simp
    rw [e]
    have := Complex.normSq_pos.2 hc
    linarith
  have h := finrank_le_posIndex hW
  rw [finrank_span_singleton hx] at h
  exact h

/-- On two coordinates, `v` and `w` with `v₀w₁ ≠ v₁w₀` give a negative square. -/
theorem one_le_negIndex_reflectionMatrix_two {v w : Fin 2 → ℂ} (hD : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    1 ≤ hermNegIndex (reflectionMatrix v w) := by
  refine one_le_negIndex_reflectionMatrix
    (x := star ![(w 1 + v 1) / (v 0 * w 1 - v 1 * w 0), -(w 0 + v 0) / (v 0 * w 1 - v 1 * w 0)]) ?_ ?_
  · rw [star_star]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD]
    ring
  · rw [star_star]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring

/-! ### Reflection of zeros -/

/-- The reflection `ρ* = 1 − ρ̄` of a zero in the strip is a zero in the strip. -/
theorem reflect_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    riemannZeta (1 - starRingEnd ℂ ρ) = 0 ∧ 0 < (1 - starRingEnd ℂ ρ).re := by
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hc : riemannZeta (starRingEnd ℂ ρ) = 0 := by rw [riemannZeta_conj, hζ, map_zero]
  refine ⟨riemannZeta_one_sub_eq_zero_of_mem_openStrip hc (by simpa using hpos) (by simpa using hlt), ?_⟩
  simp; linarith

theorem reflect_eq_self_iff (ρ : ℂ) : 1 - starRingEnd ℂ ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, h]; norm_num
    · simp

/-! ### Size of the tent energies -/

/-- **Lower bound for the tent energies**: `|d_j(ρ/2)| ≥ L (j + 3)^{−1−Re(ρ/2)}` far up the cusp. -/
theorem exists_tentEnergy_ge {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ J : ℕ, ∃ L : ℝ, 0 < L ∧ ∀ j : ℕ, J ≤ j →
      L * ((j : ℝ) + 3) ^ (-1 - (ρ / 2).re) ≤ ‖tentEnergy (ρ / 2) j‖ := by
  obtain ⟨-, -, -, -, hκ, -⟩ := resonance_data hζ hpos
  obtain ⟨J, hJ⟩ := exists_tent_phase hζ hpos
  refine ⟨J, ‖resonanceCoefficient (ρ / 2 - 1 / 2)‖ / 2048, by have := norm_pos_iff.2 hκ; positivity,
    fun j hj => ?_⟩
  set θ := (ρ / 2).im * Real.log (j + 7 / 2) - (resonanceCoefficient (ρ / 2 - 1 / 2)).arg
  have h := hJ j hj θ (by
    rw [show θ + (resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2) = 0 by
      simp only [θ]; ring, Real.cos_zero]; norm_num)
  refine h.trans ((Complex.re_le_norm _).trans_eq ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Decay exponents that differ cannot give proportional sequences. -/
theorem not_proportional_of_lt {p q : ℕ → ℝ} {α β Lp Uq : ℝ} {J : ℕ} (hαβ : α < β) (hLp : 0 < Lp)
    (hp : ∀ j, J ≤ j → Lp * ((j : ℝ) + 3) ^ (-1 - α) ≤ p j)
    (hq : ∀ j, J ≤ j → q j ≤ Uq * ((j : ℝ) + 3) ^ (-1 - β)) (hpJ : 0 < p J) (hqJ : 0 < q J) :
    ¬ ∀ j, J ≤ j → p j * q J = p J * q j := by
  intro h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
  obtain ⟨j, hj1, hj2⟩ := ((((tendsto_rpow_atTop (sub_pos.2 hαβ)).comp ht).eventually_gt_atTop
    (Uq * p J / (Lp * q J))).and (eventually_ge_atTop J)).exists
  simp only [Function.comp] at hj1
  set a : ℝ := (j : ℝ) + 3
  have ha : 0 < a := by positivity
  have e1 : a ^ (-1 - α) = a ^ (-1 - β) * a ^ (β - α) := by
    rw [← Real.rpow_add ha]; ring_nf
  have hab : 0 < a ^ (-1 - β) := Real.rpow_pos_of_pos ha _
  have key : Lp * a ^ (-1 - α) * q J ≤ p J * (Uq * a ^ (-1 - β)) := by
    calc Lp * a ^ (-1 - α) * q J ≤ p j * q J := mul_le_mul_of_nonneg_right (hp j hj2) hqJ.le
      _ = p J * q j := h j hj2
      _ ≤ p J * (Uq * a ^ (-1 - β)) := mul_le_mul_of_nonneg_left (hq j hj2) hpJ.le
  rw [e1] at key
  have key' : Lp * q J * a ^ (β - α) ≤ p J * Uq := by
    have := key
    nlinarith [mul_pos hab (mul_pos hLp hqJ)]
  have := (div_lt_iff₀ (mul_pos hLp hqJ)).1 hj1
  linarith

/-- **Independence off the line.** For a zero `ρ` with `Re ρ ≠ ½` the tent energies at `ρ/2` and at the
reflected resonance `(1 − ρ̄)/2` are not proportional. -/
theorem exists_tent_independent {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) (hoff : ρ.re ≠ 1 / 2) :
    ∃ j k : ℕ, tentEnergy (ρ / 2) j * tentEnergy ((1 - starRingEnd ℂ ρ) / 2) k -
      tentEnergy (ρ / 2) k * tentEnergy ((1 - starRingEnd ℂ ρ) / 2) j ≠ 0 := by
  obtain ⟨hζ', hpos'⟩ := reflect_zero hζ hpos
  set ρ' := 1 - starRingEnd ℂ ρ
  obtain ⟨J₁, L₁, hL₁, hlow₁⟩ := exists_tentEnergy_ge hζ hpos
  obtain ⟨J₂, L₂, hL₂, hlow₂⟩ := exists_tentEnergy_ge hζ' hpos'
  obtain ⟨U₁, hup₁⟩ := exists_tentEnergy_le hζ hpos
  obtain ⟨U₂, hup₂⟩ := exists_tentEnergy_le hζ' hpos'
  set J := max J₁ J₂
  by_contra hno
  push Not at hno
  set p : ℕ → ℝ := fun j => ‖tentEnergy (ρ / 2) j‖
  set q : ℕ → ℝ := fun j => ‖tentEnergy (ρ' / 2) j‖
  have hprop : ∀ j, J ≤ j → p j * q J = p J * q j := by
    intro j _
    have := congrArg norm (sub_eq_zero.1 (hno j J))
    simpa only [norm_mul, p, q] using this
  have hp : ∀ j, J ≤ j → L₁ * ((j : ℝ) + 3) ^ (-1 - (ρ / 2).re) ≤ p j :=
    fun j hj => hlow₁ j ((le_max_left _ _).trans hj)
  have hq : ∀ j, J ≤ j → L₂ * ((j : ℝ) + 3) ^ (-1 - (ρ' / 2).re) ≤ q j :=
    fun j hj => hlow₂ j ((le_max_right _ _).trans hj)
  have hpJ : 0 < p J := lt_of_lt_of_le (by positivity) (hp J le_rfl)
  have hqJ : 0 < q J := lt_of_lt_of_le (by positivity) (hq J le_rfl)
  have hre : (ρ / 2).re ≠ (ρ' / 2).re := by
    simp only [ρ', Complex.div_re, Complex.sub_re, Complex.one_re, Complex.conj_re]
    intro h
    apply hoff
    norm_num at h
    linarith
  rcases lt_or_gt_of_ne hre with h | h
  · exact not_proportional_of_lt h hL₁ hp (fun j _ => hup₂ j) hpJ hqJ hprop
  · exact not_proportional_of_lt h hL₂ hq (fun j _ => hup₁ j) hqJ hpJ
      (fun j hj => by rw [mul_comm, ← hprop j hj, mul_comm])

/-! ### The Krein index law -/

/-- The reflection Krein matrix of the tents `t₀, …, t_{n−1}` at the zero `ρ`: tent energies at `ρ/2` and at the
reflected resonance `(1 − ρ̄)/2`. -/
def tentReflectionKrein (ρ : ℂ) (t : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  reflectionMatrix (fun a => tentEnergy (ρ / 2) (t a)) (fun a => tentEnergy ((1 - starRingEnd ℂ ρ) / 2) (t a))

/-- **The Krein index law of the horizon.** For a zero `ρ` of `ζ` with `Re ρ > 0` the reflection Krein form of
the cavity has at most one negative square; it is positive semidefinite on the critical line; off the line two
tents carry exactly one negative square. -/
theorem tentReflectionKrein_index {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    (∀ {n : ℕ} (t : Fin n → ℕ), hermNegIndex (tentReflectionKrein ρ t) ≤ 1) ∧
    (ρ.re = 1 / 2 → ∀ {n : ℕ} (t : Fin n → ℕ), hermNegIndex (tentReflectionKrein ρ t) = 0) ∧
    (ρ.re ≠ 1 / 2 → ∃ t : Fin 2 → ℕ, hermNegIndex (tentReflectionKrein ρ t) = 1) := by
  refine ⟨fun t => negIndex_reflectionMatrix_le_one _ _, fun hre n t => ?_, fun hoff => ?_⟩
  · rw [tentReflectionKrein, (reflect_eq_self_iff ρ).2 hre]
    exact negIndex_reflectionMatrix_self _
  · obtain ⟨j, k, hjk⟩ := exists_tent_independent hζ hpos hoff
    refine ⟨![j, k], le_antisymm (negIndex_reflectionMatrix_le_one _ _) ?_⟩
    exact one_le_negIndex_reflectionMatrix_two (by simpa using hjk)

/-- **RH is the positivity of the horizon's reflection Krein forms.** -/
theorem riemannHypothesis_iff_tentReflectionKrein :
    RiemannHypothesis ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ∀ {n : ℕ} (t : Fin n → ℕ),
      hermNegIndex (tentReflectionKrein ρ t) = 0 := by
  constructor
  · intro hRH ρ hζ hpos n t
    have hre : ρ.re = 1 / 2 := hRH ρ hζ (by
      rintro ⟨m, hm⟩
      have := congrArg Complex.re hm
      simp at this
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith) (by rintro rfl; exact riemannZeta_one_ne_zero hζ)
    exact (tentReflectionKrein_index hζ hpos).2.1 hre t
  · intro h s hs htriv hs1
    have hpos : 0 < s.re := by
      by_contra hle
      push Not at hle
      exact riemannZeta_ne_zero_of_re_le_zero hle (fun m hm => htriv ⟨m, by rw [hm]; ring⟩) hs
    by_contra hne
    obtain ⟨t, ht⟩ := (tentReflectionKrein_index hs hpos).2.2 hne
    rw [h s hs hpos t] at ht
    exact absurd ht (by norm_num)

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
