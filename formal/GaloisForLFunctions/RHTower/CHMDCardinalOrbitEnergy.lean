import GaloisForLFunctions.RHTower.ThetaCardinalOrbitReadout

/-!
# The exact signed two-coordinate form of a cardinal zero orbit

The complete zero sum of each admitted real packet has finite support. Its real
and imaginary coefficients split into positive and negative orbit masses.
For a nonreal orbit these two masses agree exactly.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower
open WeilSpectral CHMDStage16 CHMDDoobGraph

def cardinalPositiveTerm (a : ℂ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) *
    ((unsignedOrbitIndicator a (gammaOf ρ) + unsignedOrbitIndicator a (conj (gammaOf ρ)))/2)^2

def cardinalNegativeTerm (a : ℂ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) *
    ((unsignedOrbitIndicator a (gammaOf ρ) - unsignedOrbitIndicator a (conj (gammaOf ρ)))/2)^2

theorem summable_cardinalPositiveTerm (a : ℂ) : Summable (cardinalPositiveTerm a) := by
  apply summable_of_cardinalOrbit_support (a := a)
  intro ρ hρ
  obtain ⟨h1, h2⟩ := unsignedOrbitIndicator_pair_eq_zero hρ
  simp [cardinalPositiveTerm, h1, h2]

theorem summable_cardinalNegativeTerm (a : ℂ) : Summable (cardinalNegativeTerm a) := by
  apply summable_of_cardinalOrbit_support (a := a)
  intro ρ hρ
  obtain ⟨h1, h2⟩ := unsignedOrbitIndicator_pair_eq_zero hρ
  simp [cardinalNegativeTerm, h1, h2]

def cardinalPositiveMass (a : ℂ) : ℝ := ∑' ρ, cardinalPositiveTerm a ρ
def cardinalNegativeMass (a : ℂ) : ℝ := ∑' ρ, cardinalNegativeTerm a ρ

theorem cardinalRealSource_Wsummand_re {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (c : ℂ) (ρ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.Wsummand (fun x => (cardinalRealSource a c x : ℂ))
      (fun x => (cardinalRealSource a c x : ℂ)) ρ).re =
        c.re^2 * cardinalPositiveTerm a ρ - c.im^2 * cardinalNegativeTerm a ρ := by
  have hc : XiC (conj (gammaOf ρ)) = 0 := by rw [XiC_conj, XiC_gammaOf_eq_zero ρ, map_zero]
  rw [ZeroConfig.Wsummand, cardinalRealSource_paperFT ha hz c (XiC_gammaOf_eq_zero ρ),
    cardinalRealSource_paperFT ha hz c hc, cardinalOrbitValue_conj, conj_conj]
  have hm : (zetaZeroConfig.mult ρ : ℂ) * cardinalOrbitValue a c (gammaOf ρ) *
      cardinalOrbitValue a c (gammaOf ρ) =
      (zetaZeroConfig.mult ρ : ℂ) * cardinalOrbitValue a c (gammaOf ρ)^2 := by ring
  rw [hm, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [cardinalOrbitValue_sq_re]
  dsimp [cardinalPositiveTerm, cardinalNegativeTerm]
  ring

/-- The complete graph-side spectral expression is an exact signed diagonal form. -/
theorem signedZeroEnergy_cardinalRealSource {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) (c : ℂ) :
    signedZeroEnergy (cardinalRealSource a c) =
      c.re^2 * cardinalPositiveMass a - c.im^2 * cardinalNegativeMass a := by
  obtain ⟨hp, hm⟩ := cardinalRealSource_poles ha hz c
  rw [signedZeroEnergy, hp, hm]
  simp only [zero_mul, add_zero, Complex.zero_re, sub_zero]
  rw [ZeroConfig.W, Complex.re_tsum (summable_cardinalRealSource_W ha hz c)]
  simp_rw [cardinalRealSource_Wsummand_re ha hz c]
  rw [Summable.tsum_sub ((summable_cardinalPositiveTerm a).mul_left (c.re^2))
    ((summable_cardinalNegativeTerm a).mul_left (c.im^2)), tsum_mul_left, tsum_mul_left]
  rfl

theorem unsignedOrbitIndicator_neg (a z : ℂ) :
    unsignedOrbitIndicator a (-z) = unsignedOrbitIndicator a z := by
  have he : (-z = a ∨ -z = -a) ↔ (z = a ∨ z = -a) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (neg_eq_iff_eq_neg.mp h)
      · exact Or.inl (neg_inj.mp h)
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (neg_neg a)
  simp only [unsignedOrbitIndicator, he]

theorem unsignedOrbitIndicator_conj (a z : ℂ) :
    unsignedOrbitIndicator a (conj z) = unsignedOrbitIndicator (conj a) z := by
  have he : (conj z = a ∨ conj z = -a) ↔ (z = conj a ∨ z = -conj a) := by
    constructor <;> rintro (h | h)
    · exact Or.inl (by simpa using congrArg conj h)
    · exact Or.inr (by simpa using congrArg conj h)
    · exact Or.inl (by simpa using congrArg conj h)
    · exact Or.inr (by simpa using congrArg conj h)
  simp only [unsignedOrbitIndicator, he]

theorem unsignedOrbitIndicators_disjoint {a : ℂ} (ha : 0 < a.re) (hi : a.im ≠ 0) (z : ℂ) :
    unsignedOrbitIndicator a z * unsignedOrbitIndicator a (conj z) = 0 := by
  have h1 : conj a ≠ a := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.conj_im] at hh
    exact hi (by linarith)
  have h2 : conj a ≠ -a := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at hh
    linarith
  by_cases hz : z = a ∨ z = -a
  · rcases hz with rfl | rfl
    · simp [unsignedOrbitIndicator, h1, h2]
    · simp [unsignedOrbitIndicator, h1, h2, neg_eq_iff_eq_neg]
  · simp [unsignedOrbitIndicator, hz]

/-- Each nonreal orbit contributes balanced positive and negative masses. -/
theorem cardinalPositiveMass_eq_negative {a : ℂ} (ha : 0 < a.re) (hi : a.im ≠ 0) :
    cardinalPositiveMass a = cardinalNegativeMass a := by
  apply tsum_congr
  intro ρ
  have hd := unsignedOrbitIndicators_disjoint ha hi (gammaOf ρ)
  dsimp [cardinalPositiveTerm, cardinalNegativeTerm]
  congr 1
  nlinarith

theorem cardinalNegativeMass_eq_zero_of_real {a : ℂ} (hi : a.im = 0) :
    cardinalNegativeMass a = 0 := by
  have hc : conj a = a := by apply Complex.ext <;> simp [hi]
  unfold cardinalNegativeMass cardinalNegativeTerm
  simp only [unsignedOrbitIndicator_conj, hc, sub_self, zero_div, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, tsum_zero]

theorem cardinalPositiveMass_nonneg (a : ℂ) : 0 ≤ cardinalPositiveMass a :=
  tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem cardinalNegativeMass_nonneg (a : ℂ) : 0 ≤ cardinalNegativeMass a :=
  tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem cardinalPositiveMass_pos {a : ℂ} (ρ : zetaZeroConfig.carrier)
    (hρ : gammaOf ρ = a ∨ gammaOf ρ = -a) : 0 < cardinalPositiveMass a := by
  apply (summable_cardinalPositiveTerm a).tsum_pos
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ρ
  have hm : (0 : ℝ) < zetaZeroConfig.mult ρ := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (zetaZeroConfig.one_le_mult ρ ρ.property)
  have hA : unsignedOrbitIndicator a (gammaOf ρ) = 1 := if_pos hρ
  have hB := unsignedOrbitIndicator_nonneg a (conj (gammaOf ρ))
  dsimp only [cardinalPositiveTerm]
  rw [hA]
  positivity

end RHTower
