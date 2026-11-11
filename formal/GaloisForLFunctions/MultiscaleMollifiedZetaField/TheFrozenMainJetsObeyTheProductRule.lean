import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFrozenMainTermsSeparateIntoTheirScaledFactors
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiTaperHasItsConductorJetLimits

/-!
# Product rules for the actual frozen main jets

The finite arithmetic sums, scaled zeta poles, and reflected taper integral
have exact successive derivatives. Their product rules identify the first
two normalized jets of the original main term, with coefficients frozen.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- First arithmetic jet along the direct frozen-coefficient direction. -/
def frozenDirectGcdFirst (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) : ℝ :=
  correctedProfileFirstJet P P N (-2 * u + (-2) * z) (u + 2 * z) (-2) 2 0 0

/-- Second arithmetic jet along the same direction. -/
def frozenDirectGcdSecond (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) : ℝ :=
  correctedProfileSecondJet P P N (-2 * u + (-2) * z) (u + 2 * z) (-2) 2 0 0

/-- First arithmetic jet along the reflected frozen-coefficient direction. -/
def frozenReflectedGcdFirst (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) : ℝ :=
  correctedProfileFirstJet P P N (-2 * (-u) + 2 * z) (-u + 0 * z) 2 0 0 0

/-- Second arithmetic jet along the reflected direction. -/
def frozenReflectedGcdSecond (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) : ℝ :=
  correctedProfileSecondJet P P N (-2 * (-u) + 2 * z) (-u + 0 * z) 2 0 0 0

theorem hasDerivAt_frozenDirectGcd {N : ℕ} (hN : 1 < N) (P : ℝ → ℝ) (u z : ℝ) :
    HasDerivAt (frozenDirectGcd P N u) (frozenDirectGcdFirst P N u z) z := by
  rw [frozenDirectGcd_eq hN]
  simp_rw [shiftedSelbergProfileForm_eq_correctedProfileJetSum]
  exact hasDerivAt_correctedProfileJetSum_direction P P N 0 0 (-2 * u) u (-2) 2 z

theorem hasDerivAt_frozenDirectGcdFirst (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) :
    HasDerivAt (frozenDirectGcdFirst P N u) (frozenDirectGcdSecond P N u z) z :=
  hasDerivAt_correctedProfileFirstJet_direction P P N 0 0 (-2 * u) u (-2) 2 z

theorem hasDerivAt_frozenReflectedGcd {N : ℕ} (hN : 1 < N) (P : ℝ → ℝ) (u z : ℝ) :
    HasDerivAt (frozenReflectedGcd P N u) (frozenReflectedGcdFirst P N u z) z := by
  rw [frozenReflectedGcd_eq hN]
  simp_rw [shiftedSelbergProfileForm_eq_correctedProfileJetSum]
  exact hasDerivAt_correctedProfileJetSum_direction P P N 0 0 (-2 * (-u)) (-u) 2 0 z

theorem hasDerivAt_frozenReflectedGcdFirst (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) :
    HasDerivAt (frozenReflectedGcdFirst P N u) (frozenReflectedGcdSecond P N u z) z :=
  hasDerivAt_correctedProfileFirstJet_direction P P N 0 0 (-2 * (-u)) (-u) 2 0 z

theorem realNormalizedChiTaperJet_zero (L p q η u : ℝ) :
    realNormalizedChiTaperJet L p q η 0 u = realChiTaperIntegral p q η (u / L) := by
  unfold realNormalizedChiTaperJet normalizedChiTaperJet
  simp only [iteratedDeriv_zero, ← Complex.ofReal_div, holomorphicChiPair_ofReal]
  rw [integral_chiPairWeight_eq_ofReal, Complex.ofReal_re]

/-- First jet of a product of three scalar factors. -/
def scalarTripleFirstJet (a a₁ b b₁ c c₁ : ℝ) : ℝ :=
  a₁ * b * c + a * b₁ * c + a * b * c₁

/-- Second jet of a product of three scalar factors. -/
def scalarTripleSecondJet (a a₁ a₂ b b₁ b₂ c c₁ c₂ : ℝ) : ℝ :=
  a₂ * b * c + a * b₂ * c + a * b * c₂ +
    2 * a₁ * b₁ * c + 2 * a₁ * b * c₁ + 2 * a * b₁ * c₁

private theorem hasDerivAt_triple {a b c : ℝ → ℝ} {a₁ b₁ c₁ z : ℝ}
    (ha : HasDerivAt a a₁ z) (hb : HasDerivAt b b₁ z) (hc : HasDerivAt c c₁ z) :
    HasDerivAt (fun x => a x * b x * c x)
      (scalarTripleFirstJet (a z) a₁ (b z) b₁ (c z) c₁) z := by
  apply ((ha.mul hb).mul hc).congr_deriv
  dsimp only [scalarTripleFirstJet]
  ring

private theorem hasDerivAt_scalarTripleFirstJet {a a₁ b b₁ c c₁ : ℝ → ℝ} {a₂ b₂ c₂ z : ℝ}
    (ha : HasDerivAt a (a₁ z) z) (ha₁ : HasDerivAt a₁ a₂ z)
    (hb : HasDerivAt b (b₁ z) z) (hb₁ : HasDerivAt b₁ b₂ z)
    (hc : HasDerivAt c (c₁ z) z) (hc₁ : HasDerivAt c₁ c₂ z) :
    HasDerivAt (fun x => scalarTripleFirstJet (a x) (a₁ x) (b x) (b₁ x) (c x) (c₁ x))
      (scalarTripleSecondJet (a z) (a₁ z) a₂ (b z) (b₁ z) b₂ (c z) (c₁ z) c₂) z := by
  apply ((((ha₁.mul hb).mul hc).add ((ha.mul hb₁).mul hc)).add
    ((ha.mul hb).mul hc₁)).congr_deriv
  dsimp only [scalarTripleSecondJet]
  ring

/-- The first product-rule expression for the normalized main term. -/
def frozenMainProductFirst (P : ℝ → ℝ) (N : ℕ) (u p q η z : ℝ) : ℝ :=
  scalarTripleFirstJet (frozenDirectGcd P N u z) (frozenDirectGcdFirst P N u z)
    (scaledZetaPoleValue (Real.log N) (-2) (u + z))
    (scaledZetaPoleFirstJet (Real.log N) (-2) (u + z))
    (∫ t, blockWindow p q η t) 0 +
  scalarTripleFirstJet (frozenReflectedGcd P N u z) (frozenReflectedGcdFirst P N u z)
    (scaledZetaPoleValue (Real.log N) 2 (u + z))
    (scaledZetaPoleFirstJet (Real.log N) 2 (u + z))
    (realNormalizedChiTaperJet (Real.log N) p q η 0 (u + z))
    (realNormalizedChiTaperJet (Real.log N) p q η 1 (u + z))

/-- The second product-rule expression includes all three cross terms. -/
def frozenMainProductSecond (P : ℝ → ℝ) (N : ℕ) (u p q η z : ℝ) : ℝ :=
  scalarTripleSecondJet (frozenDirectGcd P N u z) (frozenDirectGcdFirst P N u z)
    (frozenDirectGcdSecond P N u z)
    (scaledZetaPoleValue (Real.log N) (-2) (u + z))
    (scaledZetaPoleFirstJet (Real.log N) (-2) (u + z))
    (scaledZetaPoleSecondJet (Real.log N) (-2) (u + z))
    (∫ t, blockWindow p q η t) 0 0 +
  scalarTripleSecondJet (frozenReflectedGcd P N u z) (frozenReflectedGcdFirst P N u z)
    (frozenReflectedGcdSecond P N u z)
    (scaledZetaPoleValue (Real.log N) 2 (u + z))
    (scaledZetaPoleFirstJet (Real.log N) 2 (u + z))
    (scaledZetaPoleSecondJet (Real.log N) 2 (u + z))
    (realNormalizedChiTaperJet (Real.log N) p q η 0 (u + z))
    (realNormalizedChiTaperJet (Real.log N) p q η 1 (u + z))
    (realNormalizedChiTaperJet (Real.log N) p q η 2 (u + z))

private theorem shifted_pole_derivatives {L u z : ℝ} (hL : L ≠ 0)
    (hu : u + z ≠ 0) {κ : ℝ} (hκ : κ ≠ 0) :
    HasDerivAt (fun y => scaledZetaPoleValue L κ (u + y))
      (scaledZetaPoleFirstJet L κ (u + z)) z ∧
    HasDerivAt (fun y => scaledZetaPoleFirstJet L κ (u + y))
      (scaledZetaPoleSecondJet L κ (u + z)) z := by
  have h := (hasDerivAt_id z).const_add u
  constructor
  · simpa only [id_eq, mul_one] using (hasDerivAt_scaledZetaPoleValue hL hκ hu).comp z h
  · simpa only [id_eq, mul_one] using (hasDerivAt_scaledZetaPoleFirstJet L hκ hu).comp z h

private theorem shifted_chi_derivative {L u p q η z : ℝ}
    (hL : 0 < L) (hu : 0 < u + z) (hη : 0 < η) (hp : 4 ≤ p - η)
    (hu20 : (u + z) / L ≤ 1 / 20) (j : ℕ) :
    HasDerivAt (fun y => realNormalizedChiTaperJet L p q η j (u + y))
      (realNormalizedChiTaperJet L p q η (j + 1) (u + z)) z := by
  simpa only [id_eq, mul_one] using
    (hasDerivAt_realNormalizedChiTaperJet hL hu hη hp hu20 j).comp z
      ((hasDerivAt_id z).const_add u)

/-- The first product formula is the actual normalized first main jet. -/
theorem normalizedFrozenMainJet_one_eq {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (u : ℝ) {p q η z : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    (hz : 0 < (u + z) / Real.log N) (hz20 : (u + z) / Real.log N ≤ 1 / 20) :
    normalizedFrozenMainJet P N u p q η 1 z = frozenMainProductFirst P N u p q η z := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hu : 0 < u + z := (div_pos_iff_of_pos_right hL).mp hz
  obtain ⟨hd, _⟩ := shifted_pole_derivatives hL.ne' hu.ne' (by norm_num : (-2 : ℝ) ≠ 0)
  obtain ⟨hr, _⟩ := shifted_pole_derivatives hL.ne' hu.ne' (by norm_num : (2 : ℝ) ≠ 0)
  have hc := shifted_chi_derivative hL hu hη hp hz20 0
  have hf := (hasDerivAt_triple (hasDerivAt_frozenDirectGcd hN P u z) hd
    (hasDerivAt_const z (∫ t, blockWindow p q η t))).add
      (hasDerivAt_triple (hasDerivAt_frozenReflectedGcd hN P u z) hr hc)
  have he : normalizedFrozenMainJet P N u p q η 0 =
      fun y => frozenDirectGcd P N u y * scaledZetaPoleValue (Real.log N) (-2) (u + y) *
        (∫ t, blockWindow p q η t) +
        frozenReflectedGcd P N u y * scaledZetaPoleValue (Real.log N) 2 (u + y) *
          realNormalizedChiTaperJet (Real.log N) p q η 0 (u + y) := by
    funext y
    rw [normalizedFrozenMainJet_zero_eq hN, realNormalizedChiTaperJet_zero]
  have hm := hasDerivAt_normalizedFrozenMainJet hN P u hη hp 0 hz hz20
  rw [he] at hm
  exact hm.deriv.symm.trans hf.deriv

private theorem hasDerivAt_frozenMainProductFirst {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (u : ℝ) {p q η z : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    (hz : 0 < (u + z) / Real.log N) (hz20 : (u + z) / Real.log N ≤ 1 / 20) :
    HasDerivAt (frozenMainProductFirst P N u p q η)
      (frozenMainProductSecond P N u p q η z) z := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hu : 0 < u + z := (div_pos_iff_of_pos_right hL).mp hz
  obtain ⟨hd, hd₁⟩ := shifted_pole_derivatives hL.ne' hu.ne' (by norm_num : (-2 : ℝ) ≠ 0)
  obtain ⟨hr, hr₁⟩ := shifted_pole_derivatives hL.ne' hu.ne' (by norm_num : (2 : ℝ) ≠ 0)
  have hc := shifted_chi_derivative hL hu hη hp hz20 0
  have hc₁ := shifted_chi_derivative hL hu hη hp hz20 1
  exact (hasDerivAt_scalarTripleFirstJet (hasDerivAt_frozenDirectGcd hN P u z)
    (hasDerivAt_frozenDirectGcdFirst P N u z) hd hd₁
    (hasDerivAt_const z (∫ t, blockWindow p q η t)) (hasDerivAt_const z 0)).add
      (hasDerivAt_scalarTripleFirstJet (hasDerivAt_frozenReflectedGcd hN P u z)
        (hasDerivAt_frozenReflectedGcdFirst P N u z) hr hr₁ hc hc₁)

/-- The second product formula is the actual normalized second main jet. -/
theorem normalizedFrozenMainJet_two_eq {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (u : ℝ) {p q η z : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    (hz : 0 < (u + z) / Real.log N) (hz20 : (u + z) / Real.log N < 1 / 20) :
    normalizedFrozenMainJet P N u p q η 2 z = frozenMainProductSecond P N u p q η z := by
  have hcont : ContinuousAt (fun y : ℝ => (u + y) / Real.log N) z := by fun_prop
  have hnear := hcont.eventually (isOpen_Ioo.mem_nhds (And.intro hz hz20))
  have he : normalizedFrozenMainJet P N u p q η 1 =ᶠ[𝓝 z] frozenMainProductFirst P N u p q η := by
    filter_upwards [hnear] with y hy
    exact normalizedFrozenMainJet_one_eq hN P u hη hp hy.1 hy.2.le
  have hf := (hasDerivAt_frozenMainProductFirst hN P u hη hp hz hz20.le).congr_of_eventuallyEq he
  exact (hasDerivAt_normalizedFrozenMainJet hN P u hη hp 1 hz hz20.le).deriv.symm.trans hf.deriv

end GaloisForLFunctions.MultiscaleMollifiedZetaField
