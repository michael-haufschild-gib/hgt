import GaloisForLFunctions.RHTower.XiShiftedHardEdgeArchimedeanDensity
import GaloisForLFunctions.HTGeometry.SquaredVariableSubstitution
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries
import GaloisForLFunctions.HTGeometry.PsdHankelJetVanishing
import GaloisForLFunctions.RHTower.HardyZ

/-!
# The literal finite-prime hard-edge density and its squared-variable pairing

At hard-edge type `σ` the completed source has the explicit density

`V_σ(x) = ϑ_∞(x) - ∑_{2 ≤ n, log n ≤ 2σ} Λ(n) n^{-1/2} cos(x log n)`,

the archimedean rate minus the finitely many prime oscillations visible to a test of type below
`σ`.  Its restricted-Weil form on even states, written in the squared variable `u = x²`, is the
pairing against the signed density `V_σ(√u)/√u` on the half-line together with the polar atom of
mass `2π` at `u = -1/4`.  The change of variables is the whole content of the passage: the
Jacobian `1/√u` is what makes the half-line description exact.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The archimedean rate is even -/

theorem digamma_conj {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma (starRingEnd ℂ s) = starRingEnd ℂ (Complex.digamma s) := by
  have hs' : 0 < ((starRingEnd ℂ) s).re := by
    simpa using hs
  have hstar : (starRingEnd ℂ) (∑' n : ℕ, gaussDigammaSeriesTerm s n)
      = ∑' n : ℕ, (starRingEnd ℂ) (gaussDigammaSeriesTerm s n) := by
    simpa using (tsum_star (f := fun n : ℕ => gaussDigammaSeriesTerm s n))
  rw [digamma_eq_neg_euler_add_tsum_gauss hs', digamma_eq_neg_euler_add_tsum_gauss hs,
    map_add, map_neg, Complex.conj_ofReal, hstar]
  congr 1
  refine tsum_congr fun n => ?_
  rw [gaussDigammaSeriesTerm, gaussDigammaSeriesTerm]
  simp only [map_sub, map_div₀, map_one, map_add, Complex.conj_natCast]

theorem routeUArchimedeanPoint_neg (x : ℝ) :
    routeUArchimedeanPoint (-x) = starRingEnd ℂ (routeUArchimedeanPoint x) := by
  rw [routeUArchimedeanPoint, routeUArchimedeanPoint]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem routeUArchimedeanPoint_re (x : ℝ) : (routeUArchimedeanPoint x).re = 1 / 4 := by
  rw [routeUArchimedeanPoint]
  simp

theorem routeUArchimedeanRate_neg (x : ℝ) :
    routeUArchimedeanRate (-x) = routeUArchimedeanRate x := by
  have hre : (0 : ℝ) < (routeUArchimedeanPoint x).re := by
    rw [routeUArchimedeanPoint_re]
    norm_num
  rw [routeUArchimedeanRate, routeUArchimedeanRate, routeUArchimedeanPoint_neg,
    digamma_conj hre, Complex.conj_re]

theorem routeUArchimedeanRate_abs (x : ℝ) :
    routeUArchimedeanRate |x| = routeUArchimedeanRate x := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, routeUArchimedeanRate_neg]

/-- The finitely many prime frequencies visible below type `σ`. -/
def routeUHardEdgeFrequencyBound (σ : ℝ) : ℕ := ⌊Real.exp (2 * σ)⌋₊

/-- **The literal finite-prime hard-edge density of type `σ`.** -/
def routeUHardEdgeDensity (σ x : ℝ) : ℝ :=
  routeUArchimedeanRate x
    - ∑ m ∈ Finset.Icc 2 (routeUHardEdgeFrequencyBound σ),
        (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m * Real.cos (x * Real.log m)

/-- **The squared-variable pairing of the hard-edge density.**  The half-line integral against the
square-root Jacobian together with the polar atom at `-1/4`. -/
def routeUHardEdgePairing (σ : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), Φ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
    + 2 * Real.pi * Φ (-1 / 4)

/-- The even restricted-Weil form of a squared-variable state. -/
def routeUHardEdgeEvenForm (σ : ℝ) (H K : ℝ → ℝ) : ℝ :=
  routeUHardEdgePairing σ fun u => H u * K u

/-- The odd restricted-Weil form of a squared-variable state: the same pairing with one factor of
the coordinate, which is multiplication by the Fourier variable on the odd side. -/
def routeUHardEdgeOddForm (σ : ℝ) (H K : ℝ → ℝ) : ℝ :=
  routeUHardEdgePairing σ fun u => u * (H u * K u)

/-! ## The passage between the line and the half-line -/

/-- **The restricted-Weil form of an even state is the squared-variable pairing.**  This is the
squared-variable substitution applied to the literal density. -/
theorem integral_density_comp_sq_eq_pairing (σ : ℝ) (Φ : ℝ → ℝ) :
    (∫ x : ℝ, routeUHardEdgeDensity σ x * Φ (x ^ 2))
      + 2 * Real.pi * Φ (-1 / 4)
      = routeUHardEdgePairing σ Φ := by
  rw [routeUHardEdgePairing]
  congr 1
  have hsub := integral_comp_sq_eq_integral_Ioi
    (fun u : ℝ => Φ u * routeUHardEdgeDensity σ (Real.sqrt u))
  rw [← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have habs : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
  have hcos : routeUHardEdgeDensity σ |x| = routeUHardEdgeDensity σ x := by
    rw [routeUHardEdgeDensity, routeUHardEdgeDensity, routeUArchimedeanRate_abs]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  show routeUHardEdgeDensity σ x * Φ (x ^ 2)
    = Φ (x ^ 2) * routeUHardEdgeDensity σ (Real.sqrt (x ^ 2))
  rw [habs, hcos]
  ring



/-! ## The archimedean rate is the Hardy phase rate -/

theorem routeUArchimedeanPoint_eq_linePt (x : ℝ) :
    routeUArchimedeanPoint x = linePt x / 2 := by
  rw [routeUArchimedeanPoint, linePt]
  push_cast
  ring

/-- **The Route-U archimedean rate is the Gamma--Hardy phase rate.**  Both are
`(Re ψ(1/4 + i x/2) - log π)/2`, so the literal hard-edge density and the literal
Connes--Consani source use one and the same archimedean term. -/
theorem routeUArchimedeanRate_eq_gammaHardyPhaseRate (x : ℝ) :
    routeUArchimedeanRate x = gammaHardyPhaseRate x := by
  rw [routeUArchimedeanRate, gammaHardyPhaseRate, routeUArchimedeanPoint_eq_linePt]
  ring

/-! ## The literal restricted-Weil forms of the two parity sectors -/

/-- The restricted-Weil form of the even states `x ↦ H (x²)` and `x ↦ K (x²)`.  The polar term is
the value at `i/2`, whose square is `-1/4`. -/
def routeUEvenWeil (σ : ℝ) (H K : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, routeUHardEdgeDensity σ x * (H (x ^ 2) * K (x ^ 2)))
    + 2 * Real.pi * (H (-1 / 4) * K (-1 / 4))

/-- The restricted-Weil form of the odd states `x ↦ x·H (x²)` and `x ↦ x·K (x²)`.  The polar term
carries the extra factor `(i/2)² = -1/4`. -/
def routeUOddWeil (σ : ℝ) (H K : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, routeUHardEdgeDensity σ x * (x ^ 2 * (H (x ^ 2) * K (x ^ 2))))
    + 2 * Real.pi * (-1 / 4 * (H (-1 / 4) * K (-1 / 4)))

/-- **The even sector is the squared-variable pairing.** -/
theorem routeUEvenWeil_eq (σ : ℝ) (H K : ℝ → ℝ) :
    routeUEvenWeil σ H K = routeUHardEdgeEvenForm σ H K := by
  rw [routeUEvenWeil, routeUHardEdgeEvenForm,
    ← integral_density_comp_sq_eq_pairing σ fun u => H u * K u]

/-- **(HPJI.3) The odd sector is the squared-variable pairing with one factor of the coordinate.**
Multiplication by the Fourier variable is multiplication by `u` in the squared variable, including
the sign of the polar atom. -/
theorem routeUOddWeil_eq (σ : ℝ) (H K : ℝ → ℝ) :
    routeUOddWeil σ H K = routeUHardEdgeOddForm σ H K := by
  rw [routeUOddWeil, routeUHardEdgeOddForm,
    ← integral_density_comp_sq_eq_pairing σ fun u => u * (H u * K u)]

/-! ## Linearity of the pairing -/

theorem routeUHardEdgePairing_const_mul (σ : ℝ) (c : ℝ) (Φ : ℝ → ℝ) :
    routeUHardEdgePairing σ (fun u => c * Φ u) = c * routeUHardEdgePairing σ Φ := by
  have hint : (∫ u in Ioi (0 : ℝ), c * Φ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      = c * ∫ u in Ioi (0 : ℝ), Φ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [routeUHardEdgePairing, routeUHardEdgePairing, hint]
  ring

theorem routeUHardEdgePairing_add (σ : ℝ) (Φ Ψ : ℝ → ℝ)
    (hΦ : IntegrableOn
      (fun u : ℝ => Φ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hΨ : IntegrableOn
      (fun u : ℝ => Ψ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0)) :
    routeUHardEdgePairing σ (fun u => Φ u + Ψ u)
      = routeUHardEdgePairing σ Φ + routeUHardEdgePairing σ Ψ := by
  have hint : (∫ u in Ioi (0 : ℝ),
        (Φ u + Ψ u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      = (∫ u in Ioi (0 : ℝ), Φ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
        + ∫ u in Ioi (0 : ℝ), Ψ u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u := by
    rw [← integral_add hΦ hΨ]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [routeUHardEdgePairing, routeUHardEdgePairing, routeUHardEdgePairing, hint]
  ring


/-! ## The quadratic expansion and Cauchy--Schwarz on the form domain -/

/-- The quadratic expansion of the even form along a one-parameter family. -/
theorem routeUEvenForm_expand (σ : ℝ) (t : ℝ) (H K : ℝ → ℝ)
    (hHH : IntegrableOn (fun u : ℝ =>
      H u * H u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hHK : IntegrableOn (fun u : ℝ =>
      2 * t * (H u * K u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hKK : IntegrableOn (fun u : ℝ =>
      t ^ 2 * (K u * K u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0)) :
    routeUHardEdgeEvenForm σ (fun u => H u + t * K u) (fun u => H u + t * K u)
      = routeUHardEdgeEvenForm σ H H
        + 2 * t * routeUHardEdgeEvenForm σ H K
        + t ^ 2 * routeUHardEdgeEvenForm σ K K := by
  have hsplit : (fun u : ℝ => (H u + t * K u) * (H u + t * K u))
      = fun u : ℝ => (H u * H u + 2 * t * (H u * K u)) + t ^ 2 * (K u * K u) := by
    funext u
    ring
  have hadd1 : IntegrableOn (fun u : ℝ =>
      (H u * H u + 2 * t * (H u * K u)) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0) := by
    refine (hHH.add hHK).congr_fun ?_ measurableSet_Ioi
    intro u _
    simp only [Pi.add_apply]
    ring
  rw [routeUHardEdgeEvenForm, routeUHardEdgeEvenForm, routeUHardEdgeEvenForm,
    routeUHardEdgeEvenForm, hsplit,
    routeUHardEdgePairing_add σ _ _ hadd1 hKK,
    routeUHardEdgePairing_add σ _ _ hHH hHK,
    routeUHardEdgePairing_const_mul σ (2 * t) (fun u => H u * K u),
    routeUHardEdgePairing_const_mul σ (t ^ 2) (fun u => K u * K u)]


/-- **Cauchy--Schwarz for the even hard-edge form on its domain.** -/
theorem routeUEvenForm_sq_le (σ : ℝ) (H K : ℝ → ℝ)
    (hHH : IntegrableOn
      (fun u : ℝ => H u * H u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hHK : IntegrableOn
      (fun u : ℝ => H u * K u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hKK : IntegrableOn
      (fun u : ℝ => K u * K u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ t : ℝ,
      0 ≤ routeUHardEdgeEvenForm σ (fun u => H u + t * K u) (fun u => H u + t * K u)) :
    routeUHardEdgeEvenForm σ H K ^ 2
      ≤ routeUHardEdgeEvenForm σ H H * routeUHardEdgeEvenForm σ K K := by
  refine sq_le_of_quadratic_nonneg fun t => ?_
  have hHKt : IntegrableOn
      (fun u : ℝ => 2 * t * (H u * K u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0) := by
    refine (hHK.const_mul (2 * t)).congr (Filter.Eventually.of_forall fun u => ?_)
    ring
  have hKKt : IntegrableOn
      (fun u : ℝ => t ^ 2 * (K u * K u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0) := by
    refine (hKK.const_mul (t ^ 2)).congr (Filter.Eventually.of_forall fun u => ?_)
    ring
  rw [← routeUEvenForm_expand σ t H K hHH hHKt hKKt]
  exact hpsd t

/-! ## The parity recursion on divided jets -/

/-- **(HPJI.6) The one-step divided-jet recursion.**  Multiplying a divided-jet pairing by the
coordinate raises the jet index by one and adds `r` times the original. -/
theorem routeUHardEdgePairing_coord_jet (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ)
    (h1 : IntegrableOn (fun u : ℝ =>
      (u - r) ^ (k + 1) * G u ^ 2 * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (h2 : IntegrableOn (fun u : ℝ =>
      r * ((u - r) ^ k * G u ^ 2) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0)) :
    routeUHardEdgePairing σ (fun u => u * ((u - r) ^ k * G u ^ 2))
      = routeUHardEdgePairing σ (fun u => (u - r) ^ (k + 1) * G u ^ 2)
        + r * routeUHardEdgePairing σ (fun u => (u - r) ^ k * G u ^ 2) := by
  have hsplit : (fun u : ℝ => u * ((u - r) ^ k * G u ^ 2))
      = fun u : ℝ => (u - r) ^ (k + 1) * G u ^ 2 + r * ((u - r) ^ k * G u ^ 2) := by
    funext u
    rw [pow_succ]
    ring
  rw [hsplit, routeUHardEdgePairing_add σ _ _ h1 h2,
    routeUHardEdgePairing_const_mul σ r fun u => (u - r) ^ k * G u ^ 2]

/-- **(HPJI.7) Terminal odd energy is the root times terminal even mass.** -/
theorem routeUHardEdgePairing_coord_jet_terminal (σ : ℝ) (G : ℝ → ℝ) (r : ℝ) (k : ℕ)
    (h1 : IntegrableOn (fun u : ℝ =>
      (u - r) ^ (k + 1) * G u ^ 2 * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (h2 : IntegrableOn (fun u : ℝ =>
      r * ((u - r) ^ k * G u ^ 2) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0))
    (hvanish : routeUHardEdgePairing σ (fun u => (u - r) ^ (k + 1) * G u ^ 2) = 0) :
    routeUHardEdgePairing σ (fun u => u * ((u - r) ^ k * G u ^ 2))
      = r * routeUHardEdgePairing σ (fun u => (u - r) ^ k * G u ^ 2) := by
  rw [routeUHardEdgePairing_coord_jet σ G r k h1 h2, hvanish, zero_add]

/-- The odd form is the even form of the coordinate-multiplied state. -/
theorem routeUHardEdgeOddForm_eq (σ : ℝ) (H K : ℝ → ℝ) :
    routeUHardEdgeOddForm σ H K = routeUHardEdgeEvenForm σ (fun u => u * H u) K := by
  rw [routeUHardEdgeOddForm, routeUHardEdgeEvenForm]
  congr 1
  funext u
  ring

end RHTower

end
