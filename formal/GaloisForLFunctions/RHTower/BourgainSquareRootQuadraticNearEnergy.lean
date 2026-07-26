/-
# Sharp near-energy bound for the square-root quadratic model

At natural physical scales, every near pair in the quadratic triple cloud is
an exact `(Σn,Σn²)` pair.  The Eisenstein-divisor fiber bound therefore gives
an `H^ε` weighted near-energy estimate.  Combined with Gaussian perturbation
stability, this transfers the estimate to any point family uniformly close to
the square-root quadratic samples, without an additive Taylor error.
-/
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticCloud

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Quadratic-model near energy is bounded by the energy of exact parabola
moment fibers. -/
theorem bourgainQuadraticSample_nearEnergy_le_momentPairEnergy
    {H : ℕ} {a D : ℝ} (hD : 0 < D)
    (Y : BourgainPhaseSpace)
    (hY0 : D ≤ 2 * Y 0)
    (hY1 : D ^ (2 : ℕ) ≤ 2 * Y 1)
    (w : (Fin 3 → Fin H) → ℝ)
    (hw : ∀ h, 0 ≤ w h) :
    bourgainWeightedScaledNearEnergy Y
        (bourgainTripleCloud
          (bourgainSquareRootQuadraticSample a D)) w ≤
      ∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H,
        if bourgainParabolaTripleMoment h =
            bourgainParabolaTripleMoment h'
        then w h * w h' else 0 := by
  classical
  unfold bourgainWeightedScaledNearEnergy
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro h' hh'
  by_cases hnear :
      BourgainScaledNear Y
        (bourgainTripleCloud
          (bourgainSquareRootQuadraticSample a D) h)
        (bourgainTripleCloud
          (bourgainSquareRootQuadraticSample a D) h')
  · have hmoment :=
      bourgainParabolaTripleMoment_eq_of_quadraticSample_near
        hD hY0 hY1 hnear
    simp [hnear, hmoment]
  · simp only [hnear, if_false]
    split_ifs
    · exact mul_nonneg (hw h) (hw h')
    · exact le_rfl

/-- Exact moment-pair energy is the squared mass of the moment fibers. -/
theorem bourgainMomentPairEnergy_eq_fiberMass
    {H : ℕ} (w : (Fin 3 → Fin H) → ℝ) :
    (∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H,
        if bourgainParabolaTripleMoment h =
            bourgainParabolaTripleMoment h'
        then w h * w h' else 0) =
      ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        (∑ h ∈
            (Finset.univ : Finset (Fin 3 → Fin H)).filter
              (fun h => bourgainParabolaTripleMoment h = y),
          w h) ^ (2 : ℕ) := by
  simpa using
    (sum_cellMass_sq_eq_sameCell w bourgainParabolaTripleMoment).symm

/-- Finite Cauchy--Schwarz bound for nonnegative masses on parabola fibers. -/
theorem bourgainParabolaFiberMass_sq_le
    {H : ℕ} (w : (Fin 3 → Fin H) → ℝ)
    (hw : ∀ h, 0 ≤ w h) {R : ℝ}
    (hfiber :
      ∀ y ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment,
        (((Finset.univ : Finset (Fin 3 → Fin H)).filter
          fun h => bourgainParabolaTripleMoment h = y).card : ℝ) ≤ R) :
    (∑ y ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment,
      (∑ h ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => bourgainParabolaTripleMoment h = y),
        w h) ^ (2 : ℕ)) ≤
      R * ∑ h : Fin 3 → Fin H, w h ^ (2 : ℕ) := by
  have hcomplex :=
    sum_norm_fiberSum_sq_le bourgainParabolaTripleMoment
      (fun h => (w h : ℂ)) hfiber
  have hsum
      (s : Finset (Fin 3 → Fin H)) :
      ‖∑ h ∈ s, (w h : ℂ)‖ = ∑ h ∈ s, w h := by
    have hs0 : 0 ≤ ∑ h ∈ s, w h :=
      Finset.sum_nonneg fun h hh => hw h
    rw [show
        (∑ h ∈ s, (w h : ℂ)) =
          ((∑ h ∈ s, w h : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  simpa only [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw _)] using hcomplex

/-- Exact parabola-moment pair energy has the same sharp subpower bound. -/
theorem bourgainMomentPairEnergy_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (w : (Fin 3 → Fin H) → ℝ),
        (∀ h, 0 ≤ w h) →
        (∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H,
          if bourgainParabolaTripleMoment h =
              bourgainParabolaTripleMoment h'
          then w h * w h' else 0) ≤
            C * (H : ℝ) ^ ε *
              ∑ h : Fin 3 → Fin H, w h ^ (2 : ℕ) := by
  obtain ⟨C, hC, hfiber⟩ :=
    card_bourgainParabolaTripleMoment_fiber_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H w hw
  rw [bourgainMomentPairEnergy_eq_fiberMass]
  exact bourgainParabolaFiberMass_sq_le w hw (hfiber H)

/-- Sharp `H^ε` near-energy estimate for the quadratic square-root model. -/
theorem bourgainQuadraticSample_nearEnergy_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a D : ℝ), 0 < D →
      ∀ (Y : BourgainPhaseSpace),
        D ≤ 2 * Y 0 →
        D ^ (2 : ℕ) ≤ 2 * Y 1 →
      ∀ (w : (Fin 3 → Fin H) → ℝ),
        (∀ h, 0 ≤ w h) →
        bourgainWeightedScaledNearEnergy Y
            (bourgainTripleCloud
              (bourgainSquareRootQuadraticSample a D)) w ≤
          C * (H : ℝ) ^ ε *
            ∑ h : Fin 3 → Fin H, w h ^ (2 : ℕ) := by
  obtain ⟨C, hC, hfiber⟩ :=
    card_bourgainParabolaTripleMoment_fiber_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a D hD Y hY0 hY1 w hw
  calc
    bourgainWeightedScaledNearEnergy Y
          (bourgainTripleCloud
            (bourgainSquareRootQuadraticSample a D)) w
        ≤ ∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H,
            if bourgainParabolaTripleMoment h =
                bourgainParabolaTripleMoment h'
            then w h * w h' else 0 :=
      bourgainQuadraticSample_nearEnergy_le_momentPairEnergy
        hD Y hY0 hY1 w hw
    _ = ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        (∑ h ∈
            (Finset.univ : Finset (Fin 3 → Fin H)).filter
              (fun h => bourgainParabolaTripleMoment h = y),
          w h) ^ (2 : ℕ) :=
      bourgainMomentPairEnergy_eq_fiberMass w
    _ ≤ (C * (H : ℝ) ^ ε) *
          ∑ h : Fin 3 → Fin H, w h ^ (2 : ℕ) :=
      bourgainParabolaFiberMass_sq_le w hw (hfiber H)
    _ = C * (H : ℝ) ^ ε *
          ∑ h : Fin 3 → Fin H, w h ^ (2 : ℕ) := by ring

/-- Coefficient form of the sharp quadratic-model near-energy estimate. -/
theorem bourgainQuadraticSample_weighted_nearEnergy_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a D : ℝ), 0 < D →
      ∀ (Y : BourgainPhaseSpace),
        D ≤ 2 * Y 0 →
        D ^ (2 : ℕ) ≤ 2 * Y 1 →
      ∀ c : Fin H → ℂ,
        bourgainWeightedScaledNearEnergy Y
            (bourgainTripleCloud
              (bourgainSquareRootQuadraticSample a D))
            (fun h => ‖bourgainTripleWeight c h‖) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hnear⟩ :=
    bourgainQuadraticSample_nearEnergy_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a D hD Y hY0 hY1 c
  calc
    _ ≤ C * (H : ℝ) ^ ε *
          ∑ h : Fin 3 → Fin H,
            ‖bourgainTripleWeight c h‖ ^ (2 : ℕ) :=
      hnear H a D hD Y hY0 hY1
        (fun h => ‖bourgainTripleWeight c h‖)
        (fun h => norm_nonneg _)
    _ = _ := by
      rw [sum_norm_bourgainTripleWeight_sq]

/-- Perturbation-stable Gaussian `L²` estimate for exact local curve samples.
Only the pointwise scaled Taylor bound and two natural scale inequalities are
required. -/
theorem integral_bourgainPerturbedSquareRootTriple_gaussian_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a D δ : ℝ), 0 ≤ δ → 0 < D →
      ∀ (X : BourgainPhaseSpace)
        (p : Fin H → BourgainPhaseSpace),
        D ≤ 2 * bourgainPerturbedSpacingScale (3 * δ) X 0 →
        D ^ (2 : ℕ) ≤
          2 * bourgainPerturbedSpacingScale (3 * δ) X 1 →
        (∀ n j,
          |X j *
            (p n j -
              bourgainSquareRootQuadraticSample a D n j)| ≤ δ) →
      ∀ c : Fin H → ℂ,
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand X
            (bourgainTripleCloud p)
            (bourgainTripleWeight c) x) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀, hmodel⟩ :=
    bourgainQuadraticSample_weighted_nearEnergy_subpower hε
  refine ⟨331776 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro H a D δ hδ hD X p hX0 hX1 hperturb c
  calc
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand X
          (bourgainTripleCloud p)
          (bourgainTripleWeight c) x)
        ≤ 331776 *
          bourgainWeightedScaledNearEnergy
            (bourgainPerturbedSpacingScale (3 * δ) X)
            (bourgainTripleCloud
              (bourgainSquareRootQuadraticSample a D))
            (fun h => ‖bourgainTripleWeight c h‖) :=
      integral_bourgainTripleCloud_gaussian_le_perturbed
        hδ X p (bourgainSquareRootQuadraticSample a D)
        (bourgainTripleWeight c) hperturb
    _ ≤ 331776 *
        (C₀ * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
      gcongr
      exact hmodel H a D hD
        (bourgainPerturbedSpacingScale (3 * δ) X)
        hX0 hX1 c
    _ = (331776 * C₀) * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      ring

end

end RHTower
