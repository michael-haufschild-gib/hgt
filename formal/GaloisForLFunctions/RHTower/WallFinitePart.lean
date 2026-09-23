import GaloisForLFunctions.RHTower.WallThirdRemainderTail

/-!
# `(46)`: the finite part of the transported source

The three-fold expansion of `∫_Y^x` has three boundary terms at each endpoint and an absolutely
convergent remainder.  Subtracting the three endpoint terms at `x` leaves a quantity with a limit as
`x → ∞`, and that limit is the finite part:

`FP_Y = −[boundary terms at Y] + i∫_Y^∞ E ∂D₂`.

Written with the finite part isolated, the transported source is

`∫_Y^x E = [boundary terms at x] + FP_Y − i∫_x^∞ E ∂D₂`,

so everything that depends on the evaluation point is either a boundary term at that point — each
already square integrable after multiplication by the frequency — or the tail, which is `O(x^{-2})`
after transport.  What is left is the frequency-independent charge.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [CompleteSpace X] [InnerProductSpace ℂ X] in
/-- A terminal ray splits at any interior point. -/
theorem integral_Ioi_eq_intervalIntegral_add_tail {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} {a b : ℝ} (hab : a ≤ b) (hint : IntegrableOn f (Ioi a)) :
    (∫ t in Ioi a, f t) = (∫ t in a..b, f t) + ∫ t in Ioi b, f t := by
  have hunion : Ioi a = Ioc a b ∪ Ioi b := (Ioc_union_Ioi_eq_Ioi hab).symm
  have hdisj : Disjoint (Ioc a b) (Ioi b) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have h1 : IntegrableOn f (Ioc a b) := hint.mono_set (by rw [hunion]; exact subset_union_left)
  have h2 : IntegrableOn f (Ioi b) := hint.mono_set (by rw [hunion]; exact subset_union_right)
  rw [hunion, setIntegral_union hdisj measurableSet_Ioi h1 h2,
    intervalIntegral.integral_of_le hab]

/-- The three-fold remainder integrand is integrable on a terminal ray past the threshold. -/
theorem integrableOn_wallThirdIntegrand {σ L μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {x : ℝ} (hx : 1 ≤ x) (hfloor : ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L) :
    IntegrableOn (fun t : ℝ => wallPhaseMap E T σ L t * invFamilyProduct2Deriv
      (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
      (wallGeneratorD3 X σ) t) (Ioi x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hcont := continuousOn_wallThirdIntegrand (T := T) hEdiff hE hEne hσ0 hσ1
    (S := Ioi x) (fun t ht => lt_of_lt_of_le hμ (hfloor t ht))
  refine integrableOn_of_powerTail_bound (q := 3 - (1 / 2 + σ))
    (C := K₂ * wallAmplitude3Const μ₀) (by linarith) hx0
    (hcont.aestronglyMeasurable measurableSet_Ioi) (fun t ht => ?_)
  have ht1 : (1 : ℝ) ≤ |t| := by
    have : x < t := ht
    rw [abs_of_pos (lt_trans hx0 this)]
    linarith
  exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ ht1 (hfloor t ht)

/-- **`(46)`: the finite part of the transported source at the threshold.**  It is what remains of
`∫_Y^x` after the three endpoint terms at `x` are subtracted, and it converges because the three-fold
remainder is absolutely integrable on the ray. -/
def wallFinitePart (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ L Y : ℝ) : X →L[ℂ] X :=
  -((Complex.I : ℂ) • (wallPhaseMap E T σ L Y * invFamily (wallGeneratorShift T σ L) Y)
      + wallPhaseMap E T σ L Y
        * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y
      - (Complex.I : ℂ) • (wallPhaseMap E T σ L Y
          * invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
            (wallGeneratorD2 X σ) Y))
    + (Complex.I : ℂ) • ∫ t in Ioi Y, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
        (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
        (wallGeneratorD3 X σ) t

/-- **The transported source, with the finite part isolated.**  Everything that depends on the
evaluation point is either a boundary term at that point or the absolutely convergent tail. -/
theorem wall_phase_finitePart_decomposition {σ L μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {Y x : ℝ} (hY : 1 ≤ Y) (hYx : Y ≤ x)
    (hfloor : ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L)
    (hgapY : μ₀ ≤ wallFloor T σ Y + L) :
    (∫ t in Y..x, wallPhaseMap E T σ L t * 1)
      = ((Complex.I : ℂ) • (wallPhaseMap E T σ L x * invFamily (wallGeneratorShift T σ L) x)
          + wallPhaseMap E T σ L x
            * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x
          - (Complex.I : ℂ) • (wallPhaseMap E T σ L x
              * invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) x))
        + wallFinitePart E T σ L Y
        - (Complex.I : ℂ) • ∫ t in Ioi x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
            (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
            (wallGeneratorD3 X σ) t := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hgap : ∀ t ∈ uIcc Y x, 0 < wallFloor T σ t + L := by
    intro t ht
    rw [uIcc_of_le hYx] at ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      exact lt_of_lt_of_le hμ hgapY
    · exact lt_of_lt_of_le hμ (hfloor t h)
  have hint : IntegrableOn (fun t : ℝ => wallPhaseMap E T σ L t * invFamilyProduct2Deriv
      (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
      (wallGeneratorD3 X σ) t) (Ioi Y) :=
    integrableOn_wallThirdIntegrand hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hY hfloor
  have hsplit := integral_Ioi_eq_intervalIntegral_add_tail hYx hint
  have hibp := wall_phase_ibp_thrice (E := E) (T := T) (σ := σ) (L := L) (a := Y) (b := x)
    hEdiff hE hEne hσ0 hσ1 hgap
  rw [hibp, wallFinitePart]
  have htail : (∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
      (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
      (wallGeneratorD3 X σ) t)
      = (∫ t in Ioi Y, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
          (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
          (wallGeneratorD3 X σ) t)
        - ∫ t in Ioi x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
          (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
          (wallGeneratorD3 X σ) t := by
    rw [hsplit]
    abel
  rw [htail]
  simp only [smul_sub]
  abel

end GaloisForLFunctions.RHTower
