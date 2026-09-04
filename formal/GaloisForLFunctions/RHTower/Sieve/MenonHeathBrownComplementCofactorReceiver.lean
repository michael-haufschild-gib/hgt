import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCofactorMontgomery
import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateDerivativeReceiver

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

abbrev menonHeathBrownComplementIndex
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) :=
  {i : HeathBrownBoxFactorIndex k box.m // i ∈ (Finset.univ.erase j)}

def menonHeathBrownComplementKind
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) :
    menonHeathBrownComplementIndex box j → HeathBrownFactorKind := fun i =>
  heathBrownBoxFactorKind k box.m i

def menonHeathBrownComplementExponent
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) :
    menonHeathBrownComplementIndex box j → ℕ := fun i =>
  heathBrownBoxFactorExponent box.a box.b box.q i

/-- A selected factor can be bounded pointwise while the exact erase-complement, still multiplied
by an arbitrary cofactor polynomial, is paid by fixed-shift Montgomery. -/
theorem exists_meanSquare_heathBrownBox_shift_mul_dirPoly_le_selectedFactor
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
        (j : HeathBrownBoxFactorIndex k box.m) {sigma V : ℝ},
        0 ≤ sigma → 0 ≤ V →
        ∀ (M : ℕ), 1 ≤ M → ∀ (b : Fin M → ℂ) (u : ℝ)
          {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ},
          0 < delta → 0 ≤ T →
          (∀ i, lam i + delta ≤ lam (i + 1)) →
          (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) →
          (∀ r ∈ S,
            ‖heathBrownBoxFactorValue L X k box
              ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) j‖ ≤ V) →
          ∑ r ∈ S,
              ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
                  ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) *
                dirPoly M b (-lam r)‖ ^ 2 ≤
            V ^ 2 *
              ((T + 4 *
                    ((groupedDyadicUpper
                      (menonHeathBrownComplementExponent box j)) * M : ℕ) *
                    (1 + Real.log
                      ((groupedDyadicUpper
                        (menonHeathBrownComplementExponent box j)) * M))) *
                (1 / delta + 2 * Real.log
                  ((groupedDyadicUpper
                    (menonHeathBrownComplementExponent box j)) * M)) *
                (C *
                  ((((groupedDyadicUpper
                    (menonHeathBrownComplementExponent box j)) * M : ℕ) : ℝ)) ^ epsilon *
                  ((((groupedDyadicLower
                    (menonHeathBrownComplementExponent box j) : ℝ) ^ (-sigma)) ^ 2 *
                    ((groupedDyadicUpper
                      (menonHeathBrownComplementExponent box j) : ℝ) *
                      (1 + Real.log (groupedDyadicUpper
                        (menonHeathBrownComplementExponent box j) : ℝ)) ^
                        (2 * Fintype.card (menonHeathBrownComplementIndex box j) +
                          (2 ^ (2 * Fintype.card
                            (menonHeathBrownComplementIndex box j)) - 1)))) *
                    ∑ m : Fin M, ‖b m‖ ^ 2))) := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_meanSquare_heathBrown_grouped_shift_mul_dirPoly_finset hepsilon
  refine ⟨C, hC, ?_⟩
  intro L X k box j sigma V hsigma hV M hM b u S lam delta T hdelta hT hgap hband
    hselected
  let I := menonHeathBrownComplementIndex box j
  let kind : I → HeathBrownFactorKind := menonHeathBrownComplementKind box j
  let q : I → ℕ := menonHeathBrownComplementExponent box j
  let G : ℝ := (groupedDyadicUpper q : ℝ) *
    (1 + Real.log (groupedDyadicUpper q : ℝ)) ^
      (2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1))
  letI : Nonempty I := heathBrownBoxFactor_complement_nonempty box j
  have henergy :
      ∑ n : Fin (groupedDyadicUpper q),
          ‖groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q n‖ ^ 2 ≤ G := by
    simpa only [G] using sum_normSq_heathBrownGrouped_le_fixed_polylog L X kind q
  have hcomplement := hmean L X kind q hsigma henergy M hM b u
    hdelta hT hgap hband
  have hpoint : ∀ r ∈ S,
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) *
        dirPoly M b (-lam r)‖ ^ 2 ≤
      V ^ 2 *
        ‖(∏ i : I, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (kind i)) (q i)))
              ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
          dirPoly M b (-lam r)‖ ^ 2 := by
    intro r hr
    let s : ℂ := (sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I
    let D : ℂ := dirPoly M b (-lam r)
    let P : ℂ := ∏ i : I, LSeries
      (complexCoeff (arithmeticDyadicBlock
        (heathBrownFactorBase L X (kind i)) (q i))) s
    have hfactor :
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ =
          ‖heathBrownBoxFactorValue L X k box s j‖ * ‖P‖ := by
      simpa only [I, kind, q, P, menonHeathBrownComplementKind,
        menonHeathBrownComplementExponent] using
        norm_heathBrownBox_core_eq_factor_mul_complement box j s
    have hnorm :
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s * D‖ =
          ‖heathBrownBoxFactorValue L X k box s j‖ * ‖P * D‖ := by
      rw [norm_mul, hfactor, norm_mul]
      ring
    have hsel : ‖heathBrownBoxFactorValue L X k box s j‖ ≤ V := by
      simpa only [s] using hselected r hr
    have hselSq : ‖heathBrownBoxFactorValue L X k box s j‖ ^ 2 ≤ V ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsel 2
    rw [show
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) *
          dirPoly M b (-lam r) =
        heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s * D by rfl,
      hnorm, mul_pow]
    exact mul_le_mul_of_nonneg_right hselSq (sq_nonneg ‖P * D‖)
  calc
    ∑ r ∈ S,
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
            ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) *
          dirPoly M b (-lam r)‖ ^ 2
        ≤ ∑ r ∈ S, V ^ 2 *
            ‖(∏ i : I, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X (kind i)) (q i)))
                  ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
              dirPoly M b (-lam r)‖ ^ 2 :=
          Finset.sum_le_sum fun r hr => hpoint r hr
    _ = V ^ 2 * ∑ r ∈ S,
            ‖(∏ i : I, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X (kind i)) (q i)))
                  ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)) *
              dirPoly M b (-lam r)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ V ^ 2 *
        ((T + 4 * ((groupedDyadicUpper q) * M : ℕ) *
              (1 + Real.log ((groupedDyadicUpper q) * M))) *
          (1 / delta + 2 * Real.log ((groupedDyadicUpper q) * M)) *
          (C * ((((groupedDyadicUpper q) * M : ℕ) : ℝ)) ^ epsilon *
            ((((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) *
              ∑ m : Fin M, ‖b m‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hcomplement (sq_nonneg V)
    _ = _ := by simp only [I, q, G]

end RHTower.Sieve
