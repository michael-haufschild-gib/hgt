import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerSecantGraphCompletion

/-!
# Route P primitive Burnol / Deninger four-leg Hodge completion

P-G201 puts every upper squared-Cauchy reporter in an explicit source graph completion, but the
canonical lower/upper cup is not its Hilbert energy.  This file classifies that obstruction and
constructs the minimal matrix-complete replacement.

Pulling an upper packet through conjugation gives an actual lower absolute-Euler packet.  On the
Xi jet carrier its realization is coefficientwise conjugation after critical-line reindexing.
Consequently conjugated upper secants give explicit lower secants converging strongly to the
lower squared-Cauchy jet.  The natural two-leg diagonal `inner (star x) x` remains complex
bilinear: multiplying the same graph vector by `I` reverses its sign, so phase-independent
nonnegativity forces it to vanish.

The missing positive object therefore has four legs: upper, line-reflected upper, lower, and
conjugate lower.  Coefficient conjugation of the completed lower leg equals the line-reflected
upper leg exactly.  Its Hodge pairing is the ordinary Hilbert square, and every finite four-leg
Gram equals the original upper squared-Cauchy graph Gram entrywise.  At primitive Burnol points,
functional-equation reflection flips the ordinate while complex conjugation preserves it, making
the four source poles explicit.

No zero-location, positivity, simplicity, or RH hypothesis is used.
-/

open Complex Filter Topology Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Pull an upper finite packet back to the conjugate lower source sector without changing its
coefficients. -/
def routePDeningerUpperPacketConjToLower
    (y : DeningerPrimeGammaUpperPacket) : DeningerPrimeGammaLowerPacket :=
  Finsupp.equivMapDomain deningerPrimeGammaPointConjEquiv.symm y

@[simp] theorem routePDeningerUpperPacketConjToLower_apply
    (y : DeningerPrimeGammaUpperPacket) (z : DeningerPrimeGammaLowerPoint) :
    routePDeningerUpperPacketConjToLower y z =
      y (deningerPrimeGammaPointConjEquiv z) := by
  simp [routePDeningerUpperPacketConjToLower]

@[simp] theorem routePDeningerUpperPacketConjToLower_single
    (w : DeningerPrimeGammaUpperPoint) (d : ℂ) :
    routePDeningerUpperPacketConjToLower (Finsupp.single w d) =
      Finsupp.single (deningerPrimeGammaPointConjEquiv.symm w) d := by
  simp [routePDeningerUpperPacketConjToLower]

theorem deningerPrimeGammaLowerCauchyTest_add
    (x y : DeningerPrimeGammaLowerPacket) (a : ℂ) :
    deningerPrimeGammaLowerCauchyTest (x + y) a =
      deningerPrimeGammaLowerCauchyTest x a +
        deningerPrimeGammaLowerCauchyTest y a := by
  unfold deningerPrimeGammaLowerCauchyTest
  rw [Finsupp.sum_add_index'
    (fun _ => zero_mul _)
    (fun _ c d => add_mul c d _)]

theorem deningerPrimeGammaLowerCauchyTest_upperPacketConjToLower
    (y : DeningerPrimeGammaUpperPacket) (a : ℂ) :
    deningerPrimeGammaLowerCauchyTest
        (routePDeningerUpperPacketConjToLower y) a =
      (starRingEnd ℂ)
        (deningerPrimeGammaUpperCauchyTest y ((starRingEnd ℂ) a)) := by
  classical
  induction y using Finsupp.induction with
  | zero => simp [routePDeningerUpperPacketConjToLower,
      deningerPrimeGammaLowerCauchyTest,
      deningerPrimeGammaUpperCauchyTest,
      deningerPrimeGammaUpperSharpCauchyTest, xiWeilSharp]
  | @single_add w d y hwy hd ih =>
      rw [show routePDeningerUpperPacketConjToLower (Finsupp.single w d + y) =
          Finsupp.single (deningerPrimeGammaPointConjEquiv.symm w) d +
            routePDeningerUpperPacketConjToLower y by
        apply Finsupp.ext
        intro z
        rw [routePDeningerUpperPacketConjToLower_apply]
        by_cases h : deningerPrimeGammaPointConjEquiv z = w
        · have hz : z = deningerPrimeGammaPointConjEquiv.symm w := by
            exact (deningerPrimeGammaPointConjEquiv.symm_apply_apply z).symm.trans
              (congrArg deningerPrimeGammaPointConjEquiv.symm h)
          simp [hz]
        · have hz : z ≠ deningerPrimeGammaPointConjEquiv.symm w := by
            intro hz
            apply h
            rw [hz, Equiv.apply_symm_apply]
          simp [h, hz]]
      rw [deningerPrimeGammaLowerCauchyTest_add]
      rw [deningerPrimeGammaUpperCauchyTest_add]
      simp only [map_add]
      rw [deningerPrimeGammaLowerCauchyTest_single,
        deningerPrimeGammaUpperCauchyTest_single, ih]
      simp [deningerPrimeGammaPointConjEquiv, xiWeilCauchyTest]

/-- Upper packet realization followed by critical-line reindexing and coefficient conjugation is
literally the lower packet realization at conjugate source poles. -/
theorem deningerPrimeGammaLowerToJetHilbert_upperPacketConjToLower
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaLowerToJetHilbert
        (routePDeningerUpperPacketConjToLower y) =
      star (xiWeilLineConjLp (deningerPrimeGammaUpperToJetHilbert y)) := by
  apply Subtype.ext
  funext (q : XiZeroCopy)
  rw [deningerPrimeGammaLowerToJetHilbert_apply]
  rw [deningerPrimeGammaLowerCauchyTest_upperPacketConjToLower]
  change _ = (starRingEnd ℂ)
    (deningerPrimeGammaUpperToJetHilbert y
      (xiZeroCopyLineConjEquiv q))
  rw [deningerPrimeGammaUpperToJetHilbert_apply,
    xiSpectralPoint_lineConj]

/-- Conjugate lower-sector secant attached to one coalescing upper source packet. -/
def routePDeningerLowerSecantPacket
    (A : ℂ) (z : DeningerPrimeGammaLowerPoint) (n : ℕ) :
    DeningerPrimeGammaLowerPacket :=
  routePDeningerUpperPacketConjToLower
    (routePDeningerUpperSecantPacket ((starRingEnd ℂ) A)
      (deningerPrimeGammaPointConjEquiv z) n)

/-- Four-leg lower squared-Cauchy jet: conjugate coefficients after critical-line reindexing of
the upper graph jet at the conjugate pole. -/
def routePDeningerLowerSquaredCauchyJet
    (A : ℂ) (z : DeningerPrimeGammaLowerPoint) :
    DeningerArithmeticJetHilbert :=
  star (xiWeilLineConjLp
    (routePDeningerUpperSquaredCauchyJet ((starRingEnd ℂ) A)
      (deningerPrimeGammaPointConjEquiv z)))

@[simp] theorem routePDeningerLowerSquaredCauchyJet_apply
    (A : ℂ) (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) :
    routePDeningerLowerSquaredCauchyJet A z q =
      A * xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) ^ 2 := by
  change (starRingEnd ℂ)
      (routePDeningerUpperSquaredCauchyTest ((starRingEnd ℂ) A)
        (deningerPrimeGammaPointConjEquiv z)
        (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) = _
  rw [xiSpectralPoint_lineConj]
  simp only [routePDeningerUpperSquaredCauchyTest, map_mul, map_pow,
    starRingEnd_self_apply]
  congr 1
  simp [xiWeilCauchyTest, deningerPrimeGammaPointConjEquiv]

/-- Lower absolute-Euler source secants converge strongly to the lower squared-Cauchy graph jet.
The packet nodes and coefficients are obtained solely by conjugating the explicit upper source
secants. -/
theorem tendsto_routePDeningerLowerSecantPacket_to_squaredCauchyJet
    (A : ℂ) (z : DeningerPrimeGammaLowerPoint) :
    Tendsto
      (fun n => deningerPrimeGammaLowerToJetHilbert
        (routePDeningerLowerSecantPacket A z n))
      atTop (nhds (routePDeningerLowerSquaredCauchyJet A z)) := by
  have h := tendsto_routePDeningerUpperSecantPacket_to_squaredCauchyJet
    ((starRingEnd ℂ) A) (deningerPrimeGammaPointConjEquiv z)
  have hcont : Continuous (fun v : DeningerArithmeticJetHilbert =>
      star (xiWeilLineConjLinearIsometry v)) :=
    continuous_star.comp xiWeilLineConjLinearIsometry.continuous
  have hmapped := hcont.continuousAt.tendsto.comp h
  simp only [routePDeningerLowerSecantPacket,
    routePDeningerLowerSquaredCauchyJet,
    deningerPrimeGammaLowerToJetHilbert_upperPacketConjToLower]
  change Tendsto
    ((fun v : DeningerArithmeticJetHilbert => star (xiWeilLineConjLp v)) ∘
      (fun n => deningerPrimeGammaUpperToJetHilbert
        (routePDeningerUpperSecantPacket ((starRingEnd ℂ) A)
          (deningerPrimeGammaPointConjEquiv z) n)))
    atTop
    (nhds (star (xiWeilLineConjLp
      (routePDeningerUpperSquaredCauchyJet ((starRingEnd ℂ) A)
        (deningerPrimeGammaPointConjEquiv z)))))
  exact hmapped

/-- Natural two-leg diagonal supplied by the line-reflected upper/lower source cup. -/
def routePDeningerTwoLegCupDiagonal
    (x : DeningerArithmeticJetHilbert) : ℂ :=
  inner ℂ (star x) x

/-- The natural two-leg diagonal has complex-bilinear phase: a quarter-turn reverses it. Hence it
cannot itself be a phase-independent positive Hodge metric. -/
theorem routePDeningerTwoLegCupDiagonal_I_mul
    (x : DeningerArithmeticJetHilbert) :
    routePDeningerTwoLegCupDiagonal (I • x) =
      -routePDeningerTwoLegCupDiagonal x := by
  rw [routePDeningerTwoLegCupDiagonal, routePDeningerTwoLegCupDiagonal]
  rw [star_smul, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_star]
  rw [← mul_assoc, I_mul_I, neg_one_mul]

/-- Exact phase obstruction: if the natural two-leg diagonal were nonnegative before and after a
quarter-turn of the same graph vector, it would have to vanish. -/
theorem routePDeningerTwoLegCupDiagonal_eq_zero_of_phase_nonneg
    (x : DeningerArithmeticJetHilbert)
    (hx : 0 ≤ routePDeningerTwoLegCupDiagonal x)
    (hIx : 0 ≤ routePDeningerTwoLegCupDiagonal (I • x)) :
    routePDeningerTwoLegCupDiagonal x = 0 := by
  rw [routePDeningerTwoLegCupDiagonal_I_mul] at hIx
  have hx' := RCLike.nonneg_iff.mp hx
  have hIx' := RCLike.nonneg_iff.mp hIx
  have hxre : 0 ≤ (routePDeningerTwoLegCupDiagonal x).re := by
    simpa using hx'.1
  have hIxre : 0 ≤ -(routePDeningerTwoLegCupDiagonal x).re := by
    simpa using hIx'.1
  have hre : (routePDeningerTwoLegCupDiagonal x).re = 0 := by
    linarith [hxre, hIxre]
  apply Complex.ext
  · simpa using hre
  · exact hx'.2

/-- The fourth leg is coefficient conjugation of the completed lower squared-Cauchy source jet. -/
def routePDeningerUpperFourLegHodgeMate
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    DeningerArithmeticJetHilbert :=
  star (routePDeningerLowerSquaredCauchyJet ((starRingEnd ℂ) A)
    (deningerPrimeGammaPointConjEquiv.symm w))

/-- Exact four-leg closure: conjugate-lower graph completion is precisely critical-line
reindexing of the original upper graph completion. -/
theorem routePDeningerUpperFourLegHodgeMate_eq_lineConj
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    routePDeningerUpperFourLegHodgeMate A w =
      xiWeilLineConjLp (routePDeningerUpperSquaredCauchyJet A w) := by
  simp only [routePDeningerUpperFourLegHodgeMate,
    routePDeningerLowerSquaredCauchyJet, star_star,
    starRingEnd_self_apply, Equiv.apply_symm_apply]

/-- Conjugate-lower finite source secants converge strongly to the four-leg Hodge mate. -/
theorem tendsto_routePDeningerConjugateLowerSecantPacket_to_fourLegHodgeMate
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    Tendsto
      (fun n => star (deningerPrimeGammaLowerToJetHilbert
        (routePDeningerLowerSecantPacket ((starRingEnd ℂ) A)
          (deningerPrimeGammaPointConjEquiv.symm w) n)))
      atTop (nhds (routePDeningerUpperFourLegHodgeMate A w)) := by
  have h := tendsto_routePDeningerLowerSecantPacket_to_squaredCauchyJet
    ((starRingEnd ℂ) A) (deningerPrimeGammaPointConjEquiv.symm w)
  exact continuous_star.continuousAt.tendsto.comp h

/-- Four-leg Hodge pairing is the ordinary Hilbert square, not the phase-unstable two-leg
bilinear diagonal. -/
theorem inner_lineConj_upperSquaredCauchyJet_fourLegHodgeMate
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    inner ℂ
        (xiWeilLineConjLp (routePDeningerUpperSquaredCauchyJet A w))
        (routePDeningerUpperFourLegHodgeMate A w) =
      inner ℂ (routePDeningerUpperFourLegHodgeMate A w)
        (routePDeningerUpperFourLegHodgeMate A w) := by
  rw [routePDeningerUpperFourLegHodgeMate_eq_lineConj]
  exact rfl

theorem norm_routePDeningerUpperFourLegHodgeMate
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    ‖routePDeningerUpperFourLegHodgeMate A w‖ =
      ‖routePDeningerUpperSquaredCauchyJet A w‖ := by
  rw [routePDeningerUpperFourLegHodgeMate_eq_lineConj]
  exact norm_xiWeilLineConjLp
    (routePDeningerUpperSquaredCauchyJet A w :
      lp (fun _ : XiZeroCopy => ℂ) 2)

theorem re_inner_lineConj_upperSquaredCauchyJet_fourLegHodgeMate
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    (inner ℂ
        (xiWeilLineConjLp (routePDeningerUpperSquaredCauchyJet A w))
        (routePDeningerUpperFourLegHodgeMate A w)).re =
      ‖routePDeningerUpperSquaredCauchyJet A w‖ ^ 2 := by
  rw [inner_lineConj_upperSquaredCauchyJet_fourLegHodgeMate]
  calc
    (inner ℂ (routePDeningerUpperFourLegHodgeMate A w)
      (routePDeningerUpperFourLegHodgeMate A w)).re =
        ‖routePDeningerUpperFourLegHodgeMate A w‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner
        (𝕜 := ℂ) (routePDeningerUpperFourLegHodgeMate A w)).symm
    _ = ‖routePDeningerUpperSquaredCauchyJet A w‖ ^ 2 := by
      rw [norm_routePDeningerUpperFourLegHodgeMate]

/-- Matrix-complete four-leg source graph Gram. -/
def routePDeningerFourLegHodgeGram {N : ℕ}
    (A : Fin N → ℂ) (w : Fin N → DeningerPrimeGammaUpperPoint) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i => routePDeningerUpperFourLegHodgeMate (A i) (w i))

theorem routePDeningerFourLegHodgeGram_posSemidef {N : ℕ}
    (A : Fin N → ℂ) (w : Fin N → DeningerPrimeGammaUpperPoint) :
    (routePDeningerFourLegHodgeGram A w).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ _

/-- The four-leg source Gram is exactly the upper squared-Cauchy graph Gram at every matrix
entry. This is a genuine matrix identity, not scalar diagonal positivity. -/
theorem routePDeningerFourLegHodgeGram_apply {N : ℕ}
    (A : Fin N → ℂ) (w : Fin N → DeningerPrimeGammaUpperPoint)
    (i j : Fin N) :
    routePDeningerFourLegHodgeGram A w i j =
      inner ℂ (routePDeningerUpperSquaredCauchyJet (A i) (w i))
        (routePDeningerUpperSquaredCauchyJet (A j) (w j)) := by
  rw [routePDeningerFourLegHodgeGram, Matrix.gram_apply,
    routePDeningerUpperFourLegHodgeMate_eq_lineConj,
    routePDeningerUpperFourLegHodgeMate_eq_lineConj]
  exact xiWeilLineConjLinearIsometry.inner_map_map _ _

/-- Primitive quarter-turn quartet: functional-equation reflection changes the Burnol ordinate
sign, whereas complex conjugation preserves it. -/
theorem neg_routePPrimitiveDeningerUpperPoint_coe
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    -(routePPrimitiveDeningerUpperPoint pe kappa : ℂ) =
      (routePPrimitiveDeningerLowerPoint pe (-kappa) : ℂ) := by
  rw [routePPrimitiveDeningerUpperPoint_coe]
  simp [routePPrimitiveDeningerLowerPoint,
    routePPrimitiveBurnolCenteredMode]

theorem conj_routePPrimitiveDeningerUpperPoint_coe
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    (starRingEnd ℂ) (routePPrimitiveDeningerUpperPoint pe kappa : ℂ) =
      (routePPrimitiveDeningerLowerPoint pe kappa : ℂ) := by
  simp [routePPrimitiveDeningerUpperPoint,
    deningerPrimeGammaPointConjEquiv]

end

end RHTower
