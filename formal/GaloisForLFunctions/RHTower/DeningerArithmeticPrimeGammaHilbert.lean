import GaloisForLFunctions.RHTower.DeningerArithmeticJetHilbertRigging
import GaloisForLFunctions.RHTower.DeningerPrimeGammaReflectedDiagonal
import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert

/-!
# Prime--Gamma packets in Deninger jet Hilbert cohomology

Finite prime--Gamma Cauchy packets are not compact-support classes for the product topology:
their divisor evaluations have infinitely many nonzero coordinates.  Their correct target is the
canonical square-summable middle carrier.

This file constructs the lower linear and upper conjugate-linear packet realizations in
`DeningerArithmeticJetHilbert`.  The source prime--Gamma cup product becomes exactly the Hilbert
pairing after the unconditional critical-line-reflection isometry.

Cauchy evaluation is constant across all multiplicity copies over one Xi support point.  Thus the
packet image lies in the semisimple, fiber-constant subspace.  If a multiple Xi zero exists, this
subspace is proper and the packet map cannot be surjective.  This records precisely why the
distributional Lefschetz trace sees algebraic multiplicity but cannot by itself reconstruct the
positive-depth local Jordan jets.

No RH, positivity, simplicity, or zero-location hypothesis is used.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

/-- Lower source packets as square-summable multiplicity-exact Xi evaluations. -/
def deningerPrimeGammaLowerToJetHilbert :
    DeningerPrimeGammaLowerPacket →ₗ[ℂ]
      DeningerArithmeticJetHilbert :=
  Finsupp.lsum ℂ fun z =>
    LinearMap.toSpanSingleton ℂ DeningerArithmeticJetHilbert
      (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
        (XiWeilSquareSummable_cauchy z))

@[simp]
theorem deningerPrimeGammaLowerToJetHilbert_apply
    (x : DeningerPrimeGammaLowerPacket)
    (q : DeningerArithmeticJetCoordinate) :
    deningerPrimeGammaLowerToJetHilbert x q =
      deningerPrimeGammaLowerCauchyTest x
        (xiSpectralPoint q) := by
  classical
  change
    (x.sum fun z c =>
      c • xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
        (XiWeilSquareSummable_cauchy z)) q =
      x.sum fun z c =>
        c * xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q)
  simp only [Finsupp.sum, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, xiWeilEvaluationLp_apply,
    smul_eq_mul]

/-- Linear upper sharp packets before applying the anti-linear Weil involution. -/
def deningerPrimeGammaUpperSharpToJetHilbert :
    DeningerPrimeGammaUpperPacket →ₗ[ℂ]
      DeningerArithmeticJetHilbert :=
  Finsupp.lsum ℂ fun w =>
    LinearMap.toSpanSingleton ℂ DeningerArithmeticJetHilbert
      (xiWeilEvaluationLp
        (xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ)))
        (XiWeilSquareSummable_cauchy
          ((starRingEnd ℂ) (w : ℂ))))

@[simp]
theorem deningerPrimeGammaUpperSharpToJetHilbert_apply
    (y : DeningerPrimeGammaUpperPacket)
    (q : DeningerArithmeticJetCoordinate) :
    deningerPrimeGammaUpperSharpToJetHilbert y q =
      deningerPrimeGammaUpperSharpCauchyTest y
        (xiSpectralPoint q) := by
  classical
  change
    (y.sum fun w d =>
      d • xiWeilEvaluationLp
        (xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ)))
        (XiWeilSquareSummable_cauchy
          ((starRingEnd ℂ) (w : ℂ)))) q =
      y.sum fun w d =>
        d * xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ))
          (xiSpectralPoint q)
  simp only [Finsupp.sum, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, xiWeilEvaluationLp_apply,
    smul_eq_mul]

/--
Upper source packets in the Hilbert carrier.

The map is conjugate-linear because the upper Cauchy test itself is the anti-linear Weil sharp of
the linearly represented sharp packet.
-/
def deningerPrimeGammaUpperToJetHilbert :
    DeningerPrimeGammaUpperPacket →ₛₗ[starRingEnd ℂ]
      DeningerArithmeticJetHilbert where
  toFun y :=
    star
      (xiWeilLineConjLp
        (deningerPrimeGammaUpperSharpToJetHilbert y))
  map_add' y z := by
    ext q
    change
      star ((deningerPrimeGammaUpperSharpToJetHilbert (y + z))
        (xiZeroCopyLineConjEquiv q)) =
      star ((deningerPrimeGammaUpperSharpToJetHilbert y)
        (xiZeroCopyLineConjEquiv q)) +
      star ((deningerPrimeGammaUpperSharpToJetHilbert z)
        (xiZeroCopyLineConjEquiv q))
    rw [map_add]
    exact map_add (starRingEnd ℂ) _ _
  map_smul' c y := by
    ext q
    change
      star ((deningerPrimeGammaUpperSharpToJetHilbert (c • y))
        (xiZeroCopyLineConjEquiv q)) =
      (starRingEnd ℂ) c *
        star ((deningerPrimeGammaUpperSharpToJetHilbert y)
          (xiZeroCopyLineConjEquiv q))
    rw [map_smul]
    exact map_mul (starRingEnd ℂ) c _

@[simp]
theorem deningerPrimeGammaUpperToJetHilbert_apply
    (y : DeningerPrimeGammaUpperPacket)
    (q : DeningerArithmeticJetCoordinate) :
    deningerPrimeGammaUpperToJetHilbert y q =
      deningerPrimeGammaUpperCauchyTest y
        (xiSpectralPoint q) := by
  change
    star ((deningerPrimeGammaUpperSharpToJetHilbert y)
        (xiZeroCopyLineConjEquiv q)) =
      star (deningerPrimeGammaUpperSharpCauchyTest y
        (star (xiSpectralPoint q)))
  rw [deningerPrimeGammaUpperSharpToJetHilbert_apply,
    xiSpectralPoint_lineConj]
  rfl

/-- Every finite lower prime--Gamma packet is square-summable on the exact Xi divisor. -/
theorem deningerPrimeGammaLowerCauchyTest_squareSummable
    (x : DeningerPrimeGammaLowerPacket) :
    XiWeilSquareSummable
      (deningerPrimeGammaLowerCauchyTest x) := by
  have hs :=
    HilbertSchmidt.summable_coe_sq
      (deningerPrimeGammaLowerToJetHilbert x)
  unfold XiWeilSquareSummable
  exact hs.congr fun q => by
    rw [deningerPrimeGammaLowerToJetHilbert_apply]

/-- Every finite upper prime--Gamma packet is square-summable on the exact Xi divisor. -/
theorem deningerPrimeGammaUpperCauchyTest_squareSummable
    (y : DeningerPrimeGammaUpperPacket) :
    XiWeilSquareSummable
      (deningerPrimeGammaUpperCauchyTest y) := by
  have hs :=
    HilbertSchmidt.summable_coe_sq
      (deningerPrimeGammaUpperToJetHilbert y)
  unfold XiWeilSquareSummable
  exact hs.congr fun q => by
    rw [deningerPrimeGammaUpperToJetHilbert_apply]

/-- The abstract lower packet realization is its literal `ell^(2 : ℕ)` evaluation vector. -/
theorem xiWeilEvaluationLp_deningerPrimeGammaLowerCauchyTest
    (x : DeningerPrimeGammaLowerPacket) :
    xiWeilEvaluationLp
        (deningerPrimeGammaLowerCauchyTest x)
        (deningerPrimeGammaLowerCauchyTest_squareSummable x) =
      deningerPrimeGammaLowerToJetHilbert x := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply,
    deningerPrimeGammaLowerToJetHilbert_apply]

/-- The abstract upper packet realization is its literal `ell^(2 : ℕ)` evaluation vector. -/
theorem xiWeilEvaluationLp_deningerPrimeGammaUpperCauchyTest
    (y : DeningerPrimeGammaUpperPacket) :
    xiWeilEvaluationLp
        (deningerPrimeGammaUpperCauchyTest y)
        (deningerPrimeGammaUpperCauchyTest_squareSummable y) =
      deningerPrimeGammaUpperToJetHilbert y := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply,
    deningerPrimeGammaUpperToJetHilbert_apply]

/--
Exact source/Hilbert comparison: the prime--Gamma cup is the canonical Hilbert pairing after
critical-line reflection.
-/
theorem deningerPrimeGammaSourceCup_eq_jetHilbert_inner
    (x : DeningerPrimeGammaLowerPacket)
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaSourceCup x y =
      inner ℂ
        (xiWeilLineConjLp
          (deningerPrimeGammaUpperToJetHilbert y))
        (deningerPrimeGammaLowerToJetHilbert x) := by
  rw [deningerPrimeGammaSourceCup_eq_xiWeilPolarization]
  rw [← inner_xiWeilLineConjLp_evaluation_eq_polarization
    (deningerPrimeGammaLowerCauchyTest x)
    (deningerPrimeGammaUpperCauchyTest y)
    (deningerPrimeGammaLowerCauchyTest_squareSummable x)
    (deningerPrimeGammaUpperCauchyTest_squareSummable y)]
  rw [xiWeilEvaluationLp_deningerPrimeGammaLowerCauchyTest,
    xiWeilEvaluationLp_deningerPrimeGammaUpperCauchyTest]

/-- Square-summable jets constant across every analytic-multiplicity fiber. -/
def deningerArithmeticSemisimpleJetHilbert :
    Submodule ℂ DeningerArithmeticJetHilbert where
  carrier := {v | ∀ rho k l, v ⟨rho, k⟩ = v ⟨rho, l⟩}
  zero_mem' := by
    intro rho k l
    rfl
  add_mem' := by
    intro v w hv hw rho k l
    change v ⟨rho, k⟩ + w ⟨rho, k⟩ =
      v ⟨rho, l⟩ + w ⟨rho, l⟩
    rw [hv rho k l, hw rho k l]
  smul_mem' := by
    intro c v hv rho k l
    change c * v ⟨rho, k⟩ = c * v ⟨rho, l⟩
    rw [hv rho k l]

/-- Lower Cauchy packets only see the semisimple multiplicity trace coordinate. -/
theorem deningerPrimeGammaLowerToJetHilbert_mem_semisimple
    (x : DeningerPrimeGammaLowerPacket) :
    deningerPrimeGammaLowerToJetHilbert x ∈
      deningerArithmeticSemisimpleJetHilbert := by
  intro rho k l
  rw [deningerPrimeGammaLowerToJetHilbert_apply,
    deningerPrimeGammaLowerToJetHilbert_apply,
    xiSpectralPoint_eq_support, xiSpectralPoint_eq_support]

/-- Upper Cauchy packets only see the semisimple multiplicity trace coordinate. -/
theorem deningerPrimeGammaUpperToJetHilbert_mem_semisimple
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaUpperToJetHilbert y ∈
      deningerArithmeticSemisimpleJetHilbert := by
  intro rho k l
  rw [deningerPrimeGammaUpperToJetHilbert_apply,
    deningerPrimeGammaUpperToJetHilbert_apply,
    xiSpectralPoint_eq_support, xiSpectralPoint_eq_support]

/-- A multiplicity-two local jet makes the fiber-constant Hilbert subspace proper. -/
theorem deningerArithmeticSemisimpleJetHilbert_ne_top
    {rho : XiDivisorSupport}
    (hm : 2 ≤ xiSupportMultiplicity rho) :
    deningerArithmeticSemisimpleJetHilbert ≠ ⊤ := by
  let k0 : DeningerArithmeticJetIndex rho :=
    ⟨0, lt_of_lt_of_le (by omega) hm⟩
  let k1 : DeningerArithmeticJetIndex rho :=
    ⟨1, lt_of_lt_of_le (by omega) hm⟩
  let v : DeningerArithmeticJetHilbert :=
    lp.single 2
      (⟨rho, k0⟩ : DeningerArithmeticJetCoordinate) 1
  intro htop
  have hv : v ∈ deningerArithmeticSemisimpleJetHilbert := by
    rw [htop]
    exact Submodule.mem_top
  have hcoord := hv rho k0 k1
  have hk : (⟨rho, k1⟩ : DeningerArithmeticJetCoordinate) ≠
      ⟨rho, k0⟩ := by
    intro h
    have hfin : k1 = k0 :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hval := congrArg Fin.val hfin
    simp [k0, k1] at hval
  rw [show v ⟨rho, k0⟩ = 1 by
      simp [v],
    show v ⟨rho, k1⟩ = 0 by
      simp [v, hk]] at hcoord
  exact one_ne_zero hcoord

/--
If a multiple Xi zero exists, finite prime--Gamma Cauchy packets cannot exhaust the full jet
Hilbert cohomology.
-/
theorem deningerPrimeGammaLowerToJetHilbert_not_surjective
    {rho : XiDivisorSupport}
    (hm : 2 ≤ xiSupportMultiplicity rho) :
    ¬ Function.Surjective deningerPrimeGammaLowerToJetHilbert := by
  intro hsurj
  have htop : deningerArithmeticSemisimpleJetHilbert = ⊤ := by
    apply top_unique
    intro v hv
    obtain ⟨x, rfl⟩ := hsurj v
    exact deningerPrimeGammaLowerToJetHilbert_mem_semisimple x
  exact deningerArithmeticSemisimpleJetHilbert_ne_top hm htop

end

end RHTower
