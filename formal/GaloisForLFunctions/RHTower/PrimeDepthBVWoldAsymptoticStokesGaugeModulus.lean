import GaloisForLFunctions.RHTower.PrimeDepthBVWoldPositiveStokesPolarization

/-!
# Asymptotic Stokes gauge modulus of the resolved BV--Wold source

The positive resolved BV--Wold polarization is flat for every centered
rate.  One possible source-rigidity principle would try to distinguish the
fixed Cartier metric by requiring its frame at infinite Wold depth.

This module proves that principle false.  Relative to the fixed source
frame, every resolved frame is an exact unipotent gauge with parameter

`a * primeDepthBVWoldNormalizedPotential i`.

For every fixed prime this potential tends to zero geometrically with
depth.  Thus every real value of `a` gives a flat, cycle-trivial gauge which
approaches the identity frame at infinity.  At every finite source cell the
same family is injective in `a`.  The missing Route-R rigidity must
therefore pin a finite source grading or source point; asymptotic Stokes
normalization cannot supply it.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Exact unipotent normal form -/

/-- Physical gauge comparing the resolved frame at rate `a` with the fixed
source frame at rate zero. -/
def primeDepthBVWoldSourceRelativeGauge
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (primeDepthBVWoldResolvedSourceFrame a i).comp
    (primeDepthBVWoldResolvedSourceFrameInv 0 i)

/-- The relative frame is exactly the unipotent shear whose coefficient is
the source-normalized BV--Wold vertex potential. -/
theorem primeDepthBVWoldSourceRelativeGauge_apply
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldSourceRelativeGauge a i z =
      (z.1 + ((a * primeDepthBVWoldNormalizedPotential i : ℝ) : ℂ) * z.2,
        z.2) := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  rw [primeDepthBVWoldSourceRelativeGauge]
  ext <;> simp only [LinearMap.comp_apply,
    primeDepthBVWoldResolvedSourceFrame,
    primeDepthBVWoldResolvedSourceFrameInv, LinearMap.coe_mk,
    AddHom.coe_mk]
  · push_cast
    rw [primeDepthBVWoldNormalizedPotential]
    push_cast
    field_simp [hi]
    ring
  · push_cast
    field_simp [hi]

/-- Resolved transport expressed in the orthonormal physical coordinates
of the fixed source frames at its endpoints. -/
def primeDepthBVWoldSourceNormalizedTransport
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (primeDepthBVWoldResolvedSourceFrame 0 i).comp
    ((primeDepthBVWoldResolvedTransport a i j).comp
      (primeDepthBVWoldResolvedSourceFrameInv 0 j))

/-- The normalized transition is the difference of the endpoint
unipotent potentials. -/
theorem primeDepthBVWoldSourceNormalizedTransport_apply
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldSourceNormalizedTransport a i j z =
      (z.1 - ((a * primeDepthBVWoldNormalizedConnection i j : ℝ) : ℂ) * z.2,
        z.2) := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  have hj := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero j
  rw [primeDepthBVWoldSourceNormalizedTransport]
  ext <;> simp only [LinearMap.comp_apply,
    primeDepthBVWoldResolvedSourceFrame,
    primeDepthBVWoldResolvedSourceFrameInv,
    primeDepthBVWoldResolvedTransport, LinearMap.coe_mk,
    AddHom.coe_mk]
  · push_cast
    rw [primeDepthBVWoldNormalizedConnection]
    push_cast
    field_simp [hi, hj]
    ring
  · push_cast
    field_simp [hi, hj]

/-- The normalized transition is literally the exact gauge difference
`L_i⁻¹ L_j`. -/
theorem primeDepthBVWoldSourceNormalizedTransport_eq_relativeGauge
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldSourceNormalizedTransport a i j z =
      primeDepthBVWoldSourceRelativeGauge (-a) i
        (primeDepthBVWoldSourceRelativeGauge a j z) := by
  rw [primeDepthBVWoldSourceNormalizedTransport_apply,
    primeDepthBVWoldSourceRelativeGauge_apply,
    primeDepthBVWoldSourceRelativeGauge_apply,
    primeDepthBVWoldNormalizedConnection_eq_potential_sub]
  ext <;> simp
  ring

/-- All normalized Stokes cycle data are flat for every value of the
hidden real gauge modulus. -/
theorem primeDepthBVWoldSourceNormalizedTransport_comp
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldSourceNormalizedTransport a i j
        (primeDepthBVWoldSourceNormalizedTransport a j k z) =
      primeDepthBVWoldSourceNormalizedTransport a i k z := by
  rw [primeDepthBVWoldSourceNormalizedTransport_apply,
    primeDepthBVWoldSourceNormalizedTransport_apply,
    primeDepthBVWoldSourceNormalizedTransport_apply,
    primeDepthBVWoldNormalizedConnection_eq_potential_sub,
    primeDepthBVWoldNormalizedConnection_eq_potential_sub,
    primeDepthBVWoldNormalizedConnection_eq_potential_sub]
  ext <;> simp
  ring

/-! ## The finite source modulus is faithful -/

/-- The normalized BV--Wold potential is strictly positive at every finite
prime/depth cell. -/
theorem primeDepthBVWoldNormalizedPotential_pos
    (i : PrimeDepthBVWoldCell) :
    0 < primeDepthBVWoldNormalizedPotential i := by
  rcases i with ⟨p, e⟩
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hmass :
      0 < (1 - ((p.1 : ℝ)⁻¹)) * ((p.1 : ℝ)⁻¹) ^ e := by
    exact mul_pos (sub_pos.mpr ((inv_lt_one₀ hp0).mpr hp1))
      (pow_pos (inv_pos.mpr hp0) e)
  rw [primeDepthBVWoldNormalizedPotential,
    primeDepthBVFirstTraceDepthWeight_eq]
  exact div_pos hmass
    (xiGammaEulerPrimitivePrimeDepthLogClock_pos (p, e))

/-- Evaluation at any finite source cell detects the entire real gauge
modulus. -/
theorem primeDepthBVWoldSourceRelativeGauge_injective
    (i : PrimeDepthBVWoldCell) :
    Function.Injective
      (fun a : ℝ => primeDepthBVWoldSourceRelativeGauge a i) := by
  intro a b hab
  have hz := LinearMap.congr_fun hab (0, 1)
  rw [primeDepthBVWoldSourceRelativeGauge_apply,
    primeDepthBVWoldSourceRelativeGauge_apply] at hz
  have hfirst := congrArg (fun z : ℂ × ℂ => z.1.re) hz
  norm_num at hfirst
  have hq := primeDepthBVWoldNormalizedPotential_pos i
  exact hfirst.resolve_right hq.ne'

theorem primeDepthBVWoldSourceRelativeGauge_zero
    (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldSourceRelativeGauge 0 i = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp [primeDepthBVWoldSourceRelativeGauge_apply]

/-- A finite relative source frame is the identity exactly at zero gauge
modulus. -/
theorem primeDepthBVWoldSourceRelativeGauge_eq_id_iff
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldSourceRelativeGauge a i = LinearMap.id ↔ a = 0 := by
  constructor
  · intro h
    apply primeDepthBVWoldSourceRelativeGauge_injective i
    change primeDepthBVWoldSourceRelativeGauge a i =
      primeDepthBVWoldSourceRelativeGauge 0 i
    rw [primeDepthBVWoldSourceRelativeGauge_zero]
    exact h
  · rintro rfl
    exact primeDepthBVWoldSourceRelativeGauge_zero i

/-! ## Associated-grade blindness and the source-pointed splitting -/

/-- Inclusion of the literal horizontal mass summand in the resolved
two-component source. -/
def primeDepthBVWoldHorizontalInclusion : ℂ →ₗ[ℂ] (ℂ × ℂ) where
  toFun c := (c, 0)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Projection to the literal vertical clock quotient. -/
def primeDepthBVWoldVerticalQuotient : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun z := z.2
  map_add' x y := by simp
  map_smul' r x := by simp

/-- Distinguished source section of the vertical clock quotient.  Unlike
the associated graded, this splitting detects the hidden shear modulus. -/
def primeDepthBVWoldFixedVerticalSplitting : ℂ →ₗ[ℂ] (ℂ × ℂ) where
  toFun c := (0, c)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- The distinguished vertical section is a right inverse to the clock
quotient. -/
theorem primeDepthBVWoldFixedVerticalSplitting_rightInverse :
    primeDepthBVWoldVerticalQuotient.comp
        primeDepthBVWoldFixedVerticalSplitting = LinearMap.id := by
  apply LinearMap.ext
  intro c
  rfl

/-- Every relative gauge fixes the horizontal source subobject, regardless
of its centered rate. -/
theorem primeDepthBVWoldSourceRelativeGauge_horizontal
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    (primeDepthBVWoldSourceRelativeGauge a i).comp
        primeDepthBVWoldHorizontalInclusion =
      primeDepthBVWoldHorizontalInclusion := by
  apply LinearMap.ext
  intro c
  simp [primeDepthBVWoldHorizontalInclusion,
    primeDepthBVWoldSourceRelativeGauge_apply]

/-- Every relative gauge induces the identity on the vertical quotient.
Thus its action on the associated graded is invisible for every rate. -/
theorem primeDepthBVWoldSourceRelativeGauge_verticalQuotient
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldVerticalQuotient.comp
        (primeDepthBVWoldSourceRelativeGauge a i) =
      primeDepthBVWoldVerticalQuotient := by
  apply LinearMap.ext
  intro z
  simp [primeDepthBVWoldVerticalQuotient,
    primeDepthBVWoldSourceRelativeGauge_apply]

/-- Exact affine displacement of the distinguished source splitting.  Its
coefficient is the hidden Route-R torsor coordinate `a * m_i / λ_i`. -/
theorem primeDepthBVWoldSourceRelativeGauge_fixedVerticalSplitting
    (a : ℝ) (i : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldSourceRelativeGauge a i
        (primeDepthBVWoldFixedVerticalSplitting c) =
      primeDepthBVWoldFixedVerticalSplitting c +
        primeDepthBVWoldHorizontalInclusion
          (((a * primeDepthBVWoldNormalizedPotential i : ℝ) : ℂ) * c) := by
  simp [primeDepthBVWoldFixedVerticalSplitting,
    primeDepthBVWoldHorizontalInclusion,
    primeDepthBVWoldSourceRelativeGauge_apply]

/-- Preservation of the distinguished source-pointed splitting at one
finite cell is equivalent to zero centered rate. -/
theorem
    primeDepthBVWoldSourceRelativeGauge_preserves_fixedVerticalSplitting_iff
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    (primeDepthBVWoldSourceRelativeGauge a i).comp
        primeDepthBVWoldFixedVerticalSplitting =
      primeDepthBVWoldFixedVerticalSplitting ↔ a = 0 := by
  constructor
  · intro h
    have hz := LinearMap.congr_fun h 1
    rw [LinearMap.comp_apply,
      primeDepthBVWoldSourceRelativeGauge_apply] at hz
    have hfirst := congrArg (fun z : ℂ × ℂ => z.1.re) hz
    norm_num [primeDepthBVWoldFixedVerticalSplitting] at hfirst
    exact hfirst.resolve_right
      (primeDepthBVWoldNormalizedPotential_pos i).ne'
  · rintro rfl
    rw [primeDepthBVWoldSourceRelativeGauge_zero]
    rfl

/-- **Associated-grade blindness no-go.**  At every finite source cell
there is a nontrivial gauge acting identically on both the horizontal
subobject and vertical quotient while moving the distinguished splitting.
Hence finite associated-grade preservation cannot select criticality. -/
theorem primeDepthBVWoldAssociatedGradedBlindness_strictNoGo
    (i : PrimeDepthBVWoldCell) :
    ∃ a : ℝ, a ≠ 0 ∧
      (primeDepthBVWoldSourceRelativeGauge a i).comp
          primeDepthBVWoldHorizontalInclusion =
        primeDepthBVWoldHorizontalInclusion ∧
      primeDepthBVWoldVerticalQuotient.comp
          (primeDepthBVWoldSourceRelativeGauge a i) =
        primeDepthBVWoldVerticalQuotient ∧
      (primeDepthBVWoldSourceRelativeGauge a i).comp
          primeDepthBVWoldFixedVerticalSplitting ≠
        primeDepthBVWoldFixedVerticalSplitting := by
  refine ⟨1, one_ne_zero,
    primeDepthBVWoldSourceRelativeGauge_horizontal 1 i,
    primeDepthBVWoldSourceRelativeGauge_verticalQuotient 1 i, ?_⟩
  intro h
  exact one_ne_zero
    ((primeDepthBVWoldSourceRelativeGauge_preserves_fixedVerticalSplitting_iff
      1 i).mp h)

/-! ## Infinite-depth asymptotics -/

/-- At every fixed ordinary prime, the normalized BV mass/clock potential
tends to zero.  Its geometric numerator dominates the growing clock
denominator. -/
theorem primeDepthBVWoldNormalizedPotential_tendsto_zero
    (p : Nat.Primes) :
    Tendsto
      (fun e : ℕ => primeDepthBVWoldNormalizedPotential (p, e))
      atTop (nhds 0) := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  have hr0 : 0 ≤ ((p.1 : ℝ)⁻¹) := inv_nonneg.mpr hp0.le
  have hr1 : ((p.1 : ℝ)⁻¹) < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hpow : Tendsto (fun e : ℕ => ((p.1 : ℝ)⁻¹) ^ e)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  let C : ℝ := (1 - (p.1 : ℝ)⁻¹) / Real.log (p.1 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hform (e : ℕ) :
      primeDepthBVWoldNormalizedPotential (p, e) =
        C * ((p.1 : ℝ)⁻¹) ^ e / (e + 1 : ℝ) := by
    rw [primeDepthBVWoldNormalizedPotential,
      primeDepthBVFirstTraceDepthWeight_eq,
      xiGammaEulerPrimitivePrimeDepthLogClock_apply]
    dsimp [C]
    field_simp [hlog.ne']
    norm_num
  have hmajor : Tendsto
      (fun e : ℕ => C * ((p.1 : ℝ)⁻¹) ^ e) atTop (nhds 0) := by
    simpa using hpow.const_mul C
  apply squeeze_zero
      (g := fun e : ℕ => C * ((p.1 : ℝ)⁻¹) ^ e)
  · intro e
    rw [hform]
    positivity
  · intro e
    rw [hform]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (e + 1 : ℝ))]
    have hnum : 0 ≤ C * ((p.1 : ℝ)⁻¹) ^ e :=
      mul_nonneg hC (pow_nonneg hr0 e)
    have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
    nlinarith
  · exact hmajor

/-- Every member of the real gauge family approaches the same fixed source
frame pointwise at infinite Wold depth. -/
theorem primeDepthBVWoldSourceRelativeGauge_tendsto_id
    (a : ℝ) (p : Nat.Primes) (z : ℂ × ℂ) :
    Tendsto
      (fun e : ℕ => primeDepthBVWoldSourceRelativeGauge a (p, e) z)
      atTop (nhds z) := by
  have hpot := primeDepthBVWoldNormalizedPotential_tendsto_zero p
  have hreal : Tendsto
      (fun e : ℕ => a * primeDepthBVWoldNormalizedPotential (p, e))
      atTop (nhds 0) := by
    simpa using hpot.const_mul a
  have hcomplex : Tendsto
      (fun e : ℕ =>
        ((a * primeDepthBVWoldNormalizedPotential (p, e) : ℝ) : ℂ))
      atTop (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hreal
  have hfst : Tendsto
      (fun e : ℕ => z.1 +
        ((a * primeDepthBVWoldNormalizedPotential (p, e) : ℝ) : ℂ) * z.2)
      atTop (nhds z.1) := by
    simpa using tendsto_const_nhds.add (hcomplex.mul_const z.2)
  rw [show
      (fun e : ℕ => primeDepthBVWoldSourceRelativeGauge a (p, e) z) =
        fun e : ℕ =>
          (z.1 +
              ((a * primeDepthBVWoldNormalizedPotential (p, e) : ℝ) : ℂ) * z.2,
            z.2) by
      funext e
      exact primeDepthBVWoldSourceRelativeGauge_apply a (p, e) z]
  exact hfst.prodMk_nhds tendsto_const_nhds

/-- Even successive normalized transitions approach the identity for every
gauge modulus, so edge asymptotics do not recover it either. -/
theorem primeDepthBVWoldSourceNormalizedTransport_successor_tendsto_id
    (a : ℝ) (p : Nat.Primes) (z : ℂ × ℂ) :
    Tendsto
      (fun e : ℕ =>
        primeDepthBVWoldSourceNormalizedTransport a (p, e) (p, e + 1) z)
      atTop (nhds z) := by
  have hpot := primeDepthBVWoldNormalizedPotential_tendsto_zero p
  have hpotsucc : Tendsto
      (fun e : ℕ => primeDepthBVWoldNormalizedPotential (p, e + 1))
      atTop (nhds 0) := hpot.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto
      (fun e : ℕ => primeDepthBVWoldNormalizedPotential (p, e) -
        primeDepthBVWoldNormalizedPotential (p, e + 1))
      atTop (nhds 0) := by
    simpa using hpot.sub hpotsucc
  have hreal : Tendsto
      (fun e : ℕ => a *
        (primeDepthBVWoldNormalizedPotential (p, e) -
          primeDepthBVWoldNormalizedPotential (p, e + 1)))
      atTop (nhds 0) := by
    simpa using hdiff.const_mul a
  have hcomplex : Tendsto
      (fun e : ℕ => ((a *
        (primeDepthBVWoldNormalizedPotential (p, e) -
          primeDepthBVWoldNormalizedPotential (p, e + 1)) : ℝ) : ℂ))
      atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp hreal
  have hfst : Tendsto
      (fun e : ℕ => z.1 -
        ((a *
          (primeDepthBVWoldNormalizedPotential (p, e) -
            primeDepthBVWoldNormalizedPotential (p, e + 1)) : ℝ) : ℂ) * z.2)
      atTop (nhds z.1) := by
    simpa using tendsto_const_nhds.sub (hcomplex.mul_const z.2)
  rw [show
      (fun e : ℕ =>
        primeDepthBVWoldSourceNormalizedTransport a (p, e) (p, e + 1) z) =
        fun e : ℕ =>
          (z.1 - ((a *
              (primeDepthBVWoldNormalizedPotential (p, e) -
                primeDepthBVWoldNormalizedPotential (p, e + 1)) : ℝ) : ℂ) * z.2,
            z.2) by
      funext e
      rw [primeDepthBVWoldSourceNormalizedTransport_apply,
        primeDepthBVWoldNormalizedConnection_eq_potential_sub]]
  exact hfst.prodMk_nhds tendsto_const_nhds

/-! ## Sharp no-go -/

/-- **Asymptotic Stokes-normalization no-go.**  There exists a nonzero
gauge modulus whose normalized connection is flat on every source triangle,
whose frames approach the fixed source frame at every fixed prime, and whose
finite frames are nevertheless never the fixed frame. -/
theorem primeDepthBVWoldAsymptoticStokesNormalization_strictNoGo
    (p : Nat.Primes) :
    ∃ a : ℝ, a ≠ 0 ∧
      (∀ i j k : PrimeDepthBVWoldCell, ∀ z : ℂ × ℂ,
        primeDepthBVWoldSourceNormalizedTransport a i j
            (primeDepthBVWoldSourceNormalizedTransport a j k z) =
          primeDepthBVWoldSourceNormalizedTransport a i k z) ∧
      (∀ z : ℂ × ℂ,
        Tendsto
          (fun e : ℕ => primeDepthBVWoldSourceRelativeGauge a (p, e) z)
          atTop (nhds z)) ∧
      (∀ i : PrimeDepthBVWoldCell,
        primeDepthBVWoldSourceRelativeGauge a i ≠ LinearMap.id) := by
  refine ⟨1, one_ne_zero, ?_, ?_, ?_⟩
  · intro i j k z
    exact primeDepthBVWoldSourceNormalizedTransport_comp 1 i j k z
  · exact primeDepthBVWoldSourceRelativeGauge_tendsto_id 1 p
  · intro i h
    exact one_ne_zero
      ((primeDepthBVWoldSourceRelativeGauge_eq_id_iff 1 i).mp h)

end

end RHTower
