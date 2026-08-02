import GaloisForLFunctions.RHTower.DeningerMeyerSecondaryThreeTermComplex

/-!
# Radial parity obstruction and correction

The maximal secondary Bessel domain is too large to serve directly as a
source-derived arithmetic middle term: it contains arbitrary negative-radius
functions, while the literal Meyer--Poisson boundary is even.  Every function
supported on negative radii therefore produces a cycle, and this entire vector
space injects linearly into the resulting `H¹`.

This file proves that no-go and then applies the forced repair.  The corrected
middle term is the intersection of the maximal Bessel domain with evenness on
both radial collars.  Literal Meyer boundaries land in this intersection, the
secondary differential still annihilates them, and its cycles retain the exact
primewise reflected-relation classification.  The spurious negative-radius
sector meets the corrected domain only at zero.

This parity correction does not assert a global arithmetic sheaf
identification or identify the corrected `H¹` spectrum with the Xi divisor.
-/

namespace RHTower

open scoped FourierTransform SchwartzMap

noncomputable section

/-- Meyer's positive summation is even whenever its source function is even. -/
theorem deningerMeyerSum_neg_of_even
    (f : ℝ → ℂ) (heven : ∀ x, f (-x) = f x) (x : ℝ) :
    deningerMeyerSum f (-x) = deningerMeyerSum f x := by
  rw [deningerMeyerSum, deningerMeyerSum]
  apply tsum_congr
  intro n
  rw [show ((n : ℝ) + 1) * (-x) =
      -(((n : ℝ) + 1) * x) by ring]
  exact heven _

/-- The physical collar of every literal Meyer--Poisson boundary is even. -/
theorem deningerMeyerPoissonBoundary_first_even
    (f : DeningerMeyerCap) (x : ℝ) :
    (deningerMeyerPoissonBoundaryPair f).1 (-x) =
      (deningerMeyerPoissonBoundaryPair f).1 x := by
  exact deningerMeyerSum_neg_of_even f
    ((deningerMeyerCap_mem_iff f).mp f.property).1 x

/--
Functions supported on negative radii.  These are invisible to every positive
prime evaluation in the uncorrected secondary regulator.
-/
def DeningerMeyerNegativeRadialFunctions :
    Submodule ℂ (ℝ → ℂ) where
  carrier := {k | ∀ x, 0 ≤ x → k x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]

/-- Insert a negative-radius function in the physical collar. -/
def deningerMeyerNegativeRadialPairLM :
    DeningerMeyerNegativeRadialFunctions →ₗ[ℂ]
      DeningerMeyerRadialCochainPair :=
  (LinearMap.inl ℂ (ℝ → ℂ) (ℝ → ℂ)).comp
    DeningerMeyerNegativeRadialFunctions.subtype

@[simp]
theorem deningerMeyerNegativeRadialPairLM_apply
    (k : DeningerMeyerNegativeRadialFunctions) :
    deningerMeyerNegativeRadialPairLM k =
      ((k : ℝ → ℂ), 0) :=
  rfl

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/-- Negative-radius functions lie in the maximal Bessel domain with zero regulator. -/
def deningerMeyerNegativeRadialBesselLM :
    DeningerMeyerNegativeRadialFunctions →ₗ[ℂ]
      DeningerMeyerSecondaryBesselDomain packet where
  toFun k := ⟨deningerMeyerNegativeRadialPairLM k, by
    change Memℓp
      (fun p =>
        deningerMeyerSecondaryFirstModeValue packet p
          (deningerMeyerNegativeRadialPairLM k)) 2
    have hzero :
        (fun p =>
          deningerMeyerSecondaryFirstModeValue packet p
            (deningerMeyerNegativeRadialPairLM k)) =
          fun p : Nat.Primes =>
            (0 : DeningerPrimeSuspensionHaarL2 p) := by
      funext p
      apply
        (deningerMeyerSecondaryFirstModeValue_eq_zero_iff
          packet p (deningerMeyerNegativeRadialPairLM k)).2
      apply Or.inl
      have hp : 0 ≤ (p : ℝ) := by positivity
      rw [deningerMeyerNegativeRadialPairLM_apply]
      change (k : ℝ → ℂ) (p : ℝ) =
          (((p : ℝ)⁻¹ : ℝ) : ℂ) * 0
      rw [k.property (p : ℝ) hp]
      simp
    rw [hzero]
    exact zero_mem_ℓp'⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add deningerMeyerNegativeRadialPairLM f g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul deningerMeyerNegativeRadialPairLM c f

@[simp]
theorem deningerMeyerNegativeRadialBesselLM_coe
    (k : DeningerMeyerNegativeRadialFunctions) :
    (deningerMeyerNegativeRadialBesselLM packet k :
      DeningerMeyerRadialCochainPair) =
      ((k : ℝ → ℂ), 0) :=
  rfl

/-- Every negative-radius function is a cycle in the uncorrected complex. -/
def deningerMeyerNegativeRadialCyclesLM :
    DeningerMeyerNegativeRadialFunctions →ₗ[ℂ]
      (deningerMeyerSecondaryThreeTermComplex packet).cycles1 :=
  (deningerMeyerNegativeRadialBesselLM packet).codRestrict
    (deningerMeyerSecondaryThreeTermComplex packet).cycles1
    (fun k => by
      rw [deningerMeyerSecondaryThreeTerm_cycles1_iff]
      intro p
      left
      have hp : 0 ≤ (p : ℝ) := by positivity
      rw [deningerMeyerNegativeRadialBesselLM_coe]
      change (k : ℝ → ℂ) (p : ℝ) =
          (((p : ℝ)⁻¹ : ℝ) : ℂ) * 0
      rw [k.property (p : ℝ) hp]
      simp)

/-- Degree-one cycles of the uncorrected secondary complex. -/
abbrev DeningerMeyerSecondaryCycles1
    (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p) :=
  (deningerMeyerSecondaryThreeTermComplex packet).cycles1

/-- Degree-one boundaries viewed inside cycles. -/
abbrev DeningerMeyerSecondaryBoundariesInCycles
    (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p) :=
  (deningerMeyerSecondaryThreeTermComplex packet).boundaries1.comap
    (deningerMeyerSecondaryThreeTermComplex packet).cycles1.subtype

/-- Middle cohomology of the uncorrected secondary complex. -/
abbrev DeningerMeyerSecondaryH1
    (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p) :=
  (deningerMeyerSecondaryThreeTermComplex packet).H1

/-- Cohomology class of one negative-radius cycle. -/
def deningerMeyerNegativeRadialH1
    (k : DeningerMeyerNegativeRadialFunctions) :
    DeningerMeyerSecondaryH1 packet :=
  Submodule.Quotient.mk
    (deningerMeyerNegativeRadialCyclesLM packet k)

/-- The negative-radius class map is linear. -/
def deningerMeyerNegativeRadialH1LM :
    DeningerMeyerNegativeRadialFunctions →ₗ[ℂ]
      DeningerMeyerSecondaryH1 packet where
  toFun := deningerMeyerNegativeRadialH1 packet
  map_add' k l := by
    change Submodule.Quotient.mk
        (deningerMeyerNegativeRadialCyclesLM packet (k + l)) =
      Submodule.Quotient.mk
          (deningerMeyerNegativeRadialCyclesLM packet k) +
        Submodule.Quotient.mk
          (deningerMeyerNegativeRadialCyclesLM packet l)
    rw [map_add, Submodule.Quotient.mk_add]
  map_smul' c k := by
    change Submodule.Quotient.mk
        (deningerMeyerNegativeRadialCyclesLM packet (c • k)) =
      c • Submodule.Quotient.mk
        (deningerMeyerNegativeRadialCyclesLM packet k)
    rw [map_smul, Submodule.Quotient.mk_smul]

@[simp]
theorem deningerMeyerNegativeRadialH1LM_apply
    (k : DeningerMeyerNegativeRadialFunctions) :
    deningerMeyerNegativeRadialH1LM packet k =
      deningerMeyerNegativeRadialH1 packet k :=
  rfl

/--
Every negative-radius function gives a distinct uncorrected cohomology class.
Thus the maximal Bessel domain contributes an entire spurious vector space to
`H¹`, not merely one accidental class.
-/
theorem deningerMeyerNegativeRadialH1_injective :
    Function.Injective
      (deningerMeyerNegativeRadialH1 packet) := by
  intro k l hkl
  apply sub_eq_zero.mp
  apply Subtype.ext
  change Submodule.Quotient.mk
      (deningerMeyerNegativeRadialCyclesLM packet k) =
    Submodule.Quotient.mk
      (deningerMeyerNegativeRadialCyclesLM packet l) at hkl
  rw [Submodule.Quotient.eq] at hkl
  have hsub :
      deningerMeyerNegativeRadialCyclesLM packet k -
          deningerMeyerNegativeRadialCyclesLM packet l =
        deningerMeyerNegativeRadialCyclesLM packet (k - l) :=
    (map_sub (deningerMeyerNegativeRadialCyclesLM packet) k l).symm
  rw [hsub] at hkl
  change
    ((deningerMeyerNegativeRadialCyclesLM packet (k - l) :
      (deningerMeyerSecondaryThreeTermComplex packet).cycles1) :
        DeningerMeyerSecondaryBesselDomain packet) ∈
      (deningerMeyerSecondaryThreeTermComplex packet).boundaries1 at hkl
  obtain ⟨f, hf⟩ := hkl
  funext x
  by_cases hx : 0 ≤ x
  · exact (k - l).property x hx
  · have hneg : 0 ≤ -x := le_of_lt (neg_pos.mpr (lt_of_not_ge hx))
    have hpos := (k - l).property (-x) hneg
    have hfx := congrArg
      (fun h : DeningerMeyerSecondaryBesselDomain packet =>
        (h : DeningerMeyerRadialCochainPair).1 x) hf
    have hfnx := congrArg
      (fun h : DeningerMeyerSecondaryBesselDomain packet =>
        (h : DeningerMeyerRadialCochainPair).1 (-x)) hf
    change deningerMeyerSum f x =
      ((↑(k - l) : ℝ → ℂ) x) at hfx
    change deningerMeyerSum f (-x) =
      ((↑(k - l) : ℝ → ℂ) (-x)) at hfnx
    change ((↑(k - l) : ℝ → ℂ) x) = 0
    calc
      ((↑(k - l) : ℝ → ℂ) x) =
          deningerMeyerSum f x := hfx.symm
      _ = deningerMeyerSum f (-x) :=
        (deningerMeyerPoissonBoundary_first_even f x).symm
      _ = ((↑(k - l) : ℝ → ℂ) (-x)) := hfnx
      _ = 0 := hpos

/-- Linear form of the negative-radius cohomology injection. -/
theorem deningerMeyerNegativeRadialH1LM_injective :
    Function.Injective
      (deningerMeyerNegativeRadialH1LM packet) := by
  intro k l hkl
  apply deningerMeyerNegativeRadialH1_injective packet
  exact hkl

/-- Explicit unit point mass at the negative radius `-1`. -/
def deningerMeyerNegativePointMass :
    DeningerMeyerNegativeRadialFunctions :=
  ⟨fun x => if x = -1 then 1 else 0, by
    intro x hx
    change (if x = -1 then 1 else 0) = 0
    rw [if_neg]
    intro h
    subst x
    norm_num at hx⟩

theorem deningerMeyerNegativePointMass_ne_zero :
    deningerMeyerNegativePointMass ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun k : DeningerMeyerNegativeRadialFunctions =>
      (k : ℝ → ℂ) (-1)) hzero
  norm_num [deningerMeyerNegativePointMass] at h

/-- Concrete nonzero `H¹` class exposing the uncorrected parity defect. -/
theorem deningerMeyerNegativePointMass_H1_ne_zero :
    deningerMeyerNegativeRadialH1LM packet
        deningerMeyerNegativePointMass ≠
      0 := by
  intro hzero
  have heq :
      deningerMeyerNegativeRadialH1LM packet
          deningerMeyerNegativePointMass =
        deningerMeyerNegativeRadialH1LM packet 0 := by
    calc
      deningerMeyerNegativeRadialH1LM packet
          deningerMeyerNegativePointMass = 0 := hzero
      _ = deningerMeyerNegativeRadialH1LM packet 0 :=
        (map_zero
          (deningerMeyerNegativeRadialH1LM packet)).symm
  exact deningerMeyerNegativePointMass_ne_zero
    (deningerMeyerNegativeRadialH1LM_injective packet heq)

/-- Source-forced evenness on both radial collars. -/
def DeningerMeyerEvenRadialCochainPairs :
    Submodule ℂ DeningerMeyerRadialCochainPair where
  carrier := {h | Function.Even h.1 ∧ Function.Even h.2}
  zero_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    constructor
    · intro x
      change f.1 (-x) + g.1 (-x) = f.1 x + g.1 x
      rw [hf1 x, hg1 x]
    · intro x
      change f.2 (-x) + g.2 (-x) = f.2 x + g.2 x
      rw [hf2 x, hg2 x]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    constructor
    · intro x
      change c * f.1 (-x) = c * f.1 x
      rw [hf1 x]
    · intro x
      change c * f.2 (-x) = c * f.2 x
      rw [hf2 x]

/-- Both collars of every literal Meyer boundary have the forced radial parity. -/
theorem deningerMeyerPoissonBoundaryPair_mem_even
    (f : DeningerMeyerCap) :
    deningerMeyerPoissonBoundaryPair f ∈
      DeningerMeyerEvenRadialCochainPairs := by
  constructor
  · exact deningerMeyerPoissonBoundary_first_even f
  · apply deningerMeyerSum_neg_of_even
    exact deningerFourier_even_of_even f
      ((deningerMeyerCap_mem_iff f).mp f.property).1

/--
Corrected maximal middle domain: square-summable secondary values together
with the radial parity forced by the Meyer source.
-/
def DeningerMeyerEvenSecondaryBesselDomain :
    Submodule ℂ DeningerMeyerRadialCochainPair :=
  DeningerMeyerSecondaryBesselDomain packet ⊓
    DeningerMeyerEvenRadialCochainPairs

/-- Forget parity while retaining the proved Bessel certificate. -/
def deningerMeyerEvenBesselToBesselLM :
    DeningerMeyerEvenSecondaryBesselDomain packet →ₗ[ℂ]
      DeningerMeyerSecondaryBesselDomain packet :=
  Submodule.inclusion inf_le_left

/-- Literal Meyer boundary with both its Bessel and parity certificates. -/
def deningerMeyerEvenPoissonBoundaryLM :
    DeningerMeyerCap →ₗ[ℂ]
      DeningerMeyerEvenSecondaryBesselDomain packet :=
  deningerMeyerPoissonBoundaryPairLM.codRestrict
    (DeningerMeyerEvenSecondaryBesselDomain packet)
    (fun f => ⟨
      (deningerMeyerPoissonBoundaryInSecondaryBesselDomain
        packet f).property,
      deningerMeyerPoissonBoundaryPair_mem_even f⟩)

/--
Parity-corrected source-derived three-term complex.  Its middle term removes
the negative-radius defect without changing the literal differentials.
-/
def deningerMeyerEvenSecondaryThreeTermComplex :
    DeningerArithmeticThreeTermComplex ℂ
      DeningerMeyerCap
      (DeningerMeyerEvenSecondaryBesselDomain packet)
      DeningerPrimeFirstSuspensionHilbertSum where
  d0 := deningerMeyerEvenPoissonBoundaryLM packet
  d1 := (deningerMeyerSecondaryMaximalRestriction packet).comp
    (deningerMeyerEvenBesselToBesselLM packet)
  d1_comp_d0 := by
    apply LinearMap.ext
    intro f
    exact deningerMeyerPoissonBoundary_secondaryRestriction_zero packet f

/-- Exact cycle classification survives parity correction. -/
theorem deningerMeyerEvenSecondaryThreeTerm_cycles1_iff
    (h : DeningerMeyerEvenSecondaryBesselDomain packet) :
    h ∈ (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1 ↔
      ∀ p : Nat.Primes,
        (h : DeningerMeyerRadialCochainPair).1 (p : ℝ) =
            (((p : ℝ)⁻¹ : ℝ) : ℂ) *
              (h : DeningerMeyerRadialCochainPair).2
                ((p : ℝ)⁻¹) ∨
          packet p = 0 := by
  change
    deningerMeyerSecondaryMaximalRestriction packet
        (deningerMeyerEvenBesselToBesselLM packet h) = 0 ↔ _
  exact
    deningerMeyerSecondaryMaximalRestriction_eq_zero_iff packet
      (deningerMeyerEvenBesselToBesselLM packet h)

/--
The negative-radius defect sector meets the parity-corrected middle domain
only at zero.
-/
theorem deningerMeyerNegativeRadialPair_mem_even_iff
    (k : DeningerMeyerNegativeRadialFunctions) :
    deningerMeyerNegativeRadialPairLM k ∈
        DeningerMeyerEvenRadialCochainPairs ↔
      k = 0 := by
  constructor
  · rintro ⟨heven, _⟩
    apply Subtype.ext
    funext x
    by_cases hx : 0 ≤ x
    · exact k.property x hx
    · have hneg : 0 ≤ -x :=
        le_of_lt (neg_pos.mpr (lt_of_not_ge hx))
      have hzero := k.property (-x) hneg
      have he := heven (-x)
      change (k : ℝ → ℂ) (-(-x)) =
        (k : ℝ → ℂ) (-x) at he
      rw [neg_neg, hzero] at he
      exact he
  · intro hk
    subst k
    exact DeningerMeyerEvenRadialCochainPairs.zero_mem

end

end RHTower
