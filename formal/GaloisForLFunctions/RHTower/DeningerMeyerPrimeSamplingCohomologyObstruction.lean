import GaloisForLFunctions.RHTower.DeningerMeyerRadialParityCorrection
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.ObserverPhantomDescent

/-!
# Prime sampling does not impose the global Meyer--Poisson relation

Radial parity is necessary but does not make the prime-sampled secondary
complex source-complete.  The entire subspace of even, zero-endpoint functions
vanishing at every prime produces distinct classes in the parity-corrected
`H¹`.

The positive survivor is an explicit all-radius Calderón defect.  Its kernel is
contained strictly in the prime-sampled cycle space.  Literal Meyer boundaries
lie in this smaller kernel.  Thus an honest relevant complex needs a global
archimedean/Calderón differential or an equivalent source topology that
recovers it; positive-prime sampling alone cannot do so.
-/

namespace RHTower

open scoped FourierTransform SchwartzMap

noncomputable section

/-- Even zero-endpoint functions invisible at every positive prime. -/
def DeningerMeyerPrimeInvisibleEvenFunctions :
    Submodule ℂ (ℝ → ℂ) where
  carrier := {k |
    Function.Even k ∧
      k 0 = 0 ∧
      ∀ p : Nat.Primes, k (p : ℝ) = 0}
  zero_mem' := by
    exact ⟨fun _ => rfl, rfl, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hfe, hf0, hfp⟩ ⟨hge, hg0, hgp⟩
    constructor
    · intro x
      change f (-x) + g (-x) = f x + g x
      rw [hfe x, hge x]
    constructor
    · change f 0 + g 0 = 0
      rw [hf0, hg0, zero_add]
    · intro p
      change f (p : ℝ) + g (p : ℝ) = 0
      rw [hfp p, hgp p, zero_add]
  smul_mem' := by
    rintro c f ⟨hfe, hf0, hfp⟩
    constructor
    · intro x
      change c * f (-x) = c * f x
      rw [hfe x]
    constructor
    · change c * f 0 = 0
      rw [hf0, mul_zero]
    · intro p
      change c * f (p : ℝ) = 0
      rw [hfp p, mul_zero]

/-- Insert a prime-invisible function in the physical collar. -/
def deningerMeyerPrimeInvisiblePairLM :
    DeningerMeyerPrimeInvisibleEvenFunctions →ₗ[ℂ]
      DeningerMeyerRadialCochainPair :=
  (LinearMap.inl ℂ (ℝ → ℂ) (ℝ → ℂ)).comp
    DeningerMeyerPrimeInvisibleEvenFunctions.subtype

@[simp]
theorem deningerMeyerPrimeInvisiblePairLM_apply
    (k : DeningerMeyerPrimeInvisibleEvenFunctions) :
    deningerMeyerPrimeInvisiblePairLM k =
      ((k : ℝ → ℂ), 0) :=
  rfl

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/--
Prime-invisible even functions enter the parity-corrected Bessel domain with
identically zero secondary values.
-/
def deningerMeyerPrimeInvisibleEvenBesselLM :
    DeningerMeyerPrimeInvisibleEvenFunctions →ₗ[ℂ]
      DeningerMeyerEvenSecondaryBesselDomain packet where
  toFun k := ⟨deningerMeyerPrimeInvisiblePairLM k, by
    constructor
    · change Memℓp
        (fun p =>
          deningerMeyerSecondaryFirstModeValue packet p
            (deningerMeyerPrimeInvisiblePairLM k)) 2
      have hzero :
          (fun p =>
            deningerMeyerSecondaryFirstModeValue packet p
              (deningerMeyerPrimeInvisiblePairLM k)) =
            fun p : Nat.Primes =>
              (0 : DeningerPrimeSuspensionHaarL2 p) := by
        funext p
        apply
          (deningerMeyerSecondaryFirstModeValue_eq_zero_iff
            packet p (deningerMeyerPrimeInvisiblePairLM k)).2
        left
        rw [deningerMeyerPrimeInvisiblePairLM_apply]
        change (k : ℝ → ℂ) (p : ℝ) =
          (((p : ℝ)⁻¹ : ℝ) : ℂ) * 0
        rw [k.property.2.2 p]
        simp
      rw [hzero]
      exact zero_mem_ℓp'
    · exact ⟨k.property.1, fun _ => rfl⟩⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add deningerMeyerPrimeInvisiblePairLM f g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul deningerMeyerPrimeInvisiblePairLM c f

@[simp]
theorem deningerMeyerPrimeInvisibleEvenBesselLM_coe
    (k : DeningerMeyerPrimeInvisibleEvenFunctions) :
    (deningerMeyerPrimeInvisibleEvenBesselLM packet k :
      DeningerMeyerRadialCochainPair) =
      ((k : ℝ → ℂ), 0) :=
  rfl

/-- Every prime-invisible even function is a cycle in the corrected complex. -/
def deningerMeyerPrimeInvisibleEvenCyclesLM :
    DeningerMeyerPrimeInvisibleEvenFunctions →ₗ[ℂ]
      (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1 :=
  (deningerMeyerPrimeInvisibleEvenBesselLM packet).codRestrict
    (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1
    (fun k => by
      rw [deningerMeyerEvenSecondaryThreeTerm_cycles1_iff]
      intro p
      left
      rw [deningerMeyerPrimeInvisibleEvenBesselLM_coe]
      change (k : ℝ → ℂ) (p : ℝ) =
        (((p : ℝ)⁻¹ : ℝ) : ℂ) * 0
      rw [k.property.2.2 p]
      simp)

/-- Middle cohomology of the parity-corrected secondary complex. -/
abbrev DeningerMeyerEvenSecondaryH1
    (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p) :=
  (deningerMeyerEvenSecondaryThreeTermComplex packet).H1

/-- Cohomology class of one prime-invisible even cycle. -/
def deningerMeyerPrimeInvisibleEvenH1
    (k : DeningerMeyerPrimeInvisibleEvenFunctions) :
    DeningerMeyerEvenSecondaryH1 packet :=
  Submodule.Quotient.mk
    (deningerMeyerPrimeInvisibleEvenCyclesLM packet k)

/-- Prime-invisible even cohomology classes depend linearly on their function. -/
def deningerMeyerPrimeInvisibleEvenH1LM :
    DeningerMeyerPrimeInvisibleEvenFunctions →ₗ[ℂ]
      DeningerMeyerEvenSecondaryH1 packet where
  toFun := deningerMeyerPrimeInvisibleEvenH1 packet
  map_add' k l := by
    change Submodule.Quotient.mk
        (deningerMeyerPrimeInvisibleEvenCyclesLM packet (k + l)) =
      Submodule.Quotient.mk
          (deningerMeyerPrimeInvisibleEvenCyclesLM packet k) +
        Submodule.Quotient.mk
          (deningerMeyerPrimeInvisibleEvenCyclesLM packet l)
    rw [map_add, Submodule.Quotient.mk_add]
  map_smul' c k := by
    change Submodule.Quotient.mk
        (deningerMeyerPrimeInvisibleEvenCyclesLM packet (c • k)) =
      c • Submodule.Quotient.mk
        (deningerMeyerPrimeInvisibleEvenCyclesLM packet k)
    rw [map_smul, Submodule.Quotient.mk_smul]

/--
The whole prime-invisible even endpoint subspace injects into the corrected
middle cohomology.  Global Poisson reflection, not parity alone, proves that
none of its nonzero members can be a literal Meyer boundary.
-/
theorem deningerMeyerPrimeInvisibleEvenH1_injective :
    Function.Injective
      (deningerMeyerPrimeInvisibleEvenH1 packet) := by
  intro k l hkl
  apply sub_eq_zero.mp
  apply Subtype.ext
  change Submodule.Quotient.mk
      (deningerMeyerPrimeInvisibleEvenCyclesLM packet k) =
    Submodule.Quotient.mk
      (deningerMeyerPrimeInvisibleEvenCyclesLM packet l) at hkl
  rw [Submodule.Quotient.eq] at hkl
  have hsub :
      deningerMeyerPrimeInvisibleEvenCyclesLM packet k -
          deningerMeyerPrimeInvisibleEvenCyclesLM packet l =
        deningerMeyerPrimeInvisibleEvenCyclesLM packet (k - l) :=
    (map_sub
      (deningerMeyerPrimeInvisibleEvenCyclesLM packet) k l).symm
  rw [hsub] at hkl
  change
    ((deningerMeyerPrimeInvisibleEvenCyclesLM packet (k - l) :
      (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1) :
        DeningerMeyerEvenSecondaryBesselDomain packet) ∈
      (deningerMeyerEvenSecondaryThreeTermComplex packet).boundaries1 at hkl
  obtain ⟨f, hf⟩ := hkl
  funext x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have heven := (k - l).property.1 (-x)
    change ((↑(k - l) : ℝ → ℂ) (-(-x))) =
      ((↑(k - l) : ℝ → ℂ) (-x)) at heven
    rw [neg_neg] at heven
    rw [heven]
    have hphysical := congrArg
      (fun h : DeningerMeyerEvenSecondaryBesselDomain packet =>
        (h : DeningerMeyerRadialCochainPair).1 (-x)) hf
    have hfourier := congrArg
      (fun h : DeningerMeyerEvenSecondaryBesselDomain packet =>
        (h : DeningerMeyerRadialCochainPair).2 (-x)⁻¹) hf
    change deningerMeyerSum f (-x) =
      ((↑(k - l) : ℝ → ℂ) (-x)) at hphysical
    change deningerMeyerSum
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
        (-x)⁻¹ = 0 at hfourier
    rw [← hphysical]
    rw [deningerMeyerPoisson_reflection f f.property hpos,
      hfourier, mul_zero]
    simp
  · subst x
    exact (k - l).property.2.1
  · have hphysical := congrArg
      (fun h : DeningerMeyerEvenSecondaryBesselDomain packet =>
        (h : DeningerMeyerRadialCochainPair).1 x) hf
    have hfourier := congrArg
      (fun h : DeningerMeyerEvenSecondaryBesselDomain packet =>
        (h : DeningerMeyerRadialCochainPair).2 x⁻¹) hf
    change deningerMeyerSum f x =
      ((↑(k - l) : ℝ → ℂ) x) at hphysical
    change deningerMeyerSum
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
        x⁻¹ = 0 at hfourier
    rw [← hphysical]
    rw [deningerMeyerPoisson_reflection f f.property hx,
      hfourier, mul_zero]
    simp

/-- Linear form of the prime-invisible cohomology injection. -/
theorem deningerMeyerPrimeInvisibleEvenH1LM_injective :
    Function.Injective
      (deningerMeyerPrimeInvisibleEvenH1LM packet) := by
  intro k l hkl
  apply deningerMeyerPrimeInvisibleEvenH1_injective packet
  exact hkl

/-- Explicit even point mass on the nonsampled radii `±1`. -/
def deningerMeyerPrimeInvisibleUnitMass :
    DeningerMeyerPrimeInvisibleEvenFunctions :=
  ⟨fun x => if x ^ (2 : ℕ) = 1 then 1 else 0, by
    constructor
    · intro x
      change (if (-x) ^ (2 : ℕ) = 1 then 1 else 0) =
        (if x ^ (2 : ℕ) = 1 then 1 else 0)
      rw [neg_sq]
    constructor
    · norm_num
    · intro p
      change (if (p : ℝ) ^ (2 : ℕ) = 1 then 1 else 0) = 0
      rw [if_neg]
      intro hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast p.2.two_le
      nlinarith⟩

theorem deningerMeyerPrimeInvisibleUnitMass_ne_zero :
    deningerMeyerPrimeInvisibleUnitMass ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun k : DeningerMeyerPrimeInvisibleEvenFunctions =>
      (k : ℝ → ℂ) 1) hzero
  norm_num [deningerMeyerPrimeInvisibleUnitMass] at h

/-- Concrete nonzero corrected `H¹` class missed by every prime sample. -/
theorem deningerMeyerPrimeInvisibleUnitMass_H1_ne_zero :
    deningerMeyerPrimeInvisibleEvenH1LM packet
        deningerMeyerPrimeInvisibleUnitMass ≠
      0 := by
  intro hzero
  have heq :
      deningerMeyerPrimeInvisibleEvenH1LM packet
          deningerMeyerPrimeInvisibleUnitMass =
        deningerMeyerPrimeInvisibleEvenH1LM packet 0 := by
    calc
      deningerMeyerPrimeInvisibleEvenH1LM packet
          deningerMeyerPrimeInvisibleUnitMass = 0 := hzero
      _ = deningerMeyerPrimeInvisibleEvenH1LM packet 0 :=
        (map_zero
          (deningerMeyerPrimeInvisibleEvenH1LM packet)).symm
  exact deningerMeyerPrimeInvisibleUnitMass_ne_zero
    (deningerMeyerPrimeInvisibleEvenH1LM_injective packet heq)

/-- Positive real radii, the natural domain of Meyer--Poisson reflection. -/
abbrev DeningerMeyerPositiveRadius := {x : ℝ // 0 < x}

/-- Positive-prime point observers inside the full positive-radius collar. -/
def deningerMeyerPositivePrimePointObserver
    (p : Nat.Primes) : Unit → DeningerMeyerPositiveRadius :=
  fun _ => ⟨(p : ℝ), by exact_mod_cast p.2.pos⟩

/-- The explicit nonsampled unit mass as a section on the positive-radius collar. -/
def deningerMeyerPrimeInvisibleUnitMassSection :
    DeningerMeyerPositiveRadius → ℂ :=
  fun x => (deningerMeyerPrimeInvisibleUnitMass : ℝ → ℂ) (x : ℝ)

/-- The unit-mass class is a literal section phantom for positive-prime point observers. -/
theorem deningerMeyerPositivePrimeObservers_unitMass_sectionPhantom :
    _root_.HTGeometry.NomologicalHomotopyGeometry.SectionObserverDescent.SectionObserverPhantom
      (fun p => deningerMeyerPositivePrimePointObserver p)
      (0 : ℂ) deningerMeyerPrimeInvisibleUnitMassSection := by
  constructor
  · intro hzero
    have h := congrFun hzero ⟨1, by positivity⟩
    norm_num [deningerMeyerPrimeInvisibleUnitMassSection,
      deningerMeyerPrimeInvisibleUnitMass] at h
  · intro p x
    change (deningerMeyerPrimeInvisibleUnitMass : ℝ → ℂ) (p : ℝ) = 0
    exact deningerMeyerPrimeInvisibleUnitMass.property.2.2 p

/-- Positive-prime points are not a jointly covering observer family for the all-radius collar. -/
theorem deningerMeyerPositivePrimeObservers_not_jointlySurjective :
    ¬ ∀ x : DeningerMeyerPositiveRadius,
      ∃ p : Nat.Primes, ∃ u : Unit,
        deningerMeyerPositivePrimePointObserver p u = x := by
  exact
    _root_.HTGeometry.NomologicalHomotopyGeometry.SectionObserverDescent.sectionObserverPhantom_not_jointlySurjective
        (fun p => deningerMeyerPositivePrimePointObserver p)
        (0 : ℂ) deningerMeyerPrimeInvisibleUnitMassSection
        deningerMeyerPositivePrimeObservers_unitMass_sectionPhantom

/-- All-radius Calderón defect, before sparse prime sampling. -/
def deningerMeyerGlobalPoissonDefectLM :
    DeningerMeyerRadialCochainPair →ₗ[ℂ]
      (DeningerMeyerPositiveRadius → ℂ) where
  toFun h x :=
    h.1 (x : ℝ) -
      ((((x : ℝ)⁻¹ : ℝ) : ℂ) * h.2 ((x : ℝ)⁻¹))
  map_add' f g := by
    funext x
    change
      (f.1 (x : ℝ) + g.1 (x : ℝ)) -
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
            (f.2 ((x : ℝ)⁻¹) + g.2 ((x : ℝ)⁻¹))) =
        (f.1 (x : ℝ) -
            ((((x : ℝ)⁻¹ : ℝ) : ℂ) * f.2 ((x : ℝ)⁻¹))) +
          (g.1 (x : ℝ) -
            ((((x : ℝ)⁻¹ : ℝ) : ℂ) * g.2 ((x : ℝ)⁻¹)))
    ring
  map_smul' c f := by
    funext x
    change
      c * f.1 (x : ℝ) -
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
            (c * f.2 ((x : ℝ)⁻¹))) =
        c * (f.1 (x : ℝ) -
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) * f.2 ((x : ℝ)⁻¹)))
    ring

@[simp]
theorem deningerMeyerGlobalPoissonDefectLM_apply
    (h : DeningerMeyerRadialCochainPair)
    (x : DeningerMeyerPositiveRadius) :
    deningerMeyerGlobalPoissonDefectLM h x =
      h.1 (x : ℝ) -
        ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
          h.2 ((x : ℝ)⁻¹)) :=
  rfl

/-- Literal Meyer boundaries have zero all-radius Calderón defect. -/
theorem deningerMeyerGlobalPoissonDefect_boundary_zero
    (f : DeningerMeyerCap) :
    deningerMeyerGlobalPoissonDefectLM
        (deningerMeyerPoissonBoundaryPair f) =
      0 := by
  funext x
  change deningerMeyerSum f (x : ℝ) -
      ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
        deningerMeyerSum
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
          ((x : ℝ)⁻¹)) =
    0
  apply sub_eq_zero.mpr
  convert
    deningerMeyerPoisson_reflection f f.property x.property using 1
  norm_cast

/-- All-radius defect restricted to the parity-corrected Bessel domain. -/
def deningerMeyerEvenGlobalPoissonDefectLM :
    DeningerMeyerEvenSecondaryBesselDomain packet →ₗ[ℂ]
      (DeningerMeyerPositiveRadius → ℂ) :=
  deningerMeyerGlobalPoissonDefectLM.comp
    (DeningerMeyerEvenSecondaryBesselDomain packet).subtype

/--
All-radius separated Meyer--Poisson complex.  Unlike the prime-sampled
complex, its second differential records the full source Poisson graph.
-/
def deningerMeyerGlobalPoissonThreeTermComplex :
    DeningerArithmeticThreeTermComplex ℂ
      DeningerMeyerCap
      (DeningerMeyerEvenSecondaryBesselDomain packet)
      (DeningerMeyerPositiveRadius → ℂ) where
  d0 := deningerMeyerEvenPoissonBoundaryLM packet
  d1 := deningerMeyerEvenGlobalPoissonDefectLM packet
  d1_comp_d0 := by
    apply LinearMap.ext
    intro f
    exact deningerMeyerGlobalPoissonDefect_boundary_zero f

/-- Exact all-radius cycle classification: cycles are precisely global Poisson graphs. -/
theorem deningerMeyerGlobalPoissonThreeTerm_cycles1_iff
    (h : DeningerMeyerEvenSecondaryBesselDomain packet) :
    h ∈ (deningerMeyerGlobalPoissonThreeTermComplex packet).cycles1 ↔
      ∀ x : DeningerMeyerPositiveRadius,
        (h : DeningerMeyerRadialCochainPair).1 (x : ℝ) =
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
            (h : DeningerMeyerRadialCochainPair).2
              ((x : ℝ)⁻¹)) := by
  change deningerMeyerEvenGlobalPoissonDefectLM packet h = 0 ↔ _
  constructor
  · intro hzero x
    have heval := congrArg
      (fun u : DeningerMeyerPositiveRadius → ℂ => u x)
      hzero
    simp only [Pi.zero_apply] at heval
    change deningerMeyerGlobalPoissonDefectLM
      (h : DeningerMeyerRadialCochainPair) x = 0 at heval
    rw [deningerMeyerGlobalPoissonDefectLM_apply] at heval
    exact sub_eq_zero.mp heval
  · intro hgraph
    funext x
    change
      (h : DeningerMeyerRadialCochainPair).1 (x : ℝ) -
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
            (h : DeningerMeyerRadialCochainPair).2
              ((x : ℝ)⁻¹)) =
        0
    exact sub_eq_zero.mpr (hgraph x)

/-- Every global Calderón cycle is a prime-sampled secondary cycle. -/
theorem deningerMeyerGlobalPoissonDefect_ker_le_cycles :
    LinearMap.ker
        (deningerMeyerEvenGlobalPoissonDefectLM packet) ≤
      (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1 := by
  intro h hh
  rw [deningerMeyerEvenSecondaryThreeTerm_cycles1_iff]
  intro p
  left
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast p.2.pos
  have heval := congrArg
    (fun u : DeningerMeyerPositiveRadius → ℂ =>
      u ⟨(p : ℝ), hp⟩) hh
  simp only [Pi.zero_apply] at heval
  change deningerMeyerGlobalPoissonDefectLM
    (h : DeningerMeyerRadialCochainPair)
      ⟨(p : ℝ), hp⟩ = 0 at heval
  rw [deningerMeyerGlobalPoissonDefectLM_apply] at heval
  exact sub_eq_zero.mp heval

/-- The explicit `±1` class is not a global Calderón cycle. -/
theorem deningerMeyerPrimeInvisibleUnitMass_not_globalDefect_ker :
    deningerMeyerPrimeInvisibleEvenBesselLM packet
        deningerMeyerPrimeInvisibleUnitMass ∉
      LinearMap.ker
        (deningerMeyerEvenGlobalPoissonDefectLM packet) := by
  intro hker
  have heval := congrArg
    (fun u : DeningerMeyerPositiveRadius → ℂ =>
      u ⟨1, by positivity⟩) hker
  norm_num [deningerMeyerEvenGlobalPoissonDefectLM,
    deningerMeyerGlobalPoissonDefectLM,
    deningerMeyerPrimeInvisibleEvenBesselLM_coe,
    deningerMeyerPrimeInvisibleUnitMass] at heval

/--
Prime-sampled cycles strictly exceed all-radius Poisson cycles.  This is the
exact remaining differential obstruction after radial parity correction.
-/
theorem deningerMeyerGlobalPoissonDefect_ker_lt_cycles :
    LinearMap.ker
        (deningerMeyerEvenGlobalPoissonDefectLM packet) <
      (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1 := by
  apply lt_of_le_of_ne
    (deningerMeyerGlobalPoissonDefect_ker_le_cycles packet)
  intro heq
  have hcycle :
      deningerMeyerPrimeInvisibleEvenBesselLM packet
          deningerMeyerPrimeInvisibleUnitMass ∈
        (deningerMeyerEvenSecondaryThreeTermComplex packet).cycles1 :=
    (deningerMeyerPrimeInvisibleEvenCyclesLM packet
      deningerMeyerPrimeInvisibleUnitMass).property
  rw [← heq] at hcycle
  exact
    deningerMeyerPrimeInvisibleUnitMass_not_globalDefect_ker
      packet hcycle

end

end RHTower
