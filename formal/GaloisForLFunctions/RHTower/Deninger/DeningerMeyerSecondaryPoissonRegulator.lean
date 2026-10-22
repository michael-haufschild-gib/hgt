import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonCalderonGraph

/-!
# Secondary Meyer--Poisson regulator on the all-prime rational-Witt sector

Raw prime sampling is Bessel after Schwartz damping but does not descend through Meyer boundaries.
The reflected Calderón graph supplies the missing correction.  For a two-collar cochain
`h = (h₊, h₋)` its prime-`p` secondary value is

`p⁻¹ᐟ² (h₊(p) - p⁻¹ h₋(p⁻¹)) Tₚ(aₚ)`,

where `Tₚ` is the first suspension-mode transgression of the packet coefficient `aₚ`.

This module constructs the maximal graph domain defined by square-summability of these actual
values.  It is source-derived: no target weight is inserted.  Every literal Meyer--Poisson
boundary belongs to the domain because Poisson reflection makes every component zero.  The
resulting all-prime restriction has exact kernel equal to the reflected prime graph, modulo zero
packet coefficients.

For uniformly bounded packet fields, every pair of Schwartz collars enters this maximal domain
continuously.  The physical collar uses one Schwartz moment; the reflected collar uses its explicit
`p⁻¹` factor and the zeroth Schwartz seminorm.  Both have the same prime-cubic majorant.  The
pulled-back Green energy is nonnegative with exact radical, and actual finite
arithmetic-Frobenius-fixed rational-Witt packets still give positive energy off the graph.

This closes the secondary Poisson regulator, Bessel continuity, and boundary annihilation on the
separated radial two-collar sector.  It does not identify this sector with the full sheafified
arithmetic relevant complex or prove that its closed middle boundaries have no additional
relations.
-/

namespace RHTower

open MeasureTheory
open scoped ENNReal BigOperators SchwartzMap FourierTransform

noncomputable section

/-- Algebraic pair of radial collar cochains before any topology or summability condition. -/
abbrev DeningerMeyerRadialCochainPair :=
  (ℝ → ℂ) × (ℝ → ℂ)

/-- Evaluation of the physical collar at `p` and the reflected collar at `p⁻¹`. -/
def deningerMeyerRadialCochainPrimeTrace
    (p : Nat.Primes) :
    DeningerMeyerRadialCochainPair →ₗ[ℂ] ℂ × ℂ :=
  LinearMap.prod
    ((LinearMap.proj (p : ℝ)).comp
      (LinearMap.fst ℂ (ℝ → ℂ) (ℝ → ℂ)))
    ((LinearMap.proj ((p : ℝ)⁻¹)).comp
      (LinearMap.snd ℂ (ℝ → ℂ) (ℝ → ℂ)))

@[simp]
theorem deningerMeyerRadialCochainPrimeTrace_apply
    (p : Nat.Primes) (h : DeningerMeyerRadialCochainPair) :
    deningerMeyerRadialCochainPrimeTrace p h =
      (h.1 (p : ℝ), h.2 ((p : ℝ)⁻¹)) :=
  rfl

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/-- Actual secondary first-mode value of a radial two-collar cochain at one prime. -/
def deningerMeyerSecondaryFirstModeValue
    (p : Nat.Primes) :
    DeningerMeyerRadialCochainPair →ₗ[ℂ]
      DeningerPrimeSuspensionHaarL2 p :=
  (deningerMeyerReflectedFirstModeRegulator p
    (packet p)).comp
      (deningerMeyerRadialCochainPrimeTrace p)

@[simp]
theorem deningerMeyerSecondaryFirstModeValue_apply
    (p : Nat.Primes) (h : DeningerMeyerRadialCochainPair) :
    deningerMeyerSecondaryFirstModeValue packet p h =
      deningerMeyerReflectedFirstModeRegulator p (packet p)
        (h.1 (p : ℝ), h.2 ((p : ℝ)⁻¹)) :=
  rfl

/--
Maximal source graph domain: precisely the two-collar cochains whose actual secondary
first-suspension values are square-summable over all primes.
-/
def DeningerMeyerSecondaryBesselDomain :
    Submodule ℂ DeningerMeyerRadialCochainPair where
  carrier := {h |
    Memℓp
      (fun p => deningerMeyerSecondaryFirstModeValue packet p h)
      2}
  zero_mem' := by
    simpa using
      (zero_mem_ℓp' :
        Memℓp
          (fun p : Nat.Primes =>
            (0 : DeningerPrimeSuspensionHaarL2 p)) 2)
  add_mem' := by
    intro f g hf hg
    change Memℓp
      (fun p =>
        deningerMeyerSecondaryFirstModeValue packet p (f + g)) 2
    change Memℓp
      (fun p => deningerMeyerSecondaryFirstModeValue packet p f) 2 at hf
    change Memℓp
      (fun p => deningerMeyerSecondaryFirstModeValue packet p g) 2 at hg
    have hadd := hf.add hg
    convert hadd using 1
    funext p
    exact
      map_add (deningerMeyerSecondaryFirstModeValue packet p) f g
  smul_mem' := by
    intro c f hf
    change Memℓp
      (fun p =>
        deningerMeyerSecondaryFirstModeValue packet p (c • f)) 2
    change Memℓp
      (fun p => deningerMeyerSecondaryFirstModeValue packet p f) 2 at hf
    have hsmul := hf.const_smul c
    convert hsmul using 1
    funext p
    exact
      map_smul (deningerMeyerSecondaryFirstModeValue packet p) c f

/-- Canonical all-prime restriction from the maximal secondary graph domain. -/
def deningerMeyerSecondaryMaximalRestriction :
    DeningerMeyerSecondaryBesselDomain packet →ₗ[ℂ]
      DeningerPrimeFirstSuspensionHilbertSum where
  toFun h :=
    ⟨fun p => deningerMeyerSecondaryFirstModeValue packet p h,
      h.property⟩
  map_add' f g := by
    apply lp.ext
    funext p
    change
      deningerMeyerSecondaryFirstModeValue packet p
          ((f : DeningerMeyerRadialCochainPair) +
            (g : DeningerMeyerRadialCochainPair)) =
        deningerMeyerSecondaryFirstModeValue packet p f +
          deningerMeyerSecondaryFirstModeValue packet p g
    exact
      map_add (deningerMeyerSecondaryFirstModeValue packet p)
        (f : DeningerMeyerRadialCochainPair)
        (g : DeningerMeyerRadialCochainPair)
  map_smul' c f := by
    apply lp.ext
    funext p
    change
      deningerMeyerSecondaryFirstModeValue packet p
          (c • (f : DeningerMeyerRadialCochainPair)) =
        c • deningerMeyerSecondaryFirstModeValue packet p f
    exact
      map_smul (deningerMeyerSecondaryFirstModeValue packet p) c
        (f : DeningerMeyerRadialCochainPair)

@[simp]
theorem deningerMeyerSecondaryMaximalRestriction_apply
    (h : DeningerMeyerSecondaryBesselDomain packet)
    (p : Nat.Primes) :
    deningerMeyerSecondaryMaximalRestriction packet h p =
      deningerMeyerSecondaryFirstModeValue packet p h :=
  rfl

/-- Exact local kernel of the secondary value, including the possible zero-packet degeneracy. -/
theorem deningerMeyerSecondaryFirstModeValue_eq_zero_iff
    (p : Nat.Primes) (h : DeningerMeyerRadialCochainPair) :
    deningerMeyerSecondaryFirstModeValue packet p h = 0 ↔
      h.1 (p : ℝ) =
          (((p : ℝ)⁻¹ : ℝ) : ℂ) *
            h.2 ((p : ℝ)⁻¹) ∨
        packet p = 0 := by
  by_cases hp : packet p = 0
  · constructor
    · intro
      exact Or.inr hp
    · intro
      rw [deningerMeyerSecondaryFirstModeValue_apply,
        deningerMeyerReflectedFirstModeRegulator_apply,
        hp]
      have hmode :
          deningerPrimeSuspensionFirstMode p
              (0 : DeningerPrimePacketComplexHaarL2 p) = 0 :=
        map_zero (deningerPrimeSuspensionFirstMode p)
      rw [hmode, smul_zero, smul_zero]
  · simp only [hp, or_false]
    change
      deningerMeyerReflectedFirstModeRegulator p (packet p)
          (h.1 (p : ℝ), h.2 ((p : ℝ)⁻¹)) = 0 ↔ _
    rw [← LinearMap.mem_ker,
      deningerMeyerReflectedFirstModeRegulator_ker p hp,
      deningerMeyerPoissonCalderonGraph_mem_iff]
    norm_cast

/-- Exact global kernel on the maximal Bessel graph domain. -/
theorem deningerMeyerSecondaryMaximalRestriction_eq_zero_iff
    (h : DeningerMeyerSecondaryBesselDomain packet) :
    deningerMeyerSecondaryMaximalRestriction packet h = 0 ↔
      ∀ p : Nat.Primes,
        (h : DeningerMeyerRadialCochainPair).1 (p : ℝ) =
            (((p : ℝ)⁻¹ : ℝ) : ℂ) *
              (h : DeningerMeyerRadialCochainPair).2
                ((p : ℝ)⁻¹) ∨
          packet p = 0 := by
  constructor
  · intro hzero p
    have hp := congrArg
      (fun u : DeningerPrimeFirstSuspensionHilbertSum => u p)
      hzero
    change
      deningerMeyerSecondaryFirstModeValue packet p h = 0 at hp
    exact
      (deningerMeyerSecondaryFirstModeValue_eq_zero_iff
        packet p h).mp hp
  · intro hzero
    apply lp.ext
    funext p
    change deningerMeyerSecondaryFirstModeValue packet p h = 0
    exact
      (deningerMeyerSecondaryFirstModeValue_eq_zero_iff
        packet p h).mpr (hzero p)

/-- The literal physical/Fourier Meyer--Poisson boundary as a radial two-collar cochain. -/
def deningerMeyerPoissonBoundaryPair
    (f : DeningerMeyerCap) :
    DeningerMeyerRadialCochainPair :=
  (fun x => deningerMeyerSum f x,
    fun x =>
      deningerMeyerSum
        (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) x)

/-- Every prime component of every literal Meyer--Poisson boundary is killed by the correction. -/
theorem deningerMeyerPoissonBoundary_secondaryValue_zero
    (f : DeningerMeyerCap) (p : Nat.Primes) :
    deningerMeyerSecondaryFirstModeValue packet p
        (deningerMeyerPoissonBoundaryPair f) =
      0 := by
  rw [deningerMeyerSecondaryFirstModeValue_apply]
  change
    deningerMeyerReflectedFirstModeRegulator p (packet p)
        (deningerMeyerPoissonCollarTrace (p : ℝ)
          (by exact_mod_cast p.2.pos) f) =
      0
  exact
    deningerMeyerReflectedFirstModeRegulator_boundary_zero
      p (packet p) f

/-- Every literal Meyer--Poisson boundary belongs to the maximal all-prime Bessel graph domain. -/
def deningerMeyerPoissonBoundaryInSecondaryBesselDomain
    (f : DeningerMeyerCap) :
    DeningerMeyerSecondaryBesselDomain packet :=
  ⟨deningerMeyerPoissonBoundaryPair f, by
    change Memℓp
      (fun p => deningerMeyerSecondaryFirstModeValue packet p
        (deningerMeyerPoissonBoundaryPair f)) 2
    have hzero :
        (fun p =>
          deningerMeyerSecondaryFirstModeValue packet p
            (deningerMeyerPoissonBoundaryPair f)) =
          fun p : Nat.Primes =>
            (0 : DeningerPrimeSuspensionHaarL2 p) := by
      funext p
      exact
        deningerMeyerPoissonBoundary_secondaryValue_zero
          packet f p
    rw [hzero]
    exact zero_mem_ℓp'⟩

/-- The maximal all-prime secondary restriction annihilates every literal Meyer boundary. -/
theorem deningerMeyerPoissonBoundary_secondaryRestriction_zero
    (f : DeningerMeyerCap) :
    deningerMeyerSecondaryMaximalRestriction packet
        (deningerMeyerPoissonBoundaryInSecondaryBesselDomain
          packet f) =
      0 := by
  apply lp.ext
  funext p
  exact
    deningerMeyerPoissonBoundary_secondaryValue_zero
      packet f p

/-- Reflected Fourier-collar contribution to the Schwartz secondary restriction. -/
def deningerMeyerReflectedSchwartzRestrictionValue
    (g : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    DeningerPrimeSuspensionHaarL2 p :=
  (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ)) •
    (((((p : ℝ)⁻¹ : ℝ) : ℂ) * g ((p : ℝ)⁻¹)) •
      deningerPrimeSuspensionFirstMode p (packet p))

theorem norm_deningerMeyerReflectedSchwartzRestrictionValue
    (g : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    ‖deningerMeyerReflectedSchwartzRestrictionValue packet g p‖ =
      deningerPrimePolarizedHalfDensity p *
        (p : ℝ)⁻¹ * ‖g ((p : ℝ)⁻¹)‖ * ‖packet p‖ := by
  rw [deningerMeyerReflectedSchwartzRestrictionValue,
    norm_smul, norm_smul, norm_mul,
    norm_deningerPrimeSuspensionFirstMode]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg
      (deningerPrimePolarizedHalfDensity_nonneg p),
    abs_of_pos (inv_pos.mpr
      (by exact_mod_cast p.2.pos : (0 : ℝ) < (p : ℝ)))]
  ring

theorem norm_deningerMeyerReflectedSchwartzRestrictionValue_le
    {B : ℝ} (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (g : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    ‖deningerMeyerReflectedSchwartzRestrictionValue packet g p‖ ≤
      B * SchwartzMap.seminorm ℂ 0 0 g *
        (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹) := by
  let S := SchwartzMap.seminorm ℂ 0 0 g
  have hS : 0 ≤ S := by positivity
  have hg :
      ‖g ((p : ℝ)⁻¹)‖ ≤ S :=
    SchwartzMap.norm_le_seminorm ℂ g ((p : ℝ)⁻¹)
  rw [norm_deningerMeyerReflectedSchwartzRestrictionValue]
  have hhalf :
      0 ≤ deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹ :=
    mul_nonneg
      (deningerPrimePolarizedHalfDensity_nonneg p)
      (inv_nonneg.mpr (by positivity))
  calc
    deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹ *
          ‖g ((p : ℝ)⁻¹)‖ * ‖packet p‖
        ≤ deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹ *
          S * ‖packet p‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hg hhalf)
              (norm_nonneg _)
    _ ≤ deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹ *
          S * B := by
            exact mul_le_mul_of_nonneg_left (hpacket p)
              (mul_nonneg hhalf hS)
    _ = B * S *
          (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹) := by
            ring

theorem summable_norm_deningerMeyerReflectedSchwartzRestrictionValue_sq
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (g : SchwartzMap ℝ ℂ) :
    Summable (fun p =>
      ‖deningerMeyerReflectedSchwartzRestrictionValue packet g p‖ ^
        (2 : ℝ)) := by
  let S := SchwartzMap.seminorm ℂ 0 0 g
  have hmajor :
      Summable (fun p : Nat.Primes =>
        (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ)) :=
    summable_deningerPrimeCubicMass.mul_left
      ((B * S) ^ (2 : ℝ))
  refine Summable.of_nonneg_of_le
    (fun p => Real.rpow_nonneg (norm_nonneg _) 2)
    (fun p => ?_) hmajor
  have hnorm :=
    norm_deningerMeyerReflectedSchwartzRestrictionValue_le
      packet hpacket g p
  calc
    ‖deningerMeyerReflectedSchwartzRestrictionValue packet g p‖ ^
          (2 : ℝ)
        ≤ (B * S *
          (deningerPrimePolarizedHalfDensity p *
            (p : ℝ)⁻¹)) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
    _ = (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) := by
      rw [Real.mul_rpow
        (mul_nonneg hB (by positivity : 0 ≤ S))
        (mul_nonneg
          (deningerPrimePolarizedHalfDensity_nonneg p)
          (by positivity : 0 ≤ (p : ℝ)⁻¹))]
      congr 1
      rw [Real.rpow_two,
        deningerPrimePolarizedHalfDensity_mul_inv_sq]

/-- All-prime reflected Fourier-collar restriction on Schwartz data. -/
def deningerMeyerReflectedSchwartzRestriction
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (g : SchwartzMap ℝ ℂ) :
    DeningerPrimeFirstSuspensionHilbertSum :=
  ⟨fun p =>
      deningerMeyerReflectedSchwartzRestrictionValue packet g p,
    memℓp_gen
      (summable_norm_deningerMeyerReflectedSchwartzRestrictionValue_sq
        packet hB hpacket g)⟩

@[simp]
theorem deningerMeyerReflectedSchwartzRestriction_apply
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (g : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    deningerMeyerReflectedSchwartzRestriction
        packet hB hpacket g p =
      deningerMeyerReflectedSchwartzRestrictionValue packet g p :=
  rfl

theorem norm_deningerMeyerReflectedSchwartzRestriction_le
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (g : SchwartzMap ℝ ℂ) :
    ‖deningerMeyerReflectedSchwartzRestriction packet hB hpacket g‖ ≤
      (B * Real.sqrt deningerPrimeCubicMass) *
        SchwartzMap.seminorm ℂ 0 0 g := by
  let S := SchwartzMap.seminorm ℂ 0 0 g
  let C := B * Real.sqrt deningerPrimeCubicMass * S
  have hS : 0 ≤ S := by positivity
  have hC : 0 ≤ C := by positivity
  apply lp.norm_le_of_tsum_le (by norm_num) hC
  have hterms : ∀ p : Nat.Primes,
      ‖deningerMeyerReflectedSchwartzRestriction
          packet hB hpacket g p‖ ^ (2 : ℝ) ≤
        (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) := by
    intro p
    rw [deningerMeyerReflectedSchwartzRestriction_apply]
    have hnorm :=
      norm_deningerMeyerReflectedSchwartzRestrictionValue_le
        packet hpacket g p
    calc
      ‖deningerMeyerReflectedSchwartzRestrictionValue
          packet g p‖ ^ (2 : ℝ)
          ≤ (B * S *
              (deningerPrimePolarizedHalfDensity p *
                (p : ℝ)⁻¹)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
      _ = (B * S) ^ (2 : ℝ) *
          (p : ℝ) ^ (-3 : ℝ) := by
        rw [Real.mul_rpow (mul_nonneg hB hS)
          (mul_nonneg
            (deningerPrimePolarizedHalfDensity_nonneg p)
            (by positivity : 0 ≤ (p : ℝ)⁻¹))]
        congr 1
        rw [Real.rpow_two,
          deningerPrimePolarizedHalfDensity_mul_inv_sq]
  have hleft :=
    (lp.memℓp
      (deningerMeyerReflectedSchwartzRestriction
        packet hB hpacket g)).summable
      (by norm_num)
  have hright :=
    summable_deningerPrimeCubicMass.mul_left
      ((B * S) ^ (2 : ℝ))
  calc
    ∑' (p : Nat.Primes),
        ‖deningerMeyerReflectedSchwartzRestriction
          packet hB hpacket g p‖ ^ (2 : ℝ)
        ≤ ∑' (p : Nat.Primes),
            (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) :=
      Summable.tsum_le_tsum hterms hleft hright
    _ = (B * S) ^ (2 : ℝ) *
        deningerPrimeCubicMass := by
      rw [tsum_mul_left]
      rfl
    _ = C ^ (2 : ℝ) := by
      rw [show (B * S) ^ (2 : ℝ) =
          (B * S) ^ (2 : ℕ) by norm_num,
        show C ^ (2 : ℝ) = C ^ (2 : ℕ) by norm_num]
      dsimp [C]
      calc
        (B * S) ^ 2 * deningerPrimeCubicMass =
            B ^ 2 * S ^ 2 * deningerPrimeCubicMass := by
          ring
        _ = B ^ 2 * S ^ 2 *
            (Real.sqrt deningerPrimeCubicMass) ^ 2 := by
          rw [Real.sq_sqrt deningerPrimeCubicMass_nonneg]
        _ = (B * Real.sqrt deningerPrimeCubicMass * S) ^ 2 := by
          ring

/-- Continuous linear reflected Fourier-collar restriction. -/
def deningerMeyerReflectedSchwartzRestrictionCLM
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B) :
    SchwartzMap ℝ ℂ →L[ℂ]
      DeningerPrimeFirstSuspensionHilbertSum :=
  SchwartzMap.mkCLMtoNormedSpace
    (deningerMeyerReflectedSchwartzRestriction
      packet hB hpacket)
    (fun f g => by
      apply lp.ext
      funext p
      change
        deningerMeyerReflectedSchwartzRestrictionValue
            packet (f + g) p =
          deningerMeyerReflectedSchwartzRestrictionValue packet f p +
            deningerMeyerReflectedSchwartzRestrictionValue packet g p
      simp [deningerMeyerReflectedSchwartzRestrictionValue,
        mul_add, add_smul])
    (fun c f => by
      apply lp.ext
      funext p
      change
        deningerMeyerReflectedSchwartzRestrictionValue
            packet (c • f) p =
          c •
            deningerMeyerReflectedSchwartzRestrictionValue
              packet f p
      simp only [deningerMeyerReflectedSchwartzRestrictionValue,
        smul_apply, smul_smul]
      congr 1
      ring)
    ⟨{(0, 0)}, B * Real.sqrt deningerPrimeCubicMass,
      by positivity, fun g => by
        simpa using
          norm_deningerMeyerReflectedSchwartzRestriction_le
            packet hB hpacket g⟩

/--
Continuous all-prime secondary restriction on a pair of Schwartz collars.  It is the physical
prime restriction minus the reflected Fourier-collar correction.
-/
def deningerMeyerSecondarySchwartzRestrictionCLM
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B) :
    (SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) →L[ℂ]
      DeningerPrimeFirstSuspensionHilbertSum :=
  ContinuousLinearMap.coprod
    (deningerSchwartzFirstModeRestrictionCLM
      packet hB hpacket)
    (-deningerMeyerReflectedSchwartzRestrictionCLM
      packet hB hpacket)

@[simp]
theorem deningerMeyerSecondarySchwartzRestrictionCLM_apply
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ)
    (p : Nat.Primes) :
    deningerMeyerSecondarySchwartzRestrictionCLM
        packet hB hpacket fg p =
      deningerMeyerSecondaryFirstModeValue packet p
        ((fun x => fg.1 x), fun x => fg.2 x) := by
  rw [deningerMeyerSecondarySchwartzRestrictionCLM]
  change
    deningerSchwartzFirstModeRestrictionValue packet fg.1 p -
        deningerMeyerReflectedSchwartzRestrictionValue
          packet fg.2 p =
      deningerMeyerSecondaryFirstModeValue packet p
        ((fun x => fg.1 x), fun x => fg.2 x)
  rw [deningerMeyerSecondaryFirstModeValue_apply,
    deningerMeyerReflectedFirstModeRegulator_apply,
    deningerMeyerReflectedCollarDefect_apply]
  simp only [deningerMeyerReflectedSchwartzRestrictionValue,
    deningerSchwartzFirstModeRestrictionValue]
  module

/-- Exact prime-graph kernel of the continuous Schwartz secondary restriction. -/
theorem deningerMeyerSecondarySchwartzRestrictionCLM_eq_zero_iff
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) :
    deningerMeyerSecondarySchwartzRestrictionCLM
        packet hB hpacket fg = 0 ↔
      ∀ p : Nat.Primes,
        fg.1 (p : ℝ) =
            (((p : ℝ)⁻¹ : ℝ) : ℂ) *
              fg.2 ((p : ℝ)⁻¹) ∨
          packet p = 0 := by
  constructor
  · intro hzero p
    have hp := congrArg
      (fun u : DeningerPrimeFirstSuspensionHilbertSum => u p)
      hzero
    rw [deningerMeyerSecondarySchwartzRestrictionCLM_apply] at hp
    exact
      (deningerMeyerSecondaryFirstModeValue_eq_zero_iff
        packet p
        ((fun x => fg.1 x), fun x => fg.2 x)).mp hp
  · intro hzero
    apply lp.ext
    funext p
    rw [deningerMeyerSecondarySchwartzRestrictionCLM_apply]
    exact
      (deningerMeyerSecondaryFirstModeValue_eq_zero_iff
        packet p
        ((fun x => fg.1 x), fun x => fg.2 x)).mpr
          (hzero p)

/-- Continuous Schwartz collar pairs canonically enter the maximal secondary Bessel domain. -/
def deningerMeyerSchwartzPairInSecondaryBesselDomain
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) :
    DeningerMeyerSecondaryBesselDomain packet :=
  ⟨((fun x => fg.1 x), fun x => fg.2 x), by
    change Memℓp
      (fun p => deningerMeyerSecondaryFirstModeValue packet p
        ((fun x => fg.1 x), fun x => fg.2 x)) 2
    have hmem :=
      lp.memℓp
        (deningerMeyerSecondarySchwartzRestrictionCLM
          packet hB hpacket fg)
    convert hmem using 1
    funext p
    rw [deningerMeyerSecondarySchwartzRestrictionCLM_apply]⟩

/-- The maximal graph restriction agrees with its continuous Schwartz realization. -/
theorem deningerMeyerSecondaryMaximalRestriction_schwartzPair
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) :
    deningerMeyerSecondaryMaximalRestriction packet
        (deningerMeyerSchwartzPairInSecondaryBesselDomain
          packet hB hpacket fg) =
      deningerMeyerSecondarySchwartzRestrictionCLM
        packet hB hpacket fg := by
  apply lp.ext
  funext p
  rw [deningerMeyerSecondaryMaximalRestriction_apply,
    deningerMeyerSecondarySchwartzRestrictionCLM_apply]
  change
    deningerMeyerSecondaryFirstModeValue packet p
        ((fun x => fg.1 x), fun x => fg.2 x) =
      deningerMeyerSecondaryFirstModeValue packet p
        ((fun x => fg.1 x), fun x => fg.2 x)
  rfl

/-- Green energy pulled back by the continuous secondary Schwartz restriction. -/
def deningerMeyerSecondarySchwartzGreenEnergy
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) : ℝ :=
  deningerPrimeBlockSummedGreenForm
    (deningerMeyerSecondarySchwartzRestrictionCLM
      packet hB hpacket fg)
    (deningerMeyerSecondarySchwartzRestrictionCLM
      packet hB hpacket fg)

theorem deningerMeyerSecondarySchwartzGreenEnergy_nonneg
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) :
    0 ≤ deningerMeyerSecondarySchwartzGreenEnergy
      packet hB hpacket fg :=
  deningerPrimeBlockSummedGreenForm_nonneg
    (deningerMeyerSecondarySchwartzRestrictionCLM
      packet hB hpacket fg)

/-- Exact reflected prime-graph radical of the secondary Green energy. -/
theorem deningerMeyerSecondarySchwartzGreenEnergy_eq_zero_iff
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (fg : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) :
    deningerMeyerSecondarySchwartzGreenEnergy
        packet hB hpacket fg = 0 ↔
      ∀ p : Nat.Primes,
        fg.1 (p : ℝ) =
            (((p : ℝ)⁻¹ : ℝ) : ℂ) *
              fg.2 ((p : ℝ)⁻¹) ∨
          packet p = 0 := by
  rw [deningerMeyerSecondarySchwartzGreenEnergy,
    deningerPrimeBlockSummedGreenForm_self_eq_zero_iff,
    deningerMeyerSecondarySchwartzRestrictionCLM_eq_zero_iff]

theorem deningerMeyerSecondarySchwartzRestriction_zero_second
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    deningerMeyerSecondarySchwartzRestrictionCLM
        packet hB hpacket (f, 0) =
      deningerSchwartzFirstModeRestrictionCLM
        packet hB hpacket f := by
  simp [deningerMeyerSecondarySchwartzRestrictionCLM]

theorem deningerMeyerSecondarySchwartzGreenEnergy_zero_second
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    deningerMeyerSecondarySchwartzGreenEnergy
        packet hB hpacket (f, 0) =
      deningerSchwartzFirstModeGreenEnergy
        packet hB hpacket f := by
  rw [deningerMeyerSecondarySchwartzGreenEnergy,
    deningerSchwartzFirstModeGreenEnergy,
    deningerMeyerSecondarySchwartzRestriction_zero_second]
  have hmap :
      deningerSchwartzFirstModeRestrictionCLM
          packet hB hpacket f =
        deningerSchwartzFirstModeRestriction
          packet hB hpacket f :=
    rfl
  rw [hmap]

/--
Nonvacuity on the actual source: every nonzero finite rational-Witt packet retains positive
secondary Green energy after a nonvanishing physical Schwartz sample and zero reflected collar.
-/
theorem
    deningerFiniteRationalWittSecondarySchwartz_pos_globalGreenEnergy
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) (f : SchwartzMap ℝ ℂ)
    (hf : f (p : ℝ) ≠ 0) :
    0 <
      deningerMeyerSecondarySchwartzGreenEnergy
        (deningerPrimeSupportedComplexPacket p
          (deningerPrimeFiniteStageComplexHaarL2 p s F))
        (norm_nonneg _)
        (norm_deningerPrimeSupportedComplexPacket_le p
          (deningerPrimeFiniteStageComplexHaarL2 p s F))
        (f, 0) := by
  rw [deningerMeyerSecondarySchwartzGreenEnergy_zero_second]
  exact
    deningerFiniteRationalWittSchwartzFirstMode_pos_globalGreenEnergy
      p s hF f hf

end

end RHTower
