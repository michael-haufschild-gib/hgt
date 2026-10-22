import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFirstSuspensionMode
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeBlockRestrictionAssembly
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPoissonTransfer
import Mathlib.Analysis.PSeries

/-!
# Source-forced global Schwartz--Witt first-mode restriction

This module constructs a continuous all-prime restriction from the radial
Meyer--Schwartz source into Deninger's first suspension modes.  For a uniformly
bounded packet field `a`, its prime-`p` component is

`p⁻¹ᐟ² • f(p) • deningerPrimeSuspensionFirstMode p (a p)`.

All three factors are forced by earlier structure: `f(p)` is a literal
degree-`p` discrete-flow pullback, `p⁻¹ᐟ²` is the polarized half-density, and
the target is the canonical first circle mode.  One Schwartz moment gives a
prime-cubic square majorant, hence a continuous `ℓ²` restriction without any
prime-number-theorem input.

The module also proves the exact pointwise kernel and the exact radical of the
induced all-prime Green energy, then exhibits actual arithmetic-Frobenius-fixed
rational-Witt witnesses with positive global energy.  These are source-domain
and analytic-domain theorems.  They do not identify the kernel with boundaries
of a sheafified arithmetic relevant complex.
-/

namespace RHTower

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Half-density coefficient forced by a degree-`p` polarized transfer. -/
def deningerPrimePolarizedHalfDensity (p : Nat.Primes) : ℝ :=
  (Real.sqrt (p : ℝ))⁻¹

theorem deningerPrimePolarizedHalfDensity_nonneg (p : Nat.Primes) :
    0 ≤ deningerPrimePolarizedHalfDensity p :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem deningerPrimePolarizedHalfDensity_pos (p : Nat.Primes) :
    0 < deningerPrimePolarizedHalfDensity p :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast p.2.pos))

theorem deningerPrimePolarizedHalfDensity_le_one (p : Nat.Primes) :
    deningerPrimePolarizedHalfDensity p ≤ 1 := by
  rw [deningerPrimePolarizedHalfDensity,
    inv_le_one₀ (Real.sqrt_pos.mpr (by exact_mod_cast p.2.pos))]
  exact Real.one_le_sqrt.mpr (by exact_mod_cast p.2.one_lt.le)

theorem deningerPrimePolarizedHalfDensity_sq (p : Nat.Primes) :
    deningerPrimePolarizedHalfDensity p ^ 2 = (p : ℝ)⁻¹ := by
  rw [deningerPrimePolarizedHalfDensity, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ))]

theorem deningerPrimePolarizedHalfDensity_mul_inv_sq (p : Nat.Primes) :
    (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹) ^ 2 =
      (p : ℝ) ^ (-3 : ℝ) := by
  rw [mul_pow, deningerPrimePolarizedHalfDensity_sq]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [Real.rpow_neg hp.le]
  field_simp
  change (((p : ℕ) : ℝ) ^ (3 : ℝ)) = (((p : ℕ) : ℝ) ^ (3 : ℕ))
  exact Real.rpow_natCast ((p : ℕ) : ℝ) 3

/-- Prime-cubic mass forced by half-density plus one Schwartz moment. -/
def deningerPrimeCubicMass : ℝ :=
  ∑' p : Nat.Primes, ((p : ℝ) ^ (-3 : ℝ))

theorem summable_deningerPrimeCubicMass :
    Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-3 : ℝ))) := by
  exact (Real.summable_nat_rpow.mpr (by norm_num)).subtype Nat.Prime

theorem deningerPrimeCubicMass_nonneg :
    0 ≤ deningerPrimeCubicMass :=
  tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _

/-- Hilbert `ℓ²`-sum of the prime suspension blocks. -/
abbrev DeningerPrimeFirstSuspensionHilbertSum :=
  lp (fun p : Nat.Primes => DeningerPrimeSuspensionHaarL2 p) 2

/-- Sampling at `p` is the literal degree-`p` discrete flow pullback at radial base `1`. -/
theorem deningerRadialPrimeSample_eq_discreteFlowPullback
    (f : SchwartzMap ℝ ℂ) {u : ℝ} {z : ℂ}
    (hbase : deningerSuspensionLogRadius u z = 1) (p : Nat.Primes) :
    f (deningerSuspensionLogRadius (u * (p : ℝ)) z) = f (p : ℝ) := by
  have h := deningerDiscreteFlowPullback_eq_dilation f u z (p : ℕ)
  simpa [hbase] using h

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/-- Extension by zero of one literal packet vector to the all-prime packet field. -/
def deningerPrimeSupportedComplexPacket
    (p : Nat.Primes) (v : DeningerPrimePacketComplexHaarL2 p)
    (q : Nat.Primes) : DeningerPrimePacketComplexHaarL2 q :=
  if h : q = p then
    cast (congrArg DeningerPrimePacketComplexHaarL2 h.symm) v
  else 0

@[simp] theorem deningerPrimeSupportedComplexPacket_same
    (p : Nat.Primes) (v : DeningerPrimePacketComplexHaarL2 p) :
    deningerPrimeSupportedComplexPacket p v p = v := by
  simp [deningerPrimeSupportedComplexPacket]

theorem norm_deningerPrimeSupportedComplexPacket_le
    (p : Nat.Primes) (v : DeningerPrimePacketComplexHaarL2 p)
    (q : Nat.Primes) :
    ‖deningerPrimeSupportedComplexPacket p v q‖ ≤ ‖v‖ := by
  by_cases h : q = p
  · subst q
    simp
  · simp [deningerPrimeSupportedComplexPacket, h]

/-- Prime component of the source-forced first-mode restriction. -/
def deningerSchwartzFirstModeRestrictionValue
    (f : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    DeningerPrimeSuspensionHaarL2 p :=
  ((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
    (f (p : ℝ) • deningerPrimeSuspensionFirstMode p (packet p))

theorem norm_deningerSchwartzFirstModeRestrictionValue
    (f : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    ‖deningerSchwartzFirstModeRestrictionValue packet f p‖ =
      deningerPrimePolarizedHalfDensity p * ‖f (p : ℝ)‖ * ‖packet p‖ := by
  rw [deningerSchwartzFirstModeRestrictionValue, norm_smul, norm_smul,
    norm_deningerPrimeSuspensionFirstMode]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (deningerPrimePolarizedHalfDensity_nonneg p)]
  ring

theorem norm_deningerSchwartzFirstModeRestrictionValue_le
    {B : ℝ} (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    ‖deningerSchwartzFirstModeRestrictionValue packet f p‖ ≤
      B * SchwartzMap.seminorm ℂ 1 0 f *
        (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹) := by
  let S := SchwartzMap.seminorm ℂ 1 0 f
  have hS : 0 ≤ S := by positivity
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hsemRaw := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 1 (p : ℝ)
  have hsem : (p : ℝ) * ‖f (p : ℝ)‖ ≤ S := by
    simpa [S, Real.norm_eq_abs, abs_of_pos hp] using hsemRaw
  have hf : ‖f (p : ℝ)‖ ≤ S * (p : ℝ)⁻¹ := by
    simpa [div_eq_mul_inv] using
      (le_div_iff₀ hp).2 (by simpa [mul_comm] using hsem)
  rw [norm_deningerSchwartzFirstModeRestrictionValue]
  calc
    deningerPrimePolarizedHalfDensity p * ‖f (p : ℝ)‖ * ‖packet p‖
        ≤ deningerPrimePolarizedHalfDensity p * (S * (p : ℝ)⁻¹) *
            ‖packet p‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hf
              (deningerPrimePolarizedHalfDensity_nonneg p))
            (norm_nonneg _)
    _ ≤ deningerPrimePolarizedHalfDensity p * (S * (p : ℝ)⁻¹) * B := by
          exact mul_le_mul_of_nonneg_left (hpacket p)
            (mul_nonneg (deningerPrimePolarizedHalfDensity_nonneg p)
              (mul_nonneg hS (inv_nonneg.mpr hp.le)))
    _ = B * S *
        (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹) := by ring

theorem summable_norm_deningerSchwartzFirstModeRestrictionValue_sq
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    Summable (fun p =>
      ‖deningerSchwartzFirstModeRestrictionValue packet f p‖ ^ (2 : ℝ)) := by
  let S := SchwartzMap.seminorm ℂ 1 0 f
  have hmajor : Summable (fun p : Nat.Primes =>
      (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ)) :=
    summable_deningerPrimeCubicMass.mul_left ((B * S) ^ (2 : ℝ))
  refine Summable.of_nonneg_of_le
    (fun p => Real.rpow_nonneg (norm_nonneg _) 2) (fun p => ?_) hmajor
  have hnorm :=
    norm_deningerSchwartzFirstModeRestrictionValue_le packet hpacket f p
  calc
    ‖deningerSchwartzFirstModeRestrictionValue packet f p‖ ^ (2 : ℝ)
        ≤ (B * S *
            (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹)) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
    _ = (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) := by
      rw [Real.mul_rpow (mul_nonneg hB (by positivity : 0 ≤ S))
        (mul_nonneg (deningerPrimePolarizedHalfDensity_nonneg p)
          (by positivity : 0 ≤ (p : ℝ)⁻¹))]
      congr 1
      rw [Real.rpow_two, deningerPrimePolarizedHalfDensity_mul_inv_sq]

/-- Source-forced all-prime first-mode restriction. -/
def deningerSchwartzFirstModeRestriction
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    DeningerPrimeFirstSuspensionHilbertSum :=
  ⟨fun p => deningerSchwartzFirstModeRestrictionValue packet f p,
    memℓp_gen
      (summable_norm_deningerSchwartzFirstModeRestrictionValue_sq
        packet hB hpacket f)⟩

theorem deningerSchwartzFirstModeRestriction_apply
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) (p : Nat.Primes) :
    deningerSchwartzFirstModeRestriction packet hB hpacket f p =
      deningerSchwartzFirstModeRestrictionValue packet f p := rfl

/-- Exact source-sampling kernel, before arithmetic boundary classification. -/
theorem deningerSchwartzFirstModeRestriction_eq_zero_iff
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    deningerSchwartzFirstModeRestriction packet hB hpacket f = 0 ↔
      ∀ p : Nat.Primes, f (p : ℝ) = 0 ∨ packet p = 0 := by
  constructor
  · intro hzero p
    have hp := congrArg
      (fun x : DeningerPrimeFirstSuspensionHilbertSum => x p) hzero
    change ((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
        (f (p : ℝ) • deningerPrimeSuspensionFirstMode p (packet p)) = 0 at hp
    rcases smul_eq_zero.mp hp with hhalf | hrest
    · exact False.elim ((Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne') hhalf)
    · rcases smul_eq_zero.mp hrest with hf | hmode
      · exact Or.inl hf
      · refine Or.inr ((deningerPrimeSuspensionFirstMode_injective p) ?_)
        rw [map_zero]
        exact hmode
  · intro hzero
    apply lp.ext
    funext p
    rcases hzero p with hf | hp
    · change ((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          (f (p : ℝ) • deningerPrimeSuspensionFirstMode p (packet p)) = 0
      rw [hf, zero_smul, smul_zero]
    · change ((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          (f (p : ℝ) • deningerPrimeSuspensionFirstMode p (packet p)) = 0
      rw [hp, map_zero, smul_zero, smul_zero]

theorem norm_deningerSchwartzFirstModeRestriction_le
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    ‖deningerSchwartzFirstModeRestriction packet hB hpacket f‖ ≤
      (B * Real.sqrt deningerPrimeCubicMass) *
        SchwartzMap.seminorm ℂ 1 0 f := by
  let S := SchwartzMap.seminorm ℂ 1 0 f
  let C := B * Real.sqrt deningerPrimeCubicMass * S
  have hS : 0 ≤ S := by positivity
  have hC : 0 ≤ C := by positivity
  apply lp.norm_le_of_tsum_le (by norm_num) hC
  have hterms : ∀ p : Nat.Primes,
      ‖deningerSchwartzFirstModeRestriction packet hB hpacket f p‖ ^
          (2 : ℝ) ≤
        (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) := by
    intro p
    rw [deningerSchwartzFirstModeRestriction_apply]
    have hnorm :=
      norm_deningerSchwartzFirstModeRestrictionValue_le packet hpacket f p
    calc
      ‖deningerSchwartzFirstModeRestrictionValue packet f p‖ ^ (2 : ℝ)
          ≤ (B * S *
              (deningerPrimePolarizedHalfDensity p * (p : ℝ)⁻¹)) ^
                (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
      _ = (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) := by
        rw [Real.mul_rpow (mul_nonneg hB hS)
          (mul_nonneg (deningerPrimePolarizedHalfDensity_nonneg p)
            (by positivity : 0 ≤ (p : ℝ)⁻¹))]
        congr 1
        rw [Real.rpow_two, deningerPrimePolarizedHalfDensity_mul_inv_sq]
  have hleft :=
    (lp.memℓp (deningerSchwartzFirstModeRestriction packet hB hpacket f)).summable
      (by norm_num)
  have hright :=
    summable_deningerPrimeCubicMass.mul_left ((B * S) ^ (2 : ℝ))
  calc
    ∑' (p : Nat.Primes),
        ‖deningerSchwartzFirstModeRestriction packet hB hpacket f p‖ ^
          (2 : ℝ)
        ≤ ∑' (p : Nat.Primes),
            (B * S) ^ (2 : ℝ) * (p : ℝ) ^ (-3 : ℝ) :=
      Summable.tsum_le_tsum hterms hleft hright
    _ = (B * S) ^ (2 : ℝ) * deningerPrimeCubicMass := by
      rw [tsum_mul_left]
      rfl
    _ = C ^ (2 : ℝ) := by
      rw [show (B * S) ^ (2 : ℝ) = (B * S) ^ (2 : ℕ) by norm_num,
        show C ^ (2 : ℝ) = C ^ (2 : ℕ) by norm_num]
      dsimp [C]
      calc
        (B * S) ^ 2 * deningerPrimeCubicMass =
            B ^ 2 * S ^ 2 * deningerPrimeCubicMass := by ring
        _ = B ^ 2 * S ^ 2 * (Real.sqrt deningerPrimeCubicMass) ^ 2 := by
          rw [Real.sq_sqrt deningerPrimeCubicMass_nonneg]
        _ = (B * Real.sqrt deningerPrimeCubicMass * S) ^ 2 := by ring

/-- Continuous linear form of the source-forced all-prime restriction. -/
def deningerSchwartzFirstModeRestrictionCLM
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B) :
    SchwartzMap ℝ ℂ →L[ℂ] DeningerPrimeFirstSuspensionHilbertSum :=
  SchwartzMap.mkCLMtoNormedSpace
    (deningerSchwartzFirstModeRestriction packet hB hpacket)
    (fun f g => by
      apply lp.ext
      funext p
      simp [deningerSchwartzFirstModeRestriction,
        deningerSchwartzFirstModeRestrictionValue, add_smul])
    (fun a f => by
      apply lp.ext
      funext p
      change ((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          ((a * f (p : ℝ)) •
            deningerPrimeSuspensionFirstMode p (packet p)) =
        a • (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          (f (p : ℝ) • deningerPrimeSuspensionFirstMode p (packet p)))
      simp only [smul_smul]
      congr 1
      ring)
    ⟨{(1, 0)}, B * Real.sqrt deningerPrimeCubicMass, by positivity, fun f => by
      simpa using
        norm_deningerSchwartzFirstModeRestriction_le packet hB hpacket f⟩

/-- Source-pulled all-prime Green energy of the radial-damped first-mode packet field. -/
def deningerSchwartzFirstModeGreenEnergy
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) : ℝ :=
  deningerPrimeBlockSummedGreenForm
    (deningerSchwartzFirstModeRestriction packet hB hpacket f)
    (deningerSchwartzFirstModeRestriction packet hB hpacket f)

theorem deningerSchwartzFirstModeGreenEnergy_eq
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    deningerSchwartzFirstModeGreenEnergy packet hB hpacket f =
      ∑' p : Nat.Primes,
        deningerPrimeGraphGreenCoefficient p *
          (deningerPrimePolarizedHalfDensity p * ‖f (p : ℝ)‖ *
            ‖packet p‖) ^ 2 := by
  rw [deningerSchwartzFirstModeGreenEnergy,
    deningerPrimeBlockSummedGreenForm_self]
  apply tsum_congr
  intro p
  rw [deningerSchwartzFirstModeRestriction_apply,
    norm_deningerSchwartzFirstModeRestrictionValue]

theorem deningerSchwartzFirstModeGreenEnergy_nonneg
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    0 ≤ deningerSchwartzFirstModeGreenEnergy packet hB hpacket f :=
  deningerPrimeBlockSummedGreenForm_nonneg
    (deningerSchwartzFirstModeRestriction packet hB hpacket f)

theorem deningerSchwartzFirstModeGreenEnergy_eq_zero_iff
    {B : ℝ} (hB : 0 ≤ B) (hpacket : ∀ p, ‖packet p‖ ≤ B)
    (f : SchwartzMap ℝ ℂ) :
    deningerSchwartzFirstModeGreenEnergy packet hB hpacket f = 0 ↔
      ∀ p : Nat.Primes, f (p : ℝ) = 0 ∨ packet p = 0 := by
  rw [deningerSchwartzFirstModeGreenEnergy,
    deningerPrimeBlockSummedGreenForm_self_eq_zero_iff,
    deningerSchwartzFirstModeRestriction_eq_zero_iff]

/-- A nonzero finite Wrat packet, extended by zero, has positive global source Green energy after
one nonvanishing radial Schwartz sample. -/
theorem deningerFiniteRationalWittSchwartzFirstMode_pos_globalGreenEnergy
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) (f : SchwartzMap ℝ ℂ) (hf : f (p : ℝ) ≠ 0) :
    0 < deningerSchwartzFirstModeGreenEnergy
      (deningerPrimeSupportedComplexPacket p
        (deningerPrimeFiniteStageComplexHaarL2 p s F))
      (norm_nonneg _)
      (norm_deningerPrimeSupportedComplexPacket_le p
        (deningerPrimeFiniteStageComplexHaarL2 p s F))
      f := by
  let packet' := deningerPrimeSupportedComplexPacket p
    (deningerPrimeFiniteStageComplexHaarL2 p s F)
  have hnonneg :
      0 ≤ deningerSchwartzFirstModeGreenEnergy packet' (norm_nonneg _)
        (norm_deningerPrimeSupportedComplexPacket_le p
          (deningerPrimeFiniteStageComplexHaarL2 p s F)) f :=
    deningerSchwartzFirstModeGreenEnergy_nonneg packet' (norm_nonneg _)
      (norm_deningerPrimeSupportedComplexPacket_le p
        (deningerPrimeFiniteStageComplexHaarL2 p s F)) f
  have hne :
      deningerSchwartzFirstModeGreenEnergy packet' (norm_nonneg _)
        (norm_deningerPrimeSupportedComplexPacket_le p
          (deningerPrimeFiniteStageComplexHaarL2 p s F)) f ≠ 0 := by
    intro hzero
    have hkernel :=
      (deningerSchwartzFirstModeGreenEnergy_eq_zero_iff packet'
        (norm_nonneg _)
        (norm_deningerPrimeSupportedComplexPacket_le p
          (deningerPrimeFiniteStageComplexHaarL2 p s F)) f).mp hzero
    rcases hkernel p with hfp | hp
    · exact hf hfp
    · have hp' : deningerPrimeFiniteStageComplexHaarL2 p s F = 0 := by
        simpa [packet', deningerPrimeSupportedComplexPacket] using hp
      have hmode :
          deningerPrimeFiniteStageFirstSuspensionMode p s F = 0 := by
        change deningerPrimeSuspensionFirstMode p
            (deningerPrimeFiniteStageComplexHaarL2 p s F) = 0
        rw [hp', map_zero]
      exact (deningerPrimeFiniteStageFirstSuspensionMode_ne_zero p s hF) hmode
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Actual arithmetic-Frobenius-fixed Wrat admission into the global radial-damped Green domain. -/
theorem
    deningerFiniteRationalWitt_exists_witness_pos_globalGreenEnergy
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)
    (hF : F ≠ 0) (f : SchwartzMap ℝ ℂ) (hf : f (p : ℝ) ≠ 0) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      (∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus u w =
          F (QuotientGroup.mk u)) ∧
      0 < deningerSchwartzFirstModeGreenEnergy
        (deningerPrimeSupportedComplexPacket p
          (deningerPrimeFiniteStageComplexHaarL2 p s F))
        (norm_nonneg _)
        (norm_deningerPrimeSupportedComplexPacket_le p
          (deningerPrimeFiniteStageComplexHaarL2 p s F))
        f := by
  obtain ⟨w, hwfixed, heval⟩ :=
    deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective p s F
  exact ⟨w, hwfixed, heval,
    deningerFiniteRationalWittSchwartzFirstMode_pos_globalGreenEnergy
      p s hF f hf⟩

end

end RHTower
