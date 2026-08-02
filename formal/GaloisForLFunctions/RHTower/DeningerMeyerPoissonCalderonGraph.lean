import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzPoisson
import GaloisForLFunctions.RHTower.DeningerMeyerRadialEndpoints
import GaloisForLFunctions.RHTower.DeningerArithmeticPoissonTransfer
import GaloisForLFunctions.RHTower.DeningerRationalWittSchwartzBesselRestriction

/-!
# Meyer's Poisson boundary as a radial Calderón graph

The bilateral scaled Poisson identity already available in the rational CCM sector has a sharper
one-sided consequence on Meyer's endpoint domain.  If `f` is even and both zero modes vanish, then

`Z f(x) = x⁻¹ Z (𝓕 f)(x⁻¹)` for `x > 0`.

Thus the two reflected collar values of every Meyer boundary lie on the concrete graph

`u = x⁻¹ v`.

The conormal defect `u - x⁻¹ v` has exactly this graph as kernel and is surjective.  Consequently
the quotient of the two-collar value space by the Poisson graph is canonically one-dimensional.
This gives a literal secondary regulator: raw prime evaluation is its first leg, while the
reflected Fourier collar is the correction that agrees with raw evaluation on every Poisson
boundary.

The last part tensors the quotient regulator with the source-forced polarized first suspension
mode.  For every nonzero packet coefficient its raw kernel is exactly the Poisson graph, so the
induced map from the graph quotient is injective.  This supplies the local quotient-corrected
Cauchy transgression demanded by Route L.  It does not identify the two-collar cochain space with
the full arithmetic relevant coefficient complex.
-/

namespace RHTower

open scoped SchwartzMap FourierTransform

noncomputable section

open GaloisForLFunctions.RHTower

/-- Positive-dilation sampling of a Schwartz function is summable away from the origin. -/
theorem deningerMeyerPositiveSum_summable
    (f : SchwartzMap ℝ ℂ) {x : ℝ} (hx : x ≠ 0) :
    Summable (fun n : ℕ => f (((n : ℝ) + 1) * x)) := by
  have h :=
    (ccmRationalArchimedeanSchwartz_lattice_summable f hx).of_norm
  have hsub :
      Summable (fun n : ℕ =>
        f (x * (((n : ℤ) + 1 : ℤ) : ℝ))) := by
    exact h.comp_injective (fun m n hmn => by omega)
  convert hsub using 1
  funext n
  congr 1
  push_cast
  ring

/--
For an even Schwartz source with vanishing physical zero mode, its bilateral lattice trace is
twice Meyer's positive sum.
-/
theorem deningerMeyerLatticeTrace_eq_two_sum
    (f : SchwartzMap ℝ ℂ)
    (heven : Function.Even (fun x : ℝ => f x))
    (hf0 : f 0 = 0) {x : ℝ} (hx : x ≠ 0) :
    ccmRationalArchimedeanLatticeTrace f x =
      2 * deningerMeyerSum f x := by
  have hsum :=
    ccmRationalArchimedeanLatticeTrace_summable f hx
  have hevenInt :
      Function.Even (fun n : ℤ => f (x * (n : ℝ))) := by
    intro n
    change f (x * ((-n : ℤ) : ℝ)) = f (x * (n : ℝ))
    rw [show x * ((-n : ℤ) : ℝ) =
        -(x * (n : ℝ)) by
      push_cast
      ring]
    exact heven (x * (n : ℝ))
  rw [ccmRationalArchimedeanLatticeTrace,
    tsum_int_eq_zero_add_two_mul_tsum_pnat hevenInt hsum]
  simp only [Int.cast_zero, mul_zero, hf0, zero_add, nsmul_eq_mul]
  congr 1
  calc
    (∑' n : ℕ+, f (x * ((n : ℤ) : ℝ))) =
        ∑' n : ℕ+, f (x * ((n : ℕ) : ℝ)) := by
      apply tsum_congr
      intro n
      congr 1
    _ = ∑' n : ℕ, f (x * ((n + 1 : ℕ) : ℝ)) :=
      tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => f (x * (n : ℝ)))
    _ = deningerMeyerSum f x := by
      rw [deningerMeyerSum]
      apply tsum_congr
      intro n
      congr 1
      push_cast
      ring

/-- The Fourier transform of an even complex Schwartz function is even. -/
theorem deningerFourier_even_of_even
    (f : SchwartzMap ℝ ℂ)
    (heven : Function.Even (fun x : ℝ => f x)) :
    Function.Even (fun x : ℝ =>
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) x) := by
  let g : ℝ → ℂ := fun x => f x
  have hg :
      g ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) = g := by
    funext x
    exact heven x
  intro w
  have h :=
    Real.fourier_comp_linearIsometry
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) g w
  rw [hg] at h
  exact h.symm

/--
**Meyer--Poisson reflection law.**  On Meyer's even two-endpoint domain the positive-dilation
sum on one collar is exactly the inverse-weighted Fourier sum on the reflected collar.
-/
theorem deningerMeyerPoisson_reflection
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    {x : ℝ} (hx : 0 < x) :
    deningerMeyerSum f x =
      (x⁻¹ : ℂ) *
        deningerMeyerSum
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
          x⁻¹ := by
  obtain ⟨heven, hf0, hF0⟩ :=
    (deningerMeyerCap_mem_iff f).mp hf
  have hleft :=
    deningerMeyerLatticeTrace_eq_two_sum
      f heven hf0 hx.ne'
  have hFeven := deningerFourier_even_of_even f heven
  have hright :=
    deningerMeyerLatticeTrace_eq_two_sum
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
      hFeven hF0 (inv_ne_zero hx.ne')
  rw [FourierTransform.fourierCLE_apply] at hright
  have hp :=
    ccmRationalArchimedeanLatticeTrace_poisson f hx
  rw [hleft, hright] at hp
  rw [FourierTransform.fourierCLE_apply]
  linear_combination (1 / 2) * hp

/-- Meyer's positive sum at one nonzero radius, bundled as a linear functional. -/
def deningerMeyerPositiveSumLM (x : ℝ) (hx : x ≠ 0) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ where
  toFun f := deningerMeyerSum f x
  map_add' f g := by
    rw [deningerMeyerSum]
    simp only [add_apply]
    exact
      (deningerMeyerPositiveSum_summable f hx).tsum_add
        (deningerMeyerPositiveSum_summable g hx)
  map_smul' c f := by
    rw [deningerMeyerSum]
    simp only [smul_apply]
    exact
      Summable.tsum_const_smul c
        (deningerMeyerPositiveSum_summable f hx)

@[simp]
theorem deningerMeyerPositiveSumLM_apply
    (x : ℝ) (hx : x ≠ 0) (f : SchwartzMap ℝ ℂ) :
    deningerMeyerPositiveSumLM x hx f =
      deningerMeyerSum f x :=
  rfl

/-- The two reflected collar values of one Meyer boundary. -/
def deningerMeyerPoissonCollarTrace (x : ℝ) (hx : 0 < x) :
    DeningerMeyerCap →ₗ[ℂ] ℂ × ℂ :=
  LinearMap.prod
    ((deningerMeyerPositiveSumLM x hx.ne').comp
      DeningerMeyerCap.subtype)
    ((deningerMeyerPositiveSumLM x⁻¹
        (inv_ne_zero hx.ne')).comp
      ((FourierTransform.fourierCLE ℂ
          (SchwartzMap ℝ ℂ)).toLinearMap.comp
        DeningerMeyerCap.subtype))

@[simp]
theorem deningerMeyerPoissonCollarTrace_apply
    (x : ℝ) (hx : 0 < x) (f : DeningerMeyerCap) :
    deningerMeyerPoissonCollarTrace x hx f =
      (deningerMeyerSum f x,
        deningerMeyerSum
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f) x⁻¹) :=
  rfl

/-- Conormal defect of the inverse-weighted reflected collar graph. -/
def deningerMeyerReflectedCollarDefect
    (x : ℝ) : (ℂ × ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.fst ℂ ℂ ℂ -
    (x⁻¹ : ℂ) • LinearMap.snd ℂ ℂ ℂ

@[simp]
theorem deningerMeyerReflectedCollarDefect_apply
    (x : ℝ) (u : ℂ × ℂ) :
    deningerMeyerReflectedCollarDefect x u =
      u.1 - (x⁻¹ : ℂ) * u.2 :=
  rfl

/-- Concrete radial Calderón graph cut out by Meyer--Poisson reflection. -/
def deningerMeyerPoissonCalderonGraph
    (x : ℝ) : Submodule ℂ (ℂ × ℂ) :=
  LinearMap.ker (deningerMeyerReflectedCollarDefect x)

theorem deningerMeyerPoissonCalderonGraph_mem_iff
    (x : ℝ) (u : ℂ × ℂ) :
    u ∈ deningerMeyerPoissonCalderonGraph x ↔
      u.1 = (x⁻¹ : ℂ) * u.2 := by
  rw [deningerMeyerPoissonCalderonGraph,
    LinearMap.mem_ker,
    deningerMeyerReflectedCollarDefect_apply,
    sub_eq_zero]

/-- Every literal Meyer boundary lands in the concrete reflected Calderón graph. -/
theorem deningerMeyerPoissonCollarTrace_mem_calderonGraph
    (x : ℝ) (hx : 0 < x) (f : DeningerMeyerCap) :
    deningerMeyerPoissonCollarTrace x hx f ∈
      deningerMeyerPoissonCalderonGraph x := by
  rw [deningerMeyerPoissonCalderonGraph_mem_iff,
    deningerMeyerPoissonCollarTrace_apply]
  exact deningerMeyerPoisson_reflection f f.property hx

/-- The reflected collar defect reads every scalar value. -/
theorem deningerMeyerReflectedCollarDefect_surjective
    (x : ℝ) :
    Function.Surjective
      (deningerMeyerReflectedCollarDefect x) := by
  intro z
  refine ⟨(z, 0), ?_⟩
  simp

/--
Exact local boundary classification: the two-collar value space modulo the Poisson graph is
canonically the one-dimensional defect line.
-/
def deningerMeyerPoissonCalderonQuotientEquiv
    (x : ℝ) :
    ((ℂ × ℂ) ⧸ deningerMeyerPoissonCalderonGraph x) ≃ₗ[ℂ] ℂ :=
  (deningerMeyerReflectedCollarDefect x).quotKerEquivRange.trans
    (LinearEquiv.ofTop
      (LinearMap.range
        (deningerMeyerReflectedCollarDefect x))
      (LinearMap.range_eq_top.mpr
        (deningerMeyerReflectedCollarDefect_surjective x)))

@[simp]
theorem deningerMeyerPoissonCalderonQuotientEquiv_mk
    (x : ℝ) (u : ℂ × ℂ) :
    deningerMeyerPoissonCalderonQuotientEquiv x
        (Submodule.Quotient.mk u) =
      deningerMeyerReflectedCollarDefect x u :=
  rfl

/-- A Meyer boundary has zero class in the reflected collar quotient. -/
theorem deningerMeyerPoissonCollarTrace_quotient_zero
    (x : ℝ) (hx : 0 < x) (f : DeningerMeyerCap) :
    Submodule.Quotient.mk
        (deningerMeyerPoissonCollarTrace x hx f) =
      (0 :
        (ℂ × ℂ) ⧸
          deningerMeyerPoissonCalderonGraph x) := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact
    deningerMeyerPoissonCollarTrace_mem_calderonGraph
      x hx f

/--
Polarized first-suspension transgression of the secondary collar defect at an arithmetic prime.
-/
def deningerMeyerReflectedFirstModeRegulator
    (p : Nat.Primes)
    (packet : DeningerPrimePacketComplexHaarL2 p) :
    (ℂ × ℂ) →ₗ[ℂ] DeningerPrimeSuspensionHaarL2 p :=
  (LinearMap.toSpanSingleton ℂ
    (DeningerPrimeSuspensionHaarL2 p)
    (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
      deningerPrimeSuspensionFirstMode p packet)).comp
    (deningerMeyerReflectedCollarDefect (p : ℝ))

@[simp]
theorem deningerMeyerReflectedFirstModeRegulator_apply
    (p : Nat.Primes)
    (packet : DeningerPrimePacketComplexHaarL2 p)
    (u : ℂ × ℂ) :
    deningerMeyerReflectedFirstModeRegulator p packet u =
      deningerMeyerReflectedCollarDefect (p : ℝ) u •
        (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          deningerPrimeSuspensionFirstMode p packet) :=
  rfl

/--
For a nonzero packet, the raw secondary first-mode regulator has exactly the Poisson graph as its
kernel.
-/
theorem deningerMeyerReflectedFirstModeRegulator_ker
    (p : Nat.Primes)
    {packet : DeningerPrimePacketComplexHaarL2 p}
    (hpacket : packet ≠ 0) :
    LinearMap.ker
        (deningerMeyerReflectedFirstModeRegulator p packet) =
      deningerMeyerPoissonCalderonGraph (p : ℝ) := by
  apply le_antisymm
  · intro u hu
    rw [LinearMap.mem_ker,
      deningerMeyerReflectedFirstModeRegulator_apply] at hu
    have hmode :
        (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          deningerPrimeSuspensionFirstMode p packet) ≠ 0 := by
      rw [smul_ne_zero_iff]
      refine
        ⟨Complex.ofReal_ne_zero.mpr
          (deningerPrimePolarizedHalfDensity_pos p).ne', ?_⟩
      intro hzero
      apply hpacket
      rw [← norm_eq_zero,
        ← norm_deningerPrimeSuspensionFirstMode p packet,
        hzero, norm_zero]
    have hdef :
        deningerMeyerReflectedCollarDefect (p : ℝ) u = 0 :=
      (smul_eq_zero.mp hu).resolve_right hmode
    rw [deningerMeyerPoissonCalderonGraph,
      LinearMap.mem_ker]
    exact hdef
  · intro u hu
    rw [deningerMeyerPoissonCalderonGraph,
      LinearMap.mem_ker] at hu
    rw [LinearMap.mem_ker,
      deningerMeyerReflectedFirstModeRegulator_apply,
      hu, zero_smul]

/-- The secondary first-mode regulator annihilates every literal Meyer boundary. -/
theorem deningerMeyerReflectedFirstModeRegulator_boundary_zero
    (p : Nat.Primes)
    (packet : DeningerPrimePacketComplexHaarL2 p)
    (f : DeningerMeyerCap) :
    deningerMeyerReflectedFirstModeRegulator p packet
        (deningerMeyerPoissonCollarTrace (p : ℝ)
          (by exact_mod_cast p.2.pos) f) =
      0 := by
  rw [deningerMeyerReflectedFirstModeRegulator_apply]
  have hmem :=
    deningerMeyerPoissonCollarTrace_mem_calderonGraph
      (p : ℝ) (by exact_mod_cast p.2.pos) f
  rw [deningerMeyerPoissonCalderonGraph,
    LinearMap.mem_ker] at hmem
  rw [hmem, zero_smul]

/-- First-suspension regulator induced on the exact Poisson graph quotient. -/
def deningerMeyerPoissonCalderonPacketRegulator
    (p : Nat.Primes)
    (packet : DeningerPrimePacketComplexHaarL2 p) :
    ((ℂ × ℂ) ⧸
      deningerMeyerPoissonCalderonGraph (p : ℝ)) →ₗ[ℂ]
        DeningerPrimeSuspensionHaarL2 p :=
  (deningerMeyerPoissonCalderonGraph (p : ℝ)).liftQ
    (deningerMeyerReflectedFirstModeRegulator p packet) (by
      intro u hu
      rw [deningerMeyerPoissonCalderonGraph,
        LinearMap.mem_ker] at hu
      rw [LinearMap.mem_ker,
        deningerMeyerReflectedFirstModeRegulator_apply,
        hu, zero_smul])

@[simp]
theorem deningerMeyerPoissonCalderonPacketRegulator_mk
    (p : Nat.Primes)
    (packet : DeningerPrimePacketComplexHaarL2 p)
    (u : ℂ × ℂ) :
    deningerMeyerPoissonCalderonPacketRegulator p packet
        (Submodule.Quotient.mk u) =
      deningerMeyerReflectedFirstModeRegulator p packet u :=
  rfl

/--
Every nonzero rational-Witt packet gives an injective first-mode transgression of the exact
Poisson collar quotient.
-/
theorem deningerMeyerPoissonCalderonPacketRegulator_injective
    (p : Nat.Primes)
    {packet : DeningerPrimePacketComplexHaarL2 p}
    (hpacket : packet ≠ 0) :
    Function.Injective
      (deningerMeyerPoissonCalderonPacketRegulator p packet) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ u =>
      rw [LinearMap.mem_ker,
        deningerMeyerPoissonCalderonPacketRegulator_mk] at hq
      have hu :
          u ∈ deningerMeyerPoissonCalderonGraph (p : ℝ) := by
        rw [←
          deningerMeyerReflectedFirstModeRegulator_ker
            p hpacket,
          LinearMap.mem_ker]
        exact hq
      rw [Submodule.mem_bot]
      exact
        (Submodule.Quotient.mk_eq_zero
          (deningerMeyerPoissonCalderonGraph (p : ℝ))).2 hu
  · exact bot_le

end

end RHTower
