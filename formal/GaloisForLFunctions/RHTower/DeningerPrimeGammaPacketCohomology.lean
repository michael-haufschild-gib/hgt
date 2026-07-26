import GaloisForLFunctions.RHTower.XiWeilResolventSource

/-!
# Prime--Gamma packet cohomology: source construction

This file starts the degree-one object from arithmetic source data, rather than from the Xi
divisor.  Absolute convergence naturally gives two Cauchy sectors:

* a lower sector, on which `primeArchSourceRelativeTrace z` is defined by the von-Mangoldt
  `LSeries` and the archimedean factor;
* its conjugate upper sector.

The source cup kernel is the divided difference of that trace.  At the reflected diagonal the
divided difference is completed by `-deriv`; this is the only holomorphic extension compatible
with the off-diagonal formula.  Finite packets form free complex modules, and quotienting by the
left and right radicals gives the algebraic source degree-one sectors.

Definitions in this file contain no Xi-zero enumeration.  The atomic off-diagonal comparison
with the previously proved divisor-side Weil polarization is a theorem, not part of the
construction.  Positivity, Hilbert completion, and the reflected-diagonal comparison remain
separate analytic steps.
-/

open Complex

namespace RHTower

noncomputable section

/-- Lower Cauchy parameters lying in the absolute Euler half-plane. -/
abbrev DeningerPrimeGammaLowerPoint :=
  {z : ℂ // 1 < (1 / 2 + z * Complex.I).re}

/-- Upper Cauchy parameters whose conjugates lie in the absolute Euler half-plane. -/
abbrev DeningerPrimeGammaUpperPoint :=
  {w : ℂ // 1 < (1 / 2 + (starRingEnd ℂ) w * Complex.I).re}

/-- Complex conjugation exchanges the two source Cauchy sectors. -/
def deningerPrimeGammaPointConjEquiv :
    DeningerPrimeGammaLowerPoint ≃ DeningerPrimeGammaUpperPoint where
  toFun z := ⟨(starRingEnd ℂ) z, by simpa using z.property⟩
  invFun w := ⟨(starRingEnd ℂ) w, by simpa using w.property⟩
  left_inv z := by ext; simp
  right_inv w := by ext; simp

/-- Free finite packets in the lower source sector. -/
abbrev DeningerPrimeGammaLowerPacket :=
  DeningerPrimeGammaLowerPoint →₀ ℂ

/-- Free finite packets in the upper source sector. -/
abbrev DeningerPrimeGammaUpperPacket :=
  DeningerPrimeGammaUpperPoint →₀ ℂ

/--
Source-only prime--Gamma cup kernel.

The reflected diagonal is the removable value of
`(T(conj w) - T(z)) / (z - conj w)`, hence equals `-T'(z)`.
-/
def deningerPrimeGammaSourceKernel
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint) : ℂ :=
  if (z : ℂ) = (starRingEnd ℂ) (w : ℂ) then
    -deriv primeArchSourceRelativeTrace (z : ℂ)
  else
    (primeArchSourceRelativeTrace ((starRingEnd ℂ) (w : ℂ)) -
      primeArchSourceRelativeTrace (z : ℂ)) /
        ((z : ℂ) - (starRingEnd ℂ) (w : ℂ))

@[simp]
theorem deningerPrimeGammaSourceKernel_of_ne
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint)
    (hzw : (z : ℂ) ≠ (starRingEnd ℂ) (w : ℂ)) :
    deningerPrimeGammaSourceKernel z w =
      (primeArchSourceRelativeTrace ((starRingEnd ℂ) (w : ℂ)) -
        primeArchSourceRelativeTrace (z : ℂ)) /
          ((z : ℂ) - (starRingEnd ℂ) (w : ℂ)) := by
  simp [deningerPrimeGammaSourceKernel, hzw]

@[simp]
theorem deningerPrimeGammaSourceKernel_reflectedDiagonal
    (z : DeningerPrimeGammaLowerPoint) :
    deningerPrimeGammaSourceKernel z (deningerPrimeGammaPointConjEquiv z) =
      -deriv primeArchSourceRelativeTrace (z : ℂ) := by
  simp [deningerPrimeGammaSourceKernel, deningerPrimeGammaPointConjEquiv]

/--
On the Euler half-plane the source trace and the target relative trace have the same derivative.
This follows from their already proved equality on an open neighborhood, not from differentiating
an equality at one point.
-/
theorem deriv_primeArchSourceRelativeTrace_eq_deriv_xiRelativeResolventTrace
    (z : DeningerPrimeGammaLowerPoint) :
    deriv primeArchSourceRelativeTrace (z : ℂ) =
      deriv xiRelativeResolventTrace (z : ℂ) := by
  let U : Set ℂ := {u | 1 < (1 / 2 + u * Complex.I).re}
  have hUopen : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hzU : (z : ℂ) ∈ U := z.property
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hUopen.mem_nhds hzU] with u hu
  exact primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hu

/-- The reflected-diagonal source kernel is the negative derivative of the Xi log derivative. -/
theorem deningerPrimeGammaSourceKernel_reflectedDiagonal_eq_logDeriv
    (z : DeningerPrimeGammaLowerPoint) :
    deningerPrimeGammaSourceKernel z (deningerPrimeGammaPointConjEquiv z) =
      -deriv (logDeriv XiC) (z : ℂ) := by
  rw [deningerPrimeGammaSourceKernel_reflectedDiagonal,
    deriv_primeArchSourceRelativeTrace_eq_deriv_xiRelativeResolventTrace]
  congr 1
  let U : Set ℂ := {u | 1 < (1 / 2 + u * Complex.I).re}
  have hUopen : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hzU : (z : ℂ) ∈ U := z.property
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hUopen.mem_nhds hzU] with u hu
  exact (logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_of_one_lt_centered_re hu)).symm

/-- For a lower atom, source cup product against an upper packet is a linear functional. -/
def deningerPrimeGammaSourceKernelLinear
    (z : DeningerPrimeGammaLowerPoint) :
    DeningerPrimeGammaUpperPacket →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun w =>
    LinearMap.toSpanSingleton ℂ ℂ (deningerPrimeGammaSourceKernel z w)

/-- Bilinear source cup product on free finite prime--Gamma packets. -/
def deningerPrimeGammaSourceCup :
    DeningerPrimeGammaLowerPacket →ₗ[ℂ]
      DeningerPrimeGammaUpperPacket →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun z =>
    LinearMap.toSpanSingleton ℂ
      (DeningerPrimeGammaUpperPacket →ₗ[ℂ] ℂ)
      (deningerPrimeGammaSourceKernelLinear z)

@[simp]
theorem deningerPrimeGammaSourceKernelLinear_single
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint) (d : ℂ) :
    deningerPrimeGammaSourceKernelLinear z (Finsupp.single w d) =
      d * deningerPrimeGammaSourceKernel z w := by
  simp [deningerPrimeGammaSourceKernelLinear, smul_eq_mul]

@[simp]
theorem deningerPrimeGammaSourceCup_single
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint) (c d : ℂ) :
    deningerPrimeGammaSourceCup (Finsupp.single z c) (Finsupp.single w d) =
      c * d * deningerPrimeGammaSourceKernel z w := by
  simp [deningerPrimeGammaSourceCup, smul_eq_mul]
  ring

/--
Off the reflected diagonal, each source atom is exactly the corresponding divisor-side Weil
polarization.  This theorem is a comparison result; the left-hand side is source-defined.
-/
theorem deningerPrimeGammaSourceKernel_eq_xiWeilPolarization_of_ne
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint)
    (hzw : (z : ℂ) ≠ (starRingEnd ℂ) (w : ℂ)) :
    deningerPrimeGammaSourceKernel z w =
      xiWeilPolarization
        (xiWeilCauchyTest (z : ℂ))
        (xiWeilCauchyTest (w : ℂ)) := by
  rw [deningerPrimeGammaSourceKernel_of_ne z w hzw]
  exact (xiWeilPolarization_cauchy_eq_primeArchSource_dividedDifference
    z.property w.property hzw).symm

/-- Left radical of the source cup product. -/
def deningerPrimeGammaLeftRadical :
    Submodule ℂ DeningerPrimeGammaLowerPacket :=
  LinearMap.ker deningerPrimeGammaSourceCup

/-- Right radical of the source cup product. -/
def deningerPrimeGammaRightRadical :
    Submodule ℂ DeningerPrimeGammaUpperPacket where
  carrier := {y | ∀ x, deningerPrimeGammaSourceCup x y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y₁ y₂ hy₁ hy₂ x
    rw [map_add, hy₁ x, hy₂ x, add_zero]
  smul_mem' := by
    intro a y hy x
    rw [map_smul, hy x, smul_zero]

theorem mem_deningerPrimeGammaLeftRadical_iff
    (x : DeningerPrimeGammaLowerPacket) :
    x ∈ deningerPrimeGammaLeftRadical ↔
      ∀ y, deningerPrimeGammaSourceCup x y = 0 := by
  rw [deningerPrimeGammaLeftRadical, LinearMap.mem_ker]
  constructor
  · intro hx y
    rw [hx]
    rfl
  · intro hx
    apply LinearMap.ext
    intro y
    exact hx y

theorem mem_deningerPrimeGammaRightRadical_iff
    (y : DeningerPrimeGammaUpperPacket) :
    y ∈ deningerPrimeGammaRightRadical ↔
      ∀ x, deningerPrimeGammaSourceCup x y = 0 :=
  Iff.rfl

/-- Lower degree-one source sector after quotienting by its exact cup radical. -/
abbrev DeningerPrimeGammaH1Minus :=
  DeningerPrimeGammaLowerPacket ⧸ deningerPrimeGammaLeftRadical

/-- Upper degree-one source sector after quotienting by its exact cup radical. -/
abbrev DeningerPrimeGammaH1Plus :=
  DeningerPrimeGammaUpperPacket ⧸ deningerPrimeGammaRightRadical

/-- Canonical lower packet class in source degree one. -/
def deningerPrimeGammaH1MinusClass :
    DeningerPrimeGammaLowerPacket →ₗ[ℂ] DeningerPrimeGammaH1Minus :=
  deningerPrimeGammaLeftRadical.mkQ

/-- Canonical upper packet class in source degree one. -/
def deningerPrimeGammaH1PlusClass :
    DeningerPrimeGammaUpperPacket →ₗ[ℂ] DeningerPrimeGammaH1Plus :=
  deningerPrimeGammaRightRadical.mkQ

theorem deningerPrimeGammaH1MinusClass_eq_zero_iff
    (x : DeningerPrimeGammaLowerPacket) :
    deningerPrimeGammaH1MinusClass x = 0 ↔
      ∀ y, deningerPrimeGammaSourceCup x y = 0 := by
  rw [deningerPrimeGammaH1MinusClass, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, mem_deningerPrimeGammaLeftRadical_iff]

theorem deningerPrimeGammaH1PlusClass_eq_zero_iff
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaH1PlusClass y = 0 ↔
      ∀ x, deningerPrimeGammaSourceCup x y = 0 := by
  rw [deningerPrimeGammaH1PlusClass, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, mem_deningerPrimeGammaRightRadical_iff]

/--
The lower quotient has no residual left radical: every nonzero represented class is detected by
an upper source packet.
-/
theorem exists_sourceCup_ne_zero_of_h1MinusClass_ne_zero
    {x : DeningerPrimeGammaLowerPacket}
    (hx : deningerPrimeGammaH1MinusClass x ≠ 0) :
    ∃ y, deningerPrimeGammaSourceCup x y ≠ 0 := by
  contrapose! hx
  exact (deningerPrimeGammaH1MinusClass_eq_zero_iff x).2 hx

/--
The upper quotient has no residual right radical: every nonzero represented class is detected by
a lower source packet.
-/
theorem exists_sourceCup_ne_zero_of_h1PlusClass_ne_zero
    {y : DeningerPrimeGammaUpperPacket}
    (hy : deningerPrimeGammaH1PlusClass y ≠ 0) :
    ∃ x, deningerPrimeGammaSourceCup x y ≠ 0 := by
  contrapose! hy
  exact (deningerPrimeGammaH1PlusClass_eq_zero_iff y).2 hy

end

end RHTower
