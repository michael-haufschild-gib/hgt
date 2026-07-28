import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Shape derivatives recover a symmetric carrier's chiral factor

For any nonvanishing differentiable carrier `f`, form its symmetric intensity and pole-oriented
chiral quotient

`M(a,s) = f(a + λs) f(a - λs)` and
`P(a,s) = f(a + λs) / f(a - λs)`.

Their logarithmic derivatives obey the branch-free cross laws

`LD_s P = λ LD_a M` and `LD_s M = λ LD_a P`.

Thus a full shape family of symmetric intensities contains phase information which one fixed
intensity does not. Multiplying the intensity by a shape-dependent normalization changes the
reconstructed phase derivative only by a spectral constant, hence by an exponential gauge after
integration. The final two theorems specialize the general law to Euler's Gamma function away from
its poles.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- Symmetric intensity built from the two affine orientations of one carrier. -/
def symmetricShapeCarrier (f : ℂ → ℂ) (lam a s : ℂ) : ℂ :=
  f (a + lam * s) * f (a - lam * s)

/-- Pole-oriented chiral quotient of the same two affine carrier orientations. -/
def chiralShapeCarrier (f : ℂ → ℂ) (lam a s : ℂ) : ℂ :=
  f (a + lam * s) / f (a - lam * s)

/-- A shape-dependent scalar normalization of the symmetric intensity. -/
def normalizedSymmetricShapeCarrier
    (f c : ℂ → ℂ) (lam a s : ℂ) : ℂ :=
  c a * symmetricShapeCarrier f lam a s

/-- Exact plaquette law behind the differential cross system.  A symmetric spectral displacement
is the same cross-ratio as the corresponding chiral shape displacement.  Unlike the logarithmic
derivative laws below, this identity is finite and uses no choice of logarithm. -/
theorem symmetricSpectralShift_ratio_eq_chiralShapeShift_ratio
    (f : ℂ → ℂ) (lam a s h : ℂ)
    (hpp : f (a + lam * (s + h)) ≠ 0)
    (hmp : f (a - lam * (s + h)) ≠ 0) :
    symmetricShapeCarrier f lam a (s - h) /
        symmetricShapeCarrier f lam a (s + h) =
      chiralShapeCarrier f lam (a - lam * h) s /
        chiralShapeCarrier f lam (a + lam * h) s := by
  unfold symmetricShapeCarrier chiralShapeCarrier
  rw [div_div_div_eq]
  have hden :
      f (a - lam * h - lam * s) * f (a + lam * h + lam * s) ≠ 0 :=
    mul_ne_zero
      (by convert hmp using 1 <;> ring_nf)
      (by convert hpp using 1 <;> ring_nf)
  exact (div_eq_div_iff (mul_ne_zero hpp hmp) hden).2 (by ring)

/-- Spectral logarithmic derivative of the chiral quotient equals the shape logarithmic derivative
of the symmetric intensity, scaled by the affine slope. This is branch-free phase recovery. -/
theorem chiralSpectral_logDeriv_eq_scale_mul_symmetricShape_logDeriv
    (f : ℂ → ℂ) (lam a s : ℂ)
    (hfp : DifferentiableAt ℂ f (a + lam * s))
    (hfm : DifferentiableAt ℂ f (a - lam * s))
    (hfp0 : f (a + lam * s) ≠ 0)
    (hfm0 : f (a - lam * s) ≠ 0) :
    logDeriv (fun z => chiralShapeCarrier f lam a z) s =
      lam * logDeriv (fun b => symmetricShapeCarrier f lam b s) a := by
  have hsp : DifferentiableAt ℂ (fun z => f (a + lam * z)) s := by fun_prop
  have hsm : DifferentiableAt ℂ (fun z => f (a - lam * z)) s := by fun_prop
  have hap : DifferentiableAt ℂ (fun b => f (b + lam * s)) a := by fun_prop
  have ham : DifferentiableAt ℂ (fun b => f (b - lam * s)) a := by fun_prop
  unfold chiralShapeCarrier symmetricShapeCarrier
  rw [logDeriv_div s hfp0 hfm0 hsp hsm,
    logDeriv_mul a hfp0 hfm0 hap ham]
  have hsp' :
      logDeriv (fun z => f (a + lam * z)) s =
        logDeriv f (a + lam * s) * lam := by
    have hinner : HasDerivAt (fun z : ℂ => a + lam * z) lam s := by
      simpa only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, mul_one] using
        (hasDerivAt_const s a).add ((hasDerivAt_id s).const_mul lam)
    have hcomp := logDeriv_comp (f := f) (g := fun z : ℂ => a + lam * z) (x := s)
      hfp hinner.differentiableAt
    rw [hinner.deriv] at hcomp
    simpa only [Function.comp_apply] using hcomp
  have hsm' :
      logDeriv (fun z => f (a - lam * z)) s =
        logDeriv f (a - lam * s) * (-lam) := by
    have hinner : HasDerivAt (fun z : ℂ => a - lam * z) (-lam) s := by
      simpa only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_sub, mul_one] using
        (hasDerivAt_const s a).sub ((hasDerivAt_id s).const_mul lam)
    have hcomp := logDeriv_comp (f := f) (g := fun z : ℂ => a - lam * z) (x := s)
      hfm hinner.differentiableAt
    rw [hinner.deriv] at hcomp
    simpa only [Function.comp_apply] using hcomp
  have hap' :
      logDeriv (fun b => f (b + lam * s)) a =
        logDeriv f (a + lam * s) := by
    have hinner : HasDerivAt (fun b : ℂ => b + lam * s) 1 a :=
      (hasDerivAt_id a).add_const (lam * s)
    have hcomp := logDeriv_comp (f := f) (g := fun b : ℂ => b + lam * s) (x := a)
      hfp hinner.differentiableAt
    rw [hinner.deriv, mul_one] at hcomp
    simpa only [Function.comp_apply] using hcomp
  have ham' :
      logDeriv (fun b => f (b - lam * s)) a =
        logDeriv f (a - lam * s) := by
    have hinner : HasDerivAt (fun b : ℂ => b - lam * s) 1 a :=
      (hasDerivAt_id a).sub_const (lam * s)
    have hcomp := logDeriv_comp (f := f) (g := fun b : ℂ => b - lam * s) (x := a)
      hfm hinner.differentiableAt
    rw [hinner.deriv, mul_one] at hcomp
    simpa only [Function.comp_apply] using hcomp
  rw [hsp', hsm', hap', ham']
  ring

/-- Reciprocal cross law: spectral variation of the symmetric intensity is the scaled shape
variation of the chiral quotient. -/
theorem symmetricSpectral_logDeriv_eq_scale_mul_chiralShape_logDeriv
    (f : ℂ → ℂ) (lam a s : ℂ)
    (hfp : DifferentiableAt ℂ f (a + lam * s))
    (hfm : DifferentiableAt ℂ f (a - lam * s))
    (hfp0 : f (a + lam * s) ≠ 0)
    (hfm0 : f (a - lam * s) ≠ 0) :
    logDeriv (fun z => symmetricShapeCarrier f lam a z) s =
      lam * logDeriv (fun b => chiralShapeCarrier f lam b s) a := by
  have hsp : DifferentiableAt ℂ (fun z => f (a + lam * z)) s := by fun_prop
  have hsm : DifferentiableAt ℂ (fun z => f (a - lam * z)) s := by fun_prop
  have hap : DifferentiableAt ℂ (fun b => f (b + lam * s)) a := by fun_prop
  have ham : DifferentiableAt ℂ (fun b => f (b - lam * s)) a := by fun_prop
  unfold symmetricShapeCarrier chiralShapeCarrier
  rw [logDeriv_mul s hfp0 hfm0 hsp hsm,
    logDeriv_div a hfp0 hfm0 hap ham]
  have hsp' :
      logDeriv (fun z => f (a + lam * z)) s =
        logDeriv f (a + lam * s) * lam := by
    have hinner : HasDerivAt (fun z : ℂ => a + lam * z) lam s := by
      simpa only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, mul_one] using
        (hasDerivAt_const s a).add ((hasDerivAt_id s).const_mul lam)
    have hcomp := logDeriv_comp (f := f) (g := fun z : ℂ => a + lam * z) (x := s)
      hfp hinner.differentiableAt
    rw [hinner.deriv] at hcomp
    simpa only [Function.comp_apply] using hcomp
  have hsm' :
      logDeriv (fun z => f (a - lam * z)) s =
        logDeriv f (a - lam * s) * (-lam) := by
    have hinner : HasDerivAt (fun z : ℂ => a - lam * z) (-lam) s := by
      simpa only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_sub, mul_one] using
        (hasDerivAt_const s a).sub ((hasDerivAt_id s).const_mul lam)
    have hcomp := logDeriv_comp (f := f) (g := fun z : ℂ => a - lam * z) (x := s)
      hfm hinner.differentiableAt
    rw [hinner.deriv] at hcomp
    simpa only [Function.comp_apply] using hcomp
  have hap' :
      logDeriv (fun b => f (b + lam * s)) a =
        logDeriv f (a + lam * s) := by
    have hinner : HasDerivAt (fun b : ℂ => b + lam * s) 1 a :=
      (hasDerivAt_id a).add_const (lam * s)
    have hcomp := logDeriv_comp (f := f) (g := fun b : ℂ => b + lam * s) (x := a)
      hfp hinner.differentiableAt
    rw [hinner.deriv, mul_one] at hcomp
    simpa only [Function.comp_apply] using hcomp
  have ham' :
      logDeriv (fun b => f (b - lam * s)) a =
        logDeriv f (a - lam * s) := by
    have hinner : HasDerivAt (fun b : ℂ => b - lam * s) 1 a :=
      (hasDerivAt_id a).sub_const (lam * s)
    have hcomp := logDeriv_comp (f := f) (g := fun b : ℂ => b - lam * s) (x := a)
      hfm hinner.differentiableAt
    rw [hinner.deriv, mul_one] at hcomp
    simpa only [Function.comp_apply] using hcomp
  rw [hsp', hsm', hap', ham']
  ring

/-- A scalar normalization depending only on shape changes phase recovery by the constant
`λ * LD c(a)`. After spectral integration this is exactly a linear exponential gauge. -/
theorem normalizedSymmetricShape_logDeriv_reconstructs_chiral
    (f c : ℂ → ℂ) (lam a s : ℂ)
    (hfp : DifferentiableAt ℂ f (a + lam * s))
    (hfm : DifferentiableAt ℂ f (a - lam * s))
    (hfp0 : f (a + lam * s) ≠ 0)
    (hfm0 : f (a - lam * s) ≠ 0)
    (hc : DifferentiableAt ℂ c a) (hc0 : c a ≠ 0) :
    lam * logDeriv (fun b => normalizedSymmetricShapeCarrier f c lam b s) a =
      logDeriv (fun z => chiralShapeCarrier f lam a z) s +
        lam * logDeriv c a := by
  have hMdiff :
      DifferentiableAt ℂ (fun b => symmetricShapeCarrier f lam b s) a := by
    unfold symmetricShapeCarrier
    fun_prop
  have hM0 : symmetricShapeCarrier f lam a s ≠ 0 :=
    mul_ne_zero hfp0 hfm0
  unfold normalizedSymmetricShapeCarrier
  rw [logDeriv_mul a hc0 hM0 hc hMdiff,
    chiralSpectral_logDeriv_eq_scale_mul_symmetricShape_logDeriv
      f lam a s hfp hfm hfp0 hfm0]
  ring

/-- Gamma specialization of branch-free phase recovery, valid away from the two pole lattices. -/
theorem gammaChiralSpectral_logDeriv_eq_scale_mul_symmetricShape_logDeriv
    (lam a s : ℂ)
    (hp : ∀ m : ℕ, a + lam * s ≠ -m)
    (hm : ∀ m : ℕ, a - lam * s ≠ -m) :
    logDeriv (fun z => chiralShapeCarrier Complex.Gamma lam a z) s =
      lam *
        logDeriv (fun b => symmetricShapeCarrier Complex.Gamma lam b s) a :=
  chiralSpectral_logDeriv_eq_scale_mul_symmetricShape_logDeriv
    Complex.Gamma lam a s
      (Complex.differentiableAt_Gamma _ hp)
      (Complex.differentiableAt_Gamma _ hm)
      (Complex.Gamma_ne_zero hp)
      (Complex.Gamma_ne_zero hm)

/-- Gamma specialization of the reciprocal intensity/phase cross law. -/
theorem gammaSymmetricSpectral_logDeriv_eq_scale_mul_chiralShape_logDeriv
    (lam a s : ℂ)
    (hp : ∀ m : ℕ, a + lam * s ≠ -m)
    (hm : ∀ m : ℕ, a - lam * s ≠ -m) :
    logDeriv (fun z => symmetricShapeCarrier Complex.Gamma lam a z) s =
      lam *
        logDeriv (fun b => chiralShapeCarrier Complex.Gamma lam b s) a :=
  symmetricSpectral_logDeriv_eq_scale_mul_chiralShape_logDeriv
    Complex.Gamma lam a s
      (Complex.differentiableAt_Gamma _ hp)
      (Complex.differentiableAt_Gamma _ hm)
      (Complex.Gamma_ne_zero hp)
      (Complex.Gamma_ne_zero hm)

end GaloisForLFunctions.HTGeometry
