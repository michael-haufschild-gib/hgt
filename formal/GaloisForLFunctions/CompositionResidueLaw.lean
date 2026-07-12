import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.GammaShiftCasoratian

/-!
# Residues transported by a noncritical value map

A simple-pole residue is divided by the derivative under composition with a locally
biholomorphic inner function.  For the poles of `digamma ∘ Gamma`, this gives the exact residue
`-1 / Gamma'(z₀)` at every point satisfying `Gamma z₀ = -m` with nonzero derivative.

The second pair of theorems records the companion value law for an analytic position curve
`z(x)` satisfying `g(z(x)) = -1/x`: its derivative obeys `d·z'(x)=x⁻²`, so `-1/d`, the
interpolation sampled by the transported digamma residues, is `-x²z'(x)`.
-/

open Complex Filter Topology Polynomial

namespace GaloisForLFunctions

/-- **Simple-pole residue pullback.**  If `f` has residue `R` at `g z₀` and `g` has nonzero
derivative `d` at `z₀`, then `f ∘ g` has residue `R / d` at `z₀`.  The punctured-neighborhood
mapping needed to compose the residue limit follows from the nonzero derivative. -/
theorem residue_comp_of_hasDerivAt
    {f g : ℂ → ℂ} {z₀ R d : ℂ}
    (hf : Tendsto (fun w : ℂ => (w - g z₀) * f w)
      (nhdsWithin (g z₀) {g z₀}ᶜ) (nhds R))
    (hg : HasDerivAt g d z₀) (hd : d ≠ 0) :
    Tendsto (fun z : ℂ => (z - z₀) * f (g z))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (R / d)) := by
  have hnum : Tendsto (fun z : ℂ => (g z - g z₀) * f (g z))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds R) := hf.comp (hg.tendsto_nhdsNE hd)
  have hquot := hnum.div hg.tendsto_slope hd
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hg.eventually_ne (c := g z₀) hd] with z hz hgz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  simp only [Pi.div_apply]
  rw [slope_def_field]
  have hdiff : g z - g z₀ ≠ 0 := sub_ne_zero.mpr hgz
  field_simp [hdiff]

/-- **Exact residue of `digamma ∘ Gamma` at an inverse-Gamma pole.**  If `Gamma z₀ = -m`
and `Gamma'(z₀)=d≠0`, then the composite has residue `-1/d` at `z₀`. -/
theorem digamma_comp_Gamma_residue (m : ℕ) {z₀ d : ℂ}
    (hGamma : Complex.Gamma z₀ = -(m : ℂ))
    (hGamma' : HasDerivAt Complex.Gamma d z₀) (hd : d ≠ 0) :
    Tendsto (fun z : ℂ => (z - z₀) * Complex.digamma (Complex.Gamma z))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (-1 / d)) := by
  have hpsi := digamma_residue m
  have hpsi' : Tendsto
      (fun w : ℂ => (w - Complex.Gamma z₀) * Complex.digamma w)
      (nhdsWithin (Complex.Gamma z₀) {Complex.Gamma z₀}ᶜ) (nhds (-1)) := by
    simpa [hGamma] using hpsi
  exact residue_comp_of_hasDerivAt hpsi' hGamma' hd

/-- **Principal-part pullback at arbitrary pole order.**  If `f` has leading coefficient `R`
at pole order `P` at `g z₀`, and `g'(z₀)=d≠0`, then the leading coefficient of `f ∘ g` is
`R / d^P`. -/
theorem principalPart_comp_of_hasDerivAt
    {f g : ℂ → ℂ} {z₀ R d : ℂ} (P : ℕ)
    (hf : Tendsto (fun w : ℂ => (w - g z₀) ^ P * f w)
      (nhdsWithin (g z₀) {g z₀}ᶜ) (nhds R))
    (hg : HasDerivAt g d z₀) (hd : d ≠ 0) :
    Tendsto (fun z : ℂ => (z - z₀) ^ P * f (g z))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (R / d ^ P)) := by
  have hnum : Tendsto (fun z : ℂ => (g z - g z₀) ^ P * f (g z))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds R) := hf.comp (hg.tendsto_nhdsNE hd)
  have hquot := hnum.div (hg.tendsto_slope.pow P) (pow_ne_zero P hd)
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hg.eventually_ne (c := g z₀) hd] with z hz hgz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  simp only [Pi.div_apply]
  rw [slope_def_field]
  have hdiff : g z - g z₀ ≠ 0 := sub_ne_zero.mpr hgz
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [div_pow]
  field_simp [hdiff, hzsub]

/-- **All-order polygamma-of-Gamma principal-part power law.**  At a noncritical inverse-Gamma
value `Gamma z₀ = -m`, the order-`q` polygamma composite has pole order `q+1` and leading
coefficient

`q! * (-1 / Gamma'(z₀))^(q+1)`.

Thus every leading principal part in the outer differential tower is a factorial power of the
single digamma-composite residue. -/
theorem polygamma_comp_Gamma_principalPart (q m : ℕ) {z₀ d : ℂ}
    (hGamma : Complex.Gamma z₀ = -(m : ℂ))
    (hGamma' : HasDerivAt Complex.Gamma d z₀) (hd : d ≠ 0) :
    Tendsto
      (fun z : ℂ =>
        (z - z₀) ^ (q + 1) * iteratedDeriv q Complex.digamma (Complex.Gamma z))
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds ((q.factorial : ℂ) * (-1 / d) ^ (q + 1))) := by
  have hpsi := digamma_iteratedDeriv_residue q m
  have hpsi' : Tendsto
      (fun w : ℂ =>
        (w - Complex.Gamma z₀) ^ (q + 1) * iteratedDeriv q Complex.digamma w)
      (nhdsWithin (Complex.Gamma z₀) {Complex.Gamma z₀}ᶜ)
      (nhds ((-1) ^ (q + 1) * (q.factorial : ℂ))) := by
    simpa [hGamma] using hpsi
  have hpull := principalPart_comp_of_hasDerivAt (q + 1) hpsi' hGamma' hd
  convert hpull using 1
  ring_nf

/-- **Velocity of a reciprocal-value position curve.**  If `g(z(x)) = -1/x` near a nonzero
`x`, with derivatives `g'(z(x))=d` and `z'(x)=dz`, then `d·dz=x⁻²`. -/
theorem reciprocalPosition_velocity
    {g z : ℂ → ℂ} {x dz d : ℂ} (hx : x ≠ 0)
    (hposition : (fun y : ℂ => g (z y)) =ᶠ[nhds x] (fun y : ℂ => -y⁻¹))
    (hz : HasDerivAt z dz x) (hg : HasDerivAt g d (z x)) :
    d * dz = (x ^ 2)⁻¹ := by
  have hcomp : HasDerivAt (fun y : ℂ => g (z y)) (d * dz) x := hg.comp x hz
  have hcomp' : HasDerivAt (fun y : ℂ => -y⁻¹) (d * dz) x :=
    hposition.hasDerivAt_iff.mp hcomp
  have hinv : HasDerivAt (fun y : ℂ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    convert ((hasDerivAt_id x).inv hx).neg using 1
    simp [id]
    field_simp [hx]
  exact hcomp'.unique hinv

/-- **Position-residue interpolation law.**  Along a reciprocal-value position curve, the
analytic interpolation `-1/d` of the transported residue is exactly `-x² z'(x)`.  At
`x=1/m`, `digamma_comp_Gamma_residue` identifies this interpolation with the actual residue of
`digamma ∘ Gamma`. -/
theorem reciprocalPosition_residueInterpolation
    {g z : ℂ → ℂ} {x dz d : ℂ} (hx : x ≠ 0) (hd : d ≠ 0)
    (hposition : (fun y : ℂ => g (z y)) =ᶠ[nhds x] (fun y : ℂ => -y⁻¹))
    (hz : HasDerivAt z dz x) (hg : HasDerivAt g d (z x)) :
    -1 / d = -(x ^ 2) * dz := by
  have hv := reciprocalPosition_velocity hx hposition hz hg
  field_simp [hx] at hv
  have hinvd : 1 / d = x ^ 2 * dz := by
    apply (div_eq_iff hd).2
    calc
      1 = d * dz * x ^ 2 := hv.symm
      _ = x ^ 2 * dz * d := by ring
  calc
    -1 / d = -(1 / d) := by ring
    _ = -(x ^ 2 * dz) := congrArg Neg.neg hinvd
    _ = -(x ^ 2) * dz := by ring

/-- At a reciprocal Gamma value, the scaled Gamma derivative is exactly the digamma value.  This
identifies the additive coordinate used below with a classical special-function value. -/
theorem gamma_inverseValue_logSlope_eq_digamma
    {z x : ℂ} (hx : x ≠ 0) (hvalue : Complex.Gamma z = -1 / x) :
    -x * deriv Complex.Gamma z = Complex.digamma z := by
  rw [Complex.digamma_def, logDeriv_apply, hvalue]
  field_simp [hx]

/-- **Additive inverse-Gamma log-slope cocycle.**  At a reciprocal Gamma value
`Gamma z = -1/x`, the Gamma shift transports the scaled derivative by

`-(x/z) * Gamma'(z+1) = -x * Gamma'(z) + 1/z`.

When the inverse-value residues are nonzero, `-x * Gamma'(z)` is `x/rho`; hence this identity
linearizes the fractional residue transport into an additive increment `1/z`. -/
theorem gamma_inverseValue_logSlope_add_one
    {z x : ℂ} (hx : x ≠ 0)
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hvalue : Complex.Gamma z = -1 / x) :
    -(x / z) * deriv Complex.Gamma (z + 1) =
      -x * deriv Complex.Gamma z + 1 / z := by
  have hz0 : z ≠ 0 := by
    simpa using hz 0
  have hrec := iteratedDeriv_Gamma_add_one 1 z hz
  norm_num [iteratedDeriv_one] at hrec
  rw [hrec, hvalue]
  field_simp [hx, hz0]
  ring

/-- The ascending-factorial transport multiplier is nonzero at every point off the Gamma pole
lattice. -/
private theorem ascPochhammer_eval_ne_zero_of_off_poles (k : ℕ) {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    (ascPochhammer ℂ k).eval z ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [ascPochhammer_succ_eval]
      exact mul_ne_zero ih (by
        intro h0
        apply hz k
        linear_combination h0)

/-- **Logarithmic derivative of the finite Gamma-shift multiplier.**  Away from its roots,

`(z)_k' = (z)_k · Σ_{j<k} 1/(z+j)`.

This identifies the harmonic increment in the finite inverse-Gamma cocycle with the derivative of
the ascending-factorial value that transports the Gamma branch. -/
theorem ascPochhammer_derivative_eval_eq_mul_sum (k : ℕ) {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    (ascPochhammer ℂ k).derivative.eval z =
      (ascPochhammer ℂ k).eval z *
        ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hzk0 : z + (k : ℂ) ≠ 0 := by
        intro h0
        apply hz k
        linear_combination h0
      rw [ascPochhammer_succ_right, derivative_mul]
      simp only [derivative_add, derivative_X, derivative_natCast, add_zero,
        eval_add, eval_mul, eval_X, eval_natCast, mul_one]
      rw [Finset.sum_range_succ, ih]
      field_simp [hzk0]

/-- **Finite inverse-Gamma log-slope cocycle.**  Iterating the one-step value law through the
ascending-factorial multiplier gives

`-(x/(z)_k) Γ'(z+k) = -x Γ'(z) + Σ_{j<k} 1/(z+j)`

whenever `Γ(z)=-1/x`.  This is the pointwise finite-shift core of the inverse-branch cocycle: it
does not require the local inverse branches themselves to have been selected. -/
theorem gamma_inverseValue_logSlope_add_nat (k : ℕ) {z x : ℂ} (hx : x ≠ 0)
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hvalue : Complex.Gamma z = -1 / x) :
    -(x / (ascPochhammer ℂ k).eval z) * deriv Complex.Gamma (z + k) =
      -x * deriv Complex.Gamma z +
        ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hzk0 : z + (k : ℂ) ≠ 0 := by
        intro h0
        apply hz k
        linear_combination h0
      have hPne : (ascPochhammer ℂ k).eval z ≠ 0 :=
        ascPochhammer_eval_ne_zero_of_off_poles k hz
      have hxk : x / (ascPochhammer ℂ k).eval z ≠ 0 := div_ne_zero hx hPne
      have hzshift : ∀ m : ℕ, z + (k : ℂ) ≠ -(m : ℂ) := by
        intro m hm
        apply hz (m + k)
        push_cast
        linear_combination hm
      have hGammaShift := Complex.Gamma_add_nat_eq_ascPochhammer_mul z k (by
        intro j hj hzero
        apply hz j
        linear_combination hzero)
      have hvalueShift : Complex.Gamma (z + (k : ℂ)) =
          -1 / (x / (ascPochhammer ℂ k).eval z) := by
        rw [hGammaShift, hvalue]
        field_simp [hx, hPne]
      have hstep := gamma_inverseValue_logSlope_add_one hxk hzshift hvalueShift
      rw [show z + (↑(k + 1) : ℂ) = (z + (k : ℂ)) + 1 by push_cast; ring,
        ascPochhammer_succ_eval, Finset.sum_range_succ]
      have hquot : (x / (ascPochhammer ℂ k).eval z) / (z + (k : ℂ)) =
          x / ((ascPochhammer ℂ k).eval z * (z + (k : ℂ))) := by
        field_simp [hPne, hzk0]
      rw [hquot] at hstep
      rw [hstep, ih]
      ring

/-- **Additive reciprocal-residue coordinate.**  If `rho = -1/Gamma'(z)` at the reciprocal value
`Gamma z = -1/x`, then the scaled reciprocal residue transforms by translation:

`(x/z) / (-1/Gamma'(z+1)) = x/rho + 1/z`.

The identity is totalized correctly even at a critical shifted value; at noncritical inverse
values it is exactly the additive form of the residue Möbius cocycle. -/
theorem gamma_inverseValue_reciprocalResidue_add_one
    {z x rho : ℂ} (hx : x ≠ 0)
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hvalue : Complex.Gamma z = -1 / x)
    (hrho : rho = -1 / deriv Complex.Gamma z) :
    (x / z) / (-1 / deriv Complex.Gamma (z + 1)) =
      x / rho + 1 / z := by
  have hlog := gamma_inverseValue_logSlope_add_one hx hz hvalue
  calc
    (x / z) / (-1 / deriv Complex.Gamma (z + 1)) =
        -(x / z) * deriv Complex.Gamma (z + 1) := by field_simp
    _ = -x * deriv Complex.Gamma z + 1 / z := hlog
    _ = x / (-1 / deriv Complex.Gamma z) + 1 / z := by field_simp
    _ = x / rho + 1 / z := by rw [hrho]

/-- **Finite additive reciprocal-residue cocycle.**  The finite log-slope law written in the
scaled reciprocal-residue coordinate is

`(x/(z)_k)/(-1/Γ'(z+k)) = x/rho + Σ_{j<k} 1/(z+j)`.

At noncritical inverse values this is precisely the finite branch-residue transport law in its
linearized coordinate. -/
theorem gamma_inverseValue_reciprocalResidue_add_nat (k : ℕ)
    {z x rho : ℂ} (hx : x ≠ 0)
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hvalue : Complex.Gamma z = -1 / x)
    (hrho : rho = -1 / deriv Complex.Gamma z) :
    (x / (ascPochhammer ℂ k).eval z) /
        (-1 / deriv Complex.Gamma (z + k)) =
      x / rho + ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ)) := by
  have hlog := gamma_inverseValue_logSlope_add_nat k hx hz hvalue
  calc
    (x / (ascPochhammer ℂ k).eval z) /
        (-1 / deriv Complex.Gamma (z + k)) =
        -(x / (ascPochhammer ℂ k).eval z) *
          deriv Complex.Gamma (z + k) := by field_simp
    _ = -x * deriv Complex.Gamma z +
        ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ)) := hlog
    _ = x / (-1 / deriv Complex.Gamma z) +
        ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ)) := by field_simp
    _ = x / rho + ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ)) := by rw [hrho]

/-- **Finite inverse-Gamma residue Möbius cocycle.**  If both endpoint inverse values are
noncritical, the finite shift transports the reciprocal derivative by

`-1/Γ'(z+k) = x rho / (x (z)_k + rho (z)_k')`.

Together with `ascPochhammer_derivative_eval_eq_mul_sum`, this is the finite rising-factorial form
of the one-step fractional-linear residue law. -/
theorem gamma_inverseValue_residueTransport_add_nat (k : ℕ)
    {z x rho : ℂ} (hx : x ≠ 0)
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hvalue : Complex.Gamma z = -1 / x)
    (hrho : rho = -1 / deriv Complex.Gamma z)
    (hd : deriv Complex.Gamma z ≠ 0)
    (hdk : deriv Complex.Gamma (z + k) ≠ 0) :
    -1 / deriv Complex.Gamma (z + k) =
      x * rho /
        (x * (ascPochhammer ℂ k).eval z +
          rho * (ascPochhammer ℂ k).derivative.eval z) := by
  have hlog := gamma_inverseValue_logSlope_add_nat k hx hz hvalue
  have hder := ascPochhammer_derivative_eval_eq_mul_sum k hz
  have hPne := ascPochhammer_eval_ne_zero_of_off_poles k hz
  rw [hrho, hder]
  have hdeneq : x * (ascPochhammer ℂ k).eval z +
      (-1 / deriv Complex.Gamma z) *
        ((ascPochhammer ℂ k).eval z *
          ∑ j ∈ Finset.range k, 1 / (z + (j : ℂ))) =
      x * deriv Complex.Gamma (z + k) / deriv Complex.Gamma z := by
    field_simp [hd]
    field_simp [hPne] at hlog
    linear_combination hlog
  rw [hdeneq]
  field_simp [hx, hd, hdk]

/-- **One-step inverse-Gamma residue transport.**  At an inverse value
`Gamma z = -1/x`, write `rho = -1/Gamma'(z)`.  The differentiated Gamma recurrence transports
the interpolated residue at `z` to the shifted inverse value `z+1` by the Möbius law

`-1/Gamma'(z+1) = x*rho / (rho + x*z)`.

The nonzero derivative at `z` identifies `rho` as a residue interpolant.  When the shifted
derivative is also nonzero, the left side is the shifted residue interpolant; the algebraic
identity itself remains valid if that derivative vanishes. -/
theorem gamma_inverseValue_residueTransport_add_one
    {z x rho : ℂ} (hx : x ≠ 0)
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hvalue : Complex.Gamma z = -1 / x)
    (hrho : rho = -1 / deriv Complex.Gamma z)
    (hd : deriv Complex.Gamma z ≠ 0) :
    -1 / deriv Complex.Gamma (z + 1) = x * rho / (rho + x * z) := by
  have hrec := iteratedDeriv_Gamma_add_one 1 z hz
  norm_num [iteratedDeriv_one] at hrec
  rw [hrec, hvalue, hrho]
  field_simp [hx, hd]
  ring

end GaloisForLFunctions
