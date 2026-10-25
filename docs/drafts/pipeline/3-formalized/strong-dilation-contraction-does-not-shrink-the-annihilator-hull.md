# Strong dilation contraction does not shrink the annihilator hull

- **ID:** strong-dilation-contraction-does-not-shrink-the-annihilator-hull
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), calibration no-go with positive survivor
- **Source:** Q-III, Mechanism A's passage from an escape exponent to a smaller polydisk; the checked Wiener-series extension and kernel Gram construction.
- **Statement:** For every `sigma>=1/2`, a faithful cyclic critical-Wiener representation has exact dilation norms `p^(-sigma)`, homogeneous Gram scaling `p^(-2sigma)`, and the full Bohr polydisk as its annihilator hull. For `sigma>1/2`, stronger contraction does not shrink this hull.

## Exact construction and proof

Let `H=l2(N_positive)` with orthonormal vectors `e_j`. Put

`v_j=j^(-sigma)e_j`, `V_p e_j=p^(-sigma)e_(pj)`.

The inclusion `j -> p*j` is injective. Consequently `V_p` is exactly
`p^(-sigma)` times an isometry, `V_p V_q=V_(pq)`, `V_1=Id`, and
`V_p v_j=v_(pj)`. The receiver `v_1=e_1` is cyclic. Its real Gram kernel is

`K_sigma(j,k)=1_(j=k) j^(-2sigma)`.

This kernel has unit receiver mass, positive packet energies, the usual
cofactor radius bound for `sigma>=1/2`, and the full homogeneous packet law
`Q_sigma(dilate_p c)=p^(-2sigma) Q_sigma(c)`. The generic antipodal-extension
theorem supplies its unique antipodal coordinate as well.

For `a` in the critical Wiener algebra, the operator series
`pi_sigma(a)=sum_(n>=1) a_n V_n` converges absolutely because
`sum |a_n| n^(-sigma)<=sum |a_n| n^(-1/2)`. It is a unital contractive
algebra representation by the already checked multiplicative-sequence theorem.
The `j`th coordinate of `pi_sigma(a)v_1` is exactly `a_j j^(-sigma)`.
Thus `pi_sigma` is injective. Its annihilator is zero, and its annihilator
hull is the entire Bohr polydisk, independently of `sigma`.

Choose the Bohr point with every coordinate equal to one. It belongs to this
hull. For `sigma>1/2` and `p>1`, its `p`th coordinate has modulus one, although
`sqrt(p)||V_p||=p^(1/2-sigma)<1`. Therefore contraction, even with exact full
homogeneity, does not bound the coordinates of the annihilator hull.

## Where the two spectra separate

The hull of `ker(pi)` describes characters of the Wiener quotient with its
quotient norm. It does not automatically describe characters continuous for
the operator norm on `pi(W)`. In this example the all-one character evaluates
`delta_(p^m)` as `p^(-m/2)`, while its represented operator has norm
`p^(-m*sigma)`. Their ratio tends to infinity for `sigma>1/2`. Hence this
character is not bounded for the operator norm and cannot extend continuously
to the operator-norm closure of the represented algebra.

The exact norms of all powers also give spectral radius `p^(-sigma)` for
`V_p` by the Banach-algebra spectral-radius formula. Thus the operator radius
really does shrink while the annihilator hull does not. The required
comparison between these spectral objects is a mathematical input, not a
change of terminology.

## Positive survivor and scope

The positive survivor is the full faithful weighted family: explicit cyclic
vectors, exact packet homogeneity, exact operator norms and power norms,
unchanged annihilator hull, and an explicit character failing operator-norm
continuity. The stronger operator bound also integrates the action over the
larger weighted Wiener algebra at `sigma`; that extension is a different
algebraic domain from the original critical Wiener quotient.

This is not an actual Möbius escape state. It refutes the proposed generic
inference from exponent/homogeneity to contraction of `h(ker(pi))`. It does
not refute containment for the actual receiver after additional arithmetic
constraints. In finite dimension the image is closed, so the distinction has
a different outcome; the finite-dimensional comparison is proved below.

## Corrected positive hull for the actual action

Define the operator hull by the quantitative condition

`operatorHull(pi)={omega : |bohrEval(a,omega)|<=||pi(a)|| for every a}`.

It is nonempty for every nonzero unital representation into bounded operators.
Indeed, take the operator-norm closure of its image. The image is commutative,
and commutativity passes to the closure by continuity of multiplication. This
closure is a nonzero unital commutative complex Banach algebra. A character on
it has norm one; composing with `pi` gives a Wiener character, hence a Bohr
point satisfying the displayed bound.

Every such point annihilates `ker(pi)`, so
`operatorHull(pi) subset h(ker(pi))`. On actual receiver escape, the paid-ideal
bridge further puts it inside the obstruction hull. Evaluating the norm bound
on `delta_p` gives exactly

`|omega(p)| <= sqrt(p)||V_p||`.

Thus this nonempty spectral subset, rather than the entire annihilator hull,
is controlled by stronger operator contraction. This is a dependency-closed
paper repair of the spectral inference; its Banach-subalgebra construction and
actual-source specialization are formalized. No comparison with the
translated zero hull follows without an additional arithmetic argument.

## Closed-image boundary: complete paper proof

A sufficient replacement condition is closedness of the represented algebra.
Suppose `pi(W)` is closed in the ambient Banach algebra, and let `omega` lie
in `h(ker pi)`. Its Wiener character `phi` vanishes on `ker pi`, so it descends
algebraically to `chi(pi(a))=phi(a)` on `pi(W)`. This is well-defined because
`pi(a)=pi(b)` implies `a-b` lies in the kernel. The closed image is a unital
complex Banach algebra. Every complex algebra character on it is contractive:
`chi(x)` belongs to the spectrum of `x`, whose modulus is at most `||x||`.
Consequently `omega` belongs to `operatorHull(pi)`, proving equality of the
two hulls. No inverse bound for `pi` is required.

In particular every finite-dimensional actual cofactor module has equal
annihilator and operator hulls, since its endomorphism algebra, hence the
representation image, is finite-dimensional and closed. Thus the dilation
coordinate bound holds on the entire module hull in this finite branch.
The actual finite-or-infinite alternative is unconditional; no claim that the
actual module is finite-dimensional is made. The Lean proof passed. The weighted
faithful counterfamily shows why closedness cannot be omitted in general.

## Gates

- [x] Dependency-closed paper construction, including faithfulness.
- [x] Positive survivor and precise failed spectral inference identified.
- [x] Lean construction, exact norms, faithfulness, and hull computation passed scratch checking.
- [x] Operator-spectrum and character-continuity consequences passed with standard axioms.
- [x] Nonempty operator hull and closed-image comparison passed with standard axioms.
- [x] Standard transitive axioms, final source checks, and umbrella imports.
- [x] Corrected distinction applied to Q-III; failed generic inference retired separately.

## Lean construction route

Use the canonical Gram realization of the explicit real diagonal kernel, then
`KernelHilbert.pushforward` for `j -> p*j`. The finite packet identity proves
its exact contraction; evaluating on the unit vector proves equality of the
operator norm. `sequenceRepresentation` supplies the Wiener action.
Applying the continuous inner-product coordinate to `hasSum_pointMass` gives
`<v_j,pi(a)v_1>=a_j*j^(-2sigma)`, hence faithfulness. This reuses the checked
kernel and Wiener infrastructure and does not require a separate construction
of weighted sequence spaces.

The same construction works for an algebra at any weight `tau<=sigma`.
Its annihilator remains zero while its exact dilation norm is fixed by `sigma`.
The critical specialization is `tau=1/2`. An explicit all-one Bohr character
then witnesses the mismatch with the stronger operator norm.

All weighted-family statements, critical packet bounds, antipodal uniqueness,
power norms, spectral radius, unbounded-character consequences, and closed-image
hull equality passed Lean with standard axioms. The actual nonempty-hull and
finite-dimensional comparison passed too, including the actual
admission-or-obstruction-containment wrapper.

Canonical modules are now `ArithmeticOrientationTheory/TheOperatorHullOfAWienerAction`,
`ArithmeticOrientationTheory/WeightedOrthogonalCofactorsHaveTheFullHull`, and
`ArithmeticDefectRigidity/TheCofactorOperatorHullObeysItsDilationRadii`.
Imports are wired. All three modules passed their final `lake --old env lean`
source checks. Axiom audits use only `propext`, `Classical.choice`, and
`Quot.sound`. The failed generic inference is recorded in
[the retired route](../5-failed/operator-decay-alone-controls-the-annihilator-hull.md),
with this exact positive survivor. No actual-source classification is claimed.
