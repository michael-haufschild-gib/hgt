# HB joint spatial domain and wave inverse

- **Stage:** 3-formalized.
- **Goal:** unconditional closed Lean proof/falsification of RH; not achieved.
- **Scope:** actual joint differential energy domain and its forced Laplace inverse.

Literal theta cusp → Xi occurrence → retained spin-two source → original causal
response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Exact result

The full joint differential graph has a complete domain, dense and injective
scalar projection, and a constructed self-adjoint energy operator. For every
independent complex frequency w with Re(w)>0 and every vector F in the actual
joint L² space, there is a unique energy response. Its scalar projection belongs
to the unbounded operator domain and solves `(A+w²-1)u=F`. The estimate is

`||u||_L² <= ||F||_L² / (Re(w)*|w|)`.

No angular eigenvalue, angular diagonalization, form domain, inverse, or
injectivity premise is supplied to the joint construction. Frequency positivity
is the stated analytic domain of the theorem, not an assumption about Xi zeros.
The result does not admit the non-L² principal cusp source or establish RH.

## Original coordinate and differential graph

Let x<0 be the original tortoise coordinate, `r(x)=-cosh(x)/sinh(x)`, and
`a(x)=1/cosh(x)`. Lean proves

- `r(x)>1`;
- `(log(r(x)-1)-log(r(x)+1))/2=x`;
- `r'(x)=r(x)²-1`;
- `a(x)²=(r(x)²-1)/r(x)²`.

Thus the radial vector field and angular coefficient are the original stream
wave coefficients. The scalar differential expression underlying the coexact
stream is `P=-partial_x²-a(x)²*Delta_modular`. The existing coexact angular
identities remain necessary when transporting its response to the covector
and constrained Einstein system.

Use `nu=volume restricted to x<0` and the corpus's actual invariant modular
measure mu. The ambient Hilbert space is `H=L²(nu product mu)`.
For every globally smooth compactly supported radial f with support strictly
inside x<0 and every member g of the full smooth compact modular core, form

`G(f,g)=(f*g, f'*g, a*f*D_1(g), a*f*D_2(g))`.

All products are the existing actual separated L² products. The two angular
D operators are the literal height-weighted coordinate derivatives. The domain
V is the closure of the complex span of these four-component graphs in the
sum-of-squares product Hilbert space. Its scalar projection J is continuous
and satisfies `||Jv||<=||v||`.

## Density and closability proof

Compact smooth radial tests separate L²(nu), by local integrability and the
smooth-test fundamental lemma on the open half-line. This proof does not
mistake L² on the infinite half-line for global L¹. Full smooth modular values
and the actual compact interior angular mass tests separately detect the
angular Hilbert space. The existing Hilbert tensor-product identification,
and adjoints of the actual separated-product maps, then show that both
corresponding product-test families detect H. Scalar projection density follows.

The radial identity

`<f,g'> + <f',g> = 0`

is proved by integrating the derivative of `conj(f)*g`; the compact interior
support kills the endpoint term at x=0. Angular identities come from the
existing literal modular weak derivative theorem. Multiplication by the real
weight a is symmetric between radial tests.

These identities define continuous functionals on all four graph components.
They vanish on the generators, their finite linear combinations, and their
closure. If Jv=0, the radial derivative component annihilates all product value
tests; each angular derivative component annihilates all product mass tests.
Their totality forces all three components to zero. Hence v=0 and J is
injective. Density, faithfulness, and completeness are proved for this actual
graph, not packaged as a replacement domain assumption.

## All-frequency inverse proof

The existing Friedrichs construction applied to J gives the closed self-adjoint
operator `A=(J J*)^-1`. Its form is scalar mass plus the three actual derivative
energies. On V define

`B_w=Id+(w²-1)J*J`, and `R_w=conj(w)B_w`.

The exact identity is

`Re <R_w v,v> = Re(w)*(||v||²-||Jv||²+|w|²||Jv||²)`.

Because `||Jv||<=||v||`, this is at least

`c(w)||v||²`, where `c(w)=Re(w)*min(1,|w|²)>0`.

The existing coercive bounded-operator inverse theorem provides the inverse
of R_w. Applying it to `conj(w)J*F` constructs the unique solution of

`<v,h>+(w²-1)<Jv,Jh>=<Jv,F>` for every v in V.

The exact gradient decomposition is

`sum_i <D_i v,D_i h>+w²<Jv,Jh>=<Jv,F>`.

It yields `||h||_V<=c(w)^-1*|w|*||F||_H`. Testing against h and retaining the
nonnegative derivative energy sharpens the scalar estimate to
`||Jh||_H<=||F||_H/(Re(w)*|w|)`.

Finally set `y=F+(1-w²)Jh`. The weak equation gives `J*y=h`, hence
`Jh=JJ*y` lies in the literal domain of A and `A(Jh)=y`. Therefore
`(A+w²-1)Jh=F` in the original ambient Hilbert space. This proof includes
positive real w and does not rely only on a nonreal spectral parameter.

## Lean modules and verification

Canonical prefix: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJoint`.
Namespace: `RHTower.D4BMJointWave`.

Suffixes: `RadialCore`, `RadialGreen`, `AngularTests`, `SpatialTests`,
`DifferentialGraph`, `Domain`, `Coordinate`, `WaveCoercivity`, `WaveInverse`,
`Response`.

The wave-form results are proved for a general contractive Hilbert embedding;
the final response specializes them to the fully constructed joint domain.
All ten scratch modules and exact canonical leaf builds passed. Each final
`lake build <module>` compiled only its new leaf plus bookkeeping in a cache-only
package. All twenty installed olean/ilean artifacts match the audited artifacts;
canonical source bytes match, and all ten leaves are wired once into RHTower.
One scratch audit of only the forty new public theorem axiom sets found only
`propext`, `Classical.choice`, and `Quot.sound`. Source indexing and scoped
whitespace/proof-debt checks passed. Global `lint --check-generated` reports
two unrelated modules unreachable from the RHTower umbrella:
`MobiusDivisorDilationMeanRenewal` and `MobiusDivisorDilationMeanUniformRenewal`;
it reports no new HB leaf issue. Those concurrent modules were left untouched.
No dependency, full, or umbrella build ran.
No numerical experiment or computational certificate is used.

## Remaining critical obligation

The literal quadratic source has principal cusp powers and is not automatically
in H. Retain both Weyl legs, the square potential, gradient-energy potential,
all cutoff derivatives, and the native remainder. Combine explicit principal
radial responses with a global cusp cutoff, then prove that the exact residual
forcing belongs to H at independent frequencies. Classical regularity and the
coexact/original-wave identification of that assembled response must be proved.
Time-causal inversion, constrained Einstein reconstruction, the left-QNM action
pairing, independent clock extinction, and RH remain open.

No new route-independent restriction was established beyond the existing
source-admission and original-operator requirements. This work leaves the
universal-law ledger and frontier map untouched.
