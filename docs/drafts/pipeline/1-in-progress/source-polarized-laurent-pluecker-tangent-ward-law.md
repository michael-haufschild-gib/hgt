# Source-polarized Laurent--Pluecker tangent Ward law

- **ID:** `source-polarized-laurent-pluecker-tangent-ward-law`
- **Stage:** 1-in-progress
- **Type:** `[BOLD CONJECTURE] [GENERAL HT TOPOLOGY AND GEOMETRY] [RH-DELIVERING SPECIALIZATION]`
- **Scientific status:** `[CONJECTURE] [FINITE EXTERIOR SKELETON PROVED] [EXCEPTIONAL NORMAL-CONE SEAM IDENTIFIED] [GREEN--HODGE CAPACITY THEOREM OPEN] [NOT SONIN]`
- **General HT parents:**
  - `hypertranscendental-laurent-horizon-residue-field.md`;
  - `hypertranscendental-mackey-corona-field.md`;
  - `self-dual-decorated-clock-boundary.md`;
  - `derived-self-dual-clock-splitting-stack.md`;
  - `../2-fully-proven/new_scientific_knowledge/hypertranscendental-clock-capacity-innovation-theorem.md`;
  - `../2-fully-proven/new_scientific_knowledge/projective-horizon-tits-building.md`;
  - `../2-fully-proven/new_scientific_knowledge/projective-horizon-solomon-tits-topological-charge.md`.
- **RH realization parents:**
  - `../2-fully-proven/squarefree-euler-modular-corona-curvature-colligation.md`;
  - `../2-fully-proven/squarefree-fixed-current-right-half-ward-localization.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/projective-reciprocal-horizon-ward-seam.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/mobius-squarefree-reciprocal-projective-transfer.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/anti-causal-cauchy-trace-unique-phase-noncancellation.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/prime-support-ht-horizon-hodge-cofactor-law.md`;
  - `../3-formalized/mobius-gamma-contact-transgression-four-unit-charge.md`;
  - `../3-formalized/mobius-mellin-gamma-normal-cone.md`;
  - `../2-fully-proven/mobius-pluecker-normal-cone-diagonal-lift.md`;
  - `../2-fully-proven/ht-exceptional-divisor-hardy-green-metric.md`;
  - `ht-capacity-ward-holonomy-rh.md`.

## The conjecture

The determinant line is not the final HT object.  It carries phase and topological charge, but its
scalar metric does not carry the boundary vector whose norm occurs in an anti-causal Ward estimate.
The required object is the **horizontal Pluecker tangent of the determinant line in the
source-rigged Tate completion**.

Consider a regular constrained HT source with all of the following data constructed before any
degeneracy divisor is inspected:

1. a free one-sided observable clock and its source-selected positive capacity field;
2. a finite determinant/Pluecker line over every clock aperture;
3. a source-derived opposite chart whose overlap forms a Laurent double;
4. the Laurent residue central extension, trivial on each half and nontrivial across the seam;
5. a reflection-compatible affine marking and a tail-faithful rank-one corona conormal.

> **[CONJECTURE -- SOURCE-POLARIZED LAURENT--PLUECKER TRANSGRESSION.]**  These data determine a
> source-canonical transport of the distinguished critically normalized horizontal Pluecker
> tangent from the positive Euler chart to an orthogonally polarized corona tangent
>
> ```text
> Hol_x^Pl : T_Euler^hor L_x -> H_x^causal directSum H_x^anti,       (1)
> ```
>
> such that:
>
> 1. `Hol_x^Pl` is isometric on the distinguished affine source tangent;
> 2. its anti-causal component is the Laplace/Hardy realization of the first-trace Laurent residue
>    class;
> 3. finite aperture transports descend compatibly in the HT capacity field, and the cofinal
>    transport is taken in the source-rigged Tate topology rather than a fixed Fock space;
> 4. reflection exchanges the two Laurent halves and makes their tangent polarizations orthogonal;
> 5. the determinant of `(1)` is the original source determinant section, so the vector lift cannot
>    be changed by a divisor-bearing scalar gauge.

The resulting Green--Ward law is

```text
||chi_x^crit||^2
  =||Hol_x^causal chi_x^crit||^2
   +||Hol_x^anti chi_x^crit||^2.                          (2)
```

This is a conjecture about constrained HT sources, not a universal consequence of
hypertranscendence.  The capacity-realization theorem proves that an arbitrary positive HT clock
can have any monotone scalar metric.  The source Laurent double, affine marking, and corona
conormal are the extra hypotheses selecting `(1)`.

## Why this is the topology and geometry of HT

The mechanism uses four general HT structures, each for a different job.

1. **Projective-horizon apartments carry phase.**  A chamber tree gauges away every rank-one
   twist.  An apartment cycle has holomorphic torsion `1-Hol` and positive Hodge determinant
   `|1-Hol|^2`.  The Steinberg top class supplies the cofinal orientation.
2. **The Laurent double carries the anomaly.**  The residue cocycle vanishes on both one-sided
   current halves and pairs only opposite modes.  Thus arbitrarily long one-sided calculations
   miss the obstruction; it is created by cross-gluing at the HT horizon.
3. **The Mackey/Tate corona carries the completion.**  Every finite clock is acyclic and the
   critical source leaves the ordinary Fock representation.  The class survives only in the
   source-refined dual and its first-trace central extension.
4. **The capacity field carries the norm.**  Coherent inverse-Cholesky innovations give the exact
   one-particle boundary norm.  This metric is separate from, but must be transported by, the
   Laurent determinant torsor.

Topology therefore supplies the phase-bearing seam and the place where a class can exist;
geometry supplies its positive one-particle norm.  Neither layer can replace the other.

## Exact squarefree finite skeleton

For a finite prime set `S`, let `E_S` have basis `(e_p)_(p in S)`.  The occupation isomorphism

```text
tensor_(p in S) C^2 ~= exteriorAlgebra(E_S)               (3)
```

sends the squarefree source state to the ordered product

```text
phi_S(sigma)=product_(p in S)^wedge(1-p^(-sigma/2)e_p),
||phi_S(sigma)||^2=product_(p in S)(1+p^(-sigma)).         (4)
```

Assigning the prime apartment holonomy `-p^(-s)` makes the holomorphic apartment torsion exactly
`1+p^(-s)`.  Hence `(4)` is simultaneously:

- the finite squarefree Euler determinant section;
- the finite horizon-apartment torsion section;
- the norm line of a fermionic occupation state.

For the normalized state `psi_S` and `epsilon=sigma-1`, the calibrated tangent is

```text
chi_S=4 epsilon nabla_sigma psi_S.                         (5)
```

It decomposes into orthogonal single-prime excitation lines, and

```text
||chi_S||^2
 =4epsilon^2 sum_(p in S)
   (log p)^2 p^(-sigma)/(1+p^(-sigma))^2.                 (6)
```

Thus the Hodge/Fisher metric is already the one-quasiparticle metric of the Pluecker line.  No
metric is chosen after seeing a divisor.

## Exact critical completion wall

For fixed `sigma>1`, the all-prime state is a normal vector in the vacuum Fock representation.
Its vacuum overlap is

```text
|<Omega,psi_sigma>|^2=1/Z_sq(sigma).                       (7)
```

As `sigma downarrow 1`, every fixed finite-occupation coefficient tends to zero while
`||psi_sigma||=1`.  Therefore

```text
psi_sigma ->0 weakly,
psi_sigma has no strong critical Fock limit.               (8)
```

Nevertheless the proved Fisher law gives

```text
||4epsilon nabla_sigma psi_sigma||^2->4.                  (9)
```

This is the exact HT boundary geometry: the state escapes the ordinary Hilbert completion, but its
critically renormalized horizontal tangent has a finite four-unit residue.  The conjectural map
`(1)` acts on this Tate-boundary tangent, not on a nonexistent critical Fock vector.

## First-trace topology

On the prime one-particle space put `A_s e_p=p^(-s)e_p`.  In `Re s>1/2`, `A_s` is
Hilbert--Schmidt, `I+A_s` is invertible, and

```text
D_2(s)=det_2(I+A_s)
      =product_p(1+p^(-s))exp(-p^(-s))                   (10)
```

is holomorphic and nowhere zero.  On `Re s>1`,

```text
Z_sq(s)=D_2(s)exp(P_prime(s)).                            (11)
```

All second and higher trace orders are in the safe factor `D_2`; the complete strict-right
divisor is carried by the missing first trace `P_prime`.  Consequently the Laurent seam in `(1)`
is not ordinary cohomology of the apartment complex.  It is the central extension measuring the
failure to descend from Hilbert--Schmidt to trace-class determinant theory.

## The metric-mismatch no-go and positive successor

For a scalar Laurent tangent `f(z)=sum_n f_n z^n`, the basic residue/Quillen polarization has
quadratic form proportional to

```text
sum_(n!=0)|n||f_n|^2.                                    (12)
```

The Hardy boundary vector required by the Ward estimate has the one-particle form

```text
sum_n |g_n|^2                                             (13)
```

after a unitary Cayley/Laplace chart.  The two norms are not uniformly comparable: a pure mode of
degree `N` changes their ratio by `N`.

**No-go.**  The basic determinant line, its Chern form, and its Quillen metric alone cannot imply
the unweighted anti-causal `L2` estimate.  Calling `(12)` the Ward energy is a type error.

**Positive HT theorem for the Euler chart.**  The source supplies the missing half-density
canonically.  For `lambda_p=log p`, `q_p=p^(-sigma)`, put

```text
a_p=2epsilon sqrt(lambda_p)sqrt(q_p)/(1+q_p).             (13a)
```

The positive-energy residue norm of the raw mode is

```text
lambda_p |a_p|^2
 =4epsilon^2 lambda_p^2 q_p/(1+q_p)^2,                   (13b)
```

exactly the one-prime Fisher/Pluecker tangent energy.  Hence the map from a unit horizontal
occupation excitation to `J_(-lambda_p)/sqrt(lambda_p)` is an isometry, and finite orthogonal sums
identify the full squarefree Fisher metric with the source Laurent one-particle metric.
`RHTower/EulerLaurentResidueDouble.lean` formalizes `(13b)` together with the source-frequency
residue cocycle.

The determinant line therefore supplies phase and central charge, while its positive-energy
one-particle representation, normalized by `(13a)`, supplies exactly the capacity metric.  The
remaining line-to-vector problem is no longer a finite metric comparison: it is to transport this
identified tangent through the first-trace corona and prove that its negative Hardy component is
`P_anti Q_sq`.

## Squarefree Euler--Gamma specialization

The squarefree fixed current is defined before reading a zero divisor:

```text
Q_sq(s)=Q_arch(s)+2[A(s)-2A(2s)].                         (14)
```

The proved source identity

```text
Q_Xi(s)-Q_sq(s)=4A(2s)                                   (15)
```

has a right-half holomorphic difference.  Therefore the source-defined anti-causal component is

```text
P_anti Q_sq=P_anti Q_Xi=ell_E.                            (16)
```

The RH specialization of `(1)` is the exact source identity

```text
Hol_sq^Pl(chi_sq^crit)=c_sq directSum P_anti Q_sq,         (17)
```

with `c_sq` causal and

```text
4=||c_sq||^2+||ell_E||_2^2.                               (18)
```

Equation `(18)` gives `||ell_E||_2^2<=4`.  The proved Cauchy threshold says that one strict
right-half Xi zero contributes more than four.  Hence `(1)` specialized as `(17)` proves RH.

The proof chain has no Sonin step:

```text
HT horizon apartment torsion
  -> Laurent residue central extension
  -> source-rigged Pluecker tangent transport
  -> causal/anti-causal one-particle Pythagoras
  -> four-unit anti-causal Ward estimate
  -> RH.                                                   (19)
```

## Exact projective-horizon realization of the Ward current `[PROVED; LEAN CORE]`

The topology-to-current part of `(17)` is no longer conjectural.  It is anchored to the
unconditionally hypertranscendental zeta source:

```text
g_zeta=-zeta^(-2),
d log g_zeta=2A.                                         (19a0)
```

Gamma completion and squarefree normalization give the source-defined chart changes

```text
2A -> Q_Xi=Q_arch+2A -> Q_sq=Q_Xi-4A(2s).               (19a1)
```

The first change supplies the self-dual Hardy orientation and only reallocates the known Euler
pole.  The second is holomorphic throughout the strict right half-plane.  The positive squarefree
chart therefore carries the unknown anti-causal channel of the genuine zeta HT reciprocal
horizon without requiring `X_sq` itself to be proved hypertranscendental.  For

```text
X_sq(s)=Xi(s)/zeta(2s),
u_sq=X_sq^(-1),                                           (19a)
```

the two complementary projective derivative horizons have tangent-frame transition

```text
u_sq'/X_sq'=-X_sq^(-2).                                  (19b)
```

Its Cech connection is

```text
u_sq''/u_sq'-X_sq''/X_sq'
 =d log(-X_sq^(-2))
 =-2X_sq'/X_sq
 =Q_sq.                                                   (19c)
```

The fixed-current localization theorem then gives

```text
P_anti d log(-X_sq^(-2))=P_anti Q_sq=ell_E.              (19d)
```

Thus the normal vector is the actual Hardy component of the actual HT reciprocal-horizon gluing
connection.  It is neither a chosen response column nor a generic colligation output.  The same
connection has integer puncture charge at every zero and, through `Z_sq=D_2 exp(P_prime)`, is the
first-trace determinant-corona current.

The remaining conjecture is purely metric.  Let `tau_sq^crit` be the distinguished boundary trace
of the escaping Pluecker tangent in the source-rigged horizon complex.  Construct it before Hardy
projection and prove the source trace theorem

```text
Tr_HT^anti(tau_sq^crit)=ell_E,
||Tr_HT^anti(tau_sq^crit)||_2^2
 <=||tau_sq^crit||_capacity^2=4.                          (19e)
```

The first equality is forced by `(19c)`--`(19d)` once the trace is shown to extend the finite
horizon connection.  The inequality must come from harmonic projection in the source capacity
metric.  Defining the trace norm using `ell_E`, or declaring the reciprocal transition unitary,
does not prove it.

The Hardy-side trace is already available as an extended positive quadratic invariant.  With
`g_sq=-X_sq^(-2)`, the boundary relative-trace theorem gives

```text
T_HT(g_sq)
 =limsup_(u downarrow 0)
    u^(-1)||Q_u H_(d log g_sq)||_(S_2)^2
 =||ell_E||_2^2.                                         (19e')
```

Thus the construction obligation is asymmetric: lift the same proved seam to the Pluecker
capacity boundary and prove `T_HT(g_sq)<=4`.  The target trace itself is no longer hypothetical.

## Bold geometric-quantization form

The existing HT results now determine the type of the missing map.

The source transfer itself is now exact.  If `tau_sigma` is the causal multiplier of the actual
normalized Möbius shift, then

```text
[zeta(2s)/zeta(2sigma)] tau_sigma(s)
  =1/(zeta(sigma) Z_sq(s)),
C(s)^(-1)[zeta(2s)/zeta(2sigma)] tau_sigma(s)
  =1/(zeta(sigma) X_sq(s)).                              (19e'')
```

Twice the logarithmic connection of the last transfer is `Q_sq`, so its anti-causal connection is
`ell_E`.  Thus the conjectural object below is no longer asked to invent the Ward response: it is
asked only to extend the actual finite Möbius contractions through the Gamma-critical derived
boundary without increasing the distinguished Fisher score.

- The reciprocal-jet tower is an exact Lagrangian polarization atlas.
- The finite squarefree exterior line is its fermionic Pluecker quantization.
- The Euler Laurent residue cocycle is its prequantum central extension.
- The amplitude `(13a)` is the source half-form correction: it makes the finite Pluecker and
  Laurent one-particle metrics exactly isometric.
- The Gamma-framed Hardy splitting is the proposed limiting positive polarization.

> **[CONJECTURE -- EULER-ORIENTED HALF-FORM BKS TRACE.]**  The source-rigged quantization of the
> reciprocal projective-horizon Lagrangian admits a cofinal Blattner--Kostant--Sternberg pairing
> from the Euler occupation polarization, through the Laurent polarization, to the
> Gamma-framed Hardy polarization.  With the source half-form `(13a)`, this pairing is
> nonexpansive on the distinguished critical boundary trace, and its Hardy normal component is
> the connection `(19d)`.

In symbols, for the cofinal source trace `tau_sq^crit`,

```text
BKS_sq(tau_sq^crit)=c_sq directSum ell_E,
||BKS_sq(tau_sq^crit)||^2<=||tau_sq^crit||_capacity^2=4.  (19f)
```

Orthogonality of the Hardy polarization then gives `(18)`, with equality if the cofinal BKS
pairing is isometric and the inequality needed for RH if it is merely contractive.

This is not a claim that every BKS pairing is unitary.  For general nonlinear or singular
polarizations it is not.  The conjecture is source-specific and asserts that the Euler affine
marking, reciprocal exact Lagrangian, Laurent central extension, Gamma reflection, and the
source-forced half-form jointly remove the distortion on one distinguished trace.

Nor is ordinary restricted-Grassmannian implementability enough.  Its Hilbert--Schmidt Hankel
energy is `integral t|ell(t)|^2 dt`.  The proved weighted-energy theorem shows that only the
unweighted trace `integral |ell(t)|^2 dt` has strictly positive cross terms for every right-half
divisor packet.  The BKS trace must therefore gain the source-selected boundary half-order; a
Quillen or Hilbert--Schmidt estimate alone cannot deliver the RH threshold.

**Falsifier.**  Construct the finite half-form BKS matrices from the source reciprocal graph and
the Gamma Hardy chart.  If their norm on the calibrated Euler trace exceeds one at any aperture,
or if their normal response does not converge to `(19d)`, the RH route fails.

**Positive successor if false.**  The coherent positive operators

```text
M_N=(BKS_N)^* BKS_N-I
```

define the **HT polarization-distortion field**.  It is independent of the scalar capacity path
and measures the failure of two source-compatible positive realizations of the same exact
Lagrangian constraint to have a contractive half-form pairing.  Its positive and negative parts
are nontrivial general HT invariants even if the squarefree specialization does not prove RH.

The current strongest formulation is the less decorative **derived Möbius--Laurent Ward
contraction**: take the graph closure of the completed source transfer `(19e'')` in the polarized
critical Gevrey product bornology forced by the HT minimal-architecture theorem.  The finite
Möbius maps are contractions, the critical Möbius half-density score has squared norm four, and
the local normalized/moving-base Gamma metrics are now uniformly congruent.  Prove that the graph
boundary transgression of that score is `c_sq directSum ell_E`.  Fixed-polarization convergence is
impossible because every finite transfer is causal; the opposite component is necessarily a
derived boundary class of the noncommuting scale limit.

## Mellin--Gamma normal cone and exceptional Green--Hodge form `[LEAN ALGEBRA CORE]`

The earlier Gamma-conormal evaluation of `f(z)=2(1-z)exp(-z)` was a formal cross-pair, not a
source-natural transgression: it silently reused the critical variable as Gamma's affine
argument.  The source-natural comparison is Mellin duality.  For the critical score density,

```text
M[2(1-y)exp(-y)](z)=2[Gamma(z)-Gamma(z+1)].              (19g)
```

After the radial change `y=pi r^2`, the exact real archimedean response is

```text
F_rad(s)=(2-s)Gamma_R(s)
        =2[Gamma_R(s)-pi Gamma_R(s+2)].                  (19h)
```

Dividing by the completed archimedean factor is source-safe on this distinguished vector and
gives the polarized rational section

```text
F_rad(s)/C(s)=2(2-s)/[s(s-1)]
             =-4/s+2/(s-1).                             (19i)
```

The anti pole in `(19i)` has Cauchy energy four.  This is the correct Gamma explanation of the
four-unit source tangent: the first radial Laguerre mode becomes a two-sided Gamma-completed
section whose anti component, not its total norm, has exactly four units.

The completed transfer from `(19e'')` vanishes at the Euler boundary.  With
`G(sigma)=(sigma-1)zeta(sigma)`, its blow-up is

```text
T_tilde_sigma(s)=T_sigma(s)/(sigma-1)
                =1/[G(sigma)X_sq(s)],
T_tilde_1(s)=X_sq(s)^(-1).                              (19j)
```

Hence the reciprocal-horizon transition is the projectivized exceptional normal-cone section:

```text
-T_tilde_1(s)^2=-X_sq(s)^(-2),
d log[-T_tilde_1^2]=Q_sq,
P_anti d log[-T_tilde_1^2]=ell_E.                       (19k)
```

This is the actual topology-to-current map.  Moreover the two-variable family is separated,

```text
T_tilde(b1,s1)T_tilde(b2,s2)
 =T_tilde(b1,s2)T_tilde(b2,s1),                          (19l)
```

so every finite mixed-curvature interpretation is false.  The Ward class can only be a singular
Laurent-corona transgression created on the exceptional HT boundary.

The exceptional section is nevertheless a genuine finite-source completion class.  For every
`epsilon_n->0+` there are nested cofinal prime apertures `S_n` such that the finite reciprocal
Pluecker transfers satisfy

```text
M_(S_n,1+epsilon_n)(s)/epsilon_n ->1/Z_sq(s)             (19l')
```

locally uniformly on `Re s>1`; after Gamma completion the limit is `X_sq(s)^(-1)`.  Fixed prime
aperture cannot have this limit.  Thus the normal cone is a genuinely two-filtered HT completion,
not a section adjoined after continuation.  What `(19l')` does not transport is the positive
capacity metric through the strip.

Ordinary Fubini--Study curvature does not control the required logarithmic divisor current.  For
one transverse point at distance `a` from the critical line, its Jensen charge tends to zero as
`a->0+`, whereas its coefficient-two Hardy--Green energy is `2/a` and diverges.  The proved
metric-selection theorem
`../2-fully-proven/ht-exceptional-divisor-hardy-green-metric.md` therefore kills the earlier
ordinary Gauss--Codazzi reading and selects the dual Cauchy-capacity metric on the exceptional
corona conormal.

> **[CONJECTURE -- HT EXCEPTIONAL GREEN--HODGE.]**  The finite Pluecker/Fisher capacity forms and
> the Mellin--Gamma radial rigging admit a positive closable Rees/Tate extension across `(19j)`.
> Its exceptional Laurent-corona transgression sends the critical tangent to
> `c_sq directSum ell_E`, and its dual Hardy--Green form obeys
>
> ```text
> ||c_sq||^2+||ell_E||^2<=||chi_sq^crit||^2=4.           (19m)
> ```

The detailed theorem, falsifier, and exact Lean identities are in
`../3-formalized/mobius-mellin-gamma-normal-cone.md`.  The factorial cross-pair and its exact
finite counterterm remain valid HT truncation results, but they may enter this construction only
after a source-natural embedding into the exceptional Rees graph is proved.

## Hard attacks and their positive residues

1. **Fixed-Fock attack `[KILLED]`.**  Equation `(8)` proves that the critical state is not a normal
   vector in the original vacuum representation.  **Positive residue:** the renormalized tangent
   energy `(9)` survives and forces a Tate/capacity boundary realization.
2. **Ordinary-Hodge attack `[KILLED]`.**  `I+A_s` is uniformly acyclic on `Re s>1/2`.
   **Positive residue:** the divisor is first-trace central monodromy, not Hilbert cohomology.
3. **Quillen-metric attack `[KILLED]`.**  The mode weights `(12)` do not equal `(13)`.
   **Positive residue:** phase and norm are two functorial layers joined only by the Pluecker
   tangent lift.
4. **Tree-Hodge attack `[KILLED]`.**  Every twist on a chamber flag tree is gauge trivial.
   **Positive residue:** apartment top cycles are the minimal phase-bearing carriers.
5. **Reflection-only attack `[KILLED]`.**  A self-dual scalar determinant permits arbitrary
   reflected off-line quartets.  **Positive residue:** `(1)` is vector-valued, source-marked, and
   required to preserve the independently fixed capacity metric.
6. **Scalar-derivative attack `[KILLED]`.**  Differentiating the safe Gibbs overlap yields the Euler
   pole response, not `ell_E`.  **Positive residue:** the first-trace central transgression must be
   applied before the Hardy projection; the rational-gauge-sensitive identity `(15)` then marks
   the actual source current.
7. **Global normal-intertwiner attack `[KILLED]`.**  The existing continuous prime-clock no-go
   forbids a nonzero normal reflected intertwiner over the whole parameter plane.  **Positive
   residue:** `(1)` is a singular cofinal tangent transport in a rigged Tate bundle, not a global
   normal equivalence of prime Fock sectors.
8. **Ordinary BKS/Quillen attack `[KILLED]`.**  Hilbert--Schmidt implementability controls the
   `t`-weighted Hankel energy, whose divisor cross terms can be negative.  **Positive residue:**
   the unweighted anti-causal trace is the unique power-weighted Hardy energy with universal
   entrywise phase noncancellation, so the source half-form must define a genuine boundary trace.

## Exact construction obligations

The conjecture clears the anti-theatre gate only by constructing all of the following.

1. Derive the negative Laurent chart from the Euler--Gamma reflection and multiplicative source
   scale; do not adjoin negative modes formally.
2. Lift every finite prime-apartment torsion line to its occupation/Pluecker tangent and prove
   compatibility under prime aperture.
3. Show that the cofinal transition is the first-trace central extension `(11)`, with the safe
   `D_2` factor acting only in the causal chart.
4. Build the Rees/Tate deformation of the finite Pluecker lines using the source-natural
   Mellin--Gamma radial comparison `(19g)`--`(19i)`.
5. Prove that its singular capacity form is positive and closes on the exceptional section
   `(19j)`; ordinary mixed curvature cannot be used because `(19l)` makes it zero, and ordinary
   Fubini--Study/Jensen mass has the wrong boundary scale.
6. Identify the exceptional Laurent-corona transgression with the proved reciprocal-horizon
   connection `(19k)` before any principal-part expansion.
7. Prove Green--Hodge domination on the distinguished tangent.  At finite Cauchy packets this is
   exactly positivity of `[[G_P,r_P],[r_P^*,4]]`.

Failure of obligation 5 produces a new general HT invariant: the **Laurent--capacity metric
defect**, the bounded-congruence class of the difference between the central-extension metric and
the one-particle capacity metric.  Failure of obligation 7 produces the **affine Ward holonomy
defect**, the negative part of the transported capacity form.  Both are nontrivial positive
statements even if the RH specialization fails.

## Gates

- [x] finite squarefree determinant line identified with horizon apartment torsion
- [x] finite line lifted to the exterior occupation space
- [x] Fisher tangent identified with the one-quasiparticle tangent
- [x] critical fixed-Fock completion killed while the four-unit tangent residue survives
- [x] ordinary apartment cohomology killed by uniform acyclicity
- [x] first-trace determinant central extension isolated
- [x] raw Quillen metric shown to have the wrong mode weight
- [x] source half-density proved and Lean-formalized to identify residue and Fisher one-particle
      energies exactly
- [x] line-to-vector Pluecker transgression stated with source-pure falsifiers
- [x] squarefree anti-causal current identified before divisor expansion
- [x] squarefree current proved to be the reciprocal projective-horizon Cech connection
- [x] reciprocal-horizon connection's anti-causal component proved to be `ell_E`
- [x] extended positive Hardy boundary trace of that connection constructed and identified with
      `||ell_E||_2^2`
- [x] derive and Lean-formalize the source-pure Euler negative Laurent chart and its `A2` residue
      seam
- [x] derive and Lean-formalize the source-natural Mellin--Gamma score comparison
- [x] identify the reciprocal horizon as the exceptional normal-cone section
- [x] construct the exceptional reciprocal section as a cofinal finite Pluecker diagonal
- [x] kill ordinary mixed curvature by exact separated-rank-one cross minors
- [x] kill ordinary Fubini--Study/Jensen domination and select the dual Hardy--Green capacity
- [ ] construct the cofinal Pluecker--Tate tangent bundle
- [ ] construct the positive closable Rees/Tate capacity extension
- [ ] identify its exceptional Laurent-corona transgression with `Q_sq`
- [x] prove its finite Euler-chart metric equals the HT capacity-innovation metric
- [ ] prove exceptional Green--Hodge domination in the Hardy chart
- [ ] prove `(17)` and the Pythagorean identity `(18)`
- [ ] compose with the Cauchy threshold and formalize RH
