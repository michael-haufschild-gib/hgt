# Suzuki global phase conjugacy integrates the complete divisor and its weights

- **ID:** `suzuki-global-phase-conjugacy-divisor-flow`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Lane:** Suzuki finite-aperture divisor dynamics; nonlinear prime transport
- **Parents:** `suzuki-donoghue-defect-spectral-measure-law`,
  `suzuki-finite-shift-flat-projective-resolvent-holonomy`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), especially Theorem 1.5 and
  Sections 6--7
- **Statement:** At fixed aperture, every admissible Suzuki shift lies in one global
  phase-coordinate orbit.  One orientation-preserving real-analytic diffeomorphism transports all
  self-adjoint extension spectra, the complete phase-speed density, and every Clark/Nevanlinna
  atom with its exact Jacobian.
- **RH used:** no
- **Computation used:** no

## Frontier problem and representation change

The finite-shift holonomy theorem integrated Suzuki's whole Livsic carrier exactly, but rejected a
stronger global pole-flow claim.  Simplicity gives only local implicit branches; it does not by
itself prevent a labeled pole from escaping to infinity at a finite shift.

That rejection remains correct if one uses only local zero theory.  The missing properness is
instead supplied by the normalized Donoghue phase already extracted from Suzuki's source.  Its
spectral measure is pure point and cyclic on an infinite-dimensional space.  Hence its support is
infinite.  Parity makes that support two-sided, and positivity of the Clark weights makes the phase
strictly increasing.  The phase is therefore an order isomorphism of the whole real line.  Its
inverse labels every pole globally without continuing any local branch.

This representation change closes the finite-parameter escape wall and produces a stronger
weighted-divisor theorem.

## Setup

Fix an aperture `a>0`.  Let `A=A_a` be Suzuki's Friedrichs operator.  For every admissible
resolvent shift

```text
r > -lambda_a
```

put

```text
R_r=(A+rI)^(-1),
u_r=R_r e,                  e(x)=exp(x),
F_r(z)=integral_[-a,a] u_r(x) exp(i z x) dx,
Theta_r(z)=((z-i)F_r(z))/((z+i)F_r(-z)),
m_r(z)=i(1+Theta_r(z))/(1-Theta_r(z)).                  (1)
```

The parent theorems give the following unconditional source facts.

1. `Theta_r` is meromorphic inner on the upper half-plane and has unimodular real boundary values.
2. `Theta_r(0)=-1`; its numerator and denominator have no common real zero.
3. `m_r` is the Donoghue transform of the spectral probability `nu_r` of a cyclic normalized
   deficiency vector for the canonical even extension.
4. `nu_r` is even and pure point, and

   ```text
   dmu_r(t)=(1+t^2)dnu_r(t).                            (2)
   ```

5. At every even-extension eigenvalue `x`, equivalently `Theta_r(x)=1`,

   ```text
   mu_r({x})=2/q_r(x)>0,                                (3)
   ```

   where `q_r` is the boundary phase speed.

6. The shifted resolvent depends real analytically on `r`, and the finite carrier law is

   ```text
   Theta_s=H_(s<-r) Theta_r,
   H_(t<-r)=H_(t<-s)H_(s<-r).                           (4)
   ```

## Theorem: global phase-conjugacy divisor flow `[PROVED HERE]`

For each admissible `r` there is a unique real-analytic function

```text
phi_r : R -> R
```

such that

```text
Theta_r(x)=exp(i phi_r(x)),
phi_r(0)=pi.                                             (5)
```

It has the following properties.

### 1. Global phase chart

`phi_r` is a strictly increasing real-analytic bijection of `R` onto `R`, with

```text
phi_r'(x)=q_r(x)>0.                                      (6)
```

The map `(r,x) -> phi_r(x)` is jointly real analytic on the full admissible strip.

### 2. Simultaneous transport of every extension spectrum

For admissible shifts `r,s`, define

```text
T_(s<-r)=phi_s^(-1) o phi_r.                             (7)
```

Then `T_(s<-r)` is an orientation-preserving real-analytic diffeomorphism and

```text
T_(r<-r)=id,
T_(t<-r)=T_(t<-s) o T_(s<-r).                           (8)
```

Suzuki's extension with parameter `theta` has spectrum

```text
x_(theta,k)(r)
  =phi_r^(-1)(theta+pi+2 pi k),       k in Z.            (9)
```

Consequently

```text
T_(s<-r)(x_(theta,k)(r))=x_(theta,k)(s)                 (10)
```

for every angle and every integer label.  Thus all extension spectra, including the canonical
even and odd interlacing pair, are globally transported at once.

### 3. Exact transport of phase density and Clark weights

Differentiating the phase identity gives the continuum law

```text
q_s(T_(s<-r)(x)) T_(s<-r)'(x)=q_r(x).                   (11)
```

Hence each phase cell carries the invariant mass

```text
integral_[x_(theta,k)(r),x_(theta,k+1)(r)] q_r(x) dx
  =2 pi.                                                 (12)
```

At an even-extension pole `x`, equation `(3)` turns `(11)` into the exact atom law

```text
mu_s({T_(s<-r)(x)})
  =T_(s<-r)'(x) mu_r({x}).                               (13)
```

For the normalized spectral probabilities this is

```text
nu_s({T_(s<-r)(x)})
  =T_(s<-r)'(x) (1+x^2)/(1+T_(s<-r)(x)^2) nu_r({x}).     (14)
```

### 4. Global analytic pole curves and exact generator

For every `theta,k`, the map `r -> x_(theta,k)(r)` is real analytic on the entire admissible shift
interval.  Curves with distinct labels never collide, and no fixed labeled pole can escape at an
interior shift.  On every compact shift subinterval each such curve is bounded.

Let

```text
G_r(z)=Fourier(R_r^2 e)(z),
Xi_r(z)=G_r(-z)/F_r(-z)-G_r(z)/F_r(z).                  (15)
```

The parent finite-shift theorem gives `partial_r Theta_r=Theta_r Xi_r`.  Comparing with `(5)` gives

```text
partial_r phi_r(x)=-i Xi_r(x).                          (16)
```

Therefore the global curves solve

```text
x_(theta,k)'(r)
  =i Xi_r(x_(theta,k)(r))/q_r(x_(theta,k)(r)).           (17)
```

For the even spectrum, `(3)` makes this exactly

```text
x_k'(r)=i mu_r({x_k(r)}) Xi_r(x_k(r))/2,                (18)
```

so the previously proved local Clark velocity is the infinitesimal generator of the global flow.

### 5. Restricted-Weil source norm transference

Let

```text
N_r=||v_(r,+)||_(T_r)^2
```

and let `v_(r,x)` be Suzuki's adjoint eigenvector.  The source atom formula is

```text
mu_r({x})
 =(1+x^2)|F_r(-x)|^2/(N_r ||v_(r,x)||_(T_r)^2).          (19)
```

Combining `(13)` with `(19)` gives the new exact norm-weight transport identity

```text
(1+T(x)^2)|F_s(-T(x))|^2/(N_s ||v_(s,T(x))||_(T_s)^2)
 =T'(x)(1+x^2)|F_r(-x)|^2/(N_r ||v_(r,x)||_(T_r)^2),    (20)
```

where `T=T_(s<-r)` and `x` is any even-extension pole.  Thus the global diffeomorphism transports
not just the zero set but the exact restricted-Weil Fourier amplitude/eigenvector-norm ratio.

## Proof

### Step 1: the real carrier has a normalized analytic phase

For real `x`, `|Theta_r(x)|=1`.  A real zero of its denominator would, by the reflection identity,
also be a numerator zero.  Source primeness/cyclicity excludes such a common zero.  Hence
`Theta_r(x)` is a nonzero real-analytic unit-circle-valued function on all of `R`.

Because `R` is simply connected, it has a real-analytic phase lift.  The identity
`Theta_r(0)=-1` selects the unique lift satisfying `phi_r(0)=pi`.  Equivalently, define

```text
q_r(x)=-i Theta_r'(x)/Theta_r(x),
phi_r(x)=pi+integral_0^x q_r(t) dt.                     (21)
```

The unit-circle relation makes `q_r` real and `(21)` gives `(5)`--`(6)` once positivity is proved.

### Step 2: phase speed is everywhere positive

Away from a pole of `m_r`, the Cayley relation gives

```text
m_r(x)=-cot(phi_r(x)/2),
q_r(x)=2m_r'(x)/(1+m_r(x)^2).                           (22)
```

The Donoghue representation gives

```text
m_r'(x)=integral_R (1+t^2)/(t-x)^2 dnu_r(t)>0.          (23)
```

At a pole `x`, the local expansion

```text
m_r(z)=-mu_r({x})/(z-x)+O(1)
```

gives

```text
Theta_r'(x)=2i/mu_r({x}),
q_r(x)=2/mu_r({x})>0.                                  (24)
```

Thus `q_r>0` on the entire line, including every Clark point.

### Step 3: cyclicity forces phase properness

The Donoghue measure is pure point because `m_r` is meromorphic across the real line.  Its defining
deficiency vector is cyclic for the canonical even extension.  If `nu_r` had finite support, its
spectral representation would identify the whole cyclic Hilbert space with a finite-dimensional
`L^2(nu_r)`.  Suzuki's completion is infinite dimensional, so the support is infinite.

Parity makes `nu_r` even.  Its discrete support has no finite accumulation and no atom at zero,
because `m_r(0)=0`.  It is therefore unbounded in both directions.  At every support point,
`Theta_r=1`, so `phi_r` assumes a distinct value in `2 pi Z`.  Strict monotonicity and two-sided
unbounded support imply

```text
lim_(x->-infinity) phi_r(x)=-infinity,
lim_(x->+infinity) phi_r(x)=+infinity.                  (25)
```

Hence `phi_r` is bijective.  Its derivative never vanishes, so the real-analytic inverse theorem
makes its inverse real analytic on all of `R`.

### Step 4: shift analyticity and global labeling

On `r>-lambda_a`, the resolvent `R_r` is operator-valued analytic.  Therefore `F_r`, `Theta_r`, and
`q_r` are jointly real analytic in `(r,x)`.  Formula `(21)` gives a jointly analytic normalized
phase.  Applying the analytic implicit-function theorem to

```text
phi_r(x)=theta+pi+2 pi k
```

and using `q_r>0` proves joint analytic dependence of every inverse-phase level.  Uniqueness of the
global inverse patches all local charts over the full connected admissible interval.  This proves
`(9)` and the global claims in part 4.  In particular, the missing properness is a consequence of
the phase bijection, not an assumed zero-count estimate.

### Step 5: conjugacy, cocycle, and weights

Definition `(7)` immediately gives

```text
phi_s(T_(s<-r)(x))=phi_r(x),                             (26)
```

and hence `(8)`--`(10)`.  Differentiating `(26)` in `x` proves `(11)`.  Integrating it between two
successive lifted phase levels proves `(12)`.  At an even pole, substitute
`q_r=2/mu_r` and `q_s=2/mu_s` into `(11)` to get `(13)`.  Equations `(2)` and `(13)` give `(14)`.
Finally, substitute the source formula `(19)` into both sides of `(13)` to obtain `(20)`.

### Step 6: the finite holonomy is the global flow generator

Differentiate `Theta_r=exp(i phi_r)` with respect to `r` and compare with
`partial_r Theta_r=Theta_r Xi_r`.  Since `Theta_r` never vanishes on the real line, cancellation
gives `(16)`.  Differentiating the fixed phase-level equation in `(9)` gives `(17)`, and `(3)` gives
`(18)` for the even spectrum.

This completes the proof.

## What this changes at the RH frontier

The fixed-aperture nonlinear integration problem is now closed at three nested levels:

```text
carrier:       Theta_s=H_(s<-r)Theta_r,
divisor:       x_(theta,k)(s)=T_(s<-r)(x_(theta,k)(r)),
atom weights:  mu_s({T(x)})=T'(x)mu_r({x}).              (27)
```

Prime activation cannot create, destroy, reorder, or collide finite-shift poles.  It deforms one
global phase lattice, and its exact source weights deform by the same Jacobian.  Ground escape and
free clock homogenization can therefore occur only through degeneration at an admissible shift
endpoint, at infinite shift, or through the changing-aperture limit; neither is a finite interior
branch pathology.

The remaining cofinal open core is sharper:

> Choose the intrinsic admissible shift schedule and prove compactness plus Xi identification of
> the normalized inverse-phase maps `phi_(a,r_a)^(-1)` (equivalently of `T_a`) together with their
> first derivatives at the phase lattice.

That one object carries support, ordering, Clark weights, and the exact dressed prime generator.
No separate zero-labeling or residue-matching theorem is now needed.

## Hostile audit

1. **Not simplicity disguised as properness.**  Properness comes from cyclic pure-point infinite
   support and parity.  Local simplicity is used only for nonvanishing phase speed.
2. **No hidden finite-dimensional assumption.**  Finite support is excluded because a cyclic
   self-adjoint spectral representation with finite support is finite dimensional, whereas the
   Suzuki completion contains an infinite-dimensional dense source domain.
3. **No real denominator singularity.**  Reflection makes any real denominator zero common to the
   numerator; primeness excludes it.
4. **No branch ambiguity.**  `phi_r(0)=pi` fixes the lift, and the inverse phase defines every label
   directly for every shift.
5. **No false endpoint claim.**  A pole may still diverge when `r` approaches `-lambda_a`, when
   `r->infinity`, or as `a->infinity`.  Only escape at an interior admissible shift is excluded.
6. **No RH input.**  Every ingredient is finite-aperture Suzuki theory plus general
   Livsic--Donoghue consequences already proved in the parent cards.
7. **No cofinal overclaim.**  The theorem supplies the correct global state variable but not its
   compactness or Xi limit.

## Literature and priority audit

The generic one-function ingredients are classical.  Hatinoğlu,
*Uniqueness theorems for meromorphic inner functions and canonical systems*,
[arXiv:2110.12384](https://arxiv.org/abs/2110.12384), explicitly records that a meromorphic inner
function has an increasing real-analytic phase and that Clark point masses are inverse boundary
derivatives.  Romanov, *Canonical systems and de Branges spaces*,
[arXiv:1408.6022](https://arxiv.org/abs/1408.6022), surveys the surrounding inverse spectral theory.
These generic facts are not claimed as new.

Suzuki constructs the fixed-shift self-adjoint extensions and proves reality of their spectral
zeros, but does not introduce the Donoghue phase, Clark weights, phase conjugacy, divisor flow,
Jacobian law `(13)`, or source norm transport `(20)`.  Exact phrase and concept searches of the
source, repository, and arXiv found no Suzuki-specific finite-shift theorem of this form.  Candidate
novelty is the synthesis `(7)`--`(20)`, especially closure of the previously open finite-shift
properness wall.  Specialist priority review remains required.

## Lean target

Formalize the dependency-closed global-coordinate core, reusing the finite holonomy module:

```text
suzukiPhaseTransport
suzukiPhaseTransport_self
suzukiPhaseTransport_comp
suzukiPhaseTransport_level
suzukiPhaseTransport_phaseSpeed
suzukiPhaseTransport_atomMass
suzukiPhaseTransport_probabilityMass
suzukiGlobalPoleVelocity_eq_sourceGenerator
```

The concrete unbounded Suzuki operator, spectral theorem, and global construction of `phi_r` remain
paper-level until those source objects exist in Lean.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, exact module build green, axiom audit clean
- [ ] 3 -> 4 publication-ready: standalone paper, specialist priority review
- [ ] intrinsic cofinal shift schedule
- [ ] compactness of normalized inverse-phase maps and lattice derivatives
- [ ] Xi divisor identification
- [ ] RH

## Log

- 2026-07-21 — created in Stage 1 after replacing local implicit branches by the normalized global
  Donoghue phase coordinate.
- 2026-07-21 — hostile audit closed; cyclic infinite support proved phase properness; promoted to
  Stage 2 with simultaneous all-extension transport, atom Jacobian, global source generator, and
  restricted-Weil norm-weight transference.
- 2026-07-21 — dependency-closed order-isomorphism and weighted-transport core formalized and
  axiom-audited in `SuzukiGlobalPhaseConjugacy.lean`.
