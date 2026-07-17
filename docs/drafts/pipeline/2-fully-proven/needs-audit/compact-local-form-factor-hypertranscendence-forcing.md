# Hypertranscendental scattering forces a dense compact-local form-factor sector

- **ID:** `compact-local-form-factor-hypertranscendence-forcing`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / LOCAL QFT / DIFFERENTIAL-ALGEBRAIC WATSON FORCING
- **Scientific status:** `[PROVED HERE FROM LECHNER + REEH--SCHLIEDER]`
  `[NOVELTY UNVERIFIED] [SIGNIFICANCE GATE PASSED AS A BRIDGE]`
- **Scope:** general regular one-species factorizing QFT with an HT scattering function; no RH or
  distinguished special-function input
- **Statement:** In a regular factorizing Haag--Kastler theory with hypertranscendental two-body
  scattering, every nonzero compact-local vacuum-to-two-particle form factor is
  hypertranscendental in the relative crossing coordinate.  Reeh--Schlieder makes such form
  factors dense in the two-particle Hilbert sector.  Thus HT scattering cannot remain confined to
  asymptotic data: compact local observables carry it abundantly in their exact two-particle
  matrix elements.

## Goal

Cross the wedge-to-local boundary without using a large-time scattering limit.  A limit is
insufficient for differential algebra because differential-algebraic functions can converge to a
hypertranscendental function.  The target reporter must instead be exact at finite localization.

The two-particle form factor already has such an exact reporter: its exchange quotient is the
scattering function.

## QFT hypotheses

Let `S_2` be a regular scalar factorizing scattering function and let

```text
(A(O),U,Omega,H)
```

be the local Haag--Kastler net obtained by Lechner's inverse-scattering construction.  Fix a
nonempty double cone `O` for which `Omega` is cyclic for `A(O)`.  This holds in the geometric
fermionic regularity model at every positive splitting distance.

For `A in A(O)`, define its two-particle vacuum form factor

```text
F_A(theta_1,theta_2)=(P_2 A Omega)(theta_1,theta_2).         (1)
```

Since `A(O)` is contained in a wedge algebra, Lechner's analytic form-factor theorem applies:
`F_A` is the boundary value of a holomorphic function on the regular rapidity tube.  Since
`P_2 A Omega` belongs to the `S_2`-symmetric Fock sector, it satisfies the exact Watson exchange
identity

```text
F_A(theta_2,theta_1)
  = S_2(theta_1-theta_2) F_A(theta_1,theta_2).              (2)
```

The identity extends from the real boundary to every common analytic germ by edge-of-the-wedge
uniqueness.

## Canonical relative coordinate

Put

```text
u=(theta_1+theta_2)/2,       v=theta_1-theta_2.
```

Let `t=t(v)` be the odd, locally invertible canonical scattering coordinate in which the HT claim
is made.  For the geometric CDD model,

```text
t(v)=-i sinh(v)/C,
v(t)=arcsinh(i C t)
```

on any fixed local branch.  Define the analytic pullback

```text
Fhat_A(u,t)
  = F_A(u+v(t)/2-i pi/2, u-v(t)/2-i pi/2).                 (3)
```

The common imaginary shift places `(3)` inside Lechner's holomorphy tube.  Since `t` is odd,
particle exchange is `t -> -t`, and `(2)` becomes

```text
Fhat_A(u,-t)=S_2(t) Fhat_A(u,t).                           (4)
```

No claim of invariance under arbitrary analytic reparametrization is used.  Equation `(4)` is
formulated directly in the same canonical coordinate and differential base as the scattering HT
theorem.

## Differential-algebraic forcing theorem `[PROVED]`

Use the ordinary differential field

```text
K=C(u,t),       D=d/dt,       D(u)=0.                      (5)
```

Assume `S_2(t)` is HT over `C(t)` and `Fhat_A` is not the zero germ.  Suppose for contradiction
that `Fhat_A` is DA over `K`.

1. Reflection `t -> -t` preserves differential algebraicity: the `j`-th derivative acquires the
   factor `(-1)^j`, so a differential polynomial for `Fhat_A(u,t)` gives one for
   `Fhat_A(u,-t)`.
2. The DA elements of a differential extension form a differential field.  Therefore `(4)` would
   make

   ```text
   S_2(t)=Fhat_A(u,-t)/Fhat_A(u,t)                          (6)
   ```

   DA over `C(u,t)`.
3. Hypertranscendence of a function independent of `u` descends across this purely transcendental
   constant extension.  Indeed, clear denominators in a putative differential polynomial over
   `C(u,t)`.  It becomes a polynomial in the algebraically independent constant `u` with
   coefficients in `C(t)[S_2,DS_2,...,D^rS_2]`.  Every coefficient must vanish, and at least one
   gives a nonzero differential polynomial for `S_2` over `C(t)`, a contradiction.

Consequently

```text
S_2 HT over C(t) and Fhat_A != 0
  => Fhat_A HT over C(u,t).                                (7)
```

For one reporter, every finite relative-jet packet has full rank:

```text
trdeg_(C(u,t)) C(u,t)(Fhat_A,D Fhat_A,...,D^r Fhat_A)=r+1. (8)
```

This is a forcing theorem, not an equivalence.  When `S_2` is DA, a local form factor may still be
HT for independent operator-specific reasons.

## Abundance theorem `[PROVED]`

Reeh--Schlieder says

```text
closure(A(O) Omega)=H.
```

The continuous projection `P_2:H -> H_2` therefore gives

```text
closure(P_2 A(O) Omega)=H_2.                               (9)
```

Hence compactly localized operators with nonzero two-particle form factor exist, and their
two-particle components are dense in the full two-particle sector.  Combining `(7)` and `(9)`:

```text
HT S_2
  => a dense family of compact-local observables has HT two-particle form factor.              (10)
```

More strongly, every member of this family except the zero two-particle component is forced onto
the HT branch.  The local carrier is not selected by tuning an operator to a special function.

## Kolchin locality inequality `[PROVED]`

For every compact-local `A` with nonzero two-particle component, define the relative form-factor
slope

```text
sigma_ff2(A)=sigma_(C(u,t))(Fhat_A).
```

Define the operator-independent local floor

```text
sigma_loc,2(Q)
  = inf {sigma_ff2(A) : A compact-local, P_2 A Omega != 0}. (11)
```

The set in `(11)` is nonempty by Reeh--Schlieder.  One-reporter slopes take only the values zero
and one.  If `sigma_scatt(Q)=1`, the forcing theorem `(7)` makes every term in `(11)` equal to one.
If `sigma_scatt(Q)=0`, nonnegativity of transcendence degree gives the bound trivially.  Therefore

```text
sigma_loc,2(Q) >= sigma_scatt(Q).                          (12)
```

For an HT scattering theory,

```text
sigma_loc,2(Q)=sigma_scatt(Q)=1.                           (13)
```

Equation `(12)` is a locality lower bound: no compact-local observable which couples the vacuum
to two particles can have lower one-reporter differential complexity than the exact scattering
law.  Taking the infimum removes the arbitrary choice of local operator.

## Physical interpretation

The form factor is the exact transition amplitude

```text
<theta_1,theta_2 | A | Omega>
```

for a compactly localized observable insertion.  Equation `(10)` proves that scattering HT is not
only a property of an asymptotic multiplication operator or of a wedge-local auxiliary field.  It
is encoded in a dense local observable sector.

Together with `wedge-pfg-four-point-exchange-carrier.md`, the placement is now:

```text
free one-particle propagation
        |
        +-- exact HT exchange coefficient in the wedge four-point cumulant
        |
        +-- exact HT vacuum-to-two-particle form factors of compact local observables.
```

The common source is the `S_2`-symmetry constraint on multiparticle assembly.

## Anti-theatre attacks

1. **Watson's equation renamed.**  Equation `(2)` and the form-factor program are parent theory.
   The candidate new content is the differential-algebraic forcing theorem `(7)`, its
   Reeh--Schlieder abundance upgrade `(10)`, and their use as a local HT law.
2. **Existence assumed from formal form-factor solutions.**  No bootstrap ansatz is used.
   Lechner's local algebra exists by modular nuclearity, and Reeh--Schlieder supplies actual
   bounded local operators.
3. **Boundary `L^2` vector treated as a germ.**  Lechner's analytic form-factor theorem gives the
   required holomorphic continuation for every wedge-algebra operator, hence for every compact-
   local operator in the intersection.
4. **Rapidity-coordinate inflation.**  The proof pulls the analytic form factor into the same
   canonical crossing coordinate `t` used by the scattering HT theorem.  It does not infer HT in
   an arbitrary analytic coordinate.
5. **One engineered witness.**  Projection of the Reeh--Schlieder dense set is dense in `H_2`;
   every nonzero projected form factor is forced HT.
6. **Connected interaction profile claimed.**  A vacuum-to-two-particle form factor is a local
   matrix-element sector, not yet the face-complete connected four-point profile.  The theorem
   proves compact-local HT transport, not the remaining connected-cumulant theorem.
7. **Interaction inferred from HT alone.**  Interaction in the geometric model is independently
   certified by its nonconstant reconstructed scattering operator.

## Novelty gate

The parent literature contains Watson exchange equations, minimal form factors, exact bootstrap
solutions, Lechner's analytic wedge form factors, modular nuclearity, and Reeh--Schlieder.  Recent
work also studies how generalized `T bar T` CDD factors alter minimal form factors.

Focused searches for `hypertranscendental form factor`, `differential algebra Watson equation`,
and `Kolchin form factor` found no differential-algebraic forcing or density theorem of the form
`(7)`--`(10)`.  That is negative search evidence, not a novelty proof.  Since the proof is short
once the parent theorems are assembled, a formula-level audit of integrable form-factor and
Riemann--Hilbert literature remains mandatory.

## Significance gate

This closes the compact-local **existence and abundance** bridge: HT scattering necessarily enters
exact matrix elements of bounded compact-local observables.  It turns a chosen asymptotic HT law
into a universal constraint on a dense local sector.  The operator-independent inequality `(12)`
is the first exact locality bound on the sectoral Kolchin signature.

It is not yet a Fields/Nobel theorem.  The higher target is a local law independent of the chosen
observable, such as a lower bound on a directed connected-sector Kolchin profile or a locality/
positivity inequality.  The present theorem supplies the first nonempty local sector on which such
a law can act.

## Exact remaining core

1. Prove a derivation-preserving reporter from compact-local connected correlators to the local
   form-factor germ `(3)`, or define an intrinsic local form-factor Kolchin profile and prove
   independence under admissible local operator changes.
2. Determine whether locality, crossing, and positivity strengthen `(12)` to a multireporter,
   connected-sector, or quantitative finite-jet inequality.
3. Audit whether known minimal-form-factor constructions already imply the HT conclusion for the
   geometric infinite CDD product under another language.
4. Extend the forcing theorem to matrix-valued scattering, bound states, and several commuting
   kinematic derivations.

## Lean boundary

The local Lean corpus already contains finite jet-independence and reporter-invariance machinery.
The decisive hypotheses here are external analytic/operator-algebraic facts: the Lechner tube
theorem, `S_2`-symmetric Fock sectors, modular nuclearity, compact-local intersections, and
Reeh--Schlieder density.

Formalizing only the elementary implication
`F(-t)=S(t)F(t) and DA(F) => DA(S)` would not formalize the physical theorem and would duplicate
existing rational-reporter infrastructure.  No Lean edit is justified until the local analytic
interfaces can be stated unconditionally.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- G. Lechner, *Polarization-Free Quantum Fields and Interaction*,
  <https://arxiv.org/abs/hep-th/0303062>.
- H. Babujian, A. Fring, M. Karowski, and A. Zapletal, *Exact Form Factors in Integrable Quantum
  Field Theories: the Sine-Gordon Model*, <https://arxiv.org/abs/hep-th/9805185>.
- O. A. Castro-Alvaredo, S. Negro, and I. M. Szecsenyi, *On the Representation of Minimal Form
  Factors in Integrable Quantum Field Theory*, <https://arxiv.org/abs/2311.16955>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and Linear Difference
  Equations*, <https://arxiv.org/abs/1910.01874>.

## Gates

- [x] compact-local operator source identified
- [x] analytic two-particle form-factor interface verified in the primary source
- [x] exact exchange quotient proved in the canonical HT coordinate
- [x] differential-algebraic constant-extension descent proved
- [x] Reeh--Schlieder abundance upgrade proved
- [x] operator-independent Kolchin locality inequality proved
- [x] wedge/local and form-factor/connected-sector boundaries recorded
- [ ] formula-level novelty audit across the form-factor literature
- [ ] intrinsic local form-factor profile and operator-change invariance
- [ ] connected-correlator transfer or locality inequality
- [ ] independent operator-algebraic and differential-algebra review
