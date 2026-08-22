# A two-species local QFT has projective HT without noncommuting scattering

- **ID:** `diagonal-projective-ht-local-qft`
- **Stage:** 2-fully-proven / not_new_scientific_knowledge
- **Type:** THEOREM / CONSTRUCTIVE MATRIX QFT / ANTI-THEATRE CONTROL
- **Scientific status:** `[PROVED] [PHYSICALLY REAL] [NOT NEW AS A CONSTRUCTION]`
- **Scope:** general hypertranscendental scattering in a two-species local relativistic QFT;
  no RH or distinguished special-function input
- **Parents:** `../needs-audit/open-family-hypertranscendental-cdd-qft.md` and
  `../needs-audit/projective-wigner-smith-nonabelian-ht-separation.md`
- **Statement:** There is a regular two-species factorizing S-matrix whose projective scattering
  field has differential transcendence degree one and whose relative Wigner--Smith delay is HT.
  Modular nuclearity reconstructs a compact-local, asymptotically complete interacting QFT from
  it.  Nevertheless all two-particle scattering operators at different rapidities commute.  Thus
  projective HT is physical relative-channel complexity, but it does not by itself imply
  nonabelian channel mixing.

## Input: any regular HT scalar scattering function

Let `K_0=C(t)` be the canonical crossing-coordinate base.  For rapidity differentiation, pass to
the algebraic differential kinematic extension

```text
K=K_0(partial_theta t),
(partial_theta t)^2=t^2-C^(-2).                               (1)
```

Multiplying a derivation by the nonzero algebraic Jacobian and extending the base algebraically
preserve DA versus HT.  Let

```text
h(theta)=S_(q,A,C)(theta)                                      (2)
```

be any member of the open geometric CDD family from the parent card.  The proved properties used
here are exactly:

```text
h is a regular scalar scattering function,
h(0)=-1,
h is HT over K.                                                (3)
```

The construction therefore uses an open family of HT functions, not a named isolated special
function.

## Minimal two-species matrix

Take the one-particle internal space `V=C^2`, with two neutral particles of the same positive mass.
For `alpha,beta in {1,2}`, set

```text
omega_11=h,
omega_12=omega_21=omega_22=-1,                                 (4)

S(theta)(e_alpha tensor e_beta)
  =omega_(alpha,beta)(theta) e_beta tensor e_alpha.             (5)
```

Equivalently, if `F` is the tensor flip and

```text
Omega=diag(h,-1,-1,-1)                                         (6)
```

in the ordered-pair basis `(11,12,21,22)`, then

```text
S=F Omega.                                                      (7)
```

The coefficients in `(4)` are symmetric regular scattering functions.  Hence the diagonal
S-matrix theorem of Alazzawi--Lechner gives all physical axioms: analyticity, unitarity, Hermitian
analyticity, crossing, PCT, and the Yang--Baxter equation.  Because every coefficient equals `-1`
at zero,

```text
S(0)=-F.                                                        (8)
```

Their analytic intertwiner theorem therefore applies.  There is a finite `s_min` such that the
modular nuclearity map is nuclear for every splitting distance `s>s_min`.  Consequently every
sufficiently large double cone has a hyperfinite type-III_1 local algebra with cyclic vacuum.  The
resulting Haag--Kastler model solves the inverse-scattering problem for `(5)` and is asymptotically
complete.  Its asymptotic one-particle space has exactly the two neutral species used above.

Since `h` is nonconstant, the scattering operator is not a free constant exchange operator.

## Exact projective Kolchin content

Choose any constant nonzero entry of `(5)` as projective pivot.  The ratio of the `(11)->(11)`
entry to that pivot is `-h`; every other nonzero entry ratio is constant.  Therefore

```text
P_S=K<h>,
dtrdeg_K P_S=1.                                                 (9)
```

This HT cannot be removed by multiplying the whole matrix by a common scalar CDD factor.

Let `partial` be the rapidity derivation and put

```text
u=h^(-1) partial h.                                            (10)
```

Since `Omega` is symmetric under the flip, `F Omega=Omega F`.  Direct differentiation gives

```text
A=S^(-1) partial S=diag(u,0,0,0),                              (11)
tr A=u,
A^o=diag(3u/4,-u/4,-u/4,-u/4).                                (12)
```

The logarithmic derivative `u` is HT over `K`.  Indeed, `h DA => u DA` by differential-field
closure.  Conversely, if `u` were DA then the first-order linear equation

```text
partial h=u h                                                  (13)
```

would make `h` DA over `K<u>`, and differential-algebraic transitivity would make `h` DA over
`K`, contradicting `(3)`.

For `Q=-iA`, the single relative channel-delay reporter

```text
Q_11-Q_12=-i u                                                 (14)
```

is real on the physical rapidity axis and HT.  Thus this local QFT realizes the projective
Wigner--Smith theorem operationally with one nontrivial relative reporter; the other reporters in
the universal finite panel are redundant on this one-dimensional model stratum.

The trace and projective sectors are both HT here, so this example lies in the mixed sector of the
central/projective trichotomy.  It is not a pure-traceless construction.

## Why this is not nonabelian HT

For all rapidities `theta,phi`, symmetry of the coefficients gives `[F,Omega(theta)]=0`, and the
diagonal matrices commute.  Hence

```text
S(theta)S(phi)
  =Omega(theta)Omega(phi)
  =S(phi)S(theta).                                             (15)
```

The Yang--Baxter equation is nontrivial as a consistency axiom of the many-particle theory, but
the channel algebra in `(15)` is commutative and no ordered-pair sector is mixed with another
except for the kinematic tensor flip.  A constant change of basis can make the displayed matrix
look non-diagonal, but cannot change this commuting algebra and therefore does not create a
nonabelian model.

Equations `(9)` and `(15)` prove that two axes previously conflated in the parent card are
independent:

```text
projective differential complexity:  dtrdeg_K P_S > 0,
intrinsic mixing complexity:          no constant one-particle basis U makes
                                      every flip-removed channel operator diagonal.     (16)
```

The standard `O(N)` sigma-model supplies the opposite control: it has genuine matrix channel
mixing but DA projective ratios.  The present model has HT projective ratios but a commuting
channel algebra.  Noncommutation of the flip-removed channel amplitudes is a sufficient witness
for intrinsic mixing, not a necessary one: symmetry-channel projectors can commute while their
eigenvectors remain entangled, and a nontrivial Jordan block can commute with its full rapidity
family while no `U tensor U` one-particle basis diagonalizes it.

## Anti-theatre and novelty gate

This construction is not promoted as new scientific knowledge.  Alazzawi--Lechner explicitly
allow arbitrary regular scalar scattering functions as the symmetric coefficients of diagonal
matrix S-matrices and prove their intertwiner property.  Substituting the already-proved HT scalar
family into one coefficient is therefore a direct specialization of published and internal
parent theorems.

Its load-bearing value is instead corrective and foundational:

1. it closes the existence of a physically local **projective-HT matrix** QFT;
2. it proves that “projective” and “nonabelian” must not be used as synonyms;
3. it supplies the positive local-QFT control against which a genuinely mixing construction
   must be tested;
4. it identifies one exact HT relative time-delay observable in that model.

Focused searches for `hypertranscendental diagonal S-matrix`, `differential algebra factorizing
S-matrix`, and `projective Wigner-Smith integrable QFT` found no published formulation of the
Kolchin classification `(9)`--`(14)`.  That negative search evidence concerns the classification,
not the diagonal QFT construction itself.

## Exact remaining nonabelian core

A complete-classification corollary is now proved on paper in
`../needs-audit/two-state-fermionic-zero-intrinsic-mixing-rigidity.md`.  It upgrades the
flip-anchored two-state adjacent class from pointwise product diagonality to one fixed product
basis.  The `O(N)` benchmark separates the conventions exactly: the physical quantum fermionic
anchor `-P` becomes a braid identity anchor `-I`.
The source convention conflict and theorem are recorded in
`../needs-audit/fermionic-zero-braid-anchor-commutation-gate.md`.  The complete regular
permutation-anchor strict-difference `4 x 4` quantum class is now proved projectively DA in
`two-state-regular-quantum-projective-da-rigidity.md`, but this does not erase the present
adjacent/nonregular commuting control.  A universal two-state no-go across both conversion
surfaces is therefore still not established.
Construct a regular unitary crossing-symmetric quantum Yang--Baxter family `R(theta)`, leaving its
state dimension open, such that:

1. its projective field has positive differential transcendence degree;
2. no constant one-particle gauge `U tensor U` reduces it to diagonal scattering; a
   non-diagonalizable member or noncommuting flip-removed channel algebra would be a sufficient
   stronger witness;
3. the HT survives quotienting all rapidity-dependent gauge connections declared part of the
   base;
4. an intertwiner, modular nuclearity estimate, or another theorem produces compact-local
   observables in the braid identity-anchor convention.

Tensoring `(5)` with a DA non-diagonal model, taking a direct sum, or applying a constant basis
change does not clear this gate: each operation merely hides a decomposable HT diagonal sector.

## Lean boundary

The new content is the analytic-QFT instantiation of existing theorems and the semantic separation
in `(16)`.  The finite identities `(11)`--`(15)` are elementary specializations of the existing
matrix and projective Wigner--Smith modules.  A new Lean wrapper would add no reusable theorem
surface.  No Lean edit or build is justified for this control.

## Primary literature

- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.

## Gates

- [x] regular unitary crossing-symmetric Yang--Baxter matrix
- [x] `S(0)=-F` and analytic intertwiner
- [x] modular nuclearity for sufficiently large splitting distance
- [x] compact-local type-III_1 observables and cyclic vacuum
- [x] inverse scattering and asymptotic completeness
- [x] projective differential transcendence degree one
- [x] explicit HT relative Wigner--Smith reporter
- [x] commuting-channel anti-theatre diagnosis
- [x] novelty rejected for the construction itself
- [ ] positive-unitary intrinsically mixing projective-HT scattering, with state dimension open
- [ ] independent analytic and operator-algebraic review
