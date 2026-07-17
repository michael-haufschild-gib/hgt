# Projective Wigner--Smith completeness separates relative-channel HT from scalar dressing

- **ID:** `projective-wigner-smith-nonabelian-ht-separation`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / MULTICHANNEL QFT / OPERATIONAL HT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Scope:** finite invertible matrix scattering over characteristic-zero differential fields;
  unitary real locus for the physical reporter panel; no RH or special-function input
- **Statement:** Scattering modulo arbitrary nonzero scalar dressings is Kolchin-complete in the
  traceless Wigner--Smith matrix.  A minimal panel of `n^2-1` relative channel delays reconstructs
  that matrix.  Hence relative-channel HT is exactly HT of the projective delay sector, whereas a
  matrix model whose channel ratios are DA can carry HT only in a common central phase.  This
  projective criterion is independent of whether the channel algebra is commutative or nonabelian.

## Projective scattering field

Let `K` be a characteristic-zero differential field containing `i`, let `L/K` be a differential
field extension, and let

```text
S in GL_n(L),                 A=S^(-1)DS,                 Q=-iA,       n>=2.       (1)
```

Choose any nonzero pivot entry `s=S_(a0,b0)` and put

```text
R=s^(-1)S.                                                                    (2)
```

The **projective scattering field** is

```text
P_S=K<R_ab : 1<=a,b<=n>.                                                       (3)
```

It is independent of the pivot.  If `t` is another nonzero pivot, every `t`-normalized ratio is
the quotient of two `s`-normalized ratios and conversely.  It is also unchanged by every scalar
dressing

```text
S -> fS,                          f in L^x,                                    (4)
```

because all entry ratios are unchanged.  Thus `P_S` is the differential field of the projective
class `[S] in PGL_n(L)`.

## Traceless logarithmic connection

Define

```text
A^o=A-(tr A/n)I,                  Q^o=Q-(tr Q/n)I=-i A^o.                      (5)
```

For `S=sR`, the product rule gives

```text
A=(s'/s)I+R^(-1)DR,
A^o=(R^(-1)DR)^o.                                                         (6)
```

Consequently every entry of `A^o` belongs to `P_S`.  Write

```text
E_o=K<(A^o)_ab>=K<(Q^o)_ab>.                                                  (7)
```

Then

```text
E_o <= P_S.                                                                   (8)
```

Equation `(6)` also proves the exact scalar-gauge law

```text
A(fS)=A(S)+(f'/f)I,                 A^o(fS)=A^o(S),                            (9)
Q(fS)=Q(S)-i(f'/f)I,               Q^o(fS)=Q^o(S).                           (10)
```

The traceless Wigner--Smith matrix is therefore the observable logarithmic derivative of the
projective scattering class, not of a chosen scalar normalization.

## Projective Kolchin completeness `[PROVED]`

Put `B=A^o`.  Since `A=B+aI` for `a=tr(A)/n`, equation `DS=SA` and normalization by the pivot give
the closed projective differential system

```text
D R_ab=(RB)_ab-R_ab (RB)_(a0,b0).                                             (11)
```

The scalar connection `a` cancels exactly.  Let

```text
M=E_o(R_ab : all a,b).                                                        (12)
```

This is a finitely generated ordinary field extension of `E_o`.  Equation `(11)` shows that `M`
is closed under the derivation: derivatives of the finitely many `R_ab` are polynomial in `R` with
coefficients in `E_o`, and `E_o` is already a differential field.  Hence every jet of every
`R_ab` lies in the same finite-transcendence-degree ordinary field `M`.  Infinitely many jets of
one coordinate are therefore algebraically dependent over `E_o`.  Each `R_ab` is DA over `E_o`,
so

```text
P_S/E_o is differential algebraic.                                           (13)
```

Together with `(8)`, differential-transcendence transitivity gives the exact projective law

```text
dtrdeg_K P_S=dtrdeg_K E_o.                                                    (14)
```

Thus `Q^o` loses no differential-transcendence capacity of the scattering matrix after quotienting
by arbitrary scalar CDD dressings.

## Central versus projective relative-channel HT

Jacobi's determinant identity gives

```text
tr A=D log(det S),                   tr Q=-i D log(det S).                     (15)
```

The trace is the central/determinant clock; `Q^o` is the projective relative-channel clock.  This
produces an invariant trichotomy.

1. **Central HT:** `tr Q` is HT but `Q^o` is DA.  The interaction has an HT common delay but a
   finite differential description after scalar dressing is removed.
2. **Projective HT:** `Q^o` is HT.  By `(14)`, some channel ratio of `S` is HT.  This is genuine
   relative-channel differential complexity, but it need not be noncommutative.
3. **Mixed HT:** both sectors are HT.

In particular, if

```text
S=f R_0                                                                    (16)
```

and every entry ratio of `R_0` is DA over `K`, then `P_S` and `Q^o` are DA.  Any HT of the complete
matrix is confined to the scalar factor `f`.  Calling such a model “relative-channel HT” is false.

Projective HT and nonabelian channel mixing are separate axes.  The proved diagonal control
`../not_new_scientific_knowledge/diagonal-projective-ht-local-qft.md` has `dtrdeg_K P_S=1` and an HT
relative delay while all `S(theta)` commute.  Conversely, the `O(N)` control below has
non-diagonal channel mixing but DA projective ratios.  A genuinely nonabelian HT model must satisfy
both conditions; projective Kolchin rank supplies only the differential one.  Here intrinsic
mixing means failure of simultaneous reduction of the flip-removed channel amplitudes to diagonal
form by a constant one-particle basis `U tensor U`.  Noncommutation of those flip-removed
amplitudes is sufficient for this failure but not necessary: a single non-diagonalizable channel
operator also suffices, and entangled symmetry-channel projectors can form a commuting family.

## Exact audit of the `O(N)` sigma-model example

The standard two-particle matrix has the three invariant tensor structures

```text
S=b(theta) 1+c(theta) P+d(theta) K,                                           (17)
c(theta)=-(i pi nu/theta)b(theta),
d(theta)=-(i pi nu/(i pi-theta))b(theta),              nu=2/(N-2).             (18)
```

Therefore every channel ratio lies in the rational rapidity field `C(theta)`, independently of
the common scalar factor `b`.  Its projective scattering field and `Q^o` are DA.  This iconic
non-diagonal factorizing model is a valid nonabelian QFT control, but it is not a genuinely
nonabelian HT example: any possible HT in this standard solution is central scalar dressing.

The same diagnosis applies to any rational, trigonometric, or elliptic finite-dimensional
`R`-matrix multiplied by a single scalar CDD factor, because those standard matrix entries are DA.
It does not prove that every Yang--Baxter solution has DA projective class.

## Minimal relative-delay tomography `[PROVED]`

On a unitary real-energy interval, `Q^o` is Hermitian and traceless.  Use the scalar reporters

```text
d_j=(Q^o)_jj-(Q^o)_nn,                                      1<=j<n,           (19)
A_jk=(Q^o)_jk+(Q^o)_kj,                                     j<k,               (20)
B_jk=i(Q^o)_jk-i(Q^o)_kj,                                   j<k.               (21)
```

They are physical relative delays:

```text
d_j=tau_(e_j)-tau_(e_n),
A_jk=tau_(e_j+e_k)-tau_(e_j)-tau_(e_k),
B_jk=tau_(e_j+i e_k)-tau_(e_j)-tau_(e_k).                                     (22)
```

Every expression in `(22)` balances input norm and is unchanged when a scalar multiple of the
identity is added to `Q`.  The off-diagonal entries reconstruct by

```text
(Q^o)_jk=(A_jk-iB_jk)/2,
(Q^o)_kj=(A_jk+iB_jk)/2.                                                       (23)
```

Tracelessness reconstructs the diagonal:

```text
(Q^o)_nn=-(1/n) sum_(j<n) d_j,
(Q^o)_jj=d_j+(Q^o)_nn.                                                        (24)
```

The panel contains exactly

```text
(n-1)+2 binom(n,2)=n^2-1                                                       (25)
```

real reporters, equal to the real dimension of the Hermitian traceless matrices.  It is therefore
minimal among real-linear scalar tomography panels.  Its joint differential field is `E_o`, so by
`(14)` projective HT forces at least one ordinary relative-delay trace in this fixed minimal panel
to be HT.

Applying the one-sided Erlang packet to every reporter preserves the conclusion at every positive
resolution because `(1-epsilon D)^3` exactly recovers each unsmoothed relative trace.

## Constant channel gauges

For constant invertible channel changes `S -> U S V`,

```text
A^o -> V^(-1) A^o V,                 Q^o -> V^(-1) Q^o V.                     (26)
```

The projective field and the joint field of `Q^o` are unchanged by the corresponding invertible
constant rational recombinations.  Individual reporter labels are basis-dependent, but projective
Kolchin rank is not.  Energy-dependent channel changes carry their own noncentral connection and
are not neutral gauges unless that connection is included in the declared base.

## Anti-theatre attacks

1. **A common HT factor called relative-channel HT.**  Killed by `(9)`--`(16)`: common scalar complexity
   vanishes identically from `Q^o`.
2. **Matrix non-diagonality confused with projective HT.**  The `O(N)` matrix is non-diagonal but
   has rational channel ratios.  Channel mixing and projective differential complexity are
   distinct notions.
3. **Trace-free subtraction declared physical by notation.**  Equations `(19)`--`(24)` realize it
   entirely through relative delay experiments; no absolute clock subtraction is assumed.
4. **`n^2` reporters retained after quotienting a scalar.**  The exact projective panel has
   `n^2-1` reporters and is dimension-minimal.
5. **Projective HT called nonabelian by definition.**  Killed by the two-species diagonal control:
   its projective field is HT but its rapidity scattering algebra is commutative.
6. **All Yang--Baxter matrices declared projectively DA.**  False.  In addition to the diagonal
   local-QFT control, the published non-difference control has projective HT and a non-diagonalizable
   flip-removed channel operator.  Its exact failures are positive-metric unitarity and Lorentz
   difference form, not Yang--Baxter consistency.

## Novelty and significance gates

The `GL_n -> PGL_n` central quotient, traceless logarithmic connection, Jacobi determinant identity,
Wigner mean delay, and polarization tomography are parent mathematics and physics.  Focused
searches for `traceless Wigner--Smith hypertranscendence`, `projective scattering matrix Kolchin`,
and `PGL logarithmic derivative scattering` found no statement of `(14)` or its operational
minimal-panel consequence.  This is negative search evidence, not a novelty certificate.

The result is significant because it changes the admissibility test for every proposed
relative-channel HT model.  A matrix-valued S-matrix is not enough: HT must survive in `P_S`,
equivalently in `Q^o`, and must appear in a relative channel-delay experiment.  For a genuinely
nonabelian model, one must additionally prove intrinsic channel mixing after constant
one-particle gauge reduction; non-diagonalizability or noncommutation of the flip-removed channel
amplitudes is a sufficient stronger witness.
The theorem therefore turns two previously conflated requirements into separate construction
gates.

## Exact open core

1. `[SOLVED FOR THE COMMUTING CONTROL]` The two-species diagonal model has a unitary,
   crossing-symmetric Yang--Baxter S-matrix with positive projective differential transcendence
   degree.
2. `[SOLVED FOR THE COMMUTING CONTROL]` Alazzawi--Lechner modular nuclearity gives compact-local
   type-III_1 observables and asymptotic completeness for that model.
3. Construct a regular Yang--Baxter family whose projective scattering field remains HT and which
   no constant one-particle gauge reduces to diagonal scattering.  The non-difference
   Corcoran--de Leeuw control solves this algebraically by a nontrivial unipotent channel block, but
   positive-metric unitarity and Lorentz difference form fail.  Solve both physical gates.
   The classification corollary
   `two-state-fermionic-zero-intrinsic-mixing-rigidity.md` now proves global fixed-basis
   diagonality for the positive-unitary two-state adjacent class anchored at `-P`.  The exact
   convention theorem `fermionic-zero-braid-anchor-commutation-gate.md` shows why this is not a
   no-go for the standard physical quantum lane: a physical quantum fermionic anchor `-P` becomes
   a braid identity anchor `-I`.  No minimum three-state conclusion is established there.
4. Classify spectral-parameter gauge transformations that preserve projective Kolchin rank and
   separate genuine HT cocycles from rapidity-dependent basis artifacts.
5. Prove compact-local existence for the genuinely noncommuting model.
6. Quantify the least finite-law margin of the minimal relative-delay panel under physical noise.

## Lean boundary

`FiniteDifferentialSystemAlgebraicity.lean` supplies the finite-system DA mechanism and
`MatrixWignerSmithTomography.lean` supplies full matrix polarization.

`formal/GaloisForLFunctions/HTGeometry/ProjectiveWignerSmithTomography.lean` now proves the complete
finite projective batch unconditionally:

1. the reference normalization and canonical traceless projection are invariant under every
   scalar identity shift;
2. the projective index has exactly `N^2-1` reporters;
3. reporter equality is equivalent to equality modulo a scalar identity matrix;
4. the panel is injective on trace-zero matrices.

The scratch batch and touched-file foreground Lean check passed, and the module is wired into the
HTGeometry umbrella.  The remaining algebraic scalar-gauge formula for an abstract matrix
logarithmic connection can now target the matrix product/derivative interface without duplicating
tomography.

The generated differential-field theorem `(14)` remains a separate formal layer.  No analytic
wave-packet theorem is required for the algebraic batch.

## Primary literature

- G. Lechner and C. Schützenhofer, *Towards an operator-algebraic construction of integrable
  global gauge theories*, <https://arxiv.org/abs/1208.2366>.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
- L. Corcoran and M. de Leeuw, *All regular `4 x 4` solutions of the Yang--Baxter equation*,
  <https://arxiv.org/abs/2306.10423>.
- M. de Leeuw and V. Posch, *All `4 x 4` solutions of the quantum Yang--Baxter equation*,
  <https://arxiv.org/abs/2411.18685>.
- H. M. Babujian, A. Foerster, and M. Karowski, *Exact form factors of the `O(N)` sigma-model*,
  <https://arxiv.org/abs/1308.1459>.
- C. Texier, *Wigner time delay and related concepts -- Application to transport in coherent
  conductors*, <https://arxiv.org/abs/1507.00075>.
- A. Grabsch, D. V. Savin, and C. Texier, *Wigner--Smith time-delay matrix in chaotic cavities
  with non-ideal contacts*, <https://arxiv.org/abs/1804.09580>.
- M. K. Michel and V. R. Srinivasan, *Differential Galois Groups of Differential Central Simple
  Algebras and their Projective Representations*, <https://arxiv.org/abs/2402.16093>.

## Gates

- [x] projective scattering field and pivot independence proved
- [x] scalar-dressing invariance of `Q^o` proved
- [x] projective Kolchin-completeness law proved
- [x] central/projective HT trichotomy isolated
- [x] projective HT separated from nonabelian channel mixing
- [x] standard `O(N)` matrix audited as projectively DA
- [x] diagonal projective-HT Yang--Baxter control constructed
- [x] compact-local QFT existence for the diagonal control
- [x] intrinsically mixing projective-HT Yang--Baxter control without physical unitarity/difference form
- [x] braid/quantum fermionic-zero convention and `O(N)` source conflict isolated
- [ ] global two-state no-go in the exact physical quantum convention
- [x] exact minimal `n^2-1` relative-delay panel proved
- [x] reducible scalar-dressing and energy-dependent-gauge caveats recorded
- [ ] formula-level novelty audit across differential Galois theory, inverse scattering, and
      Wigner--Smith metrology
- [x] unconditional Lean `N^2-1` projective tomography and scalar-shift invariance
- [ ] unconditional Lean projective logarithmic-connection and generated-field theorem
- [ ] positive-unitary intrinsically mixing projective-HT solution, with state dimension left open
- [ ] compact-local QFT existence theorem for the intrinsically mixing solution
