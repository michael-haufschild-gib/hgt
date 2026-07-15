# Gamma hypertranscendence has a dihedral bulk--mirror anomaly decomposition

- **ID:** `gamma-dihedral-orbifold-bulk-mirror-anomaly`
- **Stage:** 3-formalized / needs novelty audit
- **Type:** THEOREM + LEAN-FORMALIZED COHOMOLOGY
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [NOVELTY UNVERIFIED]`
- **Depends on:** `gamma-reflection-charge-conjugation-doubling`
- **Statement:** Reflection turns the Gamma orbit-charge lattice into a signed module for the
  infinite-dihedral constraint group. Ordinary reflection-symmetric HT sectors are free integer
  pairs on nonfixed orbits, while the degree-one reflection anomaly is supported only at the two
  self-dual orbit labels and equals `(Z/2)^2`. Every nonzero binary anomaly class and every nonzero
  symmetric integer sector has an explicit hypertranscendental Gamma representative.

## Setup

Fix a common shift scale `H>0` and reflection center `c`. Let

```text
B=C/(H Z),
Q=directSum_(omega in B) Z.                                (1)
```

The arbitrary-orientation Gamma theorem identifies `Q` with finite commensurable-slope Gamma
products modulo nonzero DA meromorphic gauges. Reflection `J_c:s |-> c-s` induces

```text
rho_c([b])=[H-c-b],
C(q)=-rho_c(q).                                            (2)
```

Here `rho_c` is an involution and `C` is charge conjugation. Translation and reflection generate
the infinite-dihedral symmetry of the common-scale orbit.

## The bulk--mirror theorem

### Symmetric sectors

The group of reflection-symmetric charge sectors is

```text
Q^C={q:C(q)=q}={q:q=-rho_c(q)}.                            (3)
```

Decompose `B` into fixed points and free two-cycles of `rho_c`. On a free pair `{omega,rho omega}`,
equation `(3)` has the form `(m,-m)` and contributes one copy of `Z`. On a fixed label it reads
`m=-m`, hence `m=0`. Therefore

```text
Q^C ~= directSum_({omega,rho omega} free) Z.               (4)
```

This is the exact charge-doubling law: ordinary symmetric HT content lives on free-orbit pairs and
is absent from the mirror-fixed labels.

### Degree-one reflection anomaly

Now compute the first cohomology of `C_2=<C>` with coefficients in the signed charge module `Q`:

```text
H^1(C_2,Q)=ker(1+C)/im(1-C).                               (5)
```

Because `C=-rho`, a one-cocycle is a finite charge `a` with

```text
a=rho(a),                                                  (6)
```

and a coboundary is

```text
a=g+rho(g).                                                (7)
```

On a free two-cycle, `(6)` is `(m,m)` and `(7)` realizes it from `(m,0)`, so the cohomology is zero.
On a fixed label, every integer is a cocycle and the boundaries are precisely the even integers,
so the contribution is `Z/2`.

The fixed-label equation is

```text
2b = H-c mod H Z.                                          (8)
```

It has exactly two solutions in `B`:

```text
b_0=(H-c)/2,
b_1=b_0+H/2.                                               (9)
```

They are distinct modulo `H Z`, and every solution of `(8)` differs from one of them by an
`H Z`-shift. Hence

```text
H^1(C_2,Q) ~= (Z/2)e_(b_0) directSum (Z/2)e_(b_1).         (10)
```

More generally, for any involutive label set `X` and its signed finite permutation lattice,

```text
H^1(C_2,Z_c[X] tensor sgn)
  ~= (X^rho ->_0 Z/2)
  ~= H_0^c(X^rho;Z/2).                                     (10a)
```

Thus the anomaly is a discrete Smith-localization law: degree-one signed-reflection cohomology is
the compactly supported mod-two zero-homology of the fixed locus. Equation `(10)` is `(10a)` for
the two-point fixed locus of the Gamma shift cylinder.

Equations `(4)` and `(10)` are the bulk--mirror decomposition:

```text
free reflection orbits  -> integer symmetric HT sectors;
two fixed orbit labels  -> binary reflection-twist anomalies. (11)
```

### Hypertranscendental realization

Every nonzero charge vector is represented by an HT Gamma product. Thus:

1. for each free pair and `m != 0`,

   ```text
   Gamma((s+b)/H)^m/Gamma((s+rho_c(b))/H)^m               (12)
   ```

   represents the symmetric sector `(m,-m)`;

2. `Gamma((s+b_0)/H)`, `Gamma((s+b_1)/H)`, and their product represent the three nonzero classes
   of `(10)`;

3. no DA Gamma-sector element represents a nonzero anomaly, because every DA element has zero
   orbit charge.

Doubling a mirror generator makes its **cohomology class** trivial because `2e_(b_i)` is a
coboundary. It does not make the Gamma function DA: the underlying integer charge remains nonzero.
This distinction prevents confusing reflection anomaly cancellation with hypertranscendence
annihilation.

For unit scale and the standard reflection `s |-> 1-s`, the two mirror labels are

```text
b_0=0,  b_1=1/2.                                          (13)
```

Thus the integer- and half-integer Gamma shifts are the two canonical binary mirror sectors. This
is an exact spectral-offset statement; no spin-statistics interpretation is assumed.

## Proof of completeness

The orbitwise calculation above proves `(4)--(10)` directly. A global finite-support proof can be
made constructive. Choose a linear order on `B`. For a cocycle `a=rho(a)`, define a finite
primitive `g` by:

```text
g(omega)=a(omega)/2    at fixed labels;
g(omega)=a(omega)      on the smaller member of a free pair;
g(omega)=0             on the larger member.              (14)
```

Then

```text
g+rho(g)=a                                                 (15)
```

exactly when every fixed-label coefficient is even. Consequently two cocycles are cohomologous
exactly when their coefficients have the same parity at every fixed label. This constructive
classification is the theorem formalized in Lean.

## Mathematical physical meaning

The common-scale Gamma constraint has a literal orbifold topology. The complex shift cylinder
`C/(H Z)` is acted on by an involution with two branch labels. Hypertranscendental charge separates
into:

- an integer, freely pairable sector away from the branch locus;
- a torsion response localized at the two branch labels after reflection is gauged.

This is the same mathematical pattern called bulk/fixed-locus anomaly localization in many
physical settings, but only the group-cohomological statement is asserted here. There is no
Hamiltonian, quantum state, fermion, crosscap, black-hole horizon, entropy, or physical time in the
proof. The legitimate physical insight is that symmetry can move information from an ordinary
invariant sector into torsion cohomology localized on its fixed set.

## Novelty and significance attack

The cohomology calculation for a signed permutation module of `C_2` is classical. In general,
cyclic-group cohomology is computed by the norm and difference maps; see for example
[Qiu, *On cohomology groups H1 of G-modules of finite type over cyclic groups*](https://arxiv.org/abs/1507.02370).
The infinite-dihedral group generated by a translation and reflection is likewise standard.
Euler reflection and the DA/HT orbit-charge classification are the analytic parents.

The candidate new content is the exact conjunction:

```text
Gamma DA quotient = integral orbit-charge module;
functional reflection = signed involution on that module;
HT symmetric sectors = free-pair integers;
reflection twists = two fixed-point Z/2 anomalies;
every nonzero sector is analytically realized and HT.      (16)
```

The abstract identity `(10a)` is standard signed-permutation-module cohomology; it is not claimed
as new. The candidate residue is its exact realization as the torsion response of the DA quotient
of a classical hypertranscendental function family.

Searches for Gamma-function dihedral cohomology, reflection-gauged Gamma products, signed
shift-orbit charge, and fixed-point binary HT anomalies located no equivalent theorem. That absence
does not prove novelty. The underlying algebra is an application of standard cyclic cohomology, so
the result is not yet medal-level and remains `[NOVELTY UNVERIFIED]`. Its significance is that it
identifies a new torsion invariant of a concrete HT family which was invisible both to positive
shift charge and to ordinary reflection-invariant sectors.

## RH impact audit

Functional equations of completed `L`-functions reverse the spectral variable, so the
integer/half-integer mirror labels in `(13)` are a natural archimedean audit surface. A Gamma-only
model now has a complete low-degree reflection topology: integer paired sectors plus two binary
fixed-label twists.

No identification with a root number, local epsilon factor, zeta-zero parity, or critical-line
orientation is proved. The Euler-product factor also transforms and can carry non-Gamma HT
information, so `(10)` cannot be imposed on a completed `L`-function without a new source theorem.
The result is an exact architecture and falsification constraint, not an RH proof step.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/ReflectionTateAnomaly.lean` proves:

- every reflection Tate boundary is a cocycle;
- cocycles are exactly finite charge vectors constant on reflection orbits;
- the explicit finite primitive `(14)`;
- a cocycle is a boundary iff all fixed-label coefficients are even;
- two cocycles are cohomologous iff their fixed-label parities agree;
- a fixed-label unit is nontrivial, while its double is a boundary;
- every equal-charge free mirror pair is a boundary.
- the additive subgroup of actual cocycles and the range subgroup of actual coboundaries;
- the fixed-locus parity homomorphism and its surjectivity;
- equality of the boundary subgroup with the kernel of fixed-locus parity;
- the quotient equivalence

  ```text
  H^1(C_2,Z_c[X] tensor sgn) ~= (X^rho ->_0 Z/2);
  ```

- specialization of that equivalence to `(Z/2)^2` whenever the fixed locus has two labels;
- the standard unit real shift-circle reflection `b |-> -b`;
- an explicit equivalence between its fixed locus and `Fin 2`, with representatives `0` and
  `1/2`;
- the resulting concrete additive equivalence between the standard reflected Gamma shift-circle
  cohomology and `ZMod 2 × ZMod 2`.

The existing cached module was verified directly:

```text
lake env lean GaloisForLFunctions/HTGeometry/ReflectionTateAnomaly.lean
```

No full build or broad lint was run.

## Gates

- [x] invariant-sector group computed
- [x] full degree-one signed-reflection cohomology computed
- [x] exactly two Gamma mirror labels proved
- [x] all nonzero classes realized by HT Gamma products
- [x] constructive completeness theorem formalized in Lean
- [x] no-go paired with integer and torsion positive phases
- [x] RH impact audited without upcasting
- [ ] independent group-cohomology and Gamma-product audit
- [x] formal quotient isomorphism to `(Z/2)^2`
- [ ] medal-level significance gate
