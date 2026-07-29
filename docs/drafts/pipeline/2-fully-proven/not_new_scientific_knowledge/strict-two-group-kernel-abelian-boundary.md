# Higher identity symmetry cannot contain the nonabelian quantum forces

- **ID:** `strict-two-group-kernel-abelian-boundary`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HIGHER-GAUGE NO-SELECTION BOUNDARY
- **Parent:** `../../1-in-progress/actuality-distinction-spacetime-law.md`
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** In every crossed module, the kernel of the boundary map is central and therefore
  abelian. Consequently the nonabelian weak and colour groups cannot be placed entirely in the
  identity-level symmetry of a strict 2-group.

## Goal

Test the first higher-gauge realization suggested by the global actuality-wall flatness
obstruction:

```text
external spacetime comparison = object/1-morphism symmetry
internal Standard Model symmetry = higher identity symmetry.
```

This card proves that this degree assignment is impossible. It does not rule out higher gauge
theory, a 2-stack of local actuality charts, or a first-level nonabelian Standard Model stabilizer.

## Algebraic setup

Let \(G\) and \(H\) be groups. It is enough to assume:

1. a boundary homomorphism \(\partial:H\to G\);
2. an operation \(g\triangleright h\) of \(G\) on \(H\);
3. identity action \(1_G\triangleright h=h\); and
4. the second Peiffer identity
   \[
     (\partial h)\triangleright k=hkh^{-1}.                         \tag{1}
   \]

Every crossed module has this data. The remaining action and equivariance axioms are unnecessary
for the obstruction.

## Theorem: Peiffer-kernel centrality

For every \(h\in\ker\partial\) and every \(k\in H\),

\[
  hk=kh.                                                            \tag{2}
\]

Hence

\[
  \ker\partial\le Z(H),                                             \tag{3}
\]

and \(\ker\partial\) is abelian.

### Proof `[PROVED HERE]`

Take \(h\in\ker\partial\). By `(1)` and the identity action,

\[
  hkh^{-1}
  =(\partial h)\triangleright k
  =1_G\triangleright k
  =k.
\]

Right multiplication by \(h\) gives \(hk=kh\). Since \(k\) was arbitrary, \(h\in Z(H)\), proving
`(3)`. Any subgroup of the centre is abelian. \(\square\)

## Corollary: nonabelian embedding obstruction

Let \(K\) be a group and \(i:K\to H\) an injective homomorphism satisfying
\(\partial(i(x))=1_G\) for every \(x\in K\). Then \(K\) is abelian.

### Proof `[PROVED HERE]`

For \(x,y\in K\), theorem `(2)` gives

\[
  i(xy)=i(x)i(y)=i(y)i(x)=i(yx).
\]

Injectivity gives \(xy=yx\). \(\square\)

In particular, no nonabelian \(SU(2)\) or \(SU(3)\) subgroup can be faithfully realized entirely
inside \(\ker\partial\).

## Strict and weak 2-group scope

Porst makes explicit the 2-equivalence between strict 2-groups and crossed modules. Under this
dictionary, \(\ker\partial\) is the group of automorphisms of the identity object invisible at the
object level.

Weakening strictness does not rescue the degree assignment. Baez--Lauda classify coherent
2-groups by a group of components, an **abelian** automorphism group of the identity, its action,
and a third-cohomology class. The abelianness is the same Eckmann--Hilton phenomenon expressed
homotopically.

Therefore the exact no-go is not “strict associators are too rigid.” It is:

> Nonabelian force symmetry cannot be hidden wholly above the first homotopy level of a 2-group.

Higher cells may still carry abelian phase, centre, anomaly, gerbe, or \(U(1)\) information.

## Higher-gauge literature collision

Higher gauge theory itself is parent theory:

- Baez--Huerta describe 2-connections, Poincaré 2-groups, tangent 2-groups, and gravity-related
  higher structures.
- Baez--Wise reformulate teleparallel general relativity using one connection for the
  teleparallel 2-group.
- Standard Model quantum field theory can also possess higher-group structures involving
  background 2-form fields and abelian current/anomaly data.

Thus neither “gravity is a 2-connection” nor “the Standard Model has a 2-group symmetry” is a
novelty claim.

## Exact boundary for actuality-distinction unification

The following tempting architecture is killed:

\[
  \pi_0(\mathcal G)=\text{external Lorentz/gravitational comparison},
  \qquad
  \pi_1(\mathcal G)=S(U(2)\times U(3)).                              \tag{4}
\]

The second term in `(4)` is nonabelian, whereas \(\pi_1\) of a 2-group is abelian.

The strongest positive survivor is:

> A viable actuality atlas may be higher-categorical, but the full Standard Model group must
> remain a nonabelian stabilizer of first-level local-event comparisons. Higher comparison cells
> can encode only its abelian coherence, centres, phases, or anomalies.

This sharpens the open architecture:

```text
objects:
  local actuality-distinction / exceptional-event charts

1-morphisms:
  nonabelian comparison maps carrying Lorentz and exact S(U(2)×U(3)) stabilizer data

2-morphisms:
  abelian coherence, amplitude-line, centre, and anomaly data

curvature:
  obstruction to effective first-level descent, not identification of the Standard Model
  with the higher identity kernel
```

The remaining new-physics target is not selection of a 2-group. It is a physical law that derives
the first-level comparison object, forces its external Lorentzian projection and exact internal
Standard Model stabilizer, and yields one non-product dynamics.

## No-go closure

- **Exact killing theorem/mechanism:** Peiffer identity forces the boundary kernel into the centre.
- **Strongest positive survivor:** higher cells remain available for abelian phase/anomaly
  coherence, while nonabelian force symmetry must live in first-level stabilizers.
- **New insight:** “gravity outside, quantum forces one categorical level higher” is impossible;
  unification must occur inside one first-level comparison law, with higher coherence constraining
  rather than containing the nonabelian forces.
- **Status:** dependency-closed paper proof; parent mathematics; Lean-proved and audited in
  `PeifferKernelAbelianBoundary.lean`.

## Novelty boundary

The centrality of a crossed-module kernel and the abelianness of higher homotopy groups are
standard mathematics. Their application here is a research-routing bridge, not new mathematical
or physical knowledge. No claim is made that actuality distinctions form a 2-group, that gravity
is higher-gauge curvature, or that the Standard Model is derived.

## Sources

- J. C. Baez and A. D. Lauda, *Higher-Dimensional Algebra V: 2-Groups*, Theory and Applications of
  Categories **12** (2004), 423--491, arXiv:math/0307200.
- S.-S. Porst, *Strict 2-Groups are Crossed Modules*, arXiv:0812.1464.
- J. C. Baez and J. Huerta, *An Invitation to Higher Gauge Theory*, General Relativity and
  Gravitation **43** (2011), 2335--2392, arXiv:1003.4485.
- J. C. Baez and D. K. Wise, *Teleparallel Gravity as a Higher Gauge Theory*, Communications in
  Mathematical Physics **333** (2015), 153--186, arXiv:1204.4339.

## Gates

- [x] 0 → 1: exact architecture under attack stated
- [x] 1 → 2: complete dependency-closed paper proof
- [x] 2 → 3: Peiffer-kernel centrality and injective nonabelian obstruction proved in Lean
- [ ] 3 → 4: not publication target; parent-theory bridge only

## Log

- 2026-07-29 — derived the Peiffer-kernel obstruction while auditing higher transition structures
  after global actuality-wall flatness. Classified it as standard parent mathematics and retained
  the first-level nonabelian / higher-level abelian survivor.
