# Finite orbit markers reconstruct source faces up to their exact stabilizer

- **ID:** `orbit-marker-source-face-reconstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PARENT ALGEBRA / SOURCE-EFFECTIVITY GATE
- **Scientific status:** `[LEAN-FORMALIZED]` `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/OrbitMarkerSourceFaceReconstruction.lean`
- **Statement:** A finite marker on an orbit quotient reconstructs its ambient period subgroup
  exactly when the marker is aperiodic; every nonzero finite marker has only finite residual
  stabilizer, an atom is aperiodic, two typed aperiodic markers reconstruct the labelled face
  incidence lattice, and their common coarsening retains only the join.

## Exact theorem

Let `G` be an abelian group, `H <= G`, and let

```text
D in A[G/H]
```

be finitely supported.  Translation gives the residual quotient stabilizer

```text
Stab(D)={q in G/H:q.D=D}
```

and its ambient pullback

```text
Per_H(D)=pi_H^(-1)(Stab(D)).
```

The formalized theorem proves:

```text
H <= Per_H(D);
Per_H(D)=H  iff  Stab(D)={0};
D=0         implies Stab(D)=G/H;
D!=0        implies Stab(D) is finite;
D=c[x], c!=0, implies Stab(D)={0} and Per_H(D)=H.
```

For two typed markers `D_i in A[G/H_i]`, trivial residual stabilizers give

```text
Per_(H_0)(D_0) intersect Per_(H_1)(D_1)=H_0 intersect H_1,
Per_(H_0)(D_0) + Per_(H_1)(D_1)=H_0+H_1.
```

For a rationally independent rank-three frame `v_0,v_1,v_2`, the formalization also proves

```text
span_Z{v_0,v_1} intersect span_Z{v_0,v_2}=span_Z{v_0}.
```

Thus the labelled pair reconstructs not only an abstract meet but the exact common source line.

After coarsening to one atom on `G/(H_0+H_1)`, the recovered period group is only
`H_0+H_1`.  The two faces are gone.  Finally,

```text
Z(-q)=Zq,
```

so subgroup reconstruction cannot choose an orientation between `q` and `-q`.

## Mathematical meaning

This is the exact algebraic gate separating three notions that had been conflated:

1. a complete invariant inside a fixed source fibre;
2. reconstruction of the source-face lattice across varying source frames;
3. reconstruction of a polarization or orientation.

A common orbit divisor may be complete for the DA/HT phase while failing (2) and (3).  The typed
pre-pushforward boundary markers can recover (2) on their aperiodic stratum.  An oriented primitive
kernel generator or equivalent stacky datum is still necessary for (3).

The abstract stabilizer theorem is elementary group-action algebra and is not claimed as new
science.  Its role is to prevent the HT conjecture from demanding impossible reconstruction from
an untyped common divisor.

## Lean certificate

The module proves unconditionally:

- the zero and addition laws for finite-support translation;
- the translation stabilizer as an additive subgroup;
- finiteness of the stabilizer of every nonzero finite marker;
- triviality of the stabilizer of a nonzero atom;
- the exact pullback criterion `Per_H(D)=H iff Stab(D)=0`;
- reconstruction of the meet and join of two typed aperiodic faces;
- exact common-line intersection for two faces of a rationally independent rank-three frame;
- loss of the individual faces after common coarsening;
- sign blindness of a cyclic period subgroup.

No special-function or hypertranscendence hypothesis is introduced as an axiom.

## Gates

- [x] exact source-effectivity criterion proved
- [x] zero/nonzero/atom trichotomy proved
- [x] typed two-face reconstruction proved
- [x] common-coarsening no-go proved
- [x] orientation no-go proved
- [x] Lean formalization complete
- [x] parent-algebra status stated
