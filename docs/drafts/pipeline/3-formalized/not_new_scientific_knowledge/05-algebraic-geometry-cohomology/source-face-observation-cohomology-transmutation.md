# Source-face observation cohomology transmutation

- **ID:** `source-face-observation-cohomology-transmutation`
- **Stage:** 3-formalized
- **Type:** MAXIMAL RECONSTRUCTION THEOREM / BASE-CHANGE BRIDGE / REPRESENTATION CORRECTION
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [BRIDGE]`
  `[GENERAL ALGEBRA IS NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Common-kernel parent:**
  `../../3-formalized/not_new_scientific_knowledge/da-relative-source-conservativity.md`
- **Barnes parent:**
  `../new_scientific_knowledge/barnes-differential-source-face-matrix-factorization.md`
- **Critical parent:**
  `../../3-formalized/hypertranscendental-critical-locus-universality.md`
- **Live successor:**
  `../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md`

## Lean formalization record

- `SourceFaceObservationExcess.lean` proves `(1)`--`(6)` over rings, including heterogeneous
  reporter families, quotient kernels, maximal reconstruction, and born-gauge/range-excess
  equivalence.
- `SourceFaceBaseChangeTransmutation.lean` proves the regular-face Bockstein laws `(8)`--`(11)`,
  identifies degree-zero and degree-one Tor from the same length-one free resolution, and proves
  all higher degrees vanish.
- `SourceFaceHyperTorEdge.lean` proves the explicit common-kernel counterexample and the collapsed
  one-face hyper-Tor edge sequence: inherited cycles are exactly the edge-map kernel and every
  `Tor₁` class is reached.
- `PrincipalQuotientBaseChangeTor.lean` and `BarnesSourceFaceTor.lean` prove `(13)`--`(16)` for
  polynomial and Laurent Barnes source rings.
- `CriticalNormalCrossingFaceTor.lean`, based on the existing exact Hilbert--Burch certificate,
  proves every degree of `(19)` and `(20)`, plus both forms of `(21)`:
  `Tor₁ ≃ J_F/(P_F)` and `Tor₁ ≃ ker(B/(P_F) → B/J_F)`.
- Targeted module builds pass. New capstones were audited with `#print axioms`; dependencies are
  only `propext`, `Classical.choice`, and `Quot.sound`.

## 1. Why the common kernel is not the whole object

For a normalized source-fixed gauge space `K^S` and reporters `R_r`, define the joint invisibility
space

```text
I(S,R)=K^S intersect intersection_r ker(R_r).                              (1)
```

Then the exact maximal reconstruction and positive quotient laws are

```text
Obs_R injective iff I(S,R)=0,
K^S/I(S,R) ~= range(Obs_R).                                                (1+)
```

Thus a nonzero element of `I(S,R)` is an explicit joint-nonconservativity witness, while the
quotient in `(1+)` is the maximal stratum reconstructible by the given reporters.  In particular,
reporters factoring through the same bare source cannot recover information which that source
forgot.  This is maximal at one fixed source, but it retains only the kernel of an observation
map.  It cannot predict how that kernel changes at a source face.

The smallest discriminator is over `A=k[x]`.  Multiplication by `1` and multiplication by `x`
are both injective as maps `A -> A`.  After restriction to `A/(x)`, the first remains the identity
and the second becomes zero.  Their generic kernels agree, but their generic cokernels are `0`
and `A/(x)`.  Therefore:

```text
[NO-GO]
The common-kernel sheaf, even at every regular point, is not a conservative source-face
invariant.
```

The positive successor is to retain the full two-term observation complex, including its
differential and attainment cokernel.

## 2. Quotient observation theorem `[PROVED + LEAN]`

Let `f:M -> N` be a linear observation over a field, let `P <= M` and `Q <= N`, and assume
`f(P) <= Q`.  Write

```text
f_bar:M/P -> N/Q.                                                        (2)
```

Then

```text
ker(f_bar)=f^(-1)(Q)/P,                                                  (3)
f_bar injective iff f^(-1)(Q)=P.                                        (4)
```

Modulo the generic kernel, the genuinely born part of `(3)` is

```text
B(f;P,Q)=f^(-1)(Q)/(P+ker(f)).                                           (5)
```

There is a canonical isomorphism

```text
B(f;P,Q) ~= (range(f) intersect Q)/f(P).                                 (6)
```

### Proof

The quotient map sends the class of `m` to zero exactly when `f(m)` belongs to `Q`, proving
`(3)` and `(4)`.  Restrict `f` to `f^(-1)(Q)`.  Its image is exactly
`range(f) intersect Q`.  After quotienting the target by `f(P)`, the kernel is exactly
`P+ker(f)`.  The first isomorphism theorem gives `(6)`.

Thus a boundary cannot create arbitrary invisible gauges.  Every new gauge is represented by a
generic observation which has fallen into the forgotten target layer.  This is a positive
classification, not merely the negation of reconstruction.

`formal/GaloisForLFunctions/HTGeometry/SourceFaceObservationExcess.lean` formalizes `(1)`--`(6)`
unconditionally, including reporter families with heterogeneous codomains.  Its capstones are:

- `sourceFixedJointObservation_injective_iff`;
- `sourceFixedJointObservableQuotientEquivRange`;
- `sourceFaceQuotientObservation_injective_iff`;
- `sourceFaceBornGaugeEquivRangeExcess`.

## 3. One regular source face: attainment becomes ambiguity `[PROVED]`

Let `A` be a commutative ring, let `x` be a non-zero-divisor, and let `f:M -> N` be `A`-linear,
with multiplication by `x` injective on `M` and `N`.  Put

```text
K=ker(f),       C=coker(f),       A_0=A/(x),
f_0:M/xM -> N/xN.                                                        (7)
```

The long exact cohomology sequence of multiplication by `x` on the two-term complex `[M -> N]`
gives

```text
0 -> K/xK -> ker(f_0) -> C[x] -> 0,                                     (8)
coker(f_0) ~= C/xC.                                                      (9)
```

Here `C[x]=ker(x:C -> C)`.  Since `0 -> A --x-> A -> A_0 -> 0` is a free resolution,

```text
C[x] ~= Tor_1^A(C,A_0).                                                  (10)
```

Combining `(8)` and `(10)` gives the exact transmutation law

```text
0 -> inherited common kernel -> boundary common kernel
  -> Tor_1(generic attainment defect, face) -> 0.                        (11)
```

In particular, if the generic reporter is injective, every boundary failure of injectivity is
exactly a `Tor_1` class of its pre-existing failure of attainment.

## 4. Derived commutator no-go and exact positive replacement

Suppose rigidification is represented by the homotopy fibre of an observation map and source-face
restriction by derived tensor product.  Derived tensor is an exact functor of triangulated/stable
categories, so it preserves homotopy fibres.  Consequently:

```text
[NO-GO]
A "derived rigidification--specialization commutator" defined as the comparison between derived
specialization of the homotopy fibre and the homotopy fibre of derived specialization is zero.
```

The obstruction is not failure of the two derived operations to commute.  It is failure of the
ordinary cohomology/truncation functor to commute with derived specialization.  The positive
replacement is the hyper-Tor spectral sequence

```text
E_2^(-p,q)=Tor_p^A(H^q(C_obs),B)
  => H^(q-p)(C_obs tensor_A^L B),                                        (12)
```

whose one-face edge sequence is `(8)`--`(11)`.  The common kernel is `H^(-1)`, attainment is
`H^0`, and a source face can move a class from the second to the first without creating or
destroying it in the derived observation complex.

## 5. Barnes HT realization `[PROVED]`

For the DA-relative Barnes hierarchy, let

```text
A=C[delta,T_1^(+-1),...,T_N^(+-1)],
x_i=T_i-1,
f_N=product_i x_i,
M_N=A/(f_N).                                                             (13)
```

The exact Barnes annihilator theorem identifies `M_N` as its differential-translation
characteristic module.  The presentation complex is

```text
A --f_N-> A.                                                             (14)
```

Because `A` is a domain, `(14)` is generically injective and has cokernel `M_N`.  On every
nonempty coordinate face `S`, with `B_S=A/(x_j:j in S)`, its differential becomes zero.  Hence

```text
ker((14) tensor B_S)=B_S,
Tor_1^A(M_N,B_S)=B_S,
Tor_i^A(M_N,B_S)=0 for i>=2.                                             (15)
```

Thus the previously proved Barnes pair

```text
relation death / capacity birth
```

is exactly

```text
generic attainment defect / boundary reconstruction inertia.           (16)
```

Equation `(16)` is the first exact coupling of the singular characteristic-module chart to the
regular common-kernel chart.  It does not yet identify an independently constructed analytic
reporter with `(14)`.

## 6. Complete zero-face profile of the critical normal-crossing module `[PROVED]`

Let `n>=2`,

```text
A=k[x_1,...,x_n],
P=product_i x_i,
m_i=P/x_i,
I=(m_1,...,m_n),
M_crit=A/I.                                                              (17)
```

The exact minimal resolution is

```text
0 -> directSum_(i!=s) A(-omega) --H-> directSum_i A(-alpha_i)
  --(m_1,...,m_n)-> A -> M_crit -> 0,
H(b_2,...,b_n)=(-x_1 sum_(i=2)^n b_i,x_2b_2,...,x_nb_n).                 (18)
```

Here `omega=(1,...,1)`, `alpha_i=omega-e_i`, and `s` is the base coordinate; forgetting the
multigrading gives `A(-n)^(n-1) -> A(-(n-1))^n`.

Let `F` be a nonempty coordinate face of size `k`, set
`B=A/(x_i:i in F)`, and relabel one member of `F` as `1`.  Tensoring `(18)` with `B` gives the
complete face homology.

For `k=1`, with `P_F=product_(j notin F)x_j`,

```text
Tor_0^A(M_crit,B)=B/(P_F),
Tor_1^A(M_crit,B)=directSum_(j notin F) B/(x_j)(-alpha_j),
Tor_i^A(M_crit,B)=0 for i>=2.                                            (19)
```

For `k>=2`,

```text
Tor_0^A(M_crit,B)=B,
Tor_1^A(M_crit,B)=directSum_(i in F) B(-alpha_i)
  directSum directSum_(j notin F) B/(x_j)(-alpha_j),
Tor_2^A(M_crit,B)=directSum_(i in F, i!=s) B(-omega),
Tor_i^A(M_crit,B)=0 for i>=3.                                            (20)
```

### Proof

For `k=1`, exactly one generator `m_i` survives and equals `P_F`; the other generators vanish.
After choosing the face coordinate as the base coordinate in `(18)`, the boundary map is the
direct sum of multiplication by each remaining `x_j`.  Since `B` is a domain, it has zero kernel,
and its cokernel is `B/(x_j)`, proving `(19)`.

For `k>=2`, every `m_i` vanishes.  In `(18)`, the `k-1` columns indexed by the other face
coordinates become zero, while each nonface column remains multiplication by its own `x_j`.
The zero columns give the `k-1` copies of `B(-omega)` in degree two; the `k` unhit target
coordinates give the multigraded free degree-one summands `B(-alpha_i)`; and the nonface columns
give the coordinate-torsion summands.  This proves `(20)`.

For `k=1`, put `J_F=(partial_j P_F:j notin F)`.  The summands in `Tor_1` map by multiplication by
`partial_j P_F` and have disjoint monomial supports modulo `(P_F)`.  Therefore

```text
Tor_1^A(M_crit,B) ~= J_F/(P_F)
  =ker(B/(P_F) -> B/J_F).                                                (21)
```

Thus specialization after criticalization first returns the lower normal-crossing hypersurface,
not its critical locus.  The entire correction from that hypersurface to the intrinsic lower
critical module is the born `Tor_1` class.  This zero-face law is different from the regular
coface law obtained by setting a structural coordinate to `1`.

## 7. What is and is not new

The quotient theorem, first/second isomorphism laws, exactness of derived tensor, Tor spectral
sequence, and the calculation of `(19)`--`(21)` from a known minimal free resolution are classical
homological algebra and commutative algebra.  They do not pass the scientific novelty gate by
themselves.  The relevant parent mechanisms are explicitly present in the Stacks Project's
derived tensor and Tor-spectral-sequence chapters, and the resolution of squarefree Veronese
ideals belongs to standard Stanley--Reisner/Hilbert--Burch theory.

The result is nevertheless a decisive representation correction for the research program:

```text
common kernel, source-face Tor, and critical base-change defect are not three fields;
they are cohomology and specialization data of one observation-resolution complex.            (22)
```

The candidate new scientific claim begins only after constructing this complex canonically from
an analytic HT source and an independently typed transverse reporter, and proving that two
different analytic obstruction receivers carry the same nonzero class through `(12)`.

## 8. Strong next theorem

The next theorem is not another abstract complex.  For one natural HT degeneration, construct
an analytic reporter map over the source-parameter ring and prove all three identifications:

```text
its generic H^(-1) = the normalized common reporter kernel;
its characteristic H^0 = the already computed HT characteristic module;
its Bockstein/Tor boundary = an independently computed analytic boundary charge or born gauge.
                                                                            (23)
```

The explicit Tate-theta divisor-to-winding family supplies the best current target: prove that
its node charge is the Bockstein image of the Barnes/elliptic characteristic `Tor_1` class, rather
than merely the same integer.  Success would be the first cross-receiver conservation theorem;
failure must classify the exact additional analytic coefficient sector needed by `(23)`.

## References checked

- Stacks Project, Definition 21.17.13 / tag `06YU`, derived tensor as an exact triangulated
  functor.
- Stacks Project, Section 15.63 / tag `061Y`, spectral sequences for Tor.
- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  `arXiv:1910.01874`.
- R. Feng, *Difference Galois groups under specialization*, `arXiv:1708.07944`.
- F. Galetto, *On the ideal generated by all squarefree monomials of a given degree*,
  `arXiv:1609.06396`.
