# The Connes semilocal finite part fixes the degree-one orbital source class

- **ID:** `connes-semilocal-finite-part-orbital-source-class`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CORPUS SYNTHESIS (paper), `[BRIDGE]`, `[TOP-DOWN GAP REDUCTION]`
- **Scientific status:** `[PROVED FROM LITERATURE AND PAPER ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [PROOF-CONTRIBUTING] [NOT AN RH PROOF]`
- **Parents:** Connes's semilocal trace formula;
  `ccm-gauss-paired-quantized-differential-incidence-law.md`;
  `critical-euler-position-commutator-carrier-law.md`;
  `sonin-burnol-conductor-cutoff-bounded-graph-law.md`
- **Statement:** The logarithmically growing degree-one prime--Gamma source functional does not
  have to be constructed anew on the source side.  It is the canonical finite part of Connes's
  semilocal cutoff trace, equivalently the trace pairing of the factorization-independent
  quantized-differential class.  The remaining Sonin theorem is a comparison/descent theorem for
  this already fixed class, followed by positivity.

## Semilocal finite part

Let `S` be a finite set of places of `Q` containing the archimedean place, let
`C_(Q,S)` be the corresponding semilocal idele-class group, and let `f` be a compactly supported
Schwartz test on that group.  In Connes's notation, `vartheta_a(f)` is the scaling action and
`R_Lambda` is the product of the infrared and Fourier-conjugate ultraviolet cutoffs.  The
semilocal trace formula is

```text
Tr(vartheta_a(f) R_Lambda)
  =2 f(1) log Lambda + sum_(v in S) W_v(f) + o(1).          (1)
```

Consequently the finite part

```text
FP_S(f)
 :=lim_(Lambda->infinity)
     (Tr(vartheta_a(f)R_Lambda)-2 f(1)log Lambda)           (2)
```

exists and satisfies

```text
FP_S(f)=sum_(v in S) W_v(f).                               (3)
```

This is an unconditional source theorem.  It contains no Xi divisor, zero-location hypothesis,
limiting zero measure, or RH assumption.

After the standard critical-line normalization, the nonarchimedean term is

```text
W_p(h)
 =log(p) sum_(m>=1) p^(-m/2)
    (h(p^m)+h(p^(-m))).                                    (4)
```

Thus the positive `p^m` mode has coefficient

```text
log(p) p^(-m/2)
 = [p^(-m/2)/m] [m log(p)].                                (5)
```

The first bracket in `(5)` is exactly the unsquared Euler-logarithm coefficient used by the
formal semilocal Sonin carrier, and the second is the required orbital response
`log(p^m)`.  Therefore the source functional already has the response that the fixed
Hilbert--Schmidt projection-correction pairing was unable to produce.

## Cyclic representative and factorization independence

Let `F_H=2P-1` be the Hardy polarization and let `U` be an invertible boundary multiplier.  Put

```text
delta(U)=[F_H,U],
omega(U)=U^(-1)delta(U).                                   (6)
```

For commuting or noncommuting invertible multipliers alike, the Leibniz rule gives

```text
omega(UV)=V^(-1)omega(U)V+omega(V).                        (7)
```

Modulo conjugation coboundaries `V^(-1)TV-T`, equation `(7)` is additive.  Hence a finite
Gauss splitting of the archimedean ratio and its pairing with the finite-prime ratios produce one
canonical coinvariant class, independent of the chosen factorization.  Whenever a commuting test
smoothing makes the local terms trace class, ordinary trace invariance kills the conjugation
coboundaries and yields

```text
Tr(A omega(product_j U_j))
  =sum_j Tr(A omega(U_j)).                                 (8)
```

Connes's semilocal calculation identifies `(8)` with `(3)`.  Thus the cutoff finite part, the
quantized-differential class, the additive local Weil source, and the position-commutator orbital
length are four representatives of the same degree-one source datum.

## Forced survival beyond the Hilbert--Schmidt correction

Let `b_(p,m)=p^(-m/2)/m`.  Factoring out this nonzero coefficient from the prime term leaves the
response

```text
r_(p,m)=m log(p).                                          (9)
```

Along powers of any fixed prime, `(9)` is unbounded.  By the formal theorem
`not_soninSemilocalFluxNormalization`, the response of the fixed Sonin
projection-correction/Hilbert--Schmidt pairing is uniformly bounded in `(p,m)`.  Therefore no
source comparison preserving `(3)` can send the Connes class entirely into that pairing.  In the
quotient of prime-power response functionals by uniformly bounded responses, the Connes class is
nonzero.

This is the positive content of the earlier bounded-response no-go:

```text
the degree-one orbital class must survive in
  the noncompact conductor boundary channel
  or the internal cutoff trace-defect cocycle
  (and generally in their canonical sum).                 (10)
```

The positive trace-class residual energy and the fixed Hilbert--Schmidt correction may accompany
this class, but they cannot replace it.

## The exact-aperture semilocal Sonin carrier and its source connection already exist

Connes--Consani's quasi-inner theorem supplies the Hardy-kernel carrier

```text
S_S=ker((u_S)_(22)),
u_S=rho_infinity product_(p in S_f)rho_p.                 (10a)
```

The later Connes--Consani--Moscovici theorem is stronger than an abstract injection.  For every
finite `S` containing infinity and every aperture `lambda>0`, their explicit place map is a
Hilbertian isomorphism

```text
theta_S:S_lambda(R,e_infinity) ~= S_lambda(X_S,alpha),    (10b)
```

it intertwines Fourier transforms, and both sides map to the same de Branges space `B_lambda`.
Thus the carrier comparison is closed aperture by aperture.

Moreover, in raw Mellin coordinates,

```text
U_S theta_S U_infinity^(-1)=M_(g_S),
g_S(t)=product_(p in S_f)L_p(1/2+i t)^(-1).               (10c)
```

The companion theorem
`semilocal-dual-pair-euler-connection-source-law.md` differentiates this exact formula on its
common Sobolev core and proves

```text
theta_S^(-1)D_S theta_S-D_infinity
  =M_(-sum_(p in S_f)L_p'/L_p).                           (10d)
```

The right side has precisely the finite von Mangoldt coefficients.  Hence neither the carrier,
the place comparison, nor the finite prime source transport remains to be invented.  What is not
yet transported is the cyclic **finite part after Sonin cutoff/compression**, together with its
one-sided completed sign.

## Sharpened open theorem

The phrase "construct the genuine semilocal relative trace" is too broad.  Equations `(1)`--`(8)`
already construct and normalize the source functional.  What is not yet proved is its descent to
the exact Sonin principal--relative carrier.

The remaining comparison theorem is to place the already explicit connection `(10d)`, for finite
`S` and Sonin aperture `a`, on a cutoff-compatible common graph representative

```text
Phi_(S,a) : Euler connection (theta_S^(-1)D_S theta_S-D_infinity)
              -> exact Sonin three-grade extension E_a                 (11)
```

and a relative functional `tau_(S,a)` on its image such that

```text
tau_(S,a)(Phi_(S,a)(f))=FP_S(f),                            (12)
```

with the following structural compatibility:

1. the principal image retains the finite prime-character quotient in the Calkin symbol;
2. the degree-one image of `omega` is the internal trace-defect cocycle plus the polarized
   Burnol-conductor/Euler leakage cross;
3. the quadratic image is the already formalized positive trace-class Sonin residual energy;
4. the comparison is compatible with aperture restriction and preserves the relevant negative
   index or source lower floor.

The Burnol reflection theorem and its exact prolate-resolvent dressing already make the conductor
leakage bounded on the correct common graph.  The open content of `(11)`--`(12)` is therefore the
preservation of the cyclic finite part under cutoff/resolvent descent and a one-sided positivity
estimate, not construction of a carrier, place map, local functional, or orbital factor.

## Top-down chain

```text
Connes semilocal cutoff trace formula
  -> canonical finite-part prime--Gamma source FP_S
  -> factorization-independent cyclic orbital class with response log(p^m)
  -> exact theta_S Euler connection with the same von Mangoldt coefficients
  -> [OPEN] cutoff/resolvent cyclic descent to the Sonin principal--relative graph
  -> [OPEN] completed source contraction or uniform lower floor
  -> existing completed prime--Gamma source criterion
  -> RH.                                                     (13)
```

This strictly narrows the open interface.  Any proposed construction can now be tested against
the exact equality `(12)`; merely producing some relative trace with plausible coefficients is no
longer sufficient.

## Literature

- A. Connes, [*Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*](https://arxiv.org/abs/math/9811068).
- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368),
  especially the semilocal cutoff formula and quantized-differential local decomposition.
- A. Connes and C. Consani,
  [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974).
- A. Connes, C. Consani, and H. Moscovici,
  [*Zeta zeros and prolate wave operators: semilocal adelic operators*](https://arxiv.org/abs/2310.18423),
  especially Propositions 4.6--4.8 and Theorem 4.6.
- J.-F. Burnol, [*The Explicit Formula and the conductor operator*](https://arxiv.org/abs/math/9902080).

## Lean decision

The source finite-part theorem and the unbounded connection theorem are analytic statements, while
the Lean tree currently contains the bounded multiplier square but not the closed derivative core
or the semilocal adele-class cutoff representation.  Formalizing only the scalar logarithmic
derivative would not certify `(11)`--`(12)`.  No Lean file is added until the common-core connection
and its cutoff/resolvent relative graph are formalized together.

## Gates

- [x] 0 -> 1: source-pure finite-part trace and comparison target identified
- [x] 1 -> 2: semilocal finite part imported from the proved trace formula
- [x] exact prime-power orbital response extracted
- [x] cyclic/factorization-independent representative identified
- [x] bounded Hilbert--Schmidt scalarization excluded as the complete representative
- [x] Burnol conductor graph available for the noncompact boundary channel
- [x] exact aperture-by-aperture semilocal/classical Sonin isomorphism
- [x] exact Euler connection source transport under `theta_S`
- [ ] construct the cutoff/resolvent cyclic descent `(11)`
- [ ] prove finite-part preservation `(12)`
- [ ] prove completed contraction or uniform source lower floor
- [ ] preserve aperture index and prove RH
