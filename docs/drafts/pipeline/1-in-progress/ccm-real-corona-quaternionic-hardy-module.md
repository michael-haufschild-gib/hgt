# Real-corona quaternionification of the CCM Hardy module

- **ID:** `ccm-real-corona-quaternionic-hardy-module`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HARDY-MODULE REAL DESCENT THEOREM
- **Label:** `CCM_REAL_CORONA_QUATERNIONIC_HARDY_MODULE`
- **Parents:** CCM cyclic `H^1`, Meyer spectral realization, Paugam spectral symmetries,
  Hardy inner--outer factorization, Carleson's corona theorem
- **Scientific status:** `[CONJECTURE] [NOVELTY UNDER AUDIT] [NOT AN RH PROOF]`
- **Statement:** the real-zero-free scalar CCM character sector has a canonical bounded
  quaternionic structure after its natural Hardy globalization; a real spectral fixed point is
  the exact obstruction to such a structure on a cyclic scalar Hardy module.

## 1. Exact analytic object

Let

```text
S = {s in C : 0 < Re s < 1},
f#(s) = conjugate(f(conjugate(s))).
```

Let `L` be a completed scalar self-dual `L`-function whose nontrivial divisor in `S` is discrete,
stable under `#`, has no boundary zeros, and satisfies the strip Blaschke condition.  Let `B` be
the Blaschke inner factor of that divisor in `H-infinity(S)`.  Put

```text
Q_B = H^2(S) / B H^2(S).
```

The involution `#` descends antiunitarily to `Q_B`.  Multiplication by `a^s`, `a>0`, gives the
scaling action.

For the completed Riemann zeta function, `B` has no real fixed zero in `S`.  Write

```text
B = B_+ B_-,
```

where `B_+` and `B_-` contain the zeros with positive and negative imaginary part respectively,
with multiplicity and `B_- = B_+#` after unimodular normalization.

## 2. Main conjecture

`[CONJECTURE] [CCM_REAL_CORONA_QUATERNIC_HARDY_MODULE]`

### A. Corona separation and canonical idempotent

The pair `(B_+,B_-)` is a corona pair:

```text
inf_(s in S) (|B_+(s)| + |B_-(s)|) > 0.                       (1)
```

Hence there are `u,v in H-infinity(S)` with

```text
u B_+ + v B_- = 1.                                           (2)
```

The class

```text
e = [v B_-] in H-infinity(S) / B H-infinity(S)               (3)
```

is independent of the Bezout solution and is the unique class satisfying

```text
e = 1 mod B_+,     e = 0 mod B_-.
```

It obeys

```text
e^2=e,     e#=1-e.                                           (4)
```

Thus Paugam's upper/lower spectral choice becomes a canonical bounded module projector on `Q_B`,
not a noncanonical algebraic eigenspace decomposition.

The quotient maps give a bounded topological Chinese-remainder isomorphism

```text
Q_B  ->  Q_(B_+) direct_sum Q_(B_-),
[f]  |-> ([f] mod B_+, [f] mod B_-),                           (4a)
```

whose inverse is written with any Bezout solution from `(2)`.  In `(4a)`, `e` is `(1,0)` and `#`
exchanges the two summands antiunitarily.  Therefore the equivalent Hilbert norm transported from
the orthogonal direct sum is independent of the Bezout lift and makes the quaternionic operator
below antiunitary.

### B. Quaternionic multiplier

Put `m=2e-1` in the quotient multiplier algebra and define

```text
J([f]) = m [f#].                                             (5)
```

Then `J` is bounded, anti-linear, invertible, and

```text
J^2=-1,                                                      (6)
J(a^s x)=a^s J(x)  for every a>0.                            (7)
```

On every generalized zero packet, `(5)` agrees with Paugam's sign--conjugation.  Its construction
is independent of every corona lift; only the canonical quotient class `(3)` remains.

### C. Oriented `K_0` class and cyclic character

Put `A_B=H-infinity(S)/B H-infinity(S)`.  The central idempotent defines

```text
kappa_B = [e] - [1-e] in K_0(A_B).                            (8)
```

This class has infinite order and is anti-Real:

```text
kappa_B# = -kappa_B.                                         (9)
```

Evaluation at any upper zero sends `kappa_B` to `1 in K_0(C)=Z`, while evaluation at any lower
zero sends it to `-1`; hence it cannot vanish.  For a compactly supported smooth convolution
symbol `h`, define the continuous cyclic `0`-cocycle

```text
tau_h([a]) = sum_(B(rho)=0) ord_rho(B) hhat(rho) a(rho).      (10)
```

Absolute convergence follows from vertical Schwartz decay of `hhat` and the standard zero-counting
bound.  The degree-zero Chern character of `kappa_B` is `2e-1`, so

```text
<tau_h, ch_0(kappa_B)>
  = sum_(Im rho>0) m_rho hhat(rho)
    - sum_(Im rho<0) m_rho hhat(rho).                         (11)
```

Thus the upper/lower sign is a nonzero Chern--Connes pairing on the Hardy globalization, rather
than a chosen grading of a zero-indexed vector space.

### D. Fixed-point obstruction

Let `B_0` be any scalar Real Blaschke divisor in `S`.  If `B_0` has a real zero, then no bounded
anti-linear operator `J` on `Q_(B_0)` can satisfy simultaneously

```text
J(hx)=h# J(x) for all h in H-infinity(S),
J^2=-1.                                                      (12)
```

Indeed a real maximal ideal gives a one-dimensional `#`-fixed simple quotient; `(12)` would induce
a conjugate-linear endomorphism of a complex line squaring to `-1`, which is impossible.  Therefore
the real-zero-free condition is necessary.  Together with A--B it is sufficient whenever the two
nonreal halves form a corona pair.

For an arithmetic divisor with real zeros, do not discard the obstructing sector.  Factor

```text
B_0 = B_+ B_R B_-,                                         (12a)
```

where `B_R` is the finite Blaschke product of real zeros.  The three factors are a corona family,
so topological Chinese remainder gives canonical central idempotents `e_+,e_R,e_-` with

```text
e_+ + e_R + e_- = 1,
e_+#=e_-,       e_R#=e_R.                                  (12b)
```

The classes

```text
kappa_(B_0) = [e_+] - [e_-],
delta_(B_0) = [e_R]                                         (12c)
```

are respectively anti-Real and Real in `K_0(A_(B_0))`.  Evaluation proves

```text
delta_(B_0)=0  <=>  B_R=1  <=>  B_0 has no real zero.       (12d)
```

Moreover

```text
J_0(x)=(e_+-e_-)x#,
J_0^2=-(1-e_R),                                             (12e)
```

so `J_0` is quaternionic exactly on the canonical nonreal summand and vanishes on the canonical
real obstruction summand.  For the cyclic cocycle `(10)`,

```text
<tau_h,ch_0(delta_(B_0))>
  = sum_(rho real) m_rho hhat(rho).                         (12f)
```

Thus Paugam's removed polynomial is recovered as a nonzero Real `K_0` defect with its complete
cyclic character.  The no-go theorem has a positive survivor even when a full `J` is impossible.

### E. CCM Hardy globalization and spectral-character compatibility

In the trivial compact-character sector over `Q`, Mellin transform gives the CCM/Meyer quotient

```text
M_zeta = H_- / closure(Z H_cap).
```

Its Hardy seminorm completion is canonically `Q_B`: the completed Poisson--Muntz multiplier has
inner factor `B`, its outer factor has dense range, and compactly supported logarithmic test
functions are dense in `H^2(S)`.  The induced map

```text
M_zeta -> Q_B                                               (13)
```

has dense range, is scaling equivariant, and intertwines convolution multipliers.  For every
finite divisor packet, the induced finite-dimensional multiplier trace is the sum of the Mellin
symbol over the packet, with zero multiplicity, and therefore agrees with the corresponding finite
part of Meyer's spectral character.  Passing through the directed family of packets recovers the
same absolutely convergent spectral distribution for compactly supported smooth convolution
symbols.  This is distributional character compatibility; it is **not** a claim that every such
multiplier becomes trace class on the Hilbert completion `Q_B`.

More precisely, if `A_phi` denotes compression of an analytic multiplier to the model-space
realization of `Q_B`, then the Lopatto--Rochberg criterion gives

```text
A_phi is trace class  <=>  C_B phi belongs to analytic Besov B_1,      (14)
```

where `C_B` is the canonical model-space conjugation.  Schwartz decay of `phi` on vertical lines
does not by itself prove `(14)`, because `C_B` contains the full oscillatory inner factor `B`.
No Hilbert trace is used unless `(14)` is verified for the individual symbol.

## 3. Dependency-closed proof dossier

### 3.1 Arithmetic divisors satisfy a two-ended Blaschke estimate

Use the conformal coordinate

```text
w=exp(pi i s): S -> upper half-plane H.
```

If `rho=beta+i gamma`, write `a_rho=exp(pi i rho)`.  Then

```text
|a_rho|=exp(-pi gamma),
a_(conjugate rho)=1/conjugate(a_rho).                         (15)
```

For a completed finite-degree `L`-function, the standard zero-counting estimate

```text
N(T)=O(T log(2+T))                                           (16)
```

implies, by grouping zeros in unit-height shells,

```text
sum_(gamma>0) |a_rho| + sum_(gamma<0) |a_rho|^(-1) < infinity. (17)
```

Real zeros in `S` form a finite divisor.  After removing them, discreteness and nonvanishing on
the two finite boundary segments give a number `gamma_0>0` such that every remaining zero has
`|gamma|>=gamma_0`.  Put `r=exp(-pi gamma_0)<1`.  Thus upper zeros satisfy `|a_rho|<=r`, lower
zeros satisfy `|a_rho|>=r^(-1)`, and real zeros satisfy `|a_rho|=1`.

Let

```text
b_a(w)=(w-a)/(w-conjugate(a))
```

up to the harmless unimodular normalization.  Its modulus obeys

```text
1-|b_a(w)|^2 = 4 Im(w) Im(a) / |w-conjugate(a)|^2.           (18)
```

For an upper zero `|a|<=r` and `|w|>=1`,

```text
|b_a(w)| >= (1-r)/(1+r),
1-|b_a(w)|^2 <= 4|a|/(1-r)^2.                               (19)
```

Because of `(17)`, `-log|b_a(w)|` is uniformly summable on `|w|>=1`; hence there is `c_+>0` with

```text
|B_+(w)|>=c_+  when |w|>=1.                                 (20)
```

The inverted estimate for a lower zero `|a|>=r^(-1)` and `|w|<=1` gives `c_->0` with

```text
|B_-(w)|>=c_-  when |w|<=1.                                 (21)
```

At every `w in H`, either `(20)` or `(21)` applies.  Therefore

```text
inf_H (|B_+|+|B_-|) >= min(c_+,c_-) > 0.                    (22)
```

This proves the corona assertion `(1)` without RH, zero separation inside either half, or a
numerical lower bound for the first zero.

If `B_R` is the finite product of real-zero factors, then `(B_+,B_R)` and `(B_R,B_-)` are also
corona pairs.  Indeed a finite Blaschke product can be small only in finitely many compact
pseudohyperbolic neighborhoods of its zeros; the opposite product is continuous and nonzero on
their closures, while `B_R` is bounded below off those neighborhoods.  Thus `(B_+,B_R,B_-)` is a
corona family and its three principal ideals are pairwise comaximal.

For Riemann's completed `xi`, `(16)` is classical and there are no real zeros in `S`: for
`0<s<1`, the alternating eta representation gives `eta(s)>0` and
`zeta(s)=eta(s)/(1-2^(1-s))<0`.  Hence `B_R=1` for `xi`.

### 3.2 Algebraic and Hilbert-module Chinese remainder

Let `U,V` be inner functions that form a corona pair, and choose `p,q in H-infinity(S)` with

```text
pU+qV=1.                                                     (23)
```

The ideals `UH-infinity` and `VH-infinity` are comaximal and their intersection is
`UVH-infinity`.  The latter equality follows either from inner divisibility or directly by
dividing a function carrying both relatively prime inner factors.  Therefore

```text
H-infinity/(UV) -> H-infinity/(U) x H-infinity/(V)           (24)
```

is an algebra isomorphism.  Its inverse sends `([f],[g])` to

```text
[qV f + pU g].                                               (25)
```

The same formulas act boundedly on Hardy quotients.  Inner divisibility gives

```text
UH^2 intersect VH^2 = UVH^2,                                (26)
```

and `(25)` proves surjectivity, so

```text
Q_(UV) -> Q_U direct_sum Q_V                                (27)
```

is a bounded isomorphism of Hilbert modules.  The open mapping theorem makes its inverse bounded.
Iterating proves the triple version for `B_+ B_R B_-`.

Under `(24)`, the unique idempotent with residues `(1,0)` is `e=[qV]`.  This proves independence
from `(23)`, `e^2=e`, and uniqueness in `(3)`--`(4)`.  The Real involution exchanges the two residue
components, so `e#=1-e`.  Under `(27)`, `#` exchanges `Q_(B_+)` and `Q_(B_-)` antiunitarily.
Consequently

```text
||x||_CRT^2=||x mod B_+||^2+||x mod B_-||^2                 (28)
```

is an equivalent, Bezout-independent Hilbert norm on `Q_B`.

### 3.3 Quaternionic operator

Let `gamma([f])=[f#]` and `m=2e-1`.  From `e^2=e` and `e#=1-e`,

```text
m^2=1,      m#=-m.                                          (29)
```

Therefore

```text
(m gamma)^2 x = m m# x = -x.                               (30)
```

This proves `(5)`--`(6)`.  In CRT coordinates, `m=(1,-1)`, so `m gamma` is antiunitary for `(28)`.
For `a>0`, `(a^s)#=a^s`; semilinearity gives `(7)`.

For the triple decomposition, set `m_0=e_+-e_-`.  Equations `(12b)` give

```text
m_0#=-m_0,      m_0^2=e_++e_-=1-e_R,                       (31)
```

and hence `(12e)`.

### 3.4 `K_0`, cyclic characters, and the real-zero survivor

Evaluation at a zero `rho` descends to a unital homomorphism

```text
ev_rho:A_B -> C.                                             (32)
```

For an upper zero, `(ev_rho)_*(kappa_B)=1 in K_0(C)=Z`; for a lower zero it is `-1`.  Thus
`kappa_B` has infinite order.  Since `e#=1-e`, functoriality gives `(9)`.  In the triple
decomposition, evaluation at a real zero sends `delta_(B_0)=[e_R]` to `1`; if no real zero exists,
`e_R=0`.  This proves `(12d)`.

Let `h in C_c^infinity(R_+^*)`.  Repeated integration by parts in the logarithmic coordinate shows
that its Mellin transform is rapidly decreasing, uniformly for `0<=Re(s)<=1`.  Combining this with
`(16)` gives

```text
sum_rho m_rho |hhat(rho)| < infinity.                        (33)
```

For `[a] in A_B`,

```text
|tau_h([a])| <= ||[a]||_quotient sum_rho m_rho |hhat(rho)|. (34)
```

Thus `(10)` is a continuous functional.  Since `A_B` is commutative, it is a continuous cyclic
`0`-cocycle.  The degree-zero Chern character sends an idempotent to its class modulo commutators;
therefore

```text
ch_0(kappa_B)=e-(1-e)=2e-1,      ch_0(delta_(B_0))=e_R.      (35)
```

Substitution of the residue values of the idempotents proves `(11)` and `(12f)`.

### 3.5 Fixed-fiber obstruction

Let `lambda in (0,1)` be a real zero and let `b_lambda` be its strip Blaschke factor, normalized so
that `b_lambda#` is a unimodular multiple of `b_lambda`.  Evaluation gives a nonzero quotient

```text
ev_lambda:Q_(B_0) -> C.                                     (36)
```

Its kernel is `b_lambda Q_(B_0)`: division by an interior Blaschke factor preserves `H^2`.  If a
bounded anti-linear `J` obeys the semilinearity in `(12)`, this kernel is `J`-stable.  Hence `J`
induces a conjugate-linear map `j` on the one-dimensional quotient `(36)`.  Every such map is
`j(z)=c conjugate(z)` and satisfies

```text
j^2(z)=|c|^2 z,                                               (37)
```

never `-z`.  This contradicts `J^2=-1`.  Higher zero multiplicity does not evade the argument:
the simple evaluation quotient `(36)` remains.  This proves necessity.  Sections 3.1--3.3 prove
sufficiency when the real divisor is empty and prove the exact partial survivor when it is not.

### 3.6 Source-dense CCM/Meyer Hardy globalization

Use Mellin convention

```text
M f(s)=integral_0^infinity f(x)x^s dx/x.                     (38)
```

In logarithmic coordinate `x=exp(y)`, Plancherel identifies `H^2(S)` with Fourier--Laplace
transforms of the weighted space

```text
L^2(R, max(1,exp(2y)) dy).                                  (39)
```

The two norms are equivalent; the boundary norms at `Re(s)=0,1` give the two weights.  In
particular, transforms of `C_c^infinity(R)` are dense in `H^2(S)`.

The Mellin transforms of `H_-` contain this dense subspace.  For `H_cap`, compactly supported
logarithmic functions must additionally satisfy the single moment

```text
integral_R exp(y)g(y)dy=0.                                  (40)
```

That kernel is still dense in `(39)` because the moment is not continuous there.  Explicitly, fix
`psi in C_c^infinity((0,1))` with integral `1` and put

```text
q_n(y)=exp(-y)n^(-1) psi((y-R)/n).                           (41)
```

Then the moment of `q_n` is `1`, while its `(39)` norm is `O(n^(-1/2))`.  Subtracting the moment
of any compactly supported `g` times `q_n` proves density of `(40)`.  Even extension back to the
additive real line lies in `H_cap`, since support stays away from zero.

Put

```text
G(s)=1/2 s(s-1) pi^(-s/2) Gamma(s/2),
xi(s)=G(s) zeta(s).                                         (42)
```

Uniform Stirling estimates and standard vertical-strip bounds show `G,xi in H-infinity(S)`.
They extend holomorphically across every finite boundary point.  Their logarithmic growth at the
two ends of the strip rules out endpoint singular-inner atoms as follows.  After
`w=exp(pi i s)`, finite boundary continuation forces any singular measure to be supported at
`w=0` or `w=infinity`.  A positive atom there contributes along the central ray a factor whose
logarithmic modulus is `-c exp(pi |t|)`.  For `G`, Stirling gives instead a finite linear asymptotic
in `|t|`.  For `xi`, the Hardy--Littlewood mean-square theorem supplies an unbounded sequence of
heights on which `|zeta(1/2+it)|` is at least polynomially large; Stirling then again gives
`log|xi(1/2+it)|=-pi|t|/4+O(log|t|)` on that sequence.  Both contradict a positive endpoint atom.
Since `G` is zero-free in `S`, it is outer.  Since the zeros of `xi` are exactly the nontrivial zeta
zeros, its inner factor is exactly `B`:

```text
xi=B O,       G and O outer.                                (43)
```

Define

```text
U:H_- -> H^2(S),      U(f)=G M f.                            (44)
```

Sections `(39)`--`(43)` imply that `U(H_-)` is dense.  For `f in H_cap`, Poisson--Muntz summation
gives

```text
U(Zf)=G zeta M f=xi M f.                                    (45)
```

The density following `(41)` and outer density in `(43)` give

```text
closure(U(ZH_cap))=B H^2(S).                                (46)
```

Therefore the quotient of `(44)` factors through the source-defined cyclic quotient
`M_zeta=H_-/Z(H_cap)` and has dense range in `Q_B`.  Its quotient norm is a seminorm on `M_zeta`,
and the separated Hilbert completion is exactly `Q_B`.  Scaling sends `M f(s)` to `a^s M f(s)`, so
the map is scaling equivariant; Mellin convolution becomes analytic multiplication, so it also
intertwines convolution multipliers.  This proves the source claim in `(13)` without defining the
source by its zero divisor.

### 3.7 Finite packets and the global spectral character

For a finite sub-divisor `F` of `B`, let `B_F` be its finite Blaschke product.  The quotient
`Q_(B_F)` has dimension `deg(F)`.  In the evaluation-jet filtration, analytic multiplication by
`phi` is upper triangular with `phi(rho)` repeated `m_rho` times.  Hence

```text
Tr(M_phi|Q_(B_F))=sum_(rho in F) m_rho phi(rho).             (47)
```

For `phi=hhat`, `(33)` makes `(47)` absolutely convergent over the directed family of finite
sub-divisors.  Its limit is Meyer's spectral character on the original nuclear quotient.  Inserting
`2e-1` or `e_R` gives `(11)` or `(12f)`.  No Schatten conclusion on `Q_B` enters this argument;
Lopatto--Rochberg gives the separate exact criterion `(14)`.

Sections 3.1--3.7 prove A--E modulo only the cited standard Hardy factorization, Carleson corona,
and Meyer/CCM source theorems.  None of these inputs assumes RH.

## 4. Proof plan

1. Prove boundedness of completed `xi` on the full strip and its canonical inner--outer
   factorization, including absence of a singular inner factor.
2. Map `S` conformally to the upper half-plane by `w=exp(pi i s)`.  Upper zeros lie in a fixed
   inner semicircle and lower zeros outside a fixed outer semicircle.  Uniform Blaschke-product
   estimates on `|w|>=1` and `|w|<=1` prove `(1)`.
3. Apply Carleson's corona theorem, prove algebraic and topological Chinese remainder, and derive
   `(4)`--`(7)` in the quotient multiplier algebra.
4. Prove the `K_0` nonvanishing and the cyclic pairing `(8)`--`(11)`.
5. Prove D from the fixed real evaluation quotient, including generalized multiplicity packets;
   prove triple corona and the defect identities `(12a)`--`(12f)` instead of deleting real zeros.
6. Construct `(13)` from the actual CCM degree-zero trace quotient, not from a zero-indexed ambient
   space.  Prove the range-closure identity by inner--outer factorization and source density.
7. Prove finite-packet trace compatibility from the Cauchy-jet filtration, then use Meyer's nuclear
   trace theorem only on the original nuclear quotient to identify the directed spectral character.
   Keep Hilbert trace class separate and governed by `(14)`.

## 5. Hostile audit and falsifiers

- Paugam already constructs sign--conjugation on a discrete spectral suspension.  Repeating that
  construction is not new.  Load-bearing novelty is bounded, canonical quotient-module descent.
- Hardy/model-space and Blaschke range calculations already occur in the corpus.  They do not
  prove `(1)`--`(8)` or the Real fixed-point classification.
- Spectrum alone is insufficient.  A quasinilpotent radical or failure of the range-closure
  identity in D invalidates the CCM claim.
- A corona lift is noncanonical.  Only its unique class modulo `B` may enter the theorem.
- Meyer's nuclear trace class does not automatically survive a Hilbert completion.  Any assertion
  of a global Hilbert trace without the Besov condition `(14)` invalidates the proof.
- `J^2=-1` supplies Real/KR parity, not positivity.  Paugam's form `psi(x,Jx)>0` remains
  RH-equivalent and is not claimed.
- A proof that merely removes real zeros is incomplete.  It must retain `delta_(B_0)` and its
  cyclic character `(12f)` as the exact positive survivor of the obstruction.
- If upper/lower Blaschke factors are not a corona pair, A--B fail even without real zeros.
- If `(13)` is only a divisor-defined quotient with no dense source map, the CCM application is
  theatre and must be removed.

## 6. Novelty boundary

- Meyer and CCM construct the nuclear cyclic quotient and its trace formula.
- Paugam constructs the alternating pairing and a noncanonical upper/lower spectral splitting;
  real zeros are explicitly removed.
- Standard Hardy theory supplies Blaschke factorization, model spaces, and the corona theorem.
- The proposed new theorem is the Real Chinese-remainder/corona synthesis: canonical bounded
  quaternionification, nonzero anti-Real `K_0` class with explicit cyclic pairing, exact
  real-fixed-point `K_0` defect with its surviving cyclic character, and source-dense,
  spectral-character-compatible CCM globalization.

### 6.1 Primary-source audit, 2026-08-03

- Paugam, arXiv:0803.0199, page 3, explicitly calls
  `V=V_+ direct_sum V_- direct_sum V_0` noncanonical, removes the real divisor by `P_K`, and then
  writes `C=diag(1,-1)c`.  It contains no Hardy quotient, corona idempotent, `K_0` class, or
  retained real-zero cyclic character.
- Connes--Consani, arXiv:2207.10419, identifies the adelic trace map in `HH_0` and constructs a
  Hilbert quotient for critical-line zeros over the Scaling Site.  It neither globalizes all strip
  zeros into `Q_B` nor constructs the upper/lower idempotent or real-zero defect.
- Connes--Consani--Moscovici, arXiv:2511.22755, constructs finite self-adjoint zeta spectral triples
  and leaves convergence to the complete zeta spectrum open.  It contains no corona, quaternionic,
  or `K_0` construction of the type above.
- Lopatto--Rochberg, arXiv:1410.1906, Theorem 1, characterizes analytic truncated Toeplitz
  Schatten membership by a Besov condition.  It supplies the falsifier `(14)`, not the arithmetic
  idempotent or cyclic pairing.
- Searches across arXiv for the combinations `zeta zeros + K_0 + cyclic homology`, `real symmetric
  inner function + quaternionic model space`, and `corona idempotent + zeta` found no construction
  matching `(3)`--`(13)`.  This is evidence of novelty, not a proof of bibliographic completeness;
  journal submission still requires expert literature review.

## 7. Lean target after paper proof

No Lean work begins before A--E are dependency-closed on paper.  The exact formal target is the
quotient-algebra theorem:

```text
e^2=e, e#=1-e  =>  J(x)=(2e-1)*x# satisfies J^2=-x,
```

together with the fixed-line obstruction and module/scaling intertwining.  Analytic existence of
`e` must be proved in the paper and may not be encoded as an axiom or opaque structure field.

## Gates

- [x] 0 -> 1: exact conjecture and falsifiers recorded
- [ ] A: corona separation proved
- [ ] B: canonical quaternionic multiplier proved
- [ ] C: anti-Real `K_0` class and cyclic pairing proved
- [ ] D: fixed-real-zero iff `K_0` obstruction and positive survivor proved
- [ ] E: source-dense CCM Hardy globalization and spectral-character compatibility proved
- [ ] external novelty audit complete
- [ ] hostile paper review passes general-renowned-journal threshold
- [ ] central algebraic theorem formalized unconditionally in Lean
