# Gamma-six shell Green principal class and singular Stokes transgression

- **Stage:** 3 — formalised in Lean 4
- **Route:** L — Deninger/Green/Hodge source descent
- **Status:** [FORMALIZED] [PROJECT-SPECIFIC SYNTHESIS] [PRIORITY UNVERIFIED] [NOT RH]
- **Date:** 2026-08-11
- **Exact advance:** the full corrected Gamma-six Möbius source, after canonical countertransport
  and tensor square, has a nonzero weak-trace principal class modulo trace class. Its shell Wold
  compression obeys the critical coface relation modulo trace class, and the associated Gibbs
  reader is exactly the existing physical BV/Deninger radial coefficient. The only finite
  source-valued differential annihilating both orientations is classified and shown to be an
  adaptive, character-dependent annihilator. Thus the remaining Route-L theorem is a strict
  comparison preserving this concrete trace-ideal class, not construction of a source object or
  another local coface.

## 1. Corrected source and countertransported tensor square

Let \(\mathcal H\) be the Hilbert source, let \(U_t\) be its unitary dilation group, and let
\(0\ne\Theta\in\mathcal H\). For \(m\ge3\), the corrected Gamma-six source is

\[
 H_m=\sum_{n\ge6}\mu(n)n^{-m/2}U_{-m\log n}\Theta.
\tag{1}
\]

Countertransport the first surviving atom to a fixed direction:

\[
 Y_m:=U_{m\log6}H_m
 =6^{-m/2}\Theta+Z_m,
\tag{2}
\]

where, with \(\alpha=m/2\),

\[
 \|Z_m\|
 \le \|\Theta\|\sum_{n\ge7}n^{-\alpha}
 \le \|\Theta\|7^{-\alpha}
       \left(1+\frac7{\alpha-1}\right)
 =:\varepsilon_m.
\tag{3}
\]

Put \(v=\Theta\otimes\Theta\ne0\) and

\[
 W_m:=Y_m\otimes Y_m=6^{-m}v+E_m.
\tag{4}
\]

Then

\[
 \|E_m\|
 \le 2\,6^{-m/2}\|\Theta\|\varepsilon_m+\varepsilon_m^2.
\tag{5}
\]

### Theorem 1.1 — trace-order remainder

The full source remainder satisfies

\[
 \boxed{\sum_{m\ge3}6^m\|E_m\|<\infty.}
\tag{6}
\]

### Proof

Substitute (3) into (5). The first contribution to (6) is bounded by a constant times

\[
 \sum_{m\ge3}
 \left(\frac67\right)^{m/2}
 \left(1+\frac7{m/2-1}\right),
\]

and the second by a constant times

\[
 \sum_{m\ge3}
 \left(\frac67\right)^m
 \left(1+\frac7{m/2-1}\right)^2.
\]

Both converge geometrically. This proves (6). ∎

Equation (6) is stronger than the norm asymptotic
\(\|W_m\|/(6^{-m}\|v\|)\to1\): it controls the whole corrected source at trace order after
ordinary-integer shell replication.

## 2. Ordinary-integer shell amplification

For \(m\ge3\), let

\[
 I_m=\{k\in\mathbb N:6^m\le k<6^{m+1}\},
 \qquad |I_m|=5\cdot6^m,
\tag{7}
\]

and let \(\mathscr L_6=\ell^2(\coprod_{m\ge3}I_m)\). For a sequence
\(X=(X_m)_{m\ge3}\) in a Hilbert space \(K\), define the rectangular shell amplification

\[
 \mathcal A_6(X)e_k=X_m\otimes e_k,
 \qquad k\in I_m.
\tag{8}
\]

The singular values of \(\mathcal A_6(X)\) are \(\|X_m\|\), each repeated
\(5\cdot6^m\) times. In particular,

\[
 \|\mathcal A_6(X)\|_1
 =5\sum_{m\ge3}6^m\|X_m\|
\tag{9}
\]

whenever the right side is finite.

Let \(G_6\) be the shell reciprocal Green operator

\[
 G_6e_k=6^{-m}e_k,qquad k\in I_m.
\tag{10}
\]

It is the stepwise ordinary-integer model of \(Qe_k=k^{-1}e_k\); on every shell,

\[
                         Q\le G_6\le6Q.
\tag{11}
\]

### Theorem 2.1 — full-source weak-trace principal class

Let \(\mathcal W=\mathcal A_6((W_m)_m)\) and let
\(\mathcal G_v=\mathcal A_6((6^{-m}v)_m)\). Then

\[
 \boxed{
 \mathcal W-\mathcal G_v\in\mathcal L^1,
 \qquad
 \mathcal W\in\mathcal L^{1,\infty}\setminus\mathcal L^1.}
\tag{12}
\]

Hence \(\mathcal W\) defines the same nonzero class as \(\mathcal G_v\) in
\(\mathcal L^{1,\infty}/\mathcal L^1\).

### Proof

The first assertion is (6) and (9). The singular values of \(\mathcal G_v\) are
\(6^{-m}\|v\|\), repeated \(5\cdot6^m\) times. Its trace contribution on every complete shell
is therefore \(5\|v\|\), so it is not trace class. Up through shell \(M\), its singular-value
sum grows linearly in \(M\), while the number of singular values grows like \(6^M\). Thus the
partial sums are \(O(\log N)\), proving weak-trace membership. A trace-class perturbation cannot
turn a non-trace-class operator into a trace-class operator, proving (12). ∎

Choose any bounded coefficient reader \(\lambda_v:K\to\mathbb C\) with
\(\lambda_v(v)=1\). Applied blockwise, it sends \(\mathcal W\) to

\[
                         G_6+\mathcal L^1.
\tag{13}
\]

Thus the quotient class is coefficient-faithful. Its logarithmic shell coefficient is nonzero;
for the leading positive operator,

\[
 \lim_{N\to\infty}
 \frac{\text{singular-value sum through the first }N\text{ coordinates}}
      {\log N}
 =\frac5{\log6}.
\tag{14}
\]

No divisor point or horizontal character has entered this construction.

## 3. Wold compression and the strict critical coface

Let \(S_6e_k=e_{6k}\) and let \(P_6=S_6S_6^*\). Define Wold compression on shell-amplified
operators by

\[
 \mathcal C_6(T)=(1\otimes S_6^*)TS_6.
\tag{15}
\]

For every sequence \(X\),

\[
 \mathcal C_6(\mathcal A_6(X))
 =\mathcal A_6((X_{m+1})_m),
 \qquad
 S_6^*G_6S_6=\frac16G_6.
\tag{16}
\]

### Theorem 3.1 — singular Green--Stokes coface

The complete corrected source obeys

\[
 \boxed{
 \mathcal C_6(\mathcal W)-\frac16\mathcal W\in\mathcal L^1.}
\tag{17}
\]

Equivalently,

\[
 [\mathcal C_6(\mathcal W)]
 =\frac16[\mathcal W]
 \quad\text{in }\mathcal L^{1,\infty}/\mathcal L^1.
\tag{18}
\]

### Proof

The leading term \(6^{-m}v\) satisfies (18) exactly. The remainder of the left side of (17) is
the shell amplification of \(E_{m+1}-E_m/6\). Equation (6) implies

\[
 \sum_{m\ge3}6^m\|E_{m+1}-E_m/6\|<\infty,
\]

so (9) makes it trace class. ∎

This is a genuine pre-specialization singular source relation. It is not the claim that the
physical Gamma reader annihilates the class; that claim requires a comparison which preserves
the trace-class subobject.

## 4. Operator realization of the critical-edge Köthe domain

For a scalar grade sequence \(c=(c_m)\), let \(D_c\) be shell diagonal multiplication by
\(c_m\) on \(I_m\). For \(0<a<1\),

\[
 \boxed{
 \operatorname{Tr}(|D_c|G_6^{1-a})
 =5\sum_{m\ge3}6^{am}|c_m|.}
\tag{19}
\]

Consequently the critical-edge Köthe domain is the concrete projective trace ideal

\[
 \mathfrak D_6^\partial
 =\{D_c:D_cG_6^\varepsilon\in\mathcal L^1
       \text{ for every }\varepsilon>0\}.
\tag{20}
\]

For \(\delta\in(-1,1)\), the evaluated forward and reciprocal normals are

\[
 D_+(\delta)=G_6^{1-\delta},
 \qquad
 D_-(\delta)=-G_6^{1+\delta}.
\tag{21}
\]

### Theorem 4.1 — strict two-orientation wall

\[
 \begin{aligned}
 D_+(\delta)\in\mathfrak D_6^\partial
   &\Longleftrightarrow\delta\le0,\\
 D_-(\delta)\in\mathfrak D_6^\partial
   &\Longleftrightarrow\delta\ge0.
 \end{aligned}
\tag{22}
\]

Therefore

\[
 \boxed{D_+(\delta),D_-(\delta)\in\mathfrak D_6^\partial
        \Longleftrightarrow\delta=0.}
\tag{23}
\]

### Proof

The product \(G_6^{1-\delta+\varepsilon}\) is trace class exactly when
\(1-\delta+\varepsilon>1\), or \(\varepsilon>\delta\). This holds for every
\(\varepsilon>0\) exactly when \(\delta\le0\). Reflection proves the second statement and their
intersection proves (23). ∎

The full source operator \(\mathcal W\) belongs to the corresponding vector-valued domain:
its leading term gains trace class after multiplication by every positive power of \(G_6\), and
its remainder is already trace class by Theorem 2.1.

## 5. Exact physical Gibbs reader

Define the bounded shell Stokes cocycle

\[
 C_6=\frac16I-P_6.
\tag{24}
\]

The shell BV boundary is

\[
 [S_6^*,G_6S_6]
 =S_6^*G_6S_6-G_6S_6S_6^*
 =C_6G_6.
\tag{25}
\]

For \(\operatorname{Re}z>0\), define the normalized Green Gibbs reader

\[
 \Phi_z(A)=
 \frac{\operatorname{Tr}(A G_6^{1+z})}
      {\operatorname{Tr}(G_6^{1+z})}.
\tag{26}
\]

The partition function and boundary numerator are

\[
 \operatorname{Tr}(G_6^{1+z})
 =\frac{5\,6^{-3z}}{1-6^{-z}},
 \qquad
 \operatorname{Tr}(C_6G_6^{1+z})
 =\frac56\,6^{-3z}.
\tag{27}
\]

Indeed, on every shell after the first, exactly one sixth of coordinates lie in the range of
\(S_6\), so the signed trace of \(C_6\) cancels shellwise. Only the lower shell remains.

### Theorem 5.1 — source Gibbs/physical BV identity

For \(\operatorname{Re}z>0\),

\[
 \boxed{
 \Phi_z(C_6)=\frac16(1-6^{-z}).}
\tag{28}
\]

If \(s\in\mathbb C\) and \(\delta=2\operatorname{Re}s-1\), then the meromorphic continuation of
(28) is exactly the existing ordinary-integer physical boundary coefficient

\[
 \boxed{
 \Phi_\delta(C_6)
 =\operatorname{BV}_6(s)
 =\frac16(1-6^{-\delta}).}
\tag{29}
\]

Its reflected difference is

\[
 \boxed{
 6\bigl(\Phi_\delta(C_6)-\Phi_{-\delta}(C_6)\bigr)
 =6^\delta-6^{-\delta}=K_6(s).}
\tag{30}
\]

### Proof

Divide the two expressions in (27) to obtain (28). Equations (29)--(30) are substitution and the
already fixed definition of the Deninger mate curvature. ∎

For \(\delta>0\), \(\Phi_\delta\) is a literal normal Gibbs state while the reflected formula is
only analytically continued; for \(\delta<0\) the roles reverse. At \(\delta=0\), the Gibbs mass
escapes to cofinal shells. Every shift-invariant Abel/Dixmier boundary state kills \(C_6\), since
its mean is zero on every cofinal shell. Thus the critical singular trace supplies a real Stokes
annihilator, but only after the source-to-physical comparison is known to land in its domain.

The global reciprocal Green \(Qe_k=k^{-1}e_k\) gives the parallel classical identity

\[
 \operatorname{Tr}([S_n^*,QS_n]Q^z)
 =\frac1n(1-n^{-z})\zeta(1+z),
 \qquad \operatorname{Re}z>0.
\tag{31}
\]

Its removable value at \(z=0\) is \((\log n)/n\), while its normalized Gibbs expectation tends
to zero. Equation (31) is parent Bost--Connes/spectral-zeta mathematics; novelty is not claimed
for it. The project-specific advance is the identification of its degree-six shell restriction
with the literal corrected Möbius source class and the existing BV reader; its reflected
difference becomes the Gamma/Calderón--Witt coefficient after the already fixed positive
calibration. The normal Gibbs family reads the principal shell symbol, not the full trace-class
correction. At the critical singular boundary the correction is invisible; proving the actual
completed-Green comparison preserves that quotient is precisely the open theorem below.

## 6. Classification of finite source-valued cofaces

Let \(R=\mathbb C[u,u^{-1}]\), let \(S\) be forward grade shift, and let

\[
 \Gamma_m^+=6^{-m}u^m,
 \qquad
 \Gamma_m^-=-6^{-m}u^{-m}.
\tag{32}
\]

### Theorem 6.1 — principal ideal of common local annihilators

For \(P(S)\in R[S]\),

\[
 P(S)\Gamma^+=P(S)\Gamma^-=0
\]

if and only if

\[
 \boxed{
 (S-u/6)(S-u^{-1}/6)\mid P(S).}
\tag{33}
\]

The unique monic minimal common annihilator is

\[
 D_u=S^2-\frac{u+u^{-1}}6S+\frac1{36}.
\tag{34}
\]

### Proof

Annihilation of the two geometric sequences is equivalent to
\(P(u/6)=P(u^{-1}/6)=0\). Monic polynomial division first gives
\(P=(S-u/6)Q\). Evaluation at \(u^{-1}/6\) gives

\[
 (u^{-1}/6-u/6)Q(u^{-1}/6)=0.
\]

The Laurent polynomial ring is a domain and the first factor is nonzero, so
\(Q(u^{-1}/6)=0\). A second monic division gives (33). Expansion yields (34). ∎

Under the horizontal character \(u\mapsto6^\delta\), (34) becomes

\[
 D_\delta
 =S^2-\frac{6^\delta+6^{-\delta}}6S+\frac1{36}.
\tag{35}
\]

It agrees with the fixed critical scalar coface

\[
 D_0=(S-1/6)^2
\tag{36}
\]

exactly when \(6^\delta+6^{-\delta}=2\), hence exactly when \(\delta=0\) for real \(\delta\).
Thus the common source-valued second-order coface is an adaptive annihilator: it is flat for every
character because its middle coefficient carries that character. Descending it to the fixed
critical scalar coface is already the RH-bearing step. Theorem 6.1 closes all finite local
source-valued alternatives and forces the surviving comparison to use the nonlocal trace-ideal
class of Sections 2--5.

## Lean formalization certificate

Sections 1--6 are formalized unconditionally in the following modules:

- `DeningerGammaSixFullSourcePrincipalClass`: the actual corrected Möbius source, trace-order
  tensor remainder, ordinary-integer rectangular amplification, trace-class remainder, faithful
  principal coefficient reader, and full weak-trace principal-class theorem;
- `DeningerGammaSixSingularGreenStokesCoface`: the literal shell Wold isometry, its adjoint
  compression, exact principal eigenvalue (1/6), trace-class compressed remainder, and singular
  Green--Stokes coface;
- `DeningerGammaSixGreenGibbsPhysicalReader`: the actual diagonal Gibbs weight, partition and
  Wold-range traces, normalized reader, positive-temperature trace ratio, analytic continuation,
  equality with the physical BV reader, and reflected curvature identity;
- `DeningerGammaSixFiniteCofaceClassification`: the Laurent-polynomial coefficient ring, two
  literal orientation roots, canonical quadratic, divisibility classification, minimal degree,
  and uniqueness of the monic minimal common annihilator;
- `DeningerGammaSixShellPrincipalIdeal`: the exact two-orientation Köthe-domain wall and exact
  per-shell trace mass.

The paper theorems are represented by these headline declarations:

| Paper claim | Lean declaration |
|---|---|
| Theorem 1.1 | `summable_deningerGammaSix_shellWeightedRemainder` and `summable_norm_deningerGammaSixSourceTensorRemainderColumn` |
| Theorem 2.1 | `deningerGammaSix_fullSource_weakTracePrincipalClass` and `deningerGammaSixLeadingTensorReader_comp_principal` |
| Equation (14) shell invariant | `deningerGammaSixShellTraceMass_eq_five` |
| Theorem 3.1 | `deningerGammaSixFullSource_singularGreenStokesCoface` |
| Theorem 4.1 | `DeningerGammaSixBothEdgesInDomain_iff` |
| Theorem 5.1 | `deningerGammaSixNormalizedGreenGibbsReader_eq`, `deningerGammaSixGreenGibbsContinuation_eq_physicalBV`, and `deningerGammaSixGreenGibbs_reflectedDifference` |
| Theorem 6.1 | `deningerGammaSix_commonCoface_annihilator_iff` and `deningerGammaSixCommonCofacePolynomial_unique_monic_minimal` |

Reusable Hilbert-space infrastructure lives in `RectangularVectorDiagonal`,
`RectangularWeakSchatten`, and `LpInjectionCompression`. All new modules are wired into the
`HTGeometry` or `RHTower` umbrella. Exact-module `lake build` audits pass. A `#print axioms` audit
of every headline theorem reports only `propext`, `Classical.choice`, and `Quot.sound`; no project
axioms, hypotheses, `sorry`, `admit`, `opaque`, or `unsafe` declarations occur.

Section 7 is deliberately not claimed as formalized mathematics: it records the exact open
Route-L comparison theorem exposed by the completed formal package.

## 7. Exact remaining Route-L theorem

The source object and its strict domain are now explicit. The missing theorem is:

> **Gamma-six shell Green strict comparison.** Construct, before divisor specialization, a
> place-marked Rost--Schmid/Meyer chain comparison from the full source class
> \([\mathcal W]\in\mathcal L^{1,\infty}/\mathcal L^1\) to the completed Xi
> Green/Calderón--Witt incidence carrier such that:
>
> 1. it preserves the trace-class subobject and hence descends (18);
> 2. it intertwines Wold compression with the actual Gamma/co-Poisson boundary;
> 3. the reader (13) lands on the completed Xi Green coefficient without fusing divisor,
>    prime, depth, or orientation labels; and
> 4. reflection transports the two evaluated principal symbols to both members of
>    \(\mathfrak D_6^\partial\).

Clause 4 and Theorem 4.1 force \(\delta_\rho=0\) at every Xi divisor point. Clauses 1--3 prevent
installing that conclusion as a target-domain definition. This is a strict source-to-physical
chain comparison problem, not a remaining source-existence, completion, recurrence, or scalar
annihilation problem.

## 8. Hostile and novelty audit

1. **No RH premise.** Sections 1--6 use the Möbius tail, ordinary-integer shells, Wold shift,
   trace ideals, and arbitrary real characters only.
2. **Not a chosen damping.** The principal exponent \(6^{-m}\) is the tensor square of the first
   surviving source atom \(\mu(6)=1\); Theorem 1.1 shows the complete tail has the same quotient
   class.
3. **Not grade-only topology.** Shell multiplicity \(5\cdot6^m\) is essential. Restriction to the
   lacunary orbit \(\{6^m\}\) makes both orientations trace class throughout the open strip and
   loses the selector.
4. **Not a commutator shortcut.** The source BV boundary is a Hochschild commutator, but its
   ordinary finite-part trace is nonzero. Only the singular critical trace kills it, and domain
   preservation is the open theorem.
5. **Not an adaptive recurrence.** Theorem 6.1 exhibits the unique finite adaptive recurrence and
   proves why it erases the detector for every character.
6. **Literature boundary.** Wold shifts, Bost--Connes Gibbs states, spectral zeta functions,
   Macaev ideals, Dixmier traces, and polynomial annihilators are parent mathematics. No priority
   claim is made. Corpus and targeted literature searches found no prior conjunction with the
   corrected Gamma-six Möbius tail, its trace-class remainder theorem, the physical
   Gamma/Calderón--Witt reader, and the exact Route-L comparison wall.
7. **Existing Fourier landing is insufficient.** Blockwise Plancherel preserves (12) and its
   trace-class remainder, but the corpus landing is an almost-everywhere identity on the real
   spectral line. It does not continuously evaluate off-axis Xi divisor conormals or identify the
   resulting shell quotient with the completed Xi Green incidence class. Counting that unitary
   real-boundary transport as Clause 3 of Section 7 would be theater.
