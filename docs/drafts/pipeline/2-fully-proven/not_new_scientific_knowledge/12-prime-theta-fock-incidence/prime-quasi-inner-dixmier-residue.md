# Prime quasi-inner defect has an arithmetic Dixmier residue

- **ID:** prime-quasi-inner-dixmier-residue
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** `[PROVED ON PAPER; NOVELTY UNVERIFIED]`
- **Source object:** the one-prime quasi-inner defect of Connes--Consani
- **Scientific status:** not new scientific knowledge unless the independent proof, primary-literature,
  and significance gates all pass

## Theorem

Let `p` be a rational prime, let `P` be the Hardy projection on the critical line, and let

```text
H_p = (1-P) M_(rho_infinity rho_p) P.
```

Then `|H_p|^2` belongs to the weak trace ideal `L^(1,infinity)` and is measurable in the
sense of Connes. With the standard normalization of the Dixmier trace,

```text
Tr_omega(|H_p|^2) = 2 (p-1)^4 / (p^2 log p)
```

for every Dixmier trace `Tr_omega`.

## 1. Reduction to an operator on `ell^2(Z)`

Write `L=log p`. The decomposition in Theorem 4.4 of Connes--Consani is

```text
H_p = E_infinity + E_p + E_0,
E_p = (1-p)/p U_- V D I V* U_+*,
V = U B.
```

Here `E_infinity` is an infinitesimal of infinite order, `E_0` has finite rank, `U` is an
isometry, `I e_n=e_(-n)`, and

```text
D e_0=0,
D e_n=d_n e_n,
d_n=rho_infinity(2 pi i n/L)  (n != 0).
```

Under Fourier series from `ell^2(Z)` to `L^2(R/Z)`, `B` is multiplication by

```text
b(x)=p^((1-x)/2),  0<=x<1.
```

Put `C=B D I B`. The isometries in the formula for `E_p` show that the nonzero spectrum
of `E_p* E_p` is `((p-1)/p)^2` times the spectrum of `C^2`.

Let `B_tilde=I B I`. Almost everywhere on the circle,

```text
b(x)b(-x)=sqrt(p),
```

so `B_tilde=sqrt(p) B^(-1)`. Since `d_(-n)=conj(d_n)`, one has `I D I=D*`. Therefore

```text
G_p := C^2 = p B D B^(-2) D* B.                    (1)
```

The remaining task is to compute the singular trace of the positive operator `G_p`.

## 2. Weak modulation

Let `N e_n=n e_n` and let

```text
V_0=(1+|N|)^(-1).
```

The exact modulus identity from Connes--Consani is

```text
|d_n|^2 = (L/|n|) coth(pi^2 |n|/L),  n != 0.       (2)
```

Consequently `R=|D|` belongs to `L^(2,infinity)` and `R V_0^(-1/2)` is bounded.
Extend the diagonal phase in the polar decomposition `D=U_R R` arbitrarily at `n=0`, so
that `U_R` is unitary and commutes with `R` and `V_0`.

Fix a real number `r>2` and put `s=1/r`. Multiplication by `b` is bounded on
`H^s(R/Z)` for `|s|<1/2`. In this particular case this can be seen directly from

```text
b_hat(k)=(sqrt(p)-1)/(L/2+2 pi i k):
```

after conjugation by `(1+|N|)^s`, the nonconstant part is a discrete Hilbert transform
on the power weight `(1+|n|)^(2s)`, which is an `A_2` weight exactly for `|s|<1/2`.
Thus

```text
T_s=V_0^s B V_0^(-s)
```

is bounded. Since

```text
R B V_0^(-s)=(R V_0^(-s)) T_s,
```

and `R V_0^(-s)` belongs to `L^(q,infinity)` with

```text
1/q=1/2-s,
q=2r/(r-2),
```

the weak ideal Holder inequality applied to

```text
G_p V_0^(-1/r)
 = p (B U_R R) B^(-2) (R U_R* B V_0^(-1/r))
```

gives

```text
G_p V_0^(-1/r) in L^(r/(r-1),infinity).
```

This is precisely weak `V_0`-modulation in the sense used by Goffeng--Usachev for the
ideal `L^(1,infinity)`. Their expectation-value theorem and its preceding eigenvalue
comparison lemma therefore reduce both the Dixmier trace and measurability of `G_p` to
the ordinary limit of its normalized Fourier-diagonal sums.

## 3. Moving gamma-phase lemma

For positive `n`, Stirling's formula in the definition of `rho_infinity` gives

```text
arg d_n
 = (2 pi n/L) (log(n/L)-1) - pi/4 + O(1/n).       (3)
```

Hence for every fixed integer `k`, with

```text
delta_n=log_p(n/L) mod 1,
```

one has

```text
conj(d_(n+k))/conj(d_n) - exp(-2 pi i k delta_n) -> 0.   (4)
```

Let `a_k=b_hat(k)`. Define

```text
h_n(x)=sum_k a_k conj(d_(n+k))/conj(d_n) exp(2 pi i k x),
```

where `d_0=0`. Then

```text
||h_n-b(.-delta_n)||_2 -> 0.                       (5)
```

To justify the passage from the fixed modes in (4) to (5), use

```text
|a_k| <= C/(1+|k|),
|d_m|^2 <= C/(1+|m|)  (m != 0),
|d_n|^(-2) <= C n.
```

For fixed `K`, the modes `|k|<=K` converge by (4). For the remaining modes, set
`m=n+k` and split into `|m|>=n/2` and `|m|<n/2`. The first part is bounded by
`C/K`. In the second part `|k|>=n/2`, and the bound is

```text
C n sum_(0<|m|<n/2) 1/(n^2 |m|) = O(log(n)/n).
```

Taking first `n->infinity` and then `K->infinity` proves (5). The identity
`d_(-n)=conj(d_n)` gives the same limit for negative frequencies.

## 4. Fourier diagonal

Equation (1) gives the exact positive-form identity

```text
<G_p e_n,e_n> = p ||B^(-1) D* B e_n||_2^2.         (6)
```

By the definition of `h_n`,

```text
D* B e_n=conj(d_n) e_n h_n.
```

Since `B^(-1)` is bounded, (5) and (6) imply, for both signs of `n`,

```text
<G_p e_(+/-n),e_(+/-n)>
 = p |d_n|^2 (F(delta_n)+o(1)),                    (7)

F(delta)=integral_0^1 b(x-delta)^2/b(x)^2 dx.
```

The periodic function `F` is continuous. Its period mean is especially simple. With
`s_p(x)=b(x)^2=p^(1-x)`, invariance of Haar measure gives

```text
integral_0^1 F(delta) ddelta
 = (integral_0^1 s_p(x) dx)(integral_0^1 s_p(x)^(-1) dx)
 = (p-1)^2/(p L^2).                                (8)
```

Equivalently, for `0<=delta<=1`, one orientation gives

```text
F(delta)=p^(-delta)(1-delta+p delta).
```

## 5. Harmonic logarithmic rotation

For every continuous one-periodic function `f` and every real `c`,

```text
(1/log N) sum_(n<=N) f(log_p n+c)/n
 -> integral_0^1 f(x) dx.                          (9)
```

Indeed, approximate `f` uniformly by trigonometric polynomials. For a nonzero Fourier
mode `k`, the relevant sum is a constant multiple of

```text
sum_(n<=N) n^(-1+2 pi i k/L)=O(1),
```

whereas the zero mode is the harmonic sum.

Using (2), (7), (8), and (9), and noting that the `coth-1` error in (2) is exponentially
summable, one obtains

```text
lim_(N->infinity) (1/log N)
  sum_(0<|n|<=N) <G_p e_n,e_n>
 = 2 p L (p-1)^2/(p L^2)
 = 2 (p-1)^2/L.                                    (10)
```

Ordering the eigenbasis of `V_0` as `e_0,e_1,e_(-1),e_2,e_(-2),...` changes `log N`
only by `o(log N)`. Weak modulation and the Goffeng--Usachev eigenvalue comparison lemma
now show

```text
lim_(N->infinity) (1/log N) sum_(j<=N) mu_j(G_p)
 = 2 (p-1)^2/L.                                    (11)
```

Thus `G_p` is measurable and every Dixmier trace has the value in (11).

## 6. Return to the full one-prime defect

The isometric reduction in Section 1 and (11) give

```text
Tr_omega(E_p* E_p)
 = ((p-1)/p)^2 2 (p-1)^2/L
 = 2 (p-1)^4/(p^2 L).                              (12)
```

Put `K=E_infinity+E_0`. The source decomposition makes `K` trace class. Therefore

```text
H_p* H_p-E_p* E_p=E_p* K+K* E_p+K* K
```

is trace class. Trace-class perturbations do not change the limit (11) or any Dixmier
trace. Equation (12) proves the theorem.

## 7. Spectral recovery of the local norm and the infinite Euler divisor

Nothing in Sections 1--6 uses primality: for every real `q>1`, the same proof applies to

```text
rho_q(z)=(1-q^(z-1))/(1-q^(-z))
```

and gives the residue function

```text
R(q)=2 (q-1)^4/(q^2 log q).                         (13)
```

This function is strictly increasing from `0` to `infinity`. Indeed,

```text
R'(q)/R(q)
 = 4/(q-1)-2/q-1/(q log q)
 = (1/q)(2(q+1)/(q-1)-1/log q)>0,
```

where `log q>(q-1)/q` for `q>1`. Its endpoint limits follow immediately from (13).
Consequently the unlabelled unitary ideal class of `H_q` determines `q`: if `H_q` and
`H_r` are unitarily equivalent, or merely have equal measurable residues, then `q=r`.

For the arithmetic subfamily `{H_p : p prime}`, the unlabelled multiset of operator classes
therefore reconstructs the set of primes. It consequently reconstructs the locally finite infinite
Euler divisor

```text
D_Euler = sum_(p prime) sum_(m>=1) (log p) [m log p],
```

whose Laplace transform is `-zeta'(s)/zeta(s)`. This reconstruction uses an infinite family of
singular-trace invariants, not a finite jet or a height parameter.

## Exact scope

`[PROVED ON PAPER]` The one-prime compact quasi-inner defect has a nonzero, explicit,
prime-dependent noncommutative residue.

`[PROVED ON PAPER]` The residue strictly determines the local scale, and the prime-indexed family
reconstructs the infinite Euler divisor.

`[NOT PROVED]` This does not give a full singular-value asymptotic term by term.

`[NOT PROVED]` This does not yet assemble over all primes or exclude an off-critical zero.

`[NOT PROVED]` It does not increase the Platt--Trudgian verified range.

## Scientific novelty gate

- [x] Parent-theory attack: generic Hankel/Dixmier trace and modulated-operator theorems are
  established tools; the claimed result is only the arithmetic evaluation for this exact local-factor
  defect.
- [x] Source attack: Connes--Consani prove order `1/2` and the decomposition but do not state the
  measurable residue or the constant (12).
- [x] Direct citation audit: the located papers citing the source do not state a Dixmier residue for
  this operator.
- [ ] Independent expert proof audit, especially the weak-modulation normalization and the weighted
  discrete-Hilbert-transform step.
- [ ] Broader literature audit beyond direct citations and exact-term searches.
- [x] First significance attack: the residue is not an isolated size estimate; it spectrally recovers
  the local norm and the prime-indexed family reconstructs the infinite Euler divisor.
- [ ] Strong significance audit: derive a functorial multi-place or all-place law that interacts with
  a zero-exclusion criterion. Reconstruction alone does not improve the verified zero-free range.

Until the three unchecked items pass, the permitted label is
`[PROVED ON PAPER; NOVELTY UNVERIFIED]`, not `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`.

## Primary references

- A. Connes and C. Consani, *Quasi-inner functions and local factors*, J. Number Theory 226
  (2021), 139--167; arXiv:2008.10974.
- M. Goffeng and A. Usachev, *Dixmier traces and residues on weak operator ideals*, J. Math.
  Anal. Appl. 488 (2020); arXiv:1710.08260.
- M. Englis and G. Zhang, *Hankel operators and the Dixmier trace on the Hardy space*,
  J. London Math. Soc. 94 (2016); arXiv:1601.06428.
- S. Lord, A. Sedaev, and F. Sukochev, *Dixmier traces as singular symmetric functionals and
  applications to measurable operators*, J. Funct. Anal. 224 (2005); arXiv:math/0501131.

## Lean progress log — 2026-08-22

Added `RHTower/GaussOnePrimeCriticalResidue.lean`, wired into the `RHTower` umbrella.  It proves
the literal depth-one identity

```text
gaussChannelResidue 1 p = 2 (p-1)^4 / (p^2 log p),
```

and packages the existing explicit one-prime critical diagonal realization as a weak trace-ideal
operator with that exact logarithmic residue.  The leaf build and capstone axiom audit passed with
only `propext`, `Classical.choice`, and `Quot.sound`.

Scope is intentionally narrower than the card theorem: this is the explicit critical model and
the existing weighted `G_full` diagonal calculation.  No Lean theorem currently identifies it with
the full Connes--Consani defect `H_p`, proves the source trace-class perturbation, or gives the
depth-one singular-value/Dixmier statement for that defect.  The card therefore remains at Stage 2.

`RHTower/PrimeQuasiInnerResidueRigidity.lean` now formalizes the residue-recovery part of Section 7.
It defines the real interpolation

```text
R(q)=2 (q-1)^4/(q^2 log q),
```

proves positivity and a factorization into strictly increasing algebraic and logarithmic-mean
factors on `q>1`, proves `R` strictly increasing and injective there, proves its endpoint limits and
exact image `(0,infinity)`, and identifies `R(p)` exactly with `gaussChannelResidue 1 p`.  Thus
equality of the explicit critical-model residues now unconditionally recovers the local real scale.
The targeted leaf build passed, and every new declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

`RHTower/SchattenLogResidueFiniteRankPerturbation.lean` now proves the exact finite-rank stability
needed for the `E_0` term.  A rank-`r` difference interlaces approximation numbers with an index
shift of `r`, uniformly bounds the difference of all Schatten-one partial sums by fixed prefixes,
and therefore preserves both weak Schatten-one membership and the value/existence of the ordinary
logarithmic residue.  Its targeted leaf build and full new-declaration axiom audit passed with only
the same standard axioms.

`RHTower/PositiveSchattenLogResidueTraceClassPerturbation.lean` closes the corresponding
infinite-order perturbation law.  For positive compact `A,B` with `A-B` Schatten one, it proves the
sharp uniform prefix estimate

```text
|sum_(n<N) a_n(A) - sum_(n<N) a_n(B)| <= ||A-B||_1,
```

then proves invariance of weak Schatten-one membership and exact logarithmic residue.  This is the
operator-ideal implication required once the concrete `H_p*H_p-E_p*E_p` trace-class decomposition
is available.  Targeted leaf build and all new-declaration axiom audits passed with only `propext`,
`Classical.choice`, and `Quot.sound`.

`RHTower/ConnesConsaniResiduePerturbationCapstone.lean` packages the complete abstract reduction in
the exact decomposition shape: if compact `E` has weak Schatten-one measurable `E*E` with residue
`Q` and `R` is trace class, then `(E+R)*(E+R)` is weak Schatten one and has the same exact residue
`Q`.  Positivity, compactness, and the trace-class modulus-square difference are all discharged
inside the theorem.  Its targeted leaf build and axiom audit passed with only the standard axioms.

This does not close the card: the concrete Connes--Consani `H_p` and its decomposition are not yet
constructed in Lean, so neither the identification of its distinguished block with the explicit
Gauss critical model nor the trace-class proof for its actual `E_infinity+E_0` remainder has landed.
Reconstruction of the full Euler divisor from the resulting unlabelled operator family also remains
unformalized.

`RHTower/QuasiInnerResidueTraceClassTransfer.lean` sharpens that abstract capstone at the positive
endpoint.  It proves that a positive transferred logarithmic residue forces the full energy outside
Schatten one, and specializes this result to the literal positive one-prime scale
`2 (p-1)^4/(p^2 log p)`.  Thus the eventual concrete decomposition will simultaneously yield weak
Schatten-one membership, exact measurable residue, and non-trace-classness without another ideal
argument.  The targeted leaf/module checks passed, and both declarations have axiom set exactly
`[propext, Classical.choice, Quot.sound]`.  Concrete Hardy-space realization obligations above
remain unchanged, so the card stays at Stage 2.

`RHTower/WeakSchattenHolder.lean` adds the reusable weak-ideal calculus needed by the literal
quasi-inner factorization.  It proves left/right bounded-ideal closure and the weak Hölder law

```text
S_(p,infinity) * S_(q,infinity) subset S_(pq/(p+q),infinity)
```

directly from approximation-number composition.  `RHTower/IndexedDiagonalWeakSchatten.lean` adds
unitary invariance and a finite-rank truncation theorem converting enumerated critical power decay
of an arbitrary indexed diagonal into weak Schatten membership.

`RHTower/GaussDiagonalWeakSchatten.lean` applies those results to the actual sampled Gauss Fourier
symbol.  It proves unconditionally that the literal full diagonals `D,D*` lie in weak `S_(2m)` and
that the already constructed operator

```text
gaussQuasiInnerGFull = p B D B^(-2) D* B
```

lies in weak `S_m` for every `m>=1`.  In particular the actual depth-one quasi-inner block is weak
Schatten one; this conclusion no longer appears as a premise.  Combining it with the existing
unconditional non-trace theorem also proves the sharp depth-one classification: the literal block
is outside every `S_q` for `0<q<=1` and belongs to every `S_q` for `q>1`.  All three targeted leaf builds
passed, and every new declaration has axiom set exactly
`[propext, Classical.choice, Quot.sound]`.

This still does not close the card.  Weak membership alone does not identify the depth-one
singular-value logarithmic mean with the already proved Fourier-diagonal mean.  The required
weak-modulation/Dixmier-residue comparison for the nonnormal `m=1` block, followed by construction
of the concrete Connes--Consani `H_p=E_p+E_infinity+E_0` trace-class decomposition, remains open.

`RHTower/GaussOnePrimeReducedDefectEnergy.lean` closes the distinguished-block algebra exactly.
It promotes circle reflection to an involutive linear isometry, proves `C_full=B D_full I B`
self-adjoint, and proves

```text
C_full* C_full = G_full,
E_p,reduced := ((1-p)/p) C_full,
E_p,reduced* E_p,reduced = gaussChannelOperator 1 0 p.
```

Thus the local-factor normalization and modulus-square identification are now literal operator
equalities, not spectral premises or diagonal proxies.  Targeted direct and module builds passed;
every new declaration depends only on `[propext, Classical.choice, Quot.sound]`.

Remaining Stage-3 obligations are analytic and source-faithful: prove the exact depth-one
singular-value logarithmic mean for this actual channel, construct the Hardy defect and its
`E_p+E_infinity+E_0` decomposition, transfer through the source isometries and trace-class
remainder, then formalize unlabelled-family Euler-divisor reconstruction.

`RHTower/GaussOnePrimeActualCriticalResidue.lean` now closes the exact depth-one singular-value
problem.  A sharper one-step two-piece-amplitude budget proves, for every `rho>0`,

```text
||G e_n|| <= C_rho |n|^(-1+rho).
```

The existing positive-operator diagonal comparison then transfers the already proved literal
Fourier-diagonal mean to the actual singular values:

```text
(1/log N) sum_(n<N) s_n(gaussChannelOperator 1 0 p)
  --> gaussChannelResidue 1 p = 2 (p-1)^4/(p^2 log p).
```

Consequently the actual depth-one channel is in the Dixmier ideal, has an ordinary measurable
Schatten logarithmic residue, and is not trace class.  Rewriting through the exact operator identity
from `GaussOnePrimeReducedDefectEnergy.lean` gives the same three unconditional conclusions for the
literal reduced defect energy `E_p,reduced* E_p,reduced`.  Direct Lean check and targeted leaf build
passed; every new declaration has axiom set exactly
`[propext, Classical.choice, Quot.sound]`.

Remaining Stage-3 obligations are now source realization and reconstruction only: construct the
concrete Hardy defect `H_p`, prove its source-isometric
`E_p+E_infinity+E_0` decomposition with trace-class remainder, apply the proved perturbation
capstone, and formalize Euler-divisor reconstruction from the unlabelled prime family.

`RHTower/PrimeQuasiInnerEulerReconstruction.lean` closes the reconstruction clause.  It connects
each literal reduced-defect energy to its measured residue, proves the prime-to-residue map
injective, and proves that both arbitrary unlabelled residue sets and finite unlabelled residue
packets recover their prime apertures exactly.  Therefore equal measured packets force equality of
every prime-indexed observable, including the literal finite Euler denominator

```text
product_(p in P) (1 - p^(-z)).
```

Direct Lean check and targeted leaf build passed; every new declaration has axiom set exactly
`[propext, Classical.choice, Quot.sound]`.  Only concrete Hardy/source decomposition and its
trace-class remainder transfer remain before this card can move to Stage 3.

`RHTower/GaussHarmonicModulationReference.lean` constructs the exact positive compact harmonic
reference underlying the depth-one weak-modulation route.  It transports
`diag (1/(n+1))` to `L²(ℝ/ℤ)` through the standard `ℤ ≃ ℕ` reindexing and Fourier unitary, then
proves its exact approximation numbers, weak `S₁` membership, logarithmic residue one,
injectivity, self-adjointness, nonnegativity, dense range, and compactness.  No comparison with the
Gauss block is assumed or asserted.  Direct Lean check and targeted leaf build passed; every new
declaration depends only on `[propext, Classical.choice, Quot.sound]`.

`RHTower/ConnesConsaniOnePrimeSourceDefect.lean` now constructs the literal source object

```text
(1-P) M_(rho_infinity rho_p) P
```

on the actual spectral `L²(ℝ)`, with the exact archimedean/finite local-factor product symbol,
unit-modulus multiplication operator, Hardy source/range laws, and exact two-block product
decomposition.  Thus the full Hardy defect is no longer an undefined placeholder.

The card nevertheless remains at Stage 2.  Missing source-faithful theorem is now narrower but
still analytic: identify the distinguished block through the source isometries with
`gaussOnePrimeReducedDefect`, prove the difference from the literal Hardy defect trace class, and
apply the already formalized perturbation/residue capstone.  The actual Gauss critical residue and
Euler-family reconstruction are closed, so no unproved modulation or reconstruction premise is
being hidden.

## Lean progress log — 2026-08-25

`HTGeometry/CayleyBoundaryL2Unitary.lean` and
`RHTower/CCMOnePrimeCayleyTransport.lean` close the exact full-space source transport.  The explicit
Cayley half-density is proved surjective after the omitted circle endpoint is handled as a null set,
then bundled as a unitary.  In the project's Fourier convention the nonnegative circle Hardy space
maps to upper Hardy boundary, so the source projection transports to the complementary circle
projection.  The literal product multiplier and full defect satisfy the unconditional intertwining

```text
H_p U_Cayley = U_Cayley (Q M_(rho_infinity rho_p) (1-Q)).
```

Direct checks, targeted leaf builds, and new-declaration axiom audits passed; dependencies are only
`[propext, Classical.choice, Quot.sound]`.

`RHTower/ConnesConsaniDoublePoleFiniteRank.lean` formalizes the exact `E_0` contribution of
Connes--Consani Theorem 4.4.  It constructs source isometries

```text
U_+ e_n = e_n,    U_- e_n = e_(-(n+1)),
```

the geometric and first-weighted geometric vectors at the literal double-pole node `x=-1/3`, and
the source coefficients `alpha_p`, `beta_p`.  Its Fourier matrix is proved exactly:

```text
<e_(-(r+1)),E_0 e_s>
  = alpha_p x^(r+s) + beta_p (r+s) x^(r+s).
```

The operator is then proved to have rank at most two and hence to be Schatten one, with no premises.
Direct check, targeted leaf build, and axiom audit passed with only the same standard axioms.

`RHTower/CCMPaperCayleyTransport.lean` resolves the Fourier-orientation mismatch between the
project Cayley convention and Theorem 4.4.  The explicit Hardy flip `J e_n=e_(-n-1)` is unitary,
exchanges `Q` and `1-Q`, and yields the paper-coordinate unitary `W=J U_Cayley`.  The source
projection and literal one-prime defect then satisfy the exact unconditional intertwining

```text
P W = W Q,
H_p W = W ((1-Q) M_paper Q).
```

Targeted leaf build and all four new-declaration axiom audits passed with only
`[propext, Classical.choice, Quot.sound]`.  This fixes the source/target orientation used by the
displayed `E_0` matrix rather than changing the paper statement.

`RHTower/ConnesConsaniArchimedeanPoleTraceClass.lean` formalizes the complete nonzero
archimedean-pole series `E_infinity`.  For every paper index `N>=1` it constructs the literal Cayley
node `x_N=1-4/(4N+3)`, normalized source/range Szego vectors, and the displayed Theorem 4.4 Gamma
coefficient.  A proved half-integer-Gamma/factorial identity rewrites that coefficient to an
absolutely summable factorial envelope; the resulting normalized rank-one series is therefore
unconditionally Schatten one.  The source-series equality is explicit, not hidden behind a
summability premise.  Direct check, targeted leaf build, and five new-declaration axiom audits
passed with only `[propext, Classical.choice, Quot.sound]`.

`RHTower/ConnesConsaniPoleRemainderTraceClass.lean` packages the exact pole remainder
`R_p=E_infinity+E_0` and proves it Schatten one unconditionally.  Targeted leaf build and the new
capstone axiom audit passed with only `[propext, Classical.choice, Quot.sound]`.  Thus once the
literal source equality isolates `E_p`, no further trace-class argument remains.

Card remains at Stage 2.  Remaining source theorem is the exact nonzero-prime-pole block `E_p` and
its equality, together with `E_infinity+E_p+E_0`, to the literal paper-coordinate circle defect.
The trace-class `E_infinity` and finite-rank `E_0` legs plus full Cayley transport are now closed
rather than assumed.
