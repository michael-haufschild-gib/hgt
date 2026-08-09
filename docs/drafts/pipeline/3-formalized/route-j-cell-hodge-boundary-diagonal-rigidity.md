# Route J cell Hodge-boundary diagonal rigidity

- **ID:** `route-j-cell-hodge-boundary-diagonal-rigidity`
- **Stage:** 3-formalized
- **Formalized companion:** `./route-j-cell-hodge-boundary-diagonal-rigidity-formalized.md`
- **Type:** `[PAPER-PROVED]` / HOSTILE CORRECTION / POSITIVE RIGIDITY
- **Scientific status:** `[PAPER-PROVED] [NO RH INPUT] [NO COMPUTATION] [NOVELTY UNVERIFIED]`
- **Owner:** `route-j-principal-relative-julia-current.md`
- **Predecessor:** `route-j-primitive-promoted-euler-exterior-source.md`

## Exact issue

The cofinal-depth card constructs a bounded landed coefficient profile fixed by an explicit
reflection of its finite depth indices.  That does not yet identify the profile with the actual
admitted sector

```text
kernel(actual Gamma/Hardy boundary reflection defect).
```

The actual boundary defect is evaluated before reflection-invariant scalar fusion and retains every
ordered prime/depth coordinate.  Cancellation after identifying reflected coordinates would reverse
the required order of operations and is not sector preservation.

## Internal frontier

`[CORPUS]` The prime/depth-labelled Calderón--Witt source is

```text
V_cell = directSum_(i : Nat.Primes x Nat) (D_i directSum W_i).
```

Its cross-cell carriers are exact Milnor incidence and Green-fixed:

```text
E_ij = defect_i wedge packet_j,   i != j.
```

`[CORPUS]` The actual polarized Gamma/Hardy boundary comparison proves that its reflection defect is
the reflection-odd primitive Gamma transport.  For cells `i,j`, its scalar coefficient is

```text
gamma_a(i,j)
 = xiGammaEulerPrimitiveReflectionOddExterior(a,i,j).
```

For `a!=0` this coefficient is nonzero whenever the two source half-heights differ.

`[LOCAL-RESEARCH]` The present depth countertransport is a finite combination of the `E_ij` at every
moving stage.  Its custom compensated depth reflection is proved involutive, but no theorem places
that finite incidence carrier in the actual boundary-defect kernel.

## External frontier

`[LITERATURE]` Connes--Consani's semilocal scaling Hamiltonian supplies the Hilbert-space and Weil
positivity setting, but leaves the semilocal positivity statement as an operator-theoretic problem
(`arXiv:1910.14368`).  Their scaling-site and absolute-geometry papers retain prime-periodic
Frobenius orbits (`arXiv:1603.03191`, `arXiv:2606.06604`) but do not construct this
prime/depth-labelled Calderón--Witt exterior boundary map.

The audit found no external theorem identifying the kernel of the source-specific cell-labelled
Gamma/Hardy reflection defect.  The coordinate-linear algebra below is routine; novelty, if any, is
only its exact weld to the source and the resulting Route-J survivor classification.

## Publication-corpus impact

`[CORPUS]` The Hellinger--Hodge Green-descent paper confirms the operation order used here.  Its
actual reflection defect is evaluated on vector-valued exact incidence before Haar orientation,
and one canonical cross-prime exact boundary detects every nonzero modular displacement.
Section 5.2's bounded doubled carrier is only a compensated pretrace symmetry with singular scalar
readout; it is not asserted to lie in the actual defect kernel.  Thus `(CHB-2)`--`(CHB-12)` are the
missing exact audit of that finite carrier, not a contradiction with the paper.

`[CORPUS]` The oriented source-admission paper supplies the completed-topology consequence.  The
completed Xi Green map is coefficient-faithful and dense in completed incidence.  Any closed
admission set containing its range is the whole completion, so a successful source corona must
retain one exact unsquared finite trace.  An arbitrary quotient corona, dense radical, or vertical
graph relation cannot close Route J.  The positive survivor `CHB-CORONA` is therefore sharpened to
the closed source-admission object `K_rho`; its global existence is RH-equivalent and remains open.

## Exact conjecture

Let

```text
I = Nat.Primes x Nat.
```

For `i in I`, let `delta_i` be the normalized defect coordinate and `mu_i` the suspended packet
coordinate.  For ordered cells `i,j`, define the vector-valued cross-effect

```text
N_ij(x,y)
 = delta_i(x) mu_j(y) - delta_i(y) mu_j(x).
```

Let `tau_j` be normalized packet orientation and define the actual cell boundary profile

```text
(partial_a X)(i,j)
 = gamma_a(i,j) tau_j(N_ij(X)).                       (CHB-1)
```

For normalized cell generators `d_i,w_j`, put

```text
E_ij=d_i wedge w_j.
```

`[CONJECTURE CHB-DIAGONAL]`

```text
(partial_a E_kl)(i,j)
 = if i=k and j=l then gamma_a(i,j) else 0.           (CHB-2)
```

Consequently, if `a!=0`, restriction of `partial_a` to the canonical distinct-cell carrier span

```text
C_cell=span {E_ij : i!=j}
```

is injective:

```text
C_cell intersect ker(partial_a) = {0}.                (CHB-3)
```

In particular every nonzero finite source-normal depth spread and its doubled reflected version
fail the actual admitted Hodge-sector condition.

## Hostile falsity audit

1. **Could reflected orientations cancel?** No if `(CHB-2)` holds: `E_ij` and `E_ji` occupy
   different ordered boundary coordinates.  Quotienting those coordinates first is forbidden
   scalar fusion.
2. **Could distinct cells have equal source height?** Equality gives
   `p^(e+1)=q^(f+1)`.  Unique factorization for primes forces `p=q` and `e=f`.
3. **Could `gamma_a(i,j)` vanish anyway?** Existing source theorem makes it nonzero for `a!=0`
   and unequal heights.
4. **Is this RH-equivalent theatre?** No divisor, Xi zero, first-clock lower floor, or target sign
   enters.  The claim is finite source-coordinate linear algebra.
5. **Is the result merely negative?** Its positive survivor is the exact kernel classification
   `(CHB-3)`: any nonzero admitted source carrier must leave the canonical first-clock
   defect--packet span.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Stronger conjecture forced by the expected rigidity

`[CONJECTURE CHB-CORONA]` A Route-J survivor, if one exists, is not a finite cell incidence vector.
It must be a completion relation whose every fixed ordered boundary coordinate vanishes while its
unbounded codiagonal remains as a graph relation.  Equivalently, it must live in a source corona or
an affiliated relation, not in the Hilbert/direct-sum closure on which `(CHB-1)` is a closable
operator.

`[OPEN CORE]` Construct this relation with a source-derived domain and prove a bounded
first-clock comparison before its nonclosable codiagonal, or prove class-completely that every
such relation loses the first-clock readout.

## Proof obligations

- [x] construct the cell defect and packet coordinate maps;
- [x] linearize `(CHB-1)` on the exterior square;
- [x] prove the exact Kronecker law `(CHB-2)`;
- [x] prove distinct prime/depth cells have distinct half-heights;
- [x] prove `(CHB-3)` and the finite depth-spread corollary;
- [x] correct the predecessor card's sector-preservation status;
- [x] formalize the exact dependency-closed theorem in Lean;
- [x] identify the completed survivor as a closed source-admission object with an exact finite
      oriented trace;
- [x] complete targeted Lean lint/axiom/module audit and move this card to Stage 3.

## Dependency-closed paper proof

`[PAPER-PROVED CHB-DIAGONAL]`

### 1. Cell coordinate algebra

For a cell `i=(p,e)`, write

```text
A_i^1=D_p directSum W_p.
```

Let `d_i in A_i^1` be the normalized Calderón defect and `w_i in A_i^1` the normalized
rational-Witt packet.  By construction,

```text
delta_i(d_i)=1,  delta_i(w_i)=0,
tau_i(mu_i(d_i))=0,  tau_i(mu_i(w_i))=1.              (CHB-4)
```

On the finite-support direct sum, component extraction also gives

```text
delta_i(d_k)=0                  if i!=k,
tau_i(mu_i(w_k))=0              if i!=k.              (CHB-5)
```

The second statement means: extract component `i`, apply its local packet suspension, then apply
normalized packet orientation.

For an ordered pair `(i,j)`, alternating linearization of

```text
N_ij(x,y)=delta_i(x)mu_j(y)-delta_i(y)mu_j(x)
```

defines a linear map on the exterior square.  Applying packet orientation and `(CHB-4)`--`(CHB-5)`
to `E_kl=d_k wedge w_l` gives

```text
tau_j(N_ij(E_kl))
 = delta_(i,k) delta_(j,l).                            (CHB-6)
```

The apparently missing second term is identically zero: every packet generator has zero defect
coordinate and every defect generator has zero packet coordinate.  Multiplication by the actual
Gamma/Hardy reflection coefficient proves `(CHB-2)`.

### 2. Distinct cells have distinct source half-height

Let

```text
h(p,e)=((e+1)/2) log p.
```

Assume `h(p,e)=h(q,f)`.  Since `p,q>1`, multiplying by two and using the logarithm power law gives

```text
log(p^(e+1))=log(q^(f+1)).
```

Both powers are positive, so injectivity of the real logarithm gives

```text
p^(e+1)=q^(f+1).                                       (CHB-7)
```

Because `e+1` and `f+1` are positive, `(CHB-7)` implies `p` divides a positive power of `q`.
Primality gives `p|q`, and primality of `q` gives `p=q`.  Substituting this into the original
height equality and using `log p>0` gives `e+1=f+1`, hence `e=f`.  Therefore

```text
i!=j -> h_i!=h_j.                                     (CHB-8)
```

### 3. Diagonal rigidity

Fix `a!=0`.  The already proved reflection-odd source theorem and `(CHB-8)` give

```text
gamma_a(i,j)!=0                                       (CHB-9)
```

for every `i!=j`.

Let

```text
X=sum_(k!=l) c_kl E_kl
```

have finite support and suppose `partial_a X=0`.  Evaluate its `(i,j)` coordinate.  By linearity
and `(CHB-2)`,

```text
0=(partial_a X)(i,j)=gamma_a(i,j)c_ij.
```

Equation `(CHB-9)` gives `c_ij=0` for every `i!=j`.  Hence `X=0`, proving `(CHB-3)`.

This also proves a stronger representation statement: the boundary profile is a left inverse for
canonical carrier coefficients after division by the nowhere-zero multiplier `gamma_a`.  No
linear dependence in the ambient exterior square is assumed; the boundary coordinates themselves
separate the generators.

### 4. Exact failure of the finite depth countertransport

For distinct primes `p,q`, positive depth counts `N,M`, and nonzero source weight `w`, the finite
source-normal spread has coefficients

```text
c_rs =
 D(p,r)D(q,s) w/(NM),
0<=r<N, 0<=s<M.                                       (CHB-10)
```

Critical deattenuation is strictly positive, so every coefficient in `(CHB-10)` is nonzero.  At
the base ordered coordinate `((p,0),(q,0))`, `(CHB-2)` gives

```text
(partial_a X)((p,0),(q,0))
 =gamma_a((p,0),(q,0)) c_00 !=0.                      (CHB-11)
```

The reflected carrier `E_(q,0),(p,0)` contributes only to the reversed ordered coordinate by
`(CHB-2)`.  It cannot cancel `(CHB-11)`.  Therefore neither the one-sided spread nor its doubled
reflected version lies in the actual admitted Hodge sector.

The earlier compensated depth involution remains a correct theorem about the landed coefficient
array, and its `L2` capacity bound remains correct.  What fails is the identification of that
post-identification fixed sector with the pre-fusion Gamma/Hardy boundary-defect kernel.

### 5. Positive survivor and exact remaining representation

The source-derived theorem is not merely “this candidate fails.”  It classifies the entire
canonical finite carrier span:

```text
ker(partial_a) intersect C_cell = {0},  a!=0.          (CHB-12)
```

Consequently:

1. adding more finite depths cannot help;
2. changing finite depth weights cannot help;
3. symmetrizing reflected ordered pairs cannot help before scalar fusion;
4. every finite-support linear carrier retaining a nonzero first-clock defect--packet coefficient
   escapes the actual sector.

The only remaining source representation is a completion relation which is zero under every fixed
ordered boundary coordinate but is not zero for the singular codiagonal.  This is exactly the
relation-valued/source-corona branch `CHB-CORONA`; it is not reassigned outside Route J.

## Hostile proof audit

- `(CHB-6)` uses only normalized source coordinates and direct-sum component orthogonality.
- `(CHB-8)` uses only logarithm injectivity and unique factorization for prime powers.
- `(CHB-9)` is an existing unconditional source theorem, not an RH or divisor hypothesis.
- The argument does not infer non-membership from a nonzero norm; it evaluates one literal boundary
  coordinate.
- Reflected cancellation is tested before quotienting coordinates, matching the publication-ready
  operation order.
- The positive survivor `(CHB-12)` is an exact injectivity/classification theorem.

Verdict: `[PAPER-PROVED] [NOVELTY UNVERIFIED]`.

## Updated proof obligations

- [x] construct the cell defect and packet coordinate maps on paper;
- [x] linearize `(CHB-1)` on the exterior square on paper;
- [x] prove the exact Kronecker law `(CHB-2)` on paper;
- [x] prove distinct prime/depth cells have distinct half-heights on paper;
- [x] prove `(CHB-3)` and the finite depth-spread corollary on paper;
- [x] correct the predecessor card's sector-preservation status — `route-j-primitive-promoted-euler
      -exterior-source.md` now states that the compensated finite-index fixed sector must not be
      identified with the actual boundary-defect kernel;
- [x] formalize the exact dependency-closed theorem in Lean —
      `RHTower/CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity.lean`.
