# Route J primitive-promoted Euler modular exterior source

- **ID:** route-j-primitive-promoted-euler-exterior-source
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + CONJECTURE
- **Source:** `route-j-principal-relative-julia-current.md` · survivors `J-SF1`, `J-SF2`,
  `J-SF5`, `J-SF6`
- **Statement:** Primitive promotion, modular reflection, and a Gamma height anchor construct a
  source-only pre-fusion exterior current with exact hard-block landing and nonnegative finite
  scalarizations; its cofinal uniform budget remains open.

## Goal

Construct the singular source object demanded by Route J rather than infer one from the desired
capacity.  It must retain prime and valuation-depth labels, perform primitive promotion before
scalar fusion, carry a reflection-odd modular channel, meet the certified first-clock bad cells,
and admit the two inequalities

```text
C_x(L)<0  ->  C_x(L)^2 <= R_x(L),
R_x(L) <= M
```

without Xi-zero, multiplicity, negative-part, or target-sign input.

This card is subordinate to the Route J owner card.  It does not reassign any survivor.

## Gates

- [x] 0 → 1 in-progress: source-pure object, exact attack, Door passport
- [ ] 1 → 2 fully-proven: cofinal domination and uniform budget both proved
- [ ] 2 → 3 formalized: every dependency-closed theorem in Lean; exact-module audit green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, external priority audit

## Constructed source

For a prime/depth cell `i=(p,e)`, put

```text
n_i       = p^(e+1),
h_i       = (1/2) log n_i,
A_u(i)    = sqrt((log p)/n_i * exp(-u log n_i)),
P(i)      = sqrt(log p),
J_u(i)    = P(i) A_u(i).
```

`P` is forced by the arithmetic source.  At `u=0`,

```text
J_0(p,e)
  = (log p) / sqrt(p^(e+1))
  = criticalMellinAtomWeight(p^(e+1)).
```

Equivalently, it is the output of the already proved Gamma-fibre promotion gauge

```text
(log p)/(1-p^(-1)) * p^(e/2).
```

The promoted exterior cell is

```text
E_u(i,j) = J_u(i) J_u(j) (h_i-h_j).
```

This acts on both labelled legs before scalar fusion.

## Unconditional theorem A — exact primitive landing

For every prime and every valuation depth:

```text
J_0(p,e)
  = primitiveFibreCriticalCurrent(log p,p^(-1/2),e)
  = criticalMellinAtomWeight(p^(e+1)).
```

Moreover

```text
J_u(p,e)^2
  = (log p)^2/p^(e+1) * exp(-u log(p^(e+1))).
```

Thus the new amplitude is not a fitted `sqrt(log X)` multiplier.  It is the literal primitive
half-density already present in the Euler/Gamma source.

## Unconditional theorem B — reflected modular carrier

Define

```text
r_i = 2(e+1) log(p^(-1/2)),
J_a(i) = J_0(i) exp(a r_i).
```

Then

```text
J_a(i) J_(-a)(i) = J_0(i)^2,
r_i = -2h_i,
J'_0(i) = -log(n_i) criticalMellinAtomWeight(n_i).
```

The reflection-odd exterior is formed before fusion:

```text
O_a(i,j) = (E_a(i,j)-E_(-a)(i,j))/2.
```

It is odd under `a -> -a` and antisymmetric under `i <-> j`.  Its algebraic center jet is

```text
dot O_0(i,j)
  = J_0(i)J_0(j)(r_i+r_j)(h_i-h_j)
  = -2J_0(i)J_0(j)(h_i^2-h_j^2).                       (PPES-1)
```

Equation `(PPES-1)` is the squared-height transgression: modular reflection supplies one source
logarithm beyond ordinary exterior polarization.

## Unconditional theorem C — division-free Gamma-anchor shorting

For any source height anchor `H`, define

```text
O_H(i,j) = dot O_0(i,j) + 4H E_0(i,j).
```

Then exactly

```text
O_H(i,j)
  = -2J_0(i)J_0(j)
      ((h_i-H)^2-(h_j-H)^2).                            (PPES-2)
```

This is a division-free longitudinal counterterm.  It centers the squared modular height before
scalar fusion and retains the transverse height difference.

For `tau>=0`, define the finite pair scalar

```text
q_(H,tau)(i,j)
  = -(1/2) O_H(i,j) sin(tau(h_i-h_j)).
```

If `h_i,h_j>=H` and `|tau(h_i-h_j)|<=pi`, then

```text
q_(H,tau)(i,j)>=0.
```

Hence every finite packet above the anchor has a nonnegative source-only scalar energy.

At the sixth-power aperture

```text
L_m=6 log m,
H_m=L_m/3=2 log m,
```

every prime in `(2m^4,5m^4]` has `h_p>H_m`.  The anchor is therefore determined by the first-clock
source aperture, not by a target point or bad coefficient.

## Unconditional theorem D — hard-block landing and optimal singular rate

At depth zero put

```text
j_p=(log p)p^(-1/2).
```

For every certified hard-block prime,

```text
(1/2)j_p <= bad_p(L_m) <= j_p.                          (PPES-3)
```

The primitive promotion itself obeys

```text
log(2m^4) < P(p,0)^2 <= log(5m^4).                      (PPES-4)
```

The existing class theorem says every exterior carrier dominating the block bad-mass square must
pay squared multiplier growth at least a constant times `log(2m^4)`.  `(PPES-4)` constructs that
rate from the source; `(PPES-3)` proves it lands on the literal obstruction cellwise.  This closes
the former existential question “where can the missing `sqrt(log X)` amplitude come from?”

## Conjecture ledger

### `J-PPES0` — finite two-scale domination

`[LEAN-PROVED] [SOURCE-DEFINED]`

Take the fixed source dilation and phase

```text
K=2^32,
tau=1/64.
```

For `n>0`, write

```text
eta_n(p)=(1/2)log p-(1/2)log n,

Q_n(p,q)=j_p j_q (eta_n(q)^2-eta_n(p)^2)
                    sin((eta_n(q)-eta_n(p))/64),

R_n=2 sum_(p in P_n) sum_(q in P_(Kn)) Q_n(p,q).
```

The low block has `eta_n(p) in [0,1]`; the high block has `eta_n(q) in [8,17]`.
Jordan's sine bound then gives the unconditional pair inequality

```text
3 j_p j_q <= Q_n(p,q).                                (PPES-5)
```

Chebyshev mass, without computation, gives

```text
sqrt(n)/12 <= sum_(p in P_n) j_p <= 10 sqrt(n).        (PPES-6)
```

Consequently, for `exp(20)<=n`,

```text
100 n <= R_n.                                          (PPES-7)
```

Combining `(PPES-3)`, `(PPES-6)`, and `(PPES-7)` proves, for `n=m^4`,

```text
(sum_(p in P_(m^4)) bad_p(L_m))^2 <= R_(m^4).          (PPES-8)
```

Thus primitive promotion plus the modular squared-height jet is sufficient for complete finite
hard-block domination.  The deliberately crude constants isolate existence from the genuinely
open cofinal budget problem.

### `J-PPES1` — cofinal Gamma/co-Poisson shorting

`[OPEN CORE] [DISTANCE 2]`

Construct one aperture-coherent relation `S_L` whose finite restrictions are `(PPES-2)`, whose
anchor is the completed Gamma/co-Poisson longitudinal coordinate, and whose source-height phased
scalarization is compatible under aperture refinement.

This is not ordinary closure.  Breadth must remain relation-valued/nonclosable and reflected depth
must remain beyond every finite Rees grade, as required by the biaxial source law.

### `J-PPES2` — uniform Route J budget

`[OPEN CORE] [DISTANCE 3]`

For the cofinal scalar current from `J-PPES1`, prove source-faithfully

```text
C_x(L)<0 -> C_x(L)^2 <= R_x(L),
sup_(x,L) R_x(L) < infinity.
```

Finite hard-block domination alone does not imply this.  The upper bound must arise from completed
Gamma/co-Poisson cancellation before any absolute prime norm or scalar fusion is taken.

## Anti-theatre and novelty audit

- Object is defined entirely from prime, valuation depth, Euler amplitude, Gamma radius, source
  height, aperture, and modular reflection.
- No Xi zero, zero status, multiplicity, desired sign, negative part of `C_x`, or interpolated jet
  enters any coefficient.
- `sqrt(log p)` is derived by exact landing on the primitive current, not chosen to satisfy the
  previously known lower-rate theorem.
- `(PPES-1)` and `(PPES-2)` are positive constructions, not restatements of a no-go.
- Internal collision audit found the existing Cauchy/Calderón commutator source-agnostic and the
  existing bounded exterior source-amplitude deficient.  Neither contains primitive landing,
  modular squared-height transgression, Gamma-anchor centering, and hard-cell sandwich together.
- Weighted-prime estimates alone are not claimed as novel.  External priority for the complete
  source conjunction is not certified.
- Route J remains open until `J-PPES1`--`J-PPES2` are discharged or this exact survivor is killed
  with its strongest positive replacement formalized.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedExteriorSource.lean
  CCMFirstClockPrimitivePromotedTwoScaleDomination.lean
```

The module proves all unconditional statements above with no `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, computation, or RH input.  It is wired into `RHTower.lean`.

## Log

- 2026-08-02 — source object constructed; primitive landing, modular reflection, squared-height
  transgression, Gamma-anchor shorting, finite positivity, hard-cell sandwich, and optimal
  singular-rate bounds proved in Lean.
- 2026-08-02 — `J-PPES0` closed in Lean: explicit fixed-dilation source current dominates the
  complete hard-block bad-mass square.  Aperture-coherent completed-source renormalization and its
  uniform budget remain open.

## Orientation-transgression correction: source transport before trace

The publication-ready orientation-transgression source law rules out treating the scalar
Gamma/co-Poisson cell as the completed object. Required order is

```text
labelled degree one
  -> vector-valued exterior cup
  -> singular reflected boundary transport
  -> Hodge polarization
  -> orientation trace.
```

Accordingly `J-PPES1` now has a finite algebraic part and a genuinely cofinal part.

### `J-PPES1a` — normalized Gamma/co-Poisson Green transport

`[LEAN-PROVED] [SOURCE-DEFINED]`

For `pe=(p,e)`, set

```text
C_pe(z,w)=-(e+1)^(-1)
  gammaCoPoissonIntervalCell (-(e+1)log(p)) z w.       (PPES-9)
```

This normalization is forced, not fitted:

```text
C_pe(1+a,1+a)=J_a(pe),                                (PPES-10)

(z-w)C_pe(z,w)
 =(e+1)^(-1)(
    exp((w-1/2)L_pe)-exp((z-1/2)L_pe)),               (PPES-11)

L_pe=-(e+1)log(p).
```

It is also exactly the negatively oriented ordinary-integer
Gamma/co-Poisson Euler jet. For depths `r,s`, interval concatenation gives the exact barycentric
law

```text
((r+1)+(s+1)) C_(p,r+s+1)
 =(s+1) exp((z-1/2)L_(p,r)) C_(p,s)
  +(r+1) C_(p,r) exp((w-1/2)L_(p,s)).                 (PPES-12)
```

No Euler-depth limit or scalar renormalization is inserted.

At one cell, `C_pe(z,w)` acts on the rational-Witt packet leg of
Calderón--Witt degree one while fixing the Calderón-defect leg. Its exterior lift satisfies

```text
cup o T_pe = (C_pe(z,w) id) o cup,                    (PPES-13)
T_pe o GreenSection = GreenSection o (C_pe(z,w) id), (PPES-14)
GreenRetraction o T_pe = T_pe^I o GreenRetraction.   (PPES-15)
```

This is vector-valued chain transport before orientation trace.

### Prime-power-cell source object

Existing all-prime Calderón--Witt source retains prime labels but identifies Euler depths.
Route J needs independent cells, so define

```text
A1_cell = directSum_(pe : Nat.Primes x Nat) A1_(pe.prime),
A2_cell = directSum_(pe : Nat.Primes x Nat) A2_(pe.prime).       (PPES-16)
```

Componentwise local cup defines an onto exterior cup

```text
d1_cell : exteriorSquare(A1_cell) -> A2_cell.          (PPES-17)
```

Its kernel is the cell Milnor-incidence sector. Every unequal-cell exterior pair belongs to this
kernel, including two distinct depths at the same prime. The explicit cellwise Koszul section
splits `(PPES-17)`, hence gives a canonical Green retraction.

For every coefficient family `c(pe)`, diagonal packet-leg transport is a chain map and is natural
for both Green section and Green retraction. Taking `c(pe)=C_pe(z,w)` constructs the complete
finite-support Gamma/co-Poisson source transport. In particular, every Route J cross-cell carrier
is its own canonical Green primitive: orientation trace and cup quotient erase it exactly.

This is new infrastructure forced by the paper's operation order. It closes source existence and
finite-stage transport compatibility; it does not manufacture the missing analytic estimate.

### `J-PPES1b` — cofinal sector-preserving extension

`[OPEN CORE] [DISTANCE 1]`

Extend the finite-support cell transport through aperture refinement to the singular
beyond-finite-Rees completion and prove that its explicit incidence endomorphism preserves the
admitted positive/Hodge sector. Because cross-cell energy lives entirely in incidence, a
boundary-blind orientation consumer cannot prove this: by orientation-transgression completeness
it sees only the one orientation line.

The exact missing statement is now:

```text
T^I_(z,w)(S_L) subset S_L
```

for the source-defined cofinal admitted sector `S_L`, compatibly in `L`, together with reflected
odd Hodge positivity. Scalarization before this theorem deletes the object that carries Route J
energy.

## Expanded Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedGammaCoPoissonGreenTransport.lean
  CCMFirstClockPrimitivePromotedPrimePowerCellGreenTransport.lean
```

Both modules are wired into `RHTower.lean`. Direct `lake env lean` checks pass. Proofs use no
`sorry`, `admit`, new axiom, `opaque`, `unsafe`, computation, or RH input.

## Log extension

- 2026-08-02 — orientation-transgression paper incorporated. Primitive promotion identified as
  exact depth-normalized Gamma/co-Poisson confluence, with spectral boundary and all-depth
  concatenation proved in Lean.
- 2026-08-02 — constructed independent prime-power-cell Calderón--Witt source, diagonal
  Gamma/co-Poisson cup chain map, cell Koszul--Green splitting, incidence transport, and Green
  naturality. Same-prime unequal-depth carriers are proved exact and equal to their own Green
  primitives. New same-prime depth-escape theorem proves every such carrier has nonzero
  reflection-odd Gamma coefficient at every nonzero modular displacement. Thus required
  countertransport must be depth-nonlocal inside each prime; cross-prime sewing alone cannot work.
  Remaining survivor is cofinal sector preservation and Hodge-positive uniform budget.

## Cofinal source-normal depth countertransport

### Competing constructions and hostile elimination

Three superficially plausible completions were tested before fixing a source object.

1. The ambidextrous Sonin corner and its adjoint are contractions, but their cofinal
   compositions preserve the source Gram matrix.  They cannot cancel the linear floor in
   `(PPES-7)` or create the missing Hodge column.
2. Orthogonally projecting onto the kernel of the reflection-odd Gamma functional would preserve
   that kernel with norm one, but this is tautological: it starts from the desired admitted
   sector, changes the finite current, and gives no arithmetic aperture compatibility.
3. Uniformly averaging unrenormalized deeper Euler cells loses the depth-zero primitive by the
   factor `p^(-r/2)`.  Restoring that primitive forces the unique source-normal
   deattenuation described below.  This is the only candidate of the three which retains the
   literal finite current.

Write

```text
A(p,r)=J_0(p,r)=log(p)/sqrt(p^(r+1)),
K(p)=ceil(log p).
```

For every prime and realization depth `r`, define the forced critical deattenuation

```text
D(p,r)=A(p,0)/A(p,r).                                  (PPES-18)
```

Positivity of `A` and the exact primitive-amplitude square law give

```text
D(p,r)^2=p^r,
A(p,r)D(p,r)=A(p,0).                                  (PPES-19)
```

Thus `(PPES-18)` is the primitive gauge `p^(r/2)` already forced by the source law; it is not an
adjustable normalization.  The prime-dependent depth count is also forced at sharp logarithmic
order.  Since `K(p)>=log p`, spreading the landed cell equally over the actual depths
`0<=r<K(p)` changes its squared source-normal cost from

```text
A(p,0)^2=log(p)^2/p
```

to

```text
sum_(r<K(p)) (A(p,r)D(p,r)/K(p))^2
  =A(p,0)^2/K(p)
  <=log(p)/p.                                          (PPES-20)
```

A bounded number of depths would retain the logarithmically divergent block cost, so logarithmic
depth is the first possible equal-spreading order.  Larger schedules work but add no information.

### Vector-valued two-scale countertransport

For a low/high pair in the two-scale source, put

```text
Q_n(p,q)=anchoredCrossPair(n,p,q).
```

Retain the original source record `(n,p,q)` and realize it at every actual depth rectangle

```text
0<=r<K(p), 0<=s<K(q).
```

Before physical Gamma landing, multiply the shifted cell carrier by

```text
2 D(p,r)D(q,s)/(K(p)K(q))
```

and retain the original squared-height/phase factor in `Q_n(p,q)`.  After landing, every
coordinate has the constant coefficient

```text
U_n(p,q,r,s)=2Q_n(p,q)/(K(p)K(q)).                    (PPES-21)
```

This is genuinely depth-nonlocal within both primes.  It is also a chain-level object: each
shifted cross-prime exterior carrier is in cell Milnor incidence and is its own Green primitive,
so their finite source-weighted sum has the same two properties.

The singular depth codiagonal recovers the finite current term by term:

```text
sum_(r<K(p)) sum_(s<K(q)) U_n(p,q,r,s)=2Q_n(p,q),

sum_(p,q,r,s) U_n(p,q,r,s)=R_n.                       (PPES-22)
```

No scalar normalization of `R_n` occurs.  The amplitude is transported into depth before the
singular codiagonal is read.

### Compensated finite-index reflection symmetry

On the doubled ordered-pair realization, a compensated finite-index reflection acts by exchanging
the exterior legs,
reversing each finite depth interval, and applying the orientation sign:

```text
(p,q,r,s) |-> (q,p,K(q)-1-s,K(p)-1-r).                (PPES-23)
```

The scalar kernel is symmetric:

```text
Q_n(q,p)=Q_n(p,q),
```

because both the squared-height difference and sine phase change sign under exchange.  The
profile `(PPES-21)` is constant on each depth rectangle.  Hence `(PPES-23)` fixes the landed
profile; the exterior swap sign is exactly cancelled by the odd orientation local system.
Therefore the countertransport commutes with this compensated finite-index involution and
preserves its fixed and antifixed sectors.  This is an explicit permutation/intertwining law, not
membership installed by projection.  It is not, by itself, membership in the actual admitted
Gamma/Hardy sector, whose reflection defect retains every ordered prime/depth coordinate.

### Uniform source-normal carrier capacity

Define the pretrace carrier capacity

```text
U_n =
 sum_(p in P_n) sum_(q in P_(K n))
 sum_(r<K(p)) sum_(s<K(q))
   U_n(p,q,r,s)^2.                                     (PPES-24)
```

The low/high height ranges already proved in Lean give

```text
0<=relativeHeight(n,p)<=1,
8<=relativeHeight(n,q)<=17.
```

Consequently

```text
0<=Q_n(p,q)<=289 A(p,0)A(q,0).                        (PPES-25)
```

For either fivefold prime block `P_x`, the Chebyshev upper bound and `p>2x` give

```text
sum_(p in P_x) A(p,0)^2/K(p)
 <=sum_(p in P_x) log(p)/p
 <=(1/(2x))sum_(p in P_x)log p
 <=5.                                                   (PPES-26)
```

Using `(PPES-21)`, finite Fubini, `(PPES-25)`, and `(PPES-26)` yields the unconditional,
aperture-independent bound

```text
0<=U_n
 =4 sum_(p,q) Q_n(p,q)^2/(K(p)K(q))
 <=100*289^2.                                           (PPES-27)
```

Thus the cofinal depth-nonlocal countertransport exists, is fixed by the compensated finite-index
reflection, retains the exact finite two-scale readout, and has uniform source-normal carrier
capacity.  Hostile boundary audit below proves that for nonzero modular displacement every
nonzero finite spread fails the actual Gamma/Hardy admitted-sector condition.

### Anti-theatre boundary: carrier capacity is not yet Route-J residual capacity

Equation `(PPES-27)` must not be substituted for `J-PPES2`.  The codiagonal in `(PPES-22)` is
necessarily singular.  Indeed, on the moving source carrier its operator norm obeys

```text
||Sigma_n|| >= R_n/sqrt(U_n)
             >= (10/289)n                              (PPES-28)
```

once `(PPES-7)` applies.  Uniform carrier capacity and unbounded finite readout coexist precisely
because scalar fusion is nonclosable.  This is the demanded beyond-finite-Rees behavior, but it
does not by itself prove

```text
C_x(L)<0 -> C_x(L)^2 <= R_x(L)
```

with the bounded carrier capacity on the right.  The new hard frontier is exact: construct the
source Hodge polarization which compares the negative first-clock excursion directly with
`(PPES-24)` before the singular codiagonal, or prove that every such pretrace comparison has the
same norm-growth obstruction as `(PPES-28)`.

### Literature boundary

Burnol's co-Poisson/Sonine work supplies support-intertwining and complete/minimal zero systems
(`arXiv:math/0407443`, `arXiv:math/0203120`).  Connes--Consani's scaling Hamiltonian supplies
the semilocal Sonine/scaling setting (`arXiv:1910.14368`).  The targeted audit found no theorem
constructing the source-specific ratio `(PPES-18)`, logarithmic prime-dependent actual-depth
spread, reflected exterior intertwining, and uniform block capacity `(PPES-27)` together.
Novelty is claimed only for that conjunction and remains provisional.

### Compensated-sector closure audit and actual-boundary correction

The coordinate identity `(PPES-23)` alone is not enough to claim preservation of a Hodge sector:
it could hide the exterior sign in prose.  The doubled carrier therefore carries two explicit
operations.  If `x` is a profile on the reversed ordered pair, raw exterior reflection is

```text
(R_ext x)(r,s)=-x(K(q)-1-s,K(p)-1-r),                 (PPES-29)
```

and the odd orientation local system is

```text
(O_odd x)(r,s)=-x(r,s).                               (PPES-30)
```

The compensated reflected Hodge operator exchanges the two ordered orientations and applies
`O_odd R_ext`.  Both signs are present, not suppressed.  Finite interval reversal is involutive,
so

```text
H_ref^2=1.
```

Combining this with `Q_n(q,p)=Q_n(p,q)` proves the doubled landed profile

```text
(U_n(p,q,-,-),U_n(q,p,-,-))
```

lies in `Fix(H_ref)` for every source pair.  This is the concrete compensated finite-index sector
used by the countertransport.

There are two honest capacity conventions.  Equation `(PPES-24)` counts one fundamental domain
of reflected ordered-pair orbits.  The raw Hilbert norm of the doubled fixed-sector carrier counts
both orientations and is exactly

```text
U_n^H=2U_n <= 200*289^2.                              (PPES-31)
```

Thus compensated-sector preservation does not depend on quotienting away half of the carrier, and
uniform capacity survives without changing order.  It must not be identified with

```text
ker(actual Gamma/Hardy boundary reflection defect).
```

The Hellinger--Hodge Green-descent law shows that the actual defect is evaluated before ordered
coordinates are fused and that one canonical cross-prime exact boundary detects every nonzero
modular displacement.  The cell-diagonal rigidity theorem strengthens this from one witness to
the entire finite canonical carrier span:

```text
ker(partial_a) intersect C_cell = {0},  a!=0.
```

Hence neither the finite one-sided spread nor its doubled reflected version is actually admitted
when `a!=0`; the reversed orientation occupies a different ordered boundary coordinate.  Only a
genuinely completion-relation/source-corona object can remain.  The exact Lean objects and
theorems for the compensated construction are:

```text
rawExteriorDepthReflection
oddOrientationDepthTwist
compensatedDepthReflection
reflectedDepthHodge
reflectedDepthHodge_sq
doubledLandedDepthPairProfile_mem_reflectedDepthHodgeSector
reflectedHodgeCountertransportCapacity_eq
reflectedHodgeCountertransportCapacity_le
```

in

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedCofinalDepthCountertransport.lean
```

The same module formalizes `(PPES-18)`--`(PPES-22)`, `(PPES-25)`--`(PPES-28)`, actual
prime-power-cell incidence realization, and Green fixedness.  Direct `lake env lean` and the
targeted module build pass.  `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.

The correction and exact finite-span classification are formalized in

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity.lean
```

### Pure-incidence two-leg correction and terminal readout audit

Finite mixed carriers fail actual admission, but the cell source has a complementary nonzero pure
sector.  For distinct cells `i,j`, both `d_i wedge d_j` and `w_i wedge w_j` are exact incidence and
are annihilated by every actual mixed Gamma/Hardy boundary coordinate.  Packet-leg transport acts
on the second by `c_i c_j`; therefore the forced depth deattenuation constructs a complete
prelanding cofinal carrier whose source transport lands exactly on

```text
U_n(p,q,r,s)
  ((d_(p,r) wedge d_(q,s)) + (w_(p,r) wedge w_(q,s))).
```

This carrier is actually admitted at every displacement, Green-fixed, fixed by pure exchange, and
has two-component capacity at most `200*289^2`.  Thus the missing two-leg source transport and
actual finite admission are genuinely constructed.

They still cannot furnish Route-J residual capacity.  Exact codiagonal has gain at least
`(5/289)n`.  A generic Lean theorem shows that no continuous linear functional on any complex
seminormed realization with the uniform carrier bound can retain every finite codiagonal.  This
closes the pure-Hodge bounded-readout class, including alternative normed completions; changing
topology can evade the theorem only by losing the stated capacity or scalar descent.

Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedPureHodgeCountertransport.lean
```

The surviving producer is not another finite carrier.  It is the source-derived closed admission
object with coefficient-faithful unsquared mixed finite trace described in the oriented
source-admission theorem.
