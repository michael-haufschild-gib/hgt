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
