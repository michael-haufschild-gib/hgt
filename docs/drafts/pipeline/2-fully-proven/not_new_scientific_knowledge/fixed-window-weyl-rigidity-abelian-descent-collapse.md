# Fixed-Window Weyl Rigidity and Abelian Descent Collapse

- **ID:** fixed-window-weyl-rigidity-abelian-descent-collapse
- **Stage:** 1-in-progress (complete paper proofs below; hostile re-read pending before 2-move)
- **Type:** THEOREM (two support theorems; elementary, unconditional)
- **Label:** [PROVED HERE pending re-read] [BRIDGE / search-space theorem] [NOT AN RH RESULT]
- **Parent:** `prime-covering-descent-index-divisibility-rh.md` (OPEN CORE 1);
  strengthens kill-condition 4 of `height-adaptive-cancelled-source-socle-weyl-rh.md`.

## Theorem 1 (fixed-window Weyl rigidity)

**Setup.** Let `Omega ⊂ C` be a bounded domain, `A` holomorphic on a neighborhood of
`closure(Omega)`, not identically zero, with finite zero divisor `{(rho_i, m_i)}_{i=1..r}` in
`Omega` and no zeros on `∂Omega`. Put
`Q := directSum_{i=1..r} C[x]/(x^{m_i})`, `d := sum_i m_i >= 1`,
realized as jets of holomorphic functions at the `rho_i` (for planar domains the jet map
`O(Omega) -> Q` is surjective with kernel `(A)`, by Weierstrass interpolation on planar Stein
domains; alternatively take `Q` as the definition). Fix a prime `p`, let `u ∈ Q` be the class of
`s ↦ p^{-s}`, and `M_u : Q -> Q` multiplication by `u`. Fix `k >= 1` and a primitive `2^k`-th
root of unity `zeta = exp(2*pi*i*a/2^k)`, `a` odd.

**Statement.** The following are equivalent for each of the three operator categories below:
there exists an invertible `W : Q -> Q` with `W M_u W^{-1} = zeta * M_u`, where `W` is

- (a) `C`-linear, or
- (c) semilinear over an algebra automorphism `sigma` of `Q` (`W(f*v) = sigma(f)*W(v)`),

**iff** the annulus image of the window divisor, i.e. the multiset
`R := {(p^{-rho_i}, m_i)}` in `C^*`, is invariant under multiplication by `zeta`; equivalently
the divisor `{(rho_i, m_i)}` is invariant under the vertical translation
`s ↦ s - 2*pi*i*a/(2^k * log p)  (mod (2*pi*i/log p)*Z)`.

For (b) `W` conjugate-linear, the same holds with `R` replaced by `conj(R)` on one side:
existence iff `conj(R) = zeta * R`, i.e. divisor invariance under the reflection
`rho ↦ conj(rho)` composed with the same vertical translation.

**Corollary (divisibility is the hypothesis, not the output).** If the window divisor is
nonempty, existence of such a `W` forces the annulus image to be a nonempty finite multiset
invariant under the free `Z/2^k` rotation action on `C^*` (free: `zeta^j * z = z` with `z ≠ 0`
forces `2^k | j`). The multiset therefore partitions into free orbits of size exactly `2^k`,
each carrying a constant per-point total multiplicity, so `2^k | d` outright. Constructing `W`
on a fixed window is therefore never a producer of divisibility: it presupposes a vertical
arithmetic-progression symmetry of the divisor that no source theorem supplies for hypothetical
Xi zeros.

### Proof

**Step 1 (local Jordan structure).** On the `i`-th block `C[x]/(x^{m_i})` (`x = s - rho_i`),
`M_u` is multiplication by the truncated series
`p^{-rho_i} * exp(-x*log p) = c_0 + c_1 x + ...` with `c_0 = p^{-rho_i} ≠ 0` and
`c_1 = -log(p) * p^{-rho_i} ≠ 0`. In the basis `1, x, ..., x^{m_i-1}` the operator is lower
triangular with constant diagonal `c_0`; `(M_u - c_0)` maps `x^j` to `c_1 x^{j+1} + O(x^{j+2})`,
so `(M_u - c_0)^{m_i - 1}(1) = c_1^{m_i-1} x^{m_i-1} ≠ 0`. Hence the block is a single Jordan
block `J_{m_i}(p^{-rho_i})`. The Jordan data of `M_u` is therefore exactly the multiset `R`:
eigenvalue `mu` carries one Jordan block of size `m_i` for each `i` with `p^{-rho_i} = mu`.

**Step 2 (scaling).** For any linear `T` on a `d`-dimensional space,
`charpoly(zeta*T)(X) = det(X*I - zeta*T) = zeta^d * charpoly(T)(X/zeta)`, and if
`T = lambda*I + N` is a Jordan block then `zeta*T = zeta*lambda*I + zeta*N` with `zeta*N`
similar to `N` by the diagonal conjugation `diag(1, zeta, zeta^2, ...)`. Hence the Jordan data
of `zeta*M_u` is `zeta * R` (eigenvalues rotated, block sizes unchanged).

**Case (a).** `W M_u W^{-1} = zeta*M_u` iff `M_u` and `zeta*M_u` are similar iff they have equal
Jordan data iff `R = zeta*R`. Unwinding `p^{-rho'} = zeta*p^{-rho}` gives
`rho' ≡ rho - (2*pi*i/log p)*(a/2^k) (mod (2*pi*i/log p)*Z)`. Conversely, equal Jordan data
yields a similarity `W`, proving the iff.

**Case (b).** Write `W = C ∘ B` with `C` coordinatewise conjugation in a fixed basis and `B`
invertible linear. For linear `T`, `C T C` has matrix `conj(matrix(T))`, so its Jordan data is
`conj(Jordan data of T)`. The relation becomes: Jordan data of `M_u` conjugated equals
`zeta * R`, i.e. `conj(R) = zeta * R`. Both directions as in (a).

**Case (c).** Setting `f = g = 1` in the semilinearity relation shows `W = M_{w_0} ∘ sigma_lin`
where `w_0 = W(1)` and `sigma_lin` is the linear map underlying the algebra automorphism
`sigma`; invertibility of `W` makes `w_0` a unit. Then, using commutativity of `Q`,
`W M_u W^{-1} = M_{w_0} M_{sigma(u)} M_{w_0}^{-1} = M_{sigma(u)}`, so the relation reads
`sigma(u) = zeta*u` in `Q`. Every algebra automorphism of `Q = directSum_i A_i` (`A_i` local
with pairwise-distinct... in general:) permutes the primitive idempotents, inducing a
permutation `tau` with isomorphisms `A_{tau(i)} -> A_i`; local isomorphisms
`C[x]/(x^m) -> C[x]/(x^{m'})` exist iff `m = m'` and are `x ↦ phi(x)`, `phi(x) = e_1 x + ...`,
`e_1 ≠ 0`. Componentwise, `sigma(u) = zeta*u` at constant terms reads
`p^{-rho_{tau(i)}} = zeta * p^{-rho_i}` — the same value-rotation condition — and at higher jets
`p^{-rho_{tau(i)}} * exp(-phi_i(x)*log p) = zeta * p^{-rho_i} * exp(-x*log p)` in
`C[x]/(x^{m_i})`; dividing the (equal, invertible) constant terms and taking the truncated
logarithm of the unipotent quotient forces `phi_i(x) ≡ x (mod x^{m_i})`. Hence `sigma` exists
iff the multiplicity-preserving value-rotation permutation `tau` exists, i.e. iff `R = zeta*R`.
Conversely, given the symmetry, define `sigma` by `tau` with identity local parts and take
`w_0 = 1`. ∎

**Remarks.**
1. If the window divisor is empty (`Q = 0`) everything holds vacuously; the theorem's content is
   for nonempty divisors — precisely the RH-false configurations a contradiction route feeds in.
2. The theorem covers every operator category in which the socle–Weyl generator was still
   allowed to live on the fixed window: linear, antilinear, and (via (c)) crossed-product-type
   generators `M_{w_0} sigma`. It upgrades kill-condition 4 of the socle card ("the generator
   must be semilinear/crossed-product") to: on a fixed window, semilinear does not help — the
   obstruction is the divisor's absent vertical-AP symmetry, in every category.
3. Nothing in the proof uses analyticity of the divisor's origin: it is a statement about finite
   local algebras. This makes it directly formalizable (see Lean plan).

## Theorem 2 (abelian descent collapse)

**Setup.** Fix `p`, `k >= 1`, `theta := 2*pi/(2^k * log p)`. Let `Omega_0` be a bounded domain
contained in a horizontal band of height `< theta`, and let
`S := union_{j=0}^{2^k - 1} (Omega_0 + i*j*theta)` (pairwise disjoint translates). Let `F` be
holomorphic on a neighborhood of `closure(S)` and zero-free on every `∂(Omega_0 + i*j*theta)`.
Let `N` be the number of zeros of `F` in `S` counted with multiplicity. Write `w = p^{-s}`; `w`
maps the `2^k` translates onto the `2^k` rotated copies `zeta_k^{-j} * W_0` of `W_0 := w(Omega_0)`,
where `zeta_k := exp(2*pi*i/2^k)`; thus `w(S)` is invariant under the free `Z/2^k` rotation and
the covering map `v = w^{2^k}` identifies all copies with `V_0 := (W_0)^{2^k}`-image.

**Statement.**
(i) If `F = P * R` on a neighborhood of `closure(S)` with `P, R` holomorphic and `P`
`i*theta`-periodic there (equivalently: `P` is the pullback `P = Ptilde ∘ (w ↦ w^{2^k})` of a
holomorphic `Ptilde` on a neighborhood of `closure(V_0)`), then
`N ≡ winding_{∂S}(R) (mod 2^k)`.
(ii) If moreover `R` is zero-free on `closure(S)`, then `2^k | N`, and the divisor of `F` in `S`
equals the divisor of `P` in `S`, which is invariant under `s ↦ s + i*theta` across the stack:
the divisor in `Omega_0 + i*j*theta` is the `i*j*theta`-translate of the divisor in `Omega_0`.
Thus a zero-free-remainder periodic factorization exists **iff** the stack divisor has exactly
the vertical-AP symmetry of Theorem 1.
(iii) (Matrix collapse) If `F, P, R` are `n x n`-matrix-valued with `det F` boundary-zero-free,
`P` periodic as above, and `N` is the winding of `det F` (the Toeplitz/argument-principle count),
the same conclusions hold with `R` replaced by `det R`: finite-dimensional fibres reduce to the
scalar case through the determinant.

### Proof

(i) Since `P*R` is zero-free on each `∂(Omega_0 + i*j*theta)` and both factors are holomorphic,
each factor is zero-free there, so all windings are defined. By the argument principle
`N = winding_{∂S}(F) = winding_{∂S}(P) + winding_{∂S}(R)`, where `winding_{∂S}` means the sum
over the `2^k` boundary contours. For the periodic factor: on the `j`-th contour, substituting
`s ↦ s + i*j*theta` and using periodicity, `winding_{∂(Omega_0 + i*j*theta)}(P) =
winding_{∂Omega_0}(P)` — all `2^k` contributions are equal — so
`winding_{∂S}(P) = 2^k * winding_{∂Omega_0}(P) ≡ 0 (mod 2^k)`.
(Equivalently in the `v`-coordinate: each copy maps onto the same downstairs contour
`∂V_0`, and `winding(Ptilde ∘ cover)` per copy `= winding_{∂V_0}(Ptilde)`.)

(ii) Zero-free `R` has `winding_{∂S}(R) = 0`, giving `2^k | N` by (i), and `div_S(F) =
div_S(P)`. Periodicity of `P` transports its zero set and multiplicities by `i*theta` wherever
both points lie in its domain, which contains a neighborhood of `closure(S)`; applied along the
stack this is exactly the stated AP-invariance. Conversely, if the divisor has the AP symmetry,
let `P(s) := prod_rho (1 - exp(2^k*log(p)*(rho - s)))^{m_rho}` over the divisor of `F` in
`Omega_0`: each factor is `i*theta`-periodic (its zero set is exactly `rho + i*theta*Z`, simple,
since `exp(2^k*log(p)*(rho-s)) = 1` iff `s ∈ rho + i*theta*Z`), so `div_S(P) = div_S(F)`.
*Neighborhood care:* `P` also vanishes at the AP-translates `rho + i*j*theta` with `j` outside
`0..2^k-1`, which lie OUTSIDE `closure(S)` at distance `>= theta - h > 0` (where `h < theta` is
the band height of `Omega_0`): a translate one step beyond the stack has imaginary part
displaced by at least `theta` from the corresponding window band. Hence on the open
`(theta - h)/2`-neighborhood of `closure(S)`, `R := F/P` is holomorphic and zero-free.

(iii) `det(P*R) = det(Ptilde ∘ cover) * det R` and `det(Ptilde ∘ cover) = (det Ptilde) ∘ cover`
is again a periodic scalar factor; apply (i)-(ii) to determinants. ∎

**Consequence for the parent card.** Any Fredholm realization of the stack count whose symbol is
scalar- or matrix-valued and descends along the covering abelianizes, via (iii), to a periodic
scalar factorization; by (ii) its existence with invertible remainder is equivalent to the
divisor AP-symmetry — which is Theorem 1's obstruction, not a producer. Hence the parent card's
descent operator must have infinite-dimensional (all-prime/adelic) symbol fibre, where no
determinant abelianization exists. The two support theorems together locate the exact boundary
of the commutative/finite part of the mechanism.

## Hostile audit checklist (pre-promotion)

- [x] Case (a) iff both directions (Jordan-form equality is necessary AND sufficient for
      similarity).
- [x] `c_1 ≠ 0` single-block argument (fails for general `u` with `u'(rho) = 0`; here
      `u' = -log(p)*u` never vanishes).
- [x] Case (c) `W` determined as `M_{w_0} ∘ sigma`; commutativity used; unit `w_0` cancels.
- [x] Theorem 2 disjointness of translates (band height `< theta`); boundary zero-freeness of
      each factor from that of the product.
- [x] Weierstrass periodization in (ii) converse: finite divisor per window, finite product,
      periodic elementary factors exist (`1 - e^{2^k log(p)(rho - s)}` has simple zeros exactly
      on `rho + i*theta*Z`... check: `e^{2^k*log(p)*(rho-s)} = 1` iff `s ≡ rho mod
      (2*pi*i/(2^k*log p))*Z = i*theta*Z`; yes).
- [x] First hostile pass (2026-07-18, same session, deliberate gap hunt): found and fixed
      (1) corollary understated — free-orbit partition gives `2^k | d` outright;
      (2) Theorem 2(ii) converse — periodized factor's zeros beyond the stack threatened
      holomorphy of `R` near `closure(S)`; fixed via band-height margin `theta - h`.
- [ ] Fresh-eyes re-read next session before moving to `2-fully-proven/not_new_scientific_knowledge/`.

## Lean plan (Gate 5, batched; after re-read)

1. Abstract core (new leaf module `RHTower/FixedWindowWeylRigidity.lean`):
   - `charpoly_smul`: `charpoly (zeta • T) = zeta^d * charpoly T ∘ (·/zeta)` (or the roots-multiset
     form via `Polynomial.roots`); mathlib: `LinearMap.charpoly`, `Matrix.charpoly_smul`-adjacent
     (verify exact names in /tmp scratch).
   - `similar_smul_iff_roots_rotation`: for operators with all Jordan blocks determined by a
     nonvanishing-derivative multiplication structure, similarity to `zeta • T` iff root-multiset
     rotation invariance. (Formalize at the multiset/charpoly level to avoid Jordan forms:
     similarity implies charpoly equality implies root rotation — the necessity direction, which
     is the direction the no-go needs. Sufficiency direction optional.)
   - Corollary: free rotation on nonempty finite invariant multiset in `C^*` forces `2^k ∣ card`.
2. Theorem 2 necessity direction (winding congruence) can be stated over existing corpus winding
   infrastructure if present; otherwise defer the analytic half and formalize only the algebraic
   half now (per minimal-build discipline).

## Lean status

- `formal/GaloisForLFunctions/RHTower/FixedWindowWeylRigidity.lean` — NEW (2026-07-18), builds
  clean (single-module `lake build`, 18s), umbrella-wired (`RHTower.lean` EOF append),
  `#print axioms` on `algMult_rotation`, `no_weyl_partner_of_asymmetric`, `dvd_orbit_sum` =
  `[propext, Classical.choice, Quot.sound]` only. Content = Theorem 1 necessity, abstract core:
  `algMult` (stabilized generalized-kernel dimension), conjugation/scaling invariance lemmas,
  `algMult_rotation` (Weyl conjugation forces zeta-rotation-invariant multiplicities),
  `algMult_orbit_sum`/`dvd_orbit_sum` (orbit mass = n * algMult, divisibility), and the no-go
  reading `no_weyl_partner_of_asymmetric`.
- Not yet formalized: the window-model instantiation (multiplication operator by `p^{-s}` on the
  zero algebra; Jordan single-block lemma), Theorem 1 sufficiency, cases (b)/(c), Theorem 2.

## Log

- 2026-07-18 (Fable session 1): both theorems proved on paper in full; card created. Same
  session: hostile pass (2 gaps fixed), abstract Lean core formalized unconditionally (see Lean
  status). Next: fresh-eyes re-read of the paper proofs, then move to 2-fully-proven; window-model
  Lean instantiation; then parent card OPEN CORE 2 (annulus model) and OPEN CORE 3
  (operator-valued candidate).

## Theorem 3 (covariant-family index rigidity) `[PROVED HERE, first pass]`

**Setup.** Stack `S = union_{j=0}^{2^k-1} (Omega_0 + i*j*theta)` as in Theorem 2. Let `H` be a
complex Banach space and `A` a holomorphic family on a neighborhood of `closure(S)` with values
in Fredholm operators on `H`, invertible on every window boundary `∂(Omega_0 + i*j*theta)`.
Write `M(A, Omega)` for the Gohberg--Sigal multiplicity (the operator argument principle:
total multiplicity of characteristic values of `A` in `Omega`; Gohberg--Sigal 1971,
`[LITERATURE]`, generalized Rouche/argument principle; also GGK, Classes of Linear Operators).

**Statement.** Suppose there are holomorphic families `E(s), F(s)` of INVERTIBLE operators on a
neighborhood of `closure(Omega_0 + i*j*theta)` for the relevant steps, with the deck covariance

> `A(s + i*theta) = E(s) * A(s) * F(s)`.

(Constant invertible `E = U`, `F = V` — in particular unitary adelic twists — are the special
case.) Then `M(A, Omega_j) = M(A, Omega_0)` for every `j`, hence
`sum_j M(A, Omega_j) = 2^k * M(A, Omega_0)`. Consequently no such family can satisfy the divisor
identification `M(A, Omega_j) = N_xi(Omega_j)` for all `j` unless all Xi window counts in the
stack coincide — which fails for variable window counts. Exactly covariant (even
holomorphically-cocycle-covariant) Fredholm families are divisor-blind.

**Proof.** (1) Parametrization invariance: `A_j(s) := A(s + i*j*theta)` is a holomorphic
Fredholm family near `closure(Omega_0)`, invertible on `∂Omega_0`, and
`M(A, Omega_j) = M(A_j, Omega_0)` (characteristic values and their partial multiplicities are
transported by the biholomorphic parameter shift; this is definitional for the GS multiplicity).
(2) Iterating the covariance, `A_j(s) = E_j(s) * A(s) * F_j(s)` with
`E_j(s) = E(s + i*(j-1)*theta) * ... * E(s)` and similarly `F_j` — finite products of
holomorphic invertible families, hence holomorphic invertible. (3) Equivalence invariance of
the GS multiplicity: `M(E A F, Omega_0) = M(A, Omega_0)` for holomorphic invertible `E, F`
(Gohberg--Sigal; the local Smith-form factorization `A = Phi * diag((s-rho)^{kappa_i}) * Psi`
is stable under multiplication by invertible holomorphic families, which only change
`Phi, Psi`). Hence `M(A_j, Omega_0) = M(A, Omega_0)`. QED.

**Remark (T2 strengthening).** With `H = C` the covariance degenerates to scalar
quasi-periodicity `P(s + i*theta) = c(s) * P(s)` with `c` holomorphic zero-free; the winding
argument of Theorem 2(i) is unchanged (zero-free multipliers preserve winding), so Theorem 2
holds verbatim with "periodic" relaxed to "quasi-periodic with zero-free cocycle".

**Consequence (singular-locus redirect).** T1-T3 close every symmetry/covariance-transport
implementation, INCLUDING holomorphic cocycle twists, of the `2^k`-divisibility mechanism. The
only structural place left where a deck-step mechanism can see the divisor is the SINGULAR
LOCUS of the deck cocycle: for Xi itself the scalar cocycle `xi(s + i*theta)/xi(s)` is
meromorphic with zeros/poles exactly on (shifted divisor) minus (divisor). A divisibility
producer must therefore read cocycle singularities — and the corpus's formalized decimation
Laurent-character law `R_j(rho)/R_(j-2)(rho) = r^(2*rho-1)` is exactly such a
cocycle-at-the-singular-fibre datum. This is the precise bridge from the closed
symmetry-transport family to the surviving census/recursion family: the census scalar must be a
finite-ring invariant of the deck-cocycle singularity structure.
