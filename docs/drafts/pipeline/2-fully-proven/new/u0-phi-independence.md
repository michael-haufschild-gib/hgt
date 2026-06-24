# u0 ⊥ phi_b — Algebraic Independence of the Bottcher c-Velocity

- **ID:** u0-phi-independence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Bottcher family / inverse-Bottcher obstruction lane
- **Statement:** For `b in M \ {0,-2}`, `u0(z)` and `phi_b(z)` are algebraically independent over `Qbar(b,z)`.

Disconnected case: separate card `../1-in-progress/u0-phi-independence-disconnected.md`.

## Definitions

Let

`f_b(z)=z^2+b`.

Let `phi_b` be the inverse Bottcher coordinate near infinity:

`phi_b(f_b(z))=phi_b(z)^2`, `phi_b(z)=z+O(z^-1)`.

Let

`u0(z)=sum_{n>=0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`.

Equivalently, `u0=(partial_c phi_c)|_{c=0}`, the `c`-velocity of the inverse Bottcher family at the monomial fiber.

With `x=1/z`,

`U0(x)=u0(1/x)=sum_{n>=0} 2^{-(n+1)} x^{2^{n+1}-1}`.

The exponents have Hadamard gaps and coefficient radius `1`, so the Ostrowski-Hadamard gap theorem gives `|x|=1` as a natural boundary for `U0`. Equivalently, `u0` cannot be analytically continued through any point of `|z|=1`.

Exceptional values in the connected locus:

- `b=0`: `phi_0(z)=z`;
- `b=-2`: Chebyshev case, `phi_-2` is algebraic over `C(z)`.

## Theorem `[PROVED HERE]`

For `b in M \ {0,-2}`, no nonzero polynomial `P in Qbar(b)[z,U,Y]` satisfies

`P(z,u0(z),phi_b(z))=0`

as germs near infinity.

## Proof

### 1. Bottcher continuation in the connected case

For `b in M`, the filled Julia set `K_b` is connected. Hence the basin of infinity

`Omega_b = C \ K_b`

contains no finite critical point of `f_b`; the only finite critical point is `0`, and `0 in K_b`. Therefore the Bottcher coordinate extends single-valuedly and analytically through the whole basin `Omega_b`.

### 2. The basin crosses the unit circle for `b != 0`

Assume, for contradiction, that

`Omega_b cap {|z|=1} = empty`.

Then `{|z|=1} subset K_b`. Since `Omega_b` is connected and contains infinity, it lies in the exterior component of the complement of the unit circle; hence the closed unit disk is contained in `K_b`.

The filled Julia set of a monic polynomial has logarithmic capacity `1`, and the closed unit disk also has capacity `1`. Suppose `K_b` strictly contains the closed unit disk. Choose `p in K_b` with `|p|>1`. Since `K_b` is compact and connected and contains the closed unit disk, continuum connectivity supplies a compact continuum `C subset K_b` meeting the disk and containing `p`. For a small `epsilon>0` with `1+epsilon<|p|`, the component `E` of `C cap {|z| >= 1+epsilon}` containing `p` also meets `{|z|=1+epsilon}`; hence `E` is a nondegenerate compact continuum outside the closed disk, and is nonpolar.

This gives strict capacity increase by an energy test. Let `sigma` be the equilibrium measure of the closed unit disk, so `I(sigma)=0` and `U^sigma(w)=log(1/|w|)` for `|w|>1`. Choose a probability measure `nu` on `E` with finite logarithmic energy. Since `|w|>=1+epsilon` on `E`, the cross-energy `int U^sigma dnu` is at most `-log(1+epsilon)<0`. For `mu_t=(1-t)sigma+t nu`, the energy `I(mu_t)` is negative for all sufficiently small `t>0`. Hence `cap(K_b) >= exp(-I(mu_t))>1`, contradicting `cap(K_b)=1`. Thus equality of capacities forces

`K_b = { |z| <= 1 }`.

Then `J_b=partial K_b={|z|=1}`. Since Julia sets are completely invariant,

`f_b(J_b)=J_b`.

Thus for every `|z|=1`,

`|z^2+b|=1`.

Writing `z=e^{i theta}` gives

`1+|b|^2+2 Re(b e^{-2i theta})=1`

for all `theta`, forcing `b=0`. This contradicts `b != 0`. Therefore

`Omega_b cap {|z|=1} != empty`.

Since `Omega_b` is open, this intersection contains an arc of the unit circle.

### 3. Algebraic relation would continue `u0` through its natural boundary

Assume a nonzero relation

`P(z,u0(z),phi_b(z))=0`

with `P in Qbar(b)[z,U,Y]`.

If `P` has degree zero in `U`, then it gives algebraicity of `phi_b` over `Qbar(b,z)`. This contradicts Becker-Bergweiler for nonexceptional `b`, hence for `b in M \ {0,-2}`.

Now assume `U` occurs. Let `F(T)` be the minimal polynomial of `u0` over the germ field `Qbar(b)(z,phi_b(z))`. Characteristic zero makes `F` separable. On `Omega_b`, `phi_b` is analytic, so the leading coefficient and discriminant of `F` become analytic functions. They are not identically zero; their zero sets are discrete.

Choose a crossing point

`z0 in Omega_b cap {|z|=1}`

on the arc from Step 2, avoiding those discrete bad sets. Also choose a path in `Omega_b` from the large-`|z|` germ domain to a small neighborhood of `z0`, avoiding the same branch locus. Along this path, the algebraic branch representing `u0` continues analytically. Near `z0`, the algebraic implicit function theorem gives an analytic branch equal to the continued `u0` branch.

Thus `u0` analytically continues through `z0`, and equivalently `U0(x)=u0(1/x)` analytically continues through the corresponding point of `|x|=1`. This contradicts the natural boundary from the Ostrowski-Hadamard gap theorem.

Both cases are impossible, so no such relation exists. Therefore `u0` and `phi_b` are algebraically independent over `Qbar(b,z)`. QED.

## Source Boundary

Source anchors checked:

- Nguyen, `Algebraic independence of local conjugacies and related questions in polynomial dynamics`, arXiv:1310.2329: covers local conjugacies `psi_f(u(t))`; inverse Bottcher-coordinate independence is left as a question.
- Fernandes survey / Becker-Bergweiler: algebraic Bottcher functions for polynomials are exactly the monomial/Chebyshev list; otherwise they are transcendental/hypertranscendental.
- Pritsker, `Mahler measure of polynomial iterates`: records capacity `1` for monic polynomial Julia sets.
- Standard complex dynamics: if the basin of infinity contains no finite critical point, the Bottcher coordinate extends through the whole basin.

This source boundary supports correctness of the proof. It is not by itself a novelty proof.

## Significance

`u0=(partial_c phi_c)|_{c=0}` is the tangent leak that blocks the naive `c1 -> 0` descent in the inverse-Bottcher independence problem. The theorem proves that, on the connected nonexceptional parameter locus, this leak is algebraically independent from the target Bottcher coordinate rather than an artifact of the specialization proof.

If source-new, this is significant because it converts a failed-descent obstruction into a theorem for a native mixed object: a monomial-fiber parameter derivative versus a nonexceptional inverse Bottcher coordinate.

## Theatre Status / Votes

- Professor (id=1592): correctness `accept-connected-proof`; novelty `hold-pending-team-vote`
- Haiku (id=1595): `novel+significant` — Nguyen covers ψ_c not φ_c; Becker–Bergweiler only kills deg_U=0 case; Mahler machinery doesn't cover the mixed-map pair; M–S/Xie/Baker–DeMarco cover different questions. Two proof-text fixes required (wording "contains" fix applied above; crossing path in Step 3 explicit).
- Wheeler (id=1594): `novel+significant` — u₀ as c-velocity is not a named object anywhere; the pair (c-velocity, Böttcher) is not in any source; BRIDGE not search.

Three agents: correctness accepted; novelty+significance: 2/3 explicit yes votes. The capacity step is now written directly by the energy test in Step 2, rather than deferred to a broad Ransford citation.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack via natural boundary plus capacity
- [x] 1 -> 2 fully-proven: connected case proof above, disconnected overclaim split out
- [ ] 2 -> 3 formalized: Lean theorem `u0_phi_independence_connected`
- [ ] 3 -> 4 publication-ready

## Log

- 2026-06-23 - connected theorem split from disconnected case after Haiku flagged the disconnected continuation gap.
- 2026-06-23 - Professor audit addendum folded into the proof: generic crossing point, branch continuation path, and capacity equality details made explicit.

## 2026-06-23 capacity-step clarification

The capacity argument in Step 2 is not the false general claim that equal capacities imply polar set-difference. It uses connected/full strictness.

If connected full `K_b` contains the closed unit disk and also contains a point outside it, connectedness supplies a nondegenerate continuum in `K_b` reaching outside the disk. A finite-energy probability measure on the outside continuum, mixed with small mass into the unit-disk equilibrium measure, has negative logarithmic energy because the cross-potential of the unit circle is `log(1/|w|)<0` outside the disk. Hence `cap(K_b)>cap(closed disk)`. Since both capacities are `1`, no such outside point exists, hence `K_b` is the closed disk.

Thus the connected `u0` proof avoids the polar-difference loophole flagged in the Q6.2 card.
