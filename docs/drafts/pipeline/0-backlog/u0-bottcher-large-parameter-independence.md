# u0-Bottcher Large-Parameter Independence

- **ID:** u0-bottcher-large-parameter-independence
- **Stage:** 0-backlog
- **Type:** CANDIDATE / theorem proof
- **Source:** research chat 2026-06-23; inverse-Bottcher cross-transfer note
- **Statement:** `[THEOREM CANDIDATE]` If `|b| > 2+sqrt(2)`, then `u_0(z)` and the quadratic inverse Bottcher coordinate `phi_b(z)` are algebraically independent over `C(z)`, hence over `Qbar(b,z)`.

## Goal

This card isolates the first proof-shaped residue from the inverse-Bottcher specialization obstruction.

The generic specialization `c1 -> 0` introduces the tangent Mahler section

`u_0(z)=sum_{n>=0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`,

so Becker--Bergweiler's individual transcendence of `phi_b` is not enough. The goal here is to prove algebraic independence of the leaked section `u_0` from a nonexceptional Bottcher coordinate on an explicit parameter region, without pretending the mixed-map Mahler obstruction has been solved in general.

## Gates

- [ ] 0 -> 1 in-progress: source-pure statement, exact Bottcher continuation domain cited, source search for exact mixed-pair theorem
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open source dependency
- [ ] 2 -> 3 formalized: not currently Lean-targeted
- [ ] 3 -> 4 publication-ready: only as part of an inverse-Bottcher independence note

## Definitions

Let

`f_b(z)=z^2+b`

and let `phi_b` be the inverse Bottcher coordinate near infinity:

`phi_b(f_b(z))=phi_b(z)^2`, `phi_b(z)=z+O(z^-1)`.

Let

`u_0(z)=sum_{n>=0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`.

Equivalently, `u_0` is the first parameter derivative at the monomial fiber:

`u_0(z) = (partial_c phi_c)(z)|_{c=0}`.

With `x=1/z`,

`U_0(x)=u_0(1/x)=sum_{n>=0} 2^{-(n+1)} x^{2^{n+1}-1}`

has the unit circle as a natural boundary by the Ostrowski--Hadamard gap theorem.

## Conditional Continuation Lemma

`[PROOF CANDIDATE]` Suppose a chosen analytic branch of `phi_b` continues from infinity into an open set `D` crossing the unit circle. Assume also that `phi_b` is transcendental over `C(z)`.

Then `u_0` and `phi_b` are algebraically independent over `C(z)`.

Proof sketch:

Assume a nonzero relation

`P(z,u_0(z),phi_b(z))=0`

near infinity.

If the relation has degree zero in `u_0`, it gives algebraicity of `phi_b` over `C(z)`, contradicting the transcendence hypothesis.

Otherwise take the minimal polynomial of `u_0` over the germ field `C(z,phi_b(z))`. In characteristic zero it is separable. On the continuation domain of the chosen `phi_b` branch, away from the discrete leading-coefficient and discriminant locus, the branch representing `u_0` continues analytically. Since `D` crosses the unit circle in an arc, one can choose a crossing point outside that discrete bad locus. This analytically continues `U_0(x)=u_0(1/x)` through its natural boundary, contradiction.

## Large-Parameter Green Crossing

Let `B=|b|` and set

`R_B=(1+sqrt(1+4B))/2`.

If `|z|>R_B`, then

`|f_b(z)| >= |z|^2-B > |z|`,

so `z` escapes to infinity.

If `B>2+sqrt(2)`, then `B-1>R_B`, hence

`Dbar(b,1)={w: |w-b|<=1}`

lies in the basin of infinity.

The Green function `G_b` is harmonic and nonconstant on `D(b,1)`. By the mean-value property, there is some `|eta|=1` with

`G_b(b+eta)>G_b(b)`.

Choose `zeta` with `zeta^2=eta`. Then

`|zeta|=1`

and

`G_b(zeta)=1/2 G_b(f_b(zeta))=1/2 G_b(b+eta)>1/2 G_b(b)=G_b(0)`.

Thus `zeta` lies in the standard outer Bottcher continuation domain for disconnected unicritical maps,

`Delta_b={z: G_b(z)>G_b(0)}`.

Since `Delta_b` is open, `Delta_b cap {|z|=1}` contains an arc near `zeta`; this arc lets the conditional lemma avoid the finite/discrete bad locus associated to any alleged algebraic relation.

## Parameter Split

1. Connected nonexceptional parameters `b in M \ {0,-2}`:
   likely also accessible by the same natural-boundary lemma because the Bottcher coordinate extends through the full basin of infinity when the filled Julia set is connected. This needs a separate proof that the basin crosses `|z|=1` in a usable arc.

2. Disconnected parameters with Green crossing:
   the conditional lemma applies whenever `exists |zeta|=1` with `G_b(zeta)>G_b(0)`.

3. Large parameters:
   the above estimate proves the Green crossing when `|b|>2+sqrt(2)`.

4. Remaining disconnected residue:
   parameters where the unit circle does not meet the outer Bottcher continuation domain are not addressed by this card.

## Source Boundary

Checked families that do not currently settle this exact target:

- Nguyen's local-conjugacy theorem covers `psi_f(u(t))` and explicitly leaves inverse Bottcher coordinates as a question.
- Medvedev--Scanlon product splitting kills a pure product-dynamics route, not the analytic continuation argument here.
- Xie treats products of Bottcher-coordinate values, not function-field relations between `u_0` and `phi_b`.
- Mahler/difference-Galois results cover linear Mahler systems; `phi_b` is tied to the shifted nonlinear map `z -> z^2+b`.

This source boundary is not a novelty proof. Promotion needs a targeted search for the exact natural-boundary/Bottcher mixed-pair lemma or a referee-level source audit.

## Theatre Status

Current status: `HOLD / proof candidate`.

Correctness risk: mostly source dependencies and exact Bottcher-domain statement.

Novelty risk: high enough to block promotion. The method is classical analytic continuation plus natural boundary. The result may still be new as an explicit mixed-pair theorem in the inverse-Bottcher obstruction, but that requires source audit.

Significance case if source-new: this resolves an explicit parameter region for the endogenous tangent leak `u_0` created by the failed `c1 -> 0` descent, and it gives a real theorem-shaped partial answer inside the inverse-Bottcher lane.

## Log

- 2026-06-23 - created after Wheeler/Turing natural-boundary proof attempts, Haiku continuation-domain correction, and Professor's large-parameter Green crossing estimate.

## Connected-Parameter Corollary Candidate

`[PROOF CANDIDATE]` If `b in M \ {0,-2}`, then `u_0(z)` and `phi_b(z)` are algebraically independent over `C(z)`.

Argument sketch:

For monic polynomials the filled Julia set has logarithmic capacity `1`. If `b in M`, the filled Julia set `K_b` is connected and full, and the Bottcher coordinate extends through the whole basin of infinity.

If the basin of infinity did not cross `|z|=1`, then the full unit circle would be contained in `K_b`. Since `K_b` is full, it would contain the closed unit disk. By monotonicity of logarithmic capacity and `cap(K_b)=cap(closed unit disk)=1`, equality would force `K_b` to be the closed unit disk, up to polar exceptional sets. Connected/fullness rules out such polar attachments. Hence `J_b` would be the unit circle.

But if `J_b` is the unit circle and `f_b(J_b)=J_b`, then `|z^2+b|=1` for all `|z|=1`, which forces `b=0`. Therefore for connected `K_b` with `b != 0`, the basin crosses the unit circle in an open arc. Excluding `b=-2` for the Chebyshev algebraic Bottcher coordinate, the conditional continuation lemma applies.

Dependencies before promotion:

1. cite a standard theorem that `cap(K_b)=1` for monic `z^2+b`;
2. cite or prove the strict capacity/equality step used above;
3. cite Bottcher extension through the full basin when `K_b` is connected;
4. source-audit whether this exact `u_0`/`phi_b` independence has already been recorded.

This would expand the theorem candidate to

`b in M \ {0,-2}` or `|b|>2+sqrt(2)`.

Status remains `HOLD / proof candidate`; the novelty gate is still open.

## 2026-06-23 supersession note

This backlog card is superseded for active work by

`docs/drafts/pipeline/1-in-progress/u0-phi-independence.md`.

Reason: a separate `2-fully-proven/u0-phi-independence.md` card was found to contain disconnected-case overclaims and mixed theorem/conjecture staging. That card has been demoted to `1-in-progress` and rewritten as the canonical active proof-under-audit record. Keep this backlog card only as provenance for the large-parameter estimate.

## 2026-06-23 supersession correction

The active state changed after reconciliation.

Canonical connected theorem:

`docs/drafts/pipeline/2-fully-proven/u0-phi-independence.md`

Canonical disconnected residue:

`docs/drafts/pipeline/1-in-progress/u0-phi-independence-disconnected.md`

The earlier note pointing to `docs/drafts/pipeline/1-in-progress/u0-phi-independence.md` is obsolete; that duplicate was removed after its audit content was folded into the connected/disconnected records.
