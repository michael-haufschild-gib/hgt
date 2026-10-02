# BAG fourth-grade square-root operator extrapolation

- **ID:** BAG-C28.33 / F326
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/bagchi-quantitative-sparse-recurrence.md, C28.11/C28.33
- **Statement:** The degree-two square-root/log operator scale does not extend to arbitrary fourth-grade coefficient families on the full integer block.

## Goal

Test the proposed higher-grade cancellation needed for the growing-degree BAG target weight. This rejects this particular operator estimate, not BAG or RH.

## Gates

- [x] Source-grounded conjecture: F306 degree-two matrix and F315 actual positive-grade physical kernel.
- [x] Complete paper counterexample and positive survivor.
- [x] Both formalized in `ChiDegreeFourCoherentPackets.lean`; direct leaf audit with `lake --old env lean` passed, without an umbrella build.
- [x] All eight public theorem axiom audits list only `propext`, `Classical.choice`, `Quot.sound`.

## Approach

For positive N and nonnegative H, let p,q,r,s be integers in [N,N+H] and let G=sqrt(sqrt(pq)*sqrt(rs)). For x,y in this box, sqrt(xy) stays in the box and

`0 <= x+y-2sqrt(xy) <= H²/(4N)`.

The upper bound follows from `(x+y-2sqrt(xy))*(x+y+2sqrt(xy))=(x-y)²`. Applying it to the two pairs and their geometric means gives `0<=p+q+r+s-4G<=H²/N`. Since the integer linear phase is exactly one, the full fourth-grade phase differs from one by at most `2*pi*H²/N`.

For arbitrary real C, choose a natural m>16|C|+4, take N=16m⁴ and S=[N,N+m²]. Its full fourfold phase packet has norm at least |S|⁴/2. Meanwhile `sqrt(N*(1+log(N+1)))<=8m³` and `16|C|m³<|S|²`. Thus

`C*sqrt(N*(1+log(N+1)))*|S|² < norm(full packet)`.

Here |S|² is exactly the product of the four all-one coefficient L² norms. The full packet has no removed quadruples. The logarithmic frequency identity `4log G=log p+log q+log r+log s` is also formalized.

## No-go closure

- **Exact killing theorem:** `RHTower.exists_chiDegreeFourRootPacket_exceeds_sqrt_log` gives a counterexample for every real constant C, within [N,2N].
- **Strongest positive survivor:** `RHTower.norm_chiDegreeFourRoot_packet_error_le` proves that every complete nonnegative separable fourfold packet differs from its product coefficient mass by at most the relative factor `2*pi*H²/N`. `chiDegreeFourRootPacket_norm_lower` supplies the half-mass consequence.
- **New insight:** There is a genuine coherent local mass at grade four. A useful higher-grade BAG estimate must account for this mass using the actual coefficient structure; it cannot blindly inherit the degree-two arbitrary-coefficient operator norm. Cancellation of the complete signed target form is still open.
- **Status:** Paper proof dependency-closed; exact positive survivor and counterexample both Lean verified. Direct final52855 exited0 warning-free; eight public axiom audits61265 standard-only. Wired and exact source-indexed. Lint59950 reports twelve unrelated unreachable modules, no BAG error; the global gate is not clean. Actual physical packet positivity, including the source cutoff and both remainders, is the separate C28.34 conjecture.

## Log

- 2026-10-02 — Scalar phase, weighted packet law, exact root frequency, and parameterized operator counterexample verified. Failed estimate closed with its formal positive survivor. BAG remains active.
