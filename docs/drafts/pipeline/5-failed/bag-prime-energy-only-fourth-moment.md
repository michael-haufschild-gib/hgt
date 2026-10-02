# BAG prime energy-only physical fourth moment

- **ID:** BAG-C28.38 / F329
- **Stage:** 5-failed
- **Type:** FALSIFIED ESTIMATE
- **Source:** ../1-in-progress/bagchi-quantitative-sparse-recurrence.md, C28.37/C28.38
- **Statement:** Unit coefficient energy and vanishing maximum coefficient do not give a uniform physical fourth-moment bound for prime-supported polynomials at comparable height.

## Scope

This rejects a generic estimate proposed as a possible ingredient for BAG. It does not reject BAG, RH, or C28.37's particular full-window Gaussian cofactor family.

## Dependency-closed paper proof

For all sufficiently large natural m, the source dyadic prime-window PNT gives at least 64m^7 primes in (64m^8,128m^8]. Indeed, its lower bound is 32m^8/log(128m^8), and log(128m^8)<=m/2 eventually. Partition this interval into 64m^4 consecutive integer cells of width m^4. Finite pigeonhole produces a prime set S of cardinality M>=m^3 in [N,N+m^4], with 64m^8<=N<=128m^8. No short-interval prime lower bound is assumed.

Set H=m^4 and T=(4*pi/3)N. Then H<=N/6 and 2*pi*H²/N<=1/4. The entire F327 physical chi-four kernel, including both source remainders and every quadruple, gives

`Re integral_[T,2T] W(t/T)*chi(linePt t)^4*P_S(t)^4 <= -(pi*sqrtN/8)*M^4`,

where `P_S(t)=sum_{p in S} exp(i*t*log p)`. Since sqrtN<=12m^4 and M>=m^3, the right side is at most `-T*(m²/128)*M²`. The unit norm of chi and the norm-integral inequality give the same positive lower bound for `integral W*norm(P_S)^4`.

Normalize `Q_S=P_S/sqrtM`. Its quadratic coefficient energy is exactly one; each coefficient has norm at most 1/m. On the identical prime set and height,

`Re integral W*chi^4*Q_S^4 <= -T*m²/128`,

`integral W*norm(Q_S)^4 >= T*m²/128`.

The unbounded factor m²/128 contradicts every eventual uniform constant, even when that constant is required only on these flat, unit-energy packets. Heights tend to infinity because N>=64m^8. This is an exact symbolic construction; no numerical experiment is used.

## No-go closure and positive survivor

- **Killing theorem:** `RHTower.no_uniform_flat_prime_packet_fourth_moment_bound`.
- **Strongest positive survivor:** `RHTower.eventually_exists_flat_prime_packet_fourth_moment_large` supplies actual primes, the coherent cell, exact unit energy, coefficient flatness, negative signed chi-four mass, and positive fourth-moment growth together. `eventually_exists_dense_prime_packet` supplies the unconditional arithmetic family independently.
- **New constraint:** A useful BAG moment theorem must use more than primality, energy and individual flatness. It must exploit the actual source coefficient/cofactor structure and control coherent local mass together with all inter-packet signed terms. Small separate coefficients do not imply a Gaussian physical law.
- **Applicability limit:** `CompactGaussianPrimePacketCapacity` bounds the actual normalized target-channel mass in a square-root-scale packet by O(1/log N). The artificial unit-energy normalization above does not produce a fixed target in those channels.
- **Lean status:** `ChiPrimePacketFourthMoment.lean` direct final43285 passed without warnings using `lake --old env lean`, wired into `RHTower.lean` without an umbrella build. All five public theorem and both definition axiom audits64654 passed using only `propext`, `Classical.choice`, `Quot.sound`. Exact source index finds the killing theorem. Lint54118 reports thirteen unrelated unreachable leaves, no BAG debt; global lint is not clean.

## Log

- 2026-10-02 — Source PNT, finite pigeonhole, full signed physical kernel and normalization assembled. Direct leaf and all public axiom audits passed. Failed estimate and positive survivor are closed together; BAG remains active.
