# The counted parity tower determines the full finite resolvent

- **ID:** ACP-PARITY-RESOLVENT-LIMIT
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Parent:** arithmetic-counting-small-prime-secular-gap.md
- **Sources:** arithmetic-counting-parity-spectral-mass.md; arithmetic-counting-parity-secular-data.md; arithmetic-counting-finite-secular-criterion.md in stage three
- **Statement:** For each prime p and each 0<s<2 log 2, the actual finite prime-matrix reciprocal reading of the unit parity constraint converges to its full arithmetic tower series.

## Actual scalar reading

Let e_(i,N) be an orthonormal eigenbasis of the literal full prime matrix,
let E_(i,N)=log N-lambda_(i,N)-gamma, and let
a_(i,N)=<v_(p,N),e_(i,N)>. Define

`R_(p,N)(s)=sum_i a_(i,N)^2/(E_(i,N)-s)`.

The claimed limit, along every positive integer horizon, is

`F_p(s)=sum_(k>=0) a_k^2/(D_k-s)`,

where a_k and D_k are the proved parity tower data. This is the existing
head-plus-tail `infiniteSecular` expression. The restriction on s keeps it
strictly between the ground and the first global excitation. It also lies
below every positive parity-tower energy.

## Closed proof

The Möbius transform of an arithmetic function at p^(k+1) is its difference
between p^(k+1) and p^k. Applied to parity, this is
`(-1)^(k+1)-(-1)^k=2(-1)^(k+1)`. The existing parity coordinate theorem
therefore identifies the squared coordinate at every conductor p^k with
a_k^2 in the limit. Choose an actual index i_k(N) in its isolated window,
using any index before the window exists. At horizons N+1 there is always
an index available. Window simplicity and energy convergence give

`E_(i_k(N),N+1)->D_k`, `a_(i_k(N),N+1)^2->a_k^2`.

The D_k are strictly increasing: above the ground their increments are
log p>0. Consequently the selected indices in any fixed finite initial
segment are distinct eventually.

Put g_0=2 log 2 and eta=(g_0-s)/2>0. The arithmetic adjunction sublevel
below gamma+s+eta consists exactly of conductor one, by the first-excitation
bound. Its threshold is not an arithmetic energy. The proved bounded
spectral count therefore gives exactly one actual line in that sublevel
eventually. The selected ground line lies in it, so every other index
satisfies `E_(i,N+1)-s>=eta`.

For the packet S_(K,N)={i_0(N),...,i_K(N)}, write L_(K,N) for its
reciprocal sum and M_(K,N) for its squared coordinate mass. Parseval gives
total squared mass one. Every omitted denominator is positive and at
least eta, hence the proved finite tail estimate gives, eventually in N,

`L_(K,N) <= R_(p,N+1)(s) <= L_(K,N)+(1-M_(K,N))/eta`.

For fixed K, each denominator has nonzero limit, so the finite sums
converge to the first K+1 tower terms and their squared mass. The full
tower squared mass is one. Its positive reciprocal tail is dominated by
`a_k^2/(g_0-s)`, so the reciprocal series is summable. Therefore, as K
grows, the lower packet limit tends to F_p(s), and its upper counterpart
tends to the same value. The proved eventual packet-limit principle now
gives the asserted full resolvent convergence.

This proof controls all unselected actual eigenlines, including any whose
energies escape to infinity. No independent coordinate formula at other
conductors, common horizon over all conductors, limiting operator, or
uncontrolled interchange of limits is needed.

## Scope and audit

Inputs are the actual bounded spectral count, first-excitation inequality,
counted parity eigenline coordinates, unit tower mass, and elementary finite
reciprocal bounds. The Möbius difference formula already exists in
`TransHorizonIncidenceMechanics`; its source statement was inspected and is
reused. All denominator separation and packet injectivity are proved from
these concrete arithmetic inputs, not assumed in the endpoint.

The six-endpoint formalization is installed in
`TheParityTowerDeterminesTheFiniteResolvent.lean`. Its public endpoints are
`primeParityTowerCoefficient_eq_moebius`, `exists_primeParity_tower_eigenline`,
`eventually_fullPrime_ground_count_one`, `primeParityTowerEnergy_strictMono`,
`primeParityTowerEnergy_ge_excitation`, and `tendsto_primeParityFiniteResolvent`.
Scratch check 99113 and canonical check 10211 exited zero without warnings.
All transitive axiom audits use only `propext`, `Classical.choice`, `Quot.sound`.
The adjacent audit preserves exact commands, source hash and actual output.
The umbrella and README are wired; scratch and check logs are cleaned.
The final greatest-gap identification remains on the parent card.

- [x] Closed concrete proof with controlled omitted spectral mass.
- [x] Lean proof and transitive axiom audit.
- [x] Canonical source audit, wiring, durable evidence and cleanup.
