# Alternating substitution: the odd-factor collision obstruction

- Stage: failed candidate; exact odd-sector positive survivor formalized.
- RH status: no zero-exclusion theorem and no qualifying new architecture.
- Candidate: turn an alternating zero into repeated arithmetic replacement, then control
  replacement coefficients by a square-sum bound in the strict half-strip.

## The proposed hard step

Write `eta(s)=sum_(n>=1) (-1)^(n-1)n^(-s)` in its convergent positive half-plane.
Let `b(1)=0`, and `b(n)=(-1)^n` for `n>=2`. Its ordered sum is `1-eta(s)`.
At a zeta zero in the open critical strip this sum is 1. Repeated replacement would
therefore need estimates on powers of the finite arithmetic sums which survive passage
to increasing cutoffs. A proposed estimate was a uniform exponential bound in the
replacement depth on the squared coefficient mass. Square summability of the first
coefficient vector does not give this estimate.

Products of finite sums are used below; no exchange of conditionally convergent infinite
sums is assumed. Their coefficients are grouped by the product of their integer labels.

## Direct paper obstruction

Fix `sigma>0`. For a finite collection of odd integers `m_j>=3`, put `w_j=m_j^(-sigma)`.
For a word `u` of length `k`, let `P(u)` be the product of its labels and `W(u)` the product
of its weights. Define the exact collision energy

    E_k = sum_(u,v with P(u)=P(v)) W(u) W(v).

This is the sum of squares of the coefficients of the corresponding positive Dirichlet
polynomial raised to the kth power. If there are `r` labels and `A=sum_j w_j`, then

    A^(2k)/(k+1)^r <= E_k <= A^(2k).

Proof: group words by the counts of their letters. There are at most `(k+1)^r` count
vectors. The sum of the masses of those groups is `A^k`. Cauchy--Schwarz gives the lower
bound for collisions within the groups. Equal count vectors imply equal integer products;
additional product collisions have nonnegative weight and only increase the energy.
The upper bound keeps every ordered pair of words. Unique factorization is not needed
for either bound. Consequently the kth root of `sqrt(E_k)` tends exactly to `A`.

In the literal signed coefficient powers, an odd output can only have odd factors.
Every nonzero contribution therefore has sign `(-1)^k`. Restricting its factors to the
chosen finite odd collection gives a lower bound for its squared coefficient mass.
The common complex phase of contributions with the same product does not change that
mass. Thus cancellation at a particular height cannot remove this lower bound.

Taking the collection `3,5,...,2r+1`, the masses `A` are unbounded for `sigma<=1`:
`(2j+3)^(-sigma)>=1/(2j+3)>=1/(3(j+1))`, and the harmonic series diverges.
For any proposed finite exponential bound `C^(2k)`, first choose `r` with `A>C`, then
let `k` grow. The exponential `(A/C)^(2k)` exceeds the polynomial `(k+1)^r`.
If `C=0`, already one nonzero coefficient contradicts the bound.

Conversely, for `sigma>1` the absolute coefficient sum is uniformly bounded over all
cutoffs. Multiplication of finite sums and the triangle inequality bound the squared
coefficient mass by the `2k`th power of that absolute sum. Hence the exact survivor is:

    A uniform exponential bound on these finite convolution powers exists iff sigma>1.

This is stronger than one failed contraction constant. In `1/2<sigma<=1`, each initial
coefficient vector has a uniform square-sum bound, while no finite exponential constant
controls all powers and all cutoffs.

## Scope and ancestry

The result rejects this particular coefficient-norm completion. It does not reject
conditional, height-sensitive estimates that retain the full sums, or prove they exist.
It does not establish any new relation forced by a zeta zero.

The coefficient space and multiplication problem belong to established Dirichlet-series
theory. The primary abstract of [Hedenmalm--Lindqvist--Seip
(1995/1997)](https://arxiv.org/abs/math/9512211) explicitly studies square-summable
Dirichlet coefficients, multipliers and dilated functions. That is exclusion/ancestry
evidence only: none of its theorems is used in the elementary paper argument above,
and this is not proposed as a permissible RH architecture. No scientific novelty is claimed.

## Exact formal survivor and verification

`formal/GaloisForLFunctions/RHTower/OddDirichletPowerGrowth.lean`, namespace
`RHTower.OddDirichletPowerGrowth`, contains 11 public theorems and eight definitions.

- `wordEnergy_eq_coefficient_squares` identifies the actual integer-product collision
  energy with the squared coefficient sum. `wordEnergy_lower` and `wordEnergy_upper`
  give the two bounds above for every finite alphabet of integer labels.
- `wordEnergy_exponential_bound_iff` identifies the exact admissible exponential bases
  at fixed cutoff: they are precisely `C>=A`.
- `oddEnergy_uniform_exponential_bound_iff` proves the sharp cutoff-and-depth boundary
  `sigma>1`. `oddWeight_square_summable_iff` proves the separate `sigma>1/2` threshold.
  `half_strip_power_failure` combines them throughout `1/2<sigma<=1`.
- The three `replacementCoefficient_oddLabel` / `replacement_word_*` theorems prove
  the literal signed-coefficient laws: odd-label words have sign `(-1)^k`, and every
  contribution to an odd output has that sign or is zero.

The formal growth capstone concerns the exact odd-source powers. The comparison with
the entire signed polynomial and its complex evaluation is the paper argument above;
no Lean theorem here concludes anything about a zeta zero.

Scratch and direct leaf checks with `lake env lean` passed. The final foreground command
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.OddDirichletPowerGrowth`
passed, newly building only this leaf (2338 jobs including cached dependencies).
All 19 public declarations were checked with `#print axioms` in a scratch file: only
`propext`, `Classical.choice`, and `Quot.sound` occur. The umbrella import, index refresh,
and global `scripts/formal_tools.py lint` passed. All owned Lean processes finished.
Scratch files and logs: `/tmp/hgt-odd-collision-EbZy6A`. No numerical experiment was run.

Current-source inputs inspected: `EulerDeletionFullEnergyFactorization` (full mixed terms
are flat before any zero assumption), `Sieve/DirichletPowerConvolution` (finite products,
product fibers and a collision-multiplicity upper bound). Research searches paired with
`rg`: `mixed arithmetic`, `substitution collision`, `arithmetic grammar`, `Dirichlet
convolution`, `convolution norm`; counts/caps are discovery, not exhaustive proof audits.
