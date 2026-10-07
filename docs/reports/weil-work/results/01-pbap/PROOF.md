# Exact null repair and the scalarization question

## Proved bridge: positive correction at every integer

Write T(f) for the existing `logVector f`, A(f) for `weilArchRe (EF.weilTest f f)`, and

    w(j) = 2 (∫ narrowBump(j,t)² dt) / √j > 0.

The existing pair tests p(j,±) are smooth compactly supported functions and satisfy T(p(j,±)) = ±w(j)e_j. For a real number b define

    R_j(b) = (|b|/w(j)) [p(j,sign(b))],

choosing the positive sign at b=0. These are nonnegative finitely supported mixtures. Directly, T(R_j(b)) = b e_j. Let

    D(j) = max(|A(p(j,+))|, |A(p(j,−))|)/w(j).

Then |A(R_j(b))| ≤ |b| D(j). For finitely supported b put R(b)=Σ_j R_j(b_j). Its coefficients are nonnegative, T(R(b))=b, and

    |A(R(b))| ≤ Σ_j |b_j| D(j).

All sums here are finite, including the integer-indexed defect of every finite mixture. Consequently every nonnegative mixture c has the exact nonnegative repair

    c° = c + R(−T(c)),

with T(c°)=0 at **every** integer ≥2 and

    |A(c°)−A(c)| ≤ Σ_j |T(c)_j| D(j).

Proof: positivity follows termwise; linearity gives T(c°)=T(c)−T(c); linearity and the triangle inequality give the energy bound. No positivity theorem for A is assumed. The correction keeps the full pole terms through the literal A. Thus small weighted total defect, unlike a small unchecked prefix, gives a controlled exact repair.

This is an extraction of the atom-correction mechanism already used in `WeilPositivityPrimeBlindDuality.exists_weilPositiveUpTo_of_primeBlindPositive`. Verdict: **BRIDGE**, not a novel scientific result or PBAP proof.

## Conjecture under audit: no finite-mixture obstruction beyond scalar smooth tests

Proposed precise statement: full C² PBAP is equivalent to nonnegativity of the full functional on every compactly supported smooth complex scalar test whose symmetric autocorrelation vanishes at every integer logarithm.

Reason to investigate: the old L382 note allows a cone-versus-variety gap. On the real line, Boas–Kac–Krein factorization represents each compactly supported positive-definite correlation by one compactly supported L² factor. For a smooth correlation obtained from smooth tests, rapid decay of its nonnegative Fourier transform would make that factor smooth as well: |F|²=H and rapid decay of H imply integrability of t^k F for every k, hence smoothness by Fourier inversion. Equality of correlations preserves every null constraint and both polar evaluations.

### Paper argument for the smooth approximation step

For a fixed finite mixture c, convolve each of its finitely many tests with a nonnegative C∞ approximate identity supported in [−ε,ε], with ε≤1. All approximants have support in one fixed compact interval and converge in C². Their Fourier transforms converge pointwise and obey one common bound C min(1,|t|⁻²), obtained by integrating by parts twice. Thus their squared Fourier transforms times the gamma weight are dominated by an integrable multiple of min(1,|t|⁻⁴)log(2+|t|). Dominated convergence gives convergence of the archimedean energy. Compact support and uniform convergence give convergence of the two exponential pole moments and each logarithmic autocorrelation sample.

Only finitely many integer samples can be nonzero on the common support. Therefore the repair budget of the smoothed mixture tends to zero. Add the positive repair above; its pair tests are C∞, so the repaired mixtures are smooth, remain nonnegative mixtures, satisfy every null constraint exactly, and converge in full energy to c. This proves that positivity on smooth null mixtures implies positivity on C² null mixtures. The reverse inclusion is immediate.

### Paper argument for compression of a smooth mixture

Let Φ be the sum of the autocorrelations of its finitely many smooth tests, including their nonnegative coefficients. It is compactly supported, smooth and positive definite. Boas–Kac–Krein gives a compactly supported complex L² function g with Φ=g*ĝ, where ĝ(x)=conj(g(−x)). On the real Fourier axis, |F(g)|²=F(Φ). The latter is a nonnegative Schwartz function. Hence |t|^k F(g)(t) is integrable for every nonnegative integer k, so inverse Fourier differentiation gives a smooth representative of g. This representative remains compactly supported, since it agrees almost everywhere with the compactly supported L² factor. Equality of autocorrelations is pointwise by continuity. It preserves every symmetric logarithmic sample and the entire pole-plus-archimedean functional. Thus one scalar smooth null test has exactly the same energy as the smooth mixture.

The combined equivalence has a paper proof using the classical one-dimensional factorization theorem and standard smooth approximation/Fourier inversion. **Lean status:** only exact finite repair is being formalized. Factorization, approximation, and their full-functional bridges remain unformalized here. No Lean scalarization theorem is claimed.

Exhaustive text search subsequently located the single-function reduction already stated in the corpus at `krein-producer-loops.md:4968` (L248). Thus scalarization is **REDISCOVERED**, not a new conjecture beyond the corpus. The smooth exact-repair details above clarify regularity, but do not turn it into new scientific knowledge. The later L382 rank-gap remark must be read against this earlier factorization result. Next research must address the actual scalar energy sign, not rank reduction.

## Other conjecture audits

- Universal positivity from finitely many null nodes: excluded as a source of PBAP by existing sparse-producer obstruction and duality; do not repackage it as new research.
- Polar positivity implies full positivity for arbitrary weights: no closing theorem located. Conditional positivity leaves exponential homogeneous terms; fixing their coefficient is an unpaid issue. No implication is used here.
- Two-cluster Poisson estimate plus a total-mass window bound: existing L390 already identifies the lost frequency resolution. Do not claim the anti-concentration theorem alone closes that sector.

## Proved finite Gram realization

The dependency-closed paper proof is the section “Exact finite realization” in `TORUS-DENSITY.md`. For a PSD matrix A on labels 1..N, factor A as B*B and put conjugated rows of B on translated narrow bumps. Expanding autocorrelations gives matrix entries times shifted bump autocorrelations. At `log a - log b`, every unwanted argument is `log(a*k)-log(b*j)` for unequal positive integers with `b*j <= N*L`; the corpus log-gap bound exceeds the bump autocorrelation radius. Only `a*k=b*j` survives.

If the divisibility traces for integers 2..N vanish, this yields every positive integer null; indices above N have no surviving pair. Hermitian symmetry then yields the negative samples. Unit Finsupp weights on the realized family give the literal WP01 nonnegative mixture, including repeated tests, and the sample at zero gives `packetMass * trace(A)`. These conclusions are compiled in `WeilWorkPBAPGramPackets.lean`; they assume no sign theorem for the Weil energy. The broader measure-level density construction is a separate remaining obligation.

## Proved normalized representing-measure realization

The closed paper argument is in the section “Representing-measure connection” of `TORUS-DENSITY.md`. The corpus's `UnitAddTorus Nat.Primes` and `torusCharacter` supply the continuous integer monomials. For an origin-representing probability measure mu and coefficients d, the matrix is the actual integral Gram of `d_j chi_j`. Existing `complexFeatureGram_posSemidef` proves positivity because continuous products on the compact torus are integrable. Unique prime factorization identifies the character on every rational fibre; nontrivial divisible fibres vanish by the representing identities. The trace is `sum |d_j|^2`.

For a unit coefficient profile, apply the verified null-packet theorem and multiply its Finsupp weights by `packetMass(N,L+1)^{-1}`. Positivity of packet mass preserves nonnegative weights; linearity preserves every integer-null identity; the trace formula gives mass exactly one. Every rational sample is exactly `M_mu(a,b) * packetCoeffCorrelation(d,a,b)`. This full statement is compiled as `exists_normalized_representing_mixture` in `WeilWorkPBAPMomentPackets.lean`. It does not yet assert that the coefficient correlation converges to one or control the full Weil energy.
