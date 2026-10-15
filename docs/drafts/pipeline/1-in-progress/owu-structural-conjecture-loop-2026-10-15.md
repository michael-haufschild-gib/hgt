# OWU structural conjecture loop

Status: in progress. Objective: one unconditional structural contribution overcoming an OWU obstacle; no new bound, RH receiver, or unproved producer premise.

## Source discipline

Use current Lean sources and corpus search. No external search, numerical experiments, or old research notes. The requested frontier entry identifies odd-only arbitrary-weight uniqueness as open. Read its cited Lean modules before trusting the summary.

## Plan

1. Identify exact odd-cone obstruction and reusable structures across the corpus.
2. State competing falsifiable structural conjectures; attack, prove, or record failure and successor.
3. Finish a dependency-closed mathematical proof before adding Lean.
4. Audit new modules individually in foreground, wire umbrella imports, run lint, inspect axioms, clean owned scratch files.

## Established source facts

- `OddSectorRiemannKernelRigidity`: vanishing of atom pairings on Riemann-kernel convolutions with even mean-zero tests determines every weight; no constant transform escapes detection.
- `WeilOddConeMinorantRigidity`: an odd-positive minorant of von Mangoldt equals von Mangoldt.
- `OddSectorAnyPoleWeightJointRigidity`: adding even pole-free positivity closes arbitrary-weight uniqueness. That even condition cannot be assumed here.
- `WeilOddBlindPoleWeightWindow`: odd Farkas is already proved, so another separation/receiver theorem does not meet the objective.

## Conjecture ledger

1. **Unrestricted parity transfer by translating odd tests — rejected.** The current odd cosine-shift measure lives on `rho`, with `z^2 = rho^2 - 2`. Its spectral square is `z^2 A A#`. Dividing by `z^2` to recover even positivity changes sign on the imaginary segment. This is a structural sign obstruction, not a missing decay estimate. Source: `OddSectorPoleFreeResonatorPositivity`, especially `specSq_oddLift` and the final resonator theorem.
2. **Reuse the full twisted-arc blind certificate unchanged — rejected.** The existing even null argument integrates a positive lift against an even representing measure. In the odd representation the same expression acquires `1/z^2`; positive real and imaginary contributions can balance. No vanishing follows.
3. **Replace each shifted-Gamma test by an odd test preserving its spectral modulus — false.** At frequency zero an odd transform vanishes, whereas `XiC(0) * shiftedGammaPoly j 0` is nonzero. Every nonzero nonnegative diagonal mixture retains that constant mode. This does not refute correlated, off-diagonal combinations or a different null construction.
4. **Next conjecture:** a correlated Gamma covariance can annihilate the constant mode while retaining prime blindness and the Xi factor. First open core: construct the covariance with the required two constraints; neither may be assumed as a new producer premise.

## Search limitations

The first acronym search found no OWU declarations. Deep natural-language searches returned partial results and weak semantic matches; exact lexical queries and source reads recovered the actual odd spectral machinery. The indexed corpus includes stale/uncompiled entries, so source discovery is not a Lean audit. Serena symbol lookup rejects Lean paths as ignored; use exact `rg` discovery and source reads for Lean.

## Audit

No new mathematical result or completion claim yet.

## Further attacks

5. Boundary twisted-arc parameter `a = 1/4`: its Mellin factor is
   `r² (1/4+r²)`, but its nonzero mass introduces a pole in the divisor
   transfer. A further twist would give `r²(1/4+r²)²` and remove that
   defect. Positive annihilation for these third-order arc moments remains
   unproved. The existing minimum principle does not establish it.
6. Endpoint saturation `β = 1`: the two existing asymptotic inequalities
   pin the leading Dirichlet residue, but do not supply a small-energy
   vector with nontrivial fixed mixed pairings. No rigidity conclusion.

## Current candidate: automatic squared-variable Pick continuation

This is an automatic consequence to prove from the actual odd cone, not an
extra producer assumption. Intended structural output: the arithmetic Weil
function of every odd-positive source continues holomorphically to
`Re s > 1/2, Im s > 0` and its reflected lower quadrant. Thus any obstruction
inside the right critical half-plane is confined to the real segment. This
does not assert weight uniqueness or remove the remaining real segment.

### Paper argument to audit and formalize

Write `F(a) = weilFunction lam (1/2+a)` for `Re a > 1/2`.
For such `a`, set `h_a(x) = sign(x) exp(-a |x|)`. Smooth compact odd
approximations are obtained by reflecting and subtracting the corpus's
`WeilHerglotz.testFn a j`. For any finite complex linear combination:

* Fourier transforms converge to `2 i r/(a²+r²)`; the existing one-sided
  exponential bounds give an integrable `O(log(2+|r|)/(1+r²))` archimedean
  majorant.
* Polar transforms converge since `Re a > 1/2`.
* Correlations converge pointwise and are bounded by
  `C(1+|x|) exp(-b|x|)` for a fixed `b > 1/2`. Odd-cone absolute Dirichlet
  convergence, with a smaller exponent, dominates all arithmetic terms.

Odd positivity therefore passes to these finite sums. For the complex
linear spectral functional `L` and `Re a > 1/2`, direct pole evaluation,
the Cauchy Fourier identity, and holomorphic continuation of the real
Poisson–digamma identity give

`L(1/(a²+r²)) = F(a)/a`.

Partial fractions give the proposed exact Gram identity

`Q(h_a,h_b)/4 = (a F(a) - conj(b F(b)))/(a²-conj(b)²)`.

Use indices `Re a > 1/2, Im a > 0`; the denominator cannot vanish. This
Gram kernel is positive semidefinite. Set
`q(a) = -i a²` and `H(a) = -i a F(a)`. Then `Re q(a)>0`, and this same
kernel is `(H(a)+conj H(b))/(q(a)+conj q(b))`. The corpus theorem
`HTGeometry.exists_caratheodory_interpolant` supplies a holomorphic `G`
with nonnegative real part on the full right half-plane, interpolating
these data. Define

`F_cont(a) = i G(-i a²)/a` for `Re a>0, Im a>0`.

This is holomorphic, agrees with the actual source on `Re a>1/2`, and
satisfies `Im(a F_cont(a)) >= 0`. Complex reflection gives the lower
quadrant. The exact Gram identity and convergence steps remain to be
checked in Lean; no completed contribution is claimed yet.

### Toolchain check

`lake --old env lean /tmp/owu_probe.lean` passed with imports of the odd
strip-positivity module, the actual one-sided exponential approximation
module, and Carathéodory–Nevanlinna–Pick. This only verifies existing API
availability, not the candidate theorem.
