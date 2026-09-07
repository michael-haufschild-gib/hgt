# EDQ dilation separation and power-law current growth

Stage: 3-formalized. [BRIDGE], derived from the exact prefix law and proved power-sum asymptotics. RH remains the primary objective.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Objective: remove harmonic-rate dependence from the current lower bound, thereby test whether a weaker subpower upper ceiling suffices.

## Frozen derived statements

For 0<Re(s)<1, write S_s(K)=sum_(k=1..K) k^(-s).
The corpus's remainder formula implies
S_s(K)*K^(s-1) -> 1/(1-s), hence norm(S_s(K))/K^(1-Re(s))
has a positive limit. Choose a fixed integer dilation D>=2 sufficiently
large that eventually norm(S_s(D*K))>=2*norm(S_s(K)).

For any complex scalar h, let u(K)=h*S_s(K)-1. The preceding inequality
forces norm(u(K))^2+norm(u(D*K))^2>=1/8. Indeed
1<=2*norm(u(K))+norm(u(D*K)); its square is at most eight times the
sum of their squares. This holds uniformly in h, including the literal
harmonic scalar H_N of the exact source prefix on K<=N.

Summing these pairs for K between a fixed threshold and floor(N/D),
each source coordinate is used at most twice. Thus the sum of squared
prefix norms through N is bounded below by c_s*N. For a=2*Re(s)-1 in
(0,1), each chronological weight increment through N is at least
a*(N+1)^(a-1). Consequently the actual initial Gram head is at least
C_s*N^a eventually. At a right-half zero the complete current dominates
this head; reflection gives the corresponding off-line absolute-current
floor. No decay estimate for H_N is used.

The formal constants can be chosen explicitly once D and the asymptotic
threshold are fixed: the prefix-square floor is N/(64*D), and the current
floor is (a/(128*D))*N^a eventually. Reflection gives the exponent
2*abs(Re(rho)-1/2) at every hypothetical off-line zero.

An independently proved cofinal subpower upper bound (for every positive
exponent, with constants and cutoffs allowed to depend on both exponent and
zero) therefore forces RH. Conversely RH makes every actual current zero.
This is an exact current criterion, with no shared subsequence or uniform
constant in the exponent required. The full primitive energy, squared raw
modular norm, and one-sided complete signed cross sum each have the same
sufficient subpower target, by the existing full-energy transfer and logarithmic
diagonal bound. No converse from RH to any input-energy/cross ceiling is claimed.
The bridge proves none of these source ceilings. The unconditional estimates
o(N/(log N)^q) remain compatible with every off-line floor exponent below one.

## Corpus audit and controls

EulerDeletionMobiusCurrentEscape provides the exact initial prefix and
actual-zero energy comparison. EulerDeletionMobiusLogGrowth currently
obtains superlogarithmic growth using harmonic decay. The stronger power
floor above follows from the nonconstant shape across dilations rather
than from smaller harmonic values. EulerDeletionPowerSumRemainder supplies
the unconditional asymptotic input. Corpus searches for sourcePrefix power,
kernel partial asymptotic, and harmonic cofinal/oscillation did not supply
this dilation argument. No external novelty is claimed.

This is a visible deduction, not a new universal conjecture. No numerical
experiment is justified. Finite-energy counterterm rigidity remains intact:
the scalar is never modified, and the two-point inequality holds for every
possible value it could already have.

## Lean and validation

`EulerDeletionDilationPowerGrowth.lean`, namespace
`RHTower.DeletionDilationGrowth`, contains sixteen public theorems and three
private helper proofs. Its normalized power-sum limit, fixed-dilation separation,
scalar-independent pair floor, injective summation bound, concave weight lower
bound, complete actual-zero current floor, reflection, exact subpower current
criterion, and three sufficient input criteria are all closed in Lean.

The full scratch passed `lake env lean` without diagnostics. Final targeted
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionDilationPowerGrowth`
built only the new leaf in 17 seconds; dependencies were cached. All sixteen
new public theorems were audited once with `#print axioms` in a temporary
`lake env lean` file and depend exactly on `propext`, `Classical.choice`, and
`Quot.sound`. The module is wired into `RHTower.lean`; no full or umbrella
build was run. No added axiom, admission, numerical certificate, or numerical
experiment was used.

Formal lint passed. The search index was refreshed once. Scoped source,
whitespace, unique umbrella import, all sixteen axiom records, documentation
links, and stage checks passed. All owned Lean processes exited. Temporary
proof, API, and axiom sources were removed; logs remain under
`/tmp/edq_dilation.*.log`.
