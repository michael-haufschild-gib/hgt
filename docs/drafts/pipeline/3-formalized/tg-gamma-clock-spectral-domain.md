# TG C9.18a: exact maximal spectral domain of the original Gamma cutoffs

- **Stage:** 3-formalized
- **Route:** TG, Gamma singular domain
- **Status:** production leaf final audit and all fourteen foundation queries pass; indexed and wired
- **Statement:** For every nontrivial countably generated cofinal cutoff family, its original finite Gamma multipliers converge strongly on f exactly when f belongs to the maximal domain of the full Gamma symbol; their limit is the maximal operator applied to f.

Write S(xi) for the exact C9.15 Gamma log-modulus symbol, and
S_(eps,R)(xi)=integral_[eps,R] 2(cos(xi*u)-1)gamma(u)/u du.
Because the literal integrand is nonpositive, S<=S_(eps,R)<=0.
Absolute scalar integrability gives convergence along every cofinal
pair of endpoints. Thus |S_(eps,R)-S|<=|S|. Define q=S_(eps,R)/S
where S is nonzero, and q=1 where S=0. The exact sign interval gives
0<=q<=1, q*S=S_(eps,R), and q tends pointwise to 1.

The original finite symbols are measurable and uniformly bounded in xi
for each fixed finite cutoff, by their finite density integral. They
therefore define actual bounded spectral multipliers. The full multiplier
M_S on D={f: S*f is L2} is densely defined and self-adjoint by the existing
maximal real L2 multiplication construction. For f in D, the original
finite action equals q_(eps,R)(M_S f). The corpus's bounded multiplier
convergence theorem gives strong convergence to M_S f. No spectral
growth envelope or assumed regularity core is needed.

Conversely suppose one cofinal family converges strongly to g. Select a
sequence tending to its nontrivial countably generated filter. L2
convergence gives convergence in measure and an almost-everywhere
convergent subsequence. Along that same subsequence the proved scalar
cutoff limit and literal bounded multiplier formulas force pointwise
limit S*f. Uniqueness gives g=S*f almost everywhere. Therefore S*f is
L2, f lies in the maximal domain, and M_S f=g. This proves necessity for
any cofinal family, not just one preferred exhaustion.

## Lean and scope

`formal/GaloisForLFunctions/RHTower/SoninGammaClockSpectralDomain.lean`
contains the literal symbols, exact sign/error laws, bounded quotient,
maximal self-adjoint multiplier, strong admission and full limit iff.
Its scratch proof had one remaining representation rewrite; this is
repaired through the exact almost-everywhere action theorem in the
production leaf. The required targeted `lake --old env lean` leaf audit exits 0 with empty
diagnostics. Fourteen public declarations; umbrella wired. All fourteen foundation
queries pass with only propext, Classical.choice and Quot.sound. Index
exits 0 and all fourteen names are verified. Global lint exits 1 on fourteen
unrelated unreachable leaves, with no finding in this module; diagnostics
in /tmp/tg-c918-lint.log. Closed 2026-10-04.

This is a spectral-domain closure. The next required step identifies
these original finite symbols with the literal physical strong Gamma
integrals under the actual Mellin unitary, retaining both parity blocks.
No physical carrier identity or RH conclusion is asserted here.
Arithmetic energy summability, source-to-Hardy passage and strict
sub-unit control remain open.
