# BAG envelope for the complete original growing Mellin source

- **Stage:** 3-formalized

01av. Dependency-closed paper proof; both source factor bound and axes envelope
now Lean audited. P3 bag-uniform-complete-source-envelope.
Route BAG. The target is domination of the full source needed to integrate
the now-proved signed mixed profile. Constants are not optimized.

Fix rho1,rho2>0. Write L=logN, alpha=rho1/L+i*t1, beta=rho2/L+i*t2,
Z_N=criticalCompletedConeEuler P_N (1+alpha) (1+beta), P_N=primes<=N.
There is C>0 such that, eventually in N, simultaneously for all real t1,t2,

 |Z_N| <= C*(1+|t1|+|t2|)^54 *
   [L^2/(1+(L*t1)^2)+L^2/(1+(L*t2)^2)].

The ORIGINAL source includes both coprime cofactors, both label exclusions,
the allowed first/second collision and every signed valuation sector.
No local unlabelled nonvanishing is assumed.

## Exact local replacements

For each prime put z=1/p, a=p^-alpha,b=p^-beta. Take N large enough that
|Re alpha|,|Re beta|<=1/16. The cofactor-completed unlabelled local factor is

 H_p=(1-za)*(1-zb)*weightedEuler z (za)(zb)=C_p*R_p,
 R_p=((1-z*b/a)*(1-z*a/b))/((1-z/a)*(1-z/b)),
 C_p=cubicPrimeFactor p 1 alpha beta.

This is the current mixed-base exact factorization. Each of the four nomes
in R_p has modulus<=3/4, so its complement lies between1/4 and2 in norm.
Consequently 1<=64*|R_p|; R_p never vanishes in this domain.
The corpus cubic majorant gives |C_p|<=1+b_p,
b_p=cubicMajorant*p^(-3/2), sum b_p<infinity.

For a permitted label triple (p,q,r), r differs from p and q. At an unmarked
prime the completed factor is H_p. At a marked prime it is exactly one of
the FOUR numerator functions from the current mixed-label proof:
firstNumerator(z,a,b), firstNumerator(z,b,a), thirdNumerator(z,a,b),
pairNumerator(z,a,b). The last is used when the first two labels coincide.
The identities are weightedFirst/Third/Pair_normalized_deformation, together
with symmetry of weightedConeEulerMinusOne. These numerators divide only
by products of a,b,1-z; they NEVER divide by H_p or responseBase.

Choose A>=max(rho1,rho2). For p<=N, both a,b lie in the compact annulus
exp(-A)<=|w|<=exp(A), and z lies in[0,1/2]. Every numerator is continuous
on this compact set, with its displayed denominators nonzero. Thus all
four norms have a common bound K0>=1. Put K=64*K0. At every prime the exact
completed label factor is bounded by

 |R_p|*(1+b_p)*K^[p is first label]*K^[p is second label]*K^[p is third label].

For an unmarked prime this is the cubic majorant. For a marked prime it
follows from K0<=K*|R_p|, from1+b_p>=1, and from the fact that at least one
of the three indicator exponents is1. A first/second collision uses two
factors K and is therefore also covered, without replacing its numerator.
Multiplying the three indicators costs exactly K^3. Moreover,
product_(p in P_N)(1+b_p)<=exp(sum_all_primes b_p), independently of N.

## Full original label sum and cofactors

Write Q_N(delta)=product_(p<=N)(1-p^(-1-delta)). The exact product of R_p is

 J_N=Q_N(beta-alpha)*Q_N(alpha-beta)/(Q_N(-alpha)*Q_N(-beta)).

Both original cofactor identities attach zeta(1+alpha)*zeta(1+beta) and
supply precisely the local complements already included above. They apply
because rho_i>0 implies both arguments differ from1. The prefactor for
label triple(p,q,r) is M_N^3*w_p*w_q*w_r, where
M_N=criticalPrimeNormalization P_N and w_p=logp/p>=0.
Triangle inequality for the EXACT masked sum now yields

 |Z_N| <= K^3*exp(sum b_p)*M_N^3*(sum_(p<=N)w_p)^3 *
            |zeta(1+alpha)*zeta(1+beta)*J_N|.

No signed term is removed from the source identity. The displayed
inequality enlarges the nonnegative norm sum to all triples only.
M_N*L converges to exp(-gamma) by the audited corpus theorem, and
sum w_p<=L+log4 by MertensFirst. Hence the first four real factors are
bounded uniformly in N. This proves an actual full-source factor bound
without any response denominator nonvanishing requirement.

## Pole geometry and global envelope

Let epsilon=1/L, D(t)=|epsilon+i*t| and T=1+|t1|+|t2|.
The audited U2 comparison applies simultaneously to the four shifts
rho2-rho1,rho1-rho2,-rho1,-rho2. Its upper estimates for the two numerators
and lower estimates for the two denominators give

 |J_N| <= C1*T^36*D(t1-t2)^2/(D(t1)*D(t2)).

The current global residue-factor bounds, at real parts1+rho_i/L in[1,2],
give |zeta(1+rho_i/L+i*ti)|<=M*(1+|ti|)^9/|rho_i/L+i*ti|.
For fixed positive rho, |rho/L+i*t|>=min(rho,1)*D(t). Therefore

 |Z_N| <= C2*T^54*D(t1-t2)^2/(D(t1)^2*D(t2)^2).

The exact Euclidean norm identity gives
D(t1-t2)^2<=2*(D(t1)^2+D(t2)^2). Finally
1/D(t)^2=L^2/(1+(L*t)^2), proving the stated envelope.
All constants depend only on fixed rho1,rho2 and unconditional corpus data.
No growing-frequency zeta asymptotic, RH, numerical evaluation or physical
regularity is assumed.

## Scope and next obligations

This envelope controls actual growing arithmetic source, including zeros
of local unlabelled factors. Lean proves the equivalent stronger-shaped
profile L²/(1+L*|t|)², with a different unspecified constant, using
poleSize=1/L+|t| and the triangle inequality. Since (1+x)²<=2*(1+x²)
for x>=0, the two profiles are equivalent for this statement.
The polynomial frequency weight remains; decay of the test is required.
Together with M1 and the zero signed integral of G, it should imply
(1/L)*integral Z_N*Psi->0 for each FIXED Schwartz test. The sector split,
joint-box removal, symmetry and dominated convergence need exact proofs.
The actual normalized physical test depends on N and has shrinking cutoff
edges; transfer to it and control of its complete frequency tails remain
hard open problems. No physical norm saving or RH conclusion is asserted.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanUniformSourceEnvelope` | `criticalCompletedConeEuler_uniform_axes_bound` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
