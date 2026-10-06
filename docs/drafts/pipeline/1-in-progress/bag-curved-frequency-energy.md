# BAG curved-frequency energy from the full height integral

01ax. Route BAG. Exact physical-multiplier derivation and pending transfer:
P1 bag-physical-height-averaging-transfer. This is its central low-frequency
regularity estimate. No physical asymptotic or RH conclusion follows yet.
Corpus search86162 nonpartial66007files, coverage1248594/current1248595,
noerrors, refreshincomplete; all20candidate+20source statements inspected.
No exact prior energy theorem retrieved; mostly unrelated semantic hits.
Initial checkpoint below; exact strengthened strip theorem now Lean closed.
See P3 bag-curved-frequency-energy for final statement and audits.

Proposed exact theorem: for each 1<s<3/2 there is C_s such that, for every
N>=4 and u,v in[1,2], the integral over |a|,|b|<=N/4 of

 (1+|a|+|b|)^(2s) /
 [(1+|a|)^2*(1+|b|)^2*(1+|a*v+b*u+a*b/N|)^2]

is at most C_s. The constant is independent of N,u,v. This controls a
moving curved concentration set and supplies a Sobolev order strictly
above one; it is not an optimization of a numerical constant.

Paper derivation: put A=1+|a|, B=1+|b|, D=a*v+b*(u+a/N), C=1+|D|.
On the domain, U=u+a/N belongs[3/4,9/4]. Triangle inequalities give
A<=3(B+C), B<=3(A+C), C<=3(A+B). All three are at least1.
Partition by their smallest member, assigning ties arbitrarily.

If A is smallest, B<=6C and A+B<=2B. The integrand is bounded by
36*2^(2s)*A^-2*B^(2s-4).
If B is smallest, the symmetric bound is
36*2^(2s)*B^-2*A^(2s-4).
If C is smallest, A<=6B and B<=6A, while A+B<=7A. The bound is
36*7^(2s)*A^(2s-4)*C^-2.
Replace the three disjoint indicators by the sum of these nonnegative
majorants. The first two integrate over the whole plane as products of
one-variable integrable powers, since 2s-4<-1.

For the third, fix a in[-N/4,N/4]. The affine change b->a*v+U*b has
Jacobian 1/U<=4/3. Enlarge the b interval to the whole line. Its integral
is at most (4/3)*integral_R(1+|c|)^-2, independently of a,N,u,v.
The remaining a integral of (1+|a|)^(2s-4) is finite. Summing the three
finite constants proves the proposed scalar energy bound on paper.
No stationary replacement, oscillatory cancellation premise or numerical
evaluation enters this argument.

Formal obligations: exact rpow inequalities for the three cases;
measurability and integrability on the finite rectangle; affine substitution
for the nonnegative slice; Tonelli/product majorants; unconditional theorem
with structural domain parameters. Final Lean audit pending.

After this scalar theorem, still prove the ACTUAL normalized physical
profile Fourier identity, selected cutoff derivative budgets, high-frequency
tail, Minkowski/Plancherel assembly and positive-log-map tails. This lemma
alone is not the physical regularity theorem.

Proof-exposed strengthening01ax: the b cutoff is unnecessary. Only
|lambda*a|<=1/4 is needed for U=u+lambda*a in[3/4,9/4]. The same proof
works uniformly for ALL real lambda, including lambda=0 where the strip
is the full plane. New exact target integrates over this entire strip,
with D=a*v+b*u+lambda*a*b. This contains the original N-family with
lambda=1/N and its stationary limit. The paper cases/Jacobian above
remain unchanged. Scratch /tmp/bag-curved-frequency-energy-01ax.lean
starts the exact comparison and geometry lemmas; not audited yet.

01ax CLOSED: scratch47746,production4476,axiom91780,index18632 PASS; standard3.
Lint1720 sixunrelatedunreachable174warnings,noownederror. Range strengthened
to0<=s<3/2, entirestrip, allrealcurvatureincludingzero. SeeP2/P3.
