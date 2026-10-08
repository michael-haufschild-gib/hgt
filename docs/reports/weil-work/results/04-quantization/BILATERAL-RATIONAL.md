# Bilateral rational phases: the negative harmonic mass boundary

Cycle 18. Status: L2h PROVED IN LEAN; both final direct leaf audits passed cleanly.
Cycle 20 supersedes its signed-case limitation: full signed L2 is now proved in
PERIODIC-RESIDUES.md and WeilWorkQuantizationBilateralRigidity.lean. WP04 remains
open. The seven cycle-18 declarations and dependencies use only propext,
Classical.choice and Quot.sound; output in bilateral-rational-lean-audit.txt.

## Exact conjecture and verdict

Let hW be any full-positive source, C its actual residual cumulative measure,
and R the conjunction of λ=Λ on n≥2 and RH. For coprime integers u>v>1, suppose

    exp(2πi C(x)) = Σ[k∈ℤ] p_k exp(2ik log(u/v)x), x>0,
    Σ[k∈ℤ] |p_k| (u/v)^|k| < ∞.

**L2h:** either R holds, or Σ[n≥1] max(−λ(n),0)/n diverges.
In particular every nonnegative source with this representation is rigid.
The final unconditional alternative quantifies over all representations inside
its conclusion; neither the representation nor a sign condition is asserted
to follow from hW. Verdict: SURVIVES PRELIMINARY ATTACK, with the following
dependency-closed paper proof. Independent novelty beyond the corpus is provisional.

## Proof

1. Put a=dirichletExp(lamLog λ), so a(1)=1. The already verified actual-source
   phase coupling theorem gives B(1)≠0 and B(m)=B(1) for every integer m≥1,
   where B(m) sums every resonant coefficient p_k (u/v)^(k/2) a(m(v/u)^k).
   No noninteger reflected residue is used.

2. If u does not divide m and v does not divide m, only k=0 resonates.
   Indeed k>0 requires u^k|m by coprimality, and k<0 requires v^(−k)|m.
   Both imply the excluded divisibility. Therefore B(m)=p_0 a(m).
   Apply this at m=1 to get B(1)=p_0≠0, hence a(m)=1 at every such m.

3. In particular a(q)=1 for every prime q>u: a divisor u of a prime q
   would be 1 or q, and similarly for v. The source coefficient convolution
   at a prime gives λ(q)=log(q)a(q)=Λ(q). Thus all prime deviations above u
   vanish. This conclusion retains arbitrary singular finite Toeplitz blocks;
   their invertibility is unnecessary.

4. Suppose Σ max(−λ(n),0)/n converges. Outside the finite set n≤u, split
   integers into primes and non-primes. On primes the deficit (Λ−λ)^+ is zero.
   On non-primes,

       (Λ(n)−λ(n))^+ / n ≤ Λ(n)/n + (−λ(n))^+/n.

   The first series over non-primes converges by the existing proper-prime-power
   theorem `WeilPrimeDeficit.summable_nonprime_vonMangoldt_div`; the second
   converges by assumption. The finite head has no effect. Thus the complete
   harmonic deficit is summable. The existing endpoint receiver
   `WeilOneSided.eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div`
   gives λ=Λ on n≥2. Functional congruence and the verified Weil criterion give RH.
   Contraposition proves L2h. For nonnegative λ on n≥2, its negative harmonic
   mass has only a finite head and is summable, giving the stated special case.

## Attacks and limits

This section records the cycle-18 boundary. Cycle 20 closes the signed L2
obligation using real-height translation, without proving P18 or D19.

The one-sided Blaschke warning model from cycle 17 has nonnegative weights and
finite negative harmonic mass, but is not full-positive; L2h excludes it too.
No numerical computation is used. Full positivity is positivity of a quadratic
functional, not coefficientwise nonnegativity. Consequently step 4 cannot be
silently applied to every hW. Ordinary signed convergence of Σ(λ−Λ)/n does not
give convergence of its sign parts or of max(−λ,0)/n.

The proposed proof via invertibility of every finite arithmetic Toeplitz block
is not established. Infinite Hardy-space kernel results do not pay that premise.
No counterexample to the actual L2 statement was proved. At cycle 18 the
surviving obligation was to exclude infinite negative harmonic mass under the
actual represented phase, or use a different source constraint. The cycle-20
period-one residue law supplies that different constraint.

## Formal realization

1. `WeilWorkQuantizationBilateralRough.lean`: exact zero-frequency isolation on
   the rough divisibility set, actual coefficient and prime agreement.
2. `WeilWorkQuantizationNegativeMass.lean`: finite-prime-agreement plus negative
   harmonic mass receiver, L2h, nonnegative corollary and source-only alternative.
3. Both leaves passed `lake --old env lean -o ... <leaf>` and are wired into
   RHTower.lean. No full or umbrella build. The formal weighted moment is written
   as Σ|p_k| exp(|2k log(u/v)|/2), equal to the displayed moment since u/v>1.
