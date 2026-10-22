# TG: closed arithmetic selection on the unchanged ground carrier

Status: IN PROGRESS. Parent objective remains unconditional Lean RH by TG.
This is a structural conjecture/attack cycle, not a substitute completion goal.

## Conjectures

C2: for every binary arithmetic mask, the literal finite-source selection graph
on the original Sonin ground grid has a single-valued closed graph closure.
Its closed extension is idempotent and its domain is dense in the original
closed grid span. No renorming, coefficient-space substitution, or extra
analytic hypothesis is allowed.

Generalization used in Lean: graph closure is single-valued for EVERY scalar
weight w:N→C, without a boundedness hypothesis. Only the idempotence clause
requires w_n^2=w_n. The proof below uses the same continuous coefficient
constraints for this generalization.

C3: use that closed selection to supply the original prime-polar source's
missing arithmetic cancellation. This is the load-bearing intended use;
closedness alone does not prove it.

Corpus audit: SoninGroundGridArithmeticSelection proves bounded selection iff
eventually constant mask, with explicit continuous coefficient duals. The prime
and prime-power masks have no bounded full-physical-space extension. A targeted
deep search was partial (coverage pending); exhaustive source search found no
other module using these ground-grid definitions except the umbrella. C2 has
not been found already formalized. General closed graph theory is a parent
theory: classify C2 as a BRIDGE, not a scientific breakthrough.

## Dependency-closed paper proof of C2

Let B_n = groundEntry(a, log(n+2)), a>0; H is closed span of all B_n.
The source-proved covariance is <B_i,B_j>=2a/max(i+2,j+2).
Let D_n=B_n-B_(n+1), w_n=2a/((n+2)(n+3)), q_n=D_n/w_n.
The existing coefficient duals satisfy d_0=q_0, d_(n+1)=q_(n+1)-q_n
and <d_n,B_j>=delta_(n,j).

These duals separate H. Indeed, if <d_n,f>=0 for every n, induction gives
<q_n,f>=0, hence <B_n,f>=<B_(n+1),f>. Since ||B_n||^2=2a/(n+2)
tends to zero, all these pairings vanish. Continuity then makes f orthogonal
to H. For f in H this forces ||f||^2=0.

For mask m_n in {0,1}, let Gamma be closure of span of (B_n,m_n B_n).
Every (x,y) in Gamma has x,y in H. For fixed n the continuous linear functional
(x,y) -> <d_n,y>-m_n<d_n,x> vanishes on every generator, hence on Gamma.
For x=0 dual separation forces y=0. Thus Gamma is the graph of a partially
defined linear operator, and is closed by construction. Its domain contains
span{B_n}, is contained in H, and therefore has closure H.

The continuous linear map J(x,y)=(y,y) sends each generator into its original
span because m_n^2=m_n. Hence it preserves Gamma. This proves the closed
operator is idempotent, including invariance of its domain under its output.
Gamma is minimal among closed linear graphs containing the original pairs.

## Attack on C3, before implementation

Closedness does not bound operator values and does not grant domain membership.
The desired source has coefficients c_n=primeIndicator(n+2)-polarCellMass(n).
Selection would leave prime coefficients 1-polarCellMass(n), eventually
positive and bounded below, and zero composite coefficients.

Dependency-closed paper proof of the domain obstruction:

1. Put x=n+2. On [log x,log(x+1)] the polar integrand is nonnegative and at
   most (x+2)/log x. The interval length is log(1+1/x)≤1/x. Therefore
   0≤polarCellMass(n)≤(1+2/x)/log x≤2/log x→0.
2. Suppose (f,g) belongs to the prime-selector graph and f has EXACT original
   coefficients c_n=primeIndicator(n+2)-polarCellMass(n). The graph coefficient
   identity forces g's coefficients to be primeIndicator(n+2)*c_n.
3. Remove finitely many initial coefficients from g, producing g'. Its
   coefficients b_n are all nonnegative and ≥1/2 at every sufficiently large
   prime n+2. No assumption about convergence of raw coefficient truncations
   is made here: subtraction is finite and coefficient duals are continuous.
4. Let A_n=sum_{k≤n}b_k. Telescoping the duals gives <q_n,g'>=A_n. Orthogonality
   of D_n and ||D_n||²=w_n gives Bessel's inequality
   sum_n w_n*A_n²≤||g'||², since <D_n,g'>=w_n*A_n.
5. Positivity gives A_n²≥sum_{k≤n}b_k². Nonnegative Tonelli and the exact
   telescoping sum sum_{n≥k}w_n=2a/(k+2) then imply
   2a*sum_k b_k²/(k+2)≤||g'||². But the sufficiently large prime terms dominate
   (a/2)*sum_p 1/p, which diverges. Contradiction.

Thus any vector with the original centered coefficients is outside the closed
prime-selector domain. This is a paper proof, NOT yet a Lean theorem.
It does not exclude existence of the centered source itself. C3's proposed
selection-based producer is FALSE; TG's coupled energy target remains active.

Positive survivor if C3 fails: literal closed idempotent selection exists but
the cancellation must be retained as an affine coupled source; splitting its
prime part is not an admitted operation. This is a restriction within TG,
not a pivot from its arithmetic energy target.

## Plan and verification

1. C2 paper proof: complete above; formalize exact carrier and graph.
2. Compile targeted leaf, inspect axioms in /tmp, wire umbrella, run lint.
3. C3 paper domain attack complete; Lean formalization deferred under user
   steering to work directly on quantitative source bounds and zero exclusion.
4. Continue C1: Summable soninPrimePolarGridEnergy, through the native Mellin
   conversion recorded in ../../../3-formalized/tg-quantized-exclusion-loop-2026-10-15.md.
   RH remains open.

C2 verification completed: targeted `lake build --old
+GaloisForLFunctions.RHTower.SoninGroundGridClosedMultipliers` passed;
final `lake env lean GaloisForLFunctions/RHTower/SoninGroundGridClosedMultipliers.lean`
passed without diagnostics. Scratch axiom audits of closedness, idempotence,
and cofinal limit uniqueness reported only propext, Classical.choice,
Quot.sound. Umbrella import added. Latest repository lint reports the unrelated
EvenSectorNegPartAbelRigidity leaf missing its umbrella import; no C2 or TG
Mellin conversion error.

No external search/novelty audit, per user override. No numerical experiments.
No claim of scientific novelty from formalizing C2.
