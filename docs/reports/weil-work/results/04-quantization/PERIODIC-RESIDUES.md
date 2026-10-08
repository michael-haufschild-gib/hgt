# Translation constraints on the actual reflected residues

Cycle 20. T20 and signed bilateral rational L2 proved in Lean. All four final
direct leaf audits and the dependency-axiom audit passed without diagnostics.
All 25 declarations use only propext, Classical.choice and Quot.sound.

## Conjecture T20

For the actual source hW and any exponentially summable frequency representation
of exp(2πi C(x)), let B(t) be the sum of p_j exp(ω_j/4) a(n) over
positive integers n satisfying log n + ω_j/2 = log t. Then B(t+1)=B(t)
for every t>0. This is an exact constraint on a supplied representation;
existence of a representation is not inferred from hW.

Competing route: integer radial comparisons might be the only justified
comparisons, leaving arbitrary noninteger residues unconstrained. The actual
source identity `quantization_reflected_defectLaplace_eq` rules out that
particular objection: its exponential series is exactly i-periodic, and its
polar correction disappears after multiplication by ε at every nonzero height.

[OPEN CORE] Pay the positive-real-height resonance limit and its normalization,
then transfer exact periodicity to B. Do not assume noninteger residues vanish.

## Proposed arithmetic consequence

For r=u/v with coprime u>v>1 and ω_k=2k log r, B(r^k) has exactly the
single resonance j=k, hence equals p_k r^(k/2). For k≠0, r^k+1 has no
resonance: its reduced numerator is u^|k|+v^|k|, coprime to both u and v,
and its nontrivial denominator is respectively v^k or u^(-k). Multiplication
by any integral power of r cannot make it an integer. Thus periodicity would
give p_k=0 for every k≠0, closing the signed bilateral rational case L2.

The exact proposed final source-only alternative is: either λ=Λ on n≥2 and
RH, or the actual residual phase has no such bilateral rational representation.
Full WP04 still requires excluding the remaining unrepresented phases.

## Dependency audit in progress

- Actual reflected Laplace identity: already compiled in ReflectedResidue.
- Integer-height full frequency resonance: already compiled in FrequencySum.
- Real-height extension may be obtained by scaling the kernel to height one
  and shifting each frequency by −2 log t; this would reuse the existing
  dominated infinite-frequency argument rather than redo it.
- Nonzero common normalization: source phase coupling at height one.
- Compact and upper pieces: require a real-height version, or the same scaling
  applied to the existing vanishing lemmas.
- Arithmetic isolation and final assembly: paper audit still pending.

No sign, NotchSmall, boundary continuity, atomicity or half-integer mass premise
is accepted. The D19/notch route remains unproved: inspected notch receivers
need harmonic smallness or absolute harmonic convergence not paid by the gap.

## Dependency-closed paper proof

Write Φ(y) for the actual quotient trace, Ψ(y) for its reflection, K(y,τ)
for pairKernel, κ for the origin phase, and β for the actual polar constant.
Both traces are measurable and polynomially bounded by the source theorems.
For x>0 put a=log x. Directly from the principal complex power, positive
real multiplication preserves its argument and gives

    K(y,xτ)=exp(−a/2) exp(iay) K(y,τ).

1. For each frequency family let ω'_j=ω_j−2a. Its weighted norm sum is
   finite because exp(|ω'_j|/2)≤exp(|a|) exp(|ω_j|/2). Substituting ε=xδ
   in the lower-tail integral therefore gives the exact identity

       ε∫[y≤−2] Σp_j linTwist(ω_j,y) Φ(y) K(y,ε+ix)dy
       = exp(a/2) δ∫[y≤−2] Σp_j linTwist(ω'_j,y) Φ(y) K(y,δ+i)dy.

   Apply the existing frequency-sum resonance theorem at height one. The
   error tends to zero. Its surviving coefficient is

       B(x)=exp(a/2) Σp_j quantizationFrequencyResidue(λ,ω'_j,1).

   This is the B in T20: the resonance equation is log n+ω_j/2=log x,
   and exp(a/2) exp((ω_j−2a)/4)=exp(ω_j/4).
   Summability follows from the existing residue bound at height one.

2. Height-one phase coupling supplies B(1)≠0 and

       M(δ)=quantizationMainRadial(1,δ) → L=4β/(κ B(1)) ≠0.

   Here β≠0 is already proved from the normalized nonvanishing primitive,
   and |κ|=1. No explicit evaluation of the common kernel is needed.
   Thus the actual reflected lower-tail integral at height x has radial
   limit κ L B(x). This uses its already proved almost-everywhere phase
   identity; no equality is imposed at zero or at atoms.

3. The complementary part y>−2 contributes zero. At height one, split it
   into −2<y<0, y=0 and y>0. The bounded compact piece has uniformly bounded
   integral by the existing kernel bound, the singleton has zero Lebesgue
   measure, and the polynomially bounded upper piece vanishes by the existing
   upper radial lemma. At height x, the exact scaling above replaces Ψ(y)
   by exp(iay)Ψ(y), which retains measurability and the same polynomial bound,
   and multiplies the radial expression by exp(a/2). Thus it still vanishes.

4. Changing y=2t shows the full defectLaplace residue at height x is
   κ L B(x)/(4π). The actual source identity is

       defectLaplace(Ψ(2·),τ)=Σ[n≥1] a(n) exp(−2πnτ)−β/(πτ).

   Its series is exactly invariant under τ↦τ+i, term by term. At x>0
   and x+1>0 each polar correction multiplied by ε tends to zero. Hence
   the two full residues coincide. Since κL≠0, B(x+1)=B(x).

5. For the bilateral rational specialization, x=r^k has one resonance:
   x r^(−j)=r^(k−j) is an integer iff k=j. Indeed a nonzero power of a
   reduced fraction with numerator and denominator greater than one is
   never an integer. Since a(1)=1, B(r^k)=p_k r^(k/2).

   If k>0, x+1=A/v^k with A=u^k+v^k coprime to uv. For j≥0,
   (x+1)r^(−j)=A v^j/(v^k u^j): when j>0 the u denominator cannot cancel;
   when j=0 the v denominator cannot cancel. For j<0, writing q=−j>0,
   the denominator v^(k+q) cannot cancel against A u^q. If k<0 the same
   argument exchanges u and v and replaces j by −j. Thus B(r^k+1)=0.
   Periodicity gives p_k=0 for every k≠0, including all negative harmonics.

6. At every natural m≥1, the original constant-row theorem now gives
   p_0 a(m)=p_0 a(1)=p_0, with p_0≠0. Therefore a(m)=1. The existing
   forward-coefficient rigidity receiver gives λ=Λ on n≥2 and RH.
   Contraposition yields the stated source-only alternative. This proves L2
   on paper, subject to independent formal verification of all six steps.

## Attack and external comparison

The one-sided Blaschke warning model satisfies integer rows but would have
nonzero B(r^k) and zero B(r^k+1) for some k. Therefore the new constraint
detects precisely information discarded by the integer-only system. No
countermodel to T20 was obtained. Values x<1 are handled by positive scaling,
not by a kernel bound that incorrectly assumes norm τ≥1.

The primary Kaczorowski–Molteni–Perelli account of Hamburger rigidity
(https://air.unimi.it/handle/2434/142161) requires global continuation and a
functional equation. Those assumptions cannot be silently assigned to hW.
The present proof instead uses the corpus's actual measurable-trace identity.
Its scaling and periodicity mechanisms are classical; the claimed corpus
advance is closure of the previously unpaid signed bilateral rational case.
Independent scientific novelty beyond this corpus remains unestablished.

Verdict: SURVIVES PRELIMINARY ATTACK; dependency-closed paper proof complete.
RealResonance, PeriodicResidues, RationalTranslation and BilateralRigidity passed
their final direct leaf audits without diagnostics and are wired. All 25
declarations passed the scratch dependency-axiom audit with only standard
axioms; output is in periodic-residues-lean-audit.txt. No full or umbrella build
was run. Full WP04 remains OPEN.

Validation commands used `lake --old env lean -o <leaf.olean> <leaf.lean>` for
each of the four leaves and `lake --old env lean <scratch>` for the full axiom
and mathlib-name audit. Final scratch exit was 0. The initial scratch attempt
printed the same clean axiom sets but required explicit universe levels for
two name probes; no source theorem changed during that repair.

Formal lint exited 1 on eight unrelated unreachable leaves:
WeilWorkHigherDenominatorCosineMellin, WeilWorkHigherDenominatorPrimitiveGamma,
WeilWorkSettledPhaseValuationMasks, ApertureConeCalculus, ApertureConeWinding,
ApertureLogTranslation, ApertureOpenHistoryIdeal and BoundaryCoronaCStarAlgebra.
No quantization error was reported. All four new imports occur exactly once;
the quantization corpus now has fifty wired leaves.

## D19 audit retained from this cycle

The earlier divisor-gap conjecture asks whether a(n)=1 whenever u∤n and v∤n
already forces rigidity for any actual hW. It remains unproved. The following
distinctions prevent treating the new L2 result as a proof of D19:

- A rough coefficient gap transfers to the corresponding divisor-closed
  deviation gap, but does not itself bound the absolute harmonic tails.
- `NotchSmall` contains three quantitative little-o bounds in addition to
  absolute Dirichlet summability. The latter alone is supplied here.
- `eq_vonMangoldt_of_harmonicPinning` requires absolute harmonic summability
  on every multiples fibre, not merely conditional convergence.
- The unsymmetrized gcd-weighted fibre kernel is not even. Its real quadratic
  form controls the symmetrized kernel; it cannot silently be declared the
  Fourier transform of a positive measure.
- The source coprime Abel theorem supplies bounded real values, not zero limit
  or absolute convergence. The new forward variance identity permits positive
  variance and does not identify the source with the zeta coefficients.

Kulikov–Nazarov–Sodin's Fourier uniqueness theorem
(https://jmag.ilt.kharkiv.ua/index.php/jmag/article/download/1095/jm21-0084e/1214)
concerns discrete sampling sets, not identification of canonical spectral mass.
Favorov's quasicrystal correspondence
(https://jmag.ilt.kharkiv.ua/index.php/jmag/article/download/1076/jm20-0279e/1173)
already assumes natural atomic multiplicities. Neither pays WP04's integrality
obligation. No outside theorem was used to assume those missing source facts.

## Self-audit

1. New knowledge: the actual-source period-one residue law closes signed L2,
   removing the unpaid sign/negative-mass condition. Independent novelty beyond
   literature is unestablished; present it as a verified corpus advance.
2. Rediscovery: the notch branch repeated no formalization. Exact premise
   inspection exposed missing absolute bounds, prompting the translation pivot.
3. Theatre: kernel scaling and periodicity are classical. They were formalized
   only as dependencies of the new complete signed-case theorem.
4. Frontier movement: every weighted bilateral rational representation is now
   excluded for a nonrigid actual source. P18 and D19 themselves are still open.
5. Big picture: retain real-height translation, which contains information lost
   by integer rows. Representation existence and arbitrary spectral mass remain
   the full WP04 obligation; class exclusions alone do not complete it.
6. Effort without knowledge: the first notch investigation found a precise gap;
   the subsequent work produced the period-one law and L2, not another wrapper.
7. Difficulty: the full infinite signed frequency sum and negative harmonics
   were handled, with positive dilation also covering heights below one.
8. Hardest step: attacked the unpaid signed L2 step directly. No finite-block
   invertibility, absolute harmonic convergence or sign premise was inserted.
9. Corpus use: searched candidates and source arguments, reused the actual
   measurable-trace identity and frequency-sum proof, and retained coverage
   caveats. No theorem was selected from remembered literature alone.
