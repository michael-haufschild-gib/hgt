# Arithmetic frequency selection for the actual residual phase

Cycle 19. PROVED IN LEAN; clean final direct leaf and dependency-axiom audits passed. WP04 and P18
remain open; cycle 20 closes signed L2 in PERIODIC-RESIDUES.md. This is a restriction on every represented actual phase, not a
representation producer. Independent scientific novelty is unestablished.

## Exact statements and verdict

For arbitrary hW : WeilPositiveFull λ, let C be its actual residual cumulative
measure and let R mean λ(n)=Λ(n) for every n≥2 together with RH.

**L3.** Either R holds, or every countable representation

    exp(2πi C(x)) = Σ_j p_j exp(i ω_j x), x>0,
    Σ_j |p_j| exp(|ω_j|/2) < ∞,

has an active nonzero arithmetic frequency: there are j and positive distinct
integers m,n with p_j≠0 and ω_j=2 log(m/n).

**L3p.** Either R holds, or every such periodic representation with
ω_k=2k log r, k∈ℤ, r>1, has a rational positive power: there exist k≥1 and
positive integers m,n with r^k=m/n. Thus every base with all positive powers
irrational is excluded for a nonrigid source. Rational-power bases remain open
in general; this statement does not reduce their phases to rational periods.

Verdict: SURVIVES ATTACK, with the following dependency-closed proof. No
coefficient sign, summable negative part, finite-section invertibility or
noninteger reflected radial cancellation is used.

## Proof

1. Put a(n)=dirichletExp(lamLog λ)(n). The audited source theorem
   quantization_phase_resonance_constant gives B(1)≠0 and B(m)=B(1) for every
   positive integer m, where B(m)=Σ_j p_j R(ω_j,m). Here R(ω,m) is zero unless
   some positive integer n satisfies log n+ω/2=log m; in that case it is
   exp(ω/4)a(n). Every interchange and radial limit is already paid by that
   theorem using the displayed weighted summability.
2. Suppose the conclusion of L3 fails. For an active p_j and a resonance,
   if ω_j≠0 then n≠m and ω_j=2 log(m/n), contradicting the supposition.
   Hence only zero frequencies contribute. At ω_j=0 the unique resonant
   integer is m and R(0,m)=a(m). Inactive terms vanish.
3. Define c=Σ_{j:ω_j=0} p_j, retaining repeated zero frequencies. The exact
   termwise identities and scalar multiplication of convergent series give
   B(m)=c a(m). Since a(1)=1, B(1)=c≠0. The constant-row identity therefore
   gives a(m)=1 for every m≥1. The already audited actual-source receiver
   vonMangoldt_and_RH_of_coeff_eq_one gives R. Contraposition proves L3.
4. Apply L3 to a periodic representation. Its selected frequency has k≠0:
   k=0 would imply log m=log n and hence m=n. If k>0, the frequency equality
   gives log(r^k)=log(m/n); positivity and injectivity of log give r^k=m/n.
   If k<0, negate k and interchange m,n. This proves L3p.

## Adversarial audit and scope

- Repeated frequencies and cancellation are retained; no chosen zero index or
  injectivity of the frequency enumeration is assumed. An active term is only
  a necessary condition, not a complete characterization of the Bohr spectrum.
- A nonzero rational logarithm is essential: ω=0 alone carries normalization
  and forces rigidity. The positive-integer restrictions exclude log 0.
- The result applies to infinite bilateral or countable series. It does not
  assert arbitrary Weil phases are almost periodic or have weighted summability.
- Merely irrational r is insufficient: an irrational root of a rational number
  has a rational power. These resonances must remain in the open class.
- P18's signed-composite obstruction has not disappeared. The corpus's signed
  Gibbs and notch arguments still need sign alignment, absolute control or
  NotchSmall. No argument here supplies these missing inputs.

## Literature and corpus audit

The current corpus's PhaseCoupling supplies the exact arithmetic rows; previous
PeriodicRigidity handles integer bases, RationalRigidity handles one-sided
rational phases, and NegativeMass handles finite negative harmonic mass.
Targeted searches and exhaustive text search of the quantization leaves found
no existing general arithmetic-frequency selection or rational-power necessity.

Schoolmann, *On Bohr's theorem for general Dirichlet series* (2020),
https://doi.org/10.1002/mana.201800542, treats general Dirichlet frequencies and
bounded holomorphic extensions. This is relevant parent theory, not the actual
Weil-phase normalization used here. The selection step is elementary once the
corpus's source identity is available; formalization alone is not evidence of
significant independent novelty.

The P18 audit also checked Farmer's Selberg-class multiplicity-one theorem,
https://arxiv.org/pdf/2101.02771, and Farmer–Pitale–Ryan–Schmidt,
https://aimath.org/jmm2014/a1farmer/section1.html. Their Euler-product and global
analytic hypotheses are not supplied by arbitrary hW. Booker's L-data
framework, https://arxiv.org/pdf/1308.3067, assumes a discrete spectral divisor;
it cannot supply the missing quantization before that assumption is proved.


## Formal realization

WeilWorkQuantizationArithmeticSpectrum.lean contains four declarations: the
zero-arithmetic-frequency receiver, the source-only arithmetic-frequency
alternative, the logarithmic rational-power lemma, and the source-only
periodic-base alternative. Final direct `lake --old env lean -o ... <leaf>`
check exited 0 with no diagnostics. All four declarations and dependencies
use only propext, Classical.choice and Quot.sound. Full source-only types and
output: arithmetic-spectrum-lean-audit.txt. The leaf is wired exactly once.
No full or umbrella build, numerical experiment, heartbeat override or new axiom.
