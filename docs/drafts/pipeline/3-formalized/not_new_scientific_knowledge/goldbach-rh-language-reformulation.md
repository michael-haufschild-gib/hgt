# Goldbach in the languages of the RH programmes

- **ID:** goldbach-rh-language-reformulation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE
- **Request:** express Goldbach in the objects and mechanisms of the twelve RH programmes; do not treat each programme as a candidate proof of Goldbach.
- **Source:** the twelve programme READMEs named by the user.
- **Novelty:** internal structural translation; no claim of new analytic estimates or external scientific novelty.

## Working object

For a fixed integer target N, use the actual prime vector
u_N(k) = 1_{k prime} log k on 0 ≤ k ≤ N, and reflection J_N u(k)=u(N-k).
The weighted Goldbach count is the overlap <u_N,J_N u_N>. Its strict positivity is equivalent to a representation of N by two primes.

The translation should retain this source and its target anchor throughout. It should identify the exact incidence kernel, reflection-even and reflection-odd energies, and compensation terms, then distinguish these from the test family and limit quantifiers that express RH.

## Reading ledger

All twelve requested READMEs read. The synthesis below records which objects transfer literally,
which algebra transfers after changing the kernel, and which geometrical analogy needs a new map.

## The same damped source: complete finite paper proof

Write τ_ε(k) for the existing `RHTower.pmPowerDampedDivisorCoeff ε k`, with τ_ε(0)=0. For positive k it equals ∏_{p|k}(1-p^{-ε}). Let

    a_ε(k) = if Squarefree(k) and k ≠ 1 then τ_ε(k) else 0,
    F_N(ε) = Σ_{k+l=N} a_ε(k) a_ε(l).

These definitions use squarefreeness, divisor incidence and damping; primality is not built into the definition. The unit must be removed: τ_ε(1)=1 would otherwise contaminate the second coefficient.

**Theorem [PROVED HERE, BRIDGE].** For every N≥0,

    lim_{ε→0, ε≠0} F_N(ε)/ε² = Σ_{p+q=N, p,q prime} log p log q.

Consequently binary Goldbach is equivalent to strict positivity of this limit at every N=2(n+2).

Proof. Each τ_ε(k) is a finite sum of smooth functions μ(d)d^{-ε}. Its derivative at ε is the existing `dampedVonMangoldt ε k`; at zero this is Λ(k). The value at zero is δ_{k=1}. Thus a_0(k)=0 for every k and a'_0(k)=1_{Squarefree k}Λ(k). A squarefree prime power is prime, and Λ(1)=Λ(0)=0, so this derivative is exactly `primeLogWeight k`. The definition of derivative gives a_ε(k)/ε→primeLogWeight(k). Multiply the two limits, then sum over the finite antidiagonal. For ε≠0, their product equals a_ε(k)a_ε(l)/ε². Each summand in the resulting limit is nonnegative and is positive exactly when both entries are prime. A finite nonnegative sum is positive exactly when one summand is positive. This proves both statements without an unproved input.

The stronger local description is F_N(ε)=G(N)ε²+o(ε²). This is a jet at each fixed N. It exchanges no infinite-horizon limit with ε→0.

In the finite Euler product, each factor is ε log p + O(ε²). A squarefree
integer with r prime factors therefore first appears at normal order r, with
positive leading coefficient ∏ log p. The squarefree first layer consists
exactly of primes. The equivalent geometric question is whether every even
additive fibre meets this first layer in both coordinates; its order-two
coefficient is the weighted incidence of that intersection.

**RH side, using existing corpus criterion.** For the SAME τ-family, put A_ε(m)=Σ_{k≤m}τ_ε(k)−m/ζ(1+ε). RH is cofinal admission of Σ_{m≤T}A_ε(m)²/(m(m+1)), with a bound independent of T at each admitted ε. Goldbach reads the squarefree, unit-removed second additive-overlap jet of τ. RH reads the centered prefix in the pronic norm at arbitrarily small positive dampings. This is an exact common-source relationship, not an implication between the two conclusions.

## Candidate exact bridges

1. Goldbach as strict overlap of the actual prime vector with its anchored reflection.
2. Goldbach as reflection-even energy strictly exceeding reflection-odd energy.
3. Goldbach as a finite divisor-row incidence form, with compatibility gcd(d,e)|N.
4. Same actual arithmetic source, different observation: RH via the existing global Weil/receiver criterion; Goldbach via each finite reflected fibre. An equivalence between RH and Goldbach is not asserted.
5. Goldbach as nonvanishing of the second damping coefficient of the squarefree projected source, proved above.

## Reflection and incidence: complete finite paper proofs

For any real sequence w and target N, let M = Σ_{k=0}^N w(k)² and

    E₊ = ¼ Σ_{k+l=N} (w(k)+w(l))²,
    E₋ = ¼ Σ_{k+l=N} (w(k)−w(l))²,
    D  = ½ Σ_{k+l=N} (w(k)−w(l))².

Subtract the two squares pointwise to obtain G_w(N)=E₊−E₋. Add them and use
the two bijections k↦(k,N−k) and l↦(N−l,l) to obtain E₊+E₋=M.
Consequently D=2E₋ and G_w(N)=M−D. These identities hold for every real w,
including signed weights. For the actual prime weight, G≥0, so D≤M is
automatic; Goldbach asks for strict inequality. A failed target is exactly
saturation D=M, or E₊=E₋. This identifies the boundary rather than replacing
the arithmetic question with a universal positivity assertion.

On Fin(N+1) put c_N(i,j)=1 if i+j=N, and zero otherwise. This is a symmetric
coupling in Signed Arithmetic Energy Incidence. Its existing incidenceEnergy
at the profile i↦w(i) is exactly G_w(N): expand its definition, restrict the
double sum to i+j=N, and use the antidiagonal bijection. Goldbach is strict
positivity on the specified prime profile. The matrix itself is indefinite
for N>0: at the endpoints the profile (1,−1) has energy −2. Its positivity on
all real profiles would therefore be a false reformulation.

## Formalization discipline

Write a complete finite paper proof before Lean. Reuse the existing primeLogWeight and primePairWeight from goldbach/RiemannHypothesisBridge.lean. Search the corpus before mathlib. Add no analytic premise or substitute source. Check only exact leaf modules with the user-prescribed plain Lean command.

## Synthesis and validation

- The twelve-programme dictionary is [formal/GaloisForLFunctions/goldbach/README.md](../../../../../formal/GaloisForLFunctions/goldbach/README.md).
- Definitions and proofs are integrated into the existing `goldbach/RiemannHypothesisBridge.lean`, already imported by `goldbach/Main.lean`. A separate importing leaf would require producing the existing bridge's absent olean; integration preserves the user's plain-command-only compile rule.
- The extended leaf passed `lake --old env lean GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean` from `formal/`, with no warnings. The same command with temporary `#print axioms` directives passed again; all five audited closures use only `propext`, `Classical.choice`, and `Quot.sound`. Temporary directives were removed without changing proofs.
- No external literature search was used for this task. The requested output is an internal translation, explicitly classified BRIDGE; no scientific novelty claim depends on an external audit.
- The proposed translations were checked against quantifier changes, lost target anchors, proper prime powers, the unit coefficient, and additive versus logarithmic antidiagonals. The false strengthening to positivity on all signed profiles has the endpoint witness recorded above.

## Lean certificate

Module: `formal/GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean`.
Namespace: `GaloisForLFunctions.Goldbach`.

- `hasDerivAt_squarefreeDampedSource_zero`: the projected source's first derivative is `primeLogWeight`.
- `tendsto_dampedReflectionOverlap_div_sq`: its reflected quadratic coefficient is `primePairWeight`.
- `goldbach_iff_positive_dampedReflection_limit`: the original Goldbach proposition iff every even-target coefficient is strictly positive.
- `additivePairWeight_eq_even_sub_odd`, `reflectionEvenEnergy_add_odd`, `additiveReflectionDefect_eq_twice_odd`, `additivePairWeight_eq_mass_sub_defect`: exact identities for every real sequence.
- `goldbach_iff_reflection_even_dominates`, `goldbach_iff_reflection_defect_lt_mass`: the two reflection formulations.
- `goldbachReflectionCoupling_symmetric`, `incidenceEnergy_goldbachReflectionCoupling`, `goldbach_iff_positive_reflection_incidenceEnergy`: literal specialization of the existing SAEI coupling and energy.

The four Goldbach equivalences and the existing
`riemannHypothesis_iff_boxedPrimePairMass_error` were closure-audited.
Audit log: `/tmp/hgt-goldbach-rh-language-axioms.log`.
The CRT expansion, general compensation identity, polynomial reading and
normal-layer interpretation have the finite paper proofs recorded in the
dictionary. They are not listed as additional Lean results.

## Research assessment

The useful change is representational: a Goldbach target is now an exact reading
of the RH receiver's actual source, with its projection and kernel specified.
The arithmetic source is shared; an implication between its different readings
has not been proved. No analytic frontier or literature novelty is claimed.
The requested formal reformulations are complete.

## Integration audit

- `goldbach/Main.lean` already imports the extended bridge. The separately
  completed square-divisor helper is now imported there too. No umbrella was
  compiled.
- `scripts/formal_tools.py index` regenerated all three indexes and refreshed
  the local declaration index. The generated files are refreshed again after
  the lint finding below.
- `scripts/formal_tools.py lint --check-generated` reports unreachable modules
  in other programmes and three research leaves at the package root. It also
  reports a stale global `LEAN_OVERVIEW.md` during concurrent repository edits.
  No Goldbach module is named in a diagnostic. These global findings are not
  represented as a clean repository lint result.
- Lint log: `/tmp/hgt-goldbach-rh-language-lint.log`.
- Owned tracked files pass `git diff --check`. Temporary source/search files
  and audit directives were removed; audit logs remain available. All owned
  Lean checks terminated successfully.
