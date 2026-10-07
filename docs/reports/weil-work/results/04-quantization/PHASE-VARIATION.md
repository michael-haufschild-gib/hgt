# K: intrinsic phase variation — paper and Lean proof

2026-10-07. This follows the eleventh-cycle rejection of H2's novelty claim.
H2 remains the open LP margin problem already recorded in STATUS CANNOT-496.

## Exact statement

For the specified `hW : WeilPositiveFull lam`, let ν be its canonical
integer-floor residual measure and put

`C(x) = ν.real (Ioc 0 (2*x))`,
`W(x) = exp(2*pi*i*C(x))`,
`V(x) = variationOnFromTo W univ 0 x`.

Thus for x≥0, V(x) is the ordinary metric total variation of the complex
unit-circle path W on [0,x]. It counts the chord across each jump, not the
number of turns in a chosen real phase lift. Write R for λ=Λ on n≥2 and RH.

**K:** every hW satisfies

`R ∨ ∀ α<1, ∀ K∈ℝ, ∀ᶠ U→+∞, K*U^α < V(U)`.

No discreteness, boundary continuity, atom enumeration, or residual growth
premise is an input to this final alternative. This is not full WP04: the
large-variation branch still needs exclusion.

## Exact attack and significance

J charges the entire positive floor remainder. Atoms with masses tending to
an integer from below can therefore make its obstruction large even when
their actual phase jumps are small. K charges the observed phase path.
Integer jumps cost zero; almost-integer jumps have small chord cost. General
singular-continuous and accumulating atomic measures remain in scope.

The inspected parent `fractional_two_sided_power_growth_rigidity` already
handles signed nearest-integer errors for an explicitly atomic spectrum at
distinct ordinates escaping to infinity, under a global power bound. Its
cell construction does not apply directly to an arbitrary canonical measure.
`lock_phase_variation_rigidity` assumes a differentiable lock phase and
continuous boundary values. K supplies its path from the actual radial trace
and uses only arbitrarily late quiet radii. The profile extension and
bounded-variation facts below are classical prerequisites, not novelty claims.

Preliminary verdict: **SURVIVES PRELIMINARY ATTACK** as a stronger intrinsic
source obstruction. Scientific novelty remains provisional. The external
Booker L-datum comparison retains discrete spectral support and almost-all
integral multiplicities; it cannot be applied to obtain these inputs.

## Dependency-closed proof

1. C is monotone and locally finite by the already formalized canonical
   measure construction. The function v↦exp(2πiv) is Lipschitz (constant 4π
   suffices, by its sine and cosine components). Hence W has bounded
   variation on every compact interval. Its signed cumulative variation V
   is finite, monotone on ℝ, and V(1)≥0. Exact additivity of variation gives
   `dist(W(x),W(y)) ≤ |V(x)-V(y)|` for all x,y. For x≤y this follows from
   the endpoint-distance bound on [x,y] and
   `Var[x,y] = V(y)-V(x)`; swap x,y for the other ordering.

2. Define a complex function on range(V) by V(x)↦W(x). It is well-defined:
   equal V-values force zero distance between the corresponding W-values.
   Both real components are 1-Lipschitz. Extend them separately to real
   1-Lipschitz functions a,b on ℝ by the McShane extension theorem. Set
   Ψ=a+ib and ψ=a'+ib'. Then Ψ(V(x))=W(x), ψ is measurable, and |ψ|≤2.
   Lipschitz absolute continuity and the fundamental theorem give, for u≤v,
   `Ψ(v)=Ψ(u)+∫_(u,v] ψ`.
   Only Ψ on range(V) is required to have norm one. In particular
   `min(V(x),V(U))` is one of two values in that range, so its Ψ-value also
   has norm one. No norm claim about an arbitrary extension value is needed.

3. Let d be integrable on (-∞,-1], and suppose its signed primitives satisfy
   `|∫_(-∞,b] d| ≤ E exp(b δ)` for b≤-1, E≥0 and δ>0. Cap V at V(U), U≥1.
   The corpus's general-profile layer-cake theorem, with profile density ψ
   and level majorant 1 on (V(1),V(U)], gives

   `|∫_(-∞,-1] Ψ(min(V(-t),V(U))) d(t)|
      ≤ E * (1 + 2*(V(U)-V(1)))`.

   Its product-integrability condition follows from
   `0 ≤ min(V(-t),V(U))-V(1) ≤ V(U)-V(1)` on this half-line.
   The capped and actual multipliers agree for -t≤U. Both have norm one;
   their integral difference therefore has norm at most
   `2 * ∫_(-∞,-U] |d|`.

4. Apply step 3 to
   `d(t)=ε * quantizationRadialRemainder hW m (ε+i*m) t`, m≥1.
   The already checked source primitive and absolute-tail estimates used
   in `exists_quantization_twist_local_bound` do not depend on monotonicity
   of the multiplying phase. They give, for every 0<p<1, constants A,D≥0
   independent of ε∈(0,1] and U≥1,

   `|ε∫_(-∞,-1] W(-t) remainder(t)|
      ≤ A ε^(1-p) (1+2*(V(U)-V(1)))
         + D ε^(-1) exp(-ε*U/(m+1))`.

   All source analytic estimates, both polar terms, and the actual
   arithmetic resonance subtraction are retained unchanged.

5. Suppose V(U)≤K U^α at arbitrarily late radii for some α<1. Replace α by
   max(α,1/2) and K by |K|+1. On the nontrivial filter selecting those
   radii choose α<q<1 and 0<p<1 with α<q(1-p). Put ε=U^(-q)/r for any
   fixed r>0. The first term in step 4 tends to zero since
   `α-q(1-p)<0`; the exponential tail tends to zero since q<1. The same
   quiet filter works for every fixed m and r; its constants may depend
   on m,p,r. Thus every scaled actual twisted remainder vanishes.

6. The actual reflected radial trace satisfies
   `F_reflected(2t)=originPhase*W(-t)*F(2t)` almost everywhere for t<0,
   including zeros of F. This is the existing cumulative-phase identity,
   without division by F. Feed the vanishing from step 5 into
   `quantization_rigidity_of_remainder_along`, using the measurable
   original real phase C. Its residue comparison forces all nonzero
   Dirichlet-exponential coefficients to one, hence R.

7. Negating the existence of any arbitrarily late power-small variation
   scale yields exactly K. No source upper bound for V was used or proved.

All seven steps are formalized in `WeilWorkQuantizationPhaseVariation`,
`WeilWorkQuantizationVariationLocal` and `WeilWorkQuantizationVariationRigidity`.
Each direct `lake --old env lean -o ... <leaf>.lean` audit exited 0 without
warnings. The final source theorem is
`quantization_rigidity_or_phaseVariation_eventual_power`. A scratch-file
audit of all 26 declarations found only `propext`, `Classical.choice` and
`Quot.sound`; complete output is in phase-variation-lean-audit.txt. All
three leaves are wired; no umbrella build was run. Full WP04 remains open.

## Separate next target

The quantitative identity/bound relating this path variation to diffuse
mass plus nearest-integer atom distances is not needed by the proof above.
It must be audited and proved separately before asserting a canonical
nearest-integer measure theorem. Do not silently identify path variation
with the variation of the real cumulative lift.
