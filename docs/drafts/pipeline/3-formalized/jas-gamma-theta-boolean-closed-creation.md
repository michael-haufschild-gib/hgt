# JAS Gamma–theta Boolean closed creation

Status: **FORMALIZED IN LEAN 4**

Route: JAS

Novelty: **NOVELTY UNVERIFIED**. Corpus search found separate constructions for the Gamma Boolean support connection, literal completed-theta grades, maximal real `L²` multiplication, and separated-product density, but no operator coupling all four. Literature audit through 2026-08-29 found general commuting weighted shifts and multishifts on Cartesian products (arXiv:1508.01260, arXiv:1607.03860, arXiv:1904.00983), and operator-theoretic RH programs such as Connes--Consani's scaling Hamiltonian (arXiv:1910.14368), but no Gamma-weighted finite-prime-support creator coupled to the literal completed-theta Mellin ladder or this Xi-sewing role.

## Corpus origin

`JointAncestryGammaBooleanClosedCreation` proves a closed state-dependent support-raising Gamma connection on `ell²(Finset Primes)` but explicitly leaves actual-theta coupling open. `JointAncestryActualThetaAdjacentGradeShiftEscape` proves every bounded literal theta-grade successor impossible. `MaximalRealL2Multiplication` gives the required closed unbounded multiplication, while `L2SeparatedProductDensity` gives the exact product `L²` carrier. These corpus results force, rather than merely suggest, a cross-coordinate unbounded construction.

## Result JAS-GTBC-1

On

`L²(Finset Primes × ℝ, count × volume)`, for every prime `p` and real sewing point `x`, define maximal multiplication by

`1_{p ∉ P} · jasGammaBooleanInsertionGain x p P · exp(y)`

and postcompose with the unitary toggle `P ↦ P △ {p}`.

Prove unconditionally in Lean that:

1. support toggle times identity is a measure-preserving measurable equivalence;
2. resulting partial operator is closed and densely defined;
3. every separated packet `e_P ⊗ completedThetaGrade(r)` lies in its domain;
4. exact action is zero when `p ∈ P`, and otherwise
   `e_P ⊗ theta_r ↦ gain(x,p,P) · e_(insert p P) ⊗ theta_(r+1)`;
5. for nonempty unoccupied faces, coefficient is the original corpus Gamma insertion gain;
6. at `r = |P|`, support cardinality and literal theta grade advance synchronously;
7. at every physical sewing point `x > 0`, two-prime operator paths agree on every separated packet for which both compositions are interpreted, yielding a flat closed Gamma–theta connection.

No axiom, premise package, computation, `sorry`, `admit`, `opaque`, or `unsafe` declaration is used.

Formal module: `GaloisForLFunctions.RHTower.JointAncestryGammaThetaBooleanClosedCreation`.

Main capstones:

- `jasGammaThetaCreation_closed`
- `dense_jasGammaThetaCreation_domain`
- `jasGammaThetaCreation_packet_eq_gamma`
- `jasGammaThetaCreation_supportCard_grade`
- `jasGammaThetaCreation_twoPrime_operator_paths`
- `jasGammaThetaClosedCreation_package`

The package theorem is a closed proposition universally quantifying all data. Closedness, density, and exact packet action hold for every real `x`; flatness is asserted on the corpus-native positive sewing locus.

## Full RH proof chain

JAS-GTBC-1 closes the literal support/actual-theta closed-graph burden forced by the bounded-successor and prime-torus-unit no-gos. It must then feed a coefficient-faithful prime-Poisson correspondence proving source-linearity and divisor independence of the higher-compound Xi current. That produces `XiPrimePoissonReflectionSewing ρ` for every Xi divisor. Corpus endpoints give

`XiPrimePoissonReflectionSewing ρ`
→ `xiPrimePoissonReflectionSewing_iff_internalOnly`
→ `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`
→ every nontrivial Xi zero has real part `1/2`
→ RH.

Thus this conjecture is not an RH proof; it closes one named producer burden and exposes the next exact burden: source-linear, divisor-independent Xi-current landing.

## Conjecture failure and strongest survivor

The frozen all-real flatness statement was too strong. The Boolean gain is a ratio of synchronized weights; cancelling the intermediate weights requires their nonvanishing. The corpus proves strict positivity, hence nonvanishing, on `x > 0`, which is precisely the physical Gamma sewing locus. The proof therefore pivoted to the strongest justified statement: closedness/density/exact action for all real `x`, and two-prime operator flatness for `x > 0`. No weaker carrier or abstract surrogate was substituted.

## Verification

- direct: `lake env lean GaloisForLFunctions/RHTower/JointAncestryGammaThetaBooleanClosedCreation.lean`
- leaf audit: `lake build GaloisForLFunctions.RHTower.JointAncestryGammaThetaBooleanClosedCreation` — passed `[12111/12111]`
- axiom audit: all named capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`
- formal lint: no forbidden declaration or reachability error for this module; repository-wide lint still reports unrelated pre-existing umbrella reachability failures and large-file warnings
- wired into `GaloisForLFunctions.RHTower`

## Falsifiers / pivot record

- If product toggle cannot be made measure-preserving for counting measure, retire this carrier and use the corpus Hilbert-tensor equivalence.
- If separated actual-theta packets fail the maximal domain, the proposed cross-coordinate law is false and the strongest positive survivor is the exact maximal-domain criterion.
- Product toggle is measure-preserving and separated actual-theta packets lie in the maximal domain, so the first two falsifiers did not fire.
- All-real two-prime flatness failed at the cancellation step; the exact positive-locus survivor above was formalized.
