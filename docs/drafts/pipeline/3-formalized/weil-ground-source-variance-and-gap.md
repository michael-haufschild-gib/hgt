# Weil ground source variance and the unrestricted gap

- **Stage:** 3-formalized
- **Lean:** `GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundVariance`; 15 public theorems, wired into `RHTower`.
- **Chain:** exact boundary–arithmetic source → ground-specific variational comparison → exclusion of a constrained zero ground → positive floors at all apertures → RH. The comparison is closed; exclusion remains open.
- **Corpus seeds:** `CCMRestrictedWeilPolarGroundSourceMoment`, `CCMRestrictedWeilPolarParitySourceCoupling`, `CCMRestrictedWeilPolarGroundForcing`, `CCMRestrictedWeilPolarGroundEnergy`, `CCMRestrictedWeilActualBirmanSchwinger`, `CompactConstrainedRadical`, and `HTGeometry.BesselPSD`.

## Conjecture → proof / fail → pivot
1. **Candidate:** use a fixed sign of the source moment to control a selected ground. The source is complex linear and the ground equation allows phase changes. The useful comparison must retain that phase covariance; a phase-independent magnitude is available.
2. **Conjecture:** the actual forcing equation makes the source magnitude exactly the full operator residual variance. **Proved:** the two-pole Gram matrix and orthogonality supply the exact denominator in both parity sectors.
3. **Conjecture:** the actual unrestricted variational floor controls the source magnitude more precisely than the ambient L² defect norm. **Proved:** apply the corpus's semidefinite Hermitian Cauchy–Schwarz theorem to the actual shifted full form, then substitute the exact ground and pole pairings.
4. **Candidate:** positive residual variance and that shifted positivity exclude a zero constrained ground. **False:** the kernel-checked Hermitian swap model has zero constrained energy, nonzero coupling and an attained unrestricted floor of `-1`. Its two-dimensional estimate is saturated.
5. **Positive survivor:** actual ground variance, the source-gap inequality, the literal parity integral bound, zero-source eigenstate classification, and strict unrestricted-gap consequences. All are formal, including an unconditional normalized actual-ground existence theorem.

The generic Cauchy–Schwarz inequality is reused from the corpus, not claimed as new mathematics. The new source statements identify its exact operands and equality consequences for the actual arithmetic Weil ground.

## Dependency-closed paper proof
Fix `a>0`. Write `J` for the physical embedding, `H` for the actual unrestricted Weil operator, `Q` for its form, `mu` for the constrained floor and `lambda` for the unrestricted floor. For parity `r=±1`, put

`p_r=p_++r p_-`, `D_r=2sinh(a)+2ar>0`.

Both pole profiles have complete form lifts and belong to the actual operator domain. Reflection gives equal self Gram entries `2sinh(a)`; their cross Gram entry is `2a`. Consequently

`||p_r||²=2D_r`.

For a constrained vector `f=Ju`, both pole moments vanish, so `<p_r,f>=0`. The already proved actual parity-ground equation is

`Hf=mu f+c p_r`, `c=F_a(u)/D_r`,

where `F_a` is the actual boundary–arithmetic functional. Hence

`||Hf-mu f||²=|c|²||p_r||²=2|F_a(u)|²/D_r`,

`||Hf||²=mu²||f||²+2|F_a(u)|²/D_r`.

These are operator-domain identities. They require one application of `H`; no domain membership for `Hf` or existence of `H²f` is assumed. The positive denominator proves that the residual vanishes exactly when `F_a(u)=0`, equivalently exactly when the constrained state is an unrestricted eigenvector with eigenvalue `mu`.

### Actual variational comparison
Define the shifted full form

`B_lambda(u,v)=Q(u,v)-lambda<Ju,Jv>`.

The actual unrestricted Rayleigh floor gives `B_lambda(v,v)≥0` on the entire complete form domain. The exact compact Birman–Schwinger representation proves sesquilinearity and Hermitian symmetry. Thus the corpus's semidefinite Cauchy–Schwarz theorem applies without assuming positivity of the unshifted Weil form.

On a constrained ground, the ground diagonal is

`B_lambda(u,u)=(mu-lambda)||f||²`.

On the lifted parity pole, it is

`P_r=B_lambda(p_r,p_r)=Q(p_r)-2lambda D_r≥0`.

Representing the ground's complete form by its actual operator value gives, with the corpus's conjugate-linear-first convention,

`B_lambda(u,p_r)=2 conjugate(F_a(u))`.

The scalar shift disappears from this mixed pairing because the ground is orthogonal to both poles. Cauchy–Schwarz now yields the exact source bound

`4|F_a(u)|² ≤ (mu-lambda)||f||² P_r`.

If `F_a(u)≠0`, the left side is positive, so `lambda<mu`. In particular, equal floors force every constrained one-profile ground's source moment to vanish. At a hypothetical zero constrained ground, nonzero coupling forces a negative unrestricted floor; this is a consequence, not a contradiction.

For a pure-parity ground the already identified physical source kernel gives

`2F_a(u)=I_r=integral_[-a,a] K_(a,r)(x)f(x) dx`.

Therefore

`|I_r|² ≤ (mu-lambda)||f||² P_r`.

Both endpoint boundary terms and every prime power remain inside `K_(a,r)`. No separate absolute arithmetic estimate replaces that kernel.

Finally, scale an existing nonzero actual parity ground by the reciprocal of its physical norm. Linearity preserves its operator domain and forcing equation; quadratic homogeneity preserves its Rayleigh value. This gives a normalized actual witness satisfying the forcing equation, exact operator-norm identity and source-gap bound at every positive aperture, with no RH or source-sign premise.

### Exact obstruction and positive survivor
On two complex coordinates use the Hermitian form, in linear-first convention,

`B(x,y)=x_1 conjugate(y_2)+x_2 conjugate(y_1)`.

The subspace `x_2=0` has identically zero quadratic energy. Its normalized vector `(1,0)` has mixed pairing `1` with `(0,1)`, so its source coupling is nonzero. The full quadratic obeys

`Re B(x,x)≥-(|x_1|²+|x_2|²)`

because adding the mass gives `|x_1+x_2|²`. Equality is attained at `(1,-1)`, whose mass is `2` and energy `-2`. The corresponding swap operator has unrestricted floor `-1` and sends `(1,0)` to `(0,1)`.

With unit pole mass, `D=1/2` and `F=1/2`, the source-gap inequality reads `1≤1`. Thus the generic comparison cannot be improved solely from these two-dimensional data, and positive variance does not exclude zero constrained energy. This is a formal model obstruction; it does not describe the arithmetic operator or disprove RH. The positive survivor is the actual-source inequality and its exact variance and equality information.

## Remaining arithmetic obligation
Exclude the actual forced zero ground using additional control of the combined boundary–arithmetic moment, unrestricted spectral gap and signed pole energy. Assuming the unrestricted floor nonnegative would settle the desired comparison at that aperture, but no such assumption is supplied here. Boundary divergence and a fixed-aperture error bound alone do not settle these quantities.

## Validation
- Scratch `lake env lean /tmp/hgt-ground-variance.U8bjZ0/Variance.lean`: PASS.
- Named foreground audit `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundVariance`: PASS; the new leaf built in 9.1 seconds. No full or umbrella build.
- Scratch `Audit.lean`: all 15 public theorems have exactly `[propext, Classical.choice, Quot.sound]`. Actual mathlib `RiemannHypothesis` was printed and remains unproved.
- `python3 scripts/formal_tools.py lint`: PASS; existing large-file warnings remain. Logs: `/tmp/hgt-ground-variance.U8bjZ0/Audit.txt`, `Lint.txt`, and `Lint.err`.
- No numerical experiment, computational oracle, added axiom, or RH premise supplies these results.
