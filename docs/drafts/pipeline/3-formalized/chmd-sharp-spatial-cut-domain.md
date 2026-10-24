# Sharp spatial cuts in the complete CHMD graph

- **ID:** chmd-sharp-spatial-cut-domain
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Statement:** For every real cut location, multiplying the source coordinate by either half-line indicator preserves the full maximal CHMD graph. The resulting linear maps are bounded uniformly in the cut location. Two cuts give bounded interval localization without a transition collar.

## Route and contribution

The CHMD route still requires complete odd theta–Doob positivity. The open
arithmetic inputs are reflected-prime collar payment, the primitive
half-Rayleigh bound and the oneL-defect payment. The supported-domain
theorem identifies graph vectors already supported in an aperture; the
present theorem constructs such vectors by sharp localization of any
maximal state. It does not assert positivity of their signed energies.

## Dependency-closed paper proof

Write `v` for the source coordinate, `F=Theta*v`, `mu=Theta*cosh(x/2) dx`,
and `E_arch(v)` for the literal archimedean Doob edge energy. The source
graph norm squared is `||v||_mu^2+E_arch(v)+E_prime(v)`. All quantities
refer to the complete measures, including every prime-power line.

1. **Physical L2 admission.** The established bounded map `thetaToVolume`
   sends every mass-L2 source to `F` in ordinary L2. Let its norm be `T`.

2. **The actual boundary kernel.** For a cut at `c`, write
   `F_-(t)=F(c-t)` and `F_+(s)=F(c+s)` on the positive half-line. The
   actual crossing term is

   ```
   C_c(v) = integral_(s,t>0) omega(s+t) F_-(t) F_+(s) ds dt.
   ```

   Here `omega=archLevyDensity=ccmGammaTranslationDensity`; equality
   follows from their literal definitions. The existing
   `integrable_ccmGammaBoundary_pair` proves absolute integrability for
   arbitrary L2 inputs. Translation, reflection and the shear
   `(h,x) -> (c-x,x+h-c)` have Jacobian of absolute value one, so this is
   precisely the crossing integral in the original edge coordinates.
   The established boundary-operator norm at most `2*pi` gives
   `|C_c(v)| <= 2*pi*||F_-||*||F_+|| <= pi*||F||^2`.

3. **Admission precedes the identity.** Let `v_-` and `v_+` be the two
   half-line restrictions. Pointwise, away from the null boundary,

   ```
   |Delta v_-|^2 + |Delta v_+|^2
     = |Delta v|^2 + 2*1_cross*v(left)*v(right).
   ```

   The original square is integrable and step 2 proves absolute
   integrability of the added term after multiplication by the literal
   archimedean weight. Each new nonnegative square is therefore
   integrable. This proves actual archimedean graph admission before
   integrating the equality, avoiding any conditional use of the energy
   formula. Integration gives
   `E_arch(v_-)+E_arch(v_+)=E_arch(v)+2*C_c(v)` and hence
   `E_arch(v_-) <= E_arch(v)+2*pi*||F||^2`.

4. **All prime edges remain admitted.** Both restrictions belong to mass
   L2. `memLp_allPrime_difference` admits their full prime differences.
   If `P=||primeDifference||`, then
   `E_prime(v_-) <= P^2*||v||_mu^2`. There is no truncated prime sum or
   assumed arithmetic sampling estimate here.

5. **Uniform full-graph bound.** Combining the preceding estimates gives

   ```
   ||cut_c p||_graph^2
     <= ||p||_graph^2 + (2*pi*T^2+P^2)*||p.fst||_mu^2
     <= (1+2*pi*T^2+P^2)*||p||_graph^2.
   ```

   Source injectivity identifies the constructed graph vector uniquely.
   It also proves linearity and the complementary-cut identity. The same
   estimate holds for the other half-line, uniformly in `c`. Composing
   two cuts gives interval localization; the supported maximal-domain
   theorem then places a symmetric interval restriction in its exact
   aperture completion.

Boundary point values do not matter: mass measure is equivalent to
Lebesgue measure and both endpoint maps preserve null sets.

## Corpus inputs inspected

- `CHMDDoobSourceGraph`: literal measures, endpoint nonsingularity,
  complete maximal graph and source injectivity.
- `CHMDBoundedPrimeGenerator`: bounded literal `primeDifference` on all
  mass L2; prime graph admission has no added premise.
- `CHMDHarmonicGroundPotentialAndMaximalDomainPrimeShiftForm`: maximal
  prime endpoint integrability and stationary/full-form dictionary.
- `CCMRestrictedWeilGammaBoundaryPairing`: actual Carleman domination,
  bounded boundary operator and absolute cross-boundary integrability.
- `CHMDSupportedApertureDomain`: exact supported-domain identification,
  directly checked in Lean.

## Gates

- [x] Complete paper proof, including pre-identity domain admission.
- [x] Exact Lean transport from half-line L2 to literal edge measure.
- [x] Uniform graph bound and interval construction in Lean.
- [x] Candidate and final repository leaf checks.
- [x] Axiom audit and umbrella wiring.
- [x] Temporary-file cleanup.

No external novelty claim, numerical experiment or RH sign is asserted.

## Formalization state

`formal/GaloisForLFunctions/RHTower/CHMDSharpSpatialCut.lean` constructs
the literal Gamma crossing term, transports absolute boundary
integrability to the original edge coordinates, and proves
`memLp_difference_indicator_Iio` for every actual maximal graph vector.
It also proves `exists_uniform_sharpLowerGraph_bound`,
`exists_uniform_sharpIntervalGraph_bound` and
`sharpIntervalGraph_mem_apertureGraphCompletion`.

All four principal declarations were audited with `#print axioms`:
only `propext`, `Classical.choice`, `Quot.sound`. The final actual-leaf
check passed, exit 0, no diagnostics:

```
lake --old env lean GaloisForLFunctions/RHTower/CHMDSharpSpatialCut.lean
```

The umbrella imports the finished leaf. No umbrella build was run.

The initial API probe confirmed the required product/shear
measure-preserving maps, real-to-complex L2 admission and real-part
integrability. No missing boundary estimate was added as a premise.

An equivalent proof of the uniform bound avoids explicit kernel-norm
bookkeeping. Sharp restriction is linear; its graph is closed because
the source projection is continuous and injective and ordinary L2
restriction is continuous. Hence the zero cut is bounded on the complete
stationary volume graph. `volumeGraphTranslate` is an isometry and
conjugates every cut to the zero cut, giving one common stationary bound.
The map from the full CHMD graph to its physical stationary graph is
bounded by the same closed-graph argument. The inverse `fullGroundEquiv`
controls the original graph norm by source norm plus physical stationary
graph norm. This proves the asserted uniform full-graph bound without
using an aperture-dependent equivalence. This is the proof used in the
checked Lean module.
