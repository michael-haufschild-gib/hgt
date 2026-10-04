# PM: compact closure of the critical normalized band profiles

- **ID:** pm-compact-normalized-profile-closure
- **Stage:** 5-failed
- **Type:** FALSIFIED, with audited positive survivor
- **Source:** actual natural denominator band, exact Mellin/logarithmic carriers.
- **Statement falsified:** for some positive damping, a tail of the critical normalized complete bands lies in a relatively compact L2 family.

## Exact obstruction

Total boundedness would make the actual moving phase pairing tend uniformly to zero on the proposed profile family. It also supplies a global norm bound, after the compact finite heads are included. The literal tested Abel limit is then zero. The complete cleared continuation, instantiated at an unconditional positive Hardy critical zero, instead has a strictly positive residue pairing. No simplicity assumption is used. This contradiction retains all coefficients and all mixed terms.

## Strongest positive survivor

For every epsilon>0, one c>0 works for every totally bounded profile set K and every tail start B: some X>=max(1,B) has distance at least c from every member of K. This holds in both the critical-frequency and the original logarithmic physical carriers. It follows from the failure of one finite-cover radius for the full image and total boundedness of every finite cutoff head, then exact unitary transport.

The new information is a common energy-scale obstruction to every finite or compact family of normalized profiles, beyond the earlier failure of one fixed limit. A successful upper estimate must admit noncompact motion or a weaker damping margin. This does not falsify the natural-cutoff energy conjecture or RH, and it does not prove unbounded norm.

## Paper and Lean audit

Dependency-closed proof and full audit: [noncompact complete-band energy](../3-formalized/pm-ramanujan-band-noncompact-energy.md). Exact exports are `exists_uniform_pmRamanujanBandCompact_separation` and `exists_uniform_pmRamanujanBandPhysicalCompact_separation` in `PMRamanujanBandNoncompactEnergy.lean`. All nine leaf exports passed the targeted old-mode build, mandatory actual-file `lake env lean`, and standard-axiom queries. Umbrella wired once. Global lint has thirteen unrelated unreachable leaves, none from this work. No full or umbrella build, heartbeat increase, numerical experiment or added axiom.

## Surviving hard target

Bound the complete signed natural-cutoff covariance, equivalently the full weighted critical-line moment of the actual band Mellin symbol, with a positive damping margin. Pointwise limits, finite covers, separate zeta/mollifier moment bounds and completed prime supports do not supply that estimate.
