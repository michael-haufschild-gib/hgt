# SQB: complete exponential resummation and its native mean obstruction

RH remains unproved. This audits one complete infinite quarter-lattice source,
not every possible resummation. The frontier map is read-only.

## Exact source

For each actual Xi copy rho, put s=rho/2+2, so 2<Re(s)<5/2. In the original
upper half-plane, let y_v(z)=Im(M_v z), with v ranging over the complete
projective coprime rows. Define

    h_s(y) = y^s exp(−y),
    P_s(z) = sum_v h_s(y_v(z)).

This is the literal modular periodization with the original translation
window. No row, Weyl term, or Fourier mode is removed. Its exact expansion is

    P_s(z) = sum_(n>=0) [ (−1)^n / (n! Lambda(2s+2n)) ] E_complete(s+n,z).

The completed fields have exponent s+n and angular parameter s+n−1/2.
They form the quarter-lattice subsequence j=8+4n and all have scalar entire
target mu=F((rho/2)(1−rho/2)). Their completion denominators are nonzero in
the original absolute-convergence half-plane.

## Dependency-closed proof

1. At fixed z, every row height is at most H=max(Im(z),1/Im(z)). The absolute
   Taylor double sum is bounded by
   (H^n/n!) y_v(z)^Re(s). Both factors are summable. Interchanging the two
   complete sums therefore proves the expansion in the original coordinates.
   The existing exact completed-power periodization fixes every coefficient.

2. For 2<=Re(s)<=3, the damped profile satisfies |h_s(y)|<=y^2 and
   |h_s(y)|<=6 for y>0. Separate only the identity row in the estimate.
   The remaining quadratic row mass is bounded on Im(z)>=1/2: its exact
   completed Eisenstein expression is

       [Lambda(3) y^(−1) + full_tail(3/2,z)] / Lambda(4).

   The original tail bound and nonzero Lambda(4) give a uniform bound.
   The native modular cell has Im(z)>=1/2 and finite hyperbolic volume.
   Measurability and the resulting bound admit the complete source in native L2.

3. The full height seed is integrable on the modular strip. Apply original
   half-row unfolding both to h_s and to |h_s|; the latter proves summability
   of the row integral norms, which justifies exchanging integration with the
   complete source sum. Strip coordinates give

       integral_fd P_s dmu = integral_0^infinity y^(s−2) exp(−y) dy
                          = Gamma(s−1) != 0.

   Thus the actual L2 source vector is nonzero. No positivity assumption on
   the complex source is used.

4. The literal native constant vector c=1 is approximated by the original
   smooth modular cutoffs. Their values converge to c in native norm; their
   full Laplacians are the scaled second cutoff derivatives and converge to
   zero in that norm. Passing through the native bounded inverse establishes
   A c=c in the actual energy graph. Functional calculus gives C c=c/3 because
   F(0)=1. The actual covariance range then puts c in the entire graph with
   T c=c. These are constructed graph identities, not spectral assumptions.

5. Self-adjointness of C and pairing with c give, for every native vector v,

       integral C v = (integral v)/3,
       integral [v−(2+mu) C v] = (1−mu)(integral v)/3.

   An actual Xi target cannot equal one. Otherwise F(0)=mu and the audited
   real-preimage classifier would imply 0=1/4+Im(rho)^2/4, a contradiction.
   The complete source residual G=P_s−(2+mu) C P_s consequently has nonzero
   mean (1−mu) Gamma(s−1)/3 and is nonzero.

6. C P_s is nonzero by injectivity and belongs to the actual entire graph.
   Its full operator residual is exactly G:

       T(C P_s)−mu C P_s = G != 0.

   Its normalized residual is strictly positive. The original admitted vector
   P_s itself cannot be a T-eigenvector at mu either, regardless of whether it
   belongs to the entire graph: the bounded inverse identity would force G=0.

## Positive survivor and exact boundary

This constructs a nonzero admitted complete infinite packet beyond the finite
packet obstruction. Local absolute resummation is therefore a substantive
change of convergence procedure; its operator action still requires a proof.

The native mean gives the quantitative residual bound

    |1−mu| |Gamma(s−1)| <= 3 ||c|| ||G||.

For every native vector, define Qv=<c,v>/<c,c> c and v0=v−Qv. Then v0 has
zero original mean, C v0=(C v)0, and the complete residual separates exactly:

    v−(2+mu)Cv = [v0−(2+mu)Cv0] + ((1−mu)/3) Qv.

These positive statements are formalized. They identify the surviving
centered occurrence equation without asserting that its source is nonzero
or that its residual vanishes. No infinite termwise operator interchange,
entire-domain admission of P_s, or unconditional RH conclusion is obtained.

## Lean audit

- `SelbergResummedSource.lean`: 42 public declarations; complete resummation,
  native admission, exact Gamma mean, and nonzero actual Xi vector.
- `SelbergNativeConstantMode.lean`: 30 public declarations; original constant
  energy/entire graph actions, mean residual identity, norm bound and exact centering.
- `SelbergResummedOccurrenceAudit.lean`: 13 public declarations; unconditional
  full-Xi source exclusion, actual domain source, positive normalized residual,
  and retained centered decomposition.
- Scratch checks used `lake env lean`. All three final module builds passed;
  every final module was the sole pending build target. Required stale dependency
  chains were refreshed one module at a time; no umbrella or full build ran.
- An initial dependency build launched concurrent Lean processes and was stopped.
  Its child processes were confirmed gone. The remaining dependency and final
  audits ran serially. One axiom check started before its imported leaf finished,
  failed on the missing olean, and was rerun after the completed build.
- All 85 public declarations were checked with `#print axioms` in a scratch file.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur; no added axioms,
  proof holes, unsafe declarations, or numerical proof certificates were introduced.
- All 85 public declarations appear exactly once in the corpus index. All three
  modules are wired once into the RHTower umbrella. Formal lint passed; existing
  large-file warnings remain. No numerical experiments were performed.

Detailed verification logs: `/tmp/sqb24_serial_audit.log`,
`/tmp/sqb24_occurrence_build.log`, `/tmp/sqb24_axioms.log`,
`/tmp/sqb24_index.log`, and `/tmp/sqb24_lint.log`.

