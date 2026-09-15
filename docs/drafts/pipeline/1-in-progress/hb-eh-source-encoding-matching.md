# Full canonical matching through the literal source encoding

Status: analytical factorization attack; Lean verification pending.

Frozen question: after discarding the Peierls testing rule, can an arbitrary
copy-dependent nonlinear map of the literal source carrier recover the
complete canonical temporal/metric/QNM action at every source amplitude?

Proposed statement:

`not exists R : XiZeroCopy -> HBXiPeierlsCarrier -> Complex,
 forall q a, R q (hbXiPeierlsPlusSource a q) = canonicalQNMValue q true true a`.

This tests the original encoding, not a chosen replacement observable.
DN35 only excludes readings made with the literal complementary probe.
The stronger question allows any scalar output map without continuity,
linearity, a vacuum condition, or a prescribed probe.

Attack: use an actual critical Xi copy with nonzero complete action from
DN35. The literal carrier is zero at that copy for every amplitude. The
complete action is quadratic in the original amplitude, so amplitudes zero
and one give distinct outputs from identical encoded data.

Positive target: classify precisely when two original amplitudes give the
same complete action, and retain an explicit physical replacement datum.
DN37's two coefficients `-mu*C*(mu-2)*M` and
`-mu*C*((mu-2)*X+Y)` determine the whole causal profile and its full QNM
integral. They come from the original source periods, not a fitted target.

Whole-route implication if proved: changing only the returned field or
output probe cannot repair the original carrier's loss of amplitude.
A successful replacement must change the source information retained by
the matching map. This does not establish its Hawking-clock extinction law.
