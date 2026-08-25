Completed HRTV same-grade/canonical-radiation step.

Files:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullEinsteinGaugeFixedRadiationGram.lean
- formal/GaloisForLFunctions/RHTower.lean (new import)
- docs/reports/endpoints.md
- status prose refreshed in NonlinearChiralTeukolskyReturnProducer, SelfDualTeukolskyOpticalTransgression, TeukolskyMassMemoryDoublePole.

Paper result:
For seed grade s=rho/2, quadratic full Einstein source grades are 2s, s+conj(s), 2conj(s). Xi height is nonzero, so mixed/anti grades cannot equal 2s. Exact self-dual Einstein-AdS restriction identifies the unique ++/2s full source with self-dual Plebanski carrier. Gauge commutators die in adjoint Teukolsky pairing. Thus no non-self-dual coherent same-grade counterterm exists; mixed/anti magnitudes need not be evaluated.

Exact BM map:
T(omega,z)=Gamma(c)Gamma(-1/2)/(Gamma(a)Gamma(b)), with a=c-(c-a), b=c-(c-b).
At quadratic Hawking harmonic:
c=-rho-1, a=-(rho+4)/4, b=-(3rho+2)/4.
Nonzero Xi height excludes Gamma poles, so T != 0. Existing chiral Jost theorem gives G != 0.
Gauge-invariant KI fibre radiation map:
(d,m) -> (Gd,TGd,Gm,TGm) in EuclideanSpace C (Fin 4), ordered H+,B+,H-,B-.
It intertwines real BM angular scalar, direct/mixing channels are orthogonal,
||R(d,m)||^2=||R(d,0)||^2+||R(0,m)||^2,
and both full horizon radiation and normalizable AdS direct response are nonzero for nonzero seed regardless of mixing.

Verification:
- direct source Lean check passed.
- targeted module build passed.
- all 22 new public lemmas/theorems have only [propext, Classical.choice, Quot.sound].
- formal lint has only pre-existing unreachable-module errors; new module is umbrella-reachable.
- custom corpus research finds new declarations.
- /tmp scratch removed.
No git touched.

Remaining RH-bearing physical question: whether nonlinear boundary evolution imposes zero orthogonal-helicity flux. Source cancellation and fibrewise radiation Gram compatibility are no longer open. Global discrete+continuum map is densely-defined fibrewise via KI spectral resolution; no uniform transfer bound was claimed.