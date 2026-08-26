Mission: derive source-faithful gauge-fixed Einstein–Teukolsky causal QNM cokernel on Birmingham–Mokhtari modes.

New Lean module:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMGaugeFixedCausalQNMCokernel.lean
- imported by formal/GaloisForLFunctions/RHTower.lean
No docs, route ledgers, endpoints, or git touched.

Exact derivation:
1. For causal seeds p_n and m_k, multiplication shifts the quadratic response frequencies. Both cascade denominators equal the direct cubic denominator:
   ((omega-omega_p)-Omega_pm) = omega-Omega_ppm,
   ((omega-omega_m)-Omega_pp) = omega-Omega_ppm.
2. Therefore complete causal ++- convolution (mixed response + second-harmonic response + direct Einstein third jet) equals I/(omega-Omega_ppm) times one total target-shifted cubic Schur source. No individual AIME/direct/second-harmonic decomposition remains.
3. At negative BM target sigma_N^-, the detuning is
   sigma_N^- - Omega_ppm = -2 chi + I(4n+2k-2N+3).
   On every Xi fibre Re chi != 0, hence this factor never vanishes.
4. Full physical BM boundary Jost derivative at sigma_N^- is already known nonzero. Assuming only regularity of the complete convolved angular numerator at the target (no internal intermediate-response pole collision), the exact Laurent residue is
   I * Sigma_total(sigma_N^-) /
   ((sigma_N^- - Omega_ppm) * J'_-(sigma_N^-)).
   The inverse-Laplace QNM coefficient is
   Sigma_total / ((sigma_N^- - Omega_ppm) * J'_-).
5. Formal zero-locus theorem: genuine QNM residue vanishes iff the total target-shifted angular cokernel Schur section vanishes. Temporal mismatch and radial pole normalization cannot create or erase incidence.

Hostile correction:
- Einstein action cyclicity gives a symmetric complex-bilinear Green/Hertz pairing, not a Hermitian positive norm. It cannot derive the previous hreciprocity equality ell(B p u)=normSq(optical projection).
- BM 2006 itself uses Kodama–Ishibashi gauge-invariant master fields, not a nonlinear Teukolsky/Hertz construction. Actual angular functional must be constructed by Teukolsky–Wald adjoint reconstruction plus full gauge/horizon/AdS boundary terms.
- Correct angular object is the total adjoint period
  1/2 delta^3 S_gf[h_target^dagger,h_a,h_b],
  including boundary counterterms. On a theta cusp it is a renormalized differential Eisenstein triple period, not an L2 Gram.
- Fixed-mode total angular period can be dark; cyclicity alone gives no nonvanishing or sign. Full angular-family completeness may guarantee some bright channel but does not select the divisor channel.
- Remaining hard core is explicit evaluation/nonvanishing of this total renormalized gauge-fixed angular period and proof of regularity/no internal pole collision. This is strictly narrower than prior hreciprocity.

Validation:
- Target module compiles.
- All 12 new theorems axiom-audited: only propext, Classical.choice, Quot.sound.
- Custom formal_tools research indexes new declarations.
- Targeted forbidden-token scan clean.
- Scratch and temporary olean removed.
- Global lint not rerun because same session already established only pre-existing unrelated unreachable-module failures.