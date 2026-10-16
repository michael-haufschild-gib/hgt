# HF whole-source native generator realization

Completed 2026-10-17. New modules:
- formal/GaloisForLFunctions/RHTower/PaperThetaMomentSeparation.lean
- formal/GaloisForLFunctions/RHTower/PaperThetaContourGenerator.lean
- formal/GaloisForLFunctions/RHTower/PaperThetaWholeMeyerGenerator.lean

Closed HF's explicit whole-range generator-intertwining gap for the existing fixed-Gaussian faithful native map P of original strong Meyer cohomology Q. For A = deningerMeyerCenteredCohomologyGenerator and R = nativeCompactResolvent at i, proved unconditionally R(P((A-i)q)) = Pq and thetaSpatialAction(Pq) = P(Aq), for every q. Constructed nativeMeyerDifferentialRealization : Q -> ThetaNativeDomain. The actual compact Green operator preserves the whole original-source image and agrees with the unique original cohomology solution for every forcing (nativeMeyerCompactResolvent_source). Every finite scalar-shift word is transported exactly and retains BV admission/full signed Weil expression. Closed capstone: nativeMeyer_whole_differential_realization.

Mechanism: for p(s)=-i(s-1/2), B_F the original Xi divided-difference contour and a_F=integral F/xi, exact commutator B_((p-i)F)(u)=(p(u)-i)B_F(u)+i xi(u)a_F. Native moments identify the cut trace; the Green moment law cancels it. Real theta moments separate bounded continuous profiles by positive density and L1 Fourier uniqueness. Thus R f_((p-i)F)=f_F. Pass bounded R through both source-admitted Gaussian block series and the genuine quotient; this avoids unjustified termwise differentiation of BV contour synthesis. Original causal division at s=-1/2 supplies unconditional source surjectivity for A-i.

All three direct leaf audits passed via lake --old env lean -j 1, without warnings or raised limits. Nine transitive axiom checks, including capstone, domain construction, word identity and full Weil identity, reported only propext, Classical.choice, Quot.sound. Required missing pre-existing dependency artifacts were restored; no dependency source changes/full builds. All three new imports wired into RHTower.lean. Formal indexes refreshed. lint --check-generated ran; only errors were unrelated concurrently added unwired modules (details on card), no proof debt.

Paper proof, conjecture ledger, limits, audit: docs/drafts/pipeline/3-formalized/hf-structural-obstruction-removal-2026-10-16.md. Prior candidates: Paugam skew trace already bridged by corpus; original-source upper/lower spectral splitting remains open, not retired.

Do not infer Gaussian removal in BV, source/native topology identification, positivity, RH, or arbitrary infinite-packet interpolation. No external novelty audit/claim. User declared docs/reports/rh-current-frontier-map.md read-only during this task; this task's earlier HF/RN edits were exactly reverted, preserving existing changes. Do not edit that map for this task.
