# H3/H4 validation supplement: actual fixed source

Implementation validation only; no new discovery search. Independently check the discovered true/true zero and rho+.001 through the corpus's ordinary fixed-rational-kernel defect integral: (w+1)M=2(86/625-D(w)). Derive its polynomial exactly from the inspected nonstationaryWeightStep, nonstationaryPolynomial and nonstationarySourceNumerator definitions. Evaluate x=u^4 and x=u^6 changes of variable at 50/100/160 digits (with 30 guard digits). Both retain every term and use absolutely convergent integrals. These substitutions address the endpoint singularity; they are not regulators deleting boundary work.

At both H4 zeros independently evaluate all four channels with the endpoint series at 190 digits; compare hypergeometric values at 190 digits. This validates whether the other-channel nonzero observations survive independent computation. No inference of full source/action identification or zeta-zero status.

At most 14 processes, library threads one, one pod. Maximum compute window 400 seconds plus cleanup; H3 and H4 together consumed 7.785 seconds, so the combined discovery/validation family remains below ten minutes even on timeout. Preserve completed rows. Source search/provenance inherited from H3/H4 plus inspected FixedSourcePolynomial, NonstationaryPolynomial and NonstationaryWeight. No Lean builds.
