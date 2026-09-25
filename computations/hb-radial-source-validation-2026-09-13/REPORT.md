# Independent original-source validation

All 20 validation cells completed without error on pod A. Guarded wall time 4.655 seconds; combined H3/H4/H5 wall time 12.440 seconds, far below the ten-minute family cap. Output downloaded, remote checksums verified, owned process group cleaned. No Lean build.

Twelve cells evaluate the corpus's fixed rational source defect by ordinary quadrature at the true/true radial zero and a nonzero rho+.001 anchor. They cross requested precisions 50/100/160 (plus 30 internal guard digits) with endpoint substitutions x=u^4 and x=u^6. Maximum absolute disagreements with the hypergeometric value of (w+1)M are 1.61e-81, 2.99e-131 and 1.32e-191, respectively. This uses the full exact polynomial generated from the inspected Lean recurrences, the retained constant 86/625, and the entire convergent defect integral.

Eight further cells evaluate all four radial channels at both H4 roots using independently coded endpoint series at 190 digits. Maximum absolute disagreement with the hypergeometric implementation is 4.06e-185. Every alternate channel remains nonzero with the magnitudes recorded in H4. The diagonal small residuals reflect root coordinates rounded to 160 digits, not a precision floor in the independently evaluated source.

Consequence: the two numerical blind spots are not artifacts of dropping the endpoint counterterm, mistaking the source rate for the reader frequency, or one hypergeometric implementation. They numerically refute individual-channel nonvanishing on the entire open critical strip. Both points are off-line spectral controls below the first cached zeta ordinate, not asserted zeta zeros. All-Xi survival, common-zero exclusion, complete-action identification, and extinction remain unresolved by these calculations.

This supplement validates an existing surprise; it is not a separate discovery claim. Reproduce with the recorded environment: python guard.py validate.py. Inputs, exact polynomial coefficients, source hashes, raw precision cells and the original remote checksum manifest are retained.
