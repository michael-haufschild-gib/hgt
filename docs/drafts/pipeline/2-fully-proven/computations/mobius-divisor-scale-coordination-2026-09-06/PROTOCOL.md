# Frozen protocol: complete arithmetic dilation coordination

Frozen before execution. Numerical exploration only; placement in the computations archive
does not mean RH or the proposed inequalities are proved.

1. Compute literal `mu`, divisor counts, log factorial, and the exact finite source through
   `M<2^21`. Assemble the prime-power Chebyshev source independently and compare every endpoint.
2. Discovery exponents: 12, 14, 16. Validation exponents: 18, 20, withheld until discovery is read.
   For each exponent use `M=2^e+i*2^(e-6)`, `i=0..63`.
3. Sum all dilation contributions into groups `j=floor(log2(floor(M/d)))`. Zero-pad groups to
   dimension 22. Do not drop the high quotient groups or terminal clipped block.
4. Record normalized groups `G_j=sum C_d/M`, full sum, direct Chebyshev value, absolute channel
   mass, covariance matrix, covariance by group separation, and raw/centered second moments.
5. **C1:** adjacent groups account for at least 75% of the cancellation
   `trace(Cov)-1^T Cov 1`, in every discovery band. If total cancellation is not positive,
   C1 fails. No threshold or sample-selection adjustment after results.
6. Generate 512 controls by independently permuting the 64 endpoint labels in each group;
   fixed seed 20260906. Report controls descriptively, without a p-value or independence claim.
7. After discovery, freeze any proposed new mechanism separately before testing held-out data.
   A failure must retain its strongest exact positive survivor, if one can be proved. Existing
   finite sum rearrangements alone do not count as new mathematical knowledge.

Use Runpod, at most eight worker processes, one BLAS thread each, and a 120-second command cap.
Stop or reduce the numerical range if the cap is reached; do not silently change a conjecture.
Save machine-readable rows, source metadata, code hashes, and a compact report. Rerun any
conclusion-driving endpoint using a separate high-precision direct calculation.
