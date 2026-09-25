# Retained harmonic coefficients and same-cutoff tail control


Write `J_q(N)=sum_(q|d,d<=N)mu(d)/d`. Exact finite divisor inversion gives
`K_r(N)=sum_(l<=N/r)mu(l)*J_(rl)(N)^2`. For squarefree q,
`J_q(N)=mu(q)/q*sum_(j<=N/q,gcd(j,q)=1)mu(j)/j`; nonsquarefree q contributes
zero. Taking absolute values outside that inversion gives
`sum_r |K_r|<=sum_q tau(q)*J_q^2`. The corpus's prime-supported expansion
preserves these exact coprime masks. Its logarithmic rates do not supply
the reciprocal-cutoff saving needed after multiplication by headMass(N).
In particular, the q=1 square remains the literal harmonic defect, so a
fixed-modulus rate cannot be promoted to the required all-cutoff power rate.

[BRIDGE candidate, not a replacement RH conjecture.] The complete harmonic
gcd family may provide a useful selector for the full source, beyond
minimizing its one scalar harmonic defect. The previous complete-source
measurements and the now-proved all-gcd head comparison motivate testing
this before building a tail comparison theorem. No such theorem is assumed.

Freeze four bands `[64,127]`, `[128,255]`, `[256,511]`, `[512,1023]`.
In each band choose the least minimizer of (S) `N*H(N)^2`, and independently
of (G) `headMass(N)*sum_r |K_r(N)|`. The parameter-free prediction is that
the G-selected cutoff has no greater complete raw residue energy than the
S-selected cutoff in each band. Compute complete energy intervals at all
selected cutoffs, retaining an analytic infinite-tail allowance at most
0.005. Compare intervals: separated reversal falsifies the prediction;
overlap is unresolved. Report every band and the full selection scan. Do
not change the selectors, add bands, fit constants or increase precision
after results. Also retain the literal head and later-tail energy intervals
to identify where a reversal occurs.

This asks whether a newly available finite arithmetic selector controls the
same cutoff's unobserved tail. It is not another power-of-two energy scan
or a numerical test of RH. A reversal directs proof work toward an explicit
tail observable in any selector; uniform improvement would support attacking
a comparison with the complete harmonic family. Either outcome is finite
guidance, not an asymptotic theorem. Run eight independent full-energy jobs
on the authorized RunPod under 120 seconds, with one native thread per
worker. Use exact bounded-residue tail inequalities and distinguish their
analytic error from floating-point sensitivity. No result enters Lean.

