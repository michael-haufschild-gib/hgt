# Frozen EDQ complete-column coherence diagnostic

This tests mechanisms for the unresolved signed finite-head bound. It is not
a replacement RH conjecture or a numerical proof. Inputs are the previously
archived complete kernel enclosures and full-flux values through N=512.
No new kernel scan, parameter fitting, or larger-cutoff sweep is authorized
by this protocol. All arithmetic and analysis run on the specified RunPod.

## Exact retained source

K(d,e)=sum_(j>=1)P_e(d*j)/(d*j)^2. Complete Möbius divisor inversion gives
sum_(d>=1)mu(d)K(d,e)=P_e(1). Thus define the complete row contribution

```
x_e(N)=-mu(e)*(P_e(1)-sum_(d<=N)mu(d)K(d,e)),
R(N)=sum_(e<=N)x_e(N), V(N)=sum_(e<=N)|x_e(N)|.
```

All numerator-tail and time terms are retained by this exact completion.
The baseline lower/upper kernel values bound each row before its absolute
value is taken. They are floating-point analytic enclosures, not certified
interval arithmetic. Use the predeclared 1e-8 sensitivity margin per row.

The zero Bernoulli frequency supplies the parameter-free mean profile

```
t_2(N)=6/pi^2-sum_(d<=N)mu(d)/d^2,
y_e(N)=pi^2/72 * mu(e)*e*t_2(N).
```

Indeed K's constant Bernoulli mean is -e*pi^2/(72*d^2). The residual retains
every nonzero frequency. No empirical coefficient is fitted.

## Frozen tests and why the outcome is unknown

Use every N in (32,48,64,96,128,192,256,384,512). Previous experiments measured
full flux signs, modulus ratios, and gcd-group variation; they did not
measure this complete-row variation or its Bernoulli-mean residual.
The new Lean result bounds completed coprime-column Euler errors, but does
not bound the finite heads subtracted here. It therefore predicts neither
of the following tests.

[BRIDGE mechanism A] Complete-column cancellation is already sufficient up
to the fixed factor four: V(N)<=4*R(N) at every frozen cutoff. A robust
violation directs the proof toward cancellation between different columns.

[BRIDGE mechanism B] The parameter-free Bernoulli mean explains the row
vector to 25% in absolute mass:
sum_(e<=N)|x_e(N)-y_e(N)|<=V(N)/4 at every frozen cutoff. A robust violation
requires retaining the oscillatory kernel in the missing arithmetic bound.

These finite tests do not decide any uniform subpower statement. A failure
rejects the stated finite mechanism, not EDQ or RH. Retain every case and
both outcomes without changing thresholds. Record positive and negative
row masses, absolute variation, complete flux, mean profile total, residual
mass, and all rows. No selected favorable subset is a result.

## Execution and controls

Eight independent workers, native numerical libraries limited to one thread.
Hard timeout120 seconds. Copy the frozen script and two baseline artifacts;
verify input SHA256 hashes remotely before execution. Controls: row sum
must overlap independently archived full flux at every cutoff; e=1 and
mu(e)=0 rows vanish exactly before the sensitivity margin; the e=2 row
must agree with -1/4+pi^2/32*sum_(odd d<=N)mu(d)/d^2. Download all results,
log, and output hashes; verify hashes locally; remove only this experiment's
remote files/directory. Numerical values are never Lean premises.
