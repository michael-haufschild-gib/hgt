# Logarithmic inverse islands and finite joint monodromy

- **ID:** RH-XILIM-20261007
- **Stage:** 1-in-progress; exact conjectures and paper mechanism, audit pending
- **Parent:** `xi-marked-joint-monodromy.md`
- **Related:** `../2-fully-proven/xi-finite-cover-monodromy.md`
- **Verdict:** SURVIVES PRELIMINARY ATTACK; novelty not certified

## Exact competing claims

C1-log: For every real a and positive M,R there is a holomorphic map h on
D(0,M), taking values in Re(s)>R, such that
xi(h(w))*exp(-a*h(w))=exp(w) for every w in that disk.
There is no premise concerning zeros, RH, or critical values. Its derivative
identity makes h locally injective. These inverse islands are much stronger
than mere occurrence of every nonzero value far to the right.

C2-finite: For every finite set S of distinct integers >=2, write Gamma as
product_(n in S) F(a_n,b_n), mu for the actual marked-source monodromy in
the parent, and w:Gamma->Z^S for zero winding. For every finite quotient
q:Gamma->G, q(image mu)=q(w^(-1)(diagonal Z)). This is a profinite statement;
it does not assert equality of the discrete fundamental-group image.

Competing obstruction: logarithmic critical/asymptotic values may prevent
arbitrarily large inverse disks. If that happens, determine their exact
location and retained finite monodromy obstruction. Generic Schottky value
existence alone cannot decide this, and unrelated entire functions need not
have these islands. Even C2-finite would not supply a divisor-selection law
or prove RH.

## Analytic paper mechanism to audit

On Re(s)>1 choose an analytic logarithm L_a of d_a=xi*exp(-a*s), real on the
positive real ray. The logarithmic derivative is

L_a'(s)=1/s+1/(s-1)+(1/2)*psi(s/2)-(1/2)*log(pi)+zeta'(s)/zeta(s)-a.

For Re(z)>0, the convergent digamma difference series gives
Re psi(z)>=psi(Re z): termwise Re(1/(n+z))<=1/(n+Re z). The real digamma
tends to infinity. Absolute convergence of the von Mangoldt logarithmic
Dirichlet series bounds zeta'/zeta uniformly in Re(s)>=R and makes that
bound tend to zero as R tends to infinity. The two rational terms have
positive real part. Thus choose R_a with Re L_a'(s)>=1 on Re(s)>=R_a.
All identities and convergence domains must be checked in the corpus.

Integrating on the straight segment in the right half-plane gives
Re((L_a(z)-L_a(v))/(z-v))>=1, hence
|L_a(z)-L_a(v)|>=|z-v|. In particular L_a is injective and has no critical
point. For a disk centered at s with radius r<Re(s)-R_a, Rouche applied to
L_a(z)-L_a(s) and the constant target perturbation shows that its image
contains D(L_a(s),r). Injectivity and the inverse-function theorem make the
inverse holomorphic. No compact-surface uniformization or Koebe theorem is
needed for this step.

On every fixed vertical line Re(s)=K>1, Stirling's Gamma estimate and bounded
zeta give |d_a(K+it)|->0 as t->+infinity. Consequently Re L_a(K+it)->-infinity.
Fix R>=R_a. For all large t, the strictly increasing function
sigma |-> Re L_a(sigma+it) has a unique zero sigma(t)>R; it tends to infinity
as sigma->infinity by Re L_a'>=1. For every fixed K>=R, the vertical decay
implies sigma(t)>K eventually, so sigma(t)->infinity. The real implicit
function theorem makes sigma(t) continuously differentiable. For
Y(t)=Im L_a(sigma(t)+it), Cauchy--Riemann gives
Y'(t)=|L_a'|^2/Re L_a'>=1. Thus Y is increasing and unbounded. At the times
Y(t_k)=2*pi*k, the image contains disks centered at 2*pi*i*k with radii
approaching infinity, while source centers move arbitrarily far right.
Choose the initial half-plane boundary above the requested R, then invert
on D(2*pi*i*k,M) and translate its argument. Exponentiation gives C1-log.

[OPEN CORE] Corpus verification and dependency-closed analytic implementation:
digamma inequality/real divergence, uniform zeta logarithmic derivative,
vertical Xi decay, half-plane logarithm, and the inverse-island construction.
No new Lean is written for this card before that audit closes.

## Finite joint group mechanism to audit

Let K_n be the kernel of zero winding in the nth free group, embedded in
Gamma, and K their product. The ratio d_m/d_n=exp((log n-log m)*s) implies
zero-winding vectors of all actual source loops are diagonal; hence
image(mu) is contained in w^(-1)(diagonal Z).

A finite list of based loops from K_n lifts under exp to closed logarithmic
loops in C minus the odd multiples of pi*i. Their compact images fit in one
disk D(0,M), also containing a common logarithmic basepoint. Apply C1-log for
a=log n with R sufficiently large. On this whole disk, for m>n the other
marked values have modulus <1/2, and for m<n they have modulus >2, since
|d_m(h(w))|=exp(Re(w)+(log n-log m)*Re h(w)). The other marked functions are
nonzero exponentials on the whole disk and avoid -1 there, so their loop
images are nullhomotopic. The nth component realizes the selected loops.
Connecting the source basepoint conjugates this entire finite packet by one
element of Gamma.

For a fixed finite quotient G, choose a finite packet whose q-images generate
q(K_n). This subgroup is normal in G, so the common conjugation leaves it
unchanged. Thus q(image mu) contains q(K_n) for every n and hence q(K).
An actual simple Xi zero supplies a source meridian with zero-winding vector
(1,...,1). In Gamma/K=Z^S its image generates the diagonal. Together with
the upper inclusion, this proves C2-finite. The basepoint transport and the
normality argument must be made explicit; conjugators may vary with n and
with the chosen finite quotient, which is why discrete equality is not claimed.

The same islands at w=pi*i give isolated simple zeros of 1+d_n away from all
other marked divisors. Together with a simple Xi zero they show that the
parent divisor lattice is exactly diagonal Z in the a-coordinates plus all
of Z^S in the b-coordinates. This identifies C2-finite as the finite-quotient
version of the parent's C1, rather than an unrelated maximality claim.

## Audit started

Direct deep query: `xi logarithm inverse disk Stirling right half plane a
point simple univalent`, output `/tmp/rh-xi-log-islands-search-20261007.json`.
This card was created while the rational-factor final assembly was checking;
that predecessor remains the active code task. External exact ancestry and
hostile statement audit are pending. No scientific novelty claim yet.
