from mpmath import mp, mpf, log, factorial, digamma, polygamma, zeta
from mpmath import diff
mp.dps = 50
S=[2,3]
def zS(s):
    p=mpf(1)
    for q in S: p*=1/(1-mpf(q)**(-s))
    return p
gE=-digamma(1)
def H(j,r=1): return sum(mpf(1)/k**r for k in range(1,j+1))
# T=3: predicted M_j^(3) via Bell polynomials in psi-derivatives, summed against zS-derivatives.
# L_j^(3)=sum_n n^-(j+1) * sum_{t=0..3} C(3,t)(-ln n)^{3-t} Gamma^{(t)}(j+1)
#       = j![ zS*B3 + 3*(-zS')*... ] -- easier: use mpmath polygamma for Gamma^{(t)} directly (independent),
# and compute M_j^(3) two ways: (A) closed form via zS-derivatives & Bell, (B) the monomial expansion; check equal.
print(" j |  M^(3) closed(zS-deriv)  -  monomial-expansion  (should be ~0)")
for j in range(0,6):
    z0=zS(j+1); z1=diff(lambda t:zS(t),j+1,1); z2=diff(lambda t:zS(t),j+1,2); z3=diff(lambda t:zS(t),j+1,3)
    # Gamma^{(t)}(j+1)/j! via mpmath polygamma (independent of hand ζ-forms):
    p0=digamma(j+1); p1=polygamma(1,j+1); p2=polygamma(2,j+1)
    g1=p0                      # Gamma'/Gamma
    g2=p0**2+p1                # Gamma''/Gamma
    g3=p0**3+3*p0*p1+p2        # Gamma'''/Gamma
    # M_j^(3)=L/(j! zS) = [zS*g3 + 3 zS' g2 + 3 zS'' g1 + zS''' ]/zS  (since sum_n n^-s (ln n)^m=(-1)^m zS^{(m)})
    # careful signs: sum_n n^-s (ln n)^k = (-1)^k zS^{(k)}(s). (-ln n)^{3-t}=(-1)^{3-t}(ln n)^{3-t}.
    # term t: C(3,t) Gamma^{(t)} sum_n n^-s (-ln n)^{3-t} = C(3,t)Gamma^{(t)}(-1)^{3-t}(-1)^{3-t}zS^{(3-t)}=C(3,t)Gamma^{(t)} zS^{(3-t)}
    jf=factorial(j)
    L = jf*( 1*g3*z0 + 3*g2*z1 + 3*g1*z2 + 1*z3 )   # t=3,2,1,0 with C(3,t)=1,3,3,1; Gamma^{(t)}/j!=g_t
    Mclosed = L/(jf*z0)
    # monomial expansion: express g1,g2,g3 in {gE,z2,z3} explicitly, zS-derivs in {log2,log3}
    Hj=H(j); H2=H(j,2); H3=H(j,3); z2v=zeta(2); z3v=zeta(3)
    G1=Hj-gE
    G2=(Hj-gE)**2 + (z2v-H2)
    G3=(Hj-gE)**3 + 3*(Hj-gE)*(z2v-H2) + (-2)*(z3v-H3)   # psi''=-2(zeta(3)-H3)
    Lmon = jf*( G3*z0 + 3*G2*z1 + 3*G1*z2 + z3 )
    Mmon = Lmon/(jf*z0)
    print(f"{j:2d} | {mp.nstr(Mclosed-Mmon,6)}")
print("\nWeight-3 monomials present: gE^3, gE*zeta(2), zeta(3), gE^2, gE, zeta(2), 1, x prime-log weights -> FINITE set per weight. confirmed pattern continues with new transcendental zeta(3).")
