# Reflected marked prime root averages

- **ID:** goldbach-reflected-marked-root-average
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Goldbach programme](goldbach-unconditional-2026-10-23.md), Cycle 9.
- **Statement:** Transfer a varying-target marked Type II energy to an
  actual prime sum, retaining a polynomial root average and maximal endpoints.

## Exact candidate R1

Let T tend to infinity through even integers, L=log T. For fixed K≥1,
use the disjoint punctured prime pools and bounded weight W_T from the
[Type I paper proof](../2-fully-proven/goldbach-retained-modulus-type-i.md).
Write P_T for the product of all primes in those pools. For T/4≤t≤T/2,
put

    S_(T,q)(t)=Σ_(T/4<p≤t, p prime, q|T−p)
                 log p · μ(T−p) W_T(T−p).

Candidate: for each fixed A>0, some fixed K gives

    Σ_(q≤T^(51/100), q odd squarefree, (q,T P_T)=1)
       max_(T/4≤t≤T/2)|S_(T,q)(t)| ≪_A T L^−A.

The order is A, then K, then T→∞. No growing number of pools is
allowed without a separate proof. The restriction on q is explicit;
R1 does not include the shared-marking-prime Type II case. Since W_T
vanishes on large primes, R1 itself does not prove Goldbach.

## Inputs to check, not assumptions to insert in Lean

1. Guo's varying-target cofactor energy, with the precise LWW moment
   proof behind H2′ and the target-dependent character average checked.
2. The external seven-eighths zero-free theorem and its actual proof
   closure. The endpoint and comparator mapping were located on the
   [source-audit card](goldbach-varying-shift-source-audit.md); they are
   not yet a locally verified dependency.
3. The Type II length range after choosing Vaughan cutoffs
   U=V=T^(1/10), and the coefficient class c_V(n). The source's
   displayed choice U=V=x^(1/5) must not be silently changed.
4. Uniformity in polylogarithmic Mellin frequencies, including any
   parameter order in the varying-target major-arc argument.
5. Exact square-divisibility and prime-power errors after summing q.

The reflected Type I estimate is already proved on paper; it has no
extra analytic premise. The common-cofactor energy transfer and its
coarse divisor-weighted moment are on the
[energy card](goldbach-common-cofactor-energy.md).

## Maximal endpoints with polylogarithmic frequencies: paper proof

This layer is a harmonic-analysis inequality, not a prime-cancellation
input. Let a_n be any finite complex sequence supported in
T/8≤n≤3T/4, with |a_n|≤B. For a collection Q of positive moduli
at most Q≤T, put

    F_q(v)=Σ_(n, q|T−n) a_n (n/T)^(iv),
    G(v)=Σ_(q∈Q)|F_q(v)|,  H_Q=Σ_(q≤Q)1/q.

For 0<δ<1/100 and V≥1,

    Σ_(q∈Q) max_(T/4≤t≤T/2)|Σ_(T/4<n≤t, q|T−n)a_n|
      ≪ log(2/δ) sup_(|v|≤V)G(v)
        + B[δT H_Q+Q+(T H_Q+Q)/(δV)].                         (M)

The implicit constant is absolute. Here is the complete cutoff proof.
In x=log(n/T), fix a smooth compact cutoff equal to one on
[log(1/8),log(3/4)]. Multiply it by a smooth step at s=log(t/T),
with transition width δ. Call the result ψ_s. Uniformly in s,

    ||ψ_s||_1≪1,  ||ψ_s'||_1≪1,  ||ψ_s''||_1≪δ^−1.

Thus its Fourier transform has the common envelope

    |hat ψ_s(v)|≪b_δ(v):=min(1,1/|v|,1/(δv²)),

with value one at v=0. Its integral is O(log(2/δ)), and its
integral outside |v|≤V is O(1/(δV)). Fourier inversion is valid
because these transforms are integrable. Subtract the step at
log(1/4) from the step at s. On the coefficient support this differs
from the required interval indicator only on two physical intervals
of length O(δT). In each root progression their total count is
O(δT/q+1), including endpoints. Summing gives the first error in (M).

Apply the uniform Fourier envelope after taking each modulus's own
supremum. On |v|≤V use sup G. For the tail use the original sequence:

    G(v)≤Σ_qΣ_(n,q|T−n)|a_n|≪B(T H_Q+Q).

This proves (M), with the full q average paid and no frequency
depending on a modulus-selected endpoint. In particular, for the
prime coefficients B=O_K(L), Q≤T^θ with fixed θ<1, one may take

    δ=L^(−A−4),  V=L^(2A+9).

The errors in (M) are O_(A,K,θ)(T L^(−A−2)) plus O_K(Q L).
A uniform twisted root estimate of precision A+2 therefore implies
the desired maximal estimate. Use a fixed smooth prime weight equal
to one on [T/4,T/2] and supported in (T/8,3T/4) to fit this formulation.

This resolves the endpoint frequency issue at the actual prime-sum
level. It does not assert the missing bound for G(v). In particular,
it neither removes μ nor replaces its Type II energy by an absolute
divisor estimate.

## Fixed-half-plane shortcut for the major arcs

Guo's remark "A separate contour estimate" already records the
relevant strong-input prime-polynomial bound. It is distinct from
the weaker zero-free rectangle used in the main energy theorem.
The following deduction spells out its application; it is not a
novelty claim or a verified local Lean input.

Suppose the stated fixed seven-eighths zero-free theorem is supplied
by its actual external proof. For a nonprincipal character ξ modulo
q≤T², the line Re(s)=15/16 stays a fixed distance from every zero.
The partial-fraction formula gives L'/L≪log²(q(|t|+3)). Shift
truncated Perron for the twisted logarithmic derivative to that line,
using height y² around the twist. Uniformly for |v|≤T^C and
exp(L^(1/10))≤y≤T^O(1), this gives

    |Σ_(n≤y)Λ(n)ξ(n)n^(iv)|≪_C y^(15/16)L^3.                 (P*)

The two horizontal sides and Perron error are smaller; prime powers
cost O(y^(1/2)log² y). Thus the same saving holds for prime sums
after partial summation. The pole of a principal character is the
reason it is excluded, and it will be treated separately below.

Write the normalized label polynomial as

    B_ξ(t)=(Y∏V_i)^−1 Σ_(a=p_1...p_K)
               η(a/Y)e(λa/Y)ξ(a)a^(it),  |λ|≤L^A_0.

Fix a'=p_2...p_K and sum p_1 first. Its nonempty interval lies
inside [Y/a',4Y/a'] and above exp(L^a_1). The smooth amplitude has
variation O(1+|λ|). Apply (P*) with the Mellin phase retained in the
twisted prime sum. After division by Y, the bound is

    L^O(1) exp(−L^a_1/16) Σ_(a')1/a'.

The last reciprocal sum is at most ∏_(i≥2)V_i. Hence, for every
fixed D, uniformly in nonprincipal ξ,

    |B_ξ(t)|≪_(D,K) L^−D.                                   (B*)

For the reflected major-arc energy, characters have the form
ξ_b=χψ_2 and ξ=χψ, with χ modulo T inflated to modulus kT.
The fixed twists ψ,ψ_2 are modulo kT, where k≤L^A_0; only
ψ_2/ψ is induced from modulus k. This distinction is essential
when k and T share factors. On ξ_b nonprincipal, use (B*) and the character–Mellin
mean square for MN. The product polynomial has length comparable
to T and squared coefficient norm O(L^(2C+3)/T). Orthogonality
modulo T, with O(1) product indices in each residue class, gives

    (1/φ(T)) Σ_χ ∫_(|t|≤L^B_1)|M_ξ(t)N_ξ(t)|²dt
      ≪ L^(B_1+2C+O(1))/T.

Thus this part has every prescribed logarithmic saving after (B*).

There is at most one χ for which ξ_b is principal: inflation from
the unit group modulo T is injective. On the unit support, then ξ
agrees with ψψ_2^−1, induced from the small modulus k. Remove the
target-unit indicator at cost O(L/Z) from the sifted Möbius
polynomial M. The classical maximal Möbius BV input already used
in the Type I proof gives character cancellation for k≤L^A_0:
expand a character over its reduced residue classes and absorb the
factor φ(k) into the requested precision. Partial summation costs
only a fixed logarithmic power for the polylogarithmic twists here.
The smooth-number convolution and Rankin tail in LWW Proposition
2.2 then give |M_ξ(t)|≪L^−D, for every fixed D and M≥T^ν,
ν>0 fixed. Thus its stronger polynomial-frequency input is not
needed for this application. The ordinary mean square for the remaining
N polynomial is O(L^(2C)); B is bounded. After division by φ(T),
this final character also contributes O(T^−1 L^−A).

This proves the required major-arc deduction from the fixed
zero-free theorem for arbitrary bounded sifted β coefficients,
without a c_V-specific prime-factor estimate or an exceptional-set
moment. It uses the stronger zero-free input. The actual proof of
that input remains an audit obligation. The off-major-arc replay
and the remaining transfer are recorded below.

## Shorter Vaughan variables under the weaker rectangle

The source's [block estimate](https://raw.githubusercontent.com/aster2024/openai-math-followups/main/mobius-goldbach-shift/source/main.tex)
(Proposition II) permits every fixed lower length exponent δ>0.
LWW Proposition 4.2 has the same range. Its arithmetic major-arc
completion nevertheless uses the displayed choice U=V=x^(1/5) at
two specific steps. Neither can be quoted unchanged for R1.

### Prime-factor polynomial

Guo's Lemma P is stated for y≥T^(1/6), and the subsequent bound for
the c_V polynomial uses V≥T^(1/6). Its contour proof actually gives,
for every fixed γ>0 and y≥T^γ,

    |Σ_(ℓ≤y)Λ(ℓ)χ(ℓ)ℓ^(iu)|
      ≪ y L³[L^(−γ C_zf,1/2)+L^(−C_zf,2)].                   (Pγ)

Indeed the same shifted line is
σ_0=1−C_zf,1 log L/(2L), so
y^(σ_0)≤y L^(−γ C_zf,1/2). The logarithmic-derivative bound and
the two horizontal sides are unchanged. The imprimitive correction
is O(L²), absorbed because γ is fixed and positive. This is a
deduction from the specified zero-free rectangle, whose supply is
still audited separately; it is not an added Lean premise.

With U=V=x^(1/10), x comparable to T, eventually V≥T^(1/12).
Choose γ=1/12 and C_zf,1≥24(D+4), retaining the required height
constants. Expanding c_V(n) as Σ_(ℓk=n,ℓ>V)Λ(ℓ), both endpoints
of every prime sum are at least V. The same harmonic sum over k
then proves the large-conductor bound

    |N_ξ(t)|≪L^(1−D).

Its deleted small-prime and target-unit factors cost
O((Z+L)/V), which has every fixed logarithmic saving. Mellin
frequencies of size L^E only enlarge the fixed height constant.

### Exceptional character energy

The source's sixth moment uses M³≥T^(3/5−o(1)); this is false for
the new lower range M≥T^(1/10−o(1)). Use the twelfth moment instead.
On its sparse exceptional character-frequency family E, already
bounded by |E|≤exp(L^0.9), the coefficients of M_ξ(t)^6 satisfy

    |b_u|≤M^−6 τ_6(u),  M^6<u≤64M^6,
    Σ_u|b_u|²≪M^−6 L^35.

The elementary inequality τ_6²≤τ_36 follows prime by prime:
two compositions of an exponent into six parts can be encoded by
a canonical nonnegative 6×6 transport table with those margins.
Its 36 entries recover both compositions. The usual divisor moment
then gives the displayed squared norm.

Apply the source's Halász–Montgomery Gram argument at length M^6.
The fixed support ratio 64 changes only constants in its smooth
majorant. The same-character row is O(M^6 log L), and the
distinct-character row is at most

    |E| L^O(1) T^(1/2+o(1))=T^(1/2+o(1))=o(M^6),

by Pólya–Vinogradov and M^6≥T^(3/5−o(1)). Consequently

    Σ_E |M_ξ(t)|^12≪L^36.                                    (E12)

If M≥T^(2/5), the source's Burgess second-moment argument still
applies unchanged. If M<T^(2/5), then MN is comparable to T,
so N≥T^(11/20) for large T; the source's second moment for N
is still O(L² log L). Hölder now gives

    Σ_E |M|²|N|²
      ≤sup_E|N|^(1/3) (Σ_E|M|^12)^(1/6)(Σ_E|N|²)^(5/6)
      ≪L^(8−D/3)(log L)^(5/6).

Thus any prescribed logarithmic precision follows by choosing D
sufficiently large after the fixed arc-height parameters. The bulk
and small-conductor estimates retain their original coefficient and
length bounds. No enlarged marking count is needed after this choice.

More generally, for M≥T^(ν−o(1)) choose a fixed integer k with
kν>1/2. The identical argument yields Σ_E|M|^(2k)≪L^(k²),
followed by Hölder exponents k and k/(k−1). This removes the
particular 1/5 lower-length restriction from the major-arc deduction.
It supplies no missing zero-free theorem or off-major-arc cancellation.

## Stronger candidate forced by the parameter check

The same proposed assembly reaches each fixed level θ<1, with K
allowed to depend on A and θ. Choose Vaughan cutoffs
U=V=T^ν where ν=(1−θ)/8. The short Type I variable has exponent
2ν, and the already-proved Type I condition becomes

    2(2ν)+θ=(1+θ)/2<1.

The Type II lower length ν is positive and fixed, so the higher
moment above applies. The common-cofactor root-average inequality
itself imposes no smaller polynomial level. This is **candidate R2**,
subject to the same source audit; it is not an established prime theorem.
It still excludes moduli sharing marking primes and still leaves
signed mark removal open.

## Reflected moment source: paper replay

The relevant LWW Sections 4.2–4.7 and Appendix A were read against
Guo's exact changes, rather than treating H2′ as a new assumption.
The detailed source ledger is on the
[varying-shift card](goldbach-varying-shift-source-audit.md).
No gap was found in this replay. This is a paper audit, not a Lean
verification or an assertion that every other source section was checked.

In particular, the clean lattice has a basis box of area comparable
to Y and both sides between Y^0.1 and Y^0.9. The minor-arc determinant
matrix factors into two rectangular exponential matrices; its normalized
norm is O(L^(0.2−A_0)+Y^−0.1 log Y). The memory operators have
bounded absolute weighted row and column sums, so the collision phases
used to enforce globally distinct prime selections preserve those bounds.
The unaffected edge operators retain their signed saving. The final
positive coefficient-space trace does not require normalized root vectors.

In the reflection, the congruence modulo T is retained throughout.
Its index-T lattice reduces the determinant before counting edges.
The target-unit root density is bounded above by one, and the number
of unit roots in each localized interval is O(d_0Y). Consequently
neither the root measure nor the final trace introduces a factor T.
The comparison-edge count remains O(1) after fixing one product:
the other product lies in an interval of length O(T) and one residue
class modulo T. These are the points needed for the common-cofactor
energy; a per-modulus operator contraction is not substituted for them.

Together with the fixed-half-plane major-arc deduction above, this
replay yields the proposed energy

    E=Σ_(h≠0)|S_Y(h)|² ≪_(D,K,ν) T Y L^−D,                 (E)
    S_Y(h)=(∏V_i)^−1 Σ_(a∈A, mn=T−ah)
                          η(a/Y) α_m β_n,

where α_m=μ(m)R_Z(m)1_((m,T)=1)m^(iv), |β_n|≤L,
β is sifted and supported on units modulo T, M,N≥T^ν/2,
MN comparable to T, and |v| is at most a fixed power of L.
Any additional phase of modulus one on β is allowed. Fix the
precision D, then A_0 and K, before T→∞. The sole unresolved
nonclassical dependency of this deduction is the actual external
fixed seven-eighths theorem. Equation (E) is not inserted into Lean
as an analytic hypothesis.

## Full root-average transfer and error ledger

Here is the assembly from (E), with every root sum paid. It is a
deduction from the audited source argument and the outstanding
zero-free dependency, not a claim that R2 has passed its final gate.
Fix A>0 and θ<1, put ν=(1−θ)/8, and use U=V=T^ν.
All powers of L below are independent of the subsequently chosen K.

Use a fixed smooth χ supported in (1/8,3/4), equal to one on
[1/4,1/2]. Replace the prime sum by the sifted von Mangoldt sum,
weighted by χ(n/T)(n/T)^(iv). The discarded proper prime powers
have total root multiplicity at most τ(T−n)≪_ε T^ε. Their aggregate
cost is O_(K,ε)(T^(1/2+ε)L²), uniformly in the twist and q≤T^θ.
There is no term n=T on this support. No error of size Q times a
pointwise prime-power estimate is used.

Vaughan's identity is algebraically valid for these U,V. Its second
Type I coefficient, after combining dℓ=s, is bounded by log s,
and s≤UV=T^(2ν). The first Type I logarithm is handled by partial
summation. The existing reflected Type I theorem applies since

    2(2ν)+θ=(1+θ)/2<1.

The smooth weight and any fixed polylogarithmic twist cost only a
fixed power of L in partial summation; raise the requested precision
of that theorem. This does not change K.

For Type II, use dyadic m,n boxes and the smooth label partition.
There are O(L²) boxes and O_K(L) label scales. Mellin inversion of
χ has a bounded L¹ norm and separates its product argument. Retain
frequencies at most L^F, for a fixed sufficiently large F; rapid
decay makes the tail smaller than any requested logarithmic error.
The absolute root-multiplicity bound paying this tail is

    L Σ_(r≪T, r≠T) τ(r)τ(|T−r|) ≪ T L^4.

It follows by Cauchy and the ordinary second divisor moment. In
each separated box one may define the complementary coefficient
using μ(|T−mn|)W_T(|T−mn|) when mn>T, and zero when mn=T.
The latter case is already excluded on target-unit support. This
extension preserves exact Mellin inversion; the original χ vanishes
there. Negative cofactors in the energy therefore cause no support gap.

The two other root-summed errors are as follows.

1. **Target-unit deletion.** A common prime p of mn and T on sifted
   support exceeds Z. Write mn=pv and T−mn=p(T/p−v). The inequalities
   τ(pv)≤2τ(v) and τ(pw)≤2τ(w), followed by Cauchy, give

       Σ_(r≪T, p|r) τ(r)τ(|T−r|) ≪ (T/p)L³

   with r=T omitted. Summing p|T, p>Z, and the coefficient bound L
   costs O(T L^5/Z). The original bounded mark is retained here.

2. **Repeated marking prime.** Removing (a,h)=1 from the mark
   expansion adds only terms with p² dividing |T−mn| for some pool prime p.
   The absolute expanded mark is bounded: in each pool
   ω_i(r/a)≥ω_i(r)−1, so the sum of ρ^(ω(r/a)) over the selected
   divisors a is at most ∏_i ω_i(r)ρ^(ω_i(r)−1)=O_K(1).
   Put |T−mn|=p²h. Since (p,T)=1, the affine polynomial T±p²h
   is primitive. The largest-factor divisor estimate gives

       Σ_(h≪T/p²) τ(h)τ(|T−p²h|) ≪ (T/p²)L³,

   omitting a zero argument; the plus sign has the same bound.
   Indeed each second moment is O((T/p²)L³): use τ²≤τ₄,
   delete a largest factor, and note p²=T^o(1). Since
   τ(p²h)≤3τ(h), the coefficient bound L and Σ_(p≥P)1/p²≪1/P
   give O_K(T L^4/P), where P≥exp(L^0.1).

These estimates remain valid on subintervals and with the phases
present. Multiplying by the finite logarithmic number of boxes and
scales leaves an error smaller than T L^−D for every fixed D.

After these operations, q is coprime to every label a. Thus
q|T−mn is exactly q|h. The inner sum S_Y(h) is common to all q;
the outside factor μ(|h|)ρ^(ω(|h|)) has modulus at most one.
The coarse moment from the energy card, applied separately to
positive and negative h, is

    E₂=Σ_(h≠0)τ(|h|)²|S_Y(h)|² ≪_K T Y L^17.

The negative side uses T+ah in the same primitive affine divisor
moment. With H≪T/Y, the three-Cauchy inequality and (E) give

    Σ_(q≤T^θ, (q,T P_T)=1)|T_(Y,q)|
       ≪ T L^((19−D)/4).

The odd squarefree restriction can be retained as a subset. The
O(L²) boxes and O_K(L) label scales give T L^((31−D)/4).
Choose D=4A+50 before fixing A_0,K. This is stronger than the
twisted precision A+2 required in (M). Finally take
δ=L^(−A−4), V=L^(2A+9) there. Its QL term is negligible for
every fixed θ<1. This proves the full R2 transfer from the stated
energy, including independent maximal endpoints for each modulus.

No estimate uniform as θ approaches one with T has been proved.
No shared-marking-prime Type II theorem or signed mark removal is
supplied by this assembly.

## Gates

- [x] Exact prime-sum candidate and parameter obligations recorded.
- [ ] Source energy and zero-free dependencies audited.
- [x] LWW moment chain and Guo's reflected changes replayed on paper.
- [x] Endpoint transfer (M) proved with polylogarithmic frequencies.
- [x] Two changed lower-length steps in the major-arc deduction repaired.
- [x] Prime powers, target-unit deletion, repeated marks, and Mellin tails
      paid after the root sum; R2 transfer assembled.
- [ ] External fixed zero-free proof closure verified.
- [ ] Exact unconditional Lean proof, without analytic premises.
- [ ] Signed mark removal on prime-detecting rough support.

## Log

- 2026-10-23 — Opened the actual reflected marked prime sum after the
  Type I proof. The prime-level spacing count suggests a polylogarithmic
  frequency treatment of maximal endpoints. No new prime-correlation
  theorem is claimed.
- 2026-10-23 — Proved the common-envelope maximal inequality. Identified
  the source's genuine sixth-moment length restriction and replaced it
  by a twelfth moment; rescaled the prime-sum lower endpoint as well.
  Recorded candidate R2 for every fixed θ<1. The full prime theorem
  and unconditional analytic dependency closure remain unproved.
- 2026-10-23 — Replayed the reflected moment chain through signed memory,
  distinctness, localized pairings, and cleanup, including Appendix A's
  arbitrary-modulus root count. Corrected the character-twist conductor
  description and assembled the root-summed error ledger. The external
  seven-eighths proof closure is now the explicit unresolved source input
  to R2; prime-detecting signed mark removal remains a separate open core.
