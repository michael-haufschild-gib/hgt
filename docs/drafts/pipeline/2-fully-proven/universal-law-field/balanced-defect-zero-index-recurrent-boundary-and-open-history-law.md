# Balanced defect, zero index, recurrent boundary, and open history law

- **ID:** ULF-DEFECT-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** hostile attack on boundary-index reconstruction
- **Statement:** Stable index and boundary winding can vanish identically while positive kernel--cokernel defect grows without bound along exact recurrent observations.
- **Status:** [PAPER-PROVED] [FALSIFIES INDEX COMPLETENESS] [POSITIVE SURVIVOR] [ROUTE-INDEPENDENT] [NO LEAN]

## 1. Setup

Let \(S\) be the unilateral shift on \(H=\ell^2(\mathbb N_0)\), and for \(n\ge0\) define

\[
T_n=S^n\oplus S^{*n}:H\oplus H\longrightarrow H\oplus H.
\tag{1}
\]

Let \(D_n=1-S^nS^{*n}\), the rank-\(n\) projection from the Toeplitz calibration.

## 2. Theorem

For every \(n\ge0\):

1. \(T_n\) is Fredholm;
2. its initial and final defect projections are

   \[
   K_n:=1-T_n^*T_n=0\oplus D_n,
   \qquad
   C_n:=1-T_nT_n^*=D_n\oplus0;
   \tag{2}
   \]

3. \(\operatorname{rank}K_n=\operatorname{rank}C_n=n\);
4. \(\operatorname{ind}T_n=0\);
5. its Toeplitz boundary symbol is

   \[
   \sigma(T_n)=\operatorname{diag}(z^n,z^{-n});
   \tag{3}
   \]

6. \(\det\sigma(T_n)=1\), so \([\sigma(T_n)]=0\in K_1(C(S^1))\) and the stable connecting
   class vanishes;
7. the unsigned defect energy

   \[
   E(T_n):=\operatorname{Tr}K_n+\operatorname{Tr}C_n=2n
   \tag{4}
   \]

   diverges;
8. for every \(m\ge2\), the root-of-unity boundary observer

   \[
   O_m(n)=\operatorname{diag}(\zeta_m^n,\zeta_m^{-n})
   \tag{5}
   \]

   is periodic, and along \(n=km\), \(O_m(km)=1_2\) while \(E(T_{km})=2km\to\infty\).

### Proof

Using \(S^{*n}S^n=1\) and \(S^nS^{*n}=1-D_n\),

\[
T_n^*T_n
=(S^{*n}S^n)\oplus(S^nS^{*n})
=1\oplus(1-D_n),
\]

and

\[
T_nT_n^*
=(S^nS^{*n})\oplus(S^{*n}S^n)
=(1-D_n)\oplus1.
\]

This proves (2), and both defects have rank \(n\). The kernel of \(T_n\) is the kernel of
\(S^{*n}\), of dimension \(n\); its cokernel is the cokernel of \(S^n\), also of dimension
\(n\). Hence \(T_n\) is Fredholm with index zero.

The Toeplitz quotient sends \(S\) to \(z\) and \(S^*\) to \(z^{-1}\), proving (3). Its determinant
is one. Since determinant induces the winding-number isomorphism
\(K_1(C(S^1))\cong\mathbb Z\), the class of (3) is zero. Equivalently the boundary map is

\[
[K_n]-[C_n]=n-n=0.
\]

Equation (4) follows from the ranks. Equation (5) is periodic modulo \(m\), and substituting
\(n=km\) proves the last assertion. QED.

## 3. Abstract cancellation theorem

Let \(M\) be a commutative positive monoid, \(G(M)\) any group receiving \(M\), and define the
signed-defect map

\[
\delta:M\times M\longrightarrow G(M),
\qquad
\delta(a,b)=[a]-[b].
\tag{6}
\]

Every diagonal pair \((a,a)\) lies in \(\ker\delta\). If \(w:M\to[0,\infty]\) is additive and
\(w(a)>0\), then the unsigned energy \(w(a)+w(a)=2w(a)\) is positive despite zero signed defect.
Thus no invariant factoring through \(\delta\) can reconstruct positive defect energy in general.

The shift family realizes this elementary obstruction with \(M\) the monoid of finite-dimensional
defect spaces, signed defect the Fredholm index, and \(w=\dim\).

## 4. Killing theorem and positive survivor

**Killed conjecture:** the total stable connecting/index object reconstructs exactly the history lost
by reversible observation.

**Exact why:** stable difference invariants cancel balanced positive defects.

**Strongest survivor:** retain the ordered pre-cancellation defect pair \((K,C)\), its positive size,
and its transport law. The signed index is only one shadow

\[
(K,C)\longmapsto[K]-[C].
\]

Any universal history field based only on stable \(K\)-theory, determinant, or net winding is
therefore incomplete for complexity or open-history questions.

## 5. Sharp scope

- The ordered pair is not automatically invariant under arbitrary presentation changes.
- Kernel plus cokernel dimensions still miss internal module structure and higher extensions.
- The theorem does not say every relevant defect is Fredholm.
- The positive survivor is pre-stable/unstable defect geometry, not a claim that one scalar energy is
  universal.

## Log

- 2026-08-09 — boundary-index completeness falsified; ordered positive defect pair extracted.
