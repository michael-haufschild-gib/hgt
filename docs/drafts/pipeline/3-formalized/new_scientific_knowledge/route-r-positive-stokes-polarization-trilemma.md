# Route R positive Stokes-polarization trilemma

- **ID:** `route-r-positive-stokes-polarization-trilemma`
- **Stage:** 3 — formalized in Lean 4
- **Type:** POSITIVE CONSTRUCTION / SHARP DESCENT CLASSIFICATION
- **Status:** `[LOCAL-RESEARCH] [PAPER-PROVED] [LEAN-PROVED] [NOT RH]`
- **Parent:** `../../1-in-progress/route-r-source-positive-polarization-stokes-flatness.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldPositiveStokesPolarization.lean`

## 1. Data

For a prime/depth cell \(i\), put
\[
 m_i=(1-p_i^{-1})p_i^{-e_i},\qquad
 \lambda_i=\log(p_i^{e_i+1})>0,
\]
and
\[
 \theta_{ij}=m_i\lambda_j-m_j\lambda_i.
\]
For \(a\in\mathbb R\), the already constructed determinant-one resolved source frame and
transition are
\[
 G_{a,i}=\begin{pmatrix}\lambda_i^{-1}&a m_i\\0&\lambda_i\end{pmatrix},
 \qquad
 R_{a,ij}=G_{a,i}^{-1}G_{a,j}
 =\begin{pmatrix}
 \lambda_i/\lambda_j&-a\theta_{ij}\\
 0&\lambda_j/\lambda_i
 \end{pmatrix}.
\tag{1}
\]
The identity \(R_{a,ij}R_{a,jk}=R_{a,ik}\) is already proved from the weighted source cocycle.

## 2. Positive resolved polarization

Define, on the resolved two-coordinate fibre,
\[
 H_{a,i}(z,w)=\langle G_{a,i}z,G_{a,i}w\rangle_{\mathbb C^2},
 \qquad E_{a,i}(z)=H_{a,i}(z,z)=\|G_{a,i}z\|^2.
\tag{2}
\]

### Theorem 2.1 — strict positivity

For every \(a,i\), \(E_{a,i}(z)\ge0\), and
\[
                         E_{a,i}(z)=0\iff z=0.
\tag{3}
\]

**Proof.** Nonnegativity is the sum of the squared norms of the two coordinates of
\(G_{a,i}z\).  If it vanishes, then \(G_{a,i}z=0\).  The explicit inverse of \(G_{a,i}\) exists
because \(\lambda_i>0\), so \(z=0\).  The converse is immediate. ∎

### Theorem 2.2 — independent Stokes flatness

For every \(a,i,j,z,w\),
\[
 H_{a,i}(R_{a,ij}z,R_{a,ij}w)=H_{a,j}(z,w),
 \qquad E_{a,i}(R_{a,ij}z)=E_{a,j}(z).
\tag{4}
\]

**Proof.** Equation (1) gives \(R_{a,ij}=G_{a,i}^{-1}G_{a,j}\).  Hence
\(G_{a,i}R_{a,ij}=G_{a,j}\).  Substitute this identity twice into (2).  No Xi divisor,
critical-line premise, anomaly vanishing, or scalar boundary is used. ∎

This is an actual positive source polarization and an unconditional Stokes-flatness law.  It is a
source-indexed metric field, not a single fixed same-fibre metric.

## 3. Fixed Cartier metric and literal vertical conormal

Freeze the source metric before the modular deformation:
\[
 H_i^{\mathrm{src}}:=H_{0,i},\qquad
 E_i^{\mathrm{src}}(z)
   =\left|\frac{z_1}{\lambda_i}\right|^2+|\lambda_i z_2|^2.
\tag{5}
\]
For \(c\in\mathbb C\), define the clock-normalized literal vertical conormal
\[
                         v_c(i)=\left(0,\frac c{\lambda_i}\right).
\tag{6}
\]
Then \(E_i^{\mathrm{src}}(v_c(i))=|c|^2\), independent of the source cell.

### Theorem 3.1 — exact positive Stokes excess

For every \(a,i,j,c\),
\[
 E_i^{\mathrm{src}}(R_{a,ij}v_c(j))
       -E_j^{\mathrm{src}}(v_c(j))
 =\frac{a^2\theta_{ij}^2}{\lambda_i^2\lambda_j^2}|c|^2\ge0.
\tag{7}
\]

**Proof.** From (1) and (6),
\[
 R_{a,ij}v_c(j)
 =\left(-\frac{a\theta_{ij}c}{\lambda_j},
         \frac c{\lambda_i}\right).
\]
Substitution into (5) gives
\[
 E_i^{\mathrm{src}}(R_{a,ij}v_c(j))
 =\frac{a^2\theta_{ij}^2}{\lambda_i^2\lambda_j^2}|c|^2+|c|^2.
\]
Subtract \(E_j^{\mathrm{src}}(v_c(j))=|c|^2\).  Every remaining factor is a real square and
\(\lambda_i\lambda_j>0\). ∎

### Corollary 3.2 — sharp fixed-polarization selector

If \(c\ne0\) and \(\theta_{ij}\ne0\), then
\[
 E_i^{\mathrm{src}}(R_{a,ij}v_c(j))
       =E_j^{\mathrm{src}}(v_c(j))
       \iff a=0.
\tag{8}
\]

**Proof.** By (7), equality is equivalent to
\(a^2\theta_{ij}^2|c|^2=0\).  The last two factors are nonzero, so \(a=0\). ∎

## 4. Actual Xi landing

Choose the explicit edge
\[
 i_0=((2),0),\qquad i_1=((2),1).
\]
The existing source theorem proves \(\theta_{i_0i_1}>0\).  At
\(\rho\in\operatorname{Div}(\Xi)\), put
\[
 a_\rho=2\Re\rho-1,
 \qquad
 c_\rho=\Xi^{(m_\rho)}(\rho)\ne0.
\tag{9}
\]
Both the multiplicity-exact nonvanishing and the cofinal physical source landing of
\(c_\rho\) are already formalized.

### Theorem 4.1 — pointwise Xi polarization criterion

The fixed source polarization is Stokes-flat on the actual clock-normalized leading conormal over
the witness edge iff \(\rho\) is critical:
\[
 E_{i_0}^{\mathrm{src}}
   (R_{a_\rho,i_0i_1}v_{c_\rho}(i_1))
 =E_{i_1}^{\mathrm{src}}(v_{c_\rho}(i_1))
 \iff \Re\rho=\frac12.
\tag{10}
\]

**Proof.** Apply Corollary 3.2 using \(c_\rho\ne0\) and
\(\theta_{i_0i_1}>0\).  It gives equality iff \(a_\rho=0\), which is exactly the displayed
critical-line equation. ∎

### Corollary 4.2 — global classification

Fixed-polarization Stokes flatness in (10) at every actual Xi divisor point is equivalent to RH.
This is an unconditional equivalence, not a proof of its left side.

## 5. Trilemma and frontier

The complete classification is:

1. **Positive polarization exists:** \(H_{a,i}\) is source-created and positive definite.
2. **Independent Stokes flatness exists:** the varying field \(H_{a,i}\) is parallel for every
   \(a\).
3. **Fixed same-fibre descent is selective:** replacing \(H_{a,i}\) by the source-fixed
   \(H_i^{\mathrm{src}}\) on the literal vertical Xi conormal has the exact nonnegative defect
   (7), and its global vanishing is RH.

Thus Route R no longer lacks a positive polarization or a Stokes-flatness theorem.  Missing
scientific law is a source-derived rigidity identifying the transported metric field with the
source-fixed Cartier metric on the literal vertical conormal.  Equation (7) proves that such an
identification cannot be inferred from resolved flatness, determinant one, reflection symmetry,
or positivity alone.

## 6. Novelty and non-theatre audit

Pulling back a Hilbert metric through a flat frame is standard and is not claimed as new in
isolation.  New source-specific content is the exact comparison with the fixed clock metric on the
literal, multiplicity-exact Xi conormal: its discrepancy is the fully labelled BV--Wold square in
(7), and the explicit arithmetic witness makes its zero locus exactly criticality.  This closes a
previously ambiguous representation question and rules out treating a source-indexed harmonic
metric as the missing same-fibre Cartier polarization.

The result does not prove RH and does not promote a transported metric into a fixed one.
