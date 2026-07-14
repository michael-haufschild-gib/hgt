# Post-revision referee report

## Recommendation

**Major revision.** The revision now contains a genuine unconditional estimate and no longer
consists only of equivalent formulations of RH. The endpoint-calibrated Hausdorff theorem proves
616 inequalities in the all-degree criterion without assuming RH. This is the strongest and most
defensible new feature of the manuscript. The remaining condition is correctly isolated as one
cofinal complementary tail.

I would not yet recommend acceptance. The mathematics is potentially publishable, but the current
paper is too broad, the headline theorem is too long, and the literature boundary of the new
616-condition result has not been established with enough precision for a journal claim.

## Strongest result

With

\[
 C=2+\gamma_E-\log(4\pi),\qquad R_*=\frac{C}{1-C},\qquad
 \lambda_\rho=-\frac4{(2\rho-1)^2},
\]

the paper defines the calibrated differences

\[
 D^*_{k,r}=\sum_{j=0}^r(-1)^j\binom rjR_*^{r-j}\mu_{k+j}
\]

and proves the exact value relation

\[
 D^*_{k,r}=\Re\sum_\rho
 \lambda_\rho^{k+1}(R_*-\lambda_\rho)^r.
\]

The quartet sector bounds and opposite phases then imply

\[
 D^*_{k,r}\ge0\qquad(0\le k\le13,\ 0\le r\le43),
\]

which is a block of 616 unconditional inequalities. If \(\mathsf T_*\) denotes positivity on the
complementary tail, the manuscript proves

\[
 \mathsf T_*
 \Longleftrightarrow \mathrm{RH}
 \Longleftrightarrow \sigma_{\rm abs}(S_{L,N}^-)\le1
 \Longleftrightarrow
 \sum_{n\le X}S_{L,N}^-(n)=O_\varepsilon(X^{1+\varepsilon})
 \Longleftrightarrow
 \text{local finite-KMS/Wightman closure}.
\]

This is one coherent master theorem: the source, divisor, Hausdorff, summatory, and thermal
coordinates all encode the same remaining cofinal condition. It is also actual estimate progress:
the 616 conditions have been removed from the RH premise.

## What the revision successfully fixes

1. The paper now has one headline theorem rather than two competing main results.
2. A finite but nontrivial portion of the missing positivity estimate is proved unconditionally.
3. The exact source--divisor value law explains why the Hausdorff and thermal formulations are not
   merely juxtaposed.
4. The prime--polar abscissa and cumulative-growth endpoints are incorporated into the same
   theorem.
5. The manuscript explicitly says that the complementary cofinal tail remains open and that RH is
   not proved.
6. The opposite-phase proof is transparent: the rational sector bounds lead directly to the
   \(14\times44\) rectangle.

## Mandatory revisions

### 1. Shorten Theorem A

The current Theorem A is an omnibus theorem spanning source formulas, abscissae, projective
radii, endpoint curvature, thermal moments, KMS systems, passive response, cold partitions, and
several equivalent RH criteria. A main theorem should be readable as one mathematical assertion.

The journal version should state only:

- the exact calibrated divisor-value law;
- the unconditional \(14\times44\) rectangle;
- the definition of the complementary tail;
- the five-way tail/RH/abscissa/cumulative/KMS equivalence.

The fixed-window formula, endpoint budget, Morse--Fisher estimate, passive response theorem, and
cold-partition criteria should be corollaries or supporting theorems. This would strengthen the
headline by making its logical content visible rather than weakening it by deletion.

### 2. Establish the precise novelty boundary of the 616-condition theorem

The paper compares itself broadly with Guinand, Weil, Barner, Connes, and Hausdorff moment theory,
but it does not yet give a theorem-by-theorem comparison for the endpoint-calibrated array. The
authors must answer:

- Is the value relation a new normalization of an existing Li/Hausdorff criterion, or genuinely
  new?
- Has an unconditional finite rectangle of these exact scaled differences appeared before?
- Is \(14\times44\) maximal only for the displayed worst-case sector estimates, or is any stronger
  maximality claimed?
- Which part uses project-specific estimates rather than classical zero-free information?

The safe claim is that the displayed rectangle is the largest integer rectangle certified by the
specific two rational angle bounds used in the proof. The manuscript should not call it globally
optimal without a separate theorem.

### 3. Isolate all convergence justifications in the value law

The passage from calibrated source moments to
\(\Re\sum_\rho\lambda_\rho^{k+1}(R_*-\lambda_\rho)^r\) must state explicitly:

- the multiplicity convention;
- absolute convergence for every \(k,r\);
- why the finite binomial sum may be interchanged with the divisor sum;
- why taking real parts commutes with the sum;
- the exact normalization connecting \(\mu_n\) to the reciprocal-square divisor.

These points appear to be available in the paper, but the main proof should collect them in one
lemma rather than force the reader to reconstruct them from several sections.

### 4. State the geometric sector lemma independently

The core estimate deserves a standalone proposition. It should formulate the abstract fact that,
for opposite-phase right-half-plane numbers \(z,w\), bounds on
\(|\arg z|\) and \(|\arg w|\) imply
\(\Re(z^pw^r)\ge0\) whenever the combined phase lies in
\([-\pi/2,\pi/2]\). The application should then derive the constants \(913/100\) and
\(2739/100\) and set \(p=k+1\).

This separation would make clear exactly where Xi-specific information enters and which part is
elementary complex geometry.

### 5. Explain why a finite rectangle is meaningful but cannot by itself approach RH cofinally

The paper should say explicitly that remote off-line quartets can postpone a negative calibrated
difference beyond any prescribed finite index set. Therefore the 616-condition theorem is genuine
local estimate progress but does not supply a convergence mechanism. The next required theorem
must propagate positivity cofinally, or control the complementary tail directly from the source.

This is not a weakness to hide. It is the exact research frontier created by the theorem.

### 6. Reduce the abstract and introduction

The abstract currently tries to summarize nearly the entire 60-page paper. A journal abstract
should lead with the exact value law, the 616-condition rectangle, and the cofinal-tail
equivalence. The fixed-window source construction and KMS interpretation can be summarized in two
sentences. Numerical constants and secondary equivalent criteria should move to the introduction.

### 7. Reorganize the paper around the master implication chain

A clearer order would be:

1. source construction and exact prime--Gamma/prime--polar identities;
2. reciprocal-square moments and endpoint calibration;
3. sector geometry and the 616-condition theorem;
4. Hausdorff/KMS closure and the cofinal-tail equivalence;
5. quantitative endpoint and thermal refinements;
6. Mellin tomography and ancillary criteria;
7. limitations and the remaining estimate.

At present the reader encounters many equivalent RH criteria before learning which one receives an
unconditional estimate.

### 8. Moderate the physical language

The KMS and Wightman terminology is warranted only where an explicit finite positive moment
realization is constructed. Terms such as “temperature,” “passivity,” and “Born--Witten source”
should always be tied to a stated mathematical object. The paper does not construct a global
quantum Hamiltonian whose spectrum is the Xi divisor, and it should not suggest otherwise.

The accurate claim is that the normalized source moments admit a finite-system KMS/Wightman
closure exactly when the complementary positivity tail holds.

### 9. Make the remaining estimate a named open problem

The paper should end with a single boxed problem:

\[
 D^*_{k,r}\ge0\qquad(k>13\text{ or }r>43).
\]

Equivalent source and operator forms may follow immediately. Naming this tail would make the
paper reusable: future work can target a precise propagation, total-positivity, or reflection
principle rather than another RH reformulation.

### 10. Resolve editorial and authorship policy before submission

The target journal's policy on AI systems listed as authors must be checked before submission.
Some journals require such systems to be described as tools rather than authors because they
cannot assume legal responsibility. This is an editorial issue independent of the mathematics.

## Questions for the authors

1. Is the \(14\times44\) rectangle maximal for the proved sector constants? If so, prove and state
   that limited maximality.
2. Can the exact, rather than rationally weakened, sector bounds enlarge the integer rectangle?
3. Is there any unconditional recurrence connecting \(D^*_{k,r}\) outside the rectangle to values
   inside it?
4. Can total positivity of the theta-source kernel control a cofinal ray in the \((k,r)\)-plane?
5. Which source-side inequality would imply the whole complementary tail without first assuming an
   equivalent form of RH?
6. Can a remote off-line quartet be used to prove that no fixed finite rectangle can be an RH
   criterion in this normalization?
7. Is local finite-KMS closure genuinely stronger operationally than Hausdorff positivity, or is
   it included solely as a physical realization of the same moment theorem?
8. Which result in the paper would remain new and significant if every equivalent RH criterion
   were removed from the statement?

## Assessment

- Mathematical closure: **24/25**
- Genuine progress on the missing estimate: **18/25**
- Novelty case as presently documented: **14/20**
- Exposition and journal organization: **12/20**
- Reproducibility of definitions and constants: **9/10**

**Overall: 77/100.**

The paper has moved substantially beyond an elegant reformulation: it proves a nontrivial finite
region of the missing positivity theorem. It has not reached a 90/100 journal state because the
cofinal estimate remains open, the novelty boundary of the rectangle needs a dedicated audit, and
the manuscript is still too encyclopedic. A focused revision could plausibly reach the
mid-eighties without proving RH. Reaching 90 would require either a substantial cofinal
propagation theorem or a comparably strong source estimate beyond every fixed finite block.
