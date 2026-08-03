# CCM four-unit cofinal contraction saturation rigidity

- **Status:** LEAN-FORMALIZED
- **Lane:** Connes--Consani--Moscovici / singular Xi Ward boundary lift
- **Novelty scope:** corpus-new source-specific classification; abstract Hilbert contraction
  saturation is classical operator geometry
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/MobiusDoubledParityContractionSaturationRigidity.lean`

## Result

Let \(T:H\to K\) be a contraction between complex Hilbert spaces. For every finite packet
\(v_i\), its Gram loss is positive semidefinite:

\[
  \operatorname{Gram}(v)-\operatorname{Gram}(Tv)\succeq0.                 \tag{1}
\]

For one distinguished detail vector \(d\),

\[
 \|T^*Td-d\|^2\le \|d\|^2-\|Td\|^2,                                     \tag{2}
\]

and therefore, for every \(x\),

\[
 |\langle Tx,Td\rangle-\langle x,d\rangle|
 \le \|x\|\sqrt{\|d\|^2-\|Td\|^2}.                                      \tag{3}
\]

Exact saturation \(\|Td\|=\|d\|\) forces \(T^*Td=d\), hence freezes the entire
detail codiagonal:

\[
 \langle Tx,Td\rangle=\langle x,d\rangle.                               \tag{4}
\]

The cofinal form is stronger than a finite-rank statement. For arbitrary Hilbert dimensions and
an arbitrary sequence of contractions \(T_n\), if

\[
\langle x_n,d_n\rangle=0,\qquad
\sup_n\|x_n\|<\infty,\qquad
\|d_n\|^2-\|T_nd_n\|^2\longrightarrow0,
\]

then

\[
\langle T_nx_n,T_nd_n\rangle\longrightarrow0.                           \tag{5}
\]

If a moving target detail is decomposed as

\[
e_n=T_nd_n+c_n,
\]

and \(\langle T_nx_n,e_n\rangle\to r\), then the connection term carries the full
limiting column:

\[
\langle T_nx_n,c_n\rangle\longrightarrow r.                             \tag{6}
\]

## CCM specialization

For the doubled Möbius parity source,

\[
F_{\sigma,u}=2^{-1/2}(d_{\sigma,u},p d_{\sigma,u}),\qquad
D_\sigma=2^{-1/2}(\chi_\sigma,-p\chi_\sigma),
\]

the corpus already proves

\[
\langle F_{\sigma,u},D_\sigma\rangle=0,\qquad
\|D_\sigma\|^2\to4.
\]

Equations (3)--(5) now prove that no bounded contraction family can turn this zero
codiagonal into the continued Xi Ward column while asymptotically retaining the four-unit detail
energy. This holds in infinite-dimensional source and target spaces and for cofinal sequences;
finite rank is irrelevant.

Lean also proves the exact source classification

\[
\mathrm{RH}
\quad\Longleftrightarrow\quad
\text{a cofinal contraction realization of the continued Xi Ward column
from the doubled Möbius source exists}.                                  \tag{7}
\]

The reverse implication uses zero-adapted Xi sampling. Under RH the Ward column vanishes, and the
identity contraction along the explicit critical sequence
\(\sigma_n=1+1/(n+1)\) supplies the forward construction.

## Consequence for the active frontier

The proposed graph-norm repair cannot work by treating \(D_\sigma\) as an ordinary transported
detail. Four-unit saturation freezes its zero source codiagonal, even only asymptotically.
A surviving Julia lift must contain a genuine moving-operator connection \(c_n\), and (6) says
that this term—not \(T_nD_{\sigma_n}\)—must carry all of \(r_P\).

Thus the exact unresolved object is narrower:

> construct the source-defined Gamma/Wiener--Hopf connection term and prove that its augmented
> target detail has squared norm at most four, or prove no CCM-admissible connection can do so.

Reweighting the graph norm, ordinary target Hardy contractivity, finite-rank repair, and a
cofinal bounded contraction acting directly on the C41 detail are closed routes.

## Lean declarations

- `contractionGramDefect_posSemidef`
- `adjoint_apply_apply_eq_of_contraction_saturates`
- `norm_adjoint_apply_apply_sub_sq_le_detail_loss`
- `norm_codiagonal_defect_le`
- `codiagonal_tendsto_zero_of_cofinal_contractions`
- `connection_codiagonal_tendsto_of_cofinal_contractions`
- `continuedXiAntiCausalWardResponse_eq_zero_of_cofinalMobiusParityRealization`
- `riemannHypothesis_iff_cofinalMobiusParityRealization`

All declarations are theorem/definition based. No `sorry`, `admit`, new axiom, `opaque`, or
`unsafe` declaration is used.
