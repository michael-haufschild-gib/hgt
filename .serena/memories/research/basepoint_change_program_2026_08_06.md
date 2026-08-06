# Card `projective-ht-horizon-symmetric-space-boundary`: basepoint change — only the assembly is left

Everything else on the card is done (`mem:research/observer_boundary_layer_built_2026_08_06`).
Remaining: **basepoint change** — every geodesic ray is asymptotic to exactly one ray from the
reference metric.  Uniqueness is proved (EMI).  For existence all the inputs are now built; what is
left is one estimate and its assembly.

## The proof, in the frame form that Lean should follow
Let `b` be an antitone eigenframe of `T` with weights `w` (`exists_antitone_eigenframe`), let
`f i := g* (b i)`, let `gs := gramSchmidtOrthonormalBasis hcard f`, and let `S := diagOp gs w`
(**same** weights — this is what makes the exponents line up).  Then for `t ≥ 0`:

```text
(P⁻¹Q) (gs j) = ∑_i ⟪b i, (g*)⁻¹ (gs j)⟫ · e^(t (w j − w i)) · g⁻¹ (b i)
```
with `P = g* e^{tT} g`, `Q = e^{tS}`.  Triangularity kills `i > j`; antitonicity gives
`w j − w i ≤ 0` on the rest, so each `‖(P⁻¹Q) (gs j)‖ ≤ ∑_i |⟪b i, (g*)⁻¹ (gs j)⟫| ‖g⁻¹ (b i)‖`,
independent of `t`.  Then `norm_toCLM_le_sum_norm_apply` bounds `‖P⁻¹Q‖`.  Mirror expansion using
`g* (b i) ∈ span (gs '' Iic i)` bounds `‖Q⁻¹P‖` (expand `x`, then `y = g x`, in the `b` frame).
Finally `observerDist_le_of_norm_le` turns the two bounds into a bounded distance, i.e.
`Asymptotic (fun t => congrOp g (metricRay T t)) (observerRay hS)`.

## Lean status — all inputs built
| module | what it gives |
|-|-|
| `ObserverDistNormBound` | `observerDist_le_of_norm_le` — the metric half |
| `AntitoneEigenframe` | `exists_antitone_eigenframe`, `eigenSum_eq_span_initial` |
| `FlagTransport` | `exists_isSymmetric_eigenSum_map`, `span_gramSchmidtOrthonormalBasis_Iic`, `adjoint_equiv_injective` |
| `TriangularFrames` | `adjoint_symm_gramSchmidt_mem_span`, `mem_span_gramSchmidtOrthonormalBasis`, `norm_toCLM_le_sum_norm_apply`, `inner_eq_zero_of_mem_span_Iic`, `adjoint_symm_comp_adjoint`, `adjoint_comp_adjoint_symm` |

**Next**: write the expansion lemma
`(P⁻¹Q) (gs j) = ∑ i, ⟪b i, (g*)⁻¹ (gs j)⟫ • (e^{t(w j − w i)} • g⁻¹ (b i))`
(expand `(g*)⁻¹ (gs j)` in the `b` frame via `b.sum_repr`, apply `metricRay_apply_of_eigenvector`
termwise), then bound it with `inner_eq_zero_of_mem_span_Iic` + antitonicity, and assemble.
A `diagOp`-flavoured restatement of `FlagTransport` that *returns* `gs` and `w` (rather than the
bare `∃ S`) will be needed — add `exists_frame_eigenSum_map`.
