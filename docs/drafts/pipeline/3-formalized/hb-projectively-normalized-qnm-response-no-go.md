# HB projectively normalized QNM response no-go

- **ID:** HB-PNQR
- **Stage:** 3-formalized
- **Type:** NO-GO
- **Statement:** Bilinear QNM normalization is projectively invariant but realizes every complex HB target, so it cannot produce HB orientation.

## Closed chain

Killed `projectively normalized off-diagonal QNM response exists -> fixed HB Peierls orientation -> causal-cut extinction -> RH` at its first arrow.

For complex-bilinear `B`, `c(s,m)=B(s,m)/B(m,m)` and `R(s,m)=c(s,m) • m`. Under `m ↦ z m`, `c` has weight `z⁻¹` and `R` is invariant. On `ℂ`, `B(x,y)=xy`, `s=value`, `m=1` realizes every complex target with nonzero mode norm, hence every HB full-cokernel orbit on or off wall.

- **Killing theorem:** `d4HBProjectivelyNormalizedQNMResponseExistenceRouteKilled`
- **Positive survivor:** derive literal Einstein--Teukolsky bilinear form, source, causal contour/domain, and opposite Ward sign; normalization/covariance supplies no selection.
- **Lean audit:** direct check and targeted module build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`.

Corpus audit found diagonal bilinear descent and Hermitian/KMS alternatives dead, canonical left covectors available, and no prior normalized returned-field universal-realization theorem. Primary audit through 2026-08: Green--Hollands--Sberna--Toomani--Zimmerman `arXiv:2210.15935` and Sberna et al. `arXiv:2112.11168` supply bilinear projection/inverse-self-overlap normalization, not this HB/RH obstruction.
