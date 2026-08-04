import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# The regular part of `-ζ'/ζ`

The Möbius route used `1/ζ`, whose singularity at `s = 1` is removable.  The Chebyshev route uses
`-ζ'/ζ`, whose singularity there is a genuine simple pole with residue `1` — and that pole is the
*main term* of the prime number theorem rather than an obstruction.

Splitting it off is already available in the corpus: `logDeriv_zeta_eq` says that near `1`,

    ζ'/ζ = G'/G - 1/(s-1),     G = zetaResidueUnit = (s-1)·ζ(s),

so `-ζ'/ζ = 1/(s-1) + (-G'/G)` with the second summand holomorphic wherever `G` is nonvanishing.
That regular part is the analogue of `invZeta`, and the contour argument treats it the same way; the
pole contributes its residue and nothing else.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- **The regular part of `-ζ'/ζ`.**  The logarithmic derivative of the entire unit
`G = (s-1)ζ(s)`, negated. -/
noncomputable def zetaLogDerivReg (s : ℂ) : ℂ := -(logDeriv zetaResidueUnit s)

/-- **The pole is split off.**  Off the pole and away from the zeros of `ζ`, the negated
logarithmic derivative is `1/(s-1)` plus its regular part. -/
theorem neg_logDeriv_riemannZeta_eq {s : ℂ} (hs : s ≠ 1) (hG : zetaResidueUnit s ≠ 0) :
    -(logDeriv riemannZeta s) = (s - 1)⁻¹ + zetaLogDerivReg s := by
  rw [zetaLogDerivReg, logDeriv_zeta_eq hs hG]
  ring

/-- The regular part is holomorphic wherever the entire unit is nonvanishing. -/
theorem differentiableAt_zetaLogDerivReg {s : ℂ} (hG : zetaResidueUnit s ≠ 0) :
    DifferentiableAt ℂ zetaLogDerivReg s := by
  have hana := analyticAt_zetaResidueUnit s
  have hd : DifferentiableAt ℂ (deriv zetaResidueUnit) s := hana.deriv.differentiableAt
  have hf : DifferentiableAt ℂ zetaResidueUnit s := hana.differentiableAt
  have hquot : DifferentiableAt ℂ (fun z => deriv zetaResidueUnit z / zetaResidueUnit z) s :=
    hd.div hf hG
  have hcongr : zetaLogDerivReg = fun z => -(deriv zetaResidueUnit z / zetaResidueUnit z) := by
    funext z
    rw [zetaLogDerivReg, logDeriv_apply]
  rw [hcongr]
  exact hquot.neg

/-- **At the pole the regular part is the Euler–Mascheroni constant, negated.**  Since `G(1) = 1`
and `G'(1) = γ`, the regular part takes the value `-γ` there — the Laurent constant of `-ζ'/ζ`. -/
theorem zetaLogDerivReg_one :
    zetaLogDerivReg 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  rw [zetaLogDerivReg, logDeriv_zetaResidueUnit_one]

/-- The regular part is holomorphic at the pole itself. -/
theorem differentiableAt_zetaLogDerivReg_one : DifferentiableAt ℂ zetaLogDerivReg 1 :=
  differentiableAt_zetaLogDerivReg (by rw [zetaResidueUnit_one]; norm_num)

/-- **The regular part off the pole, in terms of `ζ` alone.**  Where `ζ` is nonvanishing and
`s ≠ 1`, the splitting is unconditional. -/
theorem neg_logDeriv_riemannZeta_eq_of_ne_zero {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    -(logDeriv riemannZeta s) = (s - 1)⁻¹ + zetaLogDerivReg s :=
  neg_logDeriv_riemannZeta_eq hs ((zetaResidueUnit_ne_zero_iff hs).2 hz)

end RHTower.Sieve
