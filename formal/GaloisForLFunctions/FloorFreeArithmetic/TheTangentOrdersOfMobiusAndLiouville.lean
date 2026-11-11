import Mathlib

/-!
# The tangent orders of Möbius and Liouville

The tangent datum of `Λ` at a zero `ρ` of `ζ` is a simple pole of `−ζ'/ζ` whose residue is the
multiplicity. For the Möbius and the Liouville function the Dirichlet series are `1/ζ(s)` and
`ζ(2s)/ζ(s)`. Right of the critical line `ζ(2s)` is analytic and nonzero at `ρ`, so both have
at `ρ` a pole of order exactly the multiplicity of the zero, and their leading coefficients
differ by the unit `ζ(2ρ)`. The same holds for `ζ(2s)^j/ζ(s)^k`, with the order `k` times the
multiplicity.

So the top layers of `Λ`, `μ` and `λ` have the same support, and the orders of `μ` and `λ`
record the multiplicities. The coefficients of `μ` are not integral: they involve the leading
Taylor coefficient of `ζ` at the zero, on which no constraint is known.

* `meromorphicOrderAt_mobius`: the order of `1/ζ` at a point.
* `meromorphicOrderAt_liouville`: the order of `ζ(2s)/ζ(s)` at a point right of the line.
* `meromorphicOrderAt_zeta_two_mul_pow_div_pow`: the order of `ζ(2s)^j/ζ(s)^k`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

/-- Right of the critical line `ζ(2s)` is analytic at `ρ`. -/
theorem analyticAt_zeta_two_mul {ρ : ℂ} (hre : 1 / 2 < ρ.re) :
    AnalyticAt ℂ (fun s => riemannZeta (2 * s)) ρ := by
  have hne : 2 * ρ ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      Complex.one_re] at hr
    linarith only [hr, hre]
  have hopen : IsOpen {s : ℂ | 2 * s ≠ 1} :=
    isOpen_ne_fun (continuous_const.mul continuous_id) continuous_const
  have hd : DifferentiableOn ℂ (fun s => riemannZeta (2 * s)) {s : ℂ | 2 * s ≠ 1} := fun s hs =>
    ((differentiableAt_riemannZeta hs).comp s
      (differentiableAt_id.const_mul 2)).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds hne)

/-- Right of the critical line `ζ(2ρ) ≠ 0`. -/
theorem zeta_two_mul_ne_zero {ρ : ℂ} (hre : 1 / 2 < ρ.re) : riemannZeta (2 * ρ) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith only [hre])

/-- **Möbius.** The series `1/ζ` has at every point the opposite order of `ζ`. -/
theorem meromorphicOrderAt_mobius (ρ : ℂ) :
    meromorphicOrderAt (riemannZeta⁻¹) ρ = -meromorphicOrderAt riemannZeta ρ :=
  meromorphicOrderAt_inv

/-- **Liouville.** Right of the critical line `ζ(2s)/ζ(s)` has the opposite order of `ζ`: a
pole of order the multiplicity at every zero. -/
theorem meromorphicOrderAt_liouville {ρ : ℂ} (hre : 1 / 2 < ρ.re) :
    meromorphicOrderAt ((fun s => riemannZeta (2 * s)) * riemannZeta⁻¹) ρ =
      -meromorphicOrderAt riemannZeta ρ := by
  rw [meromorphicOrderAt_mul_of_ne_zero (analyticAt_zeta_two_mul hre)
    (zeta_two_mul_ne_zero hre), meromorphicOrderAt_inv]

/-- Away from its pole `ζ` is analytic. -/
theorem analyticAt_riemannZeta {ρ : ℂ} (hρ : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ := by
  have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hρ)

/-- The series `ζ(2s)^j/ζ(s)^k` has, right of the critical line and away from the pole, `−k`
times the order of `ζ`. -/
theorem meromorphicOrderAt_zeta_two_mul_pow_div_pow {ρ : ℂ} (hre : 1 / 2 < ρ.re) (hρ : ρ ≠ 1)
    (j k : ℕ) :
    meromorphicOrderAt ((fun s => riemannZeta (2 * s)) ^ j * (riemannZeta ^ k)⁻¹) ρ =
      -(k * meromorphicOrderAt riemannZeta ρ) := by
  rw [meromorphicOrderAt_mul_of_ne_zero ((analyticAt_zeta_two_mul hre).pow j)
    (pow_ne_zero j (zeta_two_mul_ne_zero hre)), meromorphicOrderAt_inv,
    meromorphicOrderAt_pow (analyticAt_riemannZeta hρ).meromorphicAt]

end GaloisForLFunctions.FloorFreeArithmetic
