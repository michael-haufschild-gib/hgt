import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeSource

/-!
# The weight-one inversion implements the Born swap on the archimedean mode

The weight-one scale inversion `(J f)(t) = t⁻¹ · f(t⁻¹)` is the involution of scale profiles
whose Mellin action is the reflection `s ↦ 1 - s`.  This module verifies, on the Gaussian
theta-cusp seed and on power profiles, that `J` implements the reflection at the level of
dynamics while moving states:

* `J` is an involution away from `0` and anti-conjugates the scale generator `D = t∂_t`:
  `D(Jf) = -(Jf) - J(Df)`, i.e. `J D J = -(D + 1)`.
* Consequently the scaling Hamiltonian `D² + D = D(D+1)` **commutes** with `J`; on the
  Gaussian seed `g₀`, whose exact source identity is `(D²+D)g₀ = h` with `h` the theta-cusp
  seed, the inverted profile satisfies `(D²+D)(J g₀) = J h`.
* The Dirichlet power profiles `t^{-w}` are eigenvectors of `D² + D` with eigenvalue
  `w(w-1)` — the completed-zeta polynomial, invariant under `w ↦ 1-w` — and `J` exchanges
  the profiles `t^{-w} ↔ t^{-(1-w)}` inside each eigenspace.
* `J` does not fix the Gaussian seed itself: the swap preserves the Hamiltonian and moves
  the state.  The `J`-fixed profile is the lattice-summed theta, where Poisson summation
  exchanges the parity-signed and half-shifted theta sections.
-/

noncomputable section

namespace RHTower

/-- The weight-one scale inversion `(J f)(t) = t⁻¹ · f(t⁻¹)`: the profile-level unitary of
`L²(ℝ_{>0}, dt)` whose Mellin action is `s ↦ 1 - s`.  (For the multiplicative measure
`dt/t`, the unweighted inversion `f(t⁻¹)` is the unitary one.) -/
def weightOneInversion (f : ℝ → ℝ) (t : ℝ) : ℝ := t⁻¹ * f t⁻¹

/-- The weight-one inversion is an involution away from `0`. -/
theorem weightOneInversion_weightOneInversion (f : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    weightOneInversion (weightOneInversion f) t = f t := by
  unfold weightOneInversion
  rw [inv_inv]
  field_simp

/-- Derivative of an inverted profile. -/
theorem hasDerivAt_weightOneInversion {f : ℝ → ℝ} {f' t : ℝ} (ht : t ≠ 0)
    (hf : HasDerivAt f f' t⁻¹) :
    HasDerivAt (weightOneInversion f)
      (-(t ^ 2)⁻¹ * f t⁻¹ + t⁻¹ * (f' * -(t ^ 2)⁻¹)) t := by
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht
  have hcomp : HasDerivAt (fun y : ℝ => f y⁻¹) (f' * -(t ^ 2)⁻¹) t := hf.comp t hinv
  exact hinv.mul hcomp

/-- **The inversion anti-conjugates the scale generator**: `D(Jf) = -(Jf) - J(Df)`, i.e.
`J D J = -(D + 1)` on differentiable scale profiles. -/
theorem multiplicativeDeriv_weightOneInversion {f : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hf : DifferentiableAt ℝ f t⁻¹) :
    multiplicativeDeriv (weightOneInversion f) t
      = -weightOneInversion f t - weightOneInversion (multiplicativeDeriv f) t := by
  rw [multiplicativeDeriv, (hasDerivAt_weightOneInversion ht hf.hasDerivAt).deriv]
  unfold weightOneInversion multiplicativeDeriv
  field_simp
  ring

/-- **The scaling Hamiltonian commutes with the inversion**: `(D²+D)(Jf) = J((D²+D)f)` away
from `0`, since `J D J = -(D+1)` gives `J D(D+1) J = (-(D+1))(-D) = D(D+1)`. -/
theorem scalingHamiltonian_weightOneInversion {f : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hf : Differentiable ℝ f) (hDf : Differentiable ℝ (multiplicativeDeriv f)) :
    multiplicativeDeriv (multiplicativeDeriv (weightOneInversion f)) t
      + multiplicativeDeriv (weightOneInversion f) t
      = weightOneInversion
        (fun x => multiplicativeDeriv (multiplicativeDeriv f) x
          + multiplicativeDeriv f x) t := by
  have hJf := hasDerivAt_weightOneInversion ht (hf t⁻¹).hasDerivAt
  have hJDf := hasDerivAt_weightOneInversion ht (hDf t⁻¹).hasDerivAt
  have hg : HasDerivAt (fun y => -weightOneInversion f y
      - weightOneInversion (multiplicativeDeriv f) y)
      (-(-(t ^ 2)⁻¹ * f t⁻¹ + t⁻¹ * (deriv f t⁻¹ * -(t ^ 2)⁻¹))
        - (-(t ^ 2)⁻¹ * multiplicativeDeriv f t⁻¹
          + t⁻¹ * (deriv (multiplicativeDeriv f) t⁻¹ * -(t ^ 2)⁻¹))) t :=
    hJf.neg.sub hJDf
  have hEv : multiplicativeDeriv (weightOneInversion f) =ᶠ[nhds t]
      fun y => -weightOneInversion f y - weightOneInversion (multiplicativeDeriv f) y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (by simpa using ht : t ∈ ({(0 : ℝ)}ᶜ : Set ℝ))] with y hy
    exact multiplicativeDeriv_weightOneInversion hy (hf _)
  show t * deriv (multiplicativeDeriv (weightOneInversion f)) t
      + multiplicativeDeriv (weightOneInversion f) t = _
  rw [hEv.deriv_eq, hg.deriv, multiplicativeDeriv_weightOneInversion ht (hf t⁻¹)]
  unfold weightOneInversion multiplicativeDeriv
  field_simp
  ring

/-- **The Born swap preserves the seed dynamics**: the scaling Hamiltonian of the inverted
Gaussian seed is the inverted theta-cusp source, `(D²+D)(J g₀) = J h`. -/
theorem scalingHamiltonian_weightOneInversion_thetaCuspGaussian {t : ℝ} (ht : t ≠ 0) :
    multiplicativeDeriv (multiplicativeDeriv (weightOneInversion thetaCuspGaussian)) t
      + multiplicativeDeriv (weightOneInversion thetaCuspGaussian) t
      = weightOneInversion thetaCuspSeed t := by
  have hf : Differentiable ℝ thetaCuspGaussian := fun x =>
    (hasDerivAt_thetaCuspGaussian x).differentiableAt
  have hDf : Differentiable ℝ (multiplicativeDeriv thetaCuspGaussian) := fun x =>
    (hasDerivAt_multiplicativeDeriv_thetaCuspGaussian x).differentiableAt
  rw [scalingHamiltonian_weightOneInversion ht hf hDf]
  show t⁻¹ * (multiplicativeDeriv (multiplicativeDeriv thetaCuspGaussian) t⁻¹
      + multiplicativeDeriv thetaCuspGaussian t⁻¹) = t⁻¹ * thetaCuspSeed t⁻¹
  rw [multiplicativeDeriv_sq_add_apply_thetaCuspGaussian]

/-- The inversion moves the Gaussian seed itself: the swap preserves the Hamiltonian but
not the state. -/
theorem weightOneInversion_thetaCuspGaussian_ne :
    weightOneInversion thetaCuspGaussian 2 ≠ thetaCuspGaussian 2 := by
  unfold weightOneInversion thetaCuspGaussian
  have hpi : (3 : ℝ) ≤ 15 * Real.pi / 4 := by
    nlinarith [Real.pi_gt_three]
  have h2lt : (2 : ℝ) < Real.exp (15 * Real.pi / 4) := by
    calc (2 : ℝ) < 3 + 1 := by norm_num
      _ ≤ Real.exp 3 := Real.add_one_le_exp 3
      _ ≤ Real.exp (15 * Real.pi / 4) := Real.exp_le_exp.mpr hpi
  have hkey : 2 * Real.exp (-Real.pi * 2 ^ 2) < Real.exp (-Real.pi * (2⁻¹ : ℝ) ^ 2) := by
    calc 2 * Real.exp (-Real.pi * 2 ^ 2)
        < Real.exp (15 * Real.pi / 4) * Real.exp (-Real.pi * 2 ^ 2) :=
          mul_lt_mul_of_pos_right h2lt (Real.exp_pos _)
      _ = Real.exp (15 * Real.pi / 4 + -Real.pi * 2 ^ 2) := (Real.exp_add _ _).symm
      _ = Real.exp (-Real.pi * (2⁻¹ : ℝ) ^ 2) := by
          congr 1
          ring
  intro h
  linarith [hkey, h]

/-! ## Power profiles: the Mellin-symbol face of the swap -/

/-- The scale generator on power profiles: `D(t^{-w}) = -w · t^{-w}` on `t > 0`. -/
theorem multiplicativeDeriv_rpow {w t : ℝ} (ht : 0 < t) :
    multiplicativeDeriv (fun y : ℝ => y ^ (-w)) t = -w * t ^ (-w) := by
  rw [multiplicativeDeriv, (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).deriv,
    show -w - 1 = -w + -1 by ring, Real.rpow_add ht, Real.rpow_neg_one]
  field_simp

/-- **Power profiles are eigenvectors of the scaling Hamiltonian with the completed-zeta
polynomial eigenvalue**: `(D²+D)(t^{-w}) = w(w-1) · t^{-w}` on `t > 0`. -/
theorem scalingHamiltonian_rpow {w t : ℝ} (ht : 0 < t) :
    multiplicativeDeriv (multiplicativeDeriv (fun y : ℝ => y ^ (-w))) t
      + multiplicativeDeriv (fun y : ℝ => y ^ (-w)) t
      = w * (w - 1) * t ^ (-w) := by
  have hEv : multiplicativeDeriv (fun y : ℝ => y ^ (-w)) =ᶠ[nhds t]
      fun y => -w * y ^ (-w) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
    exact multiplicativeDeriv_rpow hy
  have hg : HasDerivAt (fun y : ℝ => -w * y ^ (-w)) (-w * (-w * t ^ (-w - 1))) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (-w)
  show t * deriv (multiplicativeDeriv fun y : ℝ => y ^ (-w)) t + _ = _
  rw [hEv.deriv_eq, hg.deriv, multiplicativeDeriv_rpow ht,
    show -w - 1 = -w + -1 by ring, Real.rpow_add ht, Real.rpow_neg_one]
  field_simp
  ring

/-- **The inversion exchanges the Dirichlet power profiles `w ↔ 1-w`**:
`J(t^{-w}) = t^{-(1-w)}` on `t > 0` — within one Hamiltonian eigenspace, since
`w(w-1) = (1-w)((1-w)-1)`. -/
theorem weightOneInversion_rpow {w t : ℝ} (ht : 0 < t) :
    weightOneInversion (fun y : ℝ => y ^ (-w)) t = t ^ (-(1 - w)) := by
  show t⁻¹ * (t⁻¹) ^ (-w) = t ^ (-(1 - w))
  have h1 : (t⁻¹) ^ (-w) = t ^ w := by
    rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]
  rw [h1, show -(1 - w) = -1 + w by ring, Real.rpow_add ht, Real.rpow_neg_one]

/-- The scaling-Hamiltonian eigenvalue is blind to the reflection: `w(w-1)` is invariant
under `w ↦ 1-w`. -/
theorem scalingHamiltonian_eigenvalue_reflect (w : ℝ) :
    w * (w - 1) = (1 - w) * ((1 - w) - 1) := by
  ring

end RHTower
