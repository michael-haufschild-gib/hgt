import GaloisForLFunctions.HTGeometry.LaurentCoefficientEulerDerivation
import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian

/-!
# The leading term of an output-jet Jacobian over a Laurent layer

Let `K((t))` carry a time derivation `δ` and coordinate derivations `∂₀,…,∂ₙ₊₁` whose effect on
boundary coefficients is the following: `δ` sends a series with boundary coefficient `c` in degree
`d` to one with boundary coefficient `δc + d a₀ c` in the same degree, the lower `∂ⱼ` act on the
boundary coefficient, and the terminal `∂` multiplies it by `κ d` while raising the degree by `N`.
This is the shape of the derivations of a cascade layer `X = t^(-N)` when the logarithmic velocity
of `X` has order zero.

Then for `Y` with boundary coefficient `h ≠ 0` in degree `d ≠ 0`, the boundary coefficient of the
output-jet Jacobian `det(∂ⱼ δⁱ Y)` is, up to sign, `κ d h^(n+2)` times the lower output-jet
Jacobian of

`U = δh/h + d a₀`

in `K`.  The boundary coefficients of the iterates `δⁱY` are the twisted iterates `(δ + d a₀)ⁱ h`,
which are `h` times the Bell polynomials of `U`; the bordered matrix they form is the
terminal-scaled Jacobian, whose determinant the Bell row reduction computes exactly.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- The twisted iterates `(δ + λ)ᵐ h` are `h` times the Bell polynomials of `U = δh/h + λ`. -/
theorem twisted_iterate_eq_mul_bellCore (δ : Derivation ℂ K K) (lam h : K) (hh : h ≠ 0) :
    ∀ m : ℕ, ((fun x => δ x + lam * x)^[m]) h =
      h * aeval (fun i : Fin m => ((δ : K → K)^[(i : ℕ)]) (δ h / h + lam)) (bellCore m) := by
  intro m
  induction m with
  | zero => simp [bellCore_zero]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [derivation_aeval_eq_sum_pderiv]
      have hjet (j : Fin m) :
          δ (((δ : K → K)^[(j : ℕ)]) (δ h / h + lam)) =
            ((δ : K → K)^[(j : ℕ) + 1]) (δ h / h + lam) :=
        (derivation_iterate_succ δ (j : ℕ) _).symm
      simp_rw [hjet]
      rw [aeval_bellCore_succ_derivationIterate]
      field_simp
      ring

/-- The same identity in the common Bell frame of the output Jacobian. -/
theorem twisted_iterate_succ_eq_mul_bellValue (δ : Derivation ℂ K K) (lam h : K) (hh : h ≠ 0)
    (n : ℕ) (r : Fin (n + 1)) :
    ((fun x => δ x + lam * x)^[(r : ℕ) + 1]) h =
      h * derivationBellValue δ (δ h / h + lam) n r := by
  have hb := twisted_iterate_eq_mul_bellCore δ lam h hh ((r : ℕ) + 1)
  simpa [derivationBellValue, bellAt, MvPolynomial.aeval_rename, Function.comp_def] using hb

/-- **Leading term of an output-jet Jacobian.**  Under the boundary-coefficient laws of a cascade
layer, a nonzero lower output-jet Jacobian of `U = δh/h + d a₀` in the coefficient field forces a
nonzero output-jet Jacobian of `Y` over the Laurent layer. -/
theorem outputJacobian_det_ne_zero_of_hasLead {n : ℕ}
    (δK : Derivation ℂ K K) (pK : Fin (n + 2) → Derivation ℂ K K)
    (δL : LaurentSeries K → LaurentSeries K)
    (pL : Fin (n + 2) → LaurentSeries K → LaurentSeries K)
    (a₀ κ : K) (N : ℤ)
    (hδ : ∀ (f : LaurentSeries K) (d : ℤ) (c : K), HasLead f d c →
      HasLead (δL f) d (δK c + (d : K) * a₀ * c))
    (hlow : ∀ (j : Fin (n + 1)) (f : LaurentSeries K) (d : ℤ) (c : K), HasLead f d c →
      HasLead (pL j.castSucc f) d (pK j.castSucc c))
    (hlast : ∀ (f : LaurentSeries K) (d : ℤ) (c : K), HasLead f d c →
      HasLead (pL (Fin.last (n + 1)) f) (d + N) (κ * ((d : K) * c)))
    {Y : LaurentSeries K} {d : ℤ} {h : K} (hY : HasLead Y d h)
    (hh : h ≠ 0) (hκ : κ ≠ 0) (hd : (d : K) ≠ 0)
    (hlower : (derivationLowerJetJacobian δK n pK (δK h / h + (d : K) * a₀)).det ≠ 0) :
    (Matrix.of fun i j : Fin (n + 2) => pL j ((δL^[(i : ℕ)]) Y)).det ≠ 0 := by
  classical
  set lam : K := (d : K) * a₀ with hlam
  set U : K := δK h / h + lam with hU
  let tw : K → K := fun x => δK x + lam * x
  have hiter : ∀ r : ℕ, HasLead ((δL^[r]) Y) d ((tw^[r]) h) := by
    intro r
    induction r with
    | zero => simpa using hY
    | succ r ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have h1 := hδ _ _ _ ih
        simpa only [tw, hlam, mul_assoc] using h1
  have hbell : ∀ r : Fin (n + 1), (tw^[(r : ℕ) + 1]) h =
      h * derivationBellValue δK U n r := fun r =>
    twisted_iterate_succ_eq_mul_bellValue δK lam h hh n r
  let L0 : Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
    terminalScaledJacobianMatrix h (κ * ((d : K) * h)) (fun c => pK c.castSucc h)
      (derivationBellValue δK U n) (derivationBellValueJacobian δK n pK U)
  let a : Fin (n + 2) → ℤ := fun _ => d
  let b : Fin (n + 2) → ℤ := Fin.lastCases N (fun _ => 0)
  have hM : ∀ i j, HasLead ((Matrix.of fun i j : Fin (n + 2) => pL j ((δL^[(i : ℕ)]) Y)) i j)
      (a i + b j) (L0 i j) := by
    intro i j
    refine Fin.lastCases ?_ (fun c => ?_) j
    · -- terminal column
      simp only [a, b, Fin.lastCases_last]
      refine Fin.cases ?_ (fun r => ?_) i
      · have hl := hlast _ _ _ (hiter 0)
        simpa [L0, terminalScaledJacobianMatrix] using hl
      · have hl' := hlast _ _ _ (hiter ((r : ℕ) + 1))
        rw [hbell r] at hl'
        convert hl' using 1
        · simp
        · simp only [L0, terminalScaledJacobianMatrix, Fin.cases_succ, Fin.lastCases_last]
          ring
    · -- lower columns
      simp only [a, b, Fin.lastCases_castSucc, add_zero]
      refine Fin.cases ?_ (fun r => ?_) i
      · have hl := hlow c _ _ _ (hiter 0)
        simpa [L0, terminalScaledJacobianMatrix] using hl
      · have hl := hlow c _ _ _ (hiter ((r : ℕ) + 1))
        rw [hbell r, Derivation.leibniz] at hl
        convert hl using 1
        · simp
        · simp only [L0, terminalScaledJacobianMatrix, Fin.cases_succ, Fin.lastCases_castSucc,
            derivationBellValueJacobian, smul_eq_mul]
  have hL0 : L0.det ≠ 0 := by
    simp only [L0]
    rw [terminalScaledJacobianMatrix_det, derivationBellValueJacobian_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero hκ (mul_ne_zero hd hh))) (pow_ne_zero _ hh)) hlower
  exact det_ne_zero_of_hasLead _ a b L0 hM hL0

end

end GaloisForLFunctions.HTGeometry
