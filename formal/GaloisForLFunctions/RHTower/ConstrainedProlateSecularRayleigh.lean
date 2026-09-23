import GaloisForLFunctions.RHTower.ConstrainedProlateOperatorIdentification

/-!
# The secular ground vector has Rayleigh quotient the secular root

Testing the weak eigen-equation against the secular vector itself — legitimate, because that vector
lies in `ℓ²` and satisfies the constraint — turns `secularVector_lp_form_eigen` into the exact
Rayleigh identity

```text
∑ d_j v_j²  =  μ₀ ∑ v_j² .
```

This is the `≤` half of the operator identification in coordinates: the vector synthesised from `v`
in any Hilbert basis diagonalising the leakage lies in the constraint hyperplane and realises the
value `μ₀`, so the constrained ground eigenvalue is at most the secular root.
-/

noncomputable section

open Filter Set

namespace RHTower

variable {d ℓ : ℕ → ℝ}

/-- **The Rayleigh identity at the secular ground root.** -/
theorem tsum_mul_secularVector_sq_eq (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    (∑' j : ℕ, d j * secularVector d ℓ (infiniteSecularRoot d ℓ) j
        * secularVector d ℓ (infiniteSecularRoot d ℓ) j)
      = infiniteSecularRoot d ℓ
        * ∑' j : ℕ, secularVector d ℓ (infiniteSecularRoot d ℓ) j
            * secularVector d ℓ (infiniteSecularRoot d ℓ) j := by
  have hmem := memℓp_secularVector h01 h12 hd2 hsum hℓ0 hℓ1
  exact secularVector_lp_form_eigen h01 h12 hd2 hsum hℓ0 hℓ1
    (⟨secularVector d ℓ (infiniteSecularRoot d ℓ), hmem⟩ : lp (fun _ : ℕ => ℝ) 2)
    (secularVector_constraint h01 h12 hd2 hsum hℓ0 hℓ1)

end RHTower

end
