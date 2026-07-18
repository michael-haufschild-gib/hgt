import Mathlib.Analysis.InnerProductSpace.l2Space
import GaloisForLFunctions.RHTower.ConstrainedProlateSecularVector

/-!
# Operator identification: constrained eigenvalues are exactly the secular roots

The constrained eigenvalue problem for the diagonal leakage operator `B e_j = d_j e_j` on the
hyperplane `⟨·, ℓ⟩ = 0` is characterized in both directions.

*Forward*: the secular vector `v_j = ℓ_j/(d_j − μ_0)` at the exact ground root lies in `ℓ²`, is
orthogonal to the constraint vector, and satisfies the rank-one-perturbed eigen-system
`d_j v_j = μ_0 v_j + ℓ_j`; tested against any `ℓ²` vector orthogonal to the constraint, the
diagonal action reduces to multiplication by `μ_0` — the weak form of the compressed
eigenvalue equation, on genuine `lp 2` vectors.

*Converse*: any nonzero square-summable solution of the span-form eigen-system
`d_j v_j = μ v_j + c·ℓ_j` in the first spectral gap that satisfies the constraint forces the
secular equation `F(μ) = 0` — the coordinates are determined up to scale, and pairing with the
constraint collapses to `c·F(μ)`.

Together with the existence, uniqueness, and interlacing theory of the secular root, this
closes the equivalence between the cards' operator-form phrasing (eigenvalues of the compressed
leakage) and the secular formulation in which the transfer theorems are proved.
-/

open Filter Set

namespace RHTower

variable {d ℓ : ℕ → ℝ}

/-- Square-summability puts a real sequence in `ℓ²`. -/
theorem memℓp_two_of_sq_summable {f : ℕ → ℝ} (hf : Summable fun j => f j ^ 2) :
    Memℓp f 2 := by
  apply memℓp_gen
  refine hf.congr fun i => ?_
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by simp, Real.rpow_natCast,
    Real.norm_eq_abs, sq_abs]

/-- The real `ℓ²` inner product is the series of coordinate products. -/
theorem lp_inner_eq_tsum_mul (f g : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ f g = ∑' j : ℕ, f j * g j := by
  rw [lp.inner_eq_tsum]
  exact tsum_congr fun j => by simp [RCLike.inner_apply, mul_comm]

/-- No pole of the secular function meets the first spectral gap. -/
theorem secular_pole_ne (h12 : d 1 < d 2) (hd2 : ∀ j, d 2 ≤ d (j + 2))
    {μ : ℝ} (hμ : μ ∈ Set.Ioo (d 0) (d 1)) (j : ℕ) : d j - μ ≠ 0 := by
  match j with
  | 0 => exact ne_of_lt (by linarith [hμ.1])
  | 1 => exact ne_of_gt (by linarith [hμ.2])
  | (m + 2) => exact ne_of_gt (by linarith [hd2 m, hμ.2])

/-- The exact eigenvector is square-summable: it is a genuine `ℓ²` vector. -/
theorem memℓp_secularVector (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    Memℓp (secularVector d ℓ (infiniteSecularRoot d ℓ)) 2 := by
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  apply memℓp_two_of_sq_summable
  exact (summable_nat_add_iff
      (f := fun j => secularVector d ℓ (infiniteSecularRoot d ℓ) j ^ 2) 2).mp
    (summable_secularVector_sq_tail hd2 hsum (by linarith [hrmem.2]))

/-- **Forward direction, `ℓ²` form.**  The exact eigenvector is orthogonal to the constraint
vector inside `lp 2`. -/
theorem secularVector_lp_orthogonal (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    inner ℝ (⟨ℓ, memℓp_two_of_sq_summable hsum⟩ : lp (fun _ : ℕ => ℝ) 2)
      (⟨secularVector d ℓ (infiniteSecularRoot d ℓ),
        memℓp_secularVector h01 h12 hd2 hsum hℓ0 hℓ1⟩ : lp (fun _ : ℕ => ℝ) 2) = 0 := by
  rw [lp_inner_eq_tsum_mul]
  exact secularVector_constraint h01 h12 hd2 hsum hℓ0 hℓ1

/-- **Forward direction, weak eigen-equation.**  Tested against any `ℓ²` vector annihilated by
the constraint, the diagonal action on the exact eigenvector is multiplication by the ground
root: the compressed operator equation in form sense. -/
theorem secularVector_lp_form_eigen (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0)
    (w : lp (fun _ : ℕ => ℝ) 2) (hw : (∑' j : ℕ, ℓ j * w j) = 0) :
    (∑' j : ℕ, d j * secularVector d ℓ (infiniteSecularRoot d ℓ) j * w j)
      = infiniteSecularRoot d ℓ *
        ∑' j : ℕ, secularVector d ℓ (infiniteSecularRoot d ℓ) j * w j := by
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  have hne := secular_pole_ne h12 hd2 hrmem
  have hsumvw : Summable fun j : ℕ =>
      secularVector d ℓ (infiniteSecularRoot d ℓ) j * w j := by
    have h := lp.summable_inner (𝕜 := ℝ)
      (⟨secularVector d ℓ (infiniteSecularRoot d ℓ),
        memℓp_secularVector h01 h12 hd2 hsum hℓ0 hℓ1⟩ : lp (fun _ : ℕ => ℝ) 2) w
    refine h.congr fun j => ?_
    simp [RCLike.inner_apply, mul_comm]
  have hsumlw : Summable fun j : ℕ => ℓ j * w j := by
    have h := lp.summable_inner (𝕜 := ℝ)
      (⟨ℓ, memℓp_two_of_sq_summable hsum⟩ : lp (fun _ : ℕ => ℝ) 2) w
    refine h.congr fun j => ?_
    simp [RCLike.inner_apply, mul_comm]
  have hterm : ∀ j : ℕ, d j * secularVector d ℓ (infiniteSecularRoot d ℓ) j * w j
      = infiniteSecularRoot d ℓ *
          (secularVector d ℓ (infiniteSecularRoot d ℓ) j * w j) + ℓ j * w j := by
    intro j
    rw [show d j * secularVector d ℓ (infiniteSecularRoot d ℓ) j
        = infiniteSecularRoot d ℓ * secularVector d ℓ (infiniteSecularRoot d ℓ) j + ℓ j
      from secularVector_eigen j (hne j)]
    ring
  rw [tsum_congr hterm,
    Summable.tsum_add (hsumvw.mul_left (infiniteSecularRoot d ℓ)) hsumlw,
    tsum_mul_left, hw, add_zero]

/-- **Converse direction.**  Any nonzero solution of the span-form constrained eigen-system in
the first spectral gap forces the secular equation: the constrained spectrum in `(d_0, d_1)` is
exactly the secular root set. -/
theorem infiniteSecular_eq_zero_of_constrained_eigen (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    {μ c : ℝ} (hμ : μ ∈ Set.Ioo (d 0) (d 1)) {v : ℕ → ℝ}
    (heig : ∀ j, d j * v j = μ * v j + c * ℓ j)
    (hconstraint : (∑' j : ℕ, ℓ j * v j) = 0)
    (hvne : v ≠ 0) :
    infiniteSecular d ℓ μ = 0 := by
  have hne := secular_pole_ne h12 hd2 hμ
  have hv : ∀ j, v j = c * ℓ j / (d j - μ) := by
    intro j
    have h2 : (d j - μ) * v j = c * ℓ j := by
      rw [sub_mul]
      linarith [heig j]
    rw [eq_div_iff (hne j), mul_comm]
    exact h2
  rcases eq_or_ne c 0 with hc0 | hcne
  · exfalso
    apply hvne
    funext j
    rw [hv j, hc0]
    simp
  · have hall : Summable (fun j : ℕ => ℓ j ^ 2 / (d j - μ)) :=
      (summable_nat_add_iff (f := fun j => ℓ j ^ 2 / (d j - μ)) 2).mp
        (summable_infiniteSecularTail hd2 hsum (by linarith [hμ.2]))
    have hcongr : ∀ j : ℕ, ℓ j * v j = c * (ℓ j ^ 2 / (d j - μ)) := by
      intro j
      rw [hv j]
      field_simp
    have h0 : (∑' j : ℕ, ℓ j * v j) = c * infiniteSecular d ℓ μ := by
      rw [tsum_congr hcongr, tsum_mul_left, infiniteSecular_eq_tsum hall]
    have hzero : c * infiniteSecular d ℓ μ = 0 := by
      rw [← h0, hconstraint]
    exact (mul_eq_zero.mp hzero).resolve_left hcne

end RHTower
