import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistance
import GaloisForLFunctions.RHTower.ConstrainedProlateGroundDistanceCCM
import GaloisForLFunctions.RHTower.ConstrainedProlateOperatorIdentification

/-!
# The full `ℓ²` ground-vector metric law for the CCM Fuchs family

The two vectors compared are *constructed* here rather than assumed: the seed is finitely
supported, so it lies in `ℓ²` outright, and the exact eigenvector lies in `ℓ²` by the tail estimate
at the constrained root.  With both vectors built, the head-alignment and tail-collapse inputs are
supplied by the corresponding theorems for the Fuchs family, leaving no analytic hypothesis beyond
the coordinate data itself.
-/

open Filter Set GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The seed as a genuine `ℓ²` vector -/

theorem summable_twoModeSeedFun_sq (ℓ : ℕ → ℝ) :
    Summable fun j => twoModeSeedFun ℓ j ^ 2 := by
  refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) ?_
  intro j hj
  rw [twoModeSeedFun_eq_zero hj]
  exact zero_pow two_ne_zero

theorem memℓp_twoModeSeedFun (ℓ : ℕ → ℝ) : Memℓp (twoModeSeedFun ℓ) 2 :=
  memℓp_two_of_sq_summable (summable_twoModeSeedFun_sq ℓ)

/-- The two-mode seed as an `ℓ²` vector. -/
def twoModeSeedLp (ℓ : ℕ → ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨twoModeSeedFun ℓ, memℓp_twoModeSeedFun ℓ⟩

@[simp] theorem twoModeSeedLp_coeFn (ℓ : ℕ → ℝ) :
    ((twoModeSeedLp ℓ : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) = twoModeSeedFun ℓ := rfl

/-! ## The eigenvector as a genuine `ℓ²` vector -/

open Classical in
/-- The exact constrained eigenvector as an `ℓ²` vector, defined to be zero off the range where
square-summability holds. -/
def secularLp (d ℓ : ℕ → ℝ) (μ : ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  if h : Memℓp (secularVector d ℓ μ) 2 then ⟨secularVector d ℓ μ, h⟩ else 0

theorem secularLp_coeFn {d ℓ : ℕ → ℝ} {μ : ℝ} (h : Memℓp (secularVector d ℓ μ) 2) :
    ((secularLp d ℓ μ : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) = secularVector d ℓ μ := by
  rw [secularLp, dif_pos h]

/-! ## Membership and summability for the CCM family -/

theorem ccm_memℓp {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop,
      Memℓp (secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)) 2 := by
  filter_upwards [ccm_struct hA hC hgrow, hsum, ccm_l0_ne_zero hl0, ccm_l1_ne_zero hl1]
    with lam hst hsm h0 h1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  exact memℓp_secularVector h01 h12 hd2 hsm h0 h1

theorem ccm_summable_secularVector_sq {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop, Summable fun j =>
      secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam) j ^ 2 := by
  filter_upwards [ccm_struct hA hC hgrow, hsum, ccm_l0_ne_zero hl0, ccm_l1_ne_zero hl1]
    with lam hst hsm h0 h1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hroot : ccmFuchsRoot A ℓ lam = infiniteSecularRoot (ccmFuchsScale A lam) (ℓ lam) := rfl
  have hlt : ccmFuchsRoot A ℓ lam < ccmFuchsScale A lam 2 := by
    rw [hroot]
    linarith [hrmem.2]
  exact (summable_nat_add_iff
      (f := fun j => secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam) j ^ 2)
      2).mp
    (summable_secularVector_sq_tail hd2 hsm hlt)

/-! ## The composed law -/

/-- **The exact constrained ground vector converges to the two-mode seed in `ℓ²`, for the CCM
Fuchs family.**  Both vectors are constructed, and every structural, nonvanishing, membership,
summability, alignment and tail hypothesis is discharged from the family data.  What remains
assumed is only the coordinate data: square-summability, the Bessel bound, and the two coordinate
limits — the last being the open prolate-to-Hermite gate. -/
theorem ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => min
        (‖(‖secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹
            • secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ 2)
        (‖(‖secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹
            • secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ 2))
      atTop (nhds 0) := by
  have ha0 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by positivity
  have ha1 : (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ≠ 0 := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  refine tendsto_min_norm_lp_normalize_sub_twoModeSeed
    (V := fun lam => secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam))
    (G := fun lam => twoModeSeedLp (ℓ lam))
    (D := fun lam => ccmFuchsScale A lam) (L := ℓ) (M := ccmFuchsRoot A ℓ)
    ((ccm_memℓp hA hC hgrow hsum hl0 hl1).mono fun lam h => secularLp_coeFn h)
    (Eventually.of_forall fun lam => twoModeSeedLp_coeFn (ℓ lam))
    (ccm_summable_secularVector_sq hA hC hgrow hsum hl0 hl1)
    (ccm_secularVector_zero_ne_zero hA hC hgrow hsum hl0 hl1)
    (ccm_l0_ne_zero hl0)
    (secularVector_head_seed_defect_tendsto_zero ha0 ha1
      (ccm_struct hA hC hgrow) hsum hbessel (ccm_tail hA) hl0 hl1)
    (secularVector_tail_fraction_tendsto_zero ha0 ha1
      (ccm_struct hA hC hgrow) hsum hbessel (ccm_tail hA) hl0 hl1)

end RHTower

end
