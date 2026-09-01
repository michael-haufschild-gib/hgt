import GaloisForLFunctions.HTGeometry.RittLogTowerWeight
import GaloisForLFunctions.HTGeometry.RittLogTowerRing

/-!
# The collapse of the affine tower as a polynomial identity

If the first `n` jets of the logarithmic seed are algebraically independent and the `n`-th jet is a
polynomial in them, the whole collapse is one identity in the polynomial ring:

`towerShift F = ρ^{-(n+1)}·F + defectPoly`.

The defect has weight at most `n`, so above that weight the comparison of the top layer is
homogeneous, and it produces a base relation with exponent `W − n − 1`, `W` the weight of `F`.  For
any weight other than `n + 1` that exponent is nonzero — Ritt's order-one form.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- The jets, as a family indexed by the variables. -/
noncomputable def jetFamily (Fr : RittFrame K L) (u : L) (n : ℕ) : Fin n → L :=
  fun j => Fr.d^[(j : ℕ)] u

theorem jetPrefixRing_eq_adjoin_range (Fr : RittFrame K L) (u : L) (n : ℕ) :
    Fr.jetPrefixRing u n = Algebra.adjoin K (Set.range (Fr.jetFamily u n)) := by
  rw [jetPrefixRing]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ), j.isLt, rfl⟩

/-- Every element of the jet prefix ring is the value of a polynomial at the jets. -/
theorem exists_mvPolynomial_of_mem_jetPrefixRing (Fr : RittFrame K L) (u : L) (n : ℕ)
    {x : L} (hx : x ∈ Fr.jetPrefixRing u n) :
    ∃ F : MvPolynomial (Fin n) K, aeval (Fr.jetFamily u n) F = x := by
  rw [Fr.jetPrefixRing_eq_adjoin_range u n, Algebra.adjoin_range_eq_range_aeval] at hx
  exact hx

/-- The polynomial representing the shift defect of the top level. -/
noncomputable def defectPoly (Fr : RittFrame K L) (b : K) (n : ℕ) : MvPolynomial (Fin n) K :=
  (∑ j : Fin n, C (Fr.logCoeff n (j : ℕ)) * X j) + C (Fr.logConst b n)

theorem aeval_defectPoly (Fr : RittFrame K L) (u : L) (b : K) (n : ℕ) :
    aeval (Fr.jetFamily u n) (Fr.defectPoly b n) = Fr.towerDefect u b n := by
  classical
  rw [defectPoly, towerDefect, map_add, map_sum, aeval_C]
  congr 1
  have hcoeff : ∀ j : Fin n, aeval (Fr.jetFamily u n) (C (Fr.logCoeff n (j : ℕ)) * X j)
      = algebraMap K L (Fr.logCoeff n (j : ℕ)) * Fr.d^[(j : ℕ)] u := by
    intro j
    rw [map_mul, aeval_C, aeval_X]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => hcoeff j),
    Fin.sum_univ_eq_sum_range (fun i => algebraMap K L (Fr.logCoeff n i) * Fr.d^[i] u) n]

theorem wLe_defectPoly (Fr : RittFrame K L) (b : K) (n : ℕ) :
    WLe n (Fr.defectPoly b n) n := by
  classical
  refine WLe.add ?_ (wLe_C (n := n) (Fr.logConst b n) _)
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      WLe n (C (Fr.logCoeff n (j : ℕ)) * X j : MvPolynomial (Fin n) K) n := by
    intro j _
    have h := (wLe_C (n := n) (Fr.logCoeff n (j : ℕ)) 0).mul (wLe_X (n := n) j)
    refine (by simpa using h : WLe n _ (jetWeight n j)).mono ?_
    simp only [jetWeight]
    omega
  exact Finset.sum_induction _ (fun F => WLe n F n) (fun _ _ => WLe.add) (wLe_zero _) hterm

/-- **The collapse, transported to the polynomial ring.** -/
theorem towerShift_eq_of_collapse (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F G : MvPolynomial (Fin n) K} {c : K}
    (hrel : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L c * aeval (Fr.jetFamily u n) F + aeval (Fr.jetFamily u n) G) :
    Fr.towerShift b n F = C c * F + G := by
  refine hind ?_
  have hleft : aeval (Fr.jetFamily u n) (Fr.towerShift b n F)
      = Fr.σ (aeval (Fr.jetFamily u n) F) := Fr.aeval_towerShift hu n F
  rw [hleft, hrel, map_add, map_mul, aeval_C]

/-- **The top weight layer of a collapse of the affine tower is a homogeneous base relation** whose
exponent is the weight of the collapsing polynomial minus `n + 1`. -/
theorem homogeneous_base_relation_of_collapse (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W) (hWn : n < W)
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = W) :
    Fr.ψ (coeff d F) = Fr.ρ ^ ((W : ℤ) - (n : ℤ) - 1) * coeff d F := by
  have hρ : (Fr.ρ : K) ≠ 0 := Fr.ρ_ne
  have hJ : (Fr.ρ : K) ^ (-((n : ℤ) + 1)) = (Fr.ρ ^ (n + 1))⁻¹ := by
    rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hcol' : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * aeval (Fr.jetFamily u n) F
        + aeval (Fr.jetFamily u n) (Fr.defectPoly b n) := by
    rw [hJ, Fr.aeval_defectPoly u b n]
    exact hcol
  have hpoly : Fr.towerShift b n F
      = C ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * F + Fr.defectPoly b n :=
    Fr.towerShift_eq_of_collapse hu hind hcol'
  have hGlt : WLt n (Fr.defectPoly b n) W :=
    fun e he => lt_of_le_of_lt (Fr.wLe_defectPoly b n e he) hWn
  have h := Fr.homogeneous_base_relation_of_towerShift b hF hGlt hpoly hd
  rw [h]
  congr 1
  rw [← zpow_natCast (Fr.ρ) W, ← zpow_add₀ hρ]
  congr 1
  ring

/-- **Ritt's order-one form from a collapse whose weight is not `n + 1`.** -/
theorem exists_rittForm_of_collapse_weight_ne (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W) (hWn : n < W) (hWne : W ≠ n + 1)
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = W) (hdne : coeff d F ≠ 0) :
    ∃ (w : K) (J : ℤ), w ≠ 0 ∧ J ≠ 0 ∧ Fr.ψ w = Fr.ρ ^ J * w := by
  refine ⟨coeff d F, (W : ℤ) - (n : ℤ) - 1, hdne, ?_,
    Fr.homogeneous_base_relation_of_collapse hu hind hF hWn hcol hd⟩
  intro h
  refine hWne ?_
  have : (W : ℤ) = (n : ℤ) + 1 := by omega
  exact_mod_cast this

theorem coeff_single_defectPoly (Fr : RittFrame K L) (b : K) {m : ℕ} (j : Fin (m + 1)) :
    coeff (Finsupp.single j 1) (Fr.defectPoly b (m + 1)) = Fr.logCoeff (m + 1) (j : ℕ) := by
  classical
  have hconst : coeff (Finsupp.single j 1) (C (Fr.logConst b (m + 1))
      : MvPolynomial (Fin (m + 1)) K) = 0 := by
    rw [coeff_C, if_neg]
    exact fun h => (Finsupp.single_ne_zero.mpr one_ne_zero) h.symm
  have hterm : ∀ i : Fin (m + 1),
      coeff (Finsupp.single j 1) (C (Fr.logCoeff (m + 1) (i : ℕ)) * X i)
        = if i = j then Fr.logCoeff (m + 1) (j : ℕ) else 0 := by
    intro i
    rw [coeff_C_mul, coeff_X]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg, mul_zero, if_neg h]
      exact fun hc => h (Finsupp.single_left_injective one_ne_zero hc)
  rw [defectPoly, coeff_add, hconst, add_zero, coeff_sum,
    Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j]
  simp

/-- **A collapse of weight at most `n` gives an affine base relation.**  The defect's top weight
layer is its nonzero subdiagonal coefficient, so the comparison at the monomial `X_{n-1}` cannot be
homogeneous. -/
theorem exists_affine_base_relation_of_collapse_weight_le [CharZero K] (Fr : RittFrame K L)
    {u : L} {b : K} (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hdρ : Fr.dK Fr.ρ ≠ 0) {m : ℕ}
    (hind : AlgebraicIndependent K (Fr.jetFamily u (m + 1)))
    {F : MvPolynomial (Fin (m + 1)) K} {W : ℕ} (hF : WLe (m + 1) F W) (hWn : W ≤ m + 1)
    (hcol : Fr.σ (aeval (Fr.jetFamily u (m + 1)) F)
      = algebraMap K L ((Fr.ρ ^ (m + 2))⁻¹) * aeval (Fr.jetFamily u (m + 1)) F
        + Fr.towerDefect u b (m + 1)) :
    ∃ (w h : K) (J : ℤ), h ≠ 0 ∧ Fr.ψ w = Fr.ρ ^ J * w + h := by
  classical
  have hρ : (Fr.ρ : K) ≠ 0 := Fr.ρ_ne
  have hsub : Fr.logCoeff (m + 1) m ≠ 0 := by
    rw [Fr.logCoeff_subdiag m]
    have hc : (((m + 2).choose 2 : ℕ) : K) ≠ 0 := by
      have hpos : 0 < (m + 2).choose 2 := Nat.choose_pos (by omega)
      exact Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc) (inv_ne_zero (pow_ne_zero _ hρ))) hdρ
  have hJ : (Fr.ρ : K) ^ (-((m : ℤ) + 2)) = (Fr.ρ ^ (m + 2))⁻¹ := by
    rw [zpow_neg, show ((m : ℤ) + 2) = ((m + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hcol' : Fr.σ (aeval (Fr.jetFamily u (m + 1)) F)
      = algebraMap K L ((Fr.ρ : K) ^ (-((m : ℤ) + 2))) * aeval (Fr.jetFamily u (m + 1)) F
        + aeval (Fr.jetFamily u (m + 1)) (Fr.defectPoly b (m + 1)) := by
    rw [hJ, Fr.aeval_defectPoly u b (m + 1)]
    exact hcol
  have hpoly : Fr.towerShift b (m + 1) F
      = C ((Fr.ρ : K) ^ (-((m : ℤ) + 2))) * F + Fr.defectPoly b (m + 1) :=
    Fr.towerShift_eq_of_collapse hu hind hcol'
  set jm : Fin (m + 1) := ⟨m, by omega⟩ with hjm
  have hd : Finsupp.weight (jetWeight (m + 1)) (Finsupp.single jm 1) = m + 1 := by
    rw [Finsupp.weight_single]
    simp [jetWeight, hjm]
  have h := Fr.base_relation_of_towerShift b (hF.mono hWn) hpoly hd
  rw [Fr.coeff_single_defectPoly b jm] at h
  refine ⟨coeff (Finsupp.single jm 1) F, Fr.ρ ^ (m + 1) * Fr.logCoeff (m + 1) (jm : ℕ),
    -((m : ℤ) + 2) + ((m + 1 : ℕ) : ℤ), ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ hρ) (by simpa [hjm] using hsub)
  · rw [h, ← zpow_natCast (Fr.ρ) (m + 1), ← zpow_add₀ hρ]

/-- **In the surviving case the top weight coefficients of the collapsing polynomial are fixed by
the base map.** -/
theorem psi_fixed_of_collapse_top (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K} (hF : WLe n F (n + 1))
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = n + 1) :
    Fr.ψ (coeff d F) = coeff d F := by
  have h := Fr.homogeneous_base_relation_of_collapse hu hind hF (by omega) hcol hd
  have hz : (((n + 1 : ℕ) : ℤ) - (n : ℤ) - 1) = 0 := by push_cast; ring
  rw [hz, zpow_zero, one_mul] at h
  exact h

/-- **The top weight coefficients are derivation constants, or Ritt's form follows.** -/
theorem dK_eq_zero_of_collapse_top (Fr : RittFrame K L) {u : L} {b : K} (q : K)
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K} (hF : WLe n F (n + 1))
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = n + 1)
    (hne : coeff d F ≠ 0) :
    Fr.dK (coeff d F) = 0 ∨
      ∃ (w : K) (I J : ℤ), w ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ w = q ^ I * Fr.ρ ^ J * w :=
  psi_fixed_dichotomy Fr hne (Fr.psi_fixed_of_collapse_top hu hind hF hcol hd)

end RittFrame

end GaloisForLFunctions.HTGeometry
