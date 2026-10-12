import GaloisForLFunctions.HTGeometry.LeeYangFirstZeroBudget

/-!
# Griffiths' first inequality with fields, and free magnetization dominance

For a finite Ising model with ferromagnetic couplings `J ≥ 0` and nonnegative fields `h ≥ 0`:

* `fieldMoment_nonneg`: every moment `Σ_D W(D) e^{Σ h_k σ_k} σ_A` is nonnegative. Both the bond
  factors `cosh J + σσ sinh J` and the site factors `cosh h + σ sinh h` expand into spin
  monomials with nonnegative coefficients.
* `tanh_mul_le_moment`: `⟨σ_k⟩ ≥ tanh h_k`. The exact identity
  `(σ − tanh h) e^{hσ} = σ / cosh h` reduces the claim to the moment of `σ_k` in the system with
  the field at `k` removed.
* `freeMagnetization_le`: for masses `c ≥ 0` in a field `w ≥ 0`, the magnetization
  `⟨Σ_k c_k σ_k⟩` is at least the independent-spin value `Σ_k c_k tanh(c_k w)`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.LeeYang

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The field factor `exp(Σ_k h_k σ_k)`. -/
def fieldFactor (h : V → ℝ) (D : Finset V) : ℝ := Real.exp (∑ k, h k * spin D k)

omit [Fintype V] in
theorem exp_mul_spin (x : ℝ) (D : Finset V) (k : V) :
    Real.exp (x * spin D k) = Real.sinh x * spin D k + Real.cosh x := by
  rw [← Real.cosh_add_sinh]
  by_cases hk : k ∈ D <;> simp [spin, hk, Real.cosh_neg, Real.sinh_neg]; ring

theorem fieldFactor_expand (h : V → ℝ) (D : Finset V) :
    fieldFactor h D = ∑ U ∈ (univ : Finset V).powerset,
      (∏ k ∈ U, Real.sinh (h k) * spin D k) * ∏ k ∈ univ \ U, Real.cosh (h k) := by
  rw [fieldFactor, Real.exp_sum, ← Finset.prod_add]
  exact Finset.prod_congr rfl fun k _ => exp_mul_spin _ D k

/-- **Griffiths' first inequality with nonnegative fields.** For ferromagnetic couplings and
nonnegative fields every unnormalized moment `Σ_D W(D) e^{Σ h_k σ_k} σ_A` is nonnegative. -/
theorem fieldMoment_nonneg (J : V → V → ℝ) (E : Finset (V × V)) (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2)
    (h : V → ℝ) (hh : ∀ k, 0 ≤ h k) (A : Finset V) :
    0 ≤ ∑ D : Finset V, isingWeight J E D * fieldFactor h D * ∏ k ∈ A, spin D k := by
  have hW : ∀ D : Finset V, isingWeight J E D =
      ∑ t ∈ E.powerset, (∏ p ∈ t, (Real.sinh (J p.1 p.2) * (spin D p.1 * spin D p.2))) *
        ∏ p ∈ E \ t, Real.cosh (J p.1 p.2) := by
    intro D
    rw [isingWeight, Real.exp_sum, ← Finset.prod_add]
    exact Finset.prod_congr rfl fun p _ => exp_bond_cosh _ D _ _
  simp_rw [hW, fieldFactor_expand, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun t ht => ?_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun U hU => ?_
  obtain ⟨B, hB⟩ := exists_prod_bond_eq t
  have ht' : t ⊆ E := Finset.mem_powerset.mp ht
  have e : ∀ D : Finset V,
      (∏ p ∈ t, (Real.sinh (J p.1 p.2) * (spin D p.1 * spin D p.2))) *
        (∏ p ∈ E \ t, Real.cosh (J p.1 p.2)) *
        ((∏ k ∈ U, Real.sinh (h k) * spin D k) * ∏ k ∈ univ \ U, Real.cosh (h k)) *
        ∏ k ∈ A, spin D k =
      (((∏ p ∈ t, Real.sinh (J p.1 p.2)) * ∏ p ∈ E \ t, Real.cosh (J p.1 p.2)) *
        ((∏ k ∈ U, Real.sinh (h k)) * ∏ k ∈ univ \ U, Real.cosh (h k))) *
        ∏ k ∈ symmDiff (symmDiff B U) A, spin D k := by
    intro D
    have h1 : ∏ p ∈ t, (Real.sinh (J p.1 p.2) * (spin D p.1 * spin D p.2)) =
        (∏ p ∈ t, Real.sinh (J p.1 p.2)) * ∏ p ∈ t, (spin D p.1 * spin D p.2) :=
      Finset.prod_mul_distrib
    have h2 : ∏ k ∈ U, (Real.sinh (h k) * spin D k) =
        (∏ k ∈ U, Real.sinh (h k)) * ∏ k ∈ U, spin D k := Finset.prod_mul_distrib
    rw [h1, h2, hB D, ← prod_spin_mul, ← prod_spin_mul]
    ring
  simp_rw [e, ← Finset.mul_sum]
  refine mul_nonneg (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p hp => ?_)
    (Finset.prod_nonneg fun p _ => (Real.cosh_pos _).le))
    (mul_nonneg (Finset.prod_nonneg fun k _ => Real.sinh_nonneg_iff.mpr (hh k))
      (Finset.prod_nonneg fun k _ => (Real.cosh_pos _).le))) (sum_prod_spin_nonneg _)
  exact Real.sinh_nonneg_iff.mpr (hJ p (ht' hp))

theorem fieldFactor_pos (h : V → ℝ) (D : Finset V) : 0 < fieldFactor h D := Real.exp_pos _

/-- Removing the field at one site. -/
theorem fieldFactor_eq_update (h : V → ℝ) (D : Finset V) (k : V) :
    fieldFactor h D = Real.exp (h k * spin D k) * fieldFactor (Function.update h k 0) D := by
  rw [fieldFactor, fieldFactor, ← Real.exp_add]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  simp only [Function.update_self, zero_mul, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [Fintype V] in
theorem sub_tanh_mul_exp (x : ℝ) (D : Finset V) (k : V) :
    (spin D k - Real.tanh x) * Real.exp (x * spin D k) = spin D k / Real.cosh x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  by_cases hk : k ∈ D
  · simp only [spin, hk, if_true]
    rw [show x * -1 = -x by ring, Real.exp_neg, ← Real.cosh_add_sinh]
    have hpos : Real.cosh x + Real.sinh x ≠ 0 := by
      rw [Real.cosh_add_sinh]; exact (Real.exp_pos x).ne'
    field_simp
    have := Real.cosh_sq_sub_sinh_sq x
    nlinarith [this]
  · simp only [spin, hk, if_false]
    rw [mul_one, ← Real.cosh_add_sinh]
    field_simp
    have := Real.cosh_sq_sub_sinh_sq x
    nlinarith [this]

/-- **Single-site magnetization bound.** In a ferromagnet with nonnegative fields, every spin's
magnetization is at least its free value: `⟨σ_k⟩ ≥ tanh h_k`. -/
theorem tanh_mul_le_moment (J : V → V → ℝ) (E : Finset (V × V)) (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2)
    (h : V → ℝ) (hh : ∀ k, 0 ≤ h k) (k : V) :
    Real.tanh (h k) * ∑ D : Finset V, isingWeight J E D * fieldFactor h D ≤
      ∑ D : Finset V, isingWeight J E D * fieldFactor h D * spin D k := by
  have hh' : ∀ j, 0 ≤ Function.update h k 0 j := fun j => by
    by_cases hj : j = k
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact hh j
  have hbase := fieldMoment_nonneg J E hJ (Function.update h k 0) hh' {k}
  simp only [Finset.prod_singleton] at hbase
  suffices hsuff : (0 : ℝ) ≤ ∑ D : Finset V, (isingWeight J E D * fieldFactor h D * spin D k -
      Real.tanh (h k) * (isingWeight J E D * fieldFactor h D)) by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsuff
    linarith
  have e : ∀ D : Finset V, isingWeight J E D * fieldFactor h D * spin D k -
      Real.tanh (h k) * (isingWeight J E D * fieldFactor h D) =
      (Real.cosh (h k))⁻¹ * (isingWeight J E D * fieldFactor (Function.update h k 0) D * spin D k) := by
    intro D
    rw [fieldFactor_eq_update h D k]
    have := sub_tanh_mul_exp (h k) D k
    have hc : Real.cosh (h k) ≠ 0 := (Real.cosh_pos _).ne'
    rw [div_eq_mul_inv] at this
    calc isingWeight J E D * (Real.exp (h k * spin D k) * fieldFactor (Function.update h k 0) D) *
          spin D k - Real.tanh (h k) * (isingWeight J E D * (Real.exp (h k * spin D k) *
          fieldFactor (Function.update h k 0) D))
        = isingWeight J E D * fieldFactor (Function.update h k 0) D *
            ((spin D k - Real.tanh (h k)) * Real.exp (h k * spin D k)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e, ← Finset.mul_sum]
  exact mul_nonneg (inv_nonneg.mpr (Real.cosh_pos _).le) hbase

/-- **Free magnetization dominance.** For a ferromagnet with masses `c_k ≥ 0` in a field `w ≥ 0`,
the magnetization `⟨Σ c_k σ_k⟩` is at least the independent-spin value `Σ c_k tanh(c_k w)`. -/
theorem freeMagnetization_le (J : V → V → ℝ) (E : Finset (V × V)) (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2)
    (c : V → ℝ) (hc : ∀ k, 0 ≤ c k) {w : ℝ} (hw : 0 ≤ w) :
    (∑ k, c k * Real.tanh (c k * w)) *
        ∑ D : Finset V, isingWeight J E D * fieldFactor (fun k => c k * w) D ≤
      ∑ D : Finset V, isingWeight J E D * fieldFactor (fun k => c k * w) D *
        ∑ k, c k * spin D k := by
  have hh : ∀ k, 0 ≤ c k * w := fun k => mul_nonneg (hc k) hw
  have hR : ∑ D : Finset V, isingWeight J E D * fieldFactor (fun k => c k * w) D *
        ∑ k, c k * spin D k =
      ∑ k, ∑ D : Finset V, c k * (isingWeight J E D * fieldFactor (fun k => c k * w) D * spin D k) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun D _ => by ring
  rw [hR, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  simp_rw [Finset.mul_sum]
  have := tanh_mul_le_moment J E hJ (fun k => c k * w) hh k
  have h2 := mul_le_mul_of_nonneg_left this (hc k)
  simp only [Finset.mul_sum] at h2
  calc ∑ D, c k * Real.tanh (c k * w) * (isingWeight J E D * fieldFactor (fun k => c k * w) D)
      = ∑ D, c k * (Real.tanh (c k * w) * (isingWeight J E D * fieldFactor (fun k => c k * w) D)) :=
        Finset.sum_congr rfl fun D _ => by ring
    _ ≤ ∑ D, c k * (isingWeight J E D * fieldFactor (fun k => c k * w) D * spin D k) := h2
    _ = _ := Finset.sum_congr rfl fun D _ => by ring

end

end GaloisForLFunctions.HTGeometry.LeeYang
