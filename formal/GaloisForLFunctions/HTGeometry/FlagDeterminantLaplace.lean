import GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity
import GaloisForLFunctions.HTGeometry.PermutohedralScheduleConservation

/-!
# The ordered flag determinant and complete monotonicity

The increment map `u ↦ (u_1, u_1 + u_2, …, u_1 + ⋯ + u_r)` has a unipotent lower-triangular matrix,
so it preserves Lebesgue measure and maps the positive orthant onto the open flag chamber
`𝓕_r = {0 < t_1 < ⋯ < t_r}` `(AFD.2)`.  In increments `z t_r + Σ_j c_j t_j = Σ_k (z + S_k) u_k`
with suffix sums `S_k = Σ_{j ≥ k} c_j` `(AFD.4)`, so the flag integral of
`e^{-z t_r} Π_j e^{-c_j t_j}` is `Π_k (z + S_k)⁻¹`.  Alternating over schedules gives the ordered
flag-determinant representation of the full schedule alternant
`R_r(z;λ) = ∫_{𝓕_r} e^{-z t_r} det(e^{-λ_i t_j}) dt` `(AFD.3)`.

For distinct positive grades `det(e^{-λ_i t_j})/Δ_r > 0` on the chamber, the integrand is dominated
by `r!/|Δ_r| · t_r^m e^{-a t_r}` (integrable through the increment map), and differentiation under
the integral gives `(-1)^m (d/dz)^m (P_r/D_r)(z) = ∫_{𝓕_r} t_r^m e^{-z t_r} det/Δ_r dt > 0` for
`z > 0`: the Weyl-divided response is completely monotone `(AFD.6)`.
-/

open MeasureTheory Filter Topology Finset
open MvPolynomial (aeval)

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

/-! ### The increment map -/

/-- The open flag chamber `0 < t_1 < ⋯ < t_r` `(AFD.2)`. -/
def flagChamber (r : ℕ) : Set (Fin r → ℝ) := {t | (∀ i, 0 < t i) ∧ StrictMono t}

/-- The positive orthant. -/
def orthant (r : ℕ) : Set (Fin r → ℝ) := Set.pi Set.univ fun _ => Set.Ioi 0

/-- The lower-triangular matrix of the increment map. -/
def partialSumMatrix (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun j i => if i ≤ j then 1 else 0

theorem det_partialSumMatrix (r : ℕ) : (partialSumMatrix r).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [partialSumMatrix]
  · intro i j hij
    simp only [partialSumMatrix, Matrix.of_apply]
    rw [if_neg]
    exact not_le.2 hij

theorem det_toLin_partialSumMatrix_ne (r : ℕ) :
    LinearMap.det (Matrix.toLin' (partialSumMatrix r)) ≠ 0 := by
  rw [LinearMap.det_toLin', det_partialSumMatrix]; exact one_ne_zero

/-- The increment map as a linear equivalence. -/
def partialSumEquiv (r : ℕ) : (Fin r → ℝ) ≃ₗ[ℝ] (Fin r → ℝ) :=
  LinearMap.equivOfDetNeZero _ (det_toLin_partialSumMatrix_ne r)

theorem partialSumEquiv_apply (r : ℕ) (u : Fin r → ℝ) (j : Fin r) :
    partialSumEquiv r u j = ∑ i ∈ Iic j, u i := by
  show Matrix.toLin' (partialSumMatrix r) u j = _
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp only [partialSumMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext i
  simp

/-- The increment map as a measurable equivalence. -/
def partialSumMeas (r : ℕ) : (Fin r → ℝ) ≃ᵐ (Fin r → ℝ) :=
  (partialSumEquiv r).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem partialSumMeas_apply (r : ℕ) (u : Fin r → ℝ) : partialSumMeas r u = partialSumEquiv r u :=
  rfl

/-- **The increment map preserves Lebesgue measure** (its matrix is unipotent). -/
theorem measurePreserving_partialSum (r : ℕ) :
    MeasurePreserving (partialSumMeas r) volume volume := by
  refine ⟨(partialSumMeas r).measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin r → ℝ))
    (det_toLin_partialSumMatrix_ne r)
  rw [LinearMap.det_toLin', det_partialSumMatrix, inv_one, abs_one, ENNReal.ofReal_one,
    one_smul] at h
  exact h

theorem preimage_partialSum_flag (r : ℕ) : partialSumMeas r ⁻¹' flagChamber r = orthant r := by
  ext u
  simp only [Set.mem_preimage, flagChamber, orthant, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioi, partialSumMeas_apply, partialSumEquiv_apply]
  constructor
  · rintro ⟨hpos, hmono⟩ i
    cases r with
    | zero => exact i.elim0
    | succ n =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have := hpos 0
        rwa [show Iic (0 : Fin (n + 1)) = {0} by ext; simp,
          sum_singleton] at this
      · have h := hmono (Fin.castSucc_lt_succ (i := j))
        rw [partialSumEquiv_apply, partialSumEquiv_apply,
          show Iic j.succ = insert j.succ (Iic j.castSucc) by
          ext k; simp only [mem_Iic, mem_insert]; constructor
          · intro hk; rcases lt_or_eq_of_le hk with h | h
            · right; exact Fin.le_castSucc_iff.2 h
            · left; exact h
          · rintro (h | h)
            · exact h.le
            · exact h.trans (Fin.castSucc_le_succ j),
          sum_insert (by simp)] at h
        linarith
  · intro hu
    refine ⟨fun j => sum_pos (fun i _ => hu i) ⟨j, mem_Iic.2 le_rfl⟩, fun a b hab => ?_⟩
    have hsub : Iic a ⊆ Iic b := Iic_subset_Iic.2 hab.le
    show partialSumEquiv r u a < partialSumEquiv r u b
    rw [partialSumEquiv_apply, partialSumEquiv_apply, ← sum_sdiff hsub]
    have hne : (Iic b \ Iic a).Nonempty := ⟨b, by simp [not_le.2 hab]⟩
    linarith [sum_pos (fun i _ => hu i) hne]

theorem measurableEmbedding_partialSum (r : ℕ) : MeasurableEmbedding (partialSumMeas r) :=
  (partialSumMeas r).measurableEmbedding

/-- Change of variables onto the flag chamber. -/
theorem setIntegral_flag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (g : (Fin r → ℝ) → E) :
    ∫ t in flagChamber r, g t = ∫ u in orthant r, g (partialSumEquiv r u) := by
  rw [← (measurePreserving_partialSum r).setIntegral_preimage_emb
    (measurableEmbedding_partialSum r), preimage_partialSum_flag]
  rfl

theorem integrableOn_flag_iff {E : Type*} [NormedAddCommGroup E] (r : ℕ) (g : (Fin r → ℝ) → E) :
    IntegrableOn g (flagChamber r) ↔
      IntegrableOn (fun u => g (partialSumEquiv r u)) (orthant r) := by
  rw [← preimage_partialSum_flag]
  exact ((measurePreserving_partialSum r).integrableOn_comp_preimage
    (measurableEmbedding_partialSum r)).symm

/-! ### The product formula -/

/-- The increment form `(AFD.4)`: `z t_r + Σ_j c_j t_j = Σ_k (z + S_k) u_k` at `t = Lu`. -/
theorem increment_form {n : ℕ} (z : ℂ) (c : Fin (n + 1) → ℝ) (u : Fin (n + 1) → ℝ) :
    z * (partialSumEquiv (n + 1) u (Fin.last n) : ℂ) +
        ∑ j, (c j : ℂ) * (partialSumEquiv (n + 1) u j : ℂ) =
      ∑ k, (z + ((∑ j ∈ Ici k, c j : ℝ) : ℂ)) * (u k : ℂ) := by
  have hlast : Iic (Fin.last n) = univ := by ext; simp [Fin.le_last]
  simp only [partialSumEquiv_apply, hlast]
  push_cast
  have hswap : ∑ j, (c j : ℂ) * ∑ i ∈ Iic j, (u i : ℂ) =
      ∑ i, (∑ j ∈ Ici i, (c j : ℂ)) * (u i : ℂ) := by
    simp_rw [mul_sum, sum_mul]
    exact sum_comm' fun j i => by simp [and_comm]
  rw [hswap, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring

theorem integral_Ioi_cexp_neg {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(w * x)) = w⁻¹ := by
  have h := integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [show (fun x : ℝ => Complex.exp (-(w * x))) = fun x : ℝ => Complex.exp (-w * x) by
    funext x; ring_nf, h]
  rw [neg_div_neg_eq, one_div]

theorem integrable_cexp_neg_Ioi {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(w * x))) (Set.Ioi 0) := by
  have := integrableOn_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  ring_nf

theorem volume_restrict_orthant (r : ℕ) :
    (volume : Measure (Fin r → ℝ)).restrict (orthant r) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Set.Ioi 0) := by
  rw [orthant, volume_pi, Measure.restrict_pi_pi]

/-- **The flag product formula**: `∫_{𝓕} e^{-z t_r} Π_j e^{-c_j t_j} dt = Π_k (z + S_k)⁻¹`. -/
theorem flag_integral_product {n : ℕ} (z : ℂ) (c : Fin (n + 1) → ℝ)
    (h : ∀ k, 0 < (z + ((∑ j ∈ Ici k, c j : ℝ) : ℂ)).re) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => Complex.exp (-(z * t (Fin.last n))) *
        ∏ j, Complex.exp (-((c j : ℂ) * t j))) (flagChamber (n + 1)) ∧
    ∫ t in flagChamber (n + 1), Complex.exp (-(z * t (Fin.last n))) *
        ∏ j, Complex.exp (-((c j : ℂ) * t j)) =
      ∏ k, (z + ((∑ j ∈ Ici k, c j : ℝ) : ℂ))⁻¹ := by
  have hpt : ∀ u : Fin (n + 1) → ℝ,
      Complex.exp (-(z * (partialSumEquiv (n + 1) u (Fin.last n) : ℝ))) *
        ∏ j, Complex.exp (-((c j : ℂ) * (partialSumEquiv (n + 1) u j : ℝ))) =
      ∏ k, Complex.exp (-((z + ((∑ j ∈ Ici k, c j : ℝ) : ℂ)) * (u k : ℝ))) := fun u => by
    rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    have := increment_form z c u
    simp only [sum_neg_distrib]
    linear_combination (-1 : ℂ) * this
  refine ⟨?_, ?_⟩
  · rw [integrableOn_flag_iff]
    refine (IntegrableOn.congr_fun ?_ (fun u _ => (hpt u).symm) (by
      rw [orthant]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi))
    rw [IntegrableOn, volume_restrict_orthant]
    exact Integrable.fintype_prod (f := fun k (x : ℝ) =>
      Complex.exp (-((z + ((∑ j ∈ Ici k, c j : ℝ) : ℂ)) * x)))
      fun k => integrable_cexp_neg_Ioi (h k)
  · rw [setIntegral_flag]
    simp_rw [hpt]
    rw [volume_restrict_orthant, integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun k (x : ℝ) => Complex.exp (-((z + ((∑ j ∈ Ici k, c j : ℝ) : ℂ)) * x)))]
    exact prod_congr rfl fun k _ => integral_Ioi_cexp_neg (h k)

/-! ### The ordered flag determinant `(AFD.3)` -/

theorem det_expKernel_neg_eq_sum {r : ℕ} (lam t : Fin r → ℝ) :
    (((expNodeMatrix (fun i => -lam i) t).det : ℝ) : ℂ) =
      ∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) *
        ∏ j, Complex.exp (-((lam (π j) : ℂ) * t j)) := by
  rw [Matrix.det_apply]
  push_cast
  refine sum_congr rfl fun π _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  push_cast
  congr 1
  refine prod_congr rfl fun j _ => ?_
  simp only [expNodeMatrix, Matrix.of_apply]
  push_cast
  ring_nf

/-- **Theorem 2.1, `(AFD.3)`: the ordered flag determinant.**  For positive grades and
`Re z > 0`, `R_r(z;λ) = ∫_{𝓕_r} e^{-z t_r} det(e^{-λ_i t_j}) dt`. -/
theorem alternant_eq_flag_integral {n : ℕ} {lam : Fin (n + 1) → ℝ} (hlam : ∀ i, 0 < lam i)
    {z : ℂ} (hz : 0 < z.re) :
    alternant z (lamC lam) = ∫ t in flagChamber (n + 1),
      Complex.exp (-(z * t (Fin.last n))) * ((expNodeMatrix (fun i => -lam i) t).det : ℂ) := by
  have hS : ∀ π : Equiv.Perm (Fin (n + 1)), ∀ k,
      0 < (z + ((∑ j ∈ Ici k, lam (π j) : ℝ) : ℂ)).re := fun π k => by
    have := suffixSum_pos hlam π k
    simp only [suffixSum] at this
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hterm := fun π : Equiv.Perm (Fin (n + 1)) =>
    flag_integral_product z (fun j => lam (π j)) (hS π)
  simp_rw [det_expKernel_neg_eq_sum, mul_sum]
  rw [integral_finsetSum _ fun π _ => by
    have := (hterm π).1.const_mul ((Equiv.Perm.sign π : ℤ) : ℂ)
    convert this using 1
    funext t
    ring]
  rw [alternant]
  refine sum_congr rfl fun π _ => ?_
  rw [show (fun t : Fin (n + 1) → ℝ => Complex.exp (-(z * t (Fin.last n))) *
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ∏ j, Complex.exp (-((lam (π j) : ℂ) * t j)))) =
    fun t => ((Equiv.Perm.sign π : ℤ) : ℂ) * (Complex.exp (-(z * t (Fin.last n))) *
      ∏ j, Complex.exp (-((lam (π j) : ℂ) * t j))) by funext t; ring,
    integral_const_mul, (hterm π).2, zsmul_eq_mul]
  congr 1
  refine prod_congr rfl fun k _ => ?_
  simp only [suffixSum, lamC]
  push_cast
  rfl


/-! ### Complete monotonicity `(AFD.6)` -/

theorem isOpen_flagChamber (r : ℕ) : IsOpen (flagChamber r) := by
  have h : flagChamber r = (⋂ i, {t : Fin r → ℝ | 0 < t i}) ∩
      ⋂ i, ⋂ j, {t : Fin r → ℝ | i < j → t i < t j} := by
    ext t; simp [flagChamber, StrictMono]
  rw [h]
  refine (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  by_cases hij : i < j
  · simp only [hij, true_implies]
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · simp only [hij, false_implies, Set.setOf_true]
    exact isOpen_univ

theorem measurableSet_flagChamber (r : ℕ) : MeasurableSet (flagChamber r) :=
  (isOpen_flagChamber r).measurableSet

theorem volume_flagChamber_pos (r : ℕ) : 0 < volume (flagChamber r) :=
  (isOpen_flagChamber r).measure_pos volume
    ⟨fun i => (i : ℝ) + 1, fun i => by positivity, fun i j hij => by
      simp only [add_lt_add_iff_right, Nat.cast_lt]; exact hij⟩

theorem abs_det_expKernel_le {r : ℕ} {lam t : Fin r → ℝ} (hlam : ∀ i, 0 < lam i)
    (ht : ∀ j, 0 ≤ t j) : |(expNodeMatrix (fun i => -lam i) t).det| ≤ r.factorial := by
  rw [Matrix.det_apply]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ σ : Equiv.Perm (Fin r),
        |Equiv.Perm.sign σ • ∏ i, expNodeMatrix (fun i => -lam i) t (σ i) i|
      ≤ ∑ _σ : Equiv.Perm (Fin r), (1 : ℝ) := by
        refine sum_le_sum fun σ _ => ?_
        rw [Units.smul_def, zsmul_eq_mul, abs_mul, abs_prod]
        have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hs, one_mul]
        refine prod_le_one (fun i _ => abs_nonneg _) fun i _ => ?_
        simp only [expNodeMatrix, Matrix.of_apply]
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        nlinarith [hlam (σ i), ht i]
    _ = r.factorial := by simp [Fintype.card_perm]

/-- `x^m e^{-ax} ≤ (m!/(a/2)^m) e^{-ax/2}` for `x ≥ 0`. -/
theorem pow_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m * Real.exp (-(a * x)) ≤ m.factorial / (a / 2) ^ m * Real.exp (-(a / 2 * x)) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * x) (by positivity) m
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have ha2 : (0 : ℝ) < (a / 2) ^ m := by positivity
  rw [div_le_iff₀ hm, mul_pow] at h
  have h2 : x ^ m ≤ m.factorial / (a / 2) ^ m * Real.exp (a / 2 * x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha2]; nlinarith [Real.exp_pos (a / 2 * x)]
  calc x ^ m * Real.exp (-(a * x)) ≤ m.factorial / (a / 2) ^ m * Real.exp (a / 2 * x) *
        Real.exp (-(a * x)) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = m.factorial / (a / 2) ^ m * Real.exp (-(a / 2 * x)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `t_r^m e^{-a t_r}` is integrable on the flag chamber. -/
theorem integrableOn_flag_pow_exp {n : ℕ} {a : ℝ} (ha : 0 < a) (m : ℕ) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => t (Fin.last n) ^ m * Real.exp (-(a * t (Fin.last n))))
      (flagChamber (n + 1)) := by
  rw [integrableOn_flag_iff]
  have hlast : ∀ u : Fin (n + 1) → ℝ, partialSumEquiv (n + 1) u (Fin.last n) = ∑ i, u i :=
    fun u => by
    rw [partialSumEquiv_apply, show Iic (Fin.last n) = univ by ext; simp [Fin.le_last]]
  have hdom : IntegrableOn (fun u : Fin (n + 1) → ℝ => (m.factorial / (a / 2) ^ m : ℝ) *
      ∏ k, Real.exp (-(a / 2 * u k))) (orthant (n + 1)) := by
    rw [IntegrableOn, volume_restrict_orthant]
    exact (Integrable.fintype_prod (f := fun _ (x : ℝ) => Real.exp (-(a / 2 * x)))
      fun _ => by
        have := exp_neg_integrableOn_Ioi 0 (by positivity : 0 < a / 2)
        refine this.congr_fun (fun x _ => by ring_nf) measurableSet_Ioi).const_mul _
  have hc : Continuous fun u : Fin (n + 1) → ℝ => partialSumEquiv (n + 1) u (Fin.last n) :=
    (continuous_apply _).comp (partialSumEquiv (n + 1)).toContinuousLinearEquiv.continuous
  refine hdom.mono' ((hc.pow m).mul (Real.continuous_exp.comp
    (continuous_const.mul hc).neg)).aestronglyMeasurable ?_
  have hmeas : MeasurableSet (orthant (n + 1)) := by
    rw [orthant]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  filter_upwards [ae_restrict_mem hmeas] with u hu
  have hu' : ∀ i, 0 < u i := fun i => hu i (Set.mem_univ i)
  have hs : 0 ≤ ∑ i, u i := sum_nonneg fun i _ => (hu' i).le
  rw [hlast, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hs m) (Real.exp_pos _).le),
    ← Real.exp_sum]
  convert pow_mul_exp_neg_le ha m (sum_nonneg fun i _ => (hu' i).le) using 3
  rw [mul_sum]
  simp only [sum_neg_distrib]

/-- The Weyl-divided flag kernel `det(e^{-λ_i t_j})/Δ_r(λ)`. -/
def flagKernel {r : ℕ} (lam : Fin r → ℝ) (t : Fin r → ℝ) : ℝ :=
  (expNodeMatrix (fun i => -lam i) t).det / delta lam

/-- The moments `∫_{𝓕} t_r^m e^{-z t_r} det/Δ dt`. -/
def flagMoment {n : ℕ} (lam : Fin (n + 1) → ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  ∫ t in flagChamber (n + 1),
    t (Fin.last n) ^ m * Real.exp (-(z * t (Fin.last n))) * flagKernel lam t

theorem abs_flagKernel_le {r : ℕ} {lam t : Fin r → ℝ} (hlam : ∀ i, 0 < lam i)
    (ht : ∀ j, 0 ≤ t j) : |flagKernel lam t| ≤ r.factorial / |delta lam| := by
  rw [flagKernel, abs_div]
  exact div_le_div_of_nonneg_right (abs_det_expKernel_le hlam ht) (abs_nonneg _)

theorem integrableOn_flagMoment {n : ℕ} {lam : Fin (n + 1) → ℝ} (hlam : ∀ i, 0 < lam i) (m : ℕ)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => t (Fin.last n) ^ m *
      Real.exp (-(a * t (Fin.last n))) * flagKernel lam t) (flagChamber (n + 1)) := by
  refine ((integrableOn_flag_pow_exp ha m).mul_const ((n + 1).factorial / |delta lam|)).mono'
    ((by fun_prop : Continuous fun t : Fin (n + 1) → ℝ => t (Fin.last n) ^ m *
      Real.exp (-(a * t (Fin.last n)))).mul ?_).aestronglyMeasurable ?_
  · unfold flagKernel expNodeMatrix
    fun_prop
  · filter_upwards [ae_restrict_mem (measurableSet_flagChamber _)] with t ht
    have hpos : ∀ j, 0 ≤ t j := fun j => (ht.1 j).le
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by
      have := hpos (Fin.last n); positivity)]
    exact mul_le_mul_of_nonneg_left (abs_flagKernel_le hlam hpos) (by
      have := hpos (Fin.last n); positivity)

theorem hasDerivAt_flagMoment {n : ℕ} {lam : Fin (n + 1) → ℝ} (hlam : ∀ i, 0 < lam i) (m : ℕ)
    {z : ℝ} (hz : 0 < z) : HasDerivAt (flagMoment lam m) (-flagMoment lam (m + 1) z) z := by
  have hs : Set.Ioi (z / 2) ∈ 𝓝 z := Ioi_mem_nhds (by linarith)
  have hmeas := measurableSet_flagChamber (n + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (flagChamber (n + 1)))
    (F := fun (w : ℝ) (t : Fin (n + 1) → ℝ) => t (Fin.last n) ^ m *
      Real.exp (-(w * t (Fin.last n))) * flagKernel lam t)
    (F' := fun (w : ℝ) (t : Fin (n + 1) → ℝ) => -(t (Fin.last n) ^ (m + 1) *
      Real.exp (-(w * t (Fin.last n))) * flagKernel lam t))
    (bound := fun t => t (Fin.last n) ^ (m + 1) * Real.exp (-(z / 2 * t (Fin.last n))) *
      ((n + 1).factorial / |delta lam|))
    hs (Eventually.of_forall fun w => by
      refine Continuous.aestronglyMeasurable ?_
      unfold flagKernel expNodeMatrix
      fun_prop)
    (integrableOn_flagMoment hlam m hz)
    (by
      refine Continuous.aestronglyMeasurable ?_
      unfold flagKernel expNodeMatrix
      fun_prop)
    (by
      filter_upwards [ae_restrict_mem hmeas] with t ht w hw
      have hpos : ∀ j, 0 ≤ t j := fun j => (ht.1 j).le
      have hl := hpos (Fin.last n)
      rw [norm_neg, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
        (abs_flagKernel_le hlam hpos) (abs_nonneg _) (by positivity)
      have : z / 2 < w := hw
      nlinarith)
    ((integrableOn_flag_pow_exp (by linarith : 0 < z / 2) (m + 1)).mul_const _)
    (by
      filter_upwards [ae_restrict_mem hmeas] with t _ w _
      have h1 : HasDerivAt (fun w : ℝ => Real.exp (-(w * t (Fin.last n))))
          (Real.exp (-(w * t (Fin.last n))) * (-t (Fin.last n))) w := by
        have := ((hasDerivAt_id' w).mul_const (t (Fin.last n))).neg.exp
        simpa using this
      refine ((h1.const_mul (t (Fin.last n) ^ m)).mul_const (flagKernel lam t)).congr_deriv ?_
      ring)
  rw [flagMoment, ← integral_neg]
  exact key.2

/-- **Theorem 3.2, `(AFD.6)`: complete monotonicity.**  For distinct positive grades and `z > 0`,
`(-1)^m (d/dz)^m (P_r/D_r)(z) = ∫_{𝓕_r} t_r^m e^{-z t_r} det(e^{-λ_i t_j})/Δ_r dt > 0`. -/
theorem complete_monotonicity {n : ℕ} {lam : Fin (n + 1) → ℝ} (hlam : ∀ i, 0 < lam i)
    (hinj : Function.Injective lam) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    (-1) ^ m * iteratedDeriv m (fun w : ℝ => aeval (point w lam) (formNumer (n + 1)) /
        aeval (point w lam) (denom (n + 1))) z = flagMoment lam m z ∧
      0 < flagMoment lam m z := by
  have hΔ : delta lam ≠ 0 := by
    rw [delta]
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => sub_ne_zero.2 fun h => ?_
    exact (ne_of_lt (mem_Ioi.1 hb)) (hinj h)
  -- `P/D = flagMoment 0` on `(0, ∞)`
  have hPD : ∀ w : ℝ, 0 < w → aeval (point w lam) (formNumer (n + 1)) /
      aeval (point w lam) (denom (n + 1)) = flagMoment lam 0 w := fun w hw => by
    have hph : ∀ S ∈ subsets (n + 1), w + ∑ i ∈ S, lam i ≠ 0 := fun S hS =>
      (add_pos_of_pos_of_nonneg hw (sum_nonneg fun i _ => (hlam i).le)).ne'
    have hR := alternant_eq w lam hph
    have hflag := alternant_eq_flag_integral hlam (z := (w : ℂ)) (by simpa using hw)
    have hcast : alternant (w : ℂ) (lamC lam) = ((alternant w lam : ℝ) : ℂ) := by
      simp only [alternant, suffixSum, lamC]
      push_cast
      rfl
    have hint : (∫ t in flagChamber (n + 1), Complex.exp (-((w : ℂ) * t (Fin.last n))) *
        ((expNodeMatrix (fun i => -lam i) t).det : ℂ)) =
        ((∫ t in flagChamber (n + 1), Real.exp (-(w * t (Fin.last n))) *
          (expNodeMatrix (fun i => -lam i) t).det : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun (measurableSet_flagChamber _) fun t _ => ?_
      push_cast
      rfl
    rw [hcast, hint] at hflag
    have hreal := Complex.ofReal_injective hflag
    rw [flagMoment]
    simp only [pow_zero, one_mul, flagKernel]
    rw [show (fun t : Fin (n + 1) → ℝ => Real.exp (-(w * t (Fin.last n))) *
        ((expNodeMatrix (fun i => -lam i) t).det / delta lam)) =
      fun t => Real.exp (-(w * t (Fin.last n))) * (expNodeMatrix (fun i => -lam i) t).det /
        delta lam by funext t; ring, integral_div, ← hreal, hR]
    field_simp
  -- iterated derivatives of `flagMoment 0`
  have hiter : ∀ k : ℕ, ∀ w : ℝ, 0 < w →
      iteratedDeriv k (flagMoment lam 0) w = (-1) ^ k * flagMoment lam k w := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hev : iteratedDeriv k (flagMoment lam 0) =ᶠ[𝓝 w]
          fun v => (-1) ^ k * flagMoment lam k v := by
        filter_upwards [Ioi_mem_nhds hw] with v hv
        exact ih v hv
      rw [iteratedDeriv_succ, hev.deriv_eq, deriv_const_mul _
        (hasDerivAt_flagMoment hlam k hw).differentiableAt,
        (hasDerivAt_flagMoment hlam k hw).deriv, pow_succ]
      ring
  have hev0 : (fun w : ℝ => aeval (point w lam) (formNumer (n + 1)) /
      aeval (point w lam) (denom (n + 1))) =ᶠ[𝓝 z] flagMoment lam 0 := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact hPD w hw
  refine ⟨?_, ?_⟩
  · rw [hev0.iteratedDeriv_eq, hiter m z hz, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_mul]
  · rw [flagMoment, setIntegral_pos_iff_support_of_nonneg_ae _
      (integrableOn_flagMoment hlam m hz)]
    · refine lt_of_lt_of_le (volume_flagChamber_pos (n + 1)) (measure_mono fun t ht => ⟨?_, ht⟩)
      rw [Function.mem_support]
      have hl := ht.1 (Fin.last n)
      exact (mul_pos (mul_pos (pow_pos hl m) (Real.exp_pos _))
        (det_expKernel_neg_div_delta_pos hinj ht.2)).ne'
    · filter_upwards [ae_restrict_mem (measurableSet_flagChamber _)] with t ht
      have hl := ht.1 (Fin.last n)
      exact (mul_pos (mul_pos (pow_pos hl m) (Real.exp_pos _))
        (det_expKernel_neg_div_delta_pos hinj ht.2)).le

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
