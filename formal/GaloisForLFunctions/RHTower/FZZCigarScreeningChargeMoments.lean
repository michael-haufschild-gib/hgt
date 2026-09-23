import GaloisForLFunctions.RHTower.FZZCigarNeutralScreeningDeterminant
import GaloisForLFunctions.HTGeometry.CauchyBinet
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Original screening charge integrals and their full moment determinant

For every integer count, integrate one complete charge family of the literal
level-four neutral screening kernel. Every opposite-charge inverse sixth power
remains in the original one-position weight. The domain retains a finite outer
position cutoff and excludes disks around every fixed opposite-charge position.

Compactness and separation prove admission of all original moments. A private
permutation expansion proves termwise product admission before distributing the
integral and applying Fubini. Row permutation signs then give the exact factorial.
The resulting identity is connected directly to the complete neutral source.

All public statements have only position, cutoff and integer data. The result
also covers empty domains, coincident fixed positions and count zero. Cutoff
removal, count continuation, physical normalization and the mixed Ward identity
remain separate mathematical obligations.
-/

open MeasureTheory Set Metric Finset Matrix Equiv
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def chargeTable {n : ℕ} {α : Type*} (f : Fin n → α → ℂ)
    (x : Fin n → α) : Matrix (Fin n) (Fin n) ℂ :=
  .of fun i j => f j (x i)

private def chargeTerm {n : ℕ} {α : Type*} (f g : Fin n → α → ℂ)
    (σ τ : Perm (Fin n)) (x : Fin n → α) : ℂ :=
  (Perm.sign σ : ℂ)*(Perm.sign τ : ℂ)*∏ i, f (σ i) (x i)*g (τ i) (x i)

private theorem determinant_product_expansion {n : ℕ} {α : Type*}
    (f g : Fin n → α → ℂ) (x : Fin n → α) :
    (chargeTable f x).det*(chargeTable g x).det =
      ∑ σ : Perm (Fin n),∑ τ : Perm (Fin n),chargeTerm f g σ τ x := by
  rw [GaloisForLFunctions.det_eq_sum_perm_row,
    GaloisForLFunctions.det_eq_sum_perm_row,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [chargeTable,Matrix.of_apply,chargeTerm,Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  ring

private theorem chargeTerm_integrable {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f g : Fin n → α → ℂ)
    (hfg : ∀ i j, Integrable (fun x => f i x*g j x) μ)
    (σ τ : Perm (Fin n)) :
    Integrable (chargeTerm f g σ τ) (Measure.pi (fun _ : Fin n => μ)) := by
  exact (Integrable.fintype_prod (fun i => hfg (σ i) (τ i))).const_mul _

private theorem determinant_product_integrable {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f g : Fin n → α → ℂ)
    (hfg : ∀ i j, Integrable (fun x => f i x*g j x) μ) :
    Integrable (fun x => (chargeTable f x).det*(chargeTable g x).det)
      (Measure.pi (fun _ : Fin n => μ)) := by
  simp_rw [determinant_product_expansion]
  exact integrable_finsetSum _ (fun σ _ =>
    integrable_finsetSum _ (fun τ _ => chargeTerm_integrable μ f g hfg σ τ))

private theorem integral_determinant_product {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f g : Fin n → α → ℂ)
    (hfg : ∀ i j, Integrable (fun x => f i x*g j x) μ) :
    (∫ x, (chargeTable f x).det*(chargeTable g x).det
      ∂(Measure.pi (fun _ : Fin n => μ))) =
      (n.factorial : ℂ)*(Matrix.of fun i j => ∫ x, f i x*g j x ∂μ).det := by
  let M : Matrix (Fin n) (Fin n) ℂ := .of fun i j => ∫ x, f i x*g j x ∂μ
  simp_rw [determinant_product_expansion]
  rw [integral_finsetSum _ (fun σ _ =>
    integrable_finsetSum _ (fun τ _ => chargeTerm_integrable μ f g hfg σ τ))]
  simp_rw [integral_finsetSum _ (fun τ _ => chargeTerm_integrable μ f g hfg _ τ)]
  simp only [chargeTerm,integral_const_mul]
  have hint (σ τ : Perm (Fin n)) :=
    integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
      (fun i x => f (σ i) x*g (τ i) x)
  simp_rw [hint]
  change (∑ σ : Perm (Fin n),∑ τ : Perm (Fin n),
    (Perm.sign σ : ℂ)*(Perm.sign τ : ℂ)*∏ i, M (σ i) (τ i)) = (n.factorial : ℂ)*M.det
  have hrow (σ : Perm (Fin n)) :
      (∑ τ : Perm (Fin n),(Perm.sign σ : ℂ)*(Perm.sign τ : ℂ)*∏ i, M (σ i) (τ i)) = M.det := by
    have hd := GaloisForLFunctions.det_eq_sum_perm_row (M.submatrix σ id)
    simp only [Matrix.submatrix_apply,id_eq] at hd
    calc
      _ = (Perm.sign σ : ℂ)*(M.submatrix σ id).det := by
        rw [hd,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ hτ
        ring
      _ = M.det := by
        rw [Matrix.det_permute]
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> rw [h] <;> simp
  simp only [hrow,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
    nsmul_eq_mul]

def fzzScreeningChargeDomain {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) : Set ℂ :=
  closedBall 0 (Real.exp R) \ ⋃ i, ball (z i) (Real.exp (-T))

def fzzScreeningChargeWeight {m : ℕ} (z : Fin m → ℂ) (w : ℂ) : ℝ :=
  ∏ i, (‖w-z i‖^(6 : ℕ))⁻¹

private theorem chargeDomain_compact {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) :
    IsCompact (fzzScreeningChargeDomain z R T) :=
  (isCompact_closedBall _ _).diff (isOpen_iUnion (fun _ => isOpen_ball))

private theorem chargeDomain_ne {m : ℕ} (z : Fin m → ℂ) (R T : ℝ)
    {w : ℂ} (hw : w ∈ fzzScreeningChargeDomain z R T) (i : Fin m) : w-z i ≠ 0 := by
  intro he
  have heq := sub_eq_zero.mp he
  exact hw.2 (mem_iUnion.mpr ⟨i,by rw [heq]; exact mem_ball_self (Real.exp_pos _)⟩)

private theorem chargeWeight_continuousOn {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) :
    ContinuousOn (fzzScreeningChargeWeight z) (fzzScreeningChargeDomain z R T) := by
  unfold fzzScreeningChargeWeight
  apply continuousOn_finsetProd
  intro i hi
  exact ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn.pow 6).inv₀
    (fun w hw => pow_ne_zero _ (norm_ne_zero_iff.mpr (chargeDomain_ne z R T hw i)))

def fzzScreeningChargeMoment {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (a b : ℕ) : ℂ :=
  ∫ w : ℂ in fzzScreeningChargeDomain z R T,
    (w^a*(starRingEnd ℂ) (w^b))*(fzzScreeningChargeWeight z w : ℂ)

theorem fzzScreeningChargeMoment_integrable {m : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (a b : ℕ) :
    IntegrableOn (fun w : ℂ =>
      (w^a*(starRingEnd ℂ) (w^b))*(fzzScreeningChargeWeight z w : ℂ))
      (fzzScreeningChargeDomain z R T) := by
  apply ContinuousOn.integrableOn_compact (chargeDomain_compact z R T)
  apply ContinuousOn.mul
  · exact (by fun_prop : Continuous (fun w : ℂ => w^a*(starRingEnd ℂ) (w^b))).continuousOn
  · exact Complex.continuous_ofReal.comp_continuousOn (chargeWeight_continuousOn z R T)


def fzzScreeningChargeMeasure {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    Measure (Fin n → ℂ) :=
  Measure.pi (fun _ : Fin n => volume.restrict (fzzScreeningChargeDomain z R T))

def fzzScreeningChargeMomentMatrix {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  .of fun i j => fzzScreeningChargeMoment z R T i.val j.val

def fzzScreeningChargeKernel {m n : ℕ} (z : Fin m → ℂ) (w : Fin n → ℂ) : ℝ :=
  ‖(Matrix.vandermonde w).det‖^(2 : ℕ)*∏ i, fzzScreeningChargeWeight z (w i)

private theorem chargeKernel_det {m n : ℕ} (z : Fin m → ℂ) (w : Fin n → ℂ) :
    (fzzScreeningChargeKernel z w : ℂ) =
      (chargeTable (fun (i : Fin n) (x : ℂ) => x^i.val) w).det *
      (chargeTable (fun (j : Fin n) (x : ℂ) =>
        (starRingEnd ℂ) (x^j.val)*(fzzScreeningChargeWeight z x : ℂ)) w).det := by
  have htable :
      chargeTable (fun (j : Fin n) (x : ℂ) =>
        (starRingEnd ℂ) (x^j.val)*(fzzScreeningChargeWeight z x : ℂ)) w =
      Matrix.of (fun i j => (fzzScreeningChargeWeight z (w i) : ℂ)*
        ((starRingEnd ℂ).mapMatrix (Matrix.vandermonde w)) i j) := by
    ext i j
    simp [chargeTable,Matrix.vandermonde,mul_comm]
  rw [htable,Matrix.det_mul_column,← (starRingEnd ℂ).map_det]
  change (fzzScreeningChargeKernel z w : ℂ) =
    (Matrix.vandermonde w).det *
      ((∏ i, (fzzScreeningChargeWeight z (w i) : ℂ))*(starRingEnd ℂ) (Matrix.vandermonde w).det)
  rw [mul_left_comm,Complex.mul_conj']
  simp [fzzScreeningChargeKernel,Complex.ofReal_prod,mul_comm]

private theorem chargeMoment_pair_integrable {m n : ℕ} (z : Fin m → ℂ)
    (R T : ℝ) (i j : Fin n) :
    Integrable (fun x : ℂ => x^i.val*
      ((starRingEnd ℂ) (x^j.val)*(fzzScreeningChargeWeight z x : ℂ)))
      (volume.restrict (fzzScreeningChargeDomain z R T)) := by
  simpa only [IntegrableOn,mul_assoc] using fzzScreeningChargeMoment_integrable z R T i.val j.val

/-- Admission of the original charge-family kernel before any integral interchange. -/
theorem fzzScreeningChargeKernel_integrable {m n : ℕ} (z : Fin m → ℂ) (R T : ℝ) :
    Integrable (fzzScreeningChargeKernel (n := n) z) (fzzScreeningChargeMeasure z R T n) := by
  have h := determinant_product_integrable
    (volume.restrict (fzzScreeningChargeDomain z R T))
    (fun (i : Fin n) (x : ℂ) => x^i.val)
    (fun (j : Fin n) (x : ℂ) => (starRingEnd ℂ) (x^j.val)*(fzzScreeningChargeWeight z x : ℂ))
    (chargeMoment_pair_integrable z R T)
  simp_rw [← chargeKernel_det] at h
  have hr := h.re
  change Integrable (fun w : Fin n → ℂ => (fzzScreeningChargeKernel z w : ℂ).re)
    (Measure.pi (fun _ : Fin n => volume.restrict (fzzScreeningChargeDomain z R T))) at hr
  simpa only [Complex.ofReal_re,fzzScreeningChargeMeasure] using hr

/-- The complete integer-count charge integral is the exact factorial times
its original moment determinant, with both position cutoffs retained. -/
theorem fzzScreeningChargeKernel_integral {m : ℕ} (z : Fin m → ℂ) (R T : ℝ) (n : ℕ) :
    (∫ w, fzzScreeningChargeKernel z w ∂fzzScreeningChargeMeasure z R T n) =
      (n.factorial : ℝ)*(fzzScreeningChargeMomentMatrix z R T n).det.re := by
  have h := integral_determinant_product
    (volume.restrict (fzzScreeningChargeDomain z R T))
    (fun (i : Fin n) (x : ℂ) => x^i.val)
    (fun (j : Fin n) (x : ℂ) => (starRingEnd ℂ) (x^j.val)*(fzzScreeningChargeWeight z x : ℂ))
    (chargeMoment_pair_integrable z R T)
  simp_rw [← chargeKernel_det,integral_complex_ofReal,← mul_assoc] at h
  have hm : (Matrix.of fun i j : Fin n =>
      ∫ x : ℂ in fzzScreeningChargeDomain z R T,
        x^i.val*(starRingEnd ℂ) (x^j.val)*(fzzScreeningChargeWeight z x : ℂ)) =
      fzzScreeningChargeMomentMatrix z R T n := rfl
  rw [hm] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero,fzzScreeningChargeMeasure] using hr

private theorem within_vandermonde {n : ℕ} (w : Fin n → ℂ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, ‖w i-w j‖^(2 : ℕ)) = ‖(Matrix.vandermonde w).det‖^(2 : ℕ) := by
  rw [Matrix.det_vandermonde]
  simp only [norm_prod,Finset.prod_pow,norm_sub_rev]

private theorem neutral_charge_factor {n : ℕ} (z w : Fin n → ℂ) :
    fzzNeutralCubicScreeningKernel z w =
      ‖(Matrix.vandermonde z).det‖^(2 : ℕ) * fzzScreeningChargeKernel z w := by
  unfold fzzNeutralCubicScreeningKernel fzzScreeningChargeKernel fzzScreeningChargeWeight
  simp only [Finset.prod_mul_distrib]
  rw [within_vandermonde,within_vandermonde]
  have hc : (∏ i, ∏ j, (‖z i-w j‖^(6 : ℕ))⁻¹) = ∏ j, ∏ i, (‖w j-z i‖^(6 : ℕ))⁻¹ := by
    rw [Finset.prod_comm]
    simp only [norm_sub_rev]
  rw [hc,mul_assoc]

/-- Admission of the full neutral source when one complete charge family is integrated. -/
theorem fzzNeutralCubicScreeningKernel_charge_integrable {n : ℕ}
    (z : Fin n → ℂ) (R T : ℝ) :
    Integrable (fzzNeutralCubicScreeningKernel z) (fzzScreeningChargeMeasure z R T n) := by
  change Integrable (fun w => fzzNeutralCubicScreeningKernel z w) _
  simp_rw [neutral_charge_factor]
  exact (fzzScreeningChargeKernel_integrable (n := n) z R T).const_mul
    (‖(Matrix.vandermonde z).det‖^(2 : ℕ))

/-- Exact original neutral source integral for every integer screening count.
All opposite-charge interactions remain inside the original moment matrix. -/
theorem fzzNeutralCubicScreeningKernel_charge_integral {n : ℕ}
    (z : Fin n → ℂ) (R T : ℝ) :
    (∫ w, fzzNeutralCubicScreeningKernel z w ∂fzzScreeningChargeMeasure z R T n) =
      ‖(Matrix.vandermonde z).det‖^(2 : ℕ) *
        ((n.factorial : ℝ)*(fzzScreeningChargeMomentMatrix z R T n).det.re) := by
  simp_rw [neutral_charge_factor]
  rw [integral_const_mul,fzzScreeningChargeKernel_integral]

end GaloisForLFunctions.RHTower
