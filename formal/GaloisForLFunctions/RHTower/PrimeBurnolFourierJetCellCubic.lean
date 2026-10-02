import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetBalancedCubic

/-!
# Complete cubic near zero two-channel Gram coupling

The full noncommutative cubic has an exact first-order factorization. For an
idempotent polarization away from the neutral and balanced values, that factor
is invertible near zero coupling. No summand of the cubic is omitted.
-/

open Filter Topology Matrix
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def burnolJetCellNeutral : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,0]
def burnolJetCellSwap : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def burnolJetCellSkew : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]
def burnolJetCellPolarization (u w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![u,w;w,1-u]
def burnolJetCellNormalizedGram (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := 1+t • burnolJetCellSwap
def burnolJetCellCommutator (u w t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  burnolJetCellPolarization u w*burnolJetCellSwap-burnolJetCellSwap*burnolJetCellPolarization u w+t • (burnolJetCellPolarization u w-burnolJetCellSwap*burnolJetCellPolarization u w*burnolJetCellSwap)
def burnolJetCellCubicVariation (u w t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let D := burnolJetCellPolarization u w-burnolJetCellNeutral
  let K := burnolJetCellCommutator u w t
  (1-t^2)⁻¹ • (D^2*K+D*K*D+K*D^2)+
    (t*(1-t^2)⁻¹^2) • (D*K^2+K*D*K+K^2*D)

theorem burnolJetCellNormalizedGram_inv {t : ℂ} (ht : 1-t^2≠0) :
    (burnolJetCellNormalizedGram t)⁻¹=(1-t^2)⁻¹ • (1-t • burnolJetCellSwap) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnolJetCellNormalizedGram,burnolJetCellSwap,Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [ht] <;> ring

theorem burnolJetCell_modular {t : ℂ} (ht : 1-t^2≠0) (u w : ℂ) :
    (burnolJetCellNormalizedGram t)⁻¹*burnolJetCellPolarization u w*burnolJetCellNormalizedGram t = burnolJetCellPolarization u w+(t*(1-t^2)⁻¹) • burnolJetCellCommutator u w t := by
  rw [burnolJetCellNormalizedGram_inv ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnolJetCellNormalizedGram,burnolJetCellPolarization,burnolJetCellSwap,burnolJetCellCommutator,Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [ht] <;> ring

theorem burnolJetCubic_increment {A : Type*} [Ring A] (P Q H : A) :
    cubicProjectionAssociatorAlgebra (Q+H) Q P =
      (Q-P)^2*H+(Q-P)*H*(Q-P)+H*(Q-P)^2+
        (Q-P)*H^2+H*(Q-P)*H+H^2*(Q-P) := by
  unfold cubicProjectionAssociatorAlgebra
  noncomm_ring

theorem burnolJetCell_cubic_factor {t : ℂ} (ht : 1-t^2≠0) (u w : ℂ) :
    cubicProjectionAssociatorAlgebra ((burnolJetCellNormalizedGram t)⁻¹*burnolJetCellPolarization u w*burnolJetCellNormalizedGram t) (burnolJetCellPolarization u w) burnolJetCellNeutral =
      t • burnolJetCellCubicVariation u w t := by
  rw [burnolJetCell_modular ht,burnolJetCubic_increment]
  simp only [burnolJetCellCubicVariation,pow_two,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  module

theorem burnolJetCellDifference_sq {u w : ℂ} (hw : w^2=u*(1-u)) :
    (burnolJetCellPolarization u w-burnolJetCellNeutral)^2=(1-u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnolJetCellPolarization,burnolJetCellNeutral,pow_two,Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination hw
  · ring
  · ring
  · linear_combination hw

theorem burnolJetCellDifference_skew (u w : ℂ) :
    (burnolJetCellPolarization u w-burnolJetCellNeutral)*burnolJetCellSkew = -(burnolJetCellSkew*(burnolJetCellPolarization u w-burnolJetCellNeutral)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnolJetCellPolarization,burnolJetCellNeutral,burnolJetCellSkew,Matrix.mul_apply,Fin.sum_univ_two]

theorem burnolJetCellCommutator_zero (u w : ℂ) : burnolJetCellCommutator u w 0=(2*u-1) • burnolJetCellSkew := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnolJetCellCommutator,burnolJetCellPolarization,burnolJetCellSwap,burnolJetCellSkew] <;> ring

theorem burnolJetCellCubicVariation_zero {u w : ℂ} (hw : w^2=u*(1-u)) :
    burnolJetCellCubicVariation u w 0=((2*u-1)*(1-u)) • burnolJetCellSkew := by
  have hmid : (burnolJetCellPolarization u w-burnolJetCellNeutral)*burnolJetCellSkew*(burnolJetCellPolarization u w-burnolJetCellNeutral)=-(1-u) • burnolJetCellSkew := by
    rw [burnolJetCellDifference_skew,neg_mul,mul_assoc,← pow_two,burnolJetCellDifference_sq hw,Matrix.mul_smul,mul_one,neg_smul]
  simp only [burnolJetCellCubicVariation,zero_pow (by decide : 2≠0),sub_zero,inv_one,one_smul,zero_mul,
    zero_smul,add_zero,burnolJetCellCommutator_zero,burnolJetCellDifference_sq hw,Matrix.smul_mul,Matrix.mul_smul,
    mul_one,one_mul,hmid,smul_smul]
  module


theorem burnolJetCellCubicVariation_continuousAt (u w : ℂ) : ContinuousAt (burnolJetCellCubicVariation u w) 0 := by
  unfold burnolJetCellCubicVariation burnolJetCellCommutator
  fun_prop (disch := norm_num)

theorem burnolJetCellCubic_eventually_isUnit {u w : ℂ} (hw : w^2=u*(1-u))
    (hu : 1-u≠0) (hb : 2*u-1≠0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t≠0 →
      IsUnit (cubicProjectionAssociatorAlgebra
        ((burnolJetCellNormalizedGram t)⁻¹*burnolJetCellPolarization u w*burnolJetCellNormalizedGram t) (burnolJetCellPolarization u w) burnolJetCellNeutral) := by
  have hd : (burnolJetCellCubicVariation u w 0).det≠0 := by
    rw [burnolJetCellCubicVariation_zero hw,Matrix.det_smul]
    simp [burnolJetCellSkew,Matrix.det_fin_two,hb,hu]
  have hlim : Tendsto (fun t => (burnolJetCellCubicVariation u w t).det) (𝓝 0) (𝓝 (burnolJetCellCubicVariation u w 0).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp (burnolJetCellCubicVariation_continuousAt u w)
  have hden : ∀ᶠ t in 𝓝 (0 : ℂ), 1-t^2≠0 :=
    (show ContinuousAt (fun t : ℂ => 1-t^2) 0 by fun_prop).eventually_ne (by norm_num)
  filter_upwards [hlim.eventually_ne hd,hden] with t ht hd ht0
  rw [burnolJetCell_cubic_factor hd,Matrix.isUnit_iff_isUnit_det,Matrix.det_smul]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ ht0) ht)

end RHTower
