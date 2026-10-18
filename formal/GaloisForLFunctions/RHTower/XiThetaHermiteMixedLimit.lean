import GaloisForLFunctions.RHTower.XiThetaConcentration
import GaloisForLFunctions.RHTower.LaguerreHermiteNormalization

/-!
# Hermite limits under the actual Xi moment expectation

Concentration makes every positive fluctuation moment vanish. The regular
Laguerre recurrence then passes to the Hermite recurrence after integration.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem tendsto_xiJensenDelta : Tendsto xiJensenDelta atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_natCast_atTop_atTop))

theorem tendsto_xiThetaExpectation_fluctuation (k : ℕ) :
    Tendsto (fun n => xiThetaExpectation n (xiThetaFluctuation n ^ k)) atTop
      (𝓝 (if k = 0 then 1 else 0)) := by
  cases k with
  | zero => simpa only [pow_zero, xiThetaExpectation_one, if_pos rfl, ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ k => simpa only [Nat.succ_ne_zero, if_false] using
      tendsto_xiThetaExpectation_fluctuation_succ k

def xiThetaHermiteArgument (n : ℕ) (x : ℝ) : ℝ[X] :=
  C x + C (xiJensenDelta n * x - 1) * xiThetaFluctuation n

def xiThetaHermiteMixed (n d k : ℕ) (x : ℝ) : ℝ :=
  xiThetaExpectation n (xiThetaFluctuation n ^ k *
    (laguerreHermite (xiJensenDelta n) d).comp (xiThetaHermiteArgument n x))

theorem xiThetaHermiteMixed_zero (n k : ℕ) (x : ℝ) :
    xiThetaHermiteMixed n 0 k x = xiThetaExpectation n (xiThetaFluctuation n ^ k) := by
  simp [xiThetaHermiteMixed, laguerreHermite]

theorem xiThetaHermiteMixed_one (n k : ℕ) (x : ℝ) :
    xiThetaHermiteMixed n 1 k x =
      x * xiThetaExpectation n (xiThetaFluctuation n ^ k) +
        (xiJensenDelta n * x - 1) * xiThetaExpectation n (xiThetaFluctuation n ^ (k + 1)) := by
  unfold xiThetaHermiteMixed
  simp only [laguerreHermite, X_comp, xiThetaHermiteArgument]
  have hpoly : xiThetaFluctuation n ^ k *
      (C x + C (xiJensenDelta n * x - 1) * xiThetaFluctuation n) =
        C x * xiThetaFluctuation n ^ k +
          C (xiJensenDelta n * x - 1) * xiThetaFluctuation n ^ (k + 1) := by
    rw [pow_succ]
    ring
  rw [hpoly, map_add, xiThetaExpectation_C_mul, xiThetaExpectation_C_mul]

theorem xiThetaHermiteMixed_add_two (n d k : ℕ) (x : ℝ) :
    xiThetaHermiteMixed n (d + 2) k x =
      (1 + ((d : ℝ) + 1) * xiJensenDelta n ^ 2)⁻¹ *
        ((x + 2 * ((d : ℝ) + 1) * xiJensenDelta n) * xiThetaHermiteMixed n (d + 1) k x +
          (xiJensenDelta n * x - 1) * xiThetaHermiteMixed n (d + 1) (k + 1) x -
            ((d : ℝ) + 1) * xiThetaHermiteMixed n d k x) := by
  let δ := xiJensenDelta n
  let Z := xiThetaFluctuation n
  let T := xiThetaHermiteArgument n x
  let U := (laguerreHermite δ (d + 1)).comp T
  let V := (laguerreHermite δ d).comp T
  have hpoly : Z ^ k * (laguerreHermite δ (d + 2)).comp T =
      C ((1 + ((d : ℝ) + 1) * δ ^ 2)⁻¹) *
        (C (x + 2 * ((d : ℝ) + 1) * δ) * (Z ^ k * U) +
          C (δ * x - 1) * (Z ^ (k + 1) * U) - C ((d : ℝ) + 1) * (Z ^ k * V)) := by
    rw [laguerreHermite]
    simp only [mul_comp, C_comp, sub_comp, add_comp, X_comp]
    change Z ^ k * (C _ * ((T + C _) * U - C _ * V)) = _
    dsimp only [T, xiThetaHermiteArgument]
    change Z ^ k * (C _ * ((C x + C (δ * x - 1) * Z + C _) * U - C _ * V)) = _
    rw [pow_succ]
    simp only [map_add]
    ring
  change xiThetaExpectation n (Z ^ k * (laguerreHermite δ (d + 2)).comp T) = _
  rw [hpoly, xiThetaExpectation_C_mul, map_sub, map_add,
    xiThetaExpectation_C_mul, xiThetaExpectation_C_mul, xiThetaExpectation_C_mul]
  rfl

theorem tendsto_xiThetaHermiteMixed (d k : ℕ) (x : ℝ) :
    Tendsto (fun n => xiThetaHermiteMixed n d k x) atTop
      (𝓝 (if k = 0 then (hermiteReal d).eval x else 0)) := by
  induction d using Nat.twoStepInduction generalizing k with
  | zero => simpa only [xiThetaHermiteMixed_zero, eval_hermiteReal_zero] using
      tendsto_xiThetaExpectation_fluctuation k
  | one =>
    have hη : Tendsto (fun n => xiJensenDelta n * x - 1) atTop (𝓝 (-1)) := by
      simpa using (tendsto_xiJensenDelta.mul_const x).sub_const 1
    have h := ((tendsto_xiThetaExpectation_fluctuation k).const_mul x).add
      (hη.mul (tendsto_xiThetaExpectation_fluctuation (k + 1)))
    cases k <;> simpa only [xiThetaHermiteMixed_one, Nat.succ_ne_zero, if_false,
      if_pos rfl, ite_true, eval_hermiteReal_one, mul_one, mul_zero, add_zero] using h
  | more d ih₀ ih₁ =>
    have hden : Tendsto (fun n => (1 + ((d : ℝ) + 1) * xiJensenDelta n ^ 2)⁻¹)
        atTop (𝓝 1) := by
      have hbase : Tendsto (fun n => 1 + ((d : ℝ) + 1) * xiJensenDelta n ^ 2)
          atTop (𝓝 (1 : ℝ)) := by
        simpa using tendsto_const_nhds.add
          ((tendsto_xiJensenDelta.pow 2).const_mul ((d : ℝ) + 1))
      simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hlin : Tendsto (fun n => x + 2 * ((d : ℝ) + 1) * xiJensenDelta n) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (tendsto_xiJensenDelta.const_mul (2 * ((d : ℝ) + 1)))
    have hη : Tendsto (fun n => xiJensenDelta n * x - 1) atTop (𝓝 (-1)) := by
      simpa using (tendsto_xiJensenDelta.mul_const x).sub_const 1
    have h := hden.mul (((hlin.mul (ih₁ k)).add (hη.mul (ih₁ (k + 1)))).sub
      ((ih₀ k).const_mul ((d : ℝ) + 1)))
    cases k <;> simpa only [xiThetaHermiteMixed_add_two, Nat.succ_ne_zero, if_false,
      if_pos rfl, ite_true, eval_hermiteReal_add_two, mul_zero, add_zero, sub_zero, one_mul] using h

theorem tendsto_xiThetaHermiteExpectation (d : ℕ) (x : ℝ) :
    Tendsto (fun n => xiThetaExpectation n
      ((laguerreHermite (xiJensenDelta n) d).comp (xiThetaHermiteArgument n x))) atTop
        (𝓝 ((hermiteReal d).eval x)) := by
  simpa only [xiThetaHermiteMixed, pow_zero, one_mul, if_pos rfl, ite_true] using
    tendsto_xiThetaHermiteMixed d 0 x

end RHTower
