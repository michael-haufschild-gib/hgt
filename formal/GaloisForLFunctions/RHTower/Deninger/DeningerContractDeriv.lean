import GaloisForLFunctions.RHTower.Deninger.DeningerHomotopyC1
import GaloisForLFunctions.RHTower.Deninger.DeningerAverageOperator

/-!
# Contraction and the exterior derivative

Contracting a form against a fixed vector is a continuous linear operation, so it commutes with
differentiation; combined with the Cartan formula this expresses the contraction of a closed form as
the exterior derivative of the contracted primitive plus a directional derivative.  A form all of
whose contractions against the coordinate vectors vanish is zero.

* `deningerExtDeriv_contract` : the exterior derivative of a contracted form.
* `deningerForm_eq_zero_of_contract` : a form with vanishing coordinate contractions is zero.
-/

namespace RHTower

open ContinuousAlternatingMap

section ContractDeriv

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The exterior derivative of a contracted form** is the antisymmetrized contraction of the
derivative. -/
theorem deningerExtDeriv_contract {β : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ} {w : E}
    (hdiff : DifferentiableAt ℂ β w) (x : E) :
    extDeriv (fun y => deningerContractCLM x (β y)) w =
      alternatizeUncurryFin ((deningerContractCLM x).comp (fderiv ℂ β w)) := by
  have hfd : fderiv ℂ (fun y => deningerContractCLM x (β y)) w =
      (deningerContractCLM x).comp (fderiv ℂ β w) := by
    have h := ((deningerContractCLM (n := n) x).hasFDerivAt).comp w hdiff.hasFDerivAt
    exact h.fderiv
  rw [extDeriv, hfd]

/-- **A form whose contractions against the coordinate vectors vanish is zero.** -/
theorem deningerForm_eq_zero_of_contract {r : ℕ}
    {α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (h : ∀ j : Fin r, deningerContractCLM (Pi.single j (1 : ℂ) : Fin r → ℂ) α = 0) : α = 0 := by
  classical
  ext v
  have hbasis : ∀ j : Fin r,
      (fun l => if j = l then (1 : ℂ) else 0) = (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j
    funext l
    rw [Pi.single_apply]
    by_cases hl : j = l
    · rw [if_pos hl, if_pos hl.symm]
    · rw [if_neg hl, if_neg (Ne.symm hl)]
  have hcontract : deningerContractL (n := n) (v 0) α = 0 := by
    conv_lhs =>
      rw [show v 0 = ∑ j, (v 0) j • (fun l => if j = l then (1 : ℂ) else 0) from
        pi_eq_sum_univ (v 0)]
    rw [_root_.map_sum]
    have hzero : ∀ j : Fin r,
        (deningerContractL (n := n) ((v 0) j • (fun l => if j = l then (1 : ℂ) else 0))) α = 0 := by
      intro j
      rw [map_smul, hbasis j]
      show (v 0) j • (deningerContractCLM (Pi.single j (1 : ℂ) : Fin r → ℂ) α) = 0
      rw [h j]
      ext u
      show (v 0) j • ((0 : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) u) =
        (0 : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) u
      rw [show ((0 : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) u) = (0 : ℂ) from rfl, smul_eq_mul, mul_zero]
    rw [_root_.sum_apply]
    exact Finset.sum_eq_zero fun j _ => hzero j
  have hval : α v = deningerContractCLM (v 0) α (Fin.tail v) := by
    show α v = α (Fin.cons (v 0) (Fin.tail v))
    rw [Fin.cons_self_tail]
  rw [hval]
  have : deningerContractCLM (v 0) α = 0 := hcontract
  rw [this]
  rfl

end ContractDeriv

end RHTower
