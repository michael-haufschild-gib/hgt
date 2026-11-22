import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.JointPartition
import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A free prime-two mode completes the balanced pair to the full gas

Twice the centered level is an odd integer. Its dyadic translates give
every positive integer exactly once. Prime occupancies and their additive
energies can thus be read directly in the two balanced labels and one
additional oscillator.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

abbrev Mode (t : ExceptionalTime) (j : ℕ) := ℕ × Pair t j

private def dyadicLabel (u : ℕ × ℕ) : ℕ+ :=
  ⟨2^u.1*(2*u.2+1),Nat.mul_pos (pow_pos (by decide) _) (Nat.succ_pos _)⟩

private theorem dyadic_valuation (u : ℕ × ℕ) : padicValNat 2 (dyadicLabel u).val = u.1 := by
  have hodd : ¬2 ∣ 2*u.2+1 := by omega
  change padicValNat 2 (2^u.1*(2*u.2+1)) = _
  rw [padicValNat.mul (pow_ne_zero _ (by decide)) (Nat.succ_ne_zero _),
    padicValNat.prime_pow,padicValNat.eq_zero_of_not_dvd hodd,add_zero]

/-- Every positive integer has a unique binary occupation and positive odd part. -/
def binaryIndex : (ℕ × ℕ) ≃ ℕ+ := by
  apply Equiv.ofBijective dyadicLabel
  constructor
  · intro u v h
    have hm := congrArg (fun n : ℕ+ => padicValNat 2 n.val) h
    change padicValNat 2 (dyadicLabel u).val = padicValNat 2 (dyadicLabel v).val at hm
    rw [dyadic_valuation,dyadic_valuation] at hm
    have hn := congrArg PNat.val h
    change 2^u.1*(2*u.2+1) = 2^v.1*(2*v.2+1) at hn
    rw [hm] at hn
    have ho := Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2:ℕ)) v.1) hn
    exact Prod.ext hm (by omega)
  · intro n
    obtain ⟨m,b,⟨k,hk⟩,he⟩ := Nat.exists_eq_two_pow_mul_odd n.ne_zero
    refine ⟨(m,k),PNat.coe_injective ?_⟩
    change 2^m*(2*k+1) = n.val
    rw [← hk,← he]

theorem binaryIndex_val (u : ℕ × ℕ) : (binaryIndex u).val = 2^u.1*(2*u.2+1) := rfl

def integerLabel (t : ExceptionalTime) (j : ℕ) (u : Mode t j) := binaryIndex (u.1,pairIndex t j u.2)

theorem binary_occupation (t : ExceptionalTime) (j : ℕ) (u : Mode t j) :
    padicValNat 2 (integerLabel t j u).val = u.1 := dyadic_valuation _

/-- The odd part fixes the paired label, and the dyadic valuation fixes the extra occupation. -/
def completedIndex (t : ExceptionalTime) (j : ℕ) : Mode t j ≃ ℕ+ :=
  ((Equiv.refl ℕ).prodCongr (pairIndex t j)).trans binaryIndex

theorem completedIndex_apply (t : ExceptionalTime) (j : ℕ) (u : Mode t j) :
    completedIndex t j u = integerLabel t j u := rfl

/-- Among real oscillator bases, only two fills the odd sector with every positive integer once. -/
theorem completion_rigid (t : ExceptionalTime) (j : ℕ) (b : ℝ) :
    (∃ e : Mode t j ≃ ℕ+, ∀ u, ((e u).val:ℝ) = b^u.1*(2*(pairIndex t j u.2:ℝ)+1)) ↔ b = 2 := by
  constructor
  · rintro ⟨e,he⟩
    let z := (pairIndex t j).symm 0
    let q := (e (1,z)).val
    have hq : 0 < q := (e (1,z)).pos
    have hb : (q:ℝ) = b := by
      have h := he (1,z)
      simpa only [z,Equiv.apply_symm_apply,Nat.cast_zero,mul_zero,zero_add,pow_one,mul_one] using h
    obtain ⟨u,hu⟩ := e.surjective (2:ℕ+)
    have h := he u
    rw [hu,← hb] at h
    have hn : 2 = q^u.1*(2*pairIndex t j u.2+1) := by exact_mod_cast h
    have hle := Nat.le_mul_of_pos_left (2*pairIndex t j u.2+1) (pow_pos hq u.1)
    have hz : pairIndex t j u.2 = 0 := by omega
    simp only [hz,mul_zero,zero_add,mul_one] at hn
    have htwo : q = 2 := by
      have hn₁ : q ≠ 1 := by intro h₁; rw [h₁,one_pow] at hn; omega
      cases hm : u.1 with
      | zero => rw [hm,pow_zero] at hn; omega
      | succ m =>
        rw [hm,pow_succ] at hn
        have hsmall := Nat.le_mul_of_pos_left q (pow_pos hq m)
        omega
    rw [← hb,htwo,Nat.cast_two]
  · rintro rfl
    refine ⟨completedIndex t j,fun u => ?_⟩
    change ((2^u.1*(2*pairIndex t j u.2+1):ℕ):ℝ) = _
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_two,Nat.cast_add,Nat.cast_one]

/-- Occupation count and the joint centered level contribute additively to energy. -/
def modeEnergy (t : ExceptionalTime) (j : ℕ) (u : Mode t j) :=
  ((u.1:ℝ)+1)*Real.log 2 + energyLevel t j u.2

theorem mode_energy_eq (t : ExceptionalTime) (j : ℕ) (u : Mode t j) :
    modeEnergy t j u = energy (completedIndex t j u) := by
  let n := pairIndex t j u.2
  have hn : 0 < (n:ℝ)+1/2 := by positivity
  have h : (2:ℝ)*(n:ℝ)+1 = 2*((n:ℝ)+1/2) := by ring
  rw [modeEnergy,energyLevel,centeredLevel_eq,energy]
  change ((u.1:ℝ)+1)*Real.log 2+Real.log ((n:ℝ)+1/2) = Real.log ((2^u.1*(2*n+1):ℕ):ℝ)
  push_cast
  rw [h,Real.log_mul (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)) (mul_pos (by norm_num) hn).ne',
    Real.log_pow,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hn.ne']
  ring

/-- Multiplication adds dyadic occupations. Odd indices combine by (2i+1)(2h+1). -/
def fuse (t : ExceptionalTime) (j : ℕ) (u v : Mode t j) : Mode t j :=
  let e := pairIndex t j
  (u.1+v.1,e.symm (e u.2+e v.2+2*e u.2*e v.2))

theorem fusion_label (t : ExceptionalTime) (j : ℕ) (u v : Mode t j) :
    completedIndex t j (fuse t j u v) = completedIndex t j u*completedIndex t j v := by
  apply PNat.coe_injective
  change 2^(u.1+v.1)*(2*pairIndex t j ((pairIndex t j).symm _)+1) =
    (2^u.1*(2*pairIndex t j u.2+1))*(2^v.1*(2*pairIndex t j v.2+1))
  rw [Equiv.apply_symm_apply,pow_add]
  ring

theorem fusion_energy (t : ExceptionalTime) (j : ℕ) (u v : Mode t j) :
    modeEnergy t j (fuse t j u v) = modeEnergy t j u+modeEnergy t j v := by
  rw [mode_energy_eq,fusion_label,energy_mul,mode_energy_eq,mode_energy_eq]

def occupationState (t : ExceptionalTime) (j : ℕ) : (Nat.Primes →₀ ℕ) ≃ Mode t j :=
  PrimeGas.label.trans (completedIndex t j).symm

theorem single_prime_state (t : ExceptionalTime) (j : ℕ) (p : Nat.Primes) :
    (completedIndex t j (occupationState t j (Finsupp.single p 1))).val = p.val := by
  change (completedIndex t j ((completedIndex t j).symm (PrimeGas.label (Finsupp.single p 1)))).val = _
  rw [Equiv.apply_symm_apply]
  exact label_one_quantum p

theorem occupation_fusion (t : ExceptionalTime) (j : ℕ) (u v : Nat.Primes →₀ ℕ) :
    occupationState t j (u+v) = fuse t j (occupationState t j u) (occupationState t j v) := by
  apply (completedIndex t j).injective
  change completedIndex t j ((completedIndex t j).symm (PrimeGas.label (u+v))) = _
  rw [Equiv.apply_symm_apply,label_add,fusion_label]
  change _ = completedIndex t j ((completedIndex t j).symm (PrimeGas.label u)) *
    completedIndex t j ((completedIndex t j).symm (PrimeGas.label v))
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]

abbrev CompleteGas (t : ExceptionalTime) (j : ℕ) := lp (fun _ : Mode t j => ℂ) 2

def basisUnitary (t : ExceptionalTime) (j : ℕ) : CompleteGas t j ≃ₗᵢ[ℂ] Gas :=
  HTGeometry.lpReindexEquiv (completedIndex t j)

private theorem half_sum (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    Summable (fun u : Mode t j => ‖heat (s.val/2) (completedIndex t j u)‖^2) :=
  (completedIndex t j).summable_iff.mpr ((summable_heat_sq_iff (s.val/2)).mpr
    (by rw [Complex.div_ofNat_re]; linarith only [s.property]))

def completedGibbs (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    CompleteGas t j →L[ℂ] CompleteGas t j :=
  let H := HilbertSchmidt.diagOp (fun u => heat (s.val/2) (completedIndex t j u)) (half_sum t j s)
  H ∘L H

private theorem completed_action (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re})
    (f : CompleteGas t j) (u : Mode t j) :
    completedGibbs t j s f u = heat s.val (completedIndex t j u)*f u := by
  simp only [completedGibbs,ContinuousLinearMap.comp_apply,HilbertSchmidt.diagOp_apply,← mul_assoc,← heat_add,add_halves]

theorem completed_action_energy (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re})
    (f : CompleteGas t j) (u : Mode t j) :
    completedGibbs t j s f u = Complex.exp (-s.val*(modeEnergy t j u:ℂ))*f u := by
  rw [mode_energy_eq,completed_action,heat]

theorem gibbs_intertwining (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) (f : CompleteGas t j) :
    basisUnitary t j (completedGibbs t j s f) = gibbsOperator s (basisUnitary t j f) := by
  apply lp.ext
  funext n
  simp only [basisUnitary,HTGeometry.lpReindexEquiv_apply,completed_action,Equiv.apply_symm_apply,gibbsOperator_apply]

/-- Adding the single prime-two oscillator restores exactly the full zeta trace. -/
theorem completed_trace (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    ContinuousLinearMap.opTrace (completedGibbs t j s) = riemannZeta s.val := by
  rw [← partition_eq_zeta s,completedGibbs,gibbsOperator,HilbertSchmidt.opTrace_diagOp_comp,
    HilbertSchmidt.opTrace_diagOp_comp]
  exact (completedIndex t j).tsum_eq (fun n => heat (s.val/2) n*heat (s.val/2) n)

#print axioms completedIndex
#print axioms binary_occupation
#print axioms completion_rigid
#print axioms single_prime_state
#print axioms fusion_energy
#print axioms occupation_fusion
#print axioms completed_action_energy
#print axioms gibbs_intertwining
#print axioms completed_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
