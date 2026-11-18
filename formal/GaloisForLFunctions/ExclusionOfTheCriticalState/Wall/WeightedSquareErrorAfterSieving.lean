import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SubcriticalMeanSquareOfTheIntegerQuadrature
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.RemovingSmallPrimesFromTheDensityReference
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Weighted square error after sieving the integer reference

Each prime acts by a difference of translates. Translation is an isometry in
L², so the density-normalized error costs the product of the local factors.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- The L² translation bound at a single sieving prime. -/
def tiltSieveFactor (β : ℝ) (p : Nat.Primes) : ℝ :=
  (1+Real.exp (β*Real.log (p:ℕ))/Real.sqrt (p:ℕ))/(1-((p:ℕ):ℝ)⁻¹)

private theorem half_le_sieve_denominator (p : Nat.Primes) : 1/2 ≤ 1-((p:ℕ):ℝ)⁻¹ := by
  have hp : (2:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.2.two_le
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hp
  rw [one_div ((p:ℕ):ℝ)] at h
  linarith only [h]

theorem tiltSieveFactor_nonneg (β : ℝ) (p : Nat.Primes) : 0 ≤ tiltSieveFactor β p :=
  div_nonneg (by positivity) (by linarith only [half_le_sieve_denominator p])

theorem tiltSieveFactor_le_four {β : ℝ} (hβ : β ≤ 1/2) (p : Nat.Primes) :
    tiltSieveFactor β p ≤ 4 := by
  have hx : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
  have hroot : Real.sqrt (p:ℕ) = Real.exp (Real.log (p:ℕ)/2) := by rw [Real.exp_half,Real.exp_log hx]
  have ha : Real.exp (β*Real.log (p:ℕ))/Real.sqrt (p:ℕ) ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 hx),hroot,Real.exp_le_exp]
    linarith only [mul_le_mul_of_nonneg_right hβ (Real.log_natCast_nonneg (p:ℕ))]
  unfold tiltSieveFactor
  rw [div_le_iff₀ (by linarith only [half_le_sieve_denominator p])]
  linarith only [ha,half_le_sieve_denominator p]

/-- On the unweighted line the factor reduces to the half-power sieve cost. -/
theorem tiltSieveFactor_zero (p : Nat.Primes) :
    tiltSieveFactor 0 p=(1-(Real.sqrt (p:ℕ))⁻¹)⁻¹ := by
  let a := (Real.sqrt (p:ℕ))⁻¹
  have ha : a^2=((p:ℕ):ℝ)⁻¹ := by dsimp only [a]; rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  have h1 : a < 1 := (inv_lt_one_iff₀).2 (Or.inr (by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one (one_lt_prime_cast p)))
  simp only [tiltSieveFactor,zero_mul,Real.exp_zero,one_div]
  change (1+a)/(1-((p:ℕ):ℝ)⁻¹)=(1-a)⁻¹
  have hden : 0 < 1-((p:ℕ):ℝ)⁻¹ := by linarith only [half_le_sieve_denominator p]
  field_simp [hden.ne',(sub_pos.2 h1).ne']
  nlinarith only [ha]

/-- Exact product upper bound on the weighted norm after a finite sieve. -/
theorem tilted_sieve_error_norm_le (P : Finset Nat.Primes) {Φ : ℝ → ℝ} {A β : ℝ}
    (hf : ∀ t : ℝ, Summable (fun n : ℕ => continuousIntegerAtom Φ n t))
    (hbase : MemLp (fun t => Real.exp (β*t)*sievedReferenceError ∅ Φ A t) 2) :
    let g := fun (Q : Finset Nat.Primes) (t : ℝ) => Real.exp (β*t)*sievedReferenceError Q Φ A t
    MemLp (g P) 2 ∧ lpNorm (g P) 2 volume ≤ (∏ p ∈ P, tiltSieveFactor β p)*lpNorm (g ∅) 2 volume := by
  let g := fun (Q : Finset Nat.Primes) (t : ℝ) => Real.exp (β*t)*sievedReferenceError Q Φ A t
  change MemLp (g P) 2 ∧ lpNorm (g P) 2 volume ≤ (∏ p ∈ P, tiltSieveFactor β p)*lpNorm (g ∅) 2 volume
  classical
  induction P using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,one_mul] using And.intro hbase (le_refl (lpNorm (g ∅) 2 volume))
  | @insert p Q hp ih =>
    let x : ℝ := (p:ℕ)
    let L := Real.log x
    let a := Real.exp (β*L)/Real.sqrt x
    let b := (1-x⁻¹)⁻¹
    let G := fun t : ℝ => g Q (t-L)
    have hx0 : 0 < x := by exact_mod_cast p.2.pos
    have ha : 0 ≤ a := div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
    have hb : 0 ≤ b := inv_nonneg.2 (by linarith only [half_le_sieve_denominator p])
    have he : g (insert p Q) = b • (g Q-a • G) := by
      funext t
      dsimp only [g,G,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
      rw [sievedReferenceError_insert hp (hf t)]
      have hx' : Real.exp (β*t)*(Real.sqrt x)⁻¹=a*Real.exp (β*(t-L)) := by
        dsimp only [a]
        rw [mul_sub,Real.exp_sub]
        field_simp [(Real.exp_pos _).ne',(Real.sqrt_pos.2 hx0).ne'] <;> ring
      change Real.exp (β*t)*((sievedReferenceError Q Φ A t-(Real.sqrt x)⁻¹*sievedReferenceError Q Φ A (t-L))/(1-x⁻¹)) = _
      dsimp only [b]
      linear_combination -(1-x⁻¹)⁻¹*sievedReferenceError Q Φ A (t-L)*hx'
    have hpres := measurePreserving_sub_right volume L
    have hG : MemLp G 2 := ih.1.comp_measurePreserving hpres
    have hnorm : lpNorm G 2 volume = lpNorm (g Q) 2 volume := by
      rw [← toReal_eLpNorm hG.1,← toReal_eLpNorm ih.1.1]
      exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving ih.1.1 hpres)
    rw [he,Finset.prod_insert hp]
    refine ⟨(ih.1.sub (hG.const_smul a)).const_smul b,?_⟩
    rw [lpNorm_const_smul]
    change ‖b‖*lpNorm (g Q-a • G) 2 volume ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg hb]
    have hsub := lpNorm_sub_le (g := a • G) ih.1 (by norm_num)
    rw [lpNorm_const_smul,hnorm] at hsub
    change _ ≤ lpNorm (g Q) 2 volume + ‖a‖*lpNorm (g Q) 2 volume at hsub
    rw [Real.norm_eq_abs,abs_of_nonneg ha] at hsub
    calc _ ≤ b*(lpNorm (g Q) 2 volume+a*lpNorm (g Q) 2 volume) := mul_le_mul_of_nonneg_left hsub hb
      _ = tiltSieveFactor β p*lpNorm (g Q) 2 volume := by dsimp only [tiltSieveFactor,b,a,L,x]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left ih.2 (tiltSieveFactor_nonneg β p)).trans_eq (mul_assoc ..).symm

/-- For the actual state the base norm is finite on every subcritical line.
The bound is uniform over the sizes of the removed primes. -/
theorem criticalState_sieved_integer_quadrature {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) (P : Finset Nat.Primes) :
    let g := fun t : ℝ => Real.exp (β*t)*sievedReferenceError P Φ (∫ u, Real.exp (-u/2)*Φ u) t
    MemLp g 2 ∧ lpNorm g 2 volume ≤ (∏ p ∈ P, tiltSieveFactor β p)*lpNorm (tiltedIntegerError Φ β) 2 volume ∧
      lpNorm g 2 volume ≤ (4:ℝ)^P.card*lpNorm (tiltedIntegerError Φ β) 2 volume := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  have h0 : (fun t => Real.exp (β*t)*sievedReferenceError ∅ Φ A t)=tiltedIntegerError Φ β := by
    funext t; simp only [sievedReferenceError,sievedIntegerReference_empty hb,tiltedIntegerError,A]
  have hbase := criticalState_subcritical_integer_error hW ht hF hc he hC hb hβ hβ'
  have h := tilted_sieve_error_norm_le P (A := A) (β := β) (summable_continuousIntegerAtom hb) (h0.symm ▸ hbase)
  dsimp only at h
  rw [h0] at h
  refine ⟨h.1,h.2,h.2.trans (mul_le_mul_of_nonneg_right ?_ lpNorm_nonneg)⟩
  calc (∏ p ∈ P, tiltSieveFactor β p) ≤ ∏ _p ∈ P, (4:ℝ) :=
         Finset.prod_le_prod (fun _ _ => tiltSieveFactor_nonneg ..) (fun _ _ => tiltSieveFactor_le_four hβ'.le _)
    _ = _ := by simp

#print axioms criticalState_sieved_integer_quadrature
end GaloisForLFunctions.ExclusionOfTheCriticalState
