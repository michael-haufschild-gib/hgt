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
  simp only [one_div] at *
  nlinarith only [ha]

private def tiltedSievedReference (P : Finset Nat.Primes) (Φ : ℝ → ℝ) (A β t : ℝ) : ℝ :=
  Real.exp (β*t)*sievedReferenceError P Φ A t

private theorem tiltedSievedReference_insert {p : Nat.Primes} {Q : Finset Nat.Primes} (hp : p ∉ Q)
    {Φ : ℝ → ℝ} (A β : ℝ) (hf : ∀ t : ℝ, Summable (fun n : ℕ => continuousIntegerAtom Φ n t)) :
    let x : ℝ := (p:ℕ)
    let L := Real.log x
    let a := Real.exp (β*L)/Real.sqrt x
    let g := tiltedSievedReference Q Φ A β
    tiltedSievedReference (insert p Q) Φ A β =
      (1-x⁻¹)⁻¹ • (g-a • (fun t => g (t-L))) := by
  dsimp only
  funext t
  simp only [tiltedSievedReference,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,sievedReferenceError_insert hp (hf t),
    mul_sub β t,Real.exp_sub,div_eq_mul_inv]
  field_simp [(Real.exp_pos (β*Real.log ((p:ℕ):ℝ))).ne']

/-- The two translates in a local sieve factor act on L² with cost at most
the sum of their absolute coefficients. -/
private theorem norm_two_translates {g : ℝ → ℝ} (hg : MemLp g 2) (L a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let f := b • (g-a • (fun t => g (t-L)))
    MemLp f 2 ∧ lpNorm f 2 volume ≤ b*(1+a)*lpNorm g 2 volume := by
  let G := fun t => g (t-L)
  have hpres := measurePreserving_sub_right volume L
  have hG : MemLp G 2 := hg.comp_measurePreserving hpres
  have hnorm : lpNorm G 2 volume = lpNorm g 2 volume := by
    rw [← toReal_eLpNorm hG.1,← toReal_eLpNorm hg.1]
    exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hg.1 hpres)
  change MemLp (b • (g-a • G)) 2 ∧ _
  refine ⟨(hg.sub (hG.const_smul a)).const_smul b,?_⟩
  change lpNorm (b • (g-a • G)) 2 volume ≤ _
  have hsub := lpNorm_sub_le (g := a • G) hg (by norm_num)
  rw [lpNorm_const_smul,hnorm] at hsub
  change _ ≤ lpNorm g 2 volume + ‖a‖*lpNorm g 2 volume at hsub
  rw [Real.norm_eq_abs,abs_of_nonneg ha] at hsub
  rw [lpNorm_const_smul]
  change ‖b‖*lpNorm (g-a • G) 2 volume ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg hb]
  exact (mul_le_mul_of_nonneg_left hsub hb).trans_eq (by ring)

/-- Exact product upper bound on the weighted norm after a finite sieve. -/
theorem tilted_sieve_error_norm_le (P : Finset Nat.Primes) {Φ : ℝ → ℝ} {A β : ℝ}
    (hf : ∀ t : ℝ, Summable (fun n : ℕ => continuousIntegerAtom Φ n t))
    (hbase : MemLp (fun t => Real.exp (β*t)*sievedReferenceError ∅ Φ A t) 2) :
    let g := fun (Q : Finset Nat.Primes) (t : ℝ) => Real.exp (β*t)*sievedReferenceError Q Φ A t
    MemLp (g P) 2 ∧ lpNorm (g P) 2 volume ≤ (∏ p ∈ P, tiltSieveFactor β p)*lpNorm (g ∅) 2 volume := by
  let g := fun Q => tiltedSievedReference Q Φ A β
  change MemLp (g P) 2 ∧ lpNorm (g P) 2 volume ≤ (∏ p ∈ P, tiltSieveFactor β p)*lpNorm (g ∅) 2 volume
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,one_mul,g,le_refl,and_true]
    exact hbase
  | @insert p Q hp ih =>
    let x : ℝ := (p:ℕ)
    let a := Real.exp (β*Real.log x)/Real.sqrt x
    let b := (1-x⁻¹)⁻¹
    have ha : 0 ≤ a := div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
    have hb : 0 ≤ b := inv_nonneg.2 (by change 0 ≤ 1-((p:ℕ):ℝ)⁻¹; linarith only [half_le_sieve_denominator p])
    have hs := norm_two_translates (g := g Q) ih.1 (Real.log x) a b ha hb
    have heq : g (insert p Q)=b • (g Q-a • (fun t => g Q (t-Real.log x))) :=
      tiltedSievedReference_insert hp A β hf
    have hfac : b*(1+a)=tiltSieveFactor β p := by dsimp only [b,a,x,tiltSieveFactor]; ring
    dsimp only at hs
    rw [heq,Finset.prod_insert hp]
    refine ⟨hs.1,hs.2.trans ?_⟩
    rw [hfac,mul_assoc]
    exact mul_le_mul_of_nonneg_left ih.2 (tiltSieveFactor_nonneg β p)

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
