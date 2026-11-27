import GaloisForLFunctions.«arithmetic-positivity-theory».SingleHeightPhaseSelectiveApertureAndPowerSaving

/-! # Relatively dense simultaneous returns of finite prime-power observations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across

open Set Finset Real
open GaloisForLFunctions.SquareRootThreshold (primeIndices)
open GaloisForLFunctions.ArithmeticPositivityTheory (exists_relDense_height_prime_phase_approx)

def unitPhase (y : ℝ) := Complex.exp ((y : ℂ)*Complex.I)

theorem real_power (y : ℝ) (k : ℕ) :
    ((unitPhase y)^k).re=cos ((k : ℝ)*y) := by
  rw [unitPhase,←Complex.exp_nat_mul]
  rw [show (k : ℂ)*((y : ℂ)*Complex.I)=(((k : ℝ)*y : ℝ) : ℂ)*Complex.I by push_cast; ring]
  simp [Complex.exp_re]

/-- Every neighborhood of a prescribed observation recurs with bounded
gaps. The interval is in physical height, before multiplication by log p. -/
theorem returns (F : Finset Nat.Primes) (θ : F → ℝ) (f : (F → ℂ) → ℝ) (hf : Continuous f)
    (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, ∃ t ∈ Set.Icc T (T+L),
      |f (fun p => unitPhase (t*log p.val.val))-f (fun p => unitPhase (θ p))|<ε := by
  classical
  let z (p : F) := unitPhase (θ p)
  obtain ⟨δ,hδ,near⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := z)) ε hε
  let N := F.sup (fun p => p.val)
  let lift (n : ℕ) : ℝ := if pn : n.Prime then
    if inF : (⟨n,pn⟩ : Nat.Primes)∈F then θ ⟨⟨n,pn⟩,inF⟩ else 0 else 0
  have lifted (p : F) : lift p.val.val=θ p := by
    rcases p with ⟨⟨n,hn⟩,hF⟩
    simp only [lift,dif_pos hn]
    split
    · rfl
    · rename_i outside
      exact (outside hF).elim
  obtain ⟨length,pos,visit⟩ := exists_relDense_height_prime_phase_approx N lift hδ
  refine ⟨2*π*length,mul_pos two_pi_pos pos,fun T => ?_⟩
  obtain ⟨u,hu,approx⟩ := visit (T/(2*π))
  refine ⟨2*π*u,⟨?_,?_⟩,?_⟩
  · linarith only [(div_le_iff₀ two_pi_pos).mp hu.1]
  · have bound := mul_le_mul_of_nonneg_left hu.2 two_pi_pos.le
    have recover : 2*π*(T/(2*π))=T := by rw [mul_comm,div_mul_cancel₀ _ two_pi_pos.ne']
    rw [mul_add,recover] at bound
    exact bound
  · apply near
    apply (dist_pi_lt_iff hδ).mpr
    intro p
    have mem : p.val.val ∈ primeIndices N :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨p.val.property.two_le,le_sup p.property⟩,p.val.property⟩
    have hp := approx p.val.val mem
    rw [lifted p] at hp
    rw [dist_eq_norm]
    change ‖unitPhase (2*π*u*log p.val.val)-unitPhase (θ p)‖<δ
    have phaseEq : unitPhase (2*π*u*log p.val.val) =
        Complex.exp (2*(π : ℂ)*Complex.I*(u : ℂ)*(log p.val.val : ℂ)) := by
      unfold unitPhase
      push_cast
      congr 1
      ring
    rw [phaseEq]
    exact hp

#print axioms real_power
#print axioms returns

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across
