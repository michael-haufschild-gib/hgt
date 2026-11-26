import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.BorrowedWire.Sector

/-! # Uniform square-root convergence on both states of a borrowed wire -/

open Matrix Complex
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire
noncomputable section

private abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ

/-- Conjugate by the control phase diag(a,1). -/
def twist (a : ℂ) (P : M₂) : M₂ :=
  !![a,0;0,1]*P*!![star a,0;0,1]

private theorem twist_sector (a : ℂ) (ha : a*star a=1) (x : ℝ) (u : ℂ) :
    twist a (sector x u)=sector x (a*u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twist,sector,pulse,Matrix.mul_apply,Fin.sum_univ_two,star_mul]
  all_goals linear_combination (x:ℂ)*ha

private theorem twist_smul (a z : ℂ) (P : M₂) : twist a (z • P)=z • twist a P := by
  simp only [twist,Matrix.mul_smul,Matrix.smul_mul]

/-- In the eigenphase z, the inverse square compensates the global
phase of the four extra controlled queries. -/
def refinePhase (z a : ℂ) (P : M₂) : M₂ :=
  (z^2)⁻¹ • (twist a P*(twist (star a) P*P*twist (star a) P)*twist a P)

private theorem refine_sector (ζ a : ℂ) (hζ : ζ≠0) (ha : a*star a=1) (x : ℝ) (u : ℂ) :
    refinePhase (ζ^2) a (ζ • sector x u)=ζ •
      (sector x (a*u)*(sector x (star a*u)*sector x u*sector x (star a*u))*sector x (a*u)) := by
  have hb : star a*star (star a)=1 := by rwa [star_star,mul_comm]
  simp only [refinePhase,twist_smul,twist_sector a ha,twist_sector (star a) hb,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  field_simp

/-- One controlled query in the Hadamard basis, followed by j
refinements. The matrix is defined using only z and z inverse. -/
def rootApprox (z : ℂ) : ℕ→M₂
  | 0 => !![(1+z)/2,(1-z)/2;(1-z)/2,(1+z)/2]
  | j+1 => refinePhase z multiplier (rootApprox z j)

private theorem first_sector {ζ : ℂ} (hζ : normSq ζ=1) :
    rootApprox (ζ^2) 0=ζ • sector ζ.re (-(ζ.im:ℂ)*I) := by
  have h : ζ.re^2+ζ.im^2=1 := by simpa only [Complex.normSq_apply,pow_two] using hζ
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [rootApprox,sector,pulse,pow_two,Complex.div_re,Complex.div_im,Complex.mul_re,
      Complex.mul_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im] <;> nlinarith only [h]

/-- Squared leakage is at most the initial squared leakage to the
power 3^j. The same real diagonal controls the two possible spectator
states, including their coherent superpositions. -/
theorem rootApprox_sector {ζ : ℂ} (hζ : normSq ζ=1) (hx : 0≤ζ.re) (j : ℕ) :
    ∃ x : ℝ, ∃ u : ℂ, rootApprox (ζ^2) j=ζ • sector x u ∧
      0≤x ∧ x^2+normSq u=1 ∧ normSq u≤(ζ.im^2)^(3^j) := by
  induction j with
  | zero =>
    have h : ζ.re^2+ζ.im^2=1 := by simpa only [Complex.normSq_apply,pow_two] using hζ
    have hn : normSq (-(ζ.im:ℂ)*I)=ζ.im^2 := by
      simp [pow_two]
    exact ⟨ζ.re,-(ζ.im:ℂ)*I,first_sector hζ,hx,by rwa [hn],by rw [hn,pow_zero,pow_one]⟩
  | succ j ih =>
    obtain ⟨x,u,hmat,hx,hu,hsmall⟩ := ih
    obtain ⟨v,hv,hy,hpoly,hunit⟩ := five_sector hx hu
    have hz : ζ≠0 := fun h => by simp [h] at hζ
    refine ⟨_,v,?_,hy,hunit,?_⟩
    · rw [rootApprox,hmat,refine_sector ζ multiplier hz multiplier_unit]
      change ζ • five x u=_
      rw [hv]
    · have h := (five_pulse_leakage hx (Complex.normSq_nonneg u) hu).2.2
      have hpow := pow_le_pow_left₀ (Complex.normSq_nonneg u) hsmall 3
      rw [←pow_mul (ζ.im^2),←pow_succ (3:ℕ) j] at hpow
      linarith only [h,hunit,hpow]

#print axioms rootApprox_sector
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire
