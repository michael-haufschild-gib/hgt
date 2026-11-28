import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.SinePolynomial

/-! # Recovering centered eigenangles from four normalized traces -/

open Real Finset
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

def angleMean (a : I → ℝ) := (∑ j, a j)/(Fintype.card I:ℝ)

/-- Imaginary part of a phase multiplied by its conjugate normalized trace. -/
def sineReading (θ : I → ℝ) (l : ℕ) (i : I) :=
  sin (l*θ i)*angleMean (fun j => cos (l*θ j))-
  cos (l*θ i)*angleMean (fun j => sin (l*θ j))

omit [Nonempty I] in
private theorem reading_eq (θ : I → ℝ) (l : ℕ) (i : I) :
    sineReading θ l i=angleMean (fun j => sin (l*(θ i-θ j))) := by
  simp only [sineReading,angleMean,mul_sub,Real.sin_sub,sum_sub_distrib,←mul_sum]
  ring

/-- Centering costs a single global phase. Every pairwise difference enters
the scalar sine estimate, with the same trace coefficients for all levels. -/
theorem trace_angles (θ : I → ℝ) (hw : ∀ i j, |θ i-θ j|≤1) (i : I) :
    |(θ i-angleMean θ)-
      (8/5*sineReading θ 1 i-2/5*sineReading θ 2 i+
        8/105*sineReading θ 3 i-1/140*sineReading θ 4 i)|≤1/630 := by
  have hD : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have h (j : I) : |(θ i-θ j)-sinePolynomial (θ i-θ j)|≤1/630 :=
    (sine_error _).trans (div_le_div_of_nonneg_right
      (by simpa using pow_le_pow_left₀ (abs_nonneg _) (hw i j) 9) (by norm_num))
  have he : ∀ j, (θ i-θ j)-sinePolynomial (θ i-θ j)=
      θ i-θ j-(8/5*sin (θ i-θ j)-2/5*sin (2*(θ i-θ j))+
        8/105*sin (3*(θ i-θ j))-1/140*sin (4*(θ i-θ j))) := fun _ => rfl
  have hav : |angleMean (fun j => (θ i-θ j)-sinePolynomial (θ i-θ j))|≤1/630 := by
    rw [angleMean,abs_div,abs_of_pos hD,div_le_iff₀ hD]
    calc
      _ ≤ ∑ j, |(θ i-θ j)-sinePolynomial (θ i-θ j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : I, (1/630:ℝ) := sum_le_sum fun j _ => h j
      _ = _ := by simp [nsmul_eq_mul,mul_comm]
  rw [angleMean] at hav
  simp only [reading_eq,Nat.cast_one,one_mul,Nat.cast_ofNat,angleMean]
  convert hav using 1
  congr 1
  simp only [he,sum_sub_distrib,sum_add_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul]
  field_simp

#print axioms trace_angles
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
