import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineArc

/-! # Finite occupation waves and their heat coordinates -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open InnerProductSpace

/-- A real superposition supported on the first m occupation modes. -/
def finiteModes {m : ℕ} (c : Fin m → ℝ) : Gas :=
  ∑ i, (c i:ℂ) • modeWave (number i.val)

theorem finiteModes_at {m : ℕ} (c : Fin m → ℝ) (i : Fin m) :
    finiteModes c (number i.val) = (c i:ℂ) := by
  simp only [finiteModes,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [modeWave,lp.single_apply]
  · intro j _ hj
    have hn : number i.val ≠ number j.val := fun h => hj (Fin.ext (number_injective h).symm)
    simp only [modeWave,lp.single_apply,Pi.single_eq_of_ne hn,mul_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

theorem finiteModes_inner {m : ℕ} (c d : Fin m → ℝ) :
    inner ℂ (finiteModes c) (finiteModes d) = ((∑ i, c i*d i : ℝ):ℂ) := by
  change inner ℂ (∑ i, (c i:ℂ) • modeWave (number i.val)) (finiteModes d) = _
  rw [sum_inner,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left,Complex.conj_ofReal,Complex.ofReal_mul]
  congr 1
  simp [modeWave,lp.inner_single_left,finiteModes_at]

theorem finiteModes_norm_sq {m : ℕ} (c : Fin m → ℝ) : ‖finiteModes c‖^2 = ∑ i, c i^2 := by
  have he : inner ℂ (finiteModes c) (finiteModes c) = ((‖finiteModes c‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K _
  simpa only [← sq] using Complex.ofReal_inj.mp (he.symm.trans (finiteModes_inner c c))

theorem finiteModes_heat {m : ℕ} (c : Fin m → ℝ) :
    criticalOperator (finiteModes c) = finiteModes (fun i => attenuation (number i.val)*c i) := by
  simp only [finiteModes,map_sum,map_smul,heat_modeWave,smul_smul,Complex.ofReal_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [mul_comm])

theorem finiteModes_square {m : ℕ} (c : Fin m → ℝ) :
    squareHeat.val (finiteModes c) = finiteModes (fun i => occupationWeight i.val*c i) := by
  change criticalOperator (criticalOperator (finiteModes c)) = _
  rw [finiteModes_heat,finiteModes_heat]
  simp only [occupationWeight,sq,mul_assoc]

theorem finiteModes_sub {m : ℕ} (c d : Fin m → ℝ) :
    finiteModes c-finiteModes d = finiteModes (fun i => c i-d i) := by
  simp only [finiteModes,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

theorem finiteModes_smul {m : ℕ} (s : ℝ) (c : Fin m → ℝ) :
    (s:ℂ) • finiteModes c = finiteModes (fun i => s*c i) := by
  simp only [finiteModes,Finset.smul_sum,smul_smul,Complex.ofReal_mul]

#print axioms finiteModes_norm_sq
#print axioms finiteModes_square

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
