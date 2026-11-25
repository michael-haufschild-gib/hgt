import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.GapDeterminant

/-! # Removing the forced zero gaps from a gap determinant -/

open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows.UniformForecasts
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Only off-diagonal differences test a genuine closing pair. Give
the diagonal positions factor one so the product still runs over I². -/
def gapFactor (E : I→ℝ) (b : ℝ) (p : I×I) : ℝ :=
  if p.1=p.2 then 1 else |b-(E p.1-E p.2)|

def reducedProduct (E : I→ℝ) (b : ℝ) : ℝ := ∏ p : I×I, gapFactor E b p

/-- The D identically zero diagonal gaps contribute precisely |b|^D,
regardless of other degeneracies. -/
theorem gap_norm_factor (H : Matrix I I ℂ) (h : H.IsHermitian) (b : ℝ) :
    ‖(Matrix.scalar (I×I) (b:ℂ)-gapOperator H).det‖ =
      |b|^(Fintype.card I)*reducedProduct h.eigenvalues b := by
  rw [gap_determinant H h,norm_prod]
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  let f (p : I×I) := if p.1=p.2 then |b| else 1
  have hd (p : I×I) : |b-(h.eigenvalues p.1-h.eigenvalues p.2)|=f p*gapFactor h.eigenvalues b p := by
    by_cases hp : p.1=p.2 <;> simp only [f,gapFactor,hp,ite_true,ite_false,sub_self,sub_zero,mul_one,one_mul]
  have hf : (∏ p : I×I, f p)=|b|^(Fintype.card I) := by
    rw [Fintype.prod_prod_type]
    simp only [f,Finset.prod_ite_eq,Finset.mem_univ,ite_true,Finset.prod_const,Finset.card_univ]
  simp_rw [hd]
  rw [Finset.prod_mul_distrib,hf,reducedProduct]

/-- Separation from an entire off-diagonal gap list supplies a witness
uniform even as the forecast tends to zero. -/
theorem reduced_lower (E : I→ℝ) (b r : ℝ) (hr : 0≤r)
    (h : ∀ i j, i≠j → r≤ |b-(E i-E j)|) :
    (min 1 r)^(Fintype.card I^2) ≤ reducedProduct E b := by
  have hh := Finset.prod_le_prod (s:=Finset.univ) (fun (_ : I×I) _ => le_min zero_le_one hr)
    (fun (p : I×I) _ => show min 1 r≤gapFactor E b p by
      by_cases hp : p.1=p.2
      · simpa only [gapFactor,if_pos hp] using min_le_left 1 r
      · simpa only [gapFactor,if_neg hp] using (min_le_right 1 r).trans (h _ _ hp))
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,pow_two,reducedProduct] using hh

/-- One actual closing gap accounts for the small factor. Every remaining
factor is bounded using just the energy and forecast magnitudes. -/
theorem reduced_upper (E : I→ℝ) (b L : ℝ) (hL : ∀ i, |E i|≤L)
    {i j : I} (hij : i≠j) :
    reducedProduct E b ≤ |b-(E i-E j)| * (1+|b|+2*max L 0)^(Fintype.card I^2) := by
  let M := 1+|b|+2*max L 0
  have hM : 1≤M := by dsimp only [M]; linarith only [abs_nonneg b,le_max_right L 0]
  have h₀ (p : I×I) : 0≤gapFactor E b p := by
    unfold gapFactor
    split
    · exact zero_le_one
    · exact abs_nonneg _
  have hb (p : I×I) : gapFactor E b p≤M := by
    unfold gapFactor
    split
    · exact hM
    · exact (abs_sub _ _).trans ((add_le_add (le_refl _) (abs_sub _ _)).trans
        (by dsimp only [M]; linarith only [hL p.1,hL p.2,le_max_left L 0]))
  rw [reducedProduct,←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (i,j)),
    show gapFactor E b (i,j)=_ from if_neg hij]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (Finset.prod_le_prod (s:=Finset.univ.erase (i,j)) (fun p _ => h₀ p) (fun p _ => hb p)).trans ?_
  rw [Finset.prod_const]
  apply pow_le_pow_right₀ hM
  simpa only [Finset.card_univ,Fintype.card_prod,pow_two] using Finset.card_le_card (Finset.erase_subset (i,j) Finset.univ)

#print axioms gap_norm_factor
#print axioms reduced_lower
#print axioms reduced_upper
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows.UniformForecasts
