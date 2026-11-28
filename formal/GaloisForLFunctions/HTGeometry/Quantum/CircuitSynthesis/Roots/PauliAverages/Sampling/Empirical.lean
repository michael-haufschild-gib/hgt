import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Sampling.Moment

/-! # A short equal-weight approximation to a Hermitian matrix mean -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
noncomputable section
variable {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype X] [Nonempty X]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Uniform arithmetic mean, with a real scalar acting on complex matrices. -/
def matrixMean (A : X → Mat I) : Mat I := (Fintype.card X:ℝ)⁻¹ • ∑ x, A x

/-- In dimension at most $2^{2k}$, a list of $kn^2$ samples
approximates the mean of matrices of norm at most $R$ to operator error $8R/n$. -/
theorem empirical_mean (A : X → Mat I) (hh : ∀ x, (A x).IsHermitian)
    {R : ℝ} (hr : 0≤R) (hb : ∀ x, ‖A x‖≤R)
    (n k : ℕ) (hn : 0<n) (hk : 0<k) (hd : Fintype.card I≤2^(2*k)) :
    ∃ a : Fin (k*n^2) → X, ‖matrixMean (A ∘ a)-matrixMean A‖≤8*R/n := by
  have hx : (0:ℝ)<Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  let μ := matrixMean A
  let C (x : X) := A x-μ
  have hm : ‖μ‖≤R := by
    rw [show μ=(Fintype.card X:ℝ)⁻¹ • ∑ x, A x by rfl,norm_smul,Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (Fintype.card X:ℝ)⁻¹*(∑ _ : X, R) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun x _ => hb x)) (by positivity)
      _ = R := by simp [nsmul_eq_mul,hx.ne']
  have hz : ∑ x, C x=0 := by
    simp only [C,sum_sub_distrib,sum_const,card_univ,μ,matrixMean]
    rw [←Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ hx.ne',one_smul,sub_self]
  have hsumherm : (∑ x, A x).IsHermitian := by
    change (∑ x, A x).conjTranspose=_
    rw [Matrix.conjTranspose_sum]
    exact sum_congr rfl fun x _ => hh x
  have hhμ : μ.IsHermitian := hsumherm.smul (by simp : IsSelfAdjoint (Fintype.card X:ℝ)⁻¹)
  haveI : Nonempty (Fin (k*n^2)) := Fin.pos_iff_nonempty.mp (by positivity)
  have hkn : k≤Fintype.card (Fin (k*n^2)) := by
    rw [Fintype.card_fin]
    calc k = k*1 := (Nat.mul_one k).symm
         _ ≤ _ := Nat.mul_le_mul_left _ (show 0<n^2 by positivity)
  obtain ⟨a,ha⟩ := exists_sample_moment (J:=Fin (k*n^2)) C hz (fun x => (hh x).sub hhμ)
    (show 0≤2*R by positivity) (fun x => (norm_sub_le ..).trans (by linarith [hb x,hm])) k hkn
  have hd' : (Fintype.card I:ℝ)≤(2:ℝ)^(2*k) := by exact_mod_cast hd
  have hsum : ‖∑ j, C (a j)‖≤8*k*n*R := by
    apply le_of_pow_le_pow_left₀ (by omega : 2*k≠0) (by positivity)
    rw [Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] at ha
    apply ha.trans
    calc
      _ ≤ (2:ℝ)^(2*k)*(4*((k:ℝ)*n^2)*k)^k*(2*R)^(2*k) := by gcongr
      _ = (8*k*n*R)^(2*k) := by
        rw [show (4:ℝ)*(k*n^2)*k=(2*k*n)^2 by ring,←pow_mul,←mul_pow,←mul_pow]
        congr 1
        ring
  refine ⟨a,?_⟩
  have he : matrixMean (A ∘ a)-μ=((k:ℝ)*n^2)⁻¹ • ∑ j, C (a j) := by
    simp only [C,Finset.sum_sub_distrib, sum_const,card_univ,Fintype.card_fin,smul_sub,
      matrixMean,Function.comp_apply,Nat.cast_mul,Nat.cast_pow]
    rw [←Nat.cast_smul_eq_nsmul ℝ,smul_smul,Nat.cast_mul,Nat.cast_pow,inv_mul_cancel₀ (by positivity),one_smul]
  rw [he,norm_smul,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((k:ℝ)*n^2)⁻¹*(8*k*n*R) := by gcongr
    _ = _ := by field_simp

#print axioms empirical_mean
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
