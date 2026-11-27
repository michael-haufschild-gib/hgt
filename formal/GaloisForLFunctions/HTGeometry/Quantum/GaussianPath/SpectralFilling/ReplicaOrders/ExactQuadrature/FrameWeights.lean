import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.Dephasing

/-! # Exact spectral quadrature bounds the weight of every physical date -/
open Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

private theorem sq_cast (z : ℂ) : ((‖z‖^2:ℝ):ℂ)=z*conj z := by
  rw [Complex.mul_conj',Complex.ofReal_pow]

/-- A clock integrating every energy difference orthogonalizes the
spectral waves for arbitrary complex amplitudes, simultaneously. -/
theorem energy_frame (E : I → ℝ) (p t : J → ℝ) (c : I → ℂ)
    (hg : ∀ i k, ∑ j, (p j:ℂ)*wave (E i-E k) (t j)=if i=k then 1 else 0) :
    ∑ j, p j*‖∑ i, c i*wave (E i) (t j)‖^2=∑ i, ‖c i‖^2 := by
  classical
  let f (i : I) (j : J) := c i*wave (E i) (t j)
  let b (i k : I) := c i*conj (c k)
  have hx (j : J) : (p j:ℂ)*(∑ i, f i j)*conj (∑ i, f i j)=
      ∑ i, ∑ k, b i k*((p j:ℂ)*wave (E i-E k) (t j)) := by
    rw [map_sum,show (p j:ℂ)*(∑ i, f i j)=∑ i, (p j:ℂ)*f i j from Finset.mul_sum ..,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    simp only [f,b,map_mul,←wave_diff]
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,sq_cast,←mul_assoc]
  change (∑ j, (p j:ℂ)*(∑ i, f i j)*conj (∑ i, f i j))=∑ i, b i i
  simp_rw [hx]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  simp_rw [←mul_sum,hg]
  simp

/-- Each date has weight at most the reciprocal of the number of
orthogonalized energies. Test the frame on the phases that are all
aligned at that particular date. -/
theorem atom_price [Nonempty I] (E : I → ℝ) (p t : J → ℝ) (hp : ∀ j, 0≤p j)
    (hg : ∀ i k, ∑ j, (p j:ℂ)*wave (E i-E k) (t j)=if i=k then 1 else 0) (j : J) :
    p j*(Fintype.card I:ℝ)≤1 := by
  classical
  let c (i : I) := conj (wave (E i) (t j))
  have hu (i : I) : ‖wave (E i) (t j)‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hc (i : I) : c i*wave (E i) (t j)=1 := by
    dsimp only [c]
    rw [Complex.conj_mul',hu]
    norm_num
  have hnorm (i : I) : ‖c i‖=1 := (Complex.norm_conj _).trans (hu i)
  have h := energy_frame E p t c hg
  have hb := single_le_sum (f:=fun k => p k*‖∑ i, c i*wave (E i) (t k)‖^2)
    (fun k _ => mul_nonneg (hp k) (sq_nonneg _)) (mem_univ j)
  rw [h] at hb
  simp only [hc,hnorm,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,Complex.norm_natCast] at hb
  have hD : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  apply (mul_le_mul_iff_left₀ hD).mp
  linarith only [hb]

#print axioms atom_price
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
