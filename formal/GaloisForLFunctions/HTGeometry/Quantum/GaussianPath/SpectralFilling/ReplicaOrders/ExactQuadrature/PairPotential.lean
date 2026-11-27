import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.SurvivalShifts

/-! # The pairwise survival potential of a physical sampling clock -/
open Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I J : Type*} [Fintype J]

/-- Fourier coefficient of the weighted physical dates. -/
def clockWave (p t : J → ℝ) (w : ℝ) : ℂ := ∑ j, (p j:ℂ)*wave w (t j)

private theorem pair_wave (p t : J → ℝ) (w : ℝ) :
    ∑ i, ∑ j, (p i:ℂ)*(p j:ℂ)*wave w (t i-t j)=((‖clockWave p t w‖^2:ℝ):ℂ) := by
  have swap (a b : ℝ) : wave a b=wave b a := by simp only [wave,mul_comm a b]
  rw [Complex.ofReal_pow,←Complex.mul_conj',clockWave,map_sum,Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [swap w (t i-t j),←wave_diff,←swap w (t i),←swap w (t j),map_mul,Complex.conj_ofReal]
  ring

/-- Excess above the resonance mean is the weighted squared Fourier
error. Colliding frequencies reinforce one another. -/
theorem pair_potential (S : Finset I) (d b : I → ℝ) (p t : J → ℝ) (hm : ∑ j, p j=1) :
    (∑ i, ∑ j, (p i:ℂ)*(p j:ℂ)*polynomial S d b (t i-t j)).re =
      (∑ x∈S, if d x=0 then b x else 0)+
      ∑ x∈S, if d x=0 then 0 else b x*‖clockWave p t (d x)‖^2 := by
  have h (i j : J) : (p i:ℂ)*(p j:ℂ)*polynomial S d b (t i-t j)=
      ∑ x∈S, (b x:ℂ)*((p i:ℂ)*(p j:ℂ)*wave (d x) (t i-t j)) := by
    rw [polynomial,mul_sum]
    exact sum_congr rfl fun x _ => by ring
  simp_rw [h,Finset.sum_comm (s:=univ) (t:=S)]
  simp_rw [←Finset.mul_sum,pair_wave]
  rw [Complex.re_sum,←sum_add_distrib]
  have hz : clockWave p t 0=1 := by simp [clockWave,wave,←Complex.ofReal_sum,hm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : d x=0 <;> simp [hx,hz]

/-- One scalar equality on pairwise time differences characterizes
exact integration of every shift of the same positive polynomial. -/
theorem pair_calibration_iff (S : Finset I) (d b : I → ℝ) (hb : ∀ x∈S, 0<b x)
    (p t : J → ℝ) (hm : ∑ j, p j=1) :
    ((∑ i, ∑ j, (p i:ℂ)*(p j:ℂ)*polynomial S d b (t i-t j)).re=
      ∑ x∈S, if d x=0 then b x else 0) ↔
      ∀ u, ∑ j, (p j:ℂ)*polynomial S d b (u+t j)=∑ x∈S, if d x=0 then (b x:ℂ) else 0 := by
  rw [pair_potential S d b p t hm,shifted_clock_iff S d b hb p t]
  let e (x : I) := if d x=0 then 0 else b x*‖clockWave p t (d x)‖^2
  have he (x : I) (hx : x∈S) : 0≤e x := by
    dsimp only [e]; split <;> first | exact le_rfl | exact mul_nonneg (hb x hx).le (sq_nonneg _)
  have hz : clockWave p t 0=1 := by simp [clockWave,wave,←Complex.ofReal_sum,hm]
  constructor
  · intro h x hx
    have hs : ∑ y∈S, e y=0 := by linarith only [h]
    have hle := single_le_sum he hx
    rw [hs] at hle
    have hx0 := le_antisymm hle (he x hx)
    change clockWave p t (d x)=_
    split_ifs with hd
    · rwa [hd]
    · have hmul : b x*‖clockWave p t (d x)‖^2=0 := by simpa only [e,if_neg hd] using hx0
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hmul).resolve_left (hb x hx).ne'))
  · intro h
    have h0 : ∑ x∈S, e x=0 := sum_eq_zero fun x hx => by
      dsimp only [e]
      split_ifs with hd
      · rfl
      · have hx0 : clockWave p t (d x)=0 := (h x hx).trans (if_neg hd)
        rw [hx0,norm_zero,zero_pow (by decide),mul_zero]
    change _+(∑ x∈S, e x)=_
    rw [h0,add_zero]

/-- At any replica order a clock of total mass one integrates all shifted
survival moments exactly if and only if its single pairwise potential
equals the infinite-time mean. No simplicity of the spectrum is needed. -/
theorem survival_pair_iff [Fintype I] [DecidableEq I] (w E : I → ℝ) (hw : ∀ i, 0<w i)
    (q : ℕ) (p t : J → ℝ) (hm : ∑ j, p j=1) :
    let f := fun u => twistedFiniteSpectralFidelity w E (fun _ => 1) u^q
    let M := average (frequencies E q).toList f 0
    ((∑ i, ∑ j, (p i:ℂ)*(p j:ℂ)*f (t i-t j)).re=M.re) ↔
      ∀ u, ∑ j, (p j:ℂ)*f (u+t j)=M := by
  classical
  intro f M
  let A := (univ : Finset I).piAntidiag q
  let d (x : (I → ℕ)×(I → ℕ)) := replicaMultiplicityEnergy E x.1-replicaMultiplicityEnergy E x.2
  let b (x : (I → ℕ)×(I → ℕ)) := fidelityReplicaMultiplicityWeight w x.1 x.2
  have hb (x) (_ : x∈A×ˢA) : 0<b x := fidelityReplicaMultiplicityWeight_pos hw _ _
  have twist (x y : I → ℕ) : replicaMultiplicityTwist (fun _ => 1) x y=1 := by
    simp [replicaMultiplicityTwist]
  have hex (s : ℝ) : polynomial (A×ˢA) d b s=f s := by
    rw [polynomial,sum_product]
    dsimp only [f]
    rw [twistedFiniteSpectralFidelity_pow_expansion]
    simp only [A,d,b,twist,mul_one,wave,mul_comm s]
  have mean : (∑ x∈A×ˢA, if d x=0 then (b x:ℂ) else 0)=M := by
    dsimp only [M,f]
    rw [sum_product,exact_replica_moment]
    simp only [A,d,sub_eq_zero,b,twist,mul_one]
  have hr : (∑ x∈A×ˢA, if d x=0 then b x else 0)=M.re := by
    rw [←mean,Complex.re_sum]
    exact sum_congr rfl fun x _ => by split_ifs <;> rfl
  simpa only [hex,hr,mean] using pair_calibration_iff (A×ˢA) d b hb p t hm

#print axioms survival_pair_iff
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
