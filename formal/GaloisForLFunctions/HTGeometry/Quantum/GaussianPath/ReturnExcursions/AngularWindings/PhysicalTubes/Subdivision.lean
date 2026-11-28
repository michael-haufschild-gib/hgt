import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.CoordinateLift

/-! # Exact circuit fits at subdivisions allowed by the windings -/

open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Two fits to the same unitary interpolate at every subdivision for which
the endpoint windings have a common relative residue. The interpolated phases
retain the original operator error, including the off-diagonal part. -/
theorem subdivision_fit (W : unitary (Mat I)) (A : I → ℝ) (m n : I → ℤ) (i₀ : I)
    {u v ε : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2))
    (hu : u∈wordDates W A (circuitTurns W) m (physicalArc ε) ε)
    (hv : v∈wordDates W A (circuitTurns W) n (physicalArc ε) ε)
    {d : ℕ} (hd : 0<d) (hdiv : ∀ i, (d:ℤ) ∣ n i-m i-(n i₀-m i₀)) (j : ℕ) (hj : j≤d) :
    u+(j:ℝ)/d*(v-u)∈circuitDates W A ε := by
  classical
  letI : Nonempty I := ⟨i₀⟩
  obtain ⟨p,hp,hfit⟩ := hu
  obtain ⟨q,hq,hfit'⟩ := hv
  choose k hk using hdiv
  let x := physicalArc ε
  let a (i) := 2*π*(u*A i-(m i:ℝ)-p)
  let b (i) := 2*π*(v*A i-(n i:ℝ)-q)
  let ratio := (j:ℝ)/d
  let z := n i₀-m i₀
  let P := p+ratio*(q-p)+ratio*(z:ℝ)
  let t := u+ratio*(v-u)
  let w (i) := m i+(j:ℤ)*k i
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have hratio : ratio∈Icc (0:ℝ) 1 := ⟨by dsimp only [ratio]; positivity,
    (div_le_one hd').mpr (by exact_mod_cast hj)⟩
  have hx := (physicalArc_spec he.1 he.2).1.2.le
  have hspan (i) : |b i-a i|≤π := by
    have h₁ := abs_le.mp (hp i)
    have h₂ := abs_le.mp (hq i)
    have hδ : |(v*A i-(n i:ℝ)-q)-(u*A i-(m i:ℝ)-p)|≤x :=
      abs_le.mpr ⟨by dsimp only [x]; linarith only [h₂.1,h₁.2],
        by dsimp only [x]; linarith only [h₂.2,h₁.1]⟩
    dsimp only [a,b]
    rw [←mul_sub,abs_mul,abs_of_pos two_pi_pos]
    linarith only [mul_le_mul_of_nonneg_left (hδ.trans hx) two_pi_pos.le]
  have hε : ε^2<2 := (pow_lt_pow_left₀ he.2 he.1.le (by decide : (2:ℕ)≠0)).trans_eq (sq_sqrt (by norm_num))
  have hmid := segment_fit W a b hε hspan hfit hfit' ratio hratio
  have heq (i) : a i+ratio*(b i-a i)=2*π*(t*A i-(w i:ℝ)-P) := by
    have hi : (n i:ℝ)-(m i:ℝ)-(z:ℝ)=(d:ℝ)*(k i:ℝ) := by exact_mod_cast hk i
    have hm : ratio*(d:ℝ)=(j:ℝ) := div_mul_cancel₀ _ hd'.ne'
    dsimp only [a,b,t,w,P]
    push_cast
    linear_combination -(2*π*ratio)*hi-(2*π*(k i:ℝ))*hm
  refine ⟨P,?_⟩
  simpa only [heq,packet_lift] using hmid

#print axioms subdivision_fit
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
