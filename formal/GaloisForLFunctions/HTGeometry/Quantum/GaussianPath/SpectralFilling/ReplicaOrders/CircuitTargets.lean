import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.SpectralTube
import GaloisForLFunctions.HTGeometry.PhaseTwistedReplicaShortcutActionLaw
import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-! # A fixed physical circuit target gives a single twisted trace test -/
open Matrix Complex Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

private theorem mean_chord {I : Type*} [Fintype I] [Nonempty I] (f : I→ℂ) (hf : ∀ i, ‖f i‖=1)
    {c : ℂ} (hc : ‖c‖=1) {ρ : ℝ} (h : ∀ i, ‖f i-c‖ ≤ ρ) :
    1-ρ^2/2 ≤ ‖∑ i, (microcanonicalWeight I i:ℂ)*f i‖ := by
  let w := microcanonicalWeight I
  let z := ∑ i, (w i:ℂ)*f i
  have hw i : 0 ≤ w i := by dsimp only [w,microcanonicalWeight]; positivity
  have hcoord (i) : 1-ρ^2/2 ≤ (f i*conj c).re := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    rw [Complex.sq_norm,Complex.normSq_sub,←Complex.sq_norm,←Complex.sq_norm,hf,hc] at hs
    linarith only [hs]
  have ha : 1-ρ^2/2 ≤ (z*conj c).re := by
    change _ ≤ ((∑ i, (w i:ℂ)*f i)*conj c).re
    rw [Finset.sum_mul,Complex.re_sum]
    simp only [mul_assoc,Complex.re_ofReal_mul]
    calc _ = ∑ i, w i*(1-ρ^2/2) := by rw [←Finset.sum_mul,show ∑ i, w i=1 from sum_microcanonicalWeight_eq_one I,one_mul]
         _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcoord i) (hw i)
  apply ha.trans (Complex.re_le_norm _ |>.trans_eq ?_)
  rw [norm_mul,Complex.norm_conj,hc,mul_one]

/-- After choosing the center a, one unit-modulus twist works for
every time in the physical target tube, with arbitrary global phase. -/
theorem target_twist {n : ℕ} (H : selfAdjoint (SharpOccupation.Register n))
    (W : Matrix.unitaryGroup (Fin n→Bool) ℂ) (a : ℝ) :
    let e := qubitConfigFin n
    let E := H.2.isHermitian.eigenvalues ∘ e.symm
    ∃ v : Fin (2^n)→ℂ, (∀ j, ‖v j‖=1) ∧ ∀ t : ℝ, ∀ c : ℂ, ‖c‖=1 → ∀ ρ : ℝ, 0 ≤ ρ → ρ^2 < 2 →
      ‖unitaryEvolution H.val t-c • (W:SharpOccupation.Register n)‖ ≤ ρ →
      1-ρ^2/2 ≤ ‖twistedFiniteSpectralAmplitude (microcanonicalWeight _) E v (t-a)‖ := by
  intro e E
  let V := H.2.isHermitian.eigenvectorUnitary
  let B := V⁻¹*W*V
  let p (i : Fin n→Bool) := Complex.exp ((((B:SharpOccupation.Register n) i i).arg:ℂ)*I)
  let u (s : ℝ) (j : Fin (2^n)) := Complex.exp (((E j*s:ℝ):ℂ)*I)
  have hu s j : ‖u s j‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hp i : ‖p i‖=1 := Complex.norm_exp_ofReal_mul_I _
  let v := fun j => p (e.symm j)*u a j
  refine ⟨v,fun j => by rw [show v j=p (e.symm j)*u a j from rfl,norm_mul,hp,hu,mul_one],?_⟩
  intro t c hc ρ hρ hsmall h
  let θ (i : Fin n→Bool) := -(t*H.2.isHermitian.eigenvalues i)
  let f (i : Fin n→Bool) := Complex.exp ((θ i:ℂ)*I)
  have hf i : ‖f i‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hU : unitaryEvolution H.val t=(V:SharpOccupation.Register n)*diagonal f*star (V:SharpOccupation.Register n) := by
    rw [unitaryEvolution_spectral H.2.isHermitian]
    congr 2; funext i; dsimp [f,θ]; push_cast; congr 1; ring
  have hBW : (V:SharpOccupation.Register n)*(B:SharpOccupation.Register n)*star (V:SharpOccupation.Register n)=(W:SharpOccupation.Register n) :=
    congrArg Subtype.val (show V*B*V⁻¹=W by dsimp only [B]; group)
  have hd : ‖diagonal f-c • (B:SharpOccupation.Register n)‖ ≤ ρ := by
    rw [←l2_opNorm_unitary_conj_eq V.2,Matrix.mul_sub,Matrix.sub_mul,←hU,Matrix.mul_smul,Matrix.smul_mul,hBW]
    exact h
  have hphase j : v j * u (t-a) j=p (e.symm j)*star (f (e.symm j)) := by
    have htime : u a j*u (t-a) j=u t j := by
      dsimp only [u]
      rw [←Complex.exp_add]
      congr 1; push_cast; ring
    have hstar : star (f (e.symm j))=u t j := by
      change conj (Complex.exp ((θ (e.symm j):ℂ)*I))=_
      rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I]
      dsimp only [u,θ,E,Function.comp_apply]
      congr 1; push_cast; ring
    rw [show v j=p (e.symm j)*u a j from rfl,mul_assoc,htime,hstar]
  have hfit j : ‖v j*u (t-a) j-star c‖ ≤ ρ := by
    let i := e.symm j
    have hh := rounded_diagonal_chord f hf (B:SharpOccupation.Register n) B.property c hc ρ hρ hsmall hd i
    have hunit : p i*star (p i)=1 := by rw [Complex.star_def,Complex.mul_conj',hp]; norm_num
    have he : p i*star (f i)-star c=p i*star (f i-c*p i) := by
      rw [star_sub,star_mul,mul_sub,←mul_assoc,hunit,one_mul]
    rw [hphase]
    change ‖p i*star (f i)-star c‖ ≤ _
    rw [he,norm_mul,hp,norm_star,one_mul]
    exact hh
  have hfu (j) : ‖v j*u (t-a) j‖=1 := by
    change ‖(p (e.symm j)*u a j)*u (t-a) j‖=1
    rw [norm_mul,norm_mul,hp,hu,hu,one_mul,one_mul]
  have hm := mean_chord _ hfu (c:=star c) (by rw [norm_star,hc]) hfit
  change 1-ρ^2/2 ≤ ‖∑ j, ((microcanonicalWeight _ j:ℂ)*v j)*u (t-a) j‖
  simpa only [mul_assoc] using hm

#print axioms target_twist
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
