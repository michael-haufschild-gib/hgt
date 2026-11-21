import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.ShearedBoxes

/-! # A transverse spectral control on a clock that exactly aligns one gap -/
open Real
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

/-- On a clock aligning levels a and b, the quadratic correction is free
to align a third level. A width m⁻¹ control leaves at most m⁻² winding
error on all the other levels by tick m(m²)^(D−3). -/
theorem pencil_clock {I : Type*} [Fintype I] [DecidableEq I] (E F : I → ℝ)
    (a b c : I) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {τ : ℝ} (n : ℤ) (hturn : τ*(E b-E a)/(2*π)=n)
    (hpin : F b=F a) (hmove : F c ≠ F a) {m : ℕ} (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧ q ≤ m*(m^2)^(Fintype.card I-3) ∧
      ∃ β : ℝ, |β| ≤ (2*π/|F c-F a|)/(m:ℝ) ∧
        ∀ j, latticeClose (((q:ℝ)*τ*(E j-E a)-β*(F j-F a))/(2*π)) (1/(m:ℝ)^2) := by
  classical
  let R := ((Finset.univ.erase a).erase b).erase c
  have hdim : Fintype.card R = Fintype.card I-3 := by
    have hb : b ∈ (Finset.univ : Finset I).erase a := Finset.mem_erase.mpr ⟨hab.symm,Finset.mem_univ _⟩
    have hc : c ∈ ((Finset.univ : Finset I).erase a).erase b :=
      Finset.mem_erase.mpr ⟨hcb,Finset.mem_erase.mpr ⟨hca,Finset.mem_univ _⟩⟩
    rw [Fintype.card_coe,show R=((Finset.univ.erase a).erase b).erase c from rfl,
      Finset.card_erase_of_mem hc,Finset.card_erase_of_mem hb,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ]
    omega
  let X (j : I) := τ*(E j-E a)/(2*π)
  let G (j : I) := (F j-F a)/(F c-F a)
  have hg := sub_ne_zero.mpr hmove
  obtain ⟨q,hq,hQ,d,hd,h⟩ := sheared_dirichlet (fun _ : Unit => X c) (fun j : R => X j)
    (fun (j : R) (_ : Unit) => G j) hm
  let β := 2*π*d ()/(F c-F a)
  refine ⟨q,hq,by simpa only [Fintype.card_unit,pow_one,hdim] using hQ,β,?_,?_⟩
  · have hβ : |β|=(2*π/|F c-F a|)*|d ()| := by
      dsimp only [β]
      rw [abs_div,abs_mul,abs_of_pos (by positivity : 0<2*π)]
      ring
    rw [hβ]
    calc
      _ ≤ (2*π/|F c-F a|)*(1/(m:ℝ)) := mul_le_mul_of_nonneg_left (hd ()).1.le (by positivity)
      _ = _ := by ring
  · intro j
    have he : ((q:ℝ)*τ*(E j-E a)-β*(F j-F a))/(2*π) = (q:ℝ)*X j-G j*d () := by
      dsimp only [β,X,G]
      field_simp
    rw [he]
    have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
    have hpos : (0:ℝ)<1/(m:ℝ)^2 := by positivity
    by_cases hja : j=a
    · subst j
      exact ⟨0,by simpa only [X,G,sub_self,mul_zero,zero_div,zero_mul,Int.cast_zero,abs_zero] using hpos⟩
    by_cases hjb : j=b
    · subst j
      have hx : X b=(n:ℝ) := hturn
      refine ⟨(q:ℤ)*n,?_⟩
      simpa only [hx,G,hpin,sub_self,zero_div,zero_mul,sub_zero,Int.cast_mul,Int.cast_natCast,abs_zero] using hpos
    by_cases hjc : j=c
    · subst j
      obtain ⟨z,hz⟩ := (hd ()).2
      refine ⟨z,?_⟩
      simpa only [G,div_self hg,one_mul,hz,sub_self,abs_zero] using hpos
    let l : R := ⟨j,Finset.mem_erase.mpr ⟨hjc,Finset.mem_erase.mpr ⟨hjb,Finset.mem_erase.mpr ⟨hja,Finset.mem_univ _⟩⟩⟩⟩
    simpa only [Fintype.sum_unique] using h l

#print axioms pencil_clock
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
