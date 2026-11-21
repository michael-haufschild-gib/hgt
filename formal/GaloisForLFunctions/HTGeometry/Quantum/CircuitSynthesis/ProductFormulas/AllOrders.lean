import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.Contact

/-! # Exponential words of arbitrary contact order with explicit cost -/
namespace GaloisForLFunctions.HTGeometry.ProductFormula
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every new factor is a real-time evolution of an original generator. -/
def Uses (w inputs : List A) : Prop :=
  ∀ y ∈ w, ∃ x ∈ inputs, ∃ c : ℝ, y = (c:ℂ) • x

omit [CompleteSpace A] in
private theorem scale_uses {w inputs : List A} (h : Uses w inputs) (a : ℝ) :
    Uses (scaleWord a w) inputs := by
  intro y hy
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
  obtain ⟨x,hx,c,rfl⟩ := h v hv
  exact ⟨x,hx,a*c,by rw [Complex.ofReal_mul,smul_smul]⟩

/-- Each extra order triples length and multiplies total norm by at most seven. -/
theorem exists_word (inputs : List A) (j : ℕ) :
    ∃ w : List A, Contact (j+2) w inputs.sum ∧ Uses w inputs ∧
      w.length = 3^j*inputs.length ∧ mass w ≤ 7^j*mass inputs := by
  induction j with
  | zero =>
    refine ⟨inputs,contact_two inputs,fun y hy => ⟨y,hy,1,by simp⟩,by simp,by simp⟩
  | succ j ih =>
    obtain ⟨w,hw,hu,hlen,hm⟩ := ih
    obtain ⟨a,b,ha,ha',hb,hb',ht,hc⟩ := exists_weights (j+2) (by omega)
    have hrev : Uses w.reverse inputs := fun y hy => hu y (List.mem_reverse.mp hy)
    refine ⟨raised w a b,contact_raised hw ht hc,?_,?_,?_⟩
    · intro y hy
      simp only [raised,List.mem_append] at hy
      rcases hy with (hy|hy)|hy
      · exact scale_uses hu a y hy
      · exact scale_uses hu a y hy
      · exact scale_uses hrev (-b) y hy
    · simp only [raised,List.length_append,scaleWord,List.length_map,List.length_reverse,hlen,pow_succ]
      ring
    · simp only [raised,mass_append,mass_scale,mass_reverse,abs_neg,
        abs_of_nonneg (show 0 ≤ a by linarith only [ha]),abs_of_nonneg (show 0 ≤ b by linarith only [hb])]
      calc
        _ = (2*a+b)*mass w := by ring
        _ ≤ 7*mass w := mul_le_mul_of_nonneg_right (by linarith only [ha',hb']) (mass_nonneg _)
        _ ≤ 7*(7^j*mass inputs) := by gcongr
        _ = _ := by rw [pow_succ]; ring

#print axioms exists_word
end
end GaloisForLFunctions.HTGeometry.ProductFormula
