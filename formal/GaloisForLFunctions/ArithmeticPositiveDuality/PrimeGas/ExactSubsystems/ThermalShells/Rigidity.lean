import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Temperatures

/-! # Equality in the sharp contrast bound for a simple Hamiltonian -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

variable {Ω : Type*} [DecidableEq Ω]

/-- On a two-state selection the reference probability depends only on the energy difference. -/
theorem two_share (E : Ω → ℝ) (β : ℝ) {x y : Ω} (hxy : x ≠ y) :
    share (weight β E) {x,y} {x} = 1/(Real.exp (β*(E x-E y))+1) := by
  have he : weight β E y = Real.exp (β*(E x-E y))*weight β E x := by
    unfold weight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [share,mass,mass,Finset.sum_pair hxy,Finset.sum_singleton,he]
  apply (div_eq_div_iff (add_pos (weight_pos β E x) (mul_pos (Real.exp_pos _) (weight_pos β E x))).ne'
    (add_pos (Real.exp_pos _) zero_lt_one).ne').mpr
  ring

private theorem oriented_pair (E : Ω → ℝ) {x y : Ω} (hxy : x ≠ y) (β γ D : ℝ)
    (hsym : β+γ = 0) (hscore : (γ-β)*(E x-E y) = |β-γ| * D) :
    ∃ A ⊆ ({x,y} : Finset Ω), (halfRatio (|β-γ| * D)+1)*share (weight γ E) {x,y} A = 1 ∧
      ∀ a ∈ A, ∀ b ∈ ({x,y} : Finset Ω) \ A, (γ-β)*(E a-E b) = |β-γ| * D := by
  have hβ : β = -γ := eq_neg_of_add_eq_zero_left hsym
  have he : |β-γ| * D/2 = γ*(E x-E y) := by rw [← hscore,hβ]; ring
  refine ⟨{x},by simp,?_,?_⟩
  · rw [two_share E γ hxy,halfRatio,he,one_div,mul_inv_cancel₀ (add_pos (Real.exp_pos _) zero_lt_one).ne']
  · intro a ha b hb
    have ha' := Finset.mem_singleton.mp ha
    have hm := Finset.mem_sdiff.mp hb
    have hb' : b = y := Finset.mem_singleton.mp ((Finset.mem_insert.mp hm.1).resolve_left
      (fun h => hm.2 (Finset.mem_singleton.mpr h)))
    simpa only [ha',hb'] using hscore

/-- A simple Hamiltonian saturates positive contrast exactly on a two-state selection spanning
the full permitted width and at opposite inverse temperatures. -/
theorem sharp_iff_pair (E : Ω → ℝ) {U : Finset Ω} (hU : U.Nonempty) (hE : Set.InjOn E (U : Set Ω))
    (β γ D : ℝ) (hD : ∀ x ∈ U, ∀ y ∈ U, |E x-E y| ≤ D) (hη : 0 < |β-γ| * D) :
    variation (weight β E) (weight γ E) U = Real.tanh (|β-γ| * D/4) ↔
      β+γ = 0 ∧ ∃ x y : Ω, x ≠ y ∧ U = {x,y} ∧ |E x-E y| = D := by
  rw [thermal_variation_equality E hU β γ D hD hη]
  constructor
  · rintro ⟨A,hA,hp,hs⟩
    have ha : A.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hp
      simp [share,mass] at hp
    have hb : (U \ A).Nonempty := by
      by_contra hempty
      have hh := one_sub_share (weight_pos γ E) hU hA
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hh
      simp only [share,mass,Finset.sum_empty,zero_div] at hh
      change 1-share (weight γ E) U A = 0 at hh
      rw [(sub_eq_zero.mp hh).symm,mul_one] at hp
      have hpos := Real.exp_pos (|β-γ| * D/2)
      unfold halfRatio at hp
      linarith only [hpos,hp]
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    have hy' := Finset.mem_sdiff.mp hy
    have hxy : x ≠ y := fun h => hy'.2 (h ▸ hx)
    have he := hs x hx y hy
    have hd : γ-β ≠ 0 := fun hz => hη.ne (by rwa [hz,zero_mul] at he)
    have hn : E x-E y ≠ 0 := fun hz => hη.ne (by rwa [hz,mul_zero] at he)
    have hax (a) (ha : a ∈ A) : a = x := by
      apply hE (hA ha) (hA hx)
      have H := mul_left_cancel₀ hd ((hs a ha y hy).trans he.symm)
      linarith only [H]
    have hby (b) (hb : b ∈ U \ A) : b = y := by
      apply hE (Finset.mem_sdiff.mp hb).1 hy'.1
      have H := mul_left_cancel₀ hd ((hs x hx b hb).trans he.symm)
      linarith only [H]
    have hA' : A = {x} := by
      ext a
      exact ⟨fun h => Finset.mem_singleton.mpr (hax a h),fun h => (Finset.mem_singleton.mp h).symm ▸ hx⟩
    have hU' : U = {x,y} := by
      ext a
      constructor
      · intro h
        by_cases ha : a ∈ A
        · exact Finset.mem_insert.mpr (Or.inl (hax a ha))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hby a (Finset.mem_sdiff.mpr ⟨h,ha⟩))))
      · intro h
        rcases Finset.mem_insert.mp h with rfl | hh
        · exact hA hx
        · exact (Finset.mem_singleton.mp hh).symm ▸ hy'.1
    rw [hU',hA',two_share E γ hxy,one_div,← div_eq_mul_inv] at hp
    have hh := (div_eq_one_iff_eq (add_pos (Real.exp_pos _) zero_lt_one).ne').mp hp
    have hh' : |β-γ| * D/2 = γ*(E x-E y) := Real.exp_injective (add_right_cancel hh)
    have hz : (β+γ)*(E x-E y) = 0 := by linarith only [he,hh']
    refine ⟨(mul_eq_zero.mp hz).resolve_right hn,x,y,hxy,hU',?_⟩
    have h := congrArg abs he
    rw [abs_mul,abs_sub_comm γ β,abs_of_pos hη] at h
    exact mul_left_cancel₀ (abs_pos.mpr (sub_ne_zero.mpr (sub_ne_zero.mp hd).symm)).ne' h
  · rintro ⟨hsym,x,y,hxy,rfl,hspan⟩
    have he : |(γ-β)*(E x-E y)| = |β-γ| * D := by rw [abs_mul,abs_sub_comm γ β,hspan]
    by_cases hpos : 0 ≤ (γ-β)*(E x-E y)
    · rw [abs_of_nonneg hpos] at he
      exact oriented_pair E hxy β γ D hsym he
    · rw [abs_of_neg (lt_of_not_ge hpos)] at he
      have hflip : (γ-β)*(E y-E x) = |β-γ| * D := by linarith only [he]
      rw [Finset.pair_comm x y]
      exact oriented_pair E hxy.symm β γ D hsym hflip

#print axioms two_share
#print axioms sharp_iff_pair

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
