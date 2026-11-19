import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRiemannHypothesisIsExactEventualCombPositivity
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFormOfLogarithmicTailsIsDeterminedByTheRowsOfTheFlatTail

/-!
# Two-dimensional parity tests for the complete Weil comb

The even block is coercive on large aligned windows. Its presence makes
nonnegativity of the mixed two-dimensional Gram determinants sufficient
to control the entire form. Each aperture may use its own cofinal scales.
-/

noncomputable section
open Filter Finset
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open HodgeTheoryOfAFixedPart AbsoluteGeometryOfSpecZ

private abbrev aligned (K N : ℕ) := Ioc (2*N) (2*(N+3*K*N))

/-- The mixed Gram determinant test on all pairs supported on opposite
parities. Each diagonal uses the same complete window as the mixed term. -/
def parityMinorsNonnegative (S : Finset ℕ) : Prop :=
  ∀ e o : ℕ → ℝ, (∀ n ∈ S, ¬2 ∣ n → e n = 0) → (∀ n ∈ S, 2 ∣ n → o n = 0) →
    (formBilin S e o)^2 ≤ combForm S e * combForm S o

private theorem square_le_product {A B C : ℝ} (ha : 0 ≤ A)
    (p : ∀ t : ℝ, 0 ≤ t^2*A+2*t*B+C) : B^2 ≤ A*C := by
  rcases ha.eq_or_lt with h | h
  · subst A
    by_cases hB : B=0
    · simp [hB]
    · have hh := p (-(C+1)/(2*B))
      have hc : 2*(-(C+1)/(2*B))*B=-(C+1) := by field_simp
      rw [mul_zero,zero_add,hc] at hh
      linarith only [hh]
  · have hh := mul_nonneg h.le (p (-B/A))
    have eq : A*((-B/A)^2*A+2*(-B/A)*B+C)=A*C-B^2 := by field_simp; ring
    exact sub_nonneg.mp (eq ▸ hh)

private theorem minors_of_positive (S : Finset ℕ) (h : ∀ c, 0 ≤ combForm S c) :
    parityMinorsNonnegative S := by
  intro e o _ _
  apply square_le_product (h e)
  intro t
  have ht := h (fun n => t*e n+o n)
  rw [AbsoluteGeometryOfSpecZ.combForm_add,←formBilin_self S (fun n => t*e n),
    formBilin_const_mul_left,formBilin_const_mul_right,formBilin_self,
    formBilin_const_mul_left] at ht
  linarith only [ht]

private theorem sum_nonnegative {A B C : ℝ} (ha : 0 ≤ A) (hc : 0 ≤ C) (hB : B^2 ≤ A*C) :
    0 ≤ A+2*B+C := by
  rcases ha.eq_or_lt with h | h
  · subst A
    have hb : B=0 := by nlinarith only [hB,sq_nonneg B]
    simpa only [hb,mul_zero,zero_add] using hc
  · apply nonneg_of_mul_nonneg_right (a := A) _ h
    nlinarith only [sq_nonneg (A+B),hB]

private theorem even_floor {K : ℕ} (hK : 1 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ e : ℕ → ℝ, (∀ n ∈ aligned K N, ¬2 ∣ n → e n=0) →
      ∑ n ∈ aligned K N, e n^2 ≤ combForm (aligned K N) e := by
  let Q : ℕ+ := ⟨3*K,by omega⟩
  simpa only [one_mul] using eventually_full_comb_on_multiples (2:ℕ+) (by decide) Q 1

private theorem all_profiles_of_minors {K N : ℕ} (hk : 1 ≤ K) (hn : 1 ≤ N)
    (h : parityMinorsNonnegative (aligned K N))
    (floor : ∀ e : ℕ → ℝ, (∀ n ∈ aligned K N, ¬2 ∣ n → e n=0) →
      ∑ n ∈ aligned K N,e n^2 ≤ combForm (aligned K N) e) :
    ∀ c, 0 ≤ combForm (aligned K N) c := by
  let S := aligned K N
  let j := 2*(N+1)
  let u : ℕ → ℝ := fun n => if n=j then 1 else 0
  have hj : j ∈ S := by
    apply mem_Ioc.mpr
    have hkn : 1 ≤ 3*K*N := (by omega : 1 ≤ 3*K).trans (Nat.le_mul_of_pos_right _ hn)
    dsimp only [j]
    omega
  have hu (n : ℕ) (_ : n ∈ S) (hne : ¬2 ∣ n) : u n=0 := by
    exact if_neg fun eq => hne (eq ▸ (dvd_mul_right 2 (N+1)))
  have u1 : 0 < combForm S u := by
    have mass : (∑ n ∈ S,u n^2)=1 := by simp [u,ite_pow,hj]
    have ub := floor u hu
    change ∑ n ∈ S,u n^2 ≤ _ at ub
    exact zero_lt_one.trans_le (mass ▸ ub)
  intro c
  let e : ℕ → ℝ := fun n => if 2 ∣ n then c n else 0
  let o : ℕ → ℝ := fun n => if 2 ∣ n then 0 else c n
  have he (n : ℕ) (_ : n ∈ S) (hz : ¬2 ∣ n) : e n=0 := if_neg hz
  have ho (n : ℕ) (_ : n ∈ S) (hz : 2 ∣ n) : o n=0 := if_pos hz
  have e0 : 0 ≤ combForm S e := (sum_nonneg fun n _ => sq_nonneg (e n)).trans (floor e he)
  have o0 : 0 ≤ combForm S o := nonneg_of_mul_nonneg_right
    ((sq_nonneg _).trans (h u o hu ho)) u1
  have dec : (fun n => e n+o n)=c := by
    funext n
    by_cases hm : 2 ∣ n <;> simp [e,o,hm]
  have eq := AbsoluteGeometryOfSpecZ.combForm_add S e o
  rw [dec] at eq
  exact eq.symm ▸ sum_nonnegative e0 o0 (h e o he ho)

/-- RH is equivalent to nonnegative two-dimensional mixed parity
determinants at arbitrarily large aligned scales for every aperture.
A failure forces a negative determinant at every sufficiently large
scale of one fixed aperture. -/
theorem rh_iff_cofinal_parity_minors :
    RiemannHypothesis ↔ ∀ K : ℕ, 1 ≤ K → ∃ᶠ N : ℕ in atTop,
      parityMinorsNonnegative (Ioc (2*N) (2*(N+3*K*N))) := by
  have top : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by decide : 0 < 2)) tendsto_id
  have window (K N : ℕ) : aligned K N=Ioc (2*N) (2*N+3*K*(2*N)) := by
    dsimp only [aligned]; congr 1; ring
  constructor
  · intro h K _
    apply Eventually.frequently
    filter_upwards [top (eventually_combForm_nonneg_of_riemannHypothesis h K)] with N hN
    apply minors_of_positive
    simpa only [←window] using hN
  · intro h
    apply riemannHypothesis_of_frequently_combForm_ge
    intro K hk η hη
    apply frequently_atTop.mpr
    intro M
    obtain ⟨N,⟨hmin,hfloor,hpos⟩,hNM⟩ := (((h K hk).and_eventually
      ((even_floor hk).and (eventually_ge_atTop 1))).and_eventually (eventually_ge_atTop M)).exists
    refine ⟨2*N,by omega,?_⟩
    intro c
    apply (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη.le) (sum_nonneg fun _ _ => sq_nonneg _)).trans
    rw [←window]
    exact all_profiles_of_minors hk hpos hmin hfloor c

#print axioms rh_iff_cofinal_parity_minors
end GaloisForLFunctions.SignedArithmeticCorrespondences
