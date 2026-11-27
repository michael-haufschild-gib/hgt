import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheArithmeticBernsteinTheorem

/-! # Prime counts on a recurrent interval of a logarithmic observation clock -/
open Set Filter Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
noncomputable section

/-- If every length-(G+w) record contains a whole interval of width w
in A, every translated logarithmic prime clock places at least c X/log X
primes below X in A. The origin may depend on X. -/
theorem prime_count_in_recurrent_intervals (A : Set ℝ) {G w h : ℝ}
    (_hG : 0≤G) (hw : 0<w) (hh : 0<h)
    (hrec : ∀ a : ℝ, ∃ v ∈ Icc a (a+G), Icc v (v+w) ⊆ A) :
    ∃ c > (0:ℝ), ∀ᶠ X : ℝ in atTop, ∀ o : ℝ, ∃ S : Finset ℕ,
      c*(X/log X)≤S.card ∧ ∀ p∈S, p.Prime ∧ (p:ℝ)≤X ∧ o+h*log (p:ℝ)∈A := by
  let b := (G+w)/h
  let δ := w/h
  have hδ : 0<δ := div_pos hw hh
  obtain ⟨c,hc,Y₀,hY₀,hwindow⟩ := GaloisForLFunctions.ArithmeticInnerFunctionTheory.exists_card_primes_window_ge hδ
  refine ⟨c*exp (-b),mul_pos hc (exp_pos _),?_⟩
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop (b+log Y₀),eventually_gt_atTop (0:ℝ)] with X hlarge hX
  intro o
  let L := log X
  let a := o+h*L-(G+w)
  obtain ⟨v,hv,hA⟩ := hrec a
  let y := (v-o)/h
  have hy : L-b≤y := by
    apply (le_div_iff₀ hh).mpr
    rw [sub_mul,show b*h=G+w from div_mul_cancel₀ _ hh.ne']
    have hv' : o+h*L-(G+w)≤v := hv.1
    linarith only [hv',mul_comm h L]
  have hy' : y+δ≤L := by
    change (v-o)/h+w/h≤L
    rw [←add_div,div_le_iff₀ hh]
    have hv' : v≤o+h*L-(G+w)+G := hv.2
    linarith only [hv',mul_comm h L]
  have hY : log Y₀≤y := by
    change b+log Y₀≤L at hlarge
    linarith only [hy,hlarge]
  have hypos := (log_pos hY₀).trans_le hY
  have hlow : Y₀≤exp y := by
    rw [←exp_log (zero_lt_one.trans hY₀)]
    exact exp_le_exp.mpr hY
  let S := primesInIoc ⌊exp y⌋₊ ⌊exp δ*exp y⌋₊
  refine ⟨S,?_,?_⟩
  · have hf := hwindow (exp y) hlow
    rw [log_exp] at hf
    have hleft : exp (-b)*X≤exp y := by
      rw [←exp_log hX,←exp_add]
      exact exp_le_exp.mpr (by linarith only [hy])
    calc c*exp (-b)*(X/log X) = c*((exp (-b)*X)/L) := by dsimp only [L]; ring
         _ ≤ c*(exp y/y) := mul_le_mul_of_nonneg_left
           (div_le_div₀ (exp_pos y).le hleft hypos (by linarith only [hy',hδ])) hc.le
         _ ≤ _ := hf
  intro p hp
  obtain ⟨hprime,hl,hu⟩ := mem_primesInIoc hp
  have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr hprime.pos
  have hp₁ : exp y ≤ (p:ℝ) := (Nat.lt_of_floor_lt hl).le
  have hp₂ : (p:ℝ) ≤ exp (δ+y) := by
    rw [exp_add]
    exact (Nat.cast_le.mpr hu).trans (Nat.floor_le (mul_nonneg (exp_pos _).le (exp_pos _).le))
  have ht₁ := log_le_log (exp_pos _) hp₁
  have ht₂ := log_le_log hp₀ hp₂
  rw [log_exp] at ht₁ ht₂
  have he : y*h=v-o := div_mul_cancel₀ _ hh.ne'
  have hd : δ*h=w := div_mul_cancel₀ _ hh.ne'
  refine ⟨hprime,?_,hA ⟨?_,?_⟩⟩
  · rw [←exp_log hX]
    exact hp₂.trans (exp_le_exp.mpr (by linarith only [hy']))
  · have h' := mul_le_mul_of_nonneg_right ht₁ hh.le
    linarith only [he,h',mul_comm h (log p)]
  · have h' := mul_le_mul_of_nonneg_right ht₂ hh.le
    rw [add_mul,he,hd] at h'
    linarith only [h',mul_comm h (log p)]

#print axioms prime_count_in_recurrent_intervals
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
