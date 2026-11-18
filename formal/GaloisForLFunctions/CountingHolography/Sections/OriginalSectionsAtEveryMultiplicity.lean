import GaloisForLFunctions.CountingHolography.Sections.OriginalSectionsAtDiagonalMultiplicity

/-!
# Square conductors having original sections at every positive multiplicity

The difference between the unit atom and its fourfold dilation has positive
degree under RH. Consequently the upper two atoms have a uniform norm
advantage over the lower atom. Off RH positive degrees are unbounded.
A common reserve on arbitrarily late conductors pays every multiplicity.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open ArithmeticScatteringHolography RenormalizedIntersectionTheory Filter Topology Finset

private theorem separation_at_four (hRH : RiemannHypothesis) :
    0 < realSplineTrace 0-realSplineTrace (Real.log 4) := by
  let a := threeGraphDivisor (0 : Fin 4) 0 3 1 0 1
  have hne : a ≠ 0 := by
    intro h
    have hh := congrFun h (0 : Fin 4)
    have h03 : (0:Fin 4) ≠ 3 := by decide
    norm_num [a,threeGraphDivisor,Pi.single_apply,Pi.add_apply,h03,h03.symm] at hh
  have h := integerProbe_pos_of_rh hRH hne
  have he : integerProbe 4 a=2*(realSplineTrace 0-realSplineTrace (Real.log 4)) := by
    rw [show a=threeGraphDivisor (0 : Fin 4) 0 3 1 0 1 from rfl,integerProbe_threeGraphDivisor]
    norm_num [atomGram_eq_splineSeries,realSplineTrace]
    ring
  linarith only [he,h]

/-- Positivity on the integer tilt kD+e₁ compares the norm of the upper
pair with the fixed lower atom without evaluating their long-range phase. -/
private theorem tilt {N : ℕ} (hRH : RiemannHypothesis) (i j l : Fin N) (k : ℕ) :
    (k:ℝ)*(4*(atomGram N j j).re+(atomGram N l l).re-4*(atomGram N l j).re)-
      ((k:ℝ)+1)*(atomGram N i i).re ≤
      (k:ℝ)*(k+1)*integerProbe N (threeGraphDivisor i j l 1 2 1) := by
  have h := riemannHypothesis_iff_integerProbes.mp hRH N (threeGraphDivisor i j l ((k:ℤ)+1) (2*(k:ℤ)) k)
  rw [integerProbe_threeGraphDivisor] at h ⊢
  push_cast at h ⊢
  linarith only [h]

private theorem tilt_squares (hRH : RiemannHypothesis) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k:ℝ)*(5*realSplineTrace 0-4*realSplineTrace (Real.log ((((2*n+1):ℕ):ℝ)^2)-Real.log ((n:ℝ)^2)))-
      ((k:ℝ)+1)*realSplineTrace 0 ≤
      (k:ℝ)*(k+1)*integerProbe _ (successorSquareTriple n) := by
  let b := (2*n+1)^2
  let j : Fin (b+1) := ⟨n^2-1,by
    have hh : n^2 ≤ b := Nat.pow_le_pow_left (by omega : n ≤ 2*n+1) 2
    omega⟩
  let l : Fin (b+1) := ⟨b-1,by omega⟩
  have hj : (j:ℝ)+1=(n:ℝ)^2 := by
    change ((n^2-1:ℕ):ℝ)+1=_
    rw [Nat.cast_sub (pow_pos hn 2),Nat.cast_pow,Nat.cast_one,sub_add_cancel]
  have hl : (l:ℝ)+1=(((2*n+1):ℕ):ℝ)^2 := by
    change ((b-1:ℕ):ℝ)+1=_
    rw [Nat.cast_sub (pow_pos (Nat.succ_pos (2*n)) 2),Nat.cast_one,sub_add_cancel]
    exact Nat.cast_pow _ _
  have h := tilt hRH (0 : Fin (b+1)) j l k
  have he : threeGraphDivisor (0 : Fin (b+1)) j l 1 2 1=successorSquareTriple n := rfl
  rw [he] at h
  simp only [atomGram_eq_splineSeries,Fin.val_zero,Nat.cast_zero,zero_add,hj,hl,sub_self] at h
  dsimp only [realSplineTrace]
  linarith only [h]

/-- The relative trace of the two upper square atoms tends to the trace
of the fixed dilation by four. -/
theorem successorSquare_relative_trace_limit :
    Tendsto (fun n : ℕ => realSplineTrace (Real.log ((((2*n+1):ℕ):ℝ)^2)-Real.log ((n:ℝ)^2)))
      atTop (𝓝 (realSplineTrace (Real.log 4))) := by
  have h₀ : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have h₂ : Tendsto (fun n : ℕ => 2+(n:ℝ)⁻¹) atTop (𝓝 (2:ℝ)) := by
    simpa only [add_zero] using h₀.const_add (2:ℝ)
  have h₄ := h₂.pow 2
  rw [show (2:ℝ)^2=4 by norm_num] at h₄
  have hc : Continuous realSplineTrace := Complex.continuous_re.comp continuous_splineSeries
  apply (hc.continuousAt.tendsto.comp ((Real.continuousAt_log (by norm_num : (4:ℝ) ≠ 0)).tendsto.comp h₄)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  change realSplineTrace (Real.log ((2+(n:ℝ)⁻¹)^2))=_
  congr 1
  rw [← Real.log_div (sq_pos_of_pos (by positivity)).ne' (sq_pos_of_pos hn').ne']
  congr 1
  push_cast
  field_simp

/-- On the critical-line alternative the signed three-square degree is
bounded away from zero at every sufficiently large conductor. -/
theorem successorSquare_degree_gap_of_rh (hRH : RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, δ ≤ integerProbe _ (successorSquareTriple n) := by
  let F := realSplineTrace 0
  let g := F-realSplineTrace (Real.log 4)
  have hg : 0 < g := separation_at_four hRH
  let k := ⌈(|F|+1)/g⌉₊
  have hk : |F|+1 ≤ (k:ℝ)*g := (div_le_iff₀ hg).mp (Nat.le_ceil _)
  have hk' : 0 < (k:ℝ) := by
    by_contra! h
    linarith only [hk,abs_nonneg F,mul_nonpos_of_nonpos_of_nonneg h hg.le]
  have hden : 0 < (k:ℝ)*(k+1) := mul_pos hk' (by linarith only [hk'])
  refine ⟨1/((k:ℝ)*(k+1)),one_div_pos.mpr hden,?_⟩
  have hnear := successorSquare_relative_trace_limit.eventually_lt_const (show realSplineTrace (Real.log 4) < F-g/2 by
    dsimp only [g] at hg ⊢; linarith only [hg])
  filter_upwards [hnear,eventually_ge_atTop 1] with n hn hn₁
  have ht := tilt_squares hRH hn₁ k
  have hh : 1 ≤ integerProbe _ (successorSquareTriple n)*((k:ℝ)*(k+1)) := by
    change (k:ℝ)*(5*F-4*_)-((k:ℝ)+1)*F ≤ _ at ht
    linarith only [ht,hk,mul_le_mul_of_nonneg_left hn.le hk'.le,le_abs_self F,abs_nonneg F]
  exact (div_le_iff₀ hden).mpr hh

/-- The given square conductors have a common positive degree reserve on
an unbounded set, independently of the location of the zeros. -/
theorem cofinal_successorSquare_positive_degree_reserve :
    ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n : ℕ in atTop, δ ≤ integerProbe _ (successorSquareTriple n) := by
  by_cases hRH : RiemannHypothesis
  · obtain ⟨δ,hδ,h⟩ := successorSquare_degree_gap_of_rh hRH
    exact ⟨δ,hδ,h.frequently⟩
  · exact ⟨1,zero_lt_one,((successorSquare_degrees_of_not_rh hRH 1).1).mono fun _ h => h.le⟩

/-- On the same arbitrarily large conductors every positive multiplicity
admits exponentially many full sections at the original radius, with one
fixed saving proportional to the sum of the two squares. -/
theorem cofinal_original_sections_at_every_multiplicity :
    ∃ γ : ℝ, 0 < γ ∧ ∃ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      let a := m • successorSquareTriple n
      Real.log (generator a : ℝ)+γ*((n:ℝ)^2+(m:ℝ)^2) ≤ radius a ∧
      2*⌊Real.exp (γ*((n:ℝ)^2+(m:ℝ)^2))⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨δ,hδ,hpos⟩ := cofinal_successorSquare_positive_degree_reserve
  obtain ⟨γ,hγ,hpaid⟩ := all_original_surpluses_of_degree_reserve hδ
  refine ⟨γ,hγ,(hpos.and_eventually hpaid).mono ?_⟩
  rintro n ⟨hn,hs⟩ m hm
  let a := m • successorSquareTriple n
  let t := γ*((n:ℝ)^2+(m:ℝ)^2)
  have h : Real.log (generator a : ℝ)+t ≤ radius a := hs hn hm
  refine ⟨h,?_⟩
  have hg : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have he := Real.exp_le_exp.mpr (show t ≤ radius a-Real.log (generator a : ℝ) by linarith only [h])
  rw [Real.exp_sub,Real.exp_log hg] at he
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.floor_mono he)) _

#print axioms successorSquare_degree_gap_of_rh
#print axioms cofinal_successorSquare_positive_degree_reserve
#print axioms cofinal_original_sections_at_every_multiplicity

end GaloisForLFunctions.CountingHolography.Sections
