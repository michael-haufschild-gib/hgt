import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhysicalOrbit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.SampleDiameter

/-! # Uniform duration of approximate visits to a physical gate budget -/
open Filter Set MeasureTheory Matrix MvPolynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

private theorem polynomial_window_bound {I : Type} [Fintype I] {w : I→ℝ}
    (hw : RationallyIndependentFrequency w) {F : MvPolynomial I ℂ} (hF : F ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, 0 < c ∧ ∀ a W δ : ℝ, 0 ≤ W →
      (∀ t ∈ Icc a (a+W), ‖aeval (fun j => energyPhase (w j) t) F‖ ≤ δ) →
      c*(min W 1)^m ≤ δ := by
  classical
  let J := F.support
  obtain ⟨i,hi⟩ := MvPolynomial.support_nonempty.mpr hF
  have hiJ : i ∈ J := hi
  obtain ⟨κ,H,hκ,hH,hb⟩ := exponential_sample_floor J (fun d => F.coeff d)
    (monomialFrequency w) hiJ (MvPolynomial.mem_support_iff.mp hi) (injective_monomialFrequency hw).injOn
  let α := min H (1/((J.card:ℝ)+1))
  have hα : 0 < α := lt_min hH (by positivity)
  have hm : 0 < J.card := Finset.card_pos.mpr ⟨i,hiJ⟩
  refine ⟨J.card,hm,κ*α^(J.card-1),mul_pos hκ (pow_pos hα _),?_⟩
  intro a W δ hW hδ
  let x := min W 1
  have hx : 0 ≤ x := le_min hW zero_le_one
  have hx1 : x ≤ 1 := min_le_right _ _
  have hstep : α*x ≤ H := (mul_le_of_le_one_right hα.le hx1).trans (min_le_left _ _)
  have hh := hb a (α*x) δ (mul_nonneg hα.le hx) hstep (fun q hq => by
    have hqR : (q:ℝ) ≤ (J.card:ℝ)+1 := by exact_mod_cast (show q ≤ J.card+1 by omega)
    have hr : (q:ℝ)*α ≤ 1 := calc
      _ ≤ ((J.card:ℝ)+1)*(1/((J.card:ℝ)+1)) := mul_le_mul hqR (min_le_right _ _) hα.le (by positivity)
      _ = _ := by field_simp
    have hlen : (q:ℝ)*(α*x) ≤ W := by
      rw [←mul_assoc]
      exact (mul_le_of_le_one_left hx hr).trans (min_le_left _ _)
    have ht := hδ (a+(q:ℝ)*(α*x))
      ⟨le_add_of_nonneg_right (by positivity),add_le_add_right hlen a⟩
    simpa only [eval_phase_expansion] using ht)
  have hpow : x^J.card ≤ x^(J.card-1) := by
    calc
      _ = x^(J.card-1)*x := by
        rw [←pow_succ,show J.card-1+1=J.card by omega]
      _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hx _) hx1
  change κ*α^(J.card-1)*x^J.card ≤ δ
  rw [mul_pow,←mul_assoc] at hh
  exact (mul_le_mul_of_nonneg_left hpow (mul_nonneg hκ.le (pow_nonneg hα.le _))).trans hh

/-- On each Gaussian prefix the length W of any uninterrupted s-gate
visit satisfies c·min(W,1)^m ≤ ε whenever 16s < 2ᴺ−1. The same positive
c and finite positive m work over the entire trajectory at every error. -/
theorem gaussian_short_circuit_visit_duration :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k s : ℕ, 16*s < 2^(k+3)-1 →
      let N := k+3
      let K := pathHamiltonian (pathPauliDisorderShell ω (k+1))
      ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, 0 < c ∧ ∀ a W ε : ℝ, 0 ≤ W →
        (∀ t∈Icc a (a+W), HasProjectiveCircuitApproximation N ε s (unitaryEvolution K t)) →
        c*(min W 1)^m ≤ ε := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k s hs N K
  let H : selfAdjoint (Reg N) := ⟨K,isSelfAdjoint_pathHamiltonian _⟩
  have hd : 2^(k+3)=2^k*8 := by rw [pow_add]; norm_num
  have hsize : s*16+1 < 2^N-1 := by dsimp only [N]; omega
  obtain ⟨F,hF,L,hL,h⟩ := orbit_probe_bound H s hsize
  have hw := maximallyProjectiveEnergy_projectiveFrequency_independent _ (hω k) (fun _ => false)
  obtain ⟨m,hm,c,hc,hbound⟩ := polynomial_window_bound hw hF
  have hK : 0 < L+1 := by linarith only [hL]
  refine ⟨m,hm,c/(L+1),div_pos hc hK,?_⟩
  intro a W ε hW hh
  have hb := hbound a W (L*ε) hW (fun t ht => h t ε (hh t ht))
  obtain ⟨_,_,_,_,he⟩ := hh a ⟨le_rfl,le_add_of_nonneg_right hW⟩
  have heps : 0 ≤ ε := (norm_nonneg _).trans he
  rw [div_mul_eq_mul_div,div_le_iff₀ hK]
  linarith only [hb,heps]

#print axioms gaussian_short_circuit_visit_duration
end
end GaloisForLFunctions.HTGeometry.ExactContacts
