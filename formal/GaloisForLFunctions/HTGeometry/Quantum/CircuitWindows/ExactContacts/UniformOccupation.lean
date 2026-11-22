import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhysicalOrbit
import GaloisForLFunctions.InfiniteRankWeilTheory.OscillatorySublevelMeasure

/-! # Time spent near short circuits in translated intervals -/
open Filter Set MeasureTheory Matrix MvPolynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- Distinct phase monomials are distinct frequencies of a single finite jet. -/
private theorem phase_sublevel {I : Type} [Fintype I] {w : I→ℝ}
    (hw : RationallyIndependentFrequency w) {F : MvPolynomial I ℂ} (hF : F ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ ∀ a δ : ℝ, 0 < δ →
      volume {t∈Ioo (a-r) (a+r) | ‖aeval (fun j => energyPhase (w j) t) F‖ < δ} ≤
        ENNReal.ofReal (K*δ^((m:ℝ)⁻¹)) := by
  classical
  let Q := ↥F.support
  let e := Fintype.equivFin Q
  let c (j : Fin (Fintype.card Q)) := F.coeff (e.symm j).val
  let γ (j : Fin (Fintype.card Q)) := -monomialFrequency w (e.symm j).val
  obtain ⟨i,hi⟩ := MvPolynomial.support_nonempty.mpr hF
  let u : Q := ⟨i,hi⟩
  have hm : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨u⟩
  have hc : c ≠ 0 := by
    intro h
    have hz := congrFun h (e u)
    exact (MvPolynomial.mem_support_iff.mp hi) (by simpa only [c,Equiv.symm_apply_apply,Pi.zero_apply,u] using hz)
  have hγ : Function.Injective γ := by
    intro j l h
    exact e.symm.injective (Subtype.ext (injective_monomialFrequency hw (neg_inj.mp h)))
  have he (t : ℝ) : InfiniteRankWeilTheory.oscillatoryJet γ c 0 t =
      aeval (fun j => energyPhase (w j) t) F := by
    rw [eval_phase_expansion]
    let f (d : I →₀ ℕ) := F.coeff d * energyPhase (monomialFrequency w d) t
    change (∑ j, (c j*(Complex.I*γ j)^0)*Complex.exp (Complex.I*((γ j:ℂ)*t))) = ∑ d ∈ F.support, f d
    calc
      _ = ∑ j, f (e.symm j).val := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [γ,c,f,energyPhase,pow_zero,mul_one,Complex.ofReal_neg]
        congr 2
        ring
      _ = ∑ j : Q, f j.val := Equiv.sum_comp e.symm (fun j : Q => f j.val)
      _ = _ := by simpa only [Finset.attach_eq_univ] using Finset.sum_attach F.support f
  obtain ⟨r,K,hr,hK,h⟩ := InfiniteRankWeilTheory.exists_uniform_oscillatory_sublevel_bound γ hγ c hc
  exact ⟨_,hm,r,K,hr,hK,fun a δ hδ => by simpa only [he] using h a δ hδ⟩

/-- A power of the precision bounds total time spent near any circuit of
at most s gates in each translated window, uniformly over its center. -/
theorem gaussian_short_circuit_window_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k s : ℕ, 16*s < 2^(k+3)-1 →
      let N := k+3
      let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
      ∃ m : ℕ, 0 < m ∧ ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ a ε : ℝ, 0 < ε →
        volume {t∈Ioo (a-r) (a+r) |
          HasProjectiveCircuitApproximation N ε s (unitaryEvolution H t)} ≤
            ENNReal.ofReal (C*ε^((m:ℝ)⁻¹)) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k s hs N H
  let K : selfAdjoint (Reg N) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  have hd : 2^(k+3)=2^k*8 := by rw [pow_add]; norm_num
  have hsize : s*16+1 < 2^N-1 := by dsimp only [N]; omega
  obtain ⟨F,hF,L,hL,h⟩ := orbit_probe_bound K s hsize
  have hw := maximallyProjectiveEnergy_projectiveFrequency_independent _ (hω k) (fun _ => false)
  obtain ⟨m,hm,r,B,hr,hB,hsub⟩ := phase_sublevel hw hF
  have hL1 : 0 < L+1 := by linarith only [hL]
  refine ⟨m,hm,r,B*(L+1)^((m:ℝ)⁻¹),hr,mul_pos hB (Real.rpow_pos_of_pos hL1 _),?_⟩
  intro a ε hε
  have hu := hsub a ((L+1)*ε) (mul_pos hL1 hε)
  rw [Real.mul_rpow hL1.le hε.le,←mul_assoc] at hu
  refine (measure_mono ?_).trans hu
  rintro t ⟨ht,hfit⟩
  exact ⟨ht,(h t ε hfit).trans_lt (mul_lt_mul_of_pos_right (lt_add_one L) hε)⟩

/-- Cover a closed observation interval with windows of radius r, including
a window centered at the left endpoint. No measurability of A is required. -/
private theorem cover_occupation (A : Set ℝ) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b)
    (hw : ∀ x : ℝ, volume (Ioo (x-r) (x+r) ∩ A) ≤ ENNReal.ofReal b)
    (a T : ℝ) (hT : 0 ≤ T) :
    volume (Icc a (a+T) ∩ A) ≤ ENNReal.ofReal ((T/r+1)*b) := by
  classical
  let n := ⌊T/r⌋₊+1
  let center (j : Fin n) := a+(j.val:ℝ)*r
  let S (j : Fin n) := Ioo (center j-r) (center j+r) ∩ A
  have hsub : Icc a (a+T) ∩ A ⊆ ⋃ j, S j := by
    rintro t ⟨⟨hl,hu⟩,ht⟩
    have hdiv : (t-a)/r ≤ T/r := div_le_div_of_nonneg_right (by linarith only [hu]) hr.le
    let j : Fin n := ⟨⌊(t-a)/r⌋₊,Nat.lt_succ_of_le (Nat.floor_mono hdiv)⟩
    have hlo : (j.val:ℝ)*r ≤ t-a := (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hl) hr.le))
    have hhi : t-a < ((j.val:ℝ)+1)*r := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one _)
    refine mem_iUnion.mpr ⟨j,⟨⟨?_,?_⟩,ht⟩⟩
    · change a+(j.val:ℝ)*r-r < t
      linarith only [hlo,hr]
    · change t < a+(j.val:ℝ)*r+r
      linarith only [hhi]
  have hn : (n:ℝ) ≤ T/r+1 := by
    dsimp only [n]
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [Nat.floor_le (div_nonneg hT hr.le)]
  calc
    _ ≤ ∑ j : Fin n, volume (S j) := (measure_mono hsub).trans (measure_iUnion_fintype_le volume S)
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal b := Finset.sum_le_sum (fun j _ => hw (center j))
    _ = ENNReal.ofReal ((n:ℝ)*b) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn hb)

/-- At every error the total affordable time in every interval of length
T is bounded by (1+T/r) C ε^(1/m) with fixed positive prefix constants. -/
theorem gaussian_short_circuit_interval_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k s : ℕ, 16*s < 2^(k+3)-1 →
      let N := k+3
      let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
      ∃ m : ℕ, 0 < m ∧ ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ a T ε : ℝ, 0 ≤ T → 0 < ε →
        volume {t∈Icc a (a+T) |
          HasProjectiveCircuitApproximation N ε s (unitaryEvolution H t)} ≤
            ENNReal.ofReal ((T/r+1)*(C*ε^((m:ℝ)⁻¹))) := by
  filter_upwards [gaussian_short_circuit_window_occupation] with ω hω
  intro k s hs N H
  obtain ⟨m,hm,r,C,hr,hC,hw⟩ := hω k s hs
  refine ⟨m,hm,r,C,hr,hC,fun a T ε hT hε => ?_⟩
  exact cover_occupation _ hr (mul_nonneg hC.le (Real.rpow_nonneg hε.le _))
    (fun x => hw x ε hε) a T hT

#print axioms gaussian_short_circuit_interval_occupation
end
end GaloisForLFunctions.HTGeometry.ExactContacts
