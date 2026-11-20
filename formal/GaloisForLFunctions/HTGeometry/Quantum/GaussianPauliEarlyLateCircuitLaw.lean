import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitOrder
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-!
# Microscopic circuit cost, large excursions and affordable returns on one Pauli chain

All prefix lengths refer to the same sequence of independent local couplings.
A translated hard interval has an attained first subsequent affordable time.
-/
open MeasureTheory Filter Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- For a fixed physical generator, a uniformly bounded wait leads to a
hard interval of the specified length. Window starts containing an
affordable time have upper time density at most 1/(r+1)^r. Each budget has a
first subsequent hit beyond the interval, with a dimensional deadline. -/
def PhysicalExcursionAndReturns {n : ℕ} (H : selfAdjoint (Reg n)) : Prop :=
  let r := excursionGateBudget n
  let W := translatedExcursionWidth n ‖(H : Reg n)‖
  let U := unitaryEvolution (H : Reg n)
  (∃ S : ℝ, 0 ≤ S ∧ ∀ A T : ℝ, 0 ≤ T →
    (r+1:ℝ)^r * volume.real (circuitWindowHits H.val r W ∩ Icc A (A+T)) ≤ T+S) ∧
  ∃ G : ℝ, 0 ≤ G ∧ ∀ A : ℝ, ∃ u ∈ Icc A (A+G),
    (∀ t ∈ Icc u (u+W), ProjectiveCircuitSeparated n (1/10:ℝ) r (U t)) ∧
    ∀ s ≤ r, ∃ v ∈ Ioc (u+W) ((|u|+1)*(100:ℝ)^(2^n-1)),
      HasProjectiveCircuitApproximation n (1/10:ℝ) s (U v) ∧
      ∀ t ∈ Ico u v, ProjectiveCircuitSeparated n (1/10:ℝ) s (U t)

private theorem excursion_of_projective_spectrum {n : ℕ} (hn : 1 ≤ n)
    (hent : atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) <
      ((2^(2^n-1) : ℕ) : ℝ)) (H : selfAdjoint (Reg n))
    (hH : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) :
    PhysicalExcursionAndReturns H := by
  let d := 2^n-1
  let e : (Fin n → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^n := by positivity
                  dsimp [d]; omega))
  let r := excursionGateBudget n
  let W := translatedExcursionWidth n ‖(H : Reg n)‖
  let m := 1/(40*(‖(H : Reg n)‖+1))
  have hm : 0 < m := by dsimp [m]; positivity
  have hs : ‖(H : Reg n)‖*m ≤ 1/40 := by
    dsimp [m]; rw [mul_one_div,div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hcount : plateauGridCount W m = (r+1)^r := by
    change ⌈((((r+1)^r-1 : ℕ) : ℝ)*m)/m⌉₊ + 1 = _
    rw [mul_div_cancel_right₀ _ hm.ne',Nat.ceil_natCast]
    have hp : 0 < (r+1)^r := by positivity
    omega
  have hc : plateauGridCount W m * (atMostQuarterCircuitNet n r).card < 2^d := by
    rw [hcount]
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < r+1)
      (by omega : r ≤ 2*r))).trans_lt (translated_excursion_square_card hn hent)
  obtain ⟨G,hG,hwin⟩ := translatedNet_physical_hard_window e H (hH.comp_equiv e.symm) W m hm hs hc
  constructor
  · obtain ⟨S,hS,hobs⟩ := spectral_sign_window_occupation e H (hH.comp_equiv e.symm)
    refine ⟨S,hS,?_⟩
    intro A T hT
    let M := (r+1)^r
    let Q := (atMostQuarterCircuitNet n r).card
    let V := volume.real (circuitWindowHits H.val r W ∩ Icc A (A+T))
    have hQ : 0 < Q := by
      obtain ⟨x,hx,_⟩ := atMostQuarterCircuitNet_cover (TwoQubitCircuit.one n)
        (show (TwoQubitCircuit.one n).gateCount ≤ r from Nat.zero_le _)
      exact Finset.card_pos.mpr ⟨x,hx⟩
    have hM : 0 < M := by dsimp [M]; positivity
    have hsq : M*M*Q < 2^d := by
      rw [show M*M = (r+1)^(2*r) by rw [two_mul,pow_add]]
      exact translated_excursion_square_card hn hent
    have hsq' : (M:ℝ)*M*Q ≤ (2:ℝ)^d := by exact_mod_cast hsq.le
    have hvol := hobs r W m hm hs A T hT
    rw [hcount] at hvol
    change (2:ℝ)^d*V ≤ (M:ℝ)*Q*(T+S) at hvol
    have hv : 0 ≤ V := ENNReal.toReal_nonneg
    have hgoal : (M:ℝ)*V ≤ T+S := by
      apply le_of_mul_le_mul_left _ (show 0 < (M:ℝ)*Q by positivity)
      calc
        _ = ((M:ℝ)*M*Q)*V := by ring
        _ ≤ (2:ℝ)^d*V := mul_le_mul_of_nonneg_right hsq' hv
        _ ≤ _ := hvol
    simpa only [M,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hgoal
  refine ⟨G,hG,?_⟩
  intro A
  obtain ⟨u,hu,hh⟩ := hwin A
  refine ⟨u,hu,hh,?_⟩
  intro s hs
  obtain ⟨v,hv,he,hgap⟩ := projective_first_circuit_visit_deadline e H u s
  refine ⟨v,⟨?_,hv.2⟩,he,hgap⟩
  by_contra! h
  obtain ⟨z,hz,C,hC,herr⟩ := he
  exact (not_lt_of_ge herr) (hh v ⟨hv.1,h⟩ z hz C (hC.trans hs))

/-- Almost every infinite Gaussian Pauli field has, on every sufficiently
long prefix, a linearly costly early window, recurring exponential-budget
hard intervals and attained first returns after those intervals. -/
theorem gaussian_pauli_chain_early_cost_excursions_and_returns :
    ∃ A B W c : ℝ, ∃ K : ℕ, 0 < A ∧ 0 < B ∧ 0 < W ∧ 0 < c ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let u := pathPauliDisorderShell ω (k+1)
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
        let E := H.2.isHermitian.eigenvalues
        (∃ i j, (∀ p q, E p-E q ≤ E i-E j) ∧
          let t := Real.pi/(E i-E j)
          A ≤ N*t ∧ N*t ≤ B ∧ ∀ τ : ℝ, (N:ℝ)*|t-τ| ≤ W →
            HasProjectiveCircuitApproximation N (1/10:ℝ) (K*N) (unitaryEvolution H.val τ) ∧
            ∀ (C : TwoQubitCircuit N) (z : ℂ),
              ‖unitaryEvolution H.val τ - z • (C.eval : Reg N)‖ ≤ 1/10 → c*N ≤ C.gateCount) ∧
          PhysicalExcursionAndReturns H := by
  obtain ⟨A,B,W,c,K,hA,hB,hW,hc,hmicro⟩ := gaussian_path_inverse_bandwidth_circuit_order
  refine ⟨A,B,W,c,K,hA,hB,hW,hc,?_⟩
  filter_upwards [hmicro,gaussian_path_all_prefixes_maximally_projective] with ω hm hω
  have hshift : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsites : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hshift.eventually hm,
    hsites.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
      with k hk he
  refine ⟨?_,excursion_of_projective_spectrum (by omega) he _ (hω k)⟩
  obtain ⟨i,j,hmax,hlo,hhi,hwin⟩ := hk
  refine ⟨i,j,hmax,?_,?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc] using hlo
  · simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc] using hhi
  intro τ hτ
  have hh := hwin τ (by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc] using hτ)
  refine ⟨hh.1,?_⟩
  intro C z herr
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc] using hh.2 C z herr

#print axioms gaussian_pauli_chain_early_cost_excursions_and_returns
end
end GaloisForLFunctions.HTGeometry
