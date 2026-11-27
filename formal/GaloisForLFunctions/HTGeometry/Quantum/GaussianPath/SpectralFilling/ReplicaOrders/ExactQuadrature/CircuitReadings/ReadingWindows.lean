import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.CircuitReadings.FrozenPlateau
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # Forward waiting windows at explicit physical clock readings -/
open Filter MeasureTheory Set Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
open SharpOccupation
noncomputable section

private theorem reading_shift (ws : List ℝ) (f : ℝ → ℝ) (a u : ℝ) :
    reading ws (fun t => f (t+u)) a=reading ws f (a+u) := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    change ((average ws (fun t => (f (t+u):ℂ)) a+
      average ws (fun t => (f (t+u):ℂ)) (a+π/|w|))/2).re=_
    simp only [reading,average,show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.div_ofReal_re,Complex.add_re] at ih ⊢
    rw [ih,ih,show a+π/|w|+u=a+u+π/|w| by ring]

/-- A positive reading means that some continuous date in the forward
window admits a fit at the fixed tolerance. -/
def windowIndicator {K : ℕ} (H : selfAdjoint (Register K)) (s : ℕ) (L a : ℝ) : ℝ := by
  classical
  exact if ∃ t∈Icc a (a+L), HasProjectiveCircuitApproximation K (1/10) s
    (unitaryEvolution H.val t) then 1 else 0

private theorem window_grid {K : ℕ} (H : selfAdjoint (Register K)) (s : ℕ) (L a : ℝ) :
    let W := circuitHamiltonianSpectralWidth H
    let h := 1/(2*(1+W))
    windowIndicator H s L a ≤ ∑ j:Fin (plateauGridCount L h), gateIndicator H s (39/80) (a+(j.val:ℝ)*h) := by
  classical
  intro W h
  have hW : 0≤W := circuitHamiltonianSpectralWidth_nonneg H
  have hpos : 0<h := by dsimp only [h]; positivity
  have hstep : (W/2)*h≤1/4 := by
    dsimp only [h]
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    linarith only [hW]
  have hz (j : Fin (plateauGridCount L h)) : 0≤gateIndicator H s (39/80) (a+(j.val:ℝ)*h) := by
    unfold gateIndicator; split <;> norm_num
  unfold windowIndicator
  split_ifs with hv
  · obtain ⟨t,ht,he⟩ := hv
    obtain ⟨j,hj⟩ := exists_plateauGrid_near hpos a ht
    let g := a+(j.val:ℝ)*h
    obtain ⟨c,hc,hlip⟩ := orbitCircuitDistance_lipschitz_spectralWidth H s
    have hd := hlip.dist_le_mul t g
    rw [Real.dist_eq,Real.dist_eq,hc] at hd
    have hh := (abs_le.mp (hd.trans (mul_le_mul_of_nonneg_left hj (div_nonneg hW (by norm_num))))).1
    have hcheap := (hasProjectiveCircuitApproximation_iff_infDist ..).mp he
    change orbitCircuitDistance H s t≤1/10 at hcheap
    have hg : orbitCircuitDistance H s g≤39/80 := by linarith only [hh,hstep,hcheap]
    have hgate : gateIndicator H s (39/80) g=1 := if_pos ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hg)
    exact hgate.ge.trans (single_le_sum (fun j _ => hz j) (mem_univ j))
  · exact sum_nonneg fun j _ => hz j

/-- On one frozen chain the fraction of binary choices followed by even
one affordable date in a continuous window of length L is bounded by
the grid count times b^D. The initial origin may be the original crossing. -/
theorem gaussian_clock_forward_wait :
    ∃ b∈Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      let q := 2*2^(k+1)
      let h := 1/(2*(1+circuitHamiltonianSpectralWidth H))
      ∀ a L : ℝ, ∀ s≤nearHilbertContinuousCircuitBudget K,
        reading (frequencies E q).toList (windowIndicator H s L) a ≤ (plateauGridCount L h:ℝ)*b^D := by
  obtain ⟨b,hb,hread⟩ := gaussian_hard_clock_readings
  refine ⟨b,hb,?_⟩
  filter_upwards [hread] with ω hw
  filter_upwards [hw] with k hk
  intro K D H E q h a L s hs
  let ws := (frequencies E q).toList
  have hsum := reading_mono ws (window_grid H s L) a
  rw [reading_sum] at hsum
  apply hsum.trans
  calc
    _ ≤ ∑ _j : Fin (plateauGridCount L h), b^D := by
      apply sum_le_sum
      intro j _
      rw [reading_shift]
      exact (hk _ (39/80) le_rfl s hs).le
    _ = _ := by rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- At any origin, apart from sampling mass at most 3√(b^D), the
following entire interval of length 1/[2(1+W)√(b^D)] has no cheap date.
Here W is the measured spectral bandwidth of the frozen prefix. -/
theorem gaussian_long_sampled_wait :
    ∃ b∈Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      let r := sqrt (b^D)
      let h := 1/(2*(1+circuitHamiltonianSpectralWidth H))
      ∀ a : ℝ, ∀ s≤nearHilbertContinuousCircuitBudget K,
        reading (frequencies E (2*2^(k+1))).toList (windowIndicator H s (h/r)) a ≤ 3*r := by
  obtain ⟨b,hb,hread⟩ := gaussian_clock_forward_wait
  refine ⟨b,hb,?_⟩
  filter_upwards [hread] with ω hw
  filter_upwards [hw] with k hk
  intro K D H E r h a s hs
  have hW := circuitHamiltonianSpectralWidth_nonneg H
  have hh : 0<h := by dsimp only [h]; positivity
  have hR : 0<r := sqrt_pos.mpr (pow_pos hb.1 D)
  have hR2 : r^2=b^D := sq_sqrt (pow_nonneg hb.1.le _)
  have hR₁ : r≤1 := by
    nlinarith only [hR2,pow_le_one₀ hb.1.le hb.2.le (n:=D),sq_nonneg (r-1)]
  have hcount : (plateauGridCount (h/r) h:ℝ)≤1/r+2 := by
    rw [plateauGridCount,show h/r/h=1/r by field_simp [hh.ne',hR.ne'],Nat.cast_add,Nat.cast_one]
    linarith only [Nat.ceil_lt_add_one (one_div_pos.mpr hR).le]
  apply (hk a (h/r) s hs).trans
  calc
    _ ≤ (1/r+2)*b^D := mul_le_mul_of_nonneg_right hcount (pow_nonneg hb.1.le _)
    _ = r+2*r^2 := by rw [←hR2]; field_simp [hR.ne']
    _ ≤ _ := by nlinarith only [mul_le_of_le_one_right hR.le hR₁]

#print axioms gaussian_long_sampled_wait
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
