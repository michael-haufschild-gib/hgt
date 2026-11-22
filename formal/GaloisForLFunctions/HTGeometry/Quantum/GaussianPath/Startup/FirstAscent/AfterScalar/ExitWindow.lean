import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.AfterScalar.UniformAngles
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ExitInfimum
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Physical first exits after a scalar visit with a specified error -/
open MeasureTheory Filter Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.AfterScalar
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Elapsed time until a circuit budget first fails at physical error 1/10. -/
def exitLag {N : ℕ} (H : selfAdjoint (Reg N)) (s : ℕ) (v : ℝ) :=
  sInf {t : ℝ | 0 ≤ t ∧ ¬HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (v+t))}

/-- Visiting the scalar tube at error δ perturbs the lower and upper dates
of the first budget exit by at most 4δ/W. -/
theorem gaussian_exit_lag_with_margin :
    ∃ c C a : ℝ, ∃ M : ℕ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        let θ := arcsin (1/20)
        a*N ≤ W ∧ ∀ s : ℕ, 0 < s → M*s ≤ N →
          let F := (s:ℝ)*sqrt (log ((N:ℝ)/s))/(N:ℝ)^2
          ∀ δ ∈ Icc 0 (θ/2), ∀ v : ℝ,
            HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val v) →
            exitLag H s v-4*θ/W ∈ Icc (c*F-4*δ/W) (C*F+4*δ/W) := by
  obtain ⟨c,C,a,b,m,hc,hC,ha,hb,hm,hw⟩ := gaussian_uniform_angles
  obtain ⟨L,hL⟩ := exists_nat_ge (C*b)
  let M := max m (L^2)
  refine ⟨c,C,a,M,hc,hC,ha,hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro N H W θ
  refine ⟨hn.1,?_⟩
  intro s hs hsize F δ hδ v hv
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hW := (mul_pos ha hN).trans_le hn.1
  have hθ : 0 < θ := arcsin_pos.mpr (by norm_num)
  have hθmax : θ ≤ π/40 := by
    have h := GaloisForLFunctions.arcsin_le_pi_half_mul (1/20) (by norm_num) (by norm_num)
    dsimp only [θ]; linarith only [h]
  have hθsin : 2*sin θ=1/10 := by
    rw [show sin θ=1/20 from sin_arcsin (by norm_num) (by norm_num)]; norm_num
  have hminus : θ-δ ∈ Icc (θ/2) (2*θ) := ⟨by linarith only [hδ.2],by linarith only [hθ,hδ.1]⟩
  have hplus : θ+δ ∈ Icc (θ/2) (2*θ) := ⟨by linarith only [hδ.1,hθ],by linarith only [hδ.2,hθ]⟩
  have hml := sine_chord_floor ((half_pos hθ).le.trans hminus.1)
    (sub_le_self θ hδ.1) (by linarith only [hθmax,pi_pos])
  have hmu := sine_chord_floor hθ.le (le_add_of_nonneg_right hδ.1)
    (by linarith only [hplus.2,hθmax,pi_pos])
  have hms := (Nat.mul_le_mul_right s (le_max_left m (L^2))).trans hsize
  have hcut := (Nat.mul_le_mul_right s (le_max_right m (L^2))).trans hsize
  have hsN := (Nat.le_mul_of_pos_left s hm).trans hms
  have hwindow := hn.2.2 s hs hms
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpay : (C*F)*W ≤ 1 := calc
    _ ≤ (C*F)*(b*N) := mul_le_mul_of_nonneg_left hn.2.1 (mul_nonneg hC.le hF)
    _ = (C*b)*((s:ℝ)/N)*sqrt (log ((N:ℝ)/s)) := by dsimp only [F]; field_simp
    _ ≤ (L:ℝ)*((s:ℝ)/N)*sqrt (log ((N:ℝ)/s)) := by gcongr
    _ ≤ 1 := budget_mass_bound (Nat.cast_nonneg L) hs' hN (by exact_mod_cast hsN) (by exact_mod_cast hcut)
  let hi := 4*(θ+δ)/W+C*F
  let lo := 4*(θ-δ)/W+c*F
  have hip : 0 ≤ hi := add_nonneg (div_nonneg (by linarith only [hθ,hδ.1]) hW.le) (mul_nonneg hC.le hF)
  have hbefore : hi < π/W := (lt_div_iff₀ hW).mpr (by
    dsimp only [hi]; rw [add_mul,div_mul_cancel₀ _ hW.ne']
    linarith only [hpay,hδ.2,hθmax,pi_gt_three])
  have lower (t : ℝ) (ht : t ∈ Icc 0 lo) :
      HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (v+t)) := by
    have hi' := (hwindow (θ-δ) hminus).1 t ht
    obtain ⟨z,hz,C',hC',he⟩ := affordable_add_time H hv hi'
    exact ⟨z,hz,C',by simpa using hC',he.trans (by linarith only [hml,hθsin])⟩
  have upper (t : ℝ) (ht : t ∈ Icc 0 (π/W))
      (hv' : HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (v+t))) : t ≤ hi := by
    have hh := affordable_add_time H (hv.neg_time H) hv'
    rw [neg_add_cancel_left,Nat.zero_add] at hh
    obtain ⟨z,hz,C',hC',he⟩ := hh
    exact (hwindow (θ+δ) hplus).2 t ht ⟨z,hz,C',hC',he.trans (by linarith only [hmu,hθsin])⟩
  have he := first_exit_bracket _ hip hbefore lower upper
  change lo ≤ exitLag H s v ∧ exitLag H s v ≤ hi at he
  simp only [hi,lo,mul_add,mul_sub,add_div,sub_div] at he
  constructor
  · linarith only [he.1]
  · linarith only [he.2]

#print axioms gaussian_exit_lag_with_margin
end
end GaloisForLFunctions.HTGeometry.FirstAscent.AfterScalar
