import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.GaussianBonds
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondMass
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Unit limiting gate density at physical error on the initial Gaussian time window -/
open Filter Set MeasureTheory Matrix Real
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

private theorem bond_fit {n : ℕ} (u : PathShell n) (t ε : ℝ)
    (he : 1/20 ≤ ε) (ht : |t| * ‖u‖ ≤ 1/100) :
    HasProjectiveCircuitApproximation (n+2) ε (n+1) (unitaryEvolution (pathHamiltonian u) t) := by
  let H : selfAdjoint (Matrix (Fin (n+2)→Bool) _ ℂ) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
  have hs : (|t| * ‖u‖)^2 ≤ (1/100:ℝ)^2 :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) ht 2
  obtain ⟨z,hz,C,hC,hfit⟩ := BondProducts.bond_sweep_error u |t| (abs_nonneg _) 1 one_pos
  have ha : HasProjectiveCircuitApproximation (n+2) ε (n+1) (unitaryEvolution H.val |t|) := by
    refine ⟨z,hz,C,by simpa using hC.le,hfit.trans ?_⟩
    simp only [Nat.cast_one,div_one]; nlinarith only [hs,he]
  by_cases h : 0≤t
  · simpa only [abs_of_nonneg h] using ha
  · simpa only [abs_of_neg (lt_of_not_ge h),neg_neg] using ha.neg_time H

private theorem budget_floor {n : ℕ} (u : PathShell n) (t ε q : ℝ) (s : ℕ)
    (hq : 0<q) (herr : ε≤1/4) (ht : |t| * ‖u‖ ≤ 1/100)
    (hlate : π ≤ |t| *q^2*(n+1:ℕ)) (hc : HasProjectiveCircuitApproximation (n+2) ε s
      (unitaryEvolution (pathHamiltonian u) t))
    (hm : ∀ S : Finset (Fin (n+1)), q*((S.card:ℝ)-3*q*(n+1:ℕ)) ≤ ∑ e∈S, |u (.inr (e,2,2))|) :
    (1-8*q)*(n+1:ℕ) ≤ s := by
  obtain ⟨z,hz,C,hC,hfit⟩ := hc
  obtain ⟨c,hvert,hmass⟩ := affordable_sparse_cut u C t z hz (hfit.trans herr) ht
  have h₁ := mul_le_mul_of_nonneg_left (hm (crossed c)) (show 0≤4*|t| from by positivity)
  have hpos : 0 < |t| := by
    by_contra! h
    have he := le_antisymm h (abs_nonneg t)
    rw [he,zero_mul,zero_mul] at hlate
    exact pi_pos.not_ge hlate
  have h₂ : ((crossed c).card:ℝ) < 4*q*(n+1:ℕ) := by
    apply (mul_lt_mul_iff_right₀ (mul_pos hpos hq)).mp
    have hb := mul_pos (mul_pos hpos (sq_pos_of_pos hq))
      (show 0<((n+1:ℕ):ℝ) by positivity)
    nlinarith only [h₁,hmass,hlate,hb]
  have h₃ : ((n+1:ℕ):ℝ) ≤ (s:ℝ)+2*(crossed c).card := by exact_mod_cast hvert.trans (Nat.add_le_add_right hC _)
  linarith only [h₂,h₃]

/-- All signed times in the window and all physical errors in [1/20,1/4]
share the same estimate. On the scale N|t|→∞, √N|t|→0, let k increase
after taking N large to obtain unit limiting gate density. -/
theorem gaussian_spanning_gate_density :
    ∃ b : ℝ, 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, π ≤ |t| *q^2*(n+1:ℕ) → t^2*(n+2:ℕ) ≤ b →
        ∀ ε∈Icc (1/20:ℝ) (1/4), ∃ s : ℕ,
          IsLeast {j | HasProjectiveCircuitApproximation (n+2) ε j
            (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)} s ∧
          (1-8*q)*(n+1:ℕ) ≤ s ∧ s≤n+1 := by
  classical
  obtain ⟨_,B,_,hB,hbulk⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨1/(10000*B),by positivity,?_⟩
  filter_upwards [hbulk,gaussian_subset_longitudinal_mass] with ω hω hmass k
  intro q
  filter_upwards [hω,hmass k] with n hn hqmass
  intro t hlate ht ε he
  let u := pathPauliDisorderShell ω n
  have hcap : |t| * ‖u‖ ≤ 1/100 := by
    have hsq := mul_le_mul_of_nonneg_left hn.2 (sq_nonneg t)
    have hb := (le_div_iff₀ (show 0<10000*B by positivity)).mp ht
    have h : (|t| * ‖u‖)^2 ≤ (1/100:ℝ)^2 := by
      rw [mul_pow,sq_abs]
      nlinarith only [hsq,hb]
    exact le_of_sq_le_sq h (by norm_num)
  let afford (j : ℕ) := HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution (pathHamiltonian u) t)
  have hu : afford (n+1) := bond_fit u t ε he.1 hcap
  have hex : ∃ j, afford j := ⟨_,hu⟩
  refine ⟨Nat.find hex,⟨Nat.find_spec hex,fun _ hx => Nat.find_min' hex hx⟩,?_,Nat.find_min' hex hu⟩
  exact budget_floor u t ε q _ (by dsimp only [q]; positivity) he.2 hcap hlate (Nat.find_spec hex) hqmass

#print axioms gaussian_spanning_gate_density
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
