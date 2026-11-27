import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.AfterVisit.Bracket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.PrecisionWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.FirstCrossings

/-! # First robust rebound below one sweep after a physical gate visit -/

open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrescribedTimes
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
private abbrev chain (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Reg (n+2)) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩

/-- Every one-tenth visit with at most half the missing gate count
restarts the same first-crossing scale as the identity. -/
theorem gaussian_visit_crossing_scale :
    ∃ γ>0, ∃ Q>0, ∃ l>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := chain ω n
      ∀ d s : ℕ, 0<d → 2*s≤d → (d:ℝ)≤γ*K → Q*K^11≤(d:ℝ)^20 →
        ∀ v : ℝ, HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) →
          ∀ ρ∈Icc (9/80:ℝ) (1/8), ∃ τ : ℝ,
            IsLeast {t : ℝ | 0≤t ∧ ρ≤orbitCircuitDistance H (n+1-d) (v+t)} τ ∧
            orbitCircuitDistance H (n+1-d) (v+τ)=ρ ∧ l*K≤τ^9*(d:ℝ)^10 ∧ τ^9*(d:ℝ)^10≤L*K := by
  obtain ⟨g,hg,R,hR,hfast⟩ := gaussian_residence_at_precision
  obtain ⟨a,ha,hearly⟩ := hfast (1/160) (by norm_num)
  obtain ⟨γ,hγ,Q,hQ,l,hl,L,hL,hlate⟩ := gaussian_first_crossing_scale
  let g' := min (1/4:ℝ) (min (g/2) γ)
  let R' := max R (2^20*Q)
  refine ⟨g',lt_min (by norm_num) (lt_min (by positivity) hγ),R',hR.trans_le (le_max_left ..),
    a/2^10,by positivity,2^10*L,by positivity,?_⟩
  filter_upwards [hearly,hlate] with ω hw hx
  filter_upwards [hw,hx] with n hn hx
  intro K H d s hd hs hγd hQd v hv ρ hρ
  let i := d+s
  let q := d-s
  have hK : 0<K := by dsimp only [K]; positivity
  have hqd : q≤d := Nat.sub_le ..
  have hqpos : 0<q := by dsimp only [q]; omega
  have hdq : (d:ℝ)≤2*(q:ℝ) := by exact_mod_cast (show d≤2*q by dsimp only [q]; omega)
  have hdi : (i:ℝ)≤2*(d:ℝ) := by exact_mod_cast (show i≤2*d by dsimp only [i]; omega)
  have hid : (d:ℝ)≤(i:ℝ) := by exact_mod_cast (Nat.le_add_right d s)
  have hratio (b : ℝ) (hb : g'≤b) := hγd.trans (mul_le_mul_of_nonneg_right hb hK.le)
  have hiK : i≤n+1 := by
    have hcap := hratio _ (min_le_left ..)
    apply (Nat.cast_le (α:=ℝ)).mp
    dsimp only [K] at hcap
    push_cast at hcap ⊢
    linarith only [hdi,hcap,Nat.cast_nonneg (α:=ℝ) n]
  have hqK : q≤n+1 := hqd.trans ((Nat.le_add_right d s).trans hiK)
  have hmin := min_le_right (1/4:ℝ) (min (g/2) γ)
  have hiγ : (i:ℝ)≤g*K := by linarith only [hdi,hratio _ (hmin.trans (min_le_left ..))]
  have hqγ := ((Nat.cast_le (α:=ℝ)).mpr hqd).trans (hratio _ (hmin.trans (min_le_right ..)))
  have hiR : R*K^11≤(i:ℝ)^20 := ((mul_le_mul_of_nonneg_right (le_max_left ..)
    (pow_nonneg hK.le 11)).trans hQd).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hid 20)
  have hqR : Q*K^11≤(q:ℝ)^20 := by
    have he := ((mul_le_mul_of_nonneg_right (le_max_right R (2^20*Q))
      (pow_nonneg hK.le 11)).trans hQd).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hdq 20)
    rw [mul_pow] at he
    linarith only [he]
  let x := fun j => pathPauliDisorderShell ω n (pathCoeffEquiv n j)
  let σ := crossingOrigin n (n+1-q) (1/4) x
  obtain ⟨hlo,hhi⟩ := hx q hqpos hqK hqγ hqR (1/4) (by constructor <;> norm_num)
  change l*K≤σ^9*(q:ℝ)^10 at hlo
  change σ^9*(q:ℝ)^10≤L*K at hhi
  have hσ : 0≤σ := Real.sInf_nonneg (s:={t : ℝ | 0≤t ∧ 1/4≤pathGateDistance n (n+1-q) x t})
    (fun _ ht => ht.1)
  have hpos : 0<σ := lt_of_le_of_ne hσ (by
    intro hz
    rw [←hz,zero_pow (by decide),zero_mul] at hlo
    exact (mul_pos hl hK).not_ge hlo)
  have hdist := crossing_attains_of_pos hpos
  change 1/4≤pathGateDistance n (n+1-q) x σ at hdist
  rw [pathGateDistance,numberedGenerator_shell (pathPauliDisorderShell ω n)] at hdist
  let P (t : ℝ) := t^9*(d:ℝ)^10 ≤ (a/2^10)*K
  have hstart : P 0 := by
    change (0:ℝ)^9*(d:ℝ)^10≤a/2^10*K
    rw [zero_pow (by decide),zero_mul]
    positivity
  have low (t : ℝ) (ht : 0≤t) (hp : P t) := hn i (hd.trans_le (Nat.le_add_right d s)) hiγ hiR t (by
    rw [abs_of_nonneg ht]
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hdi 10) (pow_nonneg ht _)).trans
    rw [mul_pow]
    change t^9*(d:ℝ)^10≤a/2^10*K at hp
    linarith only [hp])
  have hi : s+(n+1-i)≤n+1-d := by change s+(n+1-(d+s))≤n+1-d; change d+s≤n+1 at hiK; omega
  have hk : s+(n+1-d)≤n+1-q := by dsimp only [q]; omega
  obtain ⟨τ,hm,he,hb,hu⟩ := shifted_first_crossing H hv hi hk hρ hσ hdist P hstart low
  refine ⟨τ,hm,he,(lt_of_not_ge hb).le,?_⟩
  calc
    _ ≤ σ^9*(2*(q:ℝ))^10 := mul_le_mul (pow_le_pow_left₀ hm.1.1 hu 9)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hdq 10) (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hσ _)
    _ = 2^10*(σ^9*(q:ℝ)^10) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hhi (by norm_num : (0:ℝ)≤2^10)).trans_eq (by ring)

/-- At the first physical low visit after the near-Hilbert crossing,
the first subsequent 9/80 crossing of the K-1-d budget is attained
at a lag of order (K/d¹⁰)^(1/9). -/
theorem gaussian_first_dip_crossing_scale :
    ∃ γ>0, ∃ Q>0, ∃ l>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := chain ω n
      ∀ d s : ℕ, 0<d → 2*s≤d → (d:ℝ)≤γ*K → Q*K^11≤(d:ℝ)^20 →
        let v := RepeatedGates.PhysicalBlocks.firstLowAfterCrossing ω n s
        ∃ τ : ℝ, IsLeast {t : ℝ | 0≤t ∧ 9/80≤orbitCircuitDistance H (n+1-d) (v+t)} τ ∧
          orbitCircuitDistance H (n+1-d) (v+τ)=9/80 ∧ l*K≤τ^9*(d:ℝ)^10 ∧ τ^9*(d:ℝ)^10≤L*K := by
  obtain ⟨γ,hγ,Q,hQ,l,hl,L,hL,hw⟩ := gaussian_visit_crossing_scale
  refine ⟨γ,hγ,Q,hQ,l,hl,L,hL,?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro K H d s hd hs hγd hQd v
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2
  exact hn d s hd hs hγd hQd v hv (9/80) (by constructor <;> norm_num)

#print axioms gaussian_visit_crossing_scale
#print axioms gaussian_first_dip_crossing_scale
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
