import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.GateBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # Polynomial first departure dates above a full bond sweep -/

open MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
noncomputable section
private abbrev chain (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- Starting at any tenth-error visit, the first robust passage above one
sweep plus its initial gate count and excess q lies between a constant
times K⁻¹⁄² and the reciprocal date of order K⁻¹⁄²⁵⁶. The bounds hold
simultaneously for all such visits and 2s+q up to order K²⁵⁄³². -/
theorem gaussian_first_above_sweep :
    ∃ b>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      ∀ (v : ℝ) (s q : ℕ), ((2*s+q:ℕ):ℝ)≤b*(j:ℝ)^200 →
        HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution (chain ω n).val v) →
        ∀ ρ∈Icc (9/80:ℝ) (1/8),
          let τ := firstExcessAfter ω n (s+q) v ρ
          let f (u : ℝ) := orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+u)
          0≤τ ∧ τ≤1/(j:ℝ) ∧ L≤((n+2:ℕ):ℝ)*τ^2 ∧ f τ=ρ ∧ ∀ x∈Ico 0 τ, f x<ρ := by
  obtain ⟨b,hb,B,_,hwindow⟩ := gaussian_moving_gate_band
  obtain ⟨_,M,_,hM,hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨b,hb,1/(6720*M),by positivity,?_⟩
  filter_upwards [hwindow,hmass] with ω hw hm
  filter_upwards [hw,hm,eventually_ge_atTop (3:ℕ)] with n hn hnorm hlarge
  intro j v s q hq hv ρ hρ τ f
  obtain ⟨hs,hT,_,_,hband⟩ := hn
  let t := 1/(j:ℝ)
  have hj : (0:ℝ)<j := Nat.cast_pos.mpr (prefixIndex_bounds n hlarge).1
  have hscale : b*(j:ℝ)^208*t^8=b*(j:ℝ)^200 := by
    dsimp only [t]; field_simp [hj.ne']
  have hgap : ¬HasProjectiveCircuitApproximation (n+2) (1/10+ρ) (s+(n+1+(s+q)))
      (unitaryEvolution (chain ω n).val t) := by
    rintro ⟨z,hz,C,hC,he⟩
    have h := hband t ⟨le_rfl,hT⟩ (s+(n+1+(s+q))) ⟨z,hz,C,hC,he.trans (by linarith only [hρ.2])⟩
    rw [hscale] at h
    push_cast at h hq
    linarith only [h,hq]
  obtain ⟨ht₀,ht,hρ',hbefore⟩ := firstExcessAfter_le_of_increment ω n s q hs.le
    (show 1/10<ρ by linarith only [hρ.1]) hv hgap
  let u := pathPauliDisorderShell ω n
  let g := τ^2*(84*‖u‖^2)
  obtain ⟨z,hz,C,hC,herr⟩ := BondProducts.bond_sweep_error u τ ht₀ 1 one_pos
  have hinc : HasProjectiveCircuitApproximation (n+2) g (n+1)
      (unitaryEvolution (chain ω n).val τ) :=
    ⟨z,hz,C,by simpa only [one_mul] using hC.le,by simpa only [Nat.cast_one,div_one] using herr⟩
  obtain ⟨z',hz',D,hD,herr'⟩ := affordable_add_time (chain ω n) (x:=v) (y:=τ) hv hinc
  have hd : f τ≤1/10+g := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
    ⟨z',hz',D,hD.trans (by omega),herr'⟩
  change f τ=ρ at hρ'
  rw [hρ'] at hd
  have hquad := mul_le_mul_of_nonneg_left hnorm.2 (sq_nonneg τ)
  change τ^2*‖u‖^2≤_ at hquad
  refine ⟨ht₀,ht,(div_le_iff₀ (show 0<6720*M by positivity)).mpr ?_,hρ',hbefore⟩
  dsimp only [g] at hd
  linarith only [hρ.1,hd,hquad]

/-- At the first actual low return following the original near-Hilbert
crossing, the next robust passage above a full sweep takes between
order K⁻¹⁄² and order K⁻¹⁄²⁵⁶. Both constants are uniform through
excess budgets of order K²⁵⁄³². -/
theorem gaussian_polynomial_first_dip_rebound :
    ∃ a>(0:ℝ), ∃ L>(0:ℝ), ∃ M>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ s q : ℕ, ((2*s+q:ℕ):ℝ)^32≤a*K^25 →
        let v := firstLowAfterCrossing ω n s
        ∀ ρ∈Icc (9/80:ℝ) (1/8),
          let τ := firstExcessAfter ω n (s+q) v ρ
          let f (u : ℝ) := orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+u)
          0≤τ ∧ L≤K*τ^2 ∧ K*τ^256≤M ∧ f τ=ρ ∧ ∀ x∈Ico 0 τ, f x<ρ := by
  obtain ⟨b,hb,L,hL,hcross⟩ := gaussian_first_above_sweep
  let M : ℝ := 4*2^256
  have hM : 0<M := by dsimp only [M]; positivity
  refine ⟨b^32/M^25,div_pos (pow_pos hb _) (pow_pos hM _),L,hL,M,hM,?_⟩
  filter_upwards [hcross] with ω hw
  filter_upwards [hw,eventually_ge_atTop (3:ℕ)] with n hn hlarge
  intro K s q hbudget v ρ hρ τ f
  let j := prefixIndex n
  obtain ⟨hj,_,hu⟩ := prefixIndex_bounds n hlarge
  have hj' : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hK : 0≤K := Nat.cast_nonneg _
  have hsize : K≤M*(j:ℝ)^256 := (real_prefix_size n hlarge).2
  have hpay : ((2*s+q:ℕ):ℝ)≤b*(j:ℝ)^200 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK hsize 25)
      (div_nonneg (pow_nonneg hb.le 32) (pow_nonneg hM.le 25))
    have he : (b^32/M^25)*(M*(j:ℝ)^256)^25=(b*(j:ℝ)^200)^32 := by
      rw [mul_pow M,←mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ hM.ne'),mul_pow b,←pow_mul,←pow_mul]
    by_contra! hl
    exact ((hbudget.trans h).trans_eq he).not_gt
      (pow_lt_pow_left₀ hl (mul_nonneg hb.le (pow_nonneg hj'.le _)) (by decide : 32≠0))
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s
      (unitaryEvolution (chain ω n).val v) :=
    (PrecisionReturns.firstVisit_isLeast (chain ω n) _ s (by norm_num : (0:ℝ)<1/10)).1.2
  obtain ⟨ht,ht',hl,he,hpre⟩ := hn v s q hpay hv ρ hρ
  have hpow := pow_le_pow_left₀ ht ht' 256
  change τ^256≤(1/(j:ℝ))^256 at hpow
  rw [div_pow,one_pow,le_div_iff₀ (pow_pos hj' _)] at hpow
  refine ⟨ht,hl,?_,he,hpre⟩
  calc K*τ^256 ≤ (M*(j:ℝ)^256)*τ^256 := mul_le_mul_of_nonneg_right hsize (pow_nonneg ht _)
       _ = M*(τ^256*(j:ℝ)^256) := by ring
       _ ≤ M := (mul_le_mul_of_nonneg_left hpow hM.le).trans_eq (mul_one M)

#print axioms gaussian_polynomial_first_dip_rebound
#print axioms gaussian_first_above_sweep
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
