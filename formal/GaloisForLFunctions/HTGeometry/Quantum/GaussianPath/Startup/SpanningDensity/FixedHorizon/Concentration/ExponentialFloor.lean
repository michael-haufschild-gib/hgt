import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.BondTails

/-! # Exponential exclusion of circuits separated by a dense physical cut -/
open MeasureTheory Set Filter GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Draws admitting a circuit with appreciable Choi overlap and a
gate-respecting partition cutting a fixed fraction of physical bonds. -/
def cutOverlapEvent (n : ℕ) (t η κ : ℝ) : Set PathPauliDisorder :=
  {ω | ∃ C : TwoQubitCircuit (n+2), ∃ c : Cut C, η*(n+1:ℕ) ≤ ((crossed c).card:ℝ) ∧
    κ ≤ ‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t))
      (choiVector C.eval.val)‖}

/-- Enough separated detectable bonds contradict the required overlap.
Thus a fitting dense cut entails many failed physical certificates. -/
theorem cut_overlap_subset_bad {n R m : ℕ} {γ r δ η κ t : ℝ} (hm : 0 < m)
    (hδr : δ < r) (hweak : 36*|t| *γ ≤ δ)
    (himp : ∀ v : ℝ, (m:ℝ)*(r-δ)*v ≤ 2*Real.sqrt m+m*δ → v<κ)
    (hconst : ((2*(2*R+2)*m+2*R:ℕ):ℝ) ≤ (η/4)*(n+1:ℕ)) :
    cutOverlapEvent n t η κ ⊆ {ω | (η/4)*(n+1:ℕ) ≤ ((badCenters n R γ r t ω).card:ℝ)} := by
  classical
  let p := η/4
  let N : ℝ := (n+1:ℕ)
  let L := 2*R+2
  change ((2*L*m+2*R:ℕ):ℝ) ≤ p*N at hconst
  rintro ω ⟨C,c',hcross,hfit⟩
  let F := badCenters n R γ r t ω
  let D := detectable c' (pathPauliDisorderShell ω n) t r
  by_contra h
  have hsmall : (F.card:ℝ)<p*N := lt_of_not_ge h
  have hmiss : missedBonds n R γ ω ⊆ F := fun e he => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,Or.inr (Or.inr (Or.inl (Finset.mem_filter.mp he).2))⟩
  have hcover : crossed c' ⊆ D∪F := by
    intro e he
    by_cases hh : r < |bondSignal e (pathPauliDisorderShell ω n) t|
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr
        (Or.inr (Or.inr (le_of_not_gt hh)))⟩)
  have hsum : ((crossed c').card:ℝ) ≤ (D.card:ℝ)+F.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le ..)
  change η*N ≤ ((crossed c').card:ℝ) at hcross
  have hh : ((2*L*m+2*R:ℕ):ℝ)+F.card ≤ D.card := by
    dsimp only [p] at hconst hsmall
    linarith only [hconst,hsmall,hcross,hsum]
  have hb : 2*L*m+2*R+F.card ≤ D.card := by exact_mod_cast hh
  have hmF := Finset.card_le_card hmiss
  have hcount : 2*(2*R+2)*m+(missedBonds n R γ ω).card+2*R≤D.card := by
    dsimp only [L] at hb
    omega
  exact hfit.not_gt (himp _ (crowded_cut_overlap hm R ω C c' hδr hweak hcount))

/-- Exponential decay at every prescribed positive date with constants
uniform over the interval, all cut orientations, and all gate counts. -/
theorem gaussian_cut_overlap_tail {a T η κ : ℝ} (ha : 0<a) (hη : 0<η) (hκ : 0<κ) :
    ∃ A>0, ∃ c>0, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T,
      pathPauliDisorderLaw.real (cutOverlapEvent n t η κ) ≤ A*Real.exp (-c*n) := by
  classical
  let p := η/4
  have hp : 0<p := div_pos hη (by norm_num)
  obtain ⟨r,hr,hgood⟩ := gaussian_bad_center_tail (T:=T) ha hp
  obtain ⟨δ,hδ,hδr,m,hm,himp⟩ := overlap_parameters hr hκ
  let γ := δ/(72*(|T|+1))
  have hγ : 0<γ := div_pos hδ (by positivity)
  have hscale : 72*(|T|+1)*γ=δ := by dsimp only [γ]; field_simp
  obtain ⟨R,_,hbad⟩ := hgood γ hγ (hscale.le.trans hδr.le)
  let L := 2*R+2
  have hL : 0<(L:ℝ) := by dsimp only [L]; positivity
  let c := 2*(p/8)^2/(L:ℝ)
  have hc : 0<c := by dsimp only [c]; positivity
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt ((2*L*m+2*R:ℕ)/p)
  refine ⟨L,hL,c,hc,?_⟩
  filter_upwards [hbad,eventually_ge_atTop n₀] with n hn hnn
  intro t ht
  let N : ℝ := (n+1:ℕ)
  have hconst : ((2*L*m+2*R:ℕ):ℝ)≤p*N := by
    rw [mul_comm p N]
    apply (div_le_iff₀ hp).mp
    change _≤((n+1:ℕ):ℝ)
    exact hn₀.le.trans (Nat.cast_le.mpr (by omega))
  have hweak : 36*|t| *γ≤δ := by
    rw [←hscale]
    apply mul_le_mul_of_nonneg_right _ hγ.le
    rw [abs_of_pos (ha.trans_le ht.1)]
    linarith only [le_abs_self T,ht.2,abs_nonneg T]
  have hsub := cut_overlap_subset_bad hm hδr hweak himp hconst
  apply ((measureReal_mono (μ:=pathPauliDisorderLaw) hsub (measure_ne_top _ _)).trans (hn t ht)).trans
  apply mul_le_mul_of_nonneg_left _ hL.le
  apply Real.exp_le_exp.mpr
  have hnat : n≤L*(n/L+1) := by
    have hquot := Nat.mod_add_div n L
    have hrem := Nat.mod_lt n (Nat.cast_pos.mp hL)
    rw [Nat.mul_succ]
    omega
  have hq : (n:ℝ)/(L:ℝ)≤((n/L+1:ℕ):ℝ) := (div_le_iff₀ hL).mpr (by
    rw [mul_comm]
    exact_mod_cast hnat)
  have hprod := mul_le_mul_of_nonneg_left hq (by positivity : 0≤2*(p/8)^2)
  change -2*(p/8)^2*((n/L+1:ℕ):ℝ) ≤ -(2*(p/8)^2/(L:ℝ))*n
  calc -2*(p/8)^2*((n/L+1:ℕ):ℝ) = -(2*(p/8)^2*((n/L+1:ℕ):ℝ)) := by ring
       _ ≤ -(2*(p/8)^2*((n:ℝ)/(L:ℝ))) := neg_le_neg hprod
       _ = -(2*(p/8)^2/(L:ℝ))*n := by ring

#print axioms gaussian_cut_overlap_tail
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
