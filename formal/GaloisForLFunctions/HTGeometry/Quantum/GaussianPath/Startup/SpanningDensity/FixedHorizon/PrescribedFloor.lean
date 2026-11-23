import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CrowdedCut

/-! # Vanishing trace overlap below one gate per bond at prescribed dates -/
open MeasureTheory Set Filter GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- At a prescribed positive date, an appreciable normalized overlap
forces every gate-respecting cut to cross a vanishing fraction of the
physical bonds, even with unrestricted gate count. -/
theorem gaussian_prescribed_cut_overlap {a T η κ β : ℝ} (ha : 0<a) (hη : 0<η) (hκ : 0<κ) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, pathPauliDisorderLaw.real
      {ω | ∃ C : TwoQubitCircuit (n+2), ∃ c : Cut C, η*(n+1:ℕ) ≤ ((crossed c).card:ℝ) ∧
        κ ≤ ‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t))
          (choiVector C.eval.val)‖} ≤ β := by
  classical
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by unfold μ pathPauliDisorderLaw; infer_instance
  obtain ⟨r,hr,hd⟩ := gaussian_all_cut_detection (T:=T) ha (half_pos hη) (half_pos hβ)
  obtain ⟨δ,hδ,hδr,m,hm,hsep⟩ := overlap_parameters hr hκ
  let γ := δ/(36*(|T|+1))
  have hγ : 0<γ := div_pos hδ (by positivity)
  let q := η/8
  have hq : 0<q := div_pos hη (by norm_num)
  obtain ⟨R,_,hmiss⟩ := gaussian_seam_density hγ hq (half_pos hβ)
  let L := 2*(2*R+2)*m+2*R
  obtain ⟨n₀,h₀⟩ := exists_nat_gt ((L:ℝ)/q)
  filter_upwards [eventually_ge_atTop n₀] with n hn
  let N : ℝ := (n+1:ℕ)
  have hN : (L:ℝ) ≤ q*N := by
    rw [mul_comm]
    apply (div_le_iff₀ hq).mp
    apply h₀.le.trans
    change (n₀:ℝ) ≤ ((n+1:ℕ):ℝ)
    exact_mod_cast (show n₀≤n+1 by omega)
  intro t ht
  let D (C : TwoQubitCircuit (n+2)) (c : Cut C) (ω : PathPauliDisorder) :=
    detectable c (pathPauliDisorderShell ω n) t r
  let B := {ω : PathPauliDisorder | ∃ C : TwoQubitCircuit (n+2), ∃ c : Cut C,
    ((D C c ω).card:ℝ)+(η/2)*N<(crossed c).card}
  let A := {ω : PathPauliDisorder | q*N ≤ ((missedBonds n R γ ω).card:ℝ)}
  have hA : μ.real A ≤ β/2 := hmiss n
  have hB : μ.real B ≤ β/2 := hd n t ht
  apply (measureReal_mono (μ:=μ) (s₂:=A∪B) ?_ (measure_ne_top _ _)).trans
    ((measureReal_union_le A B).trans ((add_le_add hA hB).trans_eq (add_halves β)))
  rintro ω ⟨C,c,hcross,hfit⟩
  by_contra h
  have hsmall : ((missedBonds n R γ ω).card:ℝ)<q*N :=
    lt_of_not_ge (fun hb => h (Or.inl hb))
  have hc : ((crossed c).card:ℝ) ≤ ((D C c ω).card:ℝ)+(η/2)*N :=
    le_of_not_gt fun he => h (Or.inr ⟨C,c,he⟩)
  have hs : (L:ℝ)+((missedBonds n R γ ω).card:ℝ) ≤ ((D C c ω).card:ℝ) := by
    change η*N ≤ ((crossed c).card:ℝ) at hcross
    dsimp only [q] at hN hsmall
    linarith only [hcross,hc,hsmall,hN]
  have hcount : 2*(2*R+2)*m+(missedBonds n R γ ω).card+2*R ≤ (D C c ω).card := by
    have hh : L+(missedBonds n R γ ω).card ≤ (D C c ω).card := by exact_mod_cast hs
    dsimp only [L] at hh
    omega
  have hweak : 36*|t| *γ ≤ δ := by
    have htime : |t|≤|T|+1 := by
      rw [abs_of_pos (ha.trans_le ht.1)]
      linarith only [ht.2,le_abs_self T]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime (by norm_num : (0:ℝ)≤36)) hγ.le
    apply hh.trans_eq
    dsimp only [γ]
    field_simp [show 36*(|T|+1)≠0 by positivity]
  exact hfit.not_gt (hsep _ (crowded_cut_overlap hm R ω C c hδr hweak hcount))

/-- Every circuit below one gate per bond by a fixed fraction has
vanishing normalized overlap in probability, uniformly in the
prescribed positive observation date. -/
theorem gaussian_prescribed_overlap {a T η κ β : ℝ} (ha : 0<a) (hη : 0<η) (hκ : 0<κ) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, pathPauliDisorderLaw.real
      {ω | ∃ C : TwoQubitCircuit (n+2), (C.gateCount:ℝ) ≤ (1-η)*(n+1:ℕ) ∧
        κ ≤ ‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t))
          (choiVector C.eval.val)‖} ≤ β := by
  filter_upwards [gaussian_prescribed_cut_overlap (T:=T) ha (half_pos hη) hκ hβ] with n hn
  intro t ht
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans (hn t ht)
  rintro ω ⟨C,hC,hfit⟩
  obtain ⟨c,hc⟩ := many_crossed C
  refine ⟨C,c,?_,hfit⟩
  have hb : ((n+1:ℕ):ℝ) ≤ (C.gateCount:ℝ)+2*((crossed c).card:ℝ) := by exact_mod_cast hc
  linarith only [hb,hC]

#print axioms gaussian_prescribed_cut_overlap
#print axioms gaussian_prescribed_overlap
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
