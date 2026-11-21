import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.FullBudgetWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Passage

/-! # Elapsed time inside long gaps between consecutive low-cost visits -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The entire observation window is robustly hard. At every lower budget,
the window follows the first robust crossing of its own return gap. -/
def IsExcursionWindow {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ) (u W G : ℝ) : Prop :=
  (∀ t ∈ Icc u (u+W), 1/8 < orbitCircuitDistance H P t) ∧
    ∀ s ≤ P, InReturnExcursion H P s u W G

private theorem bad_windows_eq {n P : ℕ} (H : selfAdjoint (Reg n)) {W G : ℝ} (hW : 0 ≤ W)
    (hvisit : ∀ a : ℝ, ∃ t ∈ Icc a (a+G),
      HasProjectiveCircuitApproximation n (1/10:ℝ) 0 (unitaryEvolution H.val t)) :
    {u | ¬ IsExcursionWindow H P u W G} = robustWindowHits H P W := by
  ext u
  constructor
  · intro hbad
    by_contra hmiss
    have hw : ∀ t ∈ Icc u (u+W), 1/8 < orbitCircuitDistance H P t :=
      fun t ht => lt_of_not_ge fun hd => hmiss ⟨t,ht,hd⟩
    exact hbad ⟨hw,fun _ hs => excursion_of_hard_window H hs hW hvisit hw⟩
  · rintro ⟨t,ht,hd⟩ hw
    exact (hw.1 t ht).not_ge hd

/-- Compactness of the offset interval makes the event of a robust hit closed. -/
theorem isClosed_robustWindowHits {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ) (W : ℝ) :
    IsClosed (robustWindowHits H P W) := by
  let K := Icc (0:ℝ) W
  letI : CompactSpace ↥K := inferInstanceAs (CompactSpace (Icc (0:ℝ) W))
  let Z := {p : ℝ × ↥K | orbitCircuitDistance H P (p.1+p.2.val) ≤ 1/8}
  have hZ : IsClosed Z := isClosed_le ((orbitCircuitDistance_lipschitz H P).continuous.comp
    (continuous_fst.add (continuous_subtype_val.comp continuous_snd))) continuous_const
  have heq : robustWindowHits H P W = Prod.fst '' Z := by
    ext u
    constructor
    · rintro ⟨t,ht,hd⟩
      have hd' : t-u ∈ K := ⟨sub_nonneg.mpr ht.1,by linarith only [ht.2]⟩
      refine ⟨(u,⟨t-u,hd'⟩),?_,rfl⟩
      change orbitCircuitDistance H P (u+(t-u)) ≤ 1/8
      rwa [show u+(t-u)=t by ring]
    · rintro ⟨⟨v,τ⟩,hz,rfl⟩
      exact ⟨v+τ.val,⟨le_add_of_nonneg_right τ.2.1,add_le_add le_rfl τ.2.2⟩,hz⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hZ

/-- An interval longer than the exceptional-set allowance contains a
whole hard-window start even when its left endpoint is prescribed. -/
private theorem exists_good_origin {f : ℝ → Prop} {a T G M : ℝ} (hT : 0 ≤ T)
    (h : M*volume.real ({u | ¬ f u} ∩ Icc a (a+T)) ≤ T+G) (hsmall : T+G < M*T) :
    ∃ u ∈ Icc a (a+T), f u := by
  by_contra hnone
  have hfull : {u | ¬ f u} ∩ Icc a (a+T) = Icc a (a+T) :=
    Set.inter_eq_right.mpr (fun u hu hgood => hnone ⟨u,hu,hgood⟩)
  rw [hfull,Real.volume_real_Icc_of_le (le_add_of_nonneg_right hT),
    show a+T-a=T by ring] at h
  exact hsmall.not_ge h

/-- Outside an exceptional set of explicitly bounded length, observations
lie in long return gaps for each budget up to the full threshold.
Every interval of length 3G contains such excursions in their entirety. -/
theorem gaussian_first_crossing_excursion_occupation :
    ∃ q : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let G := (2:ℝ)^(D^q)
      let P := nearHilbertContinuousCircuitBudget N
      (∀ b e : ℕ, 16*(b+e) ≤ 7*D → ∀ a T : ℝ, 0 ≤ T →
        (2:ℝ)^e * volume.real ({u | ¬ IsExcursionWindow H P u ((2:ℝ)^b) G} ∩
          Icc a (a+T)) ≤ T+G) ∧
      (∀ b e : ℕ, 16*(b+e) ≤ 7*D → ∀ a T : ℝ, 0 ≤ T → T+G < (2:ℝ)^e*T →
        ∃ u ∈ Icc a (a+T), IsExcursionWindow H P u ((2:ℝ)^b) G) ∧
      ∀ a : ℝ, ∃ u ∈ Icc (a+G) (a+2*G), IsExcursionWindow H P u ((2:ℝ)^(D/4)) G := by
  obtain ⟨q,hq⟩ := gaussian_full_budget_robust_windows
  refine ⟨q,?_⟩
  filter_upwards [hq] with ω hω
  filter_upwards [hω,eventually_ge_atTop 4] with k hh hk
  intro N D x H G P
  obtain ⟨hvisit,hocc⟩ := hh
  have hG : 0 < G := by dsimp [G]; positivity
  have bound (b e : ℕ) (hbe : 16*(b+e) ≤ 7*D) (a T : ℝ) (hT : 0 ≤ T) :
      (2:ℝ)^e * volume.real ({u | ¬ IsExcursionWindow H P u ((2:ℝ)^b) G} ∩
          Icc a (a+T)) ≤ T+G := by
    rw [bad_windows_eq H (by positivity) hvisit]
    exact hocc b e hbe a T hT
  refine ⟨bound,fun b e hbe a T hT => exists_good_origin hT (bound b e hbe a T hT),?_⟩
  intro a
  have hD : 16 ≤ D := by
    dsimp [D,N]
    exact (show 16 = (2:ℕ)^4 by decide).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  let e := 3*D/16
  have hc : 16*(D/4+e) ≤ 7*D := by dsimp [e]; omega
  have htwo : (2:ℝ)^2 ≤ (2:ℝ)^e := pow_le_pow_right₀ (by norm_num) (by dsimp [e]; omega)
  have h := bound (D/4) e hc (a+G) G hG.le
  obtain ⟨u,hu,hw⟩ := exists_good_origin hG.le h
    (by nlinarith only [mul_le_mul_of_nonneg_right htwo hG.le,hG])
  exact ⟨u,⟨hu.1,by linarith only [hu.2]⟩,hw⟩

#print axioms gaussian_first_crossing_excursion_occupation
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
