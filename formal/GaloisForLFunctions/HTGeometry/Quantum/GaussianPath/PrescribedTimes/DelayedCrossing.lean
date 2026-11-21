import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.MeasurableTest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.TypicalCrossing
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing

/-! # Return windows at prescribed delays from the actual first crossing -/
open Filter Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
open ReturnExcursions SharpOccupation
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private def delayedEvent (n P : ℕ) (d b : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | let σ := crossingOrigin n P (9/80) x
       ∃ t ∈ Icc (σ+d) (σ+d+b), pathGateDistance n P x t ≤ 1/10}

/-- Dilation moves the elapsed time after the crossing. The crossing itself
returns to the same point of the undilated orbit. -/
private theorem delayed_hit {n P : ℕ} {d b a : ℝ} (ha : 0 < a) (x : PrefixIndex n → ℝ)
    (h : a • x ∈ delayedEvent n P d b) :
    ∃ y ∈ Icc (a*d) (a*d+a*b),
      pathGateDistance n P x (crossingOrigin n P (9/80) x+y) ≤ 1/10 := by
  obtain ⟨t,ht,hd⟩ := (crossing_window_dilate n P P (9/80) (1/10) d b ha x).mp h
  let σ := crossingOrigin n P (9/80) x
  exact ⟨t-σ,⟨by dsimp [σ]; linarith only [ht.1],by dsimp [σ]; linarith only [ht.2]⟩,
    by change pathGateDistance n P x (σ+(t-σ)) ≤ 1/10; rwa [show σ+(t-σ)=t by ring]⟩

/-- Translating the observation origin preserves the exceptional length.
Spending a factor F of the packing multiplicity reduces the clock correction
from G to G/F at every interval length. -/
private theorem shifted_occupation {N P : ℕ} (H : selfAdjoint (Reg N)) (σ W G M F : ℝ)
    (hF : 1 ≤ F)
    (hocc : ∀ a T : ℝ, 0 ≤ T → (M*F)*volume.real
      (robustWindowHits H P W ∩ Icc a (a+T)) ≤ T+G)
    (a T : ℝ) (hT : 0 ≤ T) :
    M*volume.real ({u | ∃ y ∈ Icc u (u+W), orbitCircuitDistance H P (σ+y) ≤ 1/8}
      ∩ Icc a (a+T)) ≤ T+G/F := by
  let S := robustWindowHits H P W ∩ Icc (σ+a) (σ+a+T)
  have hm : MeasurableSet S := (isClosed_robustWindowHits H P W).measurableSet.inter measurableSet_Icc
  have he : {u | ∃ y ∈ Icc u (u+W), orbitCircuitDistance H P (σ+y) ≤ 1/8} ∩ Icc a (a+T) =
      (fun x : ℝ => σ+x) ⁻¹' S := by
    ext u
    constructor
    · rintro ⟨⟨y,hy,hd⟩,ht⟩
      exact ⟨⟨σ+y,⟨add_le_add_right hy.1 _,by linarith only [hy.2]⟩,hd⟩,
        ⟨by linarith only [ht.1],by linarith only [ht.2]⟩⟩
    · rintro ⟨⟨v,hv,hd⟩,ht⟩
      exact ⟨⟨v-σ,⟨by linarith only [hv.1],by linarith only [hv.2]⟩,by simpa only [add_sub_cancel] using hd⟩,
        ⟨by linarith only [ht.1],by linarith only [ht.2]⟩⟩
  rw [he,show volume.real ((fun x : ℝ => σ+x) ⁻¹' S) = volume.real S from
    congrArg ENNReal.toReal ((measurePreserving_add_left volume σ).measure_preimage hm.nullMeasurableSet)]
  have h := hocc (σ+a) T hT
  change M*F*volume.real S ≤ T+G at h
  have hpos := zero_lt_one.trans_le hF
  apply le_of_mul_le_mul_right _ hpos
  rw [add_mul,div_mul_cancel₀ _ hpos.ne']
  linarith only [h,le_mul_of_one_le_right hT hF]

/-- After any prescribed delay of at least 2G/2^⌊D/8⌋ from the first crossing
at budget P and distance 9/80, every budget through P has a further first
wait between 2^⌊D/4⌋ and G. This also excludes the entire delayed interval
as a possible date of the original first return. -/
theorem gaussian_first_crossing_delayed_wait :
    ∃ c : ℕ, ∀ d : ℕ → ℝ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let G := (2:ℝ)^(D^c)
      let L := max (d k) (2*G/(2:ℝ)^(D/8))
      let B := (2:ℝ)^(D/4)
      ∃ σ : ℝ, 0 < σ ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∀ s ≤ P, σ+L+B < firstCircuitVisit H s (σ+L) ∧ firstCircuitVisit H s (σ+L) ≤ σ+L+G) ∧
        ∀ v ∈ Icc (σ+L) (σ+L+B), ¬ HasProjectiveCircuitApproximation N (1/10:ℝ) P
          (unitaryEvolution H.val v) := by
  obtain ⟨c,hclock⟩ := gaussian_full_budget_robust_windows
  obtain ⟨_,hfirst⟩ := gaussian_hilbert_first_crossing
  refine ⟨c,fun d => ?_⟩
  let D (k : ℕ) := 2^(k+3)
  let G (k : ℕ) := (2:ℝ)^((D k)^c)
  let F (k : ℕ) := (2:ℝ)^(D k/8)
  let L (k : ℕ) := max (d k) (2*G k/F k)
  let B (k : ℕ) := (2:ℝ)^(D k/4)
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
  let q (k : ℕ) := ⌈L k⌉₊+1
  let E (k : ℕ) := delayedEvent (k+1) (P k) (L k) (B k)
  have htest := gaussian_path_eventually_outside_measurable_test E
    (fun k => measurable_shifted_window _ _ _ (measurable_crossingOrigin _ _ _) _ _) q
    (fun _ => Nat.succ_pos _)
  filter_upwards [htest,hclock,hfirst] with ω hω hc hf
  filter_upwards [hω,hc,hf,eventually_ge_atTop 64] with k htest hk hfirst hlarge
  intro N _ H _ _ _ _
  let x : PrefixIndex (k+1) → ℝ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have hgen : numberedGenerator (k+1) x = H.val := numberedGenerator_shell _
  have heq (t : ℝ) : pathGateDistance (k+1) (P k) x t = orbitCircuitDistance H (P k) t := by
    rw [pathGateDistance,hgen]
    rfl
  have hP : P k ≤ D k/(16*(N+1)) := by
    apply Nat.div_le_div_left <;> dsimp [P,D,nearHilbertContinuousCircuitBudget,N] <;> omega
  obtain ⟨σ,hpos,hcross,hprior,_⟩ := hfirst (P k) hP
  have hσ : crossingOrigin (k+1) (P k) (9/80) x = σ := crossingOrigin_eq_of_first hpos.le
    ((heq σ).trans hcross) (fun t ht => (heq t).trans_lt (hprior t ht))
  let M := (2:ℝ)^(D k/1024)
  let W := (2:ℝ)^(D k/4+2)
  let C := {y | orbitCircuitDistance H (P k) (σ+y) ≤ 1/8}
  have hD : 1024 ≤ D k := by
    change 2^10 ≤ 2^(k+3)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hprice : 16*(D k/4+2+(D k/1024+D k/8)) ≤ 7*D k := by omega
  have hOcc := hk.2 (D k/4+2) (D k/1024+D k/8) hprice
  have hF : 1 ≤ F k := one_le_pow₀ (by norm_num)
  have hG : 0 < G k := by dsimp [G]; positivity
  have hL : 0 < L k := (div_pos (mul_pos zero_lt_two hG) (zero_lt_one.trans_le hF)).trans_le (le_max_right ..)
  have hmiss : x ∉ E k := by
    intro hx
    apply htest
    refine ⟨hx,mem_iInter.mpr fun i => ?_⟩
    have hq : L k ≤ (q k:ℝ) := by
      change L k ≤ ((⌈L k⌉₊+1:ℕ):ℝ)
      rw [Nat.cast_add,Nat.cast_one]
      exact (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one)
    have hd : 2*(G k/F k) ≤ L k := by
      rw [←mul_div_assoc]
      exact le_max_right ..
    have hW : 2*B k+1 ≤ W := by
      have hb : 1 ≤ B k := one_le_pow₀ (by norm_num)
      change 2*B k+1 ≤ (2:ℝ)^(D k/4+2)
      rw [pow_add,show (2:ℝ)^2=4 by norm_num]
      change 2*B k+1 ≤ B k*4
      linarith only [hb]
    refine rayGrid_count_of_window_occupation i (E k) x C hL (by dsimp [B]; positivity) hq hd hW
      (show 0 ≤ M by dsimp [M]; positivity) ?_ ?_
    · intro a ha hh
      obtain ⟨y,hy,hd⟩ := delayed_hit ha x hh
      rw [hσ,heq] at hd
      exact ⟨y,hy,hd.trans (by norm_num)⟩
    · apply shifted_occupation H σ W (G k) M (F k) hF
      intro a T hT
      simpa only [M,F,←pow_add] using hOcc a T hT
  have hnone (v : ℝ) (hv : v ∈ Icc (σ+L k) (σ+L k+B k)) :
      ¬ HasProjectiveCircuitApproximation N (1/10:ℝ) (P k) (unitaryEvolution H.val v) := by
    intro hh
    apply hmiss
    exact ⟨v,hσ.symm ▸ hv,(heq v).trans_le ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hh)⟩
  refine ⟨σ,hpos,hcross,hprior,fun s hs => ⟨?_,?_⟩,hnone⟩
  · by_contra! h
    have hh : σ+L k ∈ {a | firstCircuitVisit H s a ≤ a+B k} := h
    rw [←circuitWindowHits_eq_firstVisit] at hh
    obtain ⟨v,hv,z,hz,Y,hY,he⟩ := hh
    exact hnone v hv ⟨z,hz,Y,hY.trans hs,he⟩
  · change σ+L k ∈ {a | firstCircuitVisit H s a ≤ a+G k}
    rw [←circuitWindowHits_eq_firstVisit]
    obtain ⟨v,hv,z,hz,Y,hY,he⟩ := hk.1 (σ+L k)
    exact ⟨v,hv,z,hz,Y,hY.trans (Nat.zero_le _),he⟩

#print axioms gaussian_first_crossing_delayed_wait
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
