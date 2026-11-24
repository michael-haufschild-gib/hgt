import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.EntryWindows.ArrivalCounts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.CutoffGap

/-! # Nearly every genuine scalar entry supports an exponential affordable interval -/

open Filter Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.EntryWindows
open SharpOccupation EmptyVisitFlux Depth
noncomputable section

private theorem bernoulli {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (j : ℕ) :
    1-(j:ℝ)*u ≤ (1-u)^j := by
  induction j with
  | zero => simp only [Nat.cast_zero,zero_mul,sub_zero,pow_zero,le_refl]
  | succ j ih =>
    rw [pow_succ,Nat.cast_succ]
    apply le_trans _ (mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hu.2))
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) j) (sq_nonneg u)]

private theorem inner_arc {ε x h : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2))
    (hx : x=physicalArc ε) (hh : 0 < h) (hs : h < x) :
    ∃ δ∈Ioc (0:ℝ) ε, δ+h ≤ ε ∧ physicalArc δ=x-h := by
  obtain ⟨hr,ht⟩ := physicalArc_spec he.1 he.2
  rw [←hx] at hr ht
  let y := x-h
  have hy : 0 < y := sub_pos.mpr hs
  have hyx : y ≤ x := sub_le_self _ hh.le
  have hy' : y∈Icc (0:ℝ) (1/2) := ⟨hy.le,hyx.trans hr.2.le⟩
  let δ := zeroGateArcTolerance y
  have hδ : 0 < δ := by
    rw [show (0:ℝ)=zeroGateArcTolerance 0 by simp [zeroGateArcTolerance]]
    exact strictMonoOn_zeroGateArcTolerance (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) (1/2)) hy' hy
  have hg := chord_gap hy.le hyx hr.2.le
  rw [ht] at hg
  have hdiff : δ+h ≤ ε := by dsimp only [δ,y] at *; linarith only [hg]
  have hδε := (le_add_of_nonneg_right hh.le : δ ≤ δ+h).trans hdiff
  obtain ⟨hu,hev⟩ := physicalArc_spec hδ (hδε.trans_lt he.2)
  exact ⟨δ,⟨hδ,hδε⟩,hdiff,strictMonoOn_zeroGateArcTolerance.injOn (Ioo_subset_Icc_self hu) hy' hev⟩

/-- For D=2ᴺ, among genuine scalar entries to the fixed-error tube, all
but a fraction bounded by 2D·2^(-floor(N/m)²)/x admit D^α gates
everywhere within D^γ/2 of the entry. Here x is the angular width.
The long observation may start at any nonnegative date. -/
theorem gaussian_scalar_entry_windows (γ α : ℝ) (hγ : 0 ≤ γ) (hγα : γ < α) (hα : α ≤ 1) :
    ∃ m > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let E := fun i => -H.2.isHermitian.eigenvalues i
      let R := (2:ℝ)^(γ*(N:ℝ))/2
      let s := ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
      ∀ ε∈Ioo (0:ℝ) (sqrt 2), let x := physicalArc ε
        ∀ a ≥ (0:ℝ), ∀ᶠ T : ℝ in atTop, let A := entriesAfter E x a T
          1-2*(D:ℝ)*(1/(2:ℝ)^((N/m)^2)/x) < ((covered H s ε R A).card:ℝ)/A.card := by
  obtain ⟨m,hm,hw⟩ := gaussian_entry_window_mass γ α hγ hγα hα
  refine ⟨m,hm,?_⟩
  filter_upwards [hw] with ω hh
  filter_upwards [hh] with k hk
  intro N D H E R s ε he x a ha
  let h := 1/(2:ℝ)^((N/m)^2)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hx : 0 < x := (physicalArc_spec he.1 he.2).1.1
  let u := h/x
  have hu : 0 < u := div_pos hh hx
  have hD : 1 ≤ (D:ℝ) := by exact_mod_cast (show 1 ≤ (2:ℕ)^N from Nat.two_pow_pos N)
  by_cases hs : h < x
  · obtain ⟨δ,hδ,hd,hy⟩ := inner_arc he rfl hh hs
    have hu' : u ≤ 1 := (div_le_one hx).mpr hs.le
    have heq : physicalArc δ/x=1-u := by rw [hy,sub_div,div_self hx.ne']
    have hpow := bernoulli ⟨hu.le,hu'⟩ (D-2)
    have hdim : ((D-2:ℕ):ℝ) ≤ D := by exact_mod_cast Nat.sub_le D 2
    have hb : 1-2*(D:ℝ)*u < (physicalArc δ/x)^(D-2) := by
      rw [heq]
      apply lt_of_lt_of_le _ hpow
      linarith only [mul_le_mul_of_nonneg_right hdim hu.le,mul_pos (zero_lt_one.trans_le hD) hu]
    exact hk ε he δ hδ hd a ha _ hb
  · have hu' : 1 ≤ u := (one_le_div hx).mpr (le_of_not_gt hs)
    have hp : 1 ≤ (D:ℝ)*u := one_le_mul_of_one_le_of_one_le hD hu'
    filter_upwards with T
    apply lt_of_lt_of_le _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    change 1-2*(D:ℝ)*u < 0
    linarith only [hp]

#print axioms gaussian_scalar_entry_windows
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.EntryWindows
