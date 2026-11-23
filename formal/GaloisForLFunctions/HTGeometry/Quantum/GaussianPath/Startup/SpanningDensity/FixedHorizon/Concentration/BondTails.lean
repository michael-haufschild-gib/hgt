import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.ColorTails
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CrowdedCut

/-! # Exponential concentration of failed physical bond certificates -/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Positions without a usable full-chain test, including the boundary
layer and both possible failures of an interior certificate. -/
def badCenters (n R : ℕ) (γ r t : ℝ) (ω : PathPauliDisorder) :=
  Finset.univ.filter (fun e : Fin (n+1) => e.val<R ∨ n<e.val+R ∨ ω∈failedStrips γ R e.val ∨
    |bondSignal e (pathPauliDisorderShell ω n) t|≤r)

private def startFailure (n R : ℕ) (γ r t : ℝ) (s : ℕ) : Set (WindowRows (2*R+2)) :=
  if h : s+R+R≤n then windowFailure (n:=n) ⟨s+R,by omega⟩ R γ r t else ∅

private theorem bad_count (n R : ℕ) (γ r t : ℝ) (ω : PathPauliDisorder)
    (herr : 72*|t| *γ≤r) :
    (badCenters n R γ r t ω).card ≤ 2*R+
      ((Finset.range (n+1)).filter fun s => readWindow s (2*R+2) ω∈startFailure n R γ r t s).card := by
  let B := Finset.univ.filter fun e : Fin (n+1) => e.val<R ∨ n<e.val+R
  let F := badCenters n R γ r t ω
  let A := (Finset.range (n+1)).filter fun s => readWindow s (2*R+2) ω∈startFailure n R γ r t s
  have hi : (F \ B).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn fun e : Fin (n+1) => e.val-R
    · intro e he
      obtain ⟨hf,hb⟩ := Finset.mem_sdiff.mp he
      have hbound : ¬(e.val<R ∨ n<e.val+R) := fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have hl : R≤e.val := by omega
      have hr : e.val+R≤n := by omega
      obtain h|h|h := (Finset.mem_filter.mp hf).2
      · exact (hbound (Or.inl h)).elim
      · exact (hbound (Or.inr h)).elim
      · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Nat.sub_le e.val R).trans_lt e.isLt),?_⟩
        simp only [startFailure,dif_pos (show e.val-R+R+R≤n by omega)]
        have heq : (⟨e.val-R+R,by omega⟩ : Fin (n+1))=e := Fin.ext (Nat.sub_add_cancel hl)
        rw [heq]
        by_contra hp
        have hu := signal_of_passing_window ω e hl hr herr hp
        exact h.elim hu.1 hu.2.not_ge
    · intro e he j hj h
      have lower {i : Fin (n+1)} (hi : i∈F \ B) : R ≤ i.val := le_of_not_gt fun h =>
        (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl h⟩)
      change e.val-R=j.val-R at h
      exact Fin.ext (by have := lower he; have := lower hj; omega)
  have hsub : F ⊆ B∪(F \ B) := by
    intro e he
    by_cases h : e∈B
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  exact ((Finset.card_le_card hsub).trans (Finset.card_union_le ..)).trans (Nat.add_le_add (boundary_count ..) hi)

/-- A guard failure and a small full-chain signal have local certificates.
Coloring equal-length windows gives concentration whenever the boundary
layer fits inside the allowed fraction of bad centers. -/
theorem bad_center_bound {n R : ℕ} {p γ r t : ℝ} (hp : 0 < p)
    (hweak : 72*|t| *γ ≤ r)
    (hguard : ∀ s : ℕ, pathPauliDisorderLaw.real (absentStrip γ R s) ≤ p/8)
    (full : ∀ e : Fin (n+1), pathPauliDisorderLaw.real
      {ω | |bondSignal e (pathPauliDisorderShell ω n) t| ≤ 3*r} ≤ p/8)
    (hnreal : 2*(R:ℝ)+(4*(p/8))*((2*R+2:ℕ):ℝ) ≤ (n:ℝ)*(4*(p/8))) :
    pathPauliDisorderLaw.real {ω | p*(n+1:ℕ) ≤ ((badCenters n R γ r t ω).card:ℝ)}
      ≤ (2*R+2:ℕ)*Real.exp (-2*(p/8)^2*(n/(2*R+2)+1:ℕ)) := by
  classical
  let q := p/8
  have hq : 0 < q := div_pos hp (by norm_num)
  let L := 2*R+2
  letI : NeZero L := ⟨by dsimp only [L]; omega⟩
  let M := n/L+1
  have hcapacity : L*(M:ℝ) ≤ (n:ℝ)+L := by
    have hh := Nat.div_mul_le_self n L
    have hnat : L*M ≤ n+L := by
      dsimp only [M]
      rw [Nat.mul_succ,Nat.mul_comm L (n/L)]
      omega
    exact_mod_cast hnat
  let S := startFailure n R γ r t
  have hs (s) : MeasurableSet (S s) := by
    dsimp only [S,startFailure]
    split
    · exact measurable_windowFailure ..
    · exact MeasurableSet.empty
  have hprob (s) : (windowLaw L).real (S s)≤3*q := by
    dsimp only [S,startFailure]
    split
    next he =>
      let e : Fin (n+1) := ⟨s+R,by omega⟩
      exact (window_failure_probability e (by dsimp only [e]; omega) he hweak hguard (full e)).trans_eq (by ring)
    next => simpa only [measureReal_empty] using (mul_nonneg (by norm_num : (0:ℝ)≤3) hq.le)
  have hbound := gaussian_overlapping_windows (L:=L) n S hs hprob hq.le
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans hbound
  intro ω hω
  let K := ((Finset.range (n+1)).filter fun s => readWindow s L ω∈S s).card
  have hk : ((badCenters n R γ r t ω).card:ℝ)≤2*(R:ℝ)+K := by
    have h := bad_count n R γ r t ω hweak
    change (badCenters n R γ r t ω).card≤2*R+K at h
    exact_mod_cast h
  change p*(n+1:ℕ)≤((badCenters n R γ r t ω).card:ℝ) at hω
  change (L:ℝ)*((3*q+q)*M) ≤ K
  have hc := mul_le_mul_of_nonneg_left hcapacity (by positivity : 0≤4*q)
  rw [Nat.cast_succ] at hω
  have hscale : p=8*q := by dsimp only [q]; ring
  rw [hscale] at hω
  change 2*(R:ℝ)+(4*q)*(L:ℝ) ≤ (n:ℝ)*(4*q) at hnreal
  linarith only [hc,hk,hω,hnreal,hq]

/-- The failure fraction of full-chain physical tests has an exponential
tail. The radius is chosen after the threshold for weak edges, and stays
fixed while the prefix size grows. -/
theorem gaussian_bad_center_tail {a T p : ℝ} (ha : 0<a) (hp : 0<p) :
    ∃ r>0, ∀ γ>0, 72*(|T|+1)*γ≤r → ∃ R : ℕ, 0<R ∧
      ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T,
        pathPauliDisorderLaw.real {ω | p*(n+1:ℕ)≤((badCenters n R γ r t ω).card:ℝ)}
        ≤ (2*R+2:ℕ)*Real.exp (-2*(p/8)^2*(n/(2*R+2)+1:ℕ)) := by
  classical
  let q := p/8
  have hq : 0<q := div_pos hp (by norm_num)
  obtain ⟨r₀,hr₀,hsmall⟩ := gaussian_bond_signal_probability (T:=T) ha hq
  let r := r₀/3
  have hr : 0<r := div_pos hr₀ (by norm_num)
  refine ⟨r,hr,?_⟩
  intro γ hγ hmargin
  obtain ⟨z,hz,hstrip⟩ := gaussian_weak_strip hγ
  obtain ⟨R,hR,htail⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hz.1 hz.2).eventually_lt_const hq)).exists
  let L := 2*R+2
  have hguard (s : ℕ) : pathPauliDisorderLaw.real (absentStrip γ R s)≤q :=
    (hstrip R (fun i => s+i.val) (fun _ _ he => Fin.ext (Nat.add_left_cancel he))).le.trans htail.le
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt ((2*(R:ℝ)+(4*q)*(L:ℝ))/(4*q))
  refine ⟨R,hR,?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro t ht
  have hnreal : (2*(R:ℝ)+(4*q)*L) ≤ (n:ℝ)*(4*q) := by
    apply (div_le_iff₀ (by positivity : 0<4*q)).mp
    exact hn₀.le.trans (Nat.cast_le.mpr hn)
  have hweak : 72*|t| *γ≤r := by
    apply le_trans _ hmargin
    have htime : |t|≤|T|+1 := by
      rw [abs_of_pos (ha.trans_le ht.1)]
      linarith only [ht.2,le_abs_self T]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime (by norm_num)) hγ.le
  apply bad_center_bound hp hweak hguard _ hnreal
  intro e
  rw [show 3*r=r₀ by dsimp only [r]; ring]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsmall n e t ht)).trans_eq (ENNReal.toReal_ofReal hq.le)

#print axioms gaussian_bad_center_tail
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
