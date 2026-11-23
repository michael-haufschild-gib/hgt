import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.DisjointWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.WindowFailures
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Simultaneous failure counts for shifted blocks of Gaussian rows -/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private theorem shifted_windows {L M : ℕ} [NeZero L] (d : ℕ) :
    MeasurePreserving (fun ω (j : Fin M) => readWindow (d+j.val*L) L ω)
      pathPauliDisorderLaw (Measure.infinitePi fun _ : Fin M => windowLaw L) := by
  let g (p : Fin M × (Fin L × PathPauliDirections)) :=
    (d+p.1.val*L+p.2.1.val,p.2.2)
  have hg : Function.Injective g := by
    rintro ⟨i,k,v⟩ ⟨j,l,w⟩ h
    obtain ⟨hrow,hd⟩ := Prod.mk.inj h
    change d+i.val*L+k.val=d+j.val*L+l.val at hrow
    have h : (Nat.divModEquiv L).symm (i.val,k)=(Nat.divModEquiv L).symm (j.val,l) := by
      change i.val*L+k.val=j.val*L+l.val
      omega
    obtain ⟨hi,hk⟩ := Prod.mk.inj ((Nat.divModEquiv L).symm.injective h)
    exact Prod.ext (Fin.ext hi) (Prod.ext hk hd)
  exact disjoint_window_law (gaussianReal 0 1) g hg

/-- A window meets the chain at a different location in each test. Only
within one residue class must its coefficient rows be disjoint. -/
theorem gaussian_window_colors {L M : ℕ} [NeZero L] [NeZero M]
    (S : Fin L → Fin M → Set (WindowRows L)) (hs : ∀ d j, MeasurableSet (S d j))
    {p η : ℝ} (hp : ∀ d j, (windowLaw L).real (S d j)≤p) (hη : 0≤η) :
    pathPauliDisorderLaw.real {ω | ∃ d : Fin L, (p+η)*M ≤
      ((Finset.univ.filter fun j : Fin M => readWindow (d.val+j.val*L) L ω∈S d j).card:ℝ)}
      ≤ L*Real.exp (-2*η^2*M) := by
  classical
  let A (d : Fin L) := {x : Fin M → WindowRows L | (p+η)*M ≤
    ((Finset.univ.filter fun j => x j∈S d j).card:ℝ)}
  have hA (d) : MeasurableSet (A d) := by
    let X (j : Fin M) (x : Fin M → WindowRows L) := (S d j).indicator (fun _ => (1:ℝ)) (x j)
    have hcount (x) : ∑ j, X j x=((Finset.univ.filter fun j => x j∈S d j).card:ℝ) := by
      simpa only [X,Set.indicator_apply] using
        (Finset.sum_boole (R:=ℝ) (fun j => x j∈S d j) Finset.univ)
    change MeasurableSet {x | (p+η)*M ≤ _}
    simp only [←hcount]
    exact measurableSet_le measurable_const (Finset.measurable_sum _ fun j _ =>
      (measurable_const.indicator (hs d j)).comp (measurable_pi_apply j))
  let B (d : Fin L) := (fun ω (j : Fin M) => readWindow (d.val+j.val*L) L ω) ⁻¹' A d
  have hb (d) : pathPauliDisorderLaw.real (B d) ≤ Real.exp (-2*η^2*M) := by
    rw [show pathPauliDisorderLaw.real (B d)=
      (Measure.infinitePi fun _ : Fin M => windowLaw L).real (A d) from
      (shifted_windows (M:=M) (L:=L) d.val).measureReal_preimage (hA d).nullMeasurableSet]
    simpa only [A,Fintype.card_fin] using independent_window_failures (windowLaw L) (S d) (hs d) (hp d) hη
  have he : {ω | ∃ d : Fin L, (p+η)*M ≤ ((Finset.univ.filter fun j : Fin M =>
      readWindow (d.val+j.val*L) L ω∈S d j).card:ℝ)}=⋃ d, B d := setOf_exists _
  rw [he]
  apply (measureReal_iUnion_fintype_le B).trans
  exact (Finset.sum_le_sum fun d _ => hb d).trans_eq (by simp [nsmul_eq_mul])

#print axioms gaussian_window_colors

private theorem count_by_colors {L n : ℕ} (hL : 0<L) (P : ℕ → Prop) :
    ((Finset.range (n+1)).filter P).card ≤ ∑ d : Fin L,
      (Finset.univ.filter (fun j : Fin (n/L+1) => P (d.val+j.val*L))).card := by
  classical
  let B (d : Fin L) := Finset.univ.filter (fun j : Fin (n/L+1) => P (d.val+j.val*L))
  let F (d : Fin L) := (B d).image (fun j => d.val+j.val*L)
  have hsub : (Finset.range (n+1)).filter P ⊆ Finset.univ.biUnion F := by
    intro s hs
    obtain ⟨hs,hp⟩ := Finset.mem_filter.mp hs
    let d : Fin L := ⟨s%L,Nat.mod_lt _ hL⟩
    let j : Fin (n/L+1) := ⟨s/L,Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs)))⟩
    have he : d.val+j.val*L=s := by simpa only [d,j,Nat.mul_comm (s/L) L] using Nat.mod_add_div s L
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm ▸ hp⟩,he⟩⟩
  exact ((Finset.card_le_card hsub).trans (Finset.card_biUnion_le (s:=Finset.univ) (t:=F))).trans
    (Finset.sum_le_sum fun d _ => Finset.card_image_le)

/-- A common marginal failure bound yields exponentially few exceptional
prefixes even when every starting position uses a different test. -/
theorem gaussian_overlapping_windows {L : ℕ} [NeZero L] (n : ℕ)
    (S : ℕ → Set (WindowRows L)) (hs : ∀ d, MeasurableSet (S d))
    {p η : ℝ} (hp : ∀ d, (windowLaw L).real (S d)≤p) (hη : 0≤η) :
    let M := n/L+1
    pathPauliDisorderLaw.real {ω | L*((p+η)*M) ≤
      (((Finset.range (n+1)).filter fun s => readWindow s L ω∈S s).card:ℝ)}
      ≤ L*Real.exp (-2*η^2*M) := by
  classical
  intro M
  let A (d : Fin L) (j : Fin M) := S (d.val+j.val*L)
  letI : NeZero M := ⟨Nat.succ_ne_zero _⟩
  have hb := gaussian_window_colors A (fun _ _ => hs _) (fun _ _ => hp _) hη
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans hb
  intro ω hω
  by_contra h
  let P (s : ℕ) := readWindow s L ω∈S s
  let count (d : Fin L) := (Finset.univ.filter fun j : Fin M => P (d.val+j.val*L)).card
  have hall (d : Fin L) : (count d:ℝ)<(p+η)*M := lt_of_not_ge fun hi => h ⟨d,hi⟩
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun d _ => hall d)
  have hcount : (((Finset.range (n+1)).filter P).card:ℝ) ≤ ∑ d, (count d:ℝ) := by
    exact_mod_cast count_by_colors (n:=n) (NeZero.pos L) P
  change L*((p+η)*M) ≤ (((Finset.range (n+1)).filter P).card:ℝ) at hω
  have hlt := lt_of_le_of_lt (hω.trans hcount) hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,lt_self_iff_false] at hlt

#print axioms gaussian_overlapping_windows
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
