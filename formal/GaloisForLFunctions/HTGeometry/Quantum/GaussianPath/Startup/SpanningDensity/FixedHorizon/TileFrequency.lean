import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondProbability
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Almost sure bond detection in disjoint physical blocks -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

abbrev Tile (L : ℕ) := (Fin L × PathPauliDirections) → ℝ

/-- Rows beginning at site kL, including the coefficients at its last site. -/
def tileRows {L : ℕ} (ω : PathPauliDisorder) (k : ℕ) : Tile L :=
  fun i => ω (k*L+i.1.val,i.2)

private def tileLaw (L : ℕ) : Measure (Tile L) := Measure.infinitePi fun _ => gaussianReal 0 1
private instance (L : ℕ) : IsProbabilityMeasure (tileLaw L) := by unfold tileLaw; infer_instance

private theorem tile_preserving (L : ℕ) [NeZero L] :
    MeasurePreserving (tileRows (L:=L)) pathPauliDisorderLaw (Measure.infinitePi fun _ : ℕ => tileLaw L) := by
  let F (p : ℕ × (Fin L × PathPauliDirections)) := ((Nat.divModEquiv L).symm (p.1,p.2.1),p.2.2)
  have hf : Function.Injective F := by
    rintro ⟨k,i,d⟩ ⟨j,l,e⟩ h
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
    obtain ⟨hk,hi⟩ := Prod.mk.inj ((Nat.divModEquiv L).symm.injective h₁)
    exact Prod.ext hk (Prod.ext hi h₂)
  let ν : Measure ((ℕ × (Fin L × PathPauliDirections)) → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
  have hR : MeasurePreserving (fun ω p => ω (F p)) pathPauliDisorderLaw ν :=
    ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _),Measure.map_infinitePi_infinitePi_of_inj hf⟩
  have hC : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin L × PathPauliDirections) ℝ) ν
      (Measure.infinitePi fun _ : ℕ => tileLaw L) :=
    ⟨(MeasurableEquiv.curry ..).measurable,Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)⟩
  exact hC.comp hR

private theorem tile_average {L : ℕ} [NeZero L] (f : Tile L → ℝ) (hf : Measurable f)
    (hi : Integrable f (tileLaw L)) : ∀ᵐ ω ∂pathPauliDisorderLaw,
    Tendsto (fun m : ℕ => (∑ k ∈ Finset.range m, f (tileRows ω k))/m) atTop (𝓝 (∫ x, f x ∂tileLaw L)) := by
  let ν := Measure.infinitePi fun _ : ℕ => tileLaw L
  let X (k : ℕ) (x : ℕ → Tile L) := f (x k)
  have he (k : ℕ) : IdentDistrib (X k) f ν (tileLaw L) := by
    have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => tileLaw L) k
    have h : IdentDistrib (Function.eval k) id ν (tileLaw L) :=
      ⟨hm.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hm.map_eq⟩
    exact h.comp hf
  have hind : iIndepFun X ν := iIndepFun_infinitePi (P:=fun _ : ℕ => tileLaw L) (fun _ => hf)
  have h := strong_law_ae_real X ((he 0).integrable_iff.mpr hi)
    (fun _ _ hij => hind.indepFun hij) (fun j => (he j).trans (he 0).symm)
  rw [(he 0).integral_eq] at h
  exact (tile_preserving L).quasiMeasurePreserving.ae h

/-- Read a tile as an open-chain shell, omitting its external bond. -/
def tileShell {n : ℕ} (x : Tile (n+2)) : PathShell n :=
  WithLp.toLp 2 fun l => match l with
    | .inl (i,d) => x (i,.inl d)
    | .inr (e,d) => x (e.castSucc,.inr d)

private theorem tile_first {n : ℕ} (ω : PathPauliDisorder) :
    tileShell (tileRows ω 0)=pathPauliDisorderShell ω n := by
  apply WithLp.ext_iff.mpr
  funext l
  cases l <;> simp [tileShell,tileRows,pathPauliDisorderShell]

private theorem tile_signal_measurable {n : ℕ} (e : Fin (n+1)) (t : ℝ) :
    Measurable (fun x : Tile (n+2) => bondSignal e (tileShell x) t) := by
  let extRows (x : Tile (n+2)) (p : ℕ × PathPauliDirections) := x (Fin.ofNat (n+2) p.1,p.2)
  have hm : Measurable extRows := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he (x : Tile (n+2)) : pathPauliDisorderShell (extRows x) n=tileShell x := by
    apply WithLp.ext_iff.mpr
    funext l
    rcases l with ⟨i,d⟩|⟨e,d⟩
    · change x (Fin.ofNat (n+2) i.val,.inl d)=x (i,.inl d)
      rw [show Fin.ofNat (n+2) i.val=i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
    · change x (Fin.ofNat (n+2) e.val,.inr d)=x (e.castSucc,.inr d)
      rw [show Fin.ofNat (n+2) e.val=e.castSucc from Fin.ext (Nat.mod_eq_of_lt e.castSucc.isLt)]
  simpa only [Function.comp_apply,he] using (measurable_bondSignal e t).comp hm

/-- At each date of a prescribed finite mesh, fewer than an η fraction
of the tests at each relative bond position fail on sufficiently many
consecutive blocks. One positive threshold works for every block size. -/
theorem gaussian_tile_detection {a T η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ n : ℕ, ∀ G : Finset ℝ, (∀ t∈G, t∈Icc a T) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop, ∀ t∈G, ∀ e : Fin (n+1),
        (((Finset.range m).filter (fun k => |bondSignal e (tileShell (tileRows ω k)) t| ≤ r)).card:ℝ) < η*m := by
  classical
  obtain ⟨r,hr,hsmall⟩ := gaussian_bond_signal_probability (T:=T) ha (half_pos hη)
  refine ⟨r,hr,?_⟩
  intro n G hG
  have one (t : G) (e : Fin (n+1)) : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      (((Finset.range m).filter (fun k => |bondSignal e (tileShell (tileRows ω k)) t| ≤ r)).card:ℝ) < η*m := by
    let S := {x : Tile (n+2) | |bondSignal e (tileShell x) t| ≤ r}
    have hS : MeasurableSet S := measurableSet_le (tile_signal_measurable e t).abs measurable_const
    let f := S.indicator (fun _ => (1:ℝ))
    have hm := (measurePreserving_eval_infinitePi (fun _ : ℕ => tileLaw (n+2)) 0).comp (tile_preserving (n+2))
    have hb : tileLaw (n+2) S ≤ ENNReal.ofReal (η/2) := by
      rw [←hm.measure_preimage hS.nullMeasurableSet]
      simpa only [Set.preimage_setOf_eq,Function.comp_apply,Function.eval_apply,tile_first,S] using
        hsmall n e t (hG t t.property)
    have hlt : (tileLaw (n+2)).real S < η := ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (half_pos hη).le)).trans_lt (half_lt_self hη)
    filter_upwards [tile_average f (measurable_const.indicator hS) ((integrable_const _).indicator hS)] with ω hω
    rw [show (∫ x, f x ∂tileLaw (n+2))=(tileLaw (n+2)).real S from integral_indicator_one hS] at hω
    filter_upwards [hω.eventually_lt_const hlt,eventually_gt_atTop 0] with m h hm
    have hh := (div_lt_iff₀ (Nat.cast_pos.mpr hm)).mp h
    have hcount := Finset.sum_boole (R:=ℝ)
      (fun k => |bondSignal e (tileShell (tileRows ω k)) t| ≤ r) (Finset.range m)
    simpa only [f,S,Set.indicator_apply,Set.mem_setOf_eq,hcount] using hh
  filter_upwards [ae_all_iff.mpr (fun t => ae_all_iff.mpr (one t))] with ω hω
  have h := Filter.eventually_all.mpr (fun t : G => Filter.eventually_all.mpr (hω t))
  exact h.mono fun m hm t ht e => hm ⟨t,ht⟩ e

#print axioms gaussian_tile_detection
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
