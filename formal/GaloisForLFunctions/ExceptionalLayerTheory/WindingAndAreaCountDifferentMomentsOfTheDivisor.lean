import GaloisForLFunctions.ExceptionalLayerTheory.ThePlanarAreaOfALargeHadamardReading
import GaloisForLFunctions.ExceptionalLayerTheory.AddingLocalSuperlevelAreasOnAFiniteDivisor
import GaloisForLFunctions.RHTower.WindingXiCircle
import Mathlib.Data.Nat.Choose.Cast

/-!
# Winding and negative area in a finite ξ-window

Winding counts the sum of the zero orders. The limiting area of large
negative logarithmic derivatives counts the sum of their squares. Their
difference counts ordered pairs of distinct copies at the same point.
A circle avoiding zeros therefore admits an area test for simplicity of
every enclosed zero.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem disk_area_sum (c : ℂ) {R : ℝ} (t : Finset ℂ)
    (ht : ∀ x, x∈t ↔ ‖x-c‖<R ∧ xi x=0) (hb : ∀ x, ‖x-c‖=R → xi x≠0) :
    Tendsto (fun L : ℝ => L^2*volume.real (hadamardLevelPatch c R L)) atTop
      (𝓝 (∑ x ∈ t, Real.pi*(hadamardOrder x:ℝ)^2/4)) := by
  let f (z : ℂ) := -(logDeriv xi z).re
  have hpatch (x : ℂ) (s L : ℝ) : {z | z∈ball x s ∧ L<f z}=hadamardLevelPatch x s L := by
    ext z
    change (_ ∧ L < -(logDeriv xi z).re) ↔ (_ ∧ (logDeriv xi z).re < -L)
    constructor <;> rintro ⟨h,h'⟩ <;> exact ⟨h,by linarith only [h']⟩
  have hinside (x : ℂ) (hx : x∈t) : x∈ball c R := by
    simpa only [mem_ball,dist_eq_norm] using ((ht x).mp hx).1
  have hreg (z : ℂ) (hz : z∈closedBall c R) (hn : z∉t) : ContinuousAt f z := by
    have hle : ‖z-c‖≤R := by simpa only [dist_eq_norm] using mem_closedBall.mp hz
    have hzero : xi z≠0 := fun he => hn ((ht z).mpr ⟨hle.lt_of_ne (fun heq => hb z heq he),he⟩)
    have ha := xi_differentiable.analyticAt z
    exact (Complex.continuous_re.continuousAt.comp (ha.deriv.continuousAt.div ha.continuousAt hzero)).neg
  have h := sum_local_superlevel_areas f (fun x => Real.pi*(hadamardOrder x:ℝ)^2/4)
    (fun L => L^2) c R t hinside hreg (fun x => by
      simpa only [hpatch,hadamardOrder] using local_hadamard_level_area x)
  simpa only [hpatch] using h

/-- Winding measures the linear multiplicity count while the normalized
negative area measures the quadratic count, for the same circle. -/
theorem winding_and_hadamard_area (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi) =
        ∑ z ∈ t, (hadamardOrder z:ℤ) ∧
      Tendsto (fun L : ℝ => 4/Real.pi*L^2*volume.real (hadamardLevelPatch c R L))
        atTop (𝓝 (∑ z ∈ t, (hadamardOrder z:ℝ)^2)) := by
  obtain ⟨t,ht,hw⟩ := windingNumber_xi_circle c hR hb
  refine ⟨t,ht,hw,?_⟩
  have h := (disk_area_sum c t ht hb).const_mul (4/Real.pi)
  rw [Finset.mul_sum] at h
  have he (x : ℂ) : 4/Real.pi*(Real.pi*(hadamardOrder x:ℝ)^2/4)=(hadamardOrder x:ℝ)^2 := by
    field_simp [Real.pi_ne_zero]
  simp only [he] at h
  exact h.congr fun _ => (mul_assoc ..).symm

private theorem ord_pos {z : ℂ} (hz : xi z=0) : 0<hadamardOrder z :=
  Nat.pos_of_ne_zero fun hn => (hadamardOrder_zero_iff z).mp hn hz

/-- The difference of the two observations converges to an even integer,
twice the number of unordered coincident pairs of zero copies. -/
theorem area_winding_excess_counts_pairs (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      Tendsto (fun L : ℝ => 4/Real.pi*L^2*volume.real (hadamardLevelPatch c R L) -
        (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi):ℝ)) atTop
        (𝓝 (2*(∑ z ∈ t, ((hadamardOrder z).choose 2:ℝ)))) := by
  obtain ⟨t,ht,hw,ha⟩ := winding_and_hadamard_area c hR hb
  refine ⟨t,ht,?_⟩
  rw [hw,Int.cast_sum]
  simp only [Int.cast_natCast]
  have he : (∑ z ∈ t, (hadamardOrder z:ℝ)^2)-(∑ z ∈ t, (hadamardOrder z:ℝ)) =
      2*(∑ z ∈ t, ((hadamardOrder z).choose 2:ℝ)) := by
    rw [←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [Nat.cast_choose_two]
    ring
  exact he ▸ ha.sub_const (∑ z ∈ t, (hadamardOrder z:ℝ))

/-- The area count equals winding precisely when each enclosed ξ-zero
is simple. A multiple zero contributes its positive excess m(m−1). -/
theorem area_equals_winding_iff_simple (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    Tendsto (fun L : ℝ => 4/Real.pi*L^2*volume.real (hadamardLevelPatch c R L)) atTop
      (𝓝 ((windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi):ℤ):ℝ)) ↔
      ∀ z, ‖z-c‖<R → xi z=0 → hadamardOrder z=1 := by
  classical
  obtain ⟨t,ht,hw,ha⟩ := winding_and_hadamard_area c hR hb
  rw [hw,Int.cast_sum]
  push_cast
  constructor
  · intro h z hzr hzero
    have he := tendsto_nhds_unique ha h
    have hsum : ∑ x ∈ t, ((hadamardOrder x:ℝ)^2-(hadamardOrder x:ℝ))=0 := by
      rw [Finset.sum_sub_distrib,he,sub_self]
    have hpos (x : ℂ) (hx : x∈t) : (1:ℝ)≤hadamardOrder x := by
      exact_mod_cast ord_pos ((ht x).mp hx).2
    have hn (x : ℂ) (hx : x∈t) : 0≤(hadamardOrder x:ℝ)^2-hadamardOrder x := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr (hpos x hx)) (Nat.cast_nonneg (hadamardOrder x): (0:ℝ)≤hadamardOrder x)]
    have hzt := (ht z).mpr ⟨hzr,hzero⟩
    have hez := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum z hzt
    have hf : (hadamardOrder z:ℝ)*((hadamardOrder z:ℝ)-1)=0 := by linarith only [hez]
    have hone := (mul_eq_zero.mp hf).resolve_left (Nat.cast_ne_zero.mpr (ord_pos hzero).ne')
    exact_mod_cast sub_eq_zero.mp hone
  · intro h
    convert ha using 2
    apply Finset.sum_congr rfl
    intro z hz
    rw [h z ((ht z).mp hz).1 ((ht z).mp hz).2,Nat.cast_one,one_pow]

#print axioms winding_and_hadamard_area
#print axioms area_winding_excess_counts_pairs
#print axioms area_equals_winding_iff_simple
end GaloisForLFunctions.ExceptionalLayerTheory
