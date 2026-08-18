import Mathlib
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.GaugeProperness

/-!
# Anti-equivariant descent formation

This module formalizes the algebraic and global topological core of ULF-AEDM-1.
A source differential reversed by a reflection cannot descend nontrivially through a
reflection-blind surjection.  A marked target instead inherits the anti-equivariant grading.
The integrated flow is static on every reflection-blind quotient, and compact-preimage properness
then selects the unique source grade with compact complete history.
-/

namespace HTGeometry

open Set Topology
open NomologicalHomotopyGeometry

/-- Coordinate-free action law: any real-parameter action reversed by a source involution and
intertwined through a reflection-blind surjection is pointwise static on the target.  Only the
divisibility of the real parameter group and the action law are used. -/
theorem reversible_blind_surjective_action_static
    {X Y : Type*}
    (R : X → X) (q : X → Y)
    (U : ℝ → X → X) (V : ℝ → Y → Y)
    (hblind : ∀ x, q (R x) = q x)
    (hreverse : ∀ t x, R (U t x) = U (-t) (R x))
    (hintertwine : ∀ t x, q (U t x) = V t (q x))
    (hVadd : ∀ s t y, V (s + t) y = V s (V t y))
    (hVzero : ∀ y, V 0 y = y)
    (hq : Function.Surjective q) :
    ∀ t y, V t y = y := by
  have hsymm : ∀ t y, V t y = V (-t) y := by
    intro t y
    obtain ⟨x, rfl⟩ := hq y
    calc
      V t (q x) = q (U t x) := (hintertwine t x).symm
      _ = q (R (U t x)) := (hblind (U t x)).symm
      _ = q (U (-t) (R x)) := by rw [hreverse t x]
      _ = V (-t) (q (R x)) := hintertwine (-t) (R x)
      _ = V (-t) (q x) := by rw [hblind x]
  intro t y
  let s : ℝ := t / 2
  have ht : t = s + s := by
    dsimp [s]
    ring
  calc
    V t y = V (s + s) y := by rw [ht]
    _ = V s (V s y) := hVadd s s y
    _ = V s (V (-s) y) := by rw [hsymm s y]
    _ = V (s + -s) y := (hVadd s (-s) y).symm
    _ = y := by simpa using hVzero y

section LinearDescent

variable {X Y : Type*}
  [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- Failure of a source differential to descend through an observer. -/
def antiEquivariantDescentDefect (D : X →ₗ[ℝ] X) (q : X →ₗ[ℝ] Y)
    (Dbar : Y →ₗ[ℝ] Y) : X →ₗ[ℝ] Y :=
  q.comp D - Dbar.comp q

/-- Reflection-pair conservation: on a reflection-blind observer, the two descent defects sum to
minus twice the proposed observer clock. -/
theorem antiEquivariantDescentDefect_reflection_conservation
    (R D : X →ₗ[ℝ] X) (q : X →ₗ[ℝ] Y) (Dbar : Y →ₗ[ℝ] Y)
    (hanti : R.comp D = -(D.comp R))
    (hblind : q.comp R = q) (x : X) :
    antiEquivariantDescentDefect D q Dbar x +
        antiEquivariantDescentDefect D q Dbar (R x) =
      (-2 : ℝ) • Dbar (q x) := by
  have hanti_x : R (D x) = -D (R x) := by
    simpa using LinearMap.congr_fun hanti x
  have hblind_x : q (R x) = q x := by
    simpa using LinearMap.congr_fun hblind x
  have hblind_Dx : q (R (D x)) = q (D x) := by
    simpa using LinearMap.congr_fun hblind (D x)
  simp only [antiEquivariantDescentDefect, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hblind_x]
  have hqDR : q (D (R x)) = -q (D x) := by
    have htransport := congrArg q hanti_x
    simp only [map_neg] at htransport
    have hq : q (D x) = -q (D (R x)) := hblind_Dx.symm.trans htransport
    simpa using (congrArg Neg.neg hq).symm
  rw [hqDR]
  module

/-- Exact descent through a reflection-blind observer kills the descended clock on the observer
range. -/
theorem antiEquivariant_blind_descent_zero
    (R D : X →ₗ[ℝ] X) (q : X →ₗ[ℝ] Y) (Dbar : Y →ₗ[ℝ] Y)
    (hanti : R.comp D = -(D.comp R))
    (hblind : q.comp R = q)
    (hdesc : q.comp D = Dbar.comp q) :
    Dbar.comp q = 0 := by
  ext x
  have hdefect_x : antiEquivariantDescentDefect D q Dbar x = 0 := by
    simp [antiEquivariantDescentDefect, LinearMap.congr_fun hdesc x]
  have hdefect_Rx : antiEquivariantDescentDefect D q Dbar (R x) = 0 := by
    simp [antiEquivariantDescentDefect, LinearMap.congr_fun hdesc (R x)]
  have hconserve := antiEquivariantDescentDefect_reflection_conservation
    R D q Dbar hanti hblind x
  rw [hdefect_x, hdefect_Rx, zero_add] at hconserve
  have hz : (-2 : ℝ) • Dbar (q x) = 0 := hconserve.symm
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Surjectivity upgrades range freezing to vanishing of the whole descended clock. -/
theorem antiEquivariant_blind_surjective_descent_zero
    (R D : X →ₗ[ℝ] X) (q : X →ₗ[ℝ] Y) (Dbar : Y →ₗ[ℝ] Y)
    (hanti : R.comp D = -(D.comp R))
    (hblind : q.comp R = q)
    (hdesc : q.comp D = Dbar.comp q)
    (hq : Function.Surjective q) :
    Dbar = 0 := by
  have hz := antiEquivariant_blind_descent_zero R D q Dbar hanti hblind hdesc
  ext y
  obtain ⟨x, rfl⟩ := hq y
  simpa using LinearMap.congr_fun hz x

/-- Positive repair law: a marked surjective observer transports source anti-equivariance to the
target differential instead of freezing it. -/
theorem marked_surjective_descent_transports_antiEquivariance
    (R D : X →ₗ[ℝ] X) (S Dbar : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hanti : R.comp D = -(D.comp R))
    (hmarked : q.comp R = S.comp q)
    (hdesc : q.comp D = Dbar.comp q)
    (hq : Function.Surjective q) :
    S.comp Dbar = -(Dbar.comp S) := by
  ext y
  obtain ⟨x, rfl⟩ := hq y
  have hanti_x : R (D x) = -D (R x) := by
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply] using
      LinearMap.congr_fun hanti x
  have hmarked_x : q (R x) = S (q x) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hmarked x
  have hmarked_Dx : q (R (D x)) = S (q (D x)) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hmarked (D x)
  have hdesc_x : q (D x) = Dbar (q x) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hdesc x
  have hdesc_Rx : q (D (R x)) = Dbar (q (R x)) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hdesc (R x)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply]
  calc
    S (Dbar (q x)) = S (q (D x)) := by rw [hdesc_x]
    _ = q (R (D x)) := hmarked_Dx.symm
    _ = -q (D (R x)) := by rw [hanti_x, map_neg]
    _ = -Dbar (q (R x)) := by rw [hdesc_Rx]
    _ = -Dbar (S (q x)) := by rw [hmarked_x]

end LinearDescent

section ReversibleFlow

variable {X Y : Type*}
  [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- A continuous-time linear flow that reverses under the source reflection and descends through a
reflection-blind surjection is static on the target.  No analytic continuity hypothesis is needed;
divisibility of the real parameter group is the load-bearing input. -/
theorem reversible_blind_surjective_flow_static
    (R : X →ₗ[ℝ] X) (q : X →ₗ[ℝ] Y)
    (U : ℝ → X →ₗ[ℝ] X) (V : ℝ → Y →ₗ[ℝ] Y)
    (hblind : q.comp R = q)
    (hreverse : ∀ t, R.comp (U t) = (U (-t)).comp R)
    (hintertwine : ∀ t, q.comp (U t) = (V t).comp q)
    (hVadd : ∀ s t, V (s + t) = (V s).comp (V t))
    (hVzero : V 0 = LinearMap.id)
    (hq : Function.Surjective q) :
    ∀ t, V t = LinearMap.id := by
  have hsymm : ∀ t, V t = V (-t) := by
    intro t
    ext y
    obtain ⟨x, rfl⟩ := hq y
    calc
      V t (q x) = q (U t x) := by
        simpa using (LinearMap.congr_fun (hintertwine t) x).symm
      _ = q (R (U t x)) := by
        symm
        simpa using LinearMap.congr_fun hblind (U t x)
      _ = q (U (-t) (R x)) := by
        simpa only [LinearMap.comp_apply] using
          congrArg q (LinearMap.congr_fun (hreverse t) x)
      _ = V (-t) (q (R x)) := by
        simpa using LinearMap.congr_fun (hintertwine (-t)) (R x)
      _ = V (-t) (q x) := by
        rw [show q (R x) = q x by
          simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hblind x]
  intro t
  let s : ℝ := t / 2
  have ht : t = s + s := by
    dsimp [s]
    ring
  calc
    V t = V (s + s) := by rw [ht]
    _ = (V s).comp (V s) := hVadd s s
    _ = (V s).comp (V (-s)) := by rw [hsymm s]
    _ = V (s + -s) := (hVadd s (-s)).symm
    _ = LinearMap.id := by simpa using hVzero

end ReversibleFlow

section GlobalProperness

/-- Any noncompact family collapsed to one observer value obstructs compact-preimage properness. -/
theorem constantFamily_not_compactPreimageProper_of_noncompactClosure
    {T X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (f : X → Y) (γ : T → X) (y : Y)
    (hconstant : ∀ t, f (γ t) = y)
    (hnoncompact : ¬ IsCompact (closure (Set.range γ))) :
    ¬ CompactPreimageProper f := by
  intro hf
  have hfiberCompact : IsCompact (f ⁻¹' ({y} : Set Y)) := hf isCompact_singleton
  have hfiberClosed : IsClosed (f ⁻¹' ({y} : Set Y)) := hfiberCompact.isClosed
  apply hnoncompact
  exact hfiberCompact.of_isClosed_subset isClosed_closure
    (closure_minimal (by
      rintro _ ⟨t, rfl⟩
      simp [hconstant t]) hfiberClosed)

variable {X Y : Type*}
  [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

/-- Global formation selector.  If compact complete source history is equivalent to neutrality,
then a reflection-blind surjective proper formation map forces the neutral grade. -/
theorem reversible_blind_proper_formation_forces_neutral
    (R : X →ₗ[ℝ] X) (q : X →ₗ[ℝ] Y)
    (U : ℝ → X →ₗ[ℝ] X) (V : ℝ → Y →ₗ[ℝ] Y)
    (x : X) (a : ℝ)
    (hblind : q.comp R = q)
    (hreverse : ∀ t, R.comp (U t) = (U (-t)).comp R)
    (hintertwine : ∀ t, q.comp (U t) = (V t).comp q)
    (hVadd : ∀ s t, V (s + t) = (V s).comp (V t))
    (hVzero : V 0 = LinearMap.id)
    (hqsurj : Function.Surjective q)
    (hqproper : CompactPreimageProper q)
    (hformation : IsCompact (closure (Set.range fun t : ℝ => U t x)) ↔ a = 0) :
    a = 0 := by
  have hstatic := reversible_blind_surjective_flow_static
    R q U V hblind hreverse hintertwine hVadd hVzero hqsurj
  apply hformation.mp
  by_contra hnoncompact
  have hconstant : ∀ t : ℝ, q (U t x) = q x := by
    intro t
    calc
      q (U t x) = V t (q x) := by
        simpa using LinearMap.congr_fun (hintertwine t) x
      _ = q x := by rw [hstatic t]; rfl
  exact (constantFamily_not_compactPreimageProper_of_noncompactClosure
    q (fun t : ℝ => U t x) (q x) hconstant hnoncompact) hqproper

end GlobalProperness

end HTGeometry
