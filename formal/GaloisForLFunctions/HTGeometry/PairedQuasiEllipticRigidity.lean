import GaloisForLFunctions.HTGeometry.EllipticPoleSpace
import GaloisForLFunctions.HTGeometry.BoundaryWedgePeriodRankObstruction

/-!
# Rigidity of periodic functions with a constant second increment

An entire function that is periodic for one lattice generator and changes by a constant under the
other is constant.  Its derivative is entire and invariant under the full lattice, hence constant by
elliptic Liouville; an entire function with constant derivative is affine, and periodicity kills the
slope.

This is the analytic core of the one-pole classification of paired quasi-elliptic increments: two
functions with the same principal parts, the same period and the same constant second increment
differ by a constant.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The derivative of a periodic function is periodic. -/
theorem periodic_deriv_of_periodic {f : ℂ → ℂ} {c : ℂ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro z
  have hfun : (fun x => f (x + c)) = f := by
    funext x
    exact h x
  have hd := deriv_comp_add_const f c z
  rw [hfun] at hd
  exact hd.symm

/-- The derivative of a function with a constant increment is periodic for that step. -/
theorem periodic_deriv_of_constant_increment {f : ℂ → ℂ} {c k : ℂ}
    (h : ∀ z, f (z + c) = f z + k) : Function.Periodic (deriv f) c := by
  intro z
  have hfun : (fun x => f (x + c)) = fun x => f x + k := by
    funext x
    exact h x
  have hd := deriv_comp_add_const f c z
  rw [hfun, deriv_add_const] at hd
  exact hd.symm

/-- **Constant-increment rigidity.**  An entire function periodic for one lattice generator and
with constant increment along the other is constant. -/
theorem const_of_periodic_of_constant_increment (L : PeriodPair) {W : ℂ → ℂ} {k : ℂ}
    (hdiff : Differentiable ℂ W) (hper : Function.Periodic W L.ω₁)
    (hinc : ∀ z, W (z + L.ω₂) = W z + k) :
    ∀ x y, W x = W y := by
  have hdd : ∀ z, AnalyticAt ℂ (deriv W) z := fun z =>
    ((hdiff.differentiableOn.analyticOnNhd isOpen_univ).deriv) z (Set.mem_univ z)
  have hlat : ∀ p ∈ L.lattice, Function.Periodic (deriv W) p := by
    intro p hp
    refine periodic_of_mem_span_range ![L.ω₁, L.ω₂] (fun i => ?_) p ?_
    · fin_cases i
      · exact periodic_deriv_of_periodic hper
      · exact periodic_deriv_of_constant_increment hinc
    · rw [range_cons_two]
      exact hp
  have hconst := const_of_lattice_periodic_analytic L hdd hlat
  set c0 : ℂ := deriv W 0 with hc0def
  have hc0 : ∀ z, deriv W z = c0 := fun z => hconst z 0
  have hVdiff : Differentiable ℂ (fun z => W z - c0 * z) :=
    hdiff.sub ((differentiable_const c0).mul differentiable_id)
  have hVd : ∀ z, deriv (fun z => W z - c0 * z) z = 0 := by
    intro z
    have h1 : HasDerivAt W (deriv W z) z := (hdiff z).hasDerivAt
    have h2 : HasDerivAt (fun x : ℂ => c0 * x) c0 z := by
      simpa using (hasDerivAt_id z).const_mul c0
    have h3 : HasDerivAt (fun x : ℂ => W x - c0 * x) (deriv W z - c0) z := h1.sub h2
    rw [h3.deriv, hc0 z, sub_self]
  have hVconst := is_const_of_deriv_eq_zero hVdiff hVd
  have hWaff : ∀ z, W z = c0 * z + W 0 := by
    intro z
    have h := hVconst z 0
    simp only [mul_zero, sub_zero] at h
    linear_combination h
  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hslope : c0 = 0 := by
    have h1 := hper 0
    rw [hWaff (0 + L.ω₁), hWaff 0] at h1
    have h2 : c0 * L.ω₁ = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with hc | hw
    · exact hc
    · exact absurd hw hω
  intro x y
  rw [hWaff x, hWaff y, hslope]
  ring

/-- **Two increments with the same poles agree up to a constant.**  If two meromorphic functions
have an everywhere-analytic difference, share the period `ω₁`, and have constant `ω₂`-increments,
they differ by a constant. -/
theorem exists_const_sub_of_periodic_of_constant_increment (L : PeriodPair) {U V : ℂ → ℂ}
    {kU kV : ℂ}
    (hdiff : Differentiable ℂ (fun z => U z - V z))
    (hperU : Function.Periodic U L.ω₁) (hperV : Function.Periodic V L.ω₁)
    (hincU : ∀ z, U (z + L.ω₂) = U z + kU)
    (hincV : ∀ z, V (z + L.ω₂) = V z + kV) :
    ∃ c : ℂ, ∀ z, U z - V z = c := by
  refine ⟨U 0 - V 0, fun z => ?_⟩
  refine const_of_periodic_of_constant_increment L (k := kU - kV) hdiff ?_ ?_ z 0
  · intro w
    show U (w + L.ω₁) - V (w + L.ω₁) = U w - V w
    rw [hperU w, hperV w]
  · intro w
    show U (w + L.ω₂) - V (w + L.ω₂) = (U w - V w) + (kU - kV)
    rw [hincU w, hincV w]
    ring

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- A simple pole of residue `r` at `q`: subtracting the principal part restores analyticity. -/
def HasSimplePoleResidue (U : ℂ → ℂ) (q r : ℂ) : Prop :=
  AnalyticAt ℂ (fun w => U w - r / (w - q)) q

/-- Two functions with the same simple pole and the same residue have an analytic difference
there. -/
theorem analyticAt_sub_of_hasSimplePoleResidue {U V : ℂ → ℂ} {q r : ℂ}
    (hU : HasSimplePoleResidue U q r) (hV : HasSimplePoleResidue V q r) :
    AnalyticAt ℂ (fun w => U w - V w) q := by
  have hsub := hU.sub hV
  have hfun : ((fun w => U w - r / (w - q)) - fun w => V w - r / (w - q))
      = fun w => U w - V w := by
    funext w
    simp only [Pi.sub_apply]
    ring
  rwa [hfun] at hsub

/-- **One-pole classification.**  Two functions with the same pole set, at each point of it a
simple pole with the same residue, both periodic for `ω₁` and with constant `ω₂`-increment, differ
by a constant. -/
theorem exists_const_sub_of_matching_simple_poles (L : PeriodPair) {U V : ℂ → ℂ} {kU kV r : ℂ}
    (S : Set ℂ)
    (hUan : ∀ z ∉ S, AnalyticAt ℂ U z) (hVan : ∀ z ∉ S, AnalyticAt ℂ V z)
    (hUp : ∀ q ∈ S, HasSimplePoleResidue U q r) (hVp : ∀ q ∈ S, HasSimplePoleResidue V q r)
    (hperU : Function.Periodic U L.ω₁) (hperV : Function.Periodic V L.ω₁)
    (hincU : ∀ z, U (z + L.ω₂) = U z + kU) (hincV : ∀ z, V (z + L.ω₂) = V z + kV) :
    ∃ c : ℂ, ∀ z, U z - V z = c := by
  have han : ∀ z : ℂ, AnalyticAt ℂ (fun w => U w - V w) z := by
    intro z
    by_cases hz : z ∈ S
    · exact analyticAt_sub_of_hasSimplePoleResidue (hUp z hz) (hVp z hz)
    · exact (hUan z hz).sub (hVan z hz)
  have hdiff : Differentiable ℂ (fun z => U z - V z) := fun z => (han z).differentiableAt
  exact exists_const_sub_of_periodic_of_constant_increment L hdiff hperU hperV hincU hincV

end GaloisForLFunctions.HTGeometry
