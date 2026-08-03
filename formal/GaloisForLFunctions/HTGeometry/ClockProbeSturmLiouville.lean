import GaloisForLFunctions.HTGeometry.ClockProbeLocalExistence

/-!
# Local probes for a divergence-form second-order equation

The clock equation produced by a metric chart is not `u'' + Vu = 0` but the divergence-form
equation `(A u')' + B u = 0`, in which `A` carries the metric coefficient and the volume density.
This file supplies local solutions of that equation for arbitrary `C¹` coefficients with `A`
nowhere zero.

The construction autonomises the equation in the momentum variable `v = A u'`, giving the field
`(x, u, v) ↦ (1, v / A x, -(B x) u)` on `ℝ³`, and applies the Picard–Lindelöf existence theorem.
The first component of the integral curve is identified with `a + t` by the mean value theorem;
that identification is isolated here as a reusable lemma, since every autonomisation of a
one-dimensional equation uses it.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- **Unit-speed first component.** An integral curve starting at `(a, 1, 0)` whose first component
has derivative one throughout an interval about the origin has affine first component. -/
theorem first_component_affine {α : ℝ → ℝ × ℝ × ℝ} {a ε : ℝ} (hε : 0 < ε)
    (hα0 : α 0 = (a, 1, 0))
    (hcomp1 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).1) 1 t) :
    ∀ t ∈ Ioo (-ε) ε, (α t).1 = a + t := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
  have hg : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).1 - s) 0 t := by
    intro t ht
    have hsub := (hcomp1 t ht).sub (hasDerivAt_id t)
    have hval : (1 : ℝ) - 1 = 0 := by ring
    rw [hval] at hsub
    exact hsub
  have hdiff : DifferentiableOn ℝ (fun s => (α s).1 - s) (Ioo (-ε) ε) :=
    fun t ht => ((hg t ht).differentiableAt).differentiableWithinAt
  have hfd : EqOn (fderiv ℝ fun s => (α s).1 - s) 0 (Ioo (-ε) ε) := by
    intro t ht
    have := (hg t ht).hasFDerivAt.fderiv
    simpa using this
  intro t ht
  have hconst := isOpen_Ioo.is_const_of_fderiv_eq_zero isPreconnected_Ioo hdiff hfd ht hzero
  have hconst' : (α t).1 - t = (α 0).1 - 0 := hconst
  have h0 : (α 0).1 - 0 = a := by rw [hα0]; simp
  rw [h0] at hconst'
  linarith [hconst']

/-- Autonomised first-order field of `(A u')' + B u = 0`, in the momentum variable `v = A u'`. -/
noncomputable def sturmField (A B : ℝ → ℝ) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  fun p => (1, p.2.2 / A p.1, -(B p.1) * p.2.1)

theorem contDiff_sturmField {A B : ℝ → ℝ} (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (hA0 : ∀ t, A t ≠ 0) : ContDiff ℝ 1 (sturmField A B) := by
  refine ContDiff.prodMk contDiff_const (ContDiff.prodMk ?_ ?_)
  · exact ContDiff.div (contDiff_snd.comp contDiff_snd) (hA.comp contDiff_fst)
      (fun p => hA0 p.1)
  · exact ((hB.comp contDiff_fst).neg).mul (contDiff_fst.comp contDiff_snd)

/-- **Local existence for the divergence-form equation.** For `C¹` coefficients with `A` nowhere
zero there is, about every event, a solution of `(A u')' + B u = 0` normalized to one at the
event. -/
theorem exists_localSturmProbe {A B : ℝ → ℝ} (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (hA0 : ∀ t, A t ≠ 0) (a : ℝ) :
    ∃ (w dw : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ w a = 1 ∧
      (∀ t ∈ Ioo (a - ε) (a + ε), HasDerivAt w (dw t) t) ∧
      (∀ t ∈ Ioo (a - ε) (a + ε), DifferentiableAt ℝ dw t) ∧
      (∀ t ∈ Ioo (a - ε) (a + ε), HasDerivAt (fun s => A s * dw s) (-(B t) * w t) t) := by
  obtain ⟨α, hα0, ε, hε, hode⟩ :=
    (contDiff_sturmField hA hB
        hA0).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := ((a, 1, 0) : ℝ × ℝ × ℝ)) 0
  have hIoo : ∀ t : ℝ, t ∈ Ioo (-ε) ε → t ∈ Ioo (0 - ε) (0 + ε) := by
    intro t ht
    simpa using ht
  have hcomp1 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).1) 1 t := by
    intro t ht
    exact projOne.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have hcomp2 : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s => (α s).2.1) ((α t).2.2 / A ((α t).1)) t := by
    intro t ht
    exact projTwo.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have hcomp3 : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s => (α s).2.2) (-(B ((α t).1)) * (α t).2.1) t := by
    intro t ht
    exact projThree.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have haffine := first_component_affine hε hα0 hcomp1
  have hshift : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z - a) 1 y := by
    intro y
    simpa using (hasDerivAt_id y).sub_const a
  refine ⟨fun t => (α (t - a)).2.1, fun t => (α (t - a)).2.2 / A t, ε, hε, ?_, ?_, ?_, ?_⟩
  · simp [hα0]
  · intro t ht
    have hta : t - a ∈ Ioo (-ε) ε := by
      obtain ⟨h1, h2⟩ := ht
      constructor <;> linarith
    have hc := (hcomp2 (t - a) hta).comp t (hshift t)
    rw [mul_one, haffine (t - a) hta] at hc
    have hxx : a + (t - a) = t := by ring
    rw [hxx] at hc
    exact hc
  · intro t ht
    have hta : t - a ∈ Ioo (-ε) ε := by
      obtain ⟨h1, h2⟩ := ht
      constructor <;> linarith
    have hc := (hcomp3 (t - a) hta).comp t (hshift t)
    have hnum : DifferentiableAt ℝ (fun s => (α (s - a)).2.2) t := hc.differentiableAt
    exact hnum.div (hA.differentiable (by simp) t) (hA0 t)
  · intro t ht
    have hta : t - a ∈ Ioo (-ε) ε := by
      obtain ⟨h1, h2⟩ := ht
      constructor <;> linarith
    have hAv : (fun s => A s * ((α (s - a)).2.2 / A s)) = fun s => (α (s - a)).2.2 := by
      funext s
      have h := hA0 s
      field_simp
    show HasDerivAt (fun s => A s * ((α (s - a)).2.2 / A s))
      (-(B t) * (α (t - a)).2.1) t
    rw [hAv]
    have hc := (hcomp3 (t - a) hta).comp t (hshift t)
    rw [mul_one, haffine (t - a) hta] at hc
    have hxx : a + (t - a) = t := by ring
    rw [hxx] at hc
    exact hc

end GaloisForLFunctions.HTGeometry
