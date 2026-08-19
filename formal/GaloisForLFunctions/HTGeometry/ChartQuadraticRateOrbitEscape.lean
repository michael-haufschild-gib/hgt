/-
# The labeling orbit of the quadratic-rate relation on a chart

The fixed-shell nonflatness proof symmetrises the quadratic-rate relation over all labelings of the
spectrum and argues that the resulting product cannot vanish identically on a connected chart.
Each factor is the relation of a *relabeled* coefficient packet, which is again nonzero with zero
sum, so chart rigidity refutes every factor separately; the identity theorem for a finite product
of analytic functions then produces one chart point at which the whole orbit is nonzero.

The rate carried here is the card's own `Q(H) = Tr(H²)` up to the constant, evaluated at the chart
Hamiltonian.  No power sum of eigenvalues appears, so no Newton identity is needed.

Main results:
* `analyticOnNhd_chartQuadraticRate` — the rate is analytic on the chart.
* `exists_chartQuadraticOrbit_ne_zero` — the labeling orbit is somewhere nonzero on the chart.
-/
import GaloisForLFunctions.HTGeometry.ChartQuadraticRateEscape
import GaloisForLFunctions.HTGeometry.QuadraticRateAnalyticEscape

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Rate

variable {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]

theorem analyticAt_localExtensionMatrix_entry (E : α → ℂ) (M : Matrix α α ℂ)
    (p₀ : (ρ → ℂ) × Matrix ρ ρ ℂ) (x y : α × ρ) :
    AnalyticAt ℂ (fun p => localExtensionMatrix E p.1 M p.2 x y) p₀ := by
  have hmat := localExtensionMatrix_analyticAt E M p₀
  have hentry : AnalyticAt ℂ (fun N : Matrix (α × ρ) (α × ρ) ℂ => N x y)
      (localExtensionMatrix E p₀.1 M p₀.2) := by
    let row : Matrix (α × ρ) (α × ρ) ℂ →L[ℂ] ((α × ρ) → ℂ) := ContinuousLinearMap.proj (R := ℂ) x
    let col : ((α × ρ) → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) y
    exact (col.comp row).analyticAt _
  exact hentry.fun_comp_of_eq hmat rfl

/-- **The chart rate is analytic.**  The trace of the square of the chart Hamiltonian is a
polynomial in the chart coordinates. -/
theorem analyticOnNhd_chartQuadraticRate (E : α → ℂ) (M : Matrix α α ℂ) (κ : ℂ)
    (U : Set ((ρ → ℂ) × Matrix ρ ρ ℂ)) :
    AnalyticOnNhd ℂ (fun p => κ * ((localExtensionMatrix E p.1 M p.2) ^ 2).trace) U := by
  have hsum : (fun p : (ρ → ℂ) × Matrix ρ ρ ℂ =>
      κ * ((localExtensionMatrix E p.1 M p.2) ^ 2).trace)
      = fun p => κ * ∑ x, ∑ y,
          localExtensionMatrix E p.1 M p.2 x y * localExtensionMatrix E p.1 M p.2 y x := by
    funext p
    rw [trace_sq_eq_sum]
  rw [hsum]
  refine (analyticOnNhd_const (v := κ) (s := U)).mul ?_
  refine Finset.analyticOnNhd_fun_sum _ fun x _ => Finset.analyticOnNhd_fun_sum _ fun y _ => ?_
  intro p₀ _
  exact (analyticAt_localExtensionMatrix_entry E M p₀ x y).mul
    (analyticAt_localExtensionMatrix_entry E M p₀ y x)

end Rate

/-- **The labeling orbit of the quadratic-rate relation is somewhere nonzero on the chart.**  This
is the symmetrised obstruction of the fixed-shell nonflatness proof, with the rate the trace of the
square of the chart Hamiltonian. -/
theorem exists_chartQuadraticOrbit_ne_zero {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ p ∈ C.U, (∏ σ : Equiv.Perm (A × Bool),
        ((∑ i, c i * C.branch (σ i) p) ^ 2
          - κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ 2).trace)) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set factor : Equiv.Perm (A × Bool) → ((Bool → ℂ) × Matrix Bool Bool ℂ) → ℂ :=
    fun σ p => (∑ i, c i * C.branch (σ i) p) ^ 2
      - κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ 2).trace with hfactor
  have hanalytic : ∀ σ : Equiv.Perm (A × Bool), AnalyticOnNhd ℂ (factor σ) C.U := by
    intro σ
    refine AnalyticOnNhd.sub ?_ (analyticOnNhd_chartQuadraticRate _ M κ C.U)
    refine AnalyticOnNhd.pow ?_ 2
    exact Finset.analyticOnNhd_fun_sum _ fun i _ =>
      (analyticOnNhd_const (v := c i) (s := C.U)).mul (C.analyticOn_branch (σ i))
  have hprod : Set.EqOn (fun p => ∏ σ : Equiv.Perm (A × Bool), factor σ p) 0 C.U := by
    intro p hp
    exact hcon p hp
  obtain ⟨σ, -, hσ⟩ := exists_eqOn_zero_of_finsetProd_eqOn_zero (f := factor) Finset.univ
    (fun σ _ => hanalytic σ) C.isPreconnected_U C.isOpen_U ⟨(boolShift z₀, 0), C.center_mem⟩ hprod
  set d : A × Bool → ℂ := fun j => c (σ.symm j) with hd
  have hdne : d ≠ 0 := by
    intro h0
    refine hcne ?_
    funext i
    have := congrFun h0 (σ i)
    simpa [hd] using this
  have hdsum : (∑ j, d j) = 0 := by
    rw [hd]
    rw [Fintype.sum_equiv σ (fun i => c i) (fun j => c (σ.symm j)) fun i => by simp] at hzero
    exact hzero
  have hident : ∀ p ∈ C.U, (∑ i, d i * C.branch i p) ^ 2
      = κ * ((localExtensionMatrix (fun a => (E a : ℂ)) p.1 M p.2) ^ 2).trace := by
    intro p hp
    have hswap : (∑ i, c i * C.branch (σ i) p) = ∑ j, d j * C.branch j p :=
      Fintype.sum_equiv σ _ _ fun i => by simp [hd]
    have := hσ hp
    rw [hfactor] at this
    simp only [Pi.zero_apply, sub_eq_zero] at this
    rw [← hswap]
    exact this
  exact hdne (chart_quadraticRate_eq_zero hcard hE hgap hMherm hM hbase C d κ hident hdsum)

end

end GaloisForLFunctions.HTGeometry
