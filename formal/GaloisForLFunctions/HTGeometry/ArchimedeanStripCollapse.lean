import GaloisForLFunctions.HTGeometry.ArchimedeanShapeDominance
import GaloisForLFunctions.HTGeometry.VerticalStripBohrHull

/-!
# Autonomous collapse of a relation with archimedean coefficients

Almost periodicity supplies return times along which the solution and all its derivatives converge
back to themselves.  Translating a differential relation along those times and dividing by a
dominant coefficient turns the coefficients into constants: the dominant one becomes `1`, and every
strictly subordinate one becomes `0`.  The limit is an autonomous algebraic differential equation
satisfied on the whole strip.

The dominant index and the limiting constants do not depend on the abscissa, because a tube datum
carries one signature for the whole tube.  That is what makes the limit relation autonomous rather
than merely pointwise.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A boundary datum against the archimedean shape, uniform over the abscissae of a tube. -/
def HasArchimedeanTubeDatum {dd : ℕ} (lam : Fin dd → ℝ) (μ : Fin dd → ℂ) (α M : ℝ)
    (F : ℂ → ℂ) (k : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ) : Prop :=
  c ≠ 0 ∧ ∀ σ : ℝ, 0 < σ → σ ≤ M →
    Tendsto (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)
      / archimedeanShape lam μ α σ k ω b t) atTop (nhds c)

/-- **The autonomous collapse.**  A strip almost periodic holomorphic solution of a differential
relation whose coefficients have archimedean boundary data satisfies a constant-coefficient
relation, with the coefficient at the dominant index equal to one. -/
theorem archimedean_strip_autonomous_relation
    {dd : ℕ} (lam : Fin dd → ℝ) (μ : Fin dd → ℂ) (hlam : ∀ j, 0 < lam j) (hdd : 0 < dd)
    (α : ℝ) {σ₀ η M : ℝ} (hη : 0 < η) (hησ : η ≤ σ₀) (hM : σ₀ + η ≤ M)
    (hσG : ∀ σ : ℝ, 0 < σ → σ ≤ M → ∀ j, 0 < lam j * σ + (μ j).re)
    {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) (exps : Fin N → (ℕ →₀ ℕ)) (F : Fin N → ℂ → ℂ)
    (k : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ a, HasArchimedeanTubeDatum lam μ α M (F a) (k a) (ω a) (b a) (c a))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ₀ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ₀ η') f)
    (hrel : ∀ s : ℂ, ∑ a : Fin N, F a s * diffMonomial f (exps a) s = 0) :
    ∃ (β : Fin N) (rr : Fin N → ℂ), rr β = 1 ∧
      ∀ z₀ ∈ openVerticalStrip σ₀ η, ∑ a : Fin N, rr a * diffMonomial f (exps a) z₀ = 0 := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN k ω b
  set rr : Fin N → ℂ :=
    fun a => if (k a = k β ∧ ω a = ω β ∧ b a = b β) then c a * (c β)⁻¹ else 0 with hrr
  have hrrβ : rr β = 1 := by
    rw [hrr]
    dsimp only
    rw [if_pos ⟨rfl, rfl, rfl⟩, mul_inv_cancel₀ (hdat β).1]
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse (Finset.univ : Finset (Fin N)) hη f exps F β
      (Finset.mem_univ β) hf hap (by intro s; simpa using hrel s)
  refine ⟨β, rr, hrrβ, fun z₀ hz₀ => ?_⟩
  have habs : |z₀.re - σ₀| < η := hz₀
  have hzre : 0 < z₀.re := by
    have := (abs_lt.mp habs).1
    linarith
  have hzM : z₀.re ≤ M := by
    have := (abs_lt.mp habs).2
    linarith
  have hTline : Tendsto (fun l : ℕ => z₀.im + T l) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ z₀.im hT
  have hpt : ∀ (a : Fin N) (l : ℕ),
      F a ((z₀.re : ℂ) + ((z₀.im + T l : ℝ) : ℂ) * Complex.I)
        = F a (z₀ + (T l : ℂ) * Complex.I) := by
    intro a l
    congr 1
    apply Complex.ext <;> simp
  have hdatline : ∀ a : Fin N, Tendsto (fun t : ℝ =>
      F a ((z₀.re : ℂ) + (t : ℂ) * Complex.I)
        / archimedeanShape lam μ α z₀.re (k a) (ω a) (b a) t) atTop (nhds (c a)) :=
    fun a => (hdat a).2 z₀.re hzre hzM
  have hratio := tendsto_archimedeanShape_dominantRatio lam μ hlam hdd hzre
    (hσG z₀.re hzre hzM) α (fun a t => F a ((z₀.re : ℂ) + (t : ℂ) * Complex.I))
    k ω b c (fun a => (hdat a).1) hdatline β hβ
  have hFβ : ∀ᶠ l in atTop, F β (z₀ + (T l : ℂ) * Complex.I) ≠ 0 := by
    have hev : ∀ᶠ t : ℝ in atTop, F β ((z₀.re : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      filter_upwards [(hdatline β).eventually_ne (hdat β).1] with t hne
      exact (div_ne_zero_iff.mp hne).1
    filter_upwards [hTline.eventually hev] with l hl
    rw [← hpt β l]
    exact hl
  have hcoeff : ∀ a ∈ (Finset.univ : Finset (Fin N)), Tendsto
      (fun l => F a (z₀ + (T l : ℂ) * Complex.I) / F β (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (rr a)) := by
    intro a _
    have hcomp := (hratio a).comp hTline
    refine hcomp.congr fun l => ?_
    simp only [Function.comp_apply]
    rw [hpt a l, hpt β l]
  exact (hmain z₀ hz₀ rr hFβ hcoeff).1

end

end GaloisForLFunctions.HTGeometry
