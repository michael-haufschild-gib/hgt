import GaloisForLFunctions.ArithmeticOrientationGeometry.TheCorrespondenceAlgebra

/-!
# Correctors and the Lefschetz trace

Which quantity converts *relative* compensation into *absolute* energy? On a scaling datum the
answer is an exact conservation law for correspondences.

The **Lefschetz trace** of a correspondence `ξ` at a cycle `x` is `L(x, ξ) = Σ_g ξ(g) L(x, g)`, the
intersection of the graph of `ξ` with the diagonal. It splits into a **pole trace**, which reads only
the fibre degrees of `x`, and a **primitive trace**, which reads only the defect
(`lefschetzTrace_eq`):

    L(x, ξ) = (Σ_g ξ(g)(e^{s(g)} + 1)) (x · H)(x · V) − Σ_g ξ(g) e^{s(g)/2} c_x(g).

A **corrector** is a correspondence whose pole trace vanishes, `Σ_g ξ(g)(e^{s(g)} + 1) = 0`: it
compensates the trivial part of the Lefschetz numbers exactly, relative to the pole plane. For a
corrector the Lefschetz trace *is* primitive energy (`lefschetzTrace_of_corrector`), independent of
the fibre degrees of `x` (`lefschetzTrace_of_corrector_add_pole`):

* **Conservation law.** `L(x, ξ) = −Σ_g ξ(g) e^{s(g)/2} c_x(g)` for every corrector — relative
  compensation (vanishing pole trace) turns the Lefschetz trace into an absolute quantity read only
  by the defect.
* **Coboundaries.** The alignment deficit at a scale is half the absolute energy of the Adams
  coboundary: `δ(ψ_g x − x, ψ_g x − x) = 2c_x(0) − 2c_x(g)` (`ScalingDatum.defect_coboundary_self`).
* **Sign.** Under the orbit Hodge index every corrector `ξ ⋆ ξ′` has nonnegative primitive trace
  (`traceAt_rosati_nonneg`). The conservation law is an identity; its sign is the orientation.

So the conserved quantity asked for in the review is the Lefschetz trace of correctors: it carries
relative compensation to absolute energy at every scale, exactly, and leaves the sign — the
orientation of `x` — as the only open input.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri

namespace ScalingDatum

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ScalingDatum G E)

/-- The **Lefschetz trace** of a correspondence at a cycle: `Σ_g ξ(g) L(x, g)`. -/
def lefschetzTrace (x : E) (ξ : Correspondence G) : ℝ := ξ.sum fun g a => a * D.lefschetz x g

/-- The **pole trace** of a correspondence: `Σ_g ξ(g)(e^{s(g)} + 1)`. -/
def poleTrace (ξ : Correspondence G) : ℝ := ξ.sum fun g a => a * (Real.exp (D.scale g) + 1)

/-- The **primitive trace** at `x`: `Σ_g ξ(g) e^{s(g)/2} c_x(g)`. -/
def primTrace (x : E) (ξ : Correspondence G) : ℝ :=
  ξ.sum fun g a => a * (Real.exp (D.scale g / 2) * D.orbitCorr x g)

/-- **Lefschetz trace formula for correspondences.** -/
theorem lefschetzTrace_eq (x : E) (ξ : Correspondence G) :
    D.lefschetzTrace x ξ = D.poleTrace ξ * (D.pair x D.H * D.pair x D.V) - D.primTrace x ξ := by
  simp only [lefschetzTrace, poleTrace, primTrace, Finsupp.sum, D.lefschetz_eq, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  ring

/-- A **corrector**: a correspondence with vanishing pole trace. -/
def IsCorrector (ξ : Correspondence G) : Prop := D.poleTrace ξ = 0

/-- **The conservation law.** The Lefschetz trace of a corrector is minus its primitive trace. -/
theorem lefschetzTrace_of_corrector {ξ : Correspondence G} (hξ : D.IsCorrector ξ) (x : E) :
    D.lefschetzTrace x ξ = -D.primTrace x ξ := by
  rw [lefschetzTrace_eq, hξ, zero_mul, zero_sub]

/-- The orbit correlation does not see the pole plane. -/
theorem orbitCorr_add_pole (x : E) (a b : ℝ) (g : G) :
    D.orbitCorr (x + a • D.H + b • D.V) g = D.orbitCorr x g := by
  have hH' : ∀ z : E, D.defect (D.act g D.H) z = 0 := fun z => by
    rw [D.defect_act_left, D.defect_H_left]
  have hV' : ∀ z : E, D.defect (D.act g D.V) z = 0 := fun z => by
    rw [D.defect_act_left, D.defect_V_left]
  have hHr : ∀ z : E, D.defect z D.H = 0 := fun z => by rw [D.defect_comm, D.defect_H_left]
  have hVr : ∀ z : E, D.defect z D.V = 0 := fun z => by rw [D.defect_comm, D.defect_V_left]
  simp only [orbitCorr, map_add, map_smul, D.defect_add_left, D.defect_add_right,
    D.defect_smul_left, D.defect_smul_right, hH', hV', hHr, hVr, mul_zero, add_zero]

/-- **For a corrector the Lefschetz trace ignores the fibre degrees of the cycle**: it is the same
for `x` and for `x + aH + bV`. -/
theorem lefschetzTrace_of_corrector_add_pole {ξ : Correspondence G} (hξ : D.IsCorrector ξ)
    (x : E) (a b : ℝ) :
    D.lefschetzTrace (x + a • D.H + b • D.V) ξ = D.lefschetzTrace x ξ := by
  rw [D.lefschetzTrace_of_corrector hξ, D.lefschetzTrace_of_corrector hξ]
  simp only [primTrace, D.orbitCorr_add_pole]

/-- **The sign is the orientation.** Under the orbit Hodge index, the trace of `ξ ⋆ ξ′` at `x` is
nonnegative for every correspondence. -/
theorem traceAt_rosati_nonneg {x : E} (h : D.OrbitHodgeIndex x) (ξ : Correspondence G) :
    0 ≤ D.traceAt x (conv ξ (rosati ξ)) :=
  (D.rosatiPositive_iff_orbitHodgeIndex x).mpr h ξ

end ScalingDatum

end GaloisForLFunctions.ArithmeticOrientationGeometry
