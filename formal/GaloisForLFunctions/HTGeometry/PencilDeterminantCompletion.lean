/-
# Linear pencils: the determinant completion in several variables

At Schatten order two the completion fibre of a pencil `A : V → S₂` over a finite-dimensional
parameter space is `Sym¹(V*)`, the linear forms on `V`.  Nothing new has to be proved for that:
restricting the pencil to a coordinate axis turns the parameter into the spectral variable, because
a pencil is linear and rescaling a kernel rescales the spectral coordinate.  So the one-variable
theory applies along each axis, and the fibre coordinate is read off one coefficient at a time.

Main results:
* `pencilKernel`, `pencilKernel_axis` — the pencil and its restriction to an axis.
* `completedPencilDet`, `completedPencilDet_axis` — the completed determinant of a pencil, and its
  axis restriction as a one-variable completed determinant.
* `deriv_completedPencilDet_axis` — each coefficient of the linear jet is a derivative at the
  origin along the corresponding axis.
* `linearJet_eq_of_completedPencilDet_eq` — the fibre coordinate of a pencil is faithful.
* `tendsto_pencilJet` — multivariable necessity of the completion law at order two.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantScaling

open HilbertSchmidt Metric Filter

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [DecidableEq ι] {r : ℕ}

omit [DecidableEq ι] in
theorem isHS_zero : IsHS (0 : ι × ι → ℂ) := by
  simp [IsHS]

omit [DecidableEq ι] in
theorem isHS_finsetSum {κ : Type*} {s : Finset κ} {K : κ → (ι × ι → ℂ)}
    (h : ∀ i ∈ s, IsHS (K i)) : IsHS (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHS_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact isHS_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The kernel of a linear pencil at a parameter. -/
def pencilKernel (A : Fin r → (ι × ι → ℂ)) (v : Fin r → ℂ) : ι × ι → ℂ := ∑ i, v i • A i

omit [DecidableEq ι] in
theorem isHS_pencilKernel {A : Fin r → (ι × ι → ℂ)} (hA : ∀ i, IsHS (A i)) (v : Fin r → ℂ) :
    IsHS (pencilKernel A v) :=
  isHS_finsetSum fun i _ => (hA i).smul (v i)

omit [DecidableEq ι] in
/-- **Restricting a pencil to a coordinate axis** rescales the corresponding kernel. -/
theorem pencilKernel_axis (A : Fin r → (ι × ι → ℂ)) (i : Fin r) (t : ℂ) :
    pencilKernel A (t • Pi.single i (1 : ℂ)) = t • A i := by
  classical
  rw [pencilKernel, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The linear jet `P(v) = ∑ Pᵢ vᵢ`: the fibre coordinate at Schatten order two. -/
def linearJet (P : Fin r → ℂ) (v : Fin r → ℂ) : ℂ := ∑ i, P i * v i

omit [DecidableEq ι] in
theorem linearJet_axis (P : Fin r → ℂ) (i : Fin r) (t : ℂ) :
    linearJet P (t • Pi.single i (1 : ℂ)) = t * P i := by
  classical
  rw [linearJet, Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The completed determinant of a linear pencil, with its linear jet. -/
noncomputable def completedPencilDet (A : Fin r → (ι × ι → ℂ)) (P : Fin r → ℂ)
    (v : Fin r → ℂ) : ℂ :=
  entireDet2 (pencilKernel A v) 1 * Complex.exp (-(linearJet P v))

/-- **The axis restriction of a pencil completion is a one-variable completion.** -/
theorem completedPencilDet_axis {A : Fin r → (ι × ι → ℂ)} (hA : ∀ i, IsHS (A i))
    (P : Fin r → ℂ) (i : Fin r) (t : ℂ) :
    completedPencilDet A P (t • Pi.single i (1 : ℂ)) = completedDet2 (A i) (P i) t := by
  rw [completedPencilDet, pencilKernel_axis, linearJet_axis,
    congrFun (entireDet2_smul (hA i) t) 1, mul_one, completedDet2]

/-- **Each coefficient of the linear jet is a derivative at the origin.** -/
theorem deriv_completedPencilDet_axis {A : Fin r → (ι × ι → ℂ)} (hA : ∀ i, IsHS (A i))
    (P : Fin r → ℂ) (i : Fin r) :
    deriv (fun t : ℂ => completedPencilDet A P (t • Pi.single i (1 : ℂ))) 0 = -(P i) := by
  have hfun : (fun t : ℂ => completedPencilDet A P (t • Pi.single i (1 : ℂ)))
      = completedDet2 (A i) (P i) := funext fun t => completedPencilDet_axis hA P i t
  rw [hfun, deriv_completedDet2_zero (hA i)]

/-- **The fibre coordinate of a pencil is faithful.**  Two pencil completions that agree as
functions on the parameter space have the same linear jet. -/
theorem linearJet_eq_of_completedPencilDet_eq {A A' : Fin r → (ι × ι → ℂ)}
    (hA : ∀ i, IsHS (A i)) (hA' : ∀ i, IsHS (A' i)) {P P' : Fin r → ℂ}
    (h : completedPencilDet A P = completedPencilDet A' P') : P = P' := by
  funext i
  have h1 := deriv_completedPencilDet_axis hA P i
  have h2 := deriv_completedPencilDet_axis hA' P' i
  have hax : (fun t : ℂ => completedPencilDet A P (t • Pi.single i (1 : ℂ)))
      = fun t : ℂ => completedPencilDet A' P' (t • Pi.single i (1 : ℂ)) := by
    funext t
    exact congrFun h _
  rw [hax, h2] at h1
  exact neg_injective h1.symm

/-- **Multivariable necessity of the determinant-completion law at Schatten order two.**  If the
pencils converge coefficientwise in Hilbert--Schmidt norm and the completed determinants converge
locally uniformly along each coordinate axis, then every coefficient of the linear jet converges,
and the limit along that axis is the completed determinant of the limiting kernel. -/
theorem tendsto_pencilJet (A : ℕ → Fin r → (ι × ι → ℂ)) (A₀ : Fin r → (ι × ι → ℂ))
    (hA : ∀ n i, IsHS (A n i)) (hA₀ : ∀ i, IsHS (A₀ i))
    (hlim : ∀ i, Tendsto (fun n => hsNorm (A n i - A₀ i)) atTop (nhds 0))
    (P : ℕ → Fin r → ℂ) (G : Fin r → ℂ → ℂ)
    (hG : ∀ i, TendstoLocallyUniformlyOn
      (fun n => fun t : ℂ => completedPencilDet (A n) (P n) (t • Pi.single i (1 : ℂ)))
      (G i) atTop Set.univ) (i : Fin r) :
    Tendsto (fun n => P n i) atTop (nhds (-deriv (G i) 0)) ∧
      G i = completedDet2 (A₀ i) (-deriv (G i) 0) := by
  have hEq : (fun n => fun t : ℂ => completedPencilDet (A n) (P n) (t • Pi.single i (1 : ℂ)))
      = fun n => completedDet2 (A n i) (P n i) := by
    funext n
    exact funext fun t => completedPencilDet_axis (fun j => hA n j) (P n) i t
  have hGi := hG i
  rw [hEq] at hGi
  exact tendsto_completionCoefficient (fun n => A n i) (A₀ i) (fun n => hA n i) (hA₀ i)
    (hlim i) (fun n => P n i) (G i) hGi

end GaloisForLFunctions.HTGeometry
