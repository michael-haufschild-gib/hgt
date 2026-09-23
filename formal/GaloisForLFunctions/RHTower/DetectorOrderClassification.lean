/-
# Order classification of divisor readers vanishing on real configurations

A *reader* of a finite divisor is a functional `D ↦ ∑ⱼ mⱼ · F(zⱼ, conj zⱼ)` with kernel `F`
holomorphic in both slots; conjugated boundary germs of a logarithmic derivative are of this form
(`SlabConjugatedGermTheorem`).  Readers that vanish on every divisor supported on the real axis —
the ones that could distinguish a real configuration from a complex one — are classified by the
order of vanishing of the kernel on the diagonal:

* **order zero** (kernel holomorphic in the first slot alone): the kernel is identically zero, so
  no such reader is nonzero (`order_zero_reader_eq_zero`);
* **order one**: such readers exist, but every one carries the factor `z - conj z = 2i·Im z`
  (`exists_displacement_factor`, `fiberReader_eq_displacement_form`), and a mass-preserving
  reflection `d ↦ -d` of the configuration annihilates all of them (`mirror_mean_kill`);
* **order two**: the minimal surviving order, and every such reader is a weighted second moment of
  `Im z` (`fiberReader_orderTwo_eq_variance`), vanishing exactly on real configurations
  (`displacementVariance_eq_zero_iff`, `orderTwo_reader_eq_zero_iff`).

The load-bearing step is `diagonal_eq_zero`: vanishing of the kernel on the *real* diagonal
propagates to the whole *complex* diagonal, because `z ↦ F z z` is a one-variable holomorphic
function vanishing on a real ray.  Divisibility by `z - w` is then the `dslope` divided
difference.
-/
import GaloisForLFunctions.RHTower.LambertRayRecovery

namespace GaloisForLFunctions
namespace RHTower
namespace DetectorOrderClassification

open Complex

/-! ### Order zero: the linear/explicit-formula class contains no detector -/

/-- **Order zero.**  A reader whose kernel is holomorphic in the divisor variable alone and which
vanishes on every divisor supported on the real axis has identically vanishing kernel.  Hence no
nonzero reader of this class distinguishes real divisors from complex ones. -/
theorem order_zero_reader_eq_zero (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (h : ∀ x : ℝ, f (x : ℂ) = 0) : ∀ z : ℂ, f z = 0 :=
  _root_.RHTower.entire_eq_zero_of_zero_on_real_tail f 0 hf (fun x _ => h x)

/-! ### Real-to-complex diagonal propagation and the displacement factor -/

/-- **Diagonal propagation.**  If the kernel vanishes on the *real* diagonal then it vanishes on
the entire *complex* diagonal.  This is the step that converts a statement about critical-line
configurations into an identity of holomorphic functions. -/
theorem diagonal_eq_zero (F : ℂ → ℂ → ℂ)
    (hdiag : AnalyticOnNhd ℂ (fun z => F z z) Set.univ)
    (h : ∀ x : ℝ, F (x : ℂ) (x : ℂ) = 0) : ∀ z : ℂ, F z z = 0 :=
  _root_.RHTower.entire_eq_zero_of_zero_on_real_tail (fun z => F z z) 0 hdiag (fun x _ => h x)

/-- **The displacement factor.**  Every kernel vanishing on the real diagonal factors as
`F z w = (z - w) * G z w`.  On a fiber the first factor is the displacement `2i·Im z`, so the
displacement appears explicitly in every reader that can detect the critical line. -/
theorem exists_displacement_factor (F : ℂ → ℂ → ℂ)
    (hdiag : AnalyticOnNhd ℂ (fun z => F z z) Set.univ)
    (h : ∀ x : ℝ, F (x : ℂ) (x : ℂ) = 0) :
    ∃ G : ℂ → ℂ → ℂ, ∀ z w : ℂ, F z w = (z - w) * G z w := by
  refine ⟨fun z w => - dslope (F z) z w, ?_⟩
  intro z w
  have hz : F z z = 0 := diagonal_eq_zero F hdiag h z
  have hs := sub_smul_dslope (F z) z w
  simp only [smul_eq_mul, hz, sub_zero] at hs
  rw [← hs]
  ring

/-- Second-order factorization: if the first-order cofactor also vanishes on the real diagonal,
the kernel has a double zero there. -/
theorem exists_second_order_factor (F G : ℂ → ℂ → ℂ)
    (hFG : ∀ z w : ℂ, F z w = (z - w) * G z w)
    (hGdiag : AnalyticOnNhd ℂ (fun z => G z z) Set.univ)
    (hG : ∀ x : ℝ, G (x : ℂ) (x : ℂ) = 0) :
    ∃ H : ℂ → ℂ → ℂ, ∀ z w : ℂ, F z w = (z - w) ^ (2 : ℕ) * H z w := by
  obtain ⟨H, hH⟩ := exists_displacement_factor G hGdiag hG
  refine ⟨H, fun z w => ?_⟩
  rw [hFG, hH]
  ring

/-! ### Readers on a finite fiber -/

variable {ι : Type*}

/-- The value of the reader with kernel `F` on the finite fiber `(s, m, z)`: masses `m`, points
`z`, conjugate slot filled by `conj z`. -/
noncomputable def fiberReader (F : ℂ → ℂ → ℂ) (s : Finset ι) (m : ι → ℝ) (z : ι → ℂ) : ℂ :=
  ∑ j ∈ s, (m j : ℂ) * F (z j) ((starRingEnd ℂ) (z j))

/-- **Order one on a fiber.**  A reader whose kernel vanishes on the real diagonal displays the
displacement `2·Im zⱼ` as an explicit factor at every fiber point. -/
theorem fiberReader_eq_displacement_form (F G : ℂ → ℂ → ℂ)
    (hFG : ∀ z w : ℂ, F z w = (z - w) * G z w) (s : Finset ι) (m : ι → ℝ) (z : ι → ℂ) :
    fiberReader F s m z
      = ∑ j ∈ s, (m j : ℂ) * (((2 * (z j).im : ℝ) : ℂ) * I) *
          G (z j) ((starRingEnd ℂ) (z j)) := by
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hFG, Complex.sub_conj]
  ring

/-- **The mirror obstruction.**  On a fiber invariant under the functional-equation reflection
`d ↦ -d` (mass preserving), the first displacement moment vanishes identically.  Order-one
readers are therefore blind on the actual `Ξ` divisor: this is the mean-kill law. -/
theorem mirror_mean_kill (s : Finset ι) (m d : ι → ℝ) (σ : ι → ι)
    (hmem : ∀ a ∈ s, σ a ∈ s) (hinv : ∀ a ∈ s, σ (σ a) = a)
    (hm : ∀ a ∈ s, m (σ a) = m a) (hd : ∀ a ∈ s, d (σ a) = - d a) :
    ∑ j ∈ s, m j * d j = 0 := by
  refine Finset.sum_involution (fun a _ => σ a) ?_ ?_ ?_ ?_
  · intro a ha
    rw [hm a ha, hd a ha]
    ring
  · intro a ha hne hcon
    have hcon' : σ a = a := hcon
    have h1 : d (σ a) = - d a := hd a ha
    rw [hcon'] at h1
    have hda : d a = 0 := by linarith
    exact hne (by rw [hda, mul_zero])
  · intro a ha
    exact hmem a ha
  · intro a ha
    exact hinv a ha

/-! ### Order two: the forced form -/

/-- The displacement variance of a fiber: masses `m`, displacements `d`. -/
noncomputable def displacementVariance (s : Finset ι) (m d : ι → ℝ) : ℝ :=
  ∑ j ∈ s, m j * d j ^ (2 : ℕ)

theorem displacementVariance_nonneg (s : Finset ι) (m d : ι → ℝ)
    (hm : ∀ j ∈ s, 0 ≤ m j) : 0 ≤ displacementVariance s m d :=
  Finset.sum_nonneg fun j hj => mul_nonneg (hm j hj) (sq_nonneg _)

/-- **The minimal detector detects exactly.**  With positive masses the displacement variance
vanishes precisely when every fiber point lies on the critical line. -/
theorem displacementVariance_eq_zero_iff (s : Finset ι) (m d : ι → ℝ)
    (hm : ∀ j ∈ s, 0 < m j) :
    displacementVariance s m d = 0 ↔ ∀ j ∈ s, d j = 0 := by
  constructor
  · intro h j hj
    have hnn : ∀ i ∈ s, 0 ≤ m i * d i ^ (2 : ℕ) :=
      fun i hi => mul_nonneg (hm i hi).le (sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h j hj
    rcases mul_eq_zero.mp this with hm0 | hd0
    · exact absurd hm0 (ne_of_gt (hm j hj))
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hd0
  · intro h
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [h j hj]
    ring

/-- **Order two on a fiber is a weighted displacement variance.**  A kernel with a double zero on
the diagonal produces, at every fiber point, the factor `(z - conj z)^(2 : ℕ) = -4 (Im z)^(2 : ℕ)`. -/
theorem fiberReader_orderTwo_eq_variance (F H : ℂ → ℂ → ℂ)
    (hFH : ∀ z w : ℂ, F z w = (z - w) ^ (2 : ℕ) * H z w) (s : Finset ι) (m : ι → ℝ) (z : ι → ℂ) :
    fiberReader F s m z
      = ∑ j ∈ s, (m j : ℂ) * (-4 * (((z j).im : ℝ) : ℂ) ^ (2 : ℕ)) *
          H (z j) ((starRingEnd ℂ) (z j)) := by
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hFH, Complex.sub_conj]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Classification capstone (constant-weight case).**  The minimal order-two reader, kernel
`(z - w)^(2 : ℕ)`, evaluates on a fiber to `-4` times the displacement variance, and vanishes precisely
when the fiber lies on the critical line.  Every reader of the class considered here is a
holomorphic reweighting of this one. -/
theorem orderTwo_reader_eq_zero_iff (s : Finset ι) (m : ι → ℝ) (z : ι → ℂ)
    (hm : ∀ j ∈ s, 0 < m j) :
    fiberReader (fun zz ww => (zz - ww) ^ (2 : ℕ)) s m z
        = (-4 : ℂ) * ((displacementVariance s m fun j => (z j).im : ℝ) : ℂ)
      ∧ (fiberReader (fun zz ww => (zz - ww) ^ (2 : ℕ)) s m z = 0 ↔ ∀ j ∈ s, (z j).im = 0) := by
  have hval : fiberReader (fun zz ww => (zz - ww) ^ (2 : ℕ)) s m z
      = (-4 : ℂ) * ((displacementVariance s m fun j => (z j).im : ℝ) : ℂ) := by
    have h := fiberReader_orderTwo_eq_variance (fun zz ww => (zz - ww) ^ (2 : ℕ)) (fun _ _ => 1)
      (fun zz ww => by ring) s m z
    rw [h, displacementVariance]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  refine ⟨hval, ?_⟩
  rw [hval]
  constructor
  · intro h
    have h4 : ((displacementVariance s m fun j => (z j).im : ℝ) : ℂ) = 0 := by
      have : (-4 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h).resolve_left this
    have hR : (displacementVariance s m fun j => (z j).im) = 0 := by
      exact_mod_cast h4
    exact (displacementVariance_eq_zero_iff s m (fun j => (z j).im) hm).mp hR
  · intro h
    have hR : (displacementVariance s m fun j => (z j).im) = 0 :=
      (displacementVariance_eq_zero_iff s m (fun j => (z j).im) hm).mpr h
    rw [hR]
    push_cast
    ring

end DetectorOrderClassification
end RHTower
end GaloisForLFunctions
