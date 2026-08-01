import GaloisForLFunctions.RHTower.SuzukiFixedLatticeRigidity

/-!
# The Clark reconstruction for a finite aperture

Fixed-lattice rigidity holds for any carrier class whose lattice jets determine its boundary
Herglotz function.  This module exhibits that reconstruction concretely in the finite-aperture case:
the Donoghue transform of a finite atomic spectral measure.

Given finitely many physical points with positive masses, the transform

`m(z) = sum_j w_j K_z (x_j)`

is a Herglotz function, because every kernel value has positive imaginary part above the real axis
and the masses are positive.  On the real axis away from the atoms it is real, so it is a genuine
boundary Herglotz function, and it depends on nothing but the jets.

Feeding it into the assembled rigidity theorem gives fixed-lattice rigidity for the finite-aperture
Clark class with no abstract reconstruction parameter left.
-/

namespace GaloisForLFunctions.RHTower

open Finset GaloisForLFunctions.HTGeometry

/-- The Donoghue kernel at a real spectral parameter, as a real-valued function. -/
noncomputable def donoghueRealKernel (s t : ℝ) : ℝ := t + (t ^ 2 + 1) / (s - t)

/-- At a real spectral parameter off the atom, the kernel is the real one. -/
theorem suzukiDonoghueKernel_ofReal {s t : ℝ} (h : s ≠ t) :
    suzukiDonoghueKernel s ((t : ℝ) : ℂ) = ((donoghueRealKernel s t : ℝ) : ℂ) := by
  have hne : ((s : ℂ) - (t : ℂ)) ≠ 0 := by
    intro hc
    apply h
    have : (s : ℂ) = (t : ℂ) := by linear_combination hc
    exact_mod_cast this
  rw [suzukiDonoghueKernel, donoghueRealKernel]
  push_cast
  ring

/-- The Donoghue transform of a finite atomic spectral measure. -/
noncomputable def clarkFiniteHerglotz {ι : Type*} [Fintype ι] (w x : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ j, (w j : ℂ) * suzukiDonoghueKernel (x j) z

/-- Its boundary function, real-valued off the atoms. -/
noncomputable def clarkFiniteReconstruction {ι : Type*} [Fintype ι] (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ j, w j * donoghueRealKernel (x j) t

/-- **The finite Clark reconstruction is a Herglotz function.**  Every kernel value lies strictly
above the real axis and the masses are positive, so the sum does too. -/
theorem im_clarkFiniteHerglotz_pos {ι : Type*} [Fintype ι] [Nonempty ι] {w x : ι → ℝ}
    (hw : ∀ j, 0 < w j) {z : ℂ} (hz : 0 < z.im) : 0 < (clarkFiniteHerglotz w x z).im := by
  have hterm : ∀ j : ι, 0 < ((w j : ℂ) * suzukiDonoghueKernel (x j) z).im := by
    intro j
    have hk := im_suzukiDonoghueKernel_pos hz (x j)
    have hre : ((w j : ℂ) * suzukiDonoghueKernel (x j) z).im
        = w j * (suzukiDonoghueKernel (x j) z).im := by
      simp [Complex.mul_im]
    rw [hre]
    exact mul_pos (hw j) hk
  have hsum : (clarkFiniteHerglotz w x z).im
      = ∑ j, ((w j : ℂ) * suzukiDonoghueKernel (x j) z).im := by
    rw [clarkFiniteHerglotz, Complex.im_sum]
  rw [hsum]
  exact Finset.sum_pos (fun j _ => hterm j) Finset.univ_nonempty

/-- On the real axis off every atom the transform is the real reconstruction. -/
theorem clarkFiniteHerglotz_ofReal {ι : Type*} [Fintype ι] {w x : ι → ℝ} {t : ℝ}
    (h : ∀ j, x j ≠ t) :
    clarkFiniteHerglotz w x ((t : ℝ) : ℂ) = ((clarkFiniteReconstruction w x t : ℝ) : ℂ) := by
  rw [clarkFiniteHerglotz, clarkFiniteReconstruction, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [suzukiDonoghueKernel_ofReal (h j), Complex.ofReal_mul]

/-- The reconstruction depends on nothing but the jets. -/
theorem clarkFiniteReconstruction_congr {ι : Type*} [Fintype ι] {w₁ x₁ w₂ x₂ : ι → ℝ}
    (hw : w₁ = w₂) (hx : x₁ = x₂) :
    clarkFiniteReconstruction w₁ x₁ = clarkFiniteReconstruction w₂ x₂ := by
  rw [hw, hx]

/-- **`(19)` for the finite-aperture Clark class.**  Two reflection-normalized continuous phases
whose boundary Herglotz functions are the Donoghue transforms of their own finite jet data, with
equal jets, are equal.  No abstract reconstruction parameter remains: the reconstruction is the
explicit finite Donoghue transform. -/
theorem suzuki_fixedLattice_rigidity_finiteAperture {ι : Type*} [Fintype ι]
    {φ₁ φ₂ : ℝ → ℝ} {w₁ x₁ w₂ x₂ : ι → ℝ}
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ t, φ₁ (-t) = 2 * Real.pi - φ₁ t) (hr₂ : ∀ t, φ₂ (-t) = 2 * Real.pi - φ₂ t)
    (hl₁ : ∀ t, Complex.exp ((φ₁ t : ℂ) * Complex.I)
      = cayleyOfHerglotz ((clarkFiniteReconstruction w₁ x₁ t : ℝ) : ℂ))
    (hl₂ : ∀ t, Complex.exp ((φ₂ t : ℂ) * Complex.I)
      = cayleyOfHerglotz ((clarkFiniteReconstruction w₂ x₂ t : ℝ) : ℂ))
    (hw : w₁ = w₂) (hx : x₁ = x₂) : φ₁ = φ₂ :=
  phase_eq_of_boundaryHerglotz_eq hc₁ hc₂ hr₁ hr₂ hl₁ hl₂
    (clarkFiniteReconstruction_congr hw hx)

/-! ## The phase equation holds only off the atoms

The boundary Herglotz function has a pole at every atom, so no carrier carrying atoms can satisfy
the phase equation *at* an atom.  Requiring it everywhere therefore admits only the atomless case.
The correct hypothesis asks for it off the atoms; since both exponentials are continuous and the
atom set is finite, density recovers the equation everywhere. -/

/-- The complement of a finite subset of the line is dense. -/
theorem dense_compl_of_finite {s : Set ℝ} (hs : s.Finite) : Dense sᶜ := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  by_contra hcon
  have hsub : U ⊆ s := by
    intro y hy
    by_contra hys
    exact hcon ⟨y, hy, hys⟩
  have hIoo : Set.Ioo (x - ε) (x + ε) ⊆ s := by
    intro y hy
    refine hsub (hball ?_)
    rw [Real.ball_eq_Ioo]
    exact hy
  exact (Set.Ioo_infinite (by linarith)) (hs.subset hIoo)

/-- **Rigidity with the phase equation only off the atoms.**  Both exponentials are continuous, so
agreement on a dense set is agreement everywhere. -/
theorem phase_eq_of_boundaryHerglotz_eq_off {φ₁ φ₂ m₁ m₂ : ℝ → ℝ} {S : Set ℝ}
    (hS : Dense Sᶜ) (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ t, φ₁ (-t) = 2 * Real.pi - φ₁ t) (hr₂ : ∀ t, φ₂ (-t) = 2 * Real.pi - φ₂ t)
    (hl₁ : ∀ t ∈ Sᶜ, Complex.exp ((φ₁ t : ℂ) * Complex.I) = cayleyOfHerglotz ((m₁ t : ℝ) : ℂ))
    (hl₂ : ∀ t ∈ Sᶜ, Complex.exp ((φ₂ t : ℂ) * Complex.I) = cayleyOfHerglotz ((m₂ t : ℝ) : ℂ))
    (hm : m₁ = m₂) : φ₁ = φ₂ := by
  have hcont₁ : Continuous (fun t : ℝ => Complex.exp ((φ₁ t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hc₁).mul continuous_const)
  have hcont₂ : Continuous (fun t : ℝ => Complex.exp ((φ₂ t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hc₂).mul continuous_const)
  have heq : (fun t : ℝ => Complex.exp ((φ₁ t : ℂ) * Complex.I))
      = fun t : ℝ => Complex.exp ((φ₂ t : ℂ) * Complex.I) := by
    refine Continuous.ext_on hS hcont₁ hcont₂ ?_
    intro t ht
    show Complex.exp ((φ₁ t : ℂ) * Complex.I) = Complex.exp ((φ₂ t : ℂ) * Complex.I)
    rw [hl₁ t ht, hl₂ t ht, hm]
  exact eq_of_exp_eq_of_reflection hc₁ hc₂ hr₁ hr₂ (fun x => congrFun heq x)

/-- **`(19)` for the finite-aperture Clark class, usable form.**  The phase equation is required
only away from the atoms, which is the most any carrier with atoms can satisfy. -/
theorem suzuki_fixedLattice_rigidity_finiteAperture_offAtoms {ι : Type*} [Fintype ι]
    {φ₁ φ₂ : ℝ → ℝ} {w₁ x₁ w₂ x₂ : ι → ℝ}
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ t, φ₁ (-t) = 2 * Real.pi - φ₁ t) (hr₂ : ∀ t, φ₂ (-t) = 2 * Real.pi - φ₂ t)
    (hl₁ : ∀ t, (∀ j, x₁ j ≠ t) → Complex.exp ((φ₁ t : ℂ) * Complex.I)
      = cayleyOfHerglotz ((clarkFiniteReconstruction w₁ x₁ t : ℝ) : ℂ))
    (hl₂ : ∀ t, (∀ j, x₂ j ≠ t) → Complex.exp ((φ₂ t : ℂ) * Complex.I)
      = cayleyOfHerglotz ((clarkFiniteReconstruction w₂ x₂ t : ℝ) : ℂ))
    (hw : w₁ = w₂) (hx : x₁ = x₂) : φ₁ = φ₂ := by
  have hfin : (Set.range x₁ ∪ Set.range x₂).Finite :=
    (Set.finite_range x₁).union (Set.finite_range x₂)
  refine phase_eq_of_boundaryHerglotz_eq_off (dense_compl_of_finite hfin) hc₁ hc₂ hr₁ hr₂
    ?_ ?_ (clarkFiniteReconstruction_congr hw hx)
  · intro t ht
    refine hl₁ t fun j hj => ht ?_
    exact Or.inl ⟨j, hj⟩
  · intro t ht
    refine hl₂ t fun j hj => ht ?_
    exact Or.inr ⟨j, hj⟩

/-! ## A symmetric configuration gives an odd boundary function

The reflection normalization is exactly oddness of the boundary Herglotz function, and the origin
can never be an atom.  A spectral configuration that straddles the origin symmetrically delivers
both: reflecting the atoms and keeping the masses negates the reconstruction. -/

/-- Reflecting both the atom and the argument negates the kernel. -/
theorem donoghueRealKernel_neg (s t : ℝ) :
    donoghueRealKernel (-s) (-t) = -donoghueRealKernel s t := by
  rw [donoghueRealKernel, donoghueRealKernel]
  have h1 : (-s) - (-t) = -(s - t) := by ring
  have h2 : (-t) ^ 2 + 1 = t ^ 2 + 1 := by ring
  rw [h1, h2, div_neg]
  ring

/-- **A symmetric spectral configuration has an odd boundary Herglotz function.**  If some
involution of the index set reflects the atoms and preserves the masses, the reconstruction is odd —
hence, by `exp_reflection_of_odd`, compatible with the Suzuki reflection normalization. -/
theorem clarkFiniteReconstruction_odd {ι : Type*} [Fintype ι] {w x : ι → ℝ}
    (σ : Equiv.Perm ι) (hx : ∀ j, x (σ j) = -x j) (hw : ∀ j, w (σ j) = w j) (t : ℝ) :
    clarkFiniteReconstruction w x (-t) = -clarkFiniteReconstruction w x t := by
  rw [clarkFiniteReconstruction, clarkFiniteReconstruction, ← Finset.sum_neg_distrib,
    ← Equiv.sum_comp σ (fun j => w j * donoghueRealKernel (x j) (-t))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hw, hx, donoghueRealKernel_neg]
  ring

/-- The smallest admissible configuration: a symmetric pair of atoms at `±a` with equal masses. -/
theorem clarkFiniteReconstruction_symmetricPair_odd (a w0 : ℝ) (t : ℝ) :
    clarkFiniteReconstruction (fun _ : Bool => w0) (fun b : Bool => if b then a else -a) (-t)
      = -clarkFiniteReconstruction (fun _ : Bool => w0)
          (fun b : Bool => if b then a else -a) t := by
  refine clarkFiniteReconstruction_odd (Equiv.swap true false) ?_ ?_ t
  · intro b
    cases b <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · intro b
    rfl

/-! ## The class is inhabited

The rigidity theorem above would say nothing if no carrier satisfied its hypotheses.  The empty
aperture does: with no atoms the reconstruction vanishes, and the constant phase `pi` is a
continuous reflection-normalized lift of it.  This is degenerate, but it establishes that the
hypothesis class is not empty. -/

theorem clarkFiniteReconstruction_empty (w x : Empty → ℝ) (t : ℝ) :
    clarkFiniteReconstruction w x t = 0 := by
  simp [clarkFiniteReconstruction]

theorem cayleyOfHerglotz_zero : cayleyOfHerglotz (0 : ℂ) = -1 := by
  rw [cayleyOfHerglotz, zero_sub, zero_add, neg_div, div_self Complex.I_ne_zero]

/-- The finite-aperture Clark hypotheses are satisfiable. -/
theorem exists_clarkFinite_carrier :
    ∃ (φ : ℝ → ℝ) (w x : Empty → ℝ), Continuous φ ∧
      (∀ t, φ (-t) = 2 * Real.pi - φ t) ∧
      (∀ t, Complex.exp ((φ t : ℂ) * Complex.I)
        = cayleyOfHerglotz ((clarkFiniteReconstruction w x t : ℝ) : ℂ)) := by
  refine ⟨fun _ => Real.pi, Empty.elim, Empty.elim, continuous_const, fun t => by ring, ?_⟩
  intro t
  rw [clarkFiniteReconstruction_empty, Complex.ofReal_zero, cayleyOfHerglotz_zero]
  exact Complex.exp_pi_mul_I

end GaloisForLFunctions.RHTower
