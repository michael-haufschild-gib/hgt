import GaloisForLFunctions.HTGeometry.WaveDirectionalCalculus

/-!
# The energy flux of the clock equation

The energy of a wave field on a time slice is the integral of

`(∂ₜu)² + ∑ᵢ(∂ᵢu)² + u²`.

Its time derivative is computed pointwise by the product rule and then integrated. Two of the three
resulting terms cancel: the equation turns `∂ₜu·∂ₜ²u` into `∂ₜu·(Δu + Vu)`, the symmetry of mixed
second derivatives turns `∑ᵢ∂ᵢu·∂ₜ∂ᵢu` into `∑ᵢ∂ᵢu·∂ᵢ∂ₜu`, and the Green identity turns that into
`-∫Δu·∂ₜu`. What is left is the zeroth-order term alone,

`∫ ∂ₜ(energy density) = 2∫ (V+1)·u·∂ₜu`,

which is the estimate's engine: no derivative of `u` survives on the right.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Flux

variable {d : ℕ}

/-- The clock equation in time-space coordinates. -/
def SolvesWaveEq (u V : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ∀ p : ℝ × (Fin d → ℝ), dirDeriv (timeDir d) (dirDeriv (timeDir d) u) p
    = (∑ i : Fin d, dirDeriv (spaceDir d i) (dirDeriv (spaceDir d i) u) p) + V p * u p

/-- The energy density of a wave field. -/
noncomputable def energyDensity (u : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  (dirDeriv (timeDir d) u p) ^ 2 + (∑ i : Fin d, (dirDeriv (spaceDir d i) u p) ^ 2) + (u p) ^ 2

/-! ## The product rule for a directional derivative -/

theorem dirDeriv_mul {f g : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v p : ℝ × (Fin d → ℝ)) :
    dirDeriv v (fun q => f q * g q) p = dirDeriv v f p * g p + f p * dirDeriv v g p := by
  have hd : HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => f q * g q)
      (f p • fderiv ℝ g p + g p • fderiv ℝ f p) p :=
    (differentiableAt_of_contDiff_infty' hf p).hasFDerivAt.mul
      (differentiableAt_of_contDiff_infty' hg p).hasFDerivAt
  rw [dirDeriv, hd.fderiv]
  simp [dirDeriv]
  ring

theorem dirDeriv_sq {f : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (v p : ℝ × (Fin d → ℝ)) :
    dirDeriv v (fun q => (f q) ^ 2) p = 2 * (f p * dirDeriv v f p) := by
  have hsq : (fun q : ℝ × (Fin d → ℝ) => (f q) ^ 2) = fun q => f q * f q := by
    funext q; ring
  rw [hsq, dirDeriv_mul hf hf v p]
  ring

theorem dirDeriv_add {f g : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v p : ℝ × (Fin d → ℝ)) :
    dirDeriv v (fun q => f q + g q) p = dirDeriv v f p + dirDeriv v g p := by
  have hd : HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => f q + g q)
      (fderiv ℝ f p + fderiv ℝ g p) p :=
    (differentiableAt_of_contDiff_infty' hf p).hasFDerivAt.add
      (differentiableAt_of_contDiff_infty' hg p).hasFDerivAt
  rw [dirDeriv, hd.fderiv]
  simp [dirDeriv]

theorem dirDeriv_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ × (Fin d → ℝ) → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (v p : ℝ × (Fin d → ℝ)) :
    dirDeriv v (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, dirDeriv v (F i) p := by
  classical
  induction s using Finset.induction with
  | empty => simp [dirDeriv]
  | insert a s ha ih =>
    have hsum : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => ∑ i ∈ s, F i q :=
      ContDiff.sum fun i _ => hF i
    have hstep : (fun q : ℝ × (Fin d → ℝ) => ∑ i ∈ insert a s, F i q)
        = fun q => F a q + ∑ i ∈ s, F i q := by
      funext q
      rw [Finset.sum_insert ha]
    rw [hstep, dirDeriv_add (hF a) hsum v p, ih, Finset.sum_insert ha]

/-! ## The pointwise expansion -/

theorem dirDeriv_energyDensity {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (p : ℝ × (Fin d → ℝ)) :
    dirDeriv (timeDir d) (energyDensity u) p
      = 2 * (dirDeriv (timeDir d) u p * dirDeriv (timeDir d) (dirDeriv (timeDir d) u) p)
        + (∑ i : Fin d, 2 * (dirDeriv (spaceDir d i) u p
            * dirDeriv (timeDir d) (dirDeriv (spaceDir d i) u) p))
        + 2 * (u p * dirDeriv (timeDir d) u p) := by
  have h1 : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => (dirDeriv (timeDir d) u q) ^ 2 :=
    (contDiff_dirDeriv hu _).pow 2
  have h2 : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) =>
      ∑ i : Fin d, (dirDeriv (spaceDir d i) u q) ^ 2 :=
    ContDiff.sum fun i _ => (contDiff_dirDeriv hu _).pow 2
  have h3 : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => (u q) ^ 2 := hu.pow 2
  have hsplit : energyDensity u = fun q : ℝ × (Fin d → ℝ) =>
      ((dirDeriv (timeDir d) u q) ^ 2 + ∑ i : Fin d, (dirDeriv (spaceDir d i) u q) ^ 2)
        + (u q) ^ 2 := rfl
  rw [hsplit, dirDeriv_add (h1.add h2) h3, dirDeriv_add h1 h2,
    dirDeriv_sq (contDiff_dirDeriv hu _), dirDeriv_sq hu,
    dirDeriv_sum Finset.univ (fun i => (contDiff_dirDeriv hu (spaceDir d i)).pow 2)]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact dirDeriv_sq (contDiff_dirDeriv hu (spaceDir d i)) _ p

/-! ## The flux identity -/

section Integral

variable {u V : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

/-- The time slice of a field. -/
noncomputable def slice (u : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => u (t, x)

theorem contDiff_slice (hu : ContDiff ℝ ∞ u) (t : ℝ) : ContDiff ℝ ∞ (slice u t) := by
  have hmap : ContDiff ℝ ∞ fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
  exact hu.comp hmap

theorem hasCompactSupport_slice (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (t : ℝ) :
    HasCompactSupport (slice u t) :=
  HasCompactSupport.intro hK fun x hx => hzero (t, x) hx

theorem dirDeriv_zero_of_notMem (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (v : ℝ × (Fin d → ℝ))
    (p : ℝ × (Fin d → ℝ)) (hp : p.2 ∉ K) : dirDeriv v u p = 0 := by
  refine dirDeriv_eq_zero_of_notMem (S := Set.univ ×ˢ K) (isClosed_univ.prod hK.isClosed)
    (fun q hq => hzero q fun hq2 => hq ⟨Set.mem_univ _, hq2⟩) ?_ v
  intro hmem
  exact hp hmem.2

theorem slice_dirDeriv_spaceDir (hu : ContDiff ℝ ∞ u) (i : Fin d) (t : ℝ) :
    slice (dirDeriv (spaceDir d i) u) t = coordPartial i (slice u t) := by
  funext x
  exact dirDeriv_spaceDir_eq hu i t x

/-- **The energy flux identity.** After integration over a slice the two derivative terms cancel:
the equation turns the second time derivative into the Laplacian plus the potential term, the
symmetry of mixed partials turns the gradient term into the same Laplacian with the opposite sign
by the Green identity, and only the zeroth-order term survives. -/
theorem integral_dirDeriv_energyDensity (hu : ContDiff ℝ ∞ u) (hV : Continuous V)
    (hK : IsCompact K) (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0)
    (hsolve : SolvesWaveEq u V) (t : ℝ) :
    (∫ x : Fin d → ℝ, dirDeriv (timeDir d) (energyDensity u) (t, x))
      = 2 * ∫ x : Fin d → ℝ,
          (V (t, x) + 1) * (u (t, x) * dirDeriv (timeDir d) u (t, x)) := by
  classical
  set f : (Fin d → ℝ) → ℝ := slice u t with hf
  set g : (Fin d → ℝ) → ℝ := slice (dirDeriv (timeDir d) u) t with hg
  have hfcd : ContDiff ℝ ∞ f := contDiff_slice hu t
  have hgcd : ContDiff ℝ ∞ g := contDiff_slice (contDiff_dirDeriv hu _) t
  have hfs : HasCompactSupport f := hasCompactSupport_slice hK hzero t
  have hgs : HasCompactSupport g :=
    HasCompactSupport.intro hK fun x hx => dirDeriv_zero_of_notMem hK hzero _ (t, x) hx
  -- the pointwise expansion
  have hpt : ∀ x : Fin d → ℝ, dirDeriv (timeDir d) (energyDensity u) (t, x)
      = 2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x)
        + (∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
        + 2 * ((V (t, x) + 1) * (f x * g x)) := by
    intro x
    have hexp := dirDeriv_energyDensity hu (t, x)
    have heq := hsolve (t, x)
    have hgeta : (fun y : Fin d → ℝ => dirDeriv (timeDir d) u (t, y)) = g := rfl
    have hspeta : ∀ i : Fin d, (fun y : Fin d → ℝ => dirDeriv (spaceDir d i) u (t, y))
        = coordPartial i f := by
      intro i
      funext y
      exact dirDeriv_spaceDir_eq hu i t y
    have hlap : ∀ i : Fin d, dirDeriv (spaceDir d i) (dirDeriv (spaceDir d i) u) (t, x)
        = coordPartial i (coordPartial i f) x := by
      intro i
      rw [dirDeriv_spaceDir_eq (contDiff_dirDeriv hu _) i t x, hspeta i]
    have hmix : ∀ i : Fin d, dirDeriv (timeDir d) (dirDeriv (spaceDir d i) u) (t, x)
        = coordPartial i g x := by
      intro i
      rw [dirDeriv_comm hu, dirDeriv_spaceDir_eq (contDiff_dirDeriv hu _) i t x, hgeta]
    have hfeta : (fun y : Fin d → ℝ => u (t, y)) = f := rfl
    have hsp : ∀ i : Fin d, dirDeriv (spaceDir d i) u (t, x) = coordPartial i f x := by
      intro i
      rw [dirDeriv_spaceDir_eq hu i t x, hfeta]
    have hsum : (∑ i : Fin d, 2 * (dirDeriv (spaceDir d i) u (t, x)
          * dirDeriv (timeDir d) (dirDeriv (spaceDir d i) u) (t, x)))
        = ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x) :=
      Finset.sum_congr rfl fun i _ => by rw [hsp i, hmix i]
    have hlapsum : (∑ i : Fin d, dirDeriv (spaceDir d i) (dirDeriv (spaceDir d i) u) (t, x))
        = ∑ i : Fin d, coordPartial i (coordPartial i f) x :=
      Finset.sum_congr rfl fun i _ => hlap i
    have hg' : dirDeriv (timeDir d) u (t, x) = g x := rfl
    have hf' : u (t, x) = f x := rfl
    rw [hexp, heq, hlapsum, hsum, hg', hf']
    ring
  -- integrability of the three pieces
  have hint1 : Integrable (fun x : Fin d → ℝ =>
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x))
      (volume : Measure (Fin d → ℝ)) := by
    refine integrable_of_continuous_compactSupport ?_ ?_
    · exact continuous_const.mul (hgcd.continuous.mul (continuous_finsetSum _ fun i _ =>
        (contDiff_coordPartial (contDiff_coordPartial hfcd i) i).continuous))
    · exact (hgs.mul_right).mul_left
  have hint2 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => 2 * (coordPartial i f x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) := by
    intro i
    refine integrable_of_continuous_compactSupport ?_ ?_
    · exact continuous_const.mul ((contDiff_coordPartial hfcd i).continuous.mul
        (contDiff_coordPartial hgcd i).continuous)
    · exact ((hasCompactSupport_coordPartial hfs i).mul_right).mul_left
  have hint2' : Integrable
      (fun x : Fin d → ℝ => ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) := integrable_finsetSum _ fun i _ => hint2 i
  have hint3 : Integrable
      (fun x : Fin d → ℝ => 2 * ((V (t, x) + 1) * (f x * g x)))
      (volume : Measure (Fin d → ℝ)) := by
    refine integrable_of_continuous_compactSupport ?_ ?_
    · have hVc : Continuous fun x : Fin d → ℝ => V (t, x) := by fun_prop
      exact continuous_const.mul ((hVc.add continuous_const).mul (hfcd.continuous.mul
        hgcd.continuous))
    · exact ((hfs.mul_right).mul_left).mul_left
  -- integrate the expansion
  have hint12 : Integrable (fun x : Fin d → ℝ =>
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x)
        + ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) := hint1.add hint2'
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint12 hint3,
    integral_add hint1 hint2']
  -- the two derivative terms cancel
  have hgreen : (∫ x : Fin d → ℝ,
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x))
      = -∑ i : Fin d, 2 * ∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
    have hcomm : (fun x : Fin d → ℝ =>
        2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x))
        = fun x : Fin d → ℝ =>
          2 * ((∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x) := by
      funext x
      ring
    rw [hcomm, integral_const_mul, integral_laplacian_mul hfcd hgcd hfs hgs, mul_neg,
      Finset.mul_sum]
  have hsum2 : (∫ x : Fin d → ℝ, ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
      = ∑ i : Fin d, 2 * ∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
    rw [integral_finsetSum _ fun i _ => hint2 i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [hgreen, hsum2, neg_add_cancel, zero_add, integral_const_mul]
  rfl

end Integral

end Flux

end GaloisForLFunctions.HTGeometry
