import GaloisForLFunctions.HTGeometry.ExponentialJetOpenness
import GaloisForLFunctions.HTGeometry.InversionJetMap

/-!
# The Cayley outer jet chart is open

The Cayley exponential `chi(w) = exp((w - i)/(w + i))` factors as `exp` after an affine map after a
reciprocal after an affine map, because `(w - i)/(w + i) = 1 - 2i/(w + i)`.  Each factor acts on jet
packets by a map already known to carry neighbourhoods to neighbourhoods: affine jet maps are linear
isomorphisms, the reciprocal jet map is a continuous involution, and the exponential jet map is
triangular with nonvanishing diagonal.

So the whole chart is open, with no implicit function theorem and no Faa di Bruno formula.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A map with a continuous right inverse through the base point carries neighbourhoods to
neighbourhoods. -/
theorem image_mem_nhds_of_continuousAt_rightInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Φ : X → Y} {Ψ : Y → X} {y : X} {N : Set X} (hN : N ∈ nhds y)
    (hΨ : ContinuousAt Ψ (Φ y)) (hΨy : Ψ (Φ y) = y) (hΦΨ : ∀ w, Φ (Ψ w) = w) :
    Φ '' N ∈ nhds (Φ y) := by
  have hpre : Ψ ⁻¹' N ∈ nhds (Φ y) := by
    refine hΨ ?_
    rw [hΨy]
    exact hN
  refine Filter.mem_of_superset hpre ?_
  intro w hw
  exact ⟨Ψ w, hw, hΦΨ w⟩

/-! ## Affine jet maps -/

/-- The jets of `a f + b`. -/
def affJetScalar (a b : ℂ) (y : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then a * y 0 + b else a * y k

theorem affJetScalar_iteratedDeriv (a b : ℂ) {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ (⊤ : ℕ∞) f z) (k : ℕ) :
    iteratedDeriv k (fun w => a * f w + b) z
      = affJetScalar a b (fun j => iteratedDeriv j f z) k := by
  have hfk : ContDiffAt ℂ ((k : ℕ) : ℕ∞) f z :=
    hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
  have hmul : ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun w => a * f w) z := contDiffAt_const.mul hfk
  have hsum : (fun w => a * f w + b) = (fun w => a * f w) + fun _ => b := rfl
  rw [affJetScalar, hsum, iteratedDeriv_add hmul contDiffAt_const,
    iteratedDeriv_const_mul a hfk]
  cases k with
  | zero => simp
  | succ k =>
      simp [iteratedDeriv_succ']

@[simp]
theorem affJetScalar_apply_zero (a b : ℂ) (y : ℕ → ℂ) : affJetScalar a b y 0 = a * y 0 + b := by
  simp [affJetScalar]

theorem affJetScalar_apply_of_ne (a b : ℂ) (y : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) :
    affJetScalar a b y k = a * y k := by
  simp [affJetScalar, hk]

theorem continuous_affJetScalar (a b : ℂ) :
    Continuous fun v : ℕ → ℂ => fun k => affJetScalar a b v k := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar_apply_zero]
    exact (continuous_const.mul (continuous_apply (0 : ℕ))).add continuous_const
  · simp only [affJetScalar_apply_of_ne a b _ hk]
    exact continuous_const.mul (continuous_apply k)

theorem affJetScalar_affJetScalar {a b : ℂ} (ha : a ≠ 0) (v : ℕ → ℂ) (k : ℕ) :
    affJetScalar a b (fun j => affJetScalar a⁻¹ (-(b / a)) v j) k = v k := by
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar_apply_zero]
    field_simp
    ring
  · simp only [affJetScalar_apply_of_ne _ _ _ hk]
    field_simp

theorem affJetScalar_affJetScalar' {a b : ℂ} (ha : a ≠ 0) (v : ℕ → ℂ) (k : ℕ) :
    affJetScalar a⁻¹ (-(b / a)) (fun j => affJetScalar a b v j) k = v k := by
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar_apply_zero]
    field_simp
    ring
  · simp only [affJetScalar_apply_of_ne _ _ _ hk]
    field_simp

/-- **Affine jet maps carry neighbourhoods to neighbourhoods.** -/
theorem affJetScalar_image_mem_nhds {a b : ℂ} (ha : a ≠ 0) (y : ℕ → ℂ) {N : Set (ℕ → ℂ)}
    (hN : N ∈ nhds y) :
    (fun v : ℕ → ℂ => fun k => affJetScalar a b v k) '' N
      ∈ nhds (fun k => affJetScalar a b y k) := by
  refine image_mem_nhds_of_continuousAt_rightInverse
    (Φ := fun v : ℕ → ℂ => fun k => affJetScalar a b v k)
    (Ψ := fun v : ℕ → ℂ => fun k => affJetScalar a⁻¹ (-(b / a)) v k) hN
    ((continuous_affJetScalar a⁻¹ (-(b / a))).continuousAt) ?_ ?_
  · funext k
    exact affJetScalar_affJetScalar' ha y k
  · intro w
    funext k
    exact affJetScalar_affJetScalar ha w k

/-! ## The Cayley outer jet chart -/

/-- The jets of `chi ∘ f`, assembled from the affine, reciprocal and exponential jet maps. -/
def chiJetScalar (y : ℕ → ℂ) : ℕ → ℂ :=
  expJetScalar
    (fun j => affJetScalar (-(2 * Complex.I)) 1
      (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) j)

/-- **The Cayley outer jet chart carries neighbourhoods to neighbourhoods.** -/
theorem chiJetScalar_image_mem_nhds {y : ℕ → ℂ} (hy : y 0 + Complex.I ≠ 0) {N : Set (ℕ → ℂ)}
    (hN : N ∈ nhds y) :
    (fun v : ℕ → ℂ => fun k => chiJetScalar v k) '' N ∈ nhds (fun k => chiJetScalar y k) := by
  classical
  set A₁ : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => affJetScalar 1 Complex.I v k with hA₁
  set R : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => invJetScalar v k with hR
  set A₂ : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => affJetScalar (-(2 * Complex.I)) 1 v k with hA₂
  set E : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => expJetScalar v k with hE
  have hA₁y : A₁ y 0 ≠ 0 := by
    simp only [hA₁, affJetScalar_apply_zero, one_mul]
    exact hy
  have h1 : A₁ '' N ∈ nhds (A₁ y) := affJetScalar_image_mem_nhds one_ne_zero y hN
  have h2 : R '' (A₁ '' N) ∈ nhds (R (A₁ y)) := invJetScalar_image_mem_nhds hA₁y h1
  have h3 : A₂ '' (R '' (A₁ '' N)) ∈ nhds (A₂ (R (A₁ y))) := by
    refine affJetScalar_image_mem_nhds ?_ _ h2
    simp only [ne_eq, neg_eq_zero, mul_eq_zero]
    push Not
    exact ⟨two_ne_zero, Complex.I_ne_zero⟩
  have h4 : E '' (A₂ '' (R '' (A₁ '' N))) ∈ nhds (E (A₂ (R (A₁ y)))) :=
    expJetScalar_image_mem_nhds _ h3
  have himg : (fun v : ℕ → ℂ => fun k => chiJetScalar v k) '' N
      = E '' (A₂ '' (R '' (A₁ '' N))) := by
    rw [← Set.image_comp, ← Set.image_comp, ← Set.image_comp]
    rfl
  have hval : (fun k => chiJetScalar y k) = E (A₂ (R (A₁ y))) := rfl
  rw [himg, hval]
  exact h4

end

end GaloisForLFunctions.HTGeometry
