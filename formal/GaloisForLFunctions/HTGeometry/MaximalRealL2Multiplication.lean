import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Maximal real multiplication on scalar L²

For an arbitrary measure space and measurable real energy, this module constructs multiplication
by that energy on its maximal L² domain and proves the resulting unbounded operator self-adjoint.
Bounded spectral cutoffs lie in the domain and converge strongly. Testing an adjoint vector against
those cutoffs recovers the weighted function locally on every energy band, hence almost everywhere.
-/

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace LinearPMap Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {α : Type u} [MeasurableSpace α]

/-- Maximal `L²` domain of multiplication by a real measurable energy. -/
def maximalRealL2MulDomain (μ : Measure α) (energy : α → ℝ) :
    Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => (energy x : ℂ) * f x) 2 μ}
  zero_mem' := by
    refine (memLp_congr_ae ?_).mpr MemLp.zero
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [hx]
    simp
  add_mem' := by
    intro f g hf hg
    refine (memLp_congr_ae ?_).mpr (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf
    refine (memLp_congr_ae ?_).mpr (hf.const_mul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx]
    change (energy x : ℂ) * (c * (f : Lp ℂ 2 μ) x) =
      c * ((energy x : ℂ) * (f : Lp ℂ 2 μ) x)
    ring

/-- Multiplication by a real energy on its maximal `L²` domain. -/
def maximalRealL2Mul (μ : Measure α) (energy : α → ℝ) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalRealL2MulDomain μ energy
  toFun :=
    { toFun := fun f => f.property.toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add f.property g.property]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)] with x hx
        change (energy x : ℂ) * ((f : Lp ℂ 2 μ) + (g : Lp ℂ 2 μ)) x =
          ((fun y => (energy y : ℂ) * (f : Lp ℂ 2 μ) y) +
            fun y => (energy y : ℂ) * (g : Lp ℂ 2 μ) y) x
        rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c f.property]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (f : Lp ℂ 2 μ)] with x hx
        change (energy x : ℂ) * (c • (f : Lp ℂ 2 μ)) x =
          (c • fun y => (energy y : ℂ) * (f : Lp ℂ 2 μ) y) x
        rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring }

theorem maximalRealL2Mul_apply_ae (μ : Measure α) (energy : α → ℝ)
    (f : (maximalRealL2Mul μ energy).domain) :
    (maximalRealL2Mul μ energy f : α → ℂ) =ᵐ[μ]
      fun x => (energy x : ℂ) * (f : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp f.property

/-- Real maximal multiplication is symmetric. -/
theorem maximalRealL2Mul_formalSelfAdjoint (μ : Measure α) (energy : α → ℝ) :
    (maximalRealL2Mul μ energy).IsFormalAdjoint (maximalRealL2Mul μ energy) := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [maximalRealL2Mul_apply_ae μ energy f,
    maximalRealL2Mul_apply_ae μ energy g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

def realEnergyCutoffSymbol (energy : α → ℝ) (n : ℕ) (x : α) : ℂ :=
  if |energy x| ≤ (n : ℝ) then 1 else 0

def realEnergyTruncationSymbol (energy : α → ℝ) (n : ℕ) (x : α) : ℂ :=
  if |energy x| ≤ (n : ℝ) then (energy x : ℂ) else 0

theorem measurable_realEnergyCutoffSymbol {energy : α → ℝ} (henergy : Measurable energy)
    (n : ℕ) : Measurable (realEnergyCutoffSymbol energy n) := by
  exact Measurable.ite
    (measurableSet_le (continuous_abs.measurable.comp henergy) measurable_const)
    measurable_const measurable_const

theorem measurable_realEnergyTruncationSymbol {energy : α → ℝ} (henergy : Measurable energy)
    (n : ℕ) : Measurable (realEnergyTruncationSymbol energy n) := by
  exact Measurable.ite
    (measurableSet_le (continuous_abs.measurable.comp henergy) measurable_const)
    (Complex.measurable_ofReal.comp henergy) measurable_const

omit [MeasurableSpace α] in
theorem norm_realEnergyCutoffSymbol_le_one (energy : α → ℝ) (n : ℕ) (x : α) :
    ‖realEnergyCutoffSymbol energy n x‖ ≤ 1 := by
  by_cases hx : |energy x| ≤ (n : ℝ)
  · simp [realEnergyCutoffSymbol, hx]
  · simp [realEnergyCutoffSymbol, hx]

omit [MeasurableSpace α] in
theorem norm_realEnergyTruncationSymbol_le (energy : α → ℝ) (n : ℕ) (x : α) :
    ‖realEnergyTruncationSymbol energy n x‖ ≤ (n : ℝ) := by
  by_cases hx : |energy x| ≤ (n : ℝ)
  · rw [realEnergyTruncationSymbol, if_pos hx, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  · simp [realEnergyTruncationSymbol, hx]

omit [MeasurableSpace α] in
theorem conj_realEnergyCutoffSymbol (energy : α → ℝ) (n : ℕ) (x : α) :
    (starRingEnd ℂ) (realEnergyCutoffSymbol energy n x) =
      realEnergyCutoffSymbol energy n x := by
  by_cases hx : |energy x| ≤ (n : ℝ) <;> simp [realEnergyCutoffSymbol, hx]

omit [MeasurableSpace α] in
theorem conj_realEnergyTruncationSymbol (energy : α → ℝ) (n : ℕ) (x : α) :
    (starRingEnd ℂ) (realEnergyTruncationSymbol energy n x) =
      realEnergyTruncationSymbol energy n x := by
  by_cases hx : |energy x| ≤ (n : ℝ) <;>
    simp [realEnergyTruncationSymbol, hx, Complex.conj_ofReal]

def realEnergyCutoff (μ : Measure α) {energy : α → ℝ} (henergy : Measurable energy)
    (n : ℕ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (measurable_realEnergyCutoffSymbol henergy n) zero_le_one
    (norm_realEnergyCutoffSymbol_le_one energy n)

def realEnergyTruncation (μ : Measure α) {energy : α → ℝ} (henergy : Measurable energy)
    (n : ℕ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (measurable_realEnergyTruncationSymbol henergy n)
    (Nat.cast_nonneg n) (norm_realEnergyTruncationSymbol_le energy n)

theorem realEnergyCutoff_apply_ae (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (n : ℕ) (f : Lp ℂ 2 μ) :
    (realEnergyCutoff μ henergy n f : α → ℂ) =ᵐ[μ]
      fun x => realEnergyCutoffSymbol energy n x * f x :=
  lpBoundedMulCLM_coeFn _ _ _ _

theorem realEnergyTruncation_apply_ae (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (n : ℕ) (f : Lp ℂ 2 μ) :
    (realEnergyTruncation μ henergy n f : α → ℂ) =ᵐ[μ]
      fun x => realEnergyTruncationSymbol energy n x * f x :=
  lpBoundedMulCLM_coeFn _ _ _ _

theorem realEnergyCutoff_symmetric (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (n : ℕ) (f g : Lp ℂ 2 μ) :
    inner ℂ (realEnergyCutoff μ henergy n f) g =
      inner ℂ f (realEnergyCutoff μ henergy n g) :=
  lpBoundedMulCLM_inner_real _ _ _ (conj_realEnergyCutoffSymbol energy n) f g

theorem realEnergyTruncation_symmetric (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (n : ℕ) (f g : Lp ℂ 2 μ) :
    inner ℂ (realEnergyTruncation μ henergy n f) g =
      inner ℂ f (realEnergyTruncation μ henergy n g) :=
  lpBoundedMulCLM_inner_real _ _ _ (conj_realEnergyTruncationSymbol energy n) f g

theorem realEnergyCutoff_mem_maximalRealL2MulDomain (μ : Measure α)
    {energy : α → ℝ} (henergy : Measurable energy) (n : ℕ) (f : Lp ℂ 2 μ) :
    realEnergyCutoff μ henergy n f ∈ maximalRealL2MulDomain μ energy := by
  refine (memLp_congr_ae ?_).mpr
    (memLp_mul_of_bound (measurable_realEnergyTruncationSymbol henergy n)
      (Nat.cast_nonneg n) (norm_realEnergyTruncationSymbol_le energy n) f)
  filter_upwards [realEnergyCutoff_apply_ae μ henergy n f] with x hx
  rw [hx]
  by_cases hbound : |energy x| ≤ (n : ℝ) <;>
    simp [realEnergyCutoffSymbol, realEnergyTruncationSymbol, hbound]

theorem maximalRealL2Mul_realEnergyCutoff (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (n : ℕ) (f : Lp ℂ 2 μ) :
    maximalRealL2Mul μ energy
        ⟨realEnergyCutoff μ henergy n f,
          realEnergyCutoff_mem_maximalRealL2MulDomain μ henergy n f⟩ =
      realEnergyTruncation μ henergy n f := by
  apply Lp.ext
  filter_upwards [maximalRealL2Mul_apply_ae μ energy
      ⟨realEnergyCutoff μ henergy n f,
        realEnergyCutoff_mem_maximalRealL2MulDomain μ henergy n f⟩,
    realEnergyCutoff_apply_ae μ henergy n f,
    realEnergyTruncation_apply_ae μ henergy n f] with x hmax hcut htrunc
  rw [hmax, hcut, htrunc]
  by_cases hbound : |energy x| ≤ (n : ℝ) <;>
    simp [realEnergyCutoffSymbol, realEnergyTruncationSymbol, hbound]

theorem tendsto_realEnergyCutoff (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (f : Lp ℂ 2 μ) :
    Tendsto (fun n : ℕ => realEnergyCutoff μ henergy n f) atTop (𝓝 f) := by
  have hpt : ∀ x : α, Tendsto (fun n : ℕ => realEnergyCutoffSymbol energy n x)
      atTop (𝓝 (1 : ℂ)) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |energy x|
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbound : |energy x| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    simp [realEnergyCutoffSymbol, hbound]
  have h := tendsto_lpBoundedMulCLM_apply
    (φ := fun n x => realEnergyCutoffSymbol energy n x)
    (ψ := fun _ : α => (1 : ℂ))
    (fun n => measurable_realEnergyCutoffSymbol henergy n) measurable_const
    zero_le_one (fun n => norm_realEnergyCutoffSymbol_le_one energy n)
    (fun _ => by simp) hpt f
  have hid : lpBoundedMulCLM (p := 2) (μ := μ) (φ := fun _ : α => (1 : ℂ))
      measurable_const zero_le_one
      (fun _ : α => by norm_num) f = f := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ)
      (φ := fun _ : α => (1 : ℂ)) measurable_const
      zero_le_one (fun _ : α => by norm_num) f] with x hx
    simpa using hx
  simpa only [realEnergyCutoff, hid] using h

theorem maximalRealL2Mul_dense (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) :
    Dense ((maximalRealL2Mul μ energy).domain : Set (Lp ℂ 2 μ)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  apply mem_closure_of_tendsto (tendsto_realEnergyCutoff μ henergy f)
  exact Filter.Eventually.of_forall fun n =>
    realEnergyCutoff_mem_maximalRealL2MulDomain μ henergy n f

theorem maximalRealL2Mul_adjoint_cutoff (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (n : ℕ)
    (y : (maximalRealL2Mul μ energy)†.domain) :
    realEnergyTruncation μ henergy n (y : Lp ℂ 2 μ) =
      realEnergyCutoff μ henergy n ((maximalRealL2Mul μ energy)† y) := by
  apply ext_inner_right ℂ
  intro f
  let fdom : (maximalRealL2Mul μ energy).domain :=
    ⟨realEnergyCutoff μ henergy n f,
      realEnergyCutoff_mem_maximalRealL2MulDomain μ henergy n f⟩
  calc
    inner ℂ (realEnergyTruncation μ henergy n (y : Lp ℂ 2 μ)) f =
        inner ℂ (y : Lp ℂ 2 μ) (realEnergyTruncation μ henergy n f) :=
      realEnergyTruncation_symmetric μ henergy n _ _
    _ = inner ℂ (y : Lp ℂ 2 μ) (maximalRealL2Mul μ energy fdom) := by
      rw [maximalRealL2Mul_realEnergyCutoff]
    _ = inner ℂ ((maximalRealL2Mul μ energy)† y) (fdom : Lp ℂ 2 μ) :=
      (LinearPMap.adjoint_isFormalAdjoint (maximalRealL2Mul_dense μ henergy) y fdom).symm
    _ = inner ℂ ((maximalRealL2Mul μ energy)† y)
        (realEnergyCutoff μ henergy n f) := rfl
    _ = inner ℂ (realEnergyCutoff μ henergy n ((maximalRealL2Mul μ energy)† y)) f :=
      (realEnergyCutoff_symmetric μ henergy n _ _).symm

theorem maximalRealL2Mul_adjoint_apply_ae (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) (y : (maximalRealL2Mul μ energy)†.domain) :
    ((maximalRealL2Mul μ energy)† y : α → ℂ) =ᵐ[μ]
      fun x => (energy x : ℂ) * (y : Lp ℂ 2 μ) x := by
  let z : Lp ℂ 2 μ := (maximalRealL2Mul μ energy)† y
  have hlocal : ∀ n : ℕ, ∀ᵐ x ∂μ,
      |energy x| ≤ (n : ℝ) → (energy x : ℂ) * (y : Lp ℂ 2 μ) x = z x := by
    intro n
    have heq := maximalRealL2Mul_adjoint_cutoff μ henergy n y
    have heqae :
        (realEnergyTruncation μ henergy n (y : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
          (realEnergyCutoff μ henergy n z : α → ℂ) := by
      rw [heq]
    filter_upwards [realEnergyTruncation_apply_ae μ henergy n (y : Lp ℂ 2 μ),
      realEnergyCutoff_apply_ae μ henergy n z, heqae] with x htrunc hcut heqx hbound
    rw [htrunc, hcut] at heqx
    simpa [realEnergyTruncationSymbol, realEnergyCutoffSymbol, hbound] using heqx
  filter_upwards [MeasureTheory.ae_all_iff.2 hlocal] with x hx
  obtain ⟨n, hn⟩ := exists_nat_ge |energy x|
  exact (hx n hn).symm

/-- Maximal multiplication by any measurable real energy on scalar `L²` is self-adjoint. -/
theorem maximalRealL2Mul_isSelfAdjoint (μ : Measure α) {energy : α → ℝ}
    (henergy : Measurable energy) :
    IsSelfAdjoint (maximalRealL2Mul μ energy) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let y' : (maximalRealL2Mul μ energy)†.domain := ⟨y, hy⟩
      let z : Lp ℂ 2 μ := (maximalRealL2Mul μ energy)† y'
      change MemLp (fun x => (energy x : ℂ) * y x) 2 μ
      refine (memLp_congr_ae ?_).mpr (Lp.memLp z)
      exact (maximalRealL2Mul_adjoint_apply_ae μ henergy y').symm
    · intro x y hxy
      apply Lp.ext
      have hxyAe : ((x : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
          ((y : Lp ℂ 2 μ) : α → ℂ) := by rw [hxy]
      filter_upwards [maximalRealL2Mul_adjoint_apply_ae μ henergy x,
        maximalRealL2Mul_apply_ae μ energy y, hxyAe] with a hx hy hxy'
      rw [hx, hy, hxy']
  · exact (maximalRealL2Mul_formalSelfAdjoint μ energy).le_adjoint
      (maximalRealL2Mul_dense μ henergy)

end

end GaloisForLFunctions.HTGeometry


