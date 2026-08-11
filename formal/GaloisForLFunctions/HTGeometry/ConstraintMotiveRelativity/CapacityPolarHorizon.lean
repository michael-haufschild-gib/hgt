import Mathlib

/-!
# The capacity-polar horizon of an increasing metric chart

An increasing family of positive symmetric metrics `G₀ ≤ G₁ ≤ ⋯` on a finite-dimensional real
inner product space has inverse capacities `Q_n = G_n⁻¹` which decrease to a positive semidefinite
limit `Q_∞`.  The whole geometry is governed by the Fenchel identity

`2⟪α, x⟫ - ⟪Q_n α, α⟫ = ⟪G_n x, x⟫ - ⟪G_n (x - Q_n α), x - Q_n α⟫`,

which makes `⟪G_n x, x⟫` the Legendre transform of `⟪Q_n α, α⟫`.  The main theorem identifies the
set of bounded direct capacity with the range of the limiting cometric and with the orthogonal
complement of its kernel:

`{x | BddAbove (range fun n => ⟪G_n x, x⟫)} = range Q_∞ = (ker Q_∞)ᗮ`,

and computes the limiting metric on that sector as the reduced inverse form, represented by the
Moore–Penrose inverse of `Q_∞`.  Off the sector the direct capacities diverge.
-/

open Filter
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

/-- An **increasing capacity chart**: a monotone family of positive symmetric metrics. -/
structure CapacityChart (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] where
  /-- The metric of stage `n`. -/
  gram : ℕ → V →ₗ[ℝ] V
  /-- Each metric is symmetric. -/
  gram_symm : ∀ n x y, ⟪gram n x, y⟫ = ⟪x, gram n y⟫
  /-- Each metric is positive definite. -/
  gram_pos : ∀ n x, x ≠ 0 → 0 < ⟪gram n x, x⟫
  /-- The metrics increase. -/
  gram_mono : ∀ x, Monotone fun n => ⟪gram n x, x⟫

namespace CapacityChart

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (C : CapacityChart V)

theorem gram_nonneg (n : ℕ) (x : V) : 0 ≤ ⟪C.gram n x, x⟫ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (C.gram_pos n x hx).le

theorem gram_injective (n : ℕ) : Function.Injective (C.gram n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  have hpos := C.gram_pos n x hne
  rw [hx, inner_zero_left] at hpos
  exact lt_irrefl 0 hpos

/-- The metric of stage `n` as a linear equivalence. -/
noncomputable def gramEquiv (n : ℕ) : V ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective (C.gram n)
    ⟨C.gram_injective n, LinearMap.injective_iff_surjective.mp (C.gram_injective n)⟩

/-- The **inverse capacity** of stage `n`. -/
noncomputable def cometric (n : ℕ) : V →ₗ[ℝ] V := (C.gramEquiv n).symm

@[simp] theorem gram_cometric (n : ℕ) (x : V) : C.gram n (C.cometric n x) = x :=
  (C.gramEquiv n).apply_symm_apply x

@[simp] theorem cometric_gram (n : ℕ) (x : V) : C.cometric n (C.gram n x) = x :=
  (C.gramEquiv n).symm_apply_apply x

theorem cometric_symm (n : ℕ) (α β : V) : ⟪C.cometric n α, β⟫ = ⟪α, C.cometric n β⟫ := by
  have h := C.gram_symm n (C.cometric n α) (C.cometric n β)
  rw [gram_cometric, gram_cometric] at h
  exact h.symm

/-- **The Fenchel identity.**  Completing the square exhibits `⟪G_n x, x⟫` as the Legendre
transform of the inverse capacity form. -/
theorem fenchel (n : ℕ) (α x : V) :
    2 * ⟪α, x⟫ - ⟪C.cometric n α, α⟫
      = ⟪C.gram n x, x⟫ - ⟪C.gram n (x - C.cometric n α), x - C.cometric n α⟫ := by
  have h1 : ⟪C.gram n (C.cometric n α), x⟫ = ⟪α, x⟫ := by rw [gram_cometric]
  have h2 : ⟪C.gram n x, C.cometric n α⟫ = ⟪α, x⟫ := by
    rw [C.gram_symm, gram_cometric, real_inner_comm]
  have h3 : ⟪C.gram n (C.cometric n α), C.cometric n α⟫ = ⟪C.cometric n α, α⟫ := by
    rw [gram_cometric, real_inner_comm]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, h3]
  ring

/-- The Fenchel inequality: the direct capacity dominates every polar test. -/
theorem fenchel_le (n : ℕ) (α x : V) :
    2 * ⟪α, x⟫ - ⟪C.cometric n α, α⟫ ≤ ⟪C.gram n x, x⟫ := by
  have h := C.fenchel n α x
  have hnn := C.gram_nonneg n (x - C.cometric n α)
  linarith

/-- The Fenchel supremum is attained at the metric image. -/
theorem fenchel_eq (n : ℕ) (x : V) :
    2 * ⟪C.gram n x, x⟫ - ⟪C.cometric n (C.gram n x), C.gram n x⟫ = ⟪C.gram n x, x⟫ := by
  rw [cometric_gram, real_inner_comm]
  ring

/-! ## The decreasing inverse capacities -/

/-- The inverse-capacity quadratic form of stage `n`. -/
noncomputable def cometricForm (n : ℕ) (α : V) : ℝ := ⟪C.cometric n α, α⟫

theorem cometricForm_nonneg (n : ℕ) (α : V) : 0 ≤ C.cometricForm n α := by
  have h := C.gram_nonneg n (C.cometric n α)
  rwa [gram_cometric, real_inner_comm] at h

/-- **Inversion reverses the order.** -/
theorem cometricForm_antitone (α : V) : Antitone fun n => C.cometricForm n α := by
  intro n m hnm
  have hle := C.fenchel_le n α (C.cometric m α)
  have hgm : ⟪C.gram n (C.cometric m α), C.cometric m α⟫
      ≤ ⟪C.gram m (C.cometric m α), C.cometric m α⟫ := C.gram_mono _ hnm
  have hval : ⟪C.gram m (C.cometric m α), C.cometric m α⟫ = ⟪α, C.cometric m α⟫ := by
    rw [gram_cometric]
  have hsym : ⟪α, C.cometric m α⟫ = C.cometricForm m α := by
    rw [cometricForm, real_inner_comm]
  have hcomm : ⟪α, C.cometric m α⟫ = ⟪C.cometric m α, α⟫ := real_inner_comm _ _
  simp only [cometricForm] at hle ⊢
  rw [hval, hsym] at hgm
  simp only [cometricForm] at hgm
  linarith

theorem cometricForm_bddBelow (α : V) : BddBelow (Set.range fun n => C.cometricForm n α) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, rfl⟩
  exact C.cometricForm_nonneg n α

/-- The limiting inverse-capacity quadratic form. -/
noncomputable def cometricFormInf (α : V) : ℝ := ⨅ n, C.cometricForm n α

theorem tendsto_cometricForm (α : V) :
    Tendsto (fun n => C.cometricForm n α) atTop (𝓝 (C.cometricFormInf α)) :=
  tendsto_atTop_ciInf (C.cometricForm_antitone α) (C.cometricForm_bddBelow α)

theorem cometricFormInf_nonneg (α : V) : 0 ≤ C.cometricFormInf α :=
  le_ciInf fun n => C.cometricForm_nonneg n α

theorem cometricFormInf_le (n : ℕ) (α : V) : C.cometricFormInf α ≤ C.cometricForm n α :=
  ciInf_le (C.cometricForm_bddBelow α) n

/-- Polarization of the inverse-capacity form. -/
theorem cometric_polarization (n : ℕ) (α β : V) :
    ⟪C.cometric n α, β⟫
      = (C.cometricForm n (α + β) - C.cometricForm n α - C.cometricForm n β) / 2 := by
  have hsym : ⟪C.cometric n β, α⟫ = ⟪C.cometric n α, β⟫ := by
    rw [C.cometric_symm, real_inner_comm]
  simp only [cometricForm, map_add, inner_add_left, inner_add_right]
  rw [hsym]
  ring

theorem tendsto_inner_cometric (α β : V) :
    Tendsto (fun n => ⟪C.cometric n α, β⟫) atTop
      (𝓝 ((C.cometricFormInf (α + β) - C.cometricFormInf α - C.cometricFormInf β) / 2)) := by
  have h := (((C.tendsto_cometricForm (α + β)).sub (C.tendsto_cometricForm α)).sub
    (C.tendsto_cometricForm β)).div_const 2
  exact h.congr fun n => (C.cometric_polarization n α β).symm

theorem exists_tendsto_cometric (α : V) :
    ∃ v : V, Tendsto (fun n => C.cometric n α) atTop (𝓝 v) := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  refine ⟨∑ i, ((C.cometricFormInf (α + b i) - C.cometricFormInf α
      - C.cometricFormInf (b i)) / 2) • b i, ?_⟩
  have hexp : ∀ n, C.cometric n α = ∑ i, ⟪C.cometric n α, b i⟫ • b i := by
    intro n
    conv_lhs => rw [← b.sum_repr (C.cometric n α)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [b.repr_apply_apply, real_inner_comm]
  have h : Tendsto (fun n => ∑ i, ⟪C.cometric n α, b i⟫ • b i) atTop
      (𝓝 (∑ i, ((C.cometricFormInf (α + b i) - C.cometricFormInf α
        - C.cometricFormInf (b i)) / 2) • b i)) :=
    tendsto_finsetSum _ fun i _ => (C.tendsto_inner_cometric α (b i)).smul_const (b i)
  exact h.congr fun n => (hexp n).symm

theorem tendsto_cometric_limUnder (α : V) :
    Tendsto (fun n => C.cometric n α) atTop (𝓝 (limUnder atTop fun n => C.cometric n α)) := by
  obtain ⟨v, hv⟩ := C.exists_tendsto_cometric α
  rw [hv.limUnder_eq]
  exact hv

/-- The **limiting cometric** `Q_∞`. -/
noncomputable def cometricLimit : V →ₗ[ℝ] V where
  toFun α := limUnder atTop fun n => C.cometric n α
  map_add' a b := by
    refine tendsto_nhds_unique (C.tendsto_cometric_limUnder (a + b)) ?_
    have h := (C.tendsto_cometric_limUnder a).add (C.tendsto_cometric_limUnder b)
    simpa only [map_add] using h
  map_smul' c a := by
    refine tendsto_nhds_unique (C.tendsto_cometric_limUnder (c • a)) ?_
    have h := (C.tendsto_cometric_limUnder a).const_smul c
    simpa only [map_smul, RingHom.id_apply] using h

theorem tendsto_cometricLimit (α : V) :
    Tendsto (fun n => C.cometric n α) atTop (𝓝 (C.cometricLimit α)) :=
  C.tendsto_cometric_limUnder α

theorem inner_cometricLimit_self (α : V) : ⟪C.cometricLimit α, α⟫ = C.cometricFormInf α := by
  refine tendsto_nhds_unique ?_ (C.tendsto_cometricForm α)
  exact (C.tendsto_cometricLimit α).inner tendsto_const_nhds

theorem cometricLimit_symm (α β : V) : ⟪C.cometricLimit α, β⟫ = ⟪α, C.cometricLimit β⟫ := by
  have h1 : Tendsto (fun n => ⟪C.cometric n α, β⟫) atTop (𝓝 ⟪C.cometricLimit α, β⟫) :=
    (C.tendsto_cometricLimit α).inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪α, C.cometric n β⟫) atTop (𝓝 ⟪α, C.cometricLimit β⟫) :=
    tendsto_const_nhds.inner (C.tendsto_cometricLimit β)
  refine tendsto_nhds_unique h1 ?_
  simpa only [C.cometric_symm] using h2

theorem cometricLimit_nonneg (α : V) : 0 ≤ ⟪C.cometricLimit α, α⟫ := by
  rw [C.inner_cometricLimit_self]
  exact C.cometricFormInf_nonneg α


/-! ## The capacity-polar horizon -/

/-- The set of directions of bounded direct capacity. -/
def boundedCapacity : Set V := {x | BddAbove (Set.range fun n => ⟪C.gram n x, x⟫)}

/-- The limiting polar inequality: on the range of the limiting cometric the Legendre transform
is attained. -/
theorem polar_le (α β : V) :
    2 * ⟪α, C.cometricLimit β⟫ - ⟪C.cometricLimit α, α⟫ ≤ ⟪C.cometricLimit β, β⟫ := by
  have hnn := C.cometricLimit_nonneg (α - β)
  have hexp : ⟪C.cometricLimit (α - β), α - β⟫
      = ⟪C.cometricLimit α, α⟫ - 2 * ⟪α, C.cometricLimit β⟫ + ⟪C.cometricLimit β, β⟫ := by
    have hs : ⟪C.cometricLimit α, β⟫ = ⟪α, C.cometricLimit β⟫ := C.cometricLimit_symm α β
    have hs2 : ⟪C.cometricLimit β, α⟫ = ⟪α, C.cometricLimit β⟫ := real_inner_comm _ _
    simp only [map_sub, inner_sub_left, inner_sub_right, hs, hs2]
    ring
  linarith

/-- On the range of the limiting cometric every stage capacity is bounded by the reduced form. -/
theorem gram_le_of_mem_range (β : V) (n : ℕ) :
    ⟪C.gram n (C.cometricLimit β), C.cometricLimit β⟫ ≤ ⟪C.cometricLimit β, β⟫ := by
  set x := C.cometricLimit β with hx
  set α := C.gram n x with hα
  have hattain : ⟪C.gram n x, x⟫ = 2 * ⟪α, x⟫ - C.cometricForm n α := by
    have h := C.fenchel_eq n x
    simp only [cometricForm, hα]
    linarith [h]
  have hge : ⟪C.cometricLimit α, α⟫ ≤ C.cometricForm n α := by
    rw [C.inner_cometricLimit_self]
    exact C.cometricFormInf_le n α
  have hpolar := C.polar_le α β
  rw [← hx] at hpolar
  linarith

/-- The stage capacities converge to the reduced inverse form on the range of the limiting
cometric. -/
theorem tendsto_gram_of_mem_range (β : V) :
    Tendsto (fun n => ⟪C.gram n (C.cometricLimit β), C.cometricLimit β⟫) atTop
      (𝓝 ⟪C.cometricLimit β, β⟫) := by
  set x := C.cometricLimit β with hx
  set L := ⟪C.cometricLimit β, β⟫ with hL
  have hlow : ∀ n, 2 * ⟪β, x⟫ - C.cometricForm n β ≤ ⟪C.gram n x, x⟫ := by
    intro n
    have h := C.fenchel_le n β x
    simp only [cometricForm]
    linarith
  have hxβ : ⟪β, x⟫ = L := by rw [hx, hL, real_inner_comm]
  have htend : Tendsto (fun n => 2 * ⟪β, x⟫ - C.cometricForm n β) atTop
      (𝓝 (2 * ⟪β, x⟫ - C.cometricFormInf β)) :=
    tendsto_const_nhds.sub (C.tendsto_cometricForm β)
  have hval : 2 * ⟪β, x⟫ - C.cometricFormInf β = L := by
    rw [hxβ, ← C.inner_cometricLimit_self β, ← hL]
    have : ⟪C.cometricLimit β, β⟫ = L := hL.symm
    linarith
  rw [hval] at htend
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le htend tendsto_const_nhds hlow
    (fun n => C.gram_le_of_mem_range β n)

theorem range_subset_boundedCapacity :
    (LinearMap.range C.cometricLimit : Set V) ⊆ C.boundedCapacity := by
  rintro _ ⟨β, rfl⟩
  refine ⟨⟪C.cometricLimit β, β⟫, ?_⟩
  rintro r ⟨n, rfl⟩
  exact C.gram_le_of_mem_range β n

/-- **Off the polar sector the direct capacity diverges.** -/
theorem not_bddAbove_of_not_mem_orthogonal {x : V}
    (hx : x ∉ (LinearMap.ker C.cometricLimit)ᗮ) :
    ¬ BddAbove (Set.range fun n => ⟪C.gram n x, x⟫) := by
  rw [Submodule.mem_orthogonal] at hx
  push Not at hx
  obtain ⟨α, hαK, hαx⟩ := hx
  have hα0 : C.cometricLimit α = 0 := hαK
  set c : ℝ := |⟪α, x⟫| with hc
  have hcpos : 0 < c := abs_pos.mpr hαx
  set s : ℝ := if 0 ≤ ⟪α, x⟫ then 1 else -1 with hs
  have hsx : ⟪s • α, x⟫ = c := by
    by_cases hpos : 0 ≤ ⟪α, x⟫
    · rw [hs, if_pos hpos, one_smul, hc, abs_of_nonneg hpos]
    · rw [hs, if_neg hpos, real_inner_smul_left, hc, abs_of_neg (not_le.mp hpos)]
      ring
  set β : V := s • α with hβ
  have hβ0 : C.cometricLimit β = 0 := by rw [hβ, map_smul, hα0, smul_zero]
  have hform : C.cometricFormInf β = 0 := by
    rw [← C.inner_cometricLimit_self, hβ0, inner_zero_left]
  rintro ⟨M, hM⟩
  have hM0 : 0 ≤ M := le_trans (C.gram_nonneg 0 x) (hM (Set.mem_range_self 0))
  set t : ℝ := (M + 1) / c with ht
  have htpos : 0 < |t| + 1 := by positivity
  obtain ⟨n, hn⟩ : ∃ n, C.cometricForm n β < 1 / ((|t| + 1) ^ 2) := by
    have hlt : C.cometricFormInf β < 1 / ((|t| + 1) ^ 2) := by
      rw [hform]; positivity
    by_contra hcon
    push Not at hcon
    exact absurd (le_ciInf fun n => hcon n) (not_le.mpr hlt)
  have hfen := C.fenchel_le n (t • β) x
  have hinner : ⟪t • β, x⟫ = t * c := by rw [real_inner_smul_left, hsx]
  have hcomet : ⟪C.cometric n (t • β), t • β⟫ = t ^ 2 * C.cometricForm n β := by
    simp only [cometricForm, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hinner, hcomet] at hfen
  have hbound := hM (Set.mem_range_self n)
  have htc : t * c = M + 1 := by
    rw [ht]; field_simp
  have hsq : t ^ 2 * C.cometricForm n β < 1 := by
    have habs : t ^ 2 ≤ (|t| + 1) ^ 2 := by
      have : |t| ≤ |t| + 1 := by linarith
      nlinarith [abs_nonneg t, sq_abs t]
    have hnn := C.cometricForm_nonneg n β
    have hpos2 : (0:ℝ) < (|t| + 1) ^ 2 := by positivity
    calc t ^ 2 * C.cometricForm n β ≤ (|t| + 1) ^ 2 * C.cometricForm n β := by nlinarith
      _ < (|t| + 1) ^ 2 * (1 / ((|t| + 1) ^ 2)) := by nlinarith
      _ = 1 := by field_simp
  linarith

theorem boundedCapacity_subset_orthogonal :
    C.boundedCapacity ⊆ ((LinearMap.ker C.cometricLimit)ᗮ : Set V) := by
  intro x hx
  by_contra hcon
  exact C.not_bddAbove_of_not_mem_orthogonal hcon hx

/-- The orthogonal complement of the range of the limiting cometric is its kernel. -/
theorem orthogonal_range_cometricLimit :
    (LinearMap.range C.cometricLimit)ᗮ = LinearMap.ker C.cometricLimit := by
  ext y
  rw [Submodule.mem_orthogonal, LinearMap.mem_ker]
  constructor
  · intro hy
    have hall : ∀ α : V, ⟪α, C.cometricLimit y⟫ = 0 := by
      intro α
      rw [← C.cometricLimit_symm]
      exact hy _ ⟨α, rfl⟩
    have := hall (C.cometricLimit y)
    exact inner_self_eq_zero.mp this
  · intro hy u hu
    obtain ⟨α, rfl⟩ := hu
    rw [C.cometricLimit_symm, hy, inner_zero_right]

/-- **The polar sector is the range of the limiting cometric.** -/
theorem range_cometricLimit_eq_orthogonal :
    LinearMap.range C.cometricLimit = (LinearMap.ker C.cometricLimit)ᗮ := by
  rw [← C.orthogonal_range_cometricLimit, Submodule.orthogonal_orthogonal]

/-- **Capacity-polar horizon law.**  Bounded direct capacity, the range of the limiting cometric
and the polar complement of its kernel are the same set. -/
theorem boundedCapacity_eq :
    C.boundedCapacity = (LinearMap.range C.cometricLimit : Set V) := by
  refine Set.Subset.antisymm ?_ C.range_subset_boundedCapacity
  rw [C.range_cometricLimit_eq_orthogonal]
  exact C.boundedCapacity_subset_orthogonal

theorem boundedCapacity_eq_orthogonal :
    C.boundedCapacity = ((LinearMap.ker C.cometricLimit)ᗮ : Set V) := by
  rw [C.boundedCapacity_eq, C.range_cometricLimit_eq_orthogonal]

/-! ## The reduced inverse form and its Moore–Penrose realization -/

/-- The reduced inverse form is well defined: it depends only on the image point. -/
theorem reduced_wellDefined {β γ : V} (h : C.cometricLimit β = C.cometricLimit γ) :
    ⟪C.cometricLimit β, β⟫ = ⟪C.cometricLimit γ, γ⟫ := by
  have hker : C.cometricLimit (β - γ) = 0 := by rw [map_sub, h, sub_self]
  have hzero : ⟪C.cometricLimit β, β - γ⟫ = 0 := by
    rw [C.cometricLimit_symm, hker, inner_zero_right]
  rw [inner_sub_right] at hzero
  have hγ : ⟪C.cometricLimit β, γ⟫ = ⟪C.cometricLimit γ, γ⟫ := by rw [h]
  linarith [hzero, hγ]

/-- The limiting cometric restricted to the polar sector. -/
noncomputable def sectorMap :
    ↥(LinearMap.ker C.cometricLimit)ᗮ →ₗ[ℝ] ↥(LinearMap.ker C.cometricLimit)ᗮ :=
  LinearMap.codRestrict _ (C.cometricLimit ∘ₗ (LinearMap.ker C.cometricLimit)ᗮ.subtype)
    (fun β => by
      have hr : C.cometricLimit (β : V) ∈ LinearMap.range C.cometricLimit := ⟨(β : V), rfl⟩
      rwa [C.range_cometricLimit_eq_orthogonal] at hr)

@[simp] theorem sectorMap_coe (β : ↥(LinearMap.ker C.cometricLimit)ᗮ) :
    ((C.sectorMap β : ↥(LinearMap.ker C.cometricLimit)ᗮ) : V) = C.cometricLimit (β : V) := rfl

theorem sectorMap_injective : Function.Injective C.sectorMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro β hβ
  have hzero : C.cometricLimit (β : V) = 0 := by
    have := congrArg (fun z : ↥(LinearMap.ker C.cometricLimit)ᗮ => (z : V)) hβ
    simpa using this
  have hmem : (β : V) ∈ LinearMap.ker C.cometricLimit ⊓ (LinearMap.ker C.cometricLimit)ᗮ :=
    ⟨hzero, β.2⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hmem
  exact Subtype.ext hmem

/-- The limiting cometric is a linear automorphism of the polar sector. -/
noncomputable def sectorEquiv :
    ↥(LinearMap.ker C.cometricLimit)ᗮ ≃ₗ[ℝ] ↥(LinearMap.ker C.cometricLimit)ᗮ :=
  LinearEquiv.ofBijective C.sectorMap
    ⟨C.sectorMap_injective, LinearMap.injective_iff_surjective.mp C.sectorMap_injective⟩

/-- The **Moore–Penrose inverse** of the limiting cometric. -/
noncomputable def pseudoInverse : V →ₗ[ℝ] V :=
  (LinearMap.ker C.cometricLimit)ᗮ.subtype ∘ₗ C.sectorEquiv.symm.toLinearMap ∘ₗ
    ((LinearMap.ker C.cometricLimit)ᗮ.orthogonalProjectionOnto : V →L[ℝ] _)

theorem pseudoInverse_mem (x : V) :
    C.pseudoInverse x ∈ (LinearMap.ker C.cometricLimit)ᗮ :=
  (C.sectorEquiv.symm ((LinearMap.ker C.cometricLimit)ᗮ.orthogonalProjectionOnto x)).2

/-- On the polar sector the Moore–Penrose inverse is a genuine right inverse. -/
theorem cometricLimit_pseudoInverse {x : V} (hx : x ∈ (LinearMap.ker C.cometricLimit)ᗮ) :
    C.cometricLimit (C.pseudoInverse x) = x := by
  have hproj : (LinearMap.ker C.cometricLimit)ᗮ.orthogonalProjectionOnto x = ⟨x, hx⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x, hx⟩ :
      ↥(LinearMap.ker C.cometricLimit)ᗮ)
  have happ := C.sectorEquiv.apply_symm_apply (⟨x, hx⟩ :
    ↥(LinearMap.ker C.cometricLimit)ᗮ)
  have hval : ((C.sectorEquiv (C.sectorEquiv.symm ⟨x, hx⟩) :
      ↥(LinearMap.ker C.cometricLimit)ᗮ) : V) = x := by rw [happ]
  show C.cometricLimit ((C.sectorEquiv.symm
    ((LinearMap.ker C.cometricLimit)ᗮ.orthogonalProjectionOnto x) :
      ↥(LinearMap.ker C.cometricLimit)ᗮ) : V) = x
  rw [hproj]
  rw [← C.sectorMap_coe (C.sectorEquiv.symm ⟨x, hx⟩)]
  exact hval

/-- **Moore–Penrose form of the limiting metric.**  On the polar sector the stage capacities
converge to the reduced inverse form, computed by the Moore–Penrose inverse. -/
theorem tendsto_gram_pseudoInverse {x : V} (hx : x ∈ C.boundedCapacity) :
    Tendsto (fun n => ⟪C.gram n x, x⟫) atTop (𝓝 ⟪C.pseudoInverse x, x⟫) := by
  have hmem : x ∈ (LinearMap.ker C.cometricLimit)ᗮ := by
    have := C.boundedCapacity_eq_orthogonal ▸ hx
    exact this
  obtain ⟨β, hβ⟩ : ∃ β, C.cometricLimit β = x := by
    refine ⟨C.pseudoInverse x, C.cometricLimit_pseudoInverse hmem⟩
  have hred : ⟪C.cometricLimit β, β⟫ = ⟪C.pseudoInverse x, x⟫ := by
    have heq := C.reduced_wellDefined (β := β) (γ := C.pseudoInverse x)
      (by rw [hβ, C.cometricLimit_pseudoInverse hmem])
    rw [heq, C.cometricLimit_pseudoInverse hmem, real_inner_comm]
  have h := C.tendsto_gram_of_mem_range β
  rw [hβ] at h
  have hfinal : ⟪x, β⟫ = ⟪C.pseudoInverse x, x⟫ := by
    conv_lhs => rw [← hβ]
    exact hred
  rwa [hfinal] at h

/-- **Divergence off the polar sector.** -/
theorem not_boundedCapacity_iff (x : V) :
    x ∉ C.boundedCapacity ↔ ¬ BddAbove (Set.range fun n => ⟪C.gram n x, x⟫) := Iff.rfl

/-! ## The polar duality of the limiting pair -/

/-- The polar sector as a subspace. -/
noncomputable def boundedCapacitySubmodule : Submodule ℝ V := (LinearMap.ker C.cometricLimit)ᗮ

@[simp] theorem coe_boundedCapacitySubmodule :
    (C.boundedCapacitySubmodule : Set V) = C.boundedCapacity :=
  (C.boundedCapacity_eq_orthogonal).symm

/-- **The polar sector and the collapse kernel are complementary.** -/
theorem isCompl_boundedCapacity :
    IsCompl C.boundedCapacitySubmodule (LinearMap.ker C.cometricLimit) :=
  (Submodule.isCompl_orthogonal _).symm

/-- **Reverse polar identity.**  The limiting cometric form is the Legendre transform of the
reduced inverse form. -/
theorem isGreatest_cometricLimit (α : V) :
    IsGreatest {r : ℝ | ∃ β : V, r = 2 * ⟪α, C.cometricLimit β⟫ - ⟪C.cometricLimit β, β⟫}
      ⟪C.cometricLimit α, α⟫ := by
  constructor
  · refine ⟨α, ?_⟩
    have h : ⟪α, C.cometricLimit α⟫ = ⟪C.cometricLimit α, α⟫ := real_inner_comm _ _
    rw [h]; ring
  · rintro r ⟨β, rfl⟩
    have h := C.polar_le α β
    linarith

/-- **Polar identity for the limiting metric.**  On the polar sector the limiting direct capacity
is the Legendre transform of the limiting cometric form. -/
theorem isGreatest_gram_limit (β : V) :
    IsGreatest {r : ℝ | ∃ α : V, r = 2 * ⟪α, C.cometricLimit β⟫ - ⟪C.cometricLimit α, α⟫}
      ⟪C.cometricLimit β, β⟫ := by
  constructor
  · exact ⟨β, by rw [real_inner_comm β (C.cometricLimit β)]; ring⟩
  · rintro r ⟨α, rfl⟩
    exact C.polar_le α β

/-! ## Dependence only on the metric family -/

theorem cometric_congr {C D : CapacityChart V} (h : ∀ n, C.gram n = D.gram n) (n : ℕ) :
    C.cometric n = D.cometric n := by
  ext x
  refine D.gram_injective n ?_
  rw [D.gram_cometric, ← h n, C.gram_cometric]

theorem cometricLimit_congr {C D : CapacityChart V} (h : ∀ n, C.gram n = D.gram n) :
    C.cometricLimit = D.cometricLimit := by
  ext x
  refine tendsto_nhds_unique (C.tendsto_cometricLimit x) ?_
  exact (D.tendsto_cometricLimit x).congr fun n => by rw [cometric_congr h n]

end CapacityChart

end HTGeometry.ConstraintMotiveRelativity
