import GaloisForLFunctions.RHTower.SoninBoundaryTransition
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# The boundary corona is a Hausdorff Banach space

Bounded families of even vectors carry the supremum norm, under which they form a Banach space, and
the norm-null families are a closed subspace of it.  The quotient is therefore a Hausdorff Banach
space, and it is the same object as the algebraic quotient: the two are linearly isomorphic.

Under that isomorphism the two transition identities and the nonvanishing of the packet classes are
statements about a genuine Banach corona, and the classes acquire strictly positive norms.

Reindexing a family along a surjection of the clock is an isometry of the bounded families, and
along a clock escaping to infinity it descends to the corona.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology ENNReal

/-- Bounded families of even vectors under the supremum norm. -/
abbrev SoninBoundedSeq : Type := lp (fun _ : ℕ => evenSubspace) ∞

/-- A uniformly bounded family is a supremum-norm family. -/
theorem memℓp_infty_of_forall_norm_le {f : ℕ → evenSubspace} {M : ℝ} (h : ∀ n, ‖f n‖ ≤ M) :
    Memℓp f ∞ :=
  memℓp_infty_iff.mpr ⟨M, by rintro x ⟨n, rfl⟩; exact h n⟩

/-- Norm-null families, as a subspace of the supremum-norm space. -/
def soninNullSeq : Submodule ℂ SoninBoundedSeq where
  carrier := {f | Tendsto (fun n => ‖(f : ℕ → evenSubspace) n‖) atTop (𝓝 0)}
  add_mem' := by
    intro f g hf hg
    show Tendsto (fun n => ‖((f + g : SoninBoundedSeq) : ℕ → evenSubspace) n‖) atTop (𝓝 0)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hf.add hg)
    have hn : ((f + g : SoninBoundedSeq) : ℕ → evenSubspace) n =
        (f : ℕ → evenSubspace) n + (g : ℕ → evenSubspace) n := by
      rw [lp.coeFn_add]; rfl
    rw [hn]
    exact norm_add_le _ _
  zero_mem' := by
    show Tendsto (fun n => ‖((0 : SoninBoundedSeq) : ℕ → evenSubspace) n‖) atTop (𝓝 0)
    simp
  smul_mem' := by
    intro c f hf
    show Tendsto (fun n => ‖((c • f : SoninBoundedSeq) : ℕ → evenSubspace) n‖) atTop (𝓝 0)
    have hmul : Tendsto (fun n => ‖c‖ * ‖(f : ℕ → evenSubspace) n‖) atTop (𝓝 0) := by
      simpa using hf.const_mul ‖c‖
    refine hmul.congr fun n => ?_
    have hn : ((c • f : SoninBoundedSeq) : ℕ → evenSubspace) n =
        c • (f : ℕ → evenSubspace) n := by
      rw [lp.coeFn_smul]; rfl
    rw [hn, norm_smul]

/-- **The null families are closed.**  A supremum-norm limit of null families is null: the
approximation error is uniform in the index, and the approximant is eventually small. -/
theorem isClosed_soninNullSeq : IsClosed (soninNullSeq : Set SoninBoundedSeq) := by
  rw [← isSeqClosed_iff_isClosed]
  intro g u hg hconv
  show Tendsto (fun n => ‖(u : ℕ → evenSubspace) n‖) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ :=
    (Metric.tendsto_atTop.mp hconv (ε / 2) (by linarith)).imp fun N hN => hN N le_rfl
  have hgk : Tendsto (fun n => ‖((g k : SoninBoundedSeq) : ℕ → evenSubspace) n‖) atTop (𝓝 0) :=
    hg k
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hgk (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖((g k : SoninBoundedSeq) : ℕ → evenSubspace) n‖ < ε / 2 := by
    have h := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
  have h2 : ‖(u : ℕ → evenSubspace) n - ((g k : SoninBoundedSeq) : ℕ → evenSubspace) n‖ ≤
      ‖u - g k‖ := by
    simpa using lp.norm_apply_le_norm (E := fun _ : ℕ => evenSubspace) ENNReal.top_ne_zero
      (u - g k) n
  have h3 : ‖u - g k‖ < ε / 2 := by
    rw [← dist_eq_norm, dist_comm]
    exact hk
  have h4 : ‖(u : ℕ → evenSubspace) n‖ ≤
      ‖(u : ℕ → evenSubspace) n - ((g k : SoninBoundedSeq) : ℕ → evenSubspace) n‖ +
        ‖((g k : SoninBoundedSeq) : ℕ → evenSubspace) n‖ := by
    simpa using norm_add_le ((u : ℕ → evenSubspace) n -
      ((g k : SoninBoundedSeq) : ℕ → evenSubspace) n)
      (((g k : SoninBoundedSeq) : ℕ → evenSubspace) n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

instance : IsClosed (soninNullSeq : Set SoninBoundedSeq) := isClosed_soninNullSeq

/-- **The boundary corona as a normed space.** -/
abbrev SoninCoronaSpace : Type := SoninBoundedSeq ⧸ soninNullSeq

/-- The boundary class of a supremum-norm family. -/
def soninCoronaClass (f : SoninBoundedSeq) : SoninCoronaSpace := Submodule.Quotient.mk f

theorem soninCoronaSpace_t2 : T2Space SoninCoronaSpace := inferInstance

theorem soninCoronaSpace_completeSpace : CompleteSpace SoninCoronaSpace := inferInstance

/-- Classes agree exactly when the difference is norm-null. -/
theorem soninCoronaClass_eq_iff (f g : SoninBoundedSeq) :
    soninCoronaClass f = soninCoronaClass g ↔
      Tendsto (fun n => ‖(f : ℕ → evenSubspace) n - (g : ℕ → evenSubspace) n‖) atTop (𝓝 0) := by
  rw [soninCoronaClass, soninCoronaClass, Submodule.Quotient.eq]
  have hcoe : ∀ n, ((f - g : SoninBoundedSeq) : ℕ → evenSubspace) n =
      (f : ℕ → evenSubspace) n - (g : ℕ → evenSubspace) n := by
    intro n; rw [lp.coeFn_sub]; rfl
  constructor
  · intro h
    refine (h : Tendsto (fun n => ‖((f - g : SoninBoundedSeq) : ℕ → evenSubspace) n‖) atTop
      (𝓝 0)).congr fun n => ?_
    rw [hcoe n]
  · intro h
    show Tendsto (fun n => ‖((f - g : SoninBoundedSeq) : ℕ → evenSubspace) n‖) atTop (𝓝 0)
    refine h.congr fun n => ?_
    rw [hcoe n]

/-- The quotient norm is bounded by the supremum norm. -/
theorem norm_soninCoronaClass_le (f : SoninBoundedSeq) : ‖soninCoronaClass f‖ ≤ ‖f‖ :=
  Submodule.Quotient.norm_mk_le _ _

/-- Bounded families in the two models are the same module. -/
def soninBoundedEquiv : soninBoundedFamilies ≃ₗ[ℂ] SoninBoundedSeq where
  toFun f := ⟨(f : ℕ → evenSubspace), memℓp_infty_iff.mpr (by
    obtain ⟨M, hM⟩ := f.2
    exact ⟨M, by rintro x ⟨n, rfl⟩; exact hM n⟩)⟩
  map_add' f g := by
    refine Subtype.ext (funext fun n => ?_)
    rw [lp.coeFn_add]
    rfl
  map_smul' c f := by
    refine Subtype.ext (funext fun n => ?_)
    rw [lp.coeFn_smul]
    rfl
  invFun g := ⟨(g : ℕ → evenSubspace),
    ⟨‖g‖, fun n => lp.norm_apply_le_norm (E := fun _ : ℕ => evenSubspace) ENNReal.top_ne_zero g n⟩⟩
  left_inv f := Subtype.ext rfl
  right_inv g := Subtype.ext rfl

@[simp] theorem coe_soninBoundedEquiv (f : soninBoundedFamilies) (n : ℕ) :
    ((soninBoundedEquiv f : SoninBoundedSeq) : ℕ → evenSubspace) n =
      (f : ℕ → evenSubspace) n := rfl

/-- The isomorphism carries null families to null families. -/
theorem map_soninNullInBounded :
    soninNullInBounded.map (soninBoundedEquiv : soninBoundedFamilies →ₗ[ℂ] SoninBoundedSeq) =
      soninNullSeq := by
  ext g
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro hg
    exact ⟨soninBoundedEquiv.symm g, hg, soninBoundedEquiv.apply_symm_apply g⟩

/-- **The two coronas agree.** -/
def soninCoronaEquiv : SoninCorona ≃ₗ[ℂ] SoninCoronaSpace :=
  Submodule.Quotient.equiv soninNullInBounded soninNullSeq soninBoundedEquiv
    map_soninNullInBounded

@[simp] theorem soninCoronaEquiv_soninBoundaryClass (f : soninBoundedFamilies) :
    soninCoronaEquiv (soninBoundaryClass f) = soninCoronaClass (soninBoundedEquiv f) := rfl

/-- **`(20)` in the Banach corona.** -/
theorem soninCoronaClass_soninCouplingFamily
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    soninCoronaClass (soninBoundedEquiv (soninCouplingFamily a b c hb hbc hab.le q r hrgt)) =
      soninCoronaClass (soninBoundedEquiv (soninDilatedPacketFamily b c hb hbc q r hrpos)) := by
  have h := soninBoundaryClass_soninCouplingFamily a b c ha hb hab hbc q haq hqb r hrpos hrgt
    hcr hr
  simpa using congrArg soninCoronaEquiv h

/-- **`(21)` in the Banach corona.** -/
theorem soninCoronaClass_soninAdjointCouplingFamily
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hr : Tendsto r atTop atTop) :
    soninCoronaClass
        (soninBoundedEquiv (soninAdjointCouplingFamily a b c hb hbc hab.le q r hrpos hrgt)) =
      soninCoronaClass (soninBoundedEquiv (soninPacketFamily b c hb hbc q r)) := by
  have h := soninBoundaryClass_soninAdjointCouplingFamily a b c ha hb hab hbc q haq hqb r hrpos
    hrgt hr
  simpa using congrArg soninCoronaEquiv h

/-- The packet class has strictly positive corona norm. -/
theorem norm_soninCoronaClass_soninPacketFamily_pos
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    0 < ‖soninCoronaClass (soninBoundedEquiv (soninPacketFamily b c hb hbc q r))‖ := by
  refine norm_pos_iff.mpr ?_
  have h := soninBoundaryClass_soninPacketFamily_ne_zero b c hb hbc q hq r hr
  intro hzero
  refine h ?_
  have : soninCoronaEquiv (soninBoundaryClass (soninPacketFamily b c hb hbc q r)) = 0 := by
    simpa using hzero
  simpa using soninCoronaEquiv.injective (by simpa using this)

/-- The dilate class has strictly positive corona norm. -/
theorem norm_soninCoronaClass_soninDilatedPacketFamily_pos
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    0 < ‖soninCoronaClass (soninBoundedEquiv (soninDilatedPacketFamily b c hb hbc q r hrpos))‖ := by
  refine norm_pos_iff.mpr ?_
  have h := soninBoundaryClass_soninDilatedPacketFamily_ne_zero b c hb hbc q hq r hrpos hr
  intro hzero
  refine h ?_
  have : soninCoronaEquiv (soninBoundaryClass (soninDilatedPacketFamily b c hb hbc q r hrpos))
      = 0 := by
    simpa using hzero
  simpa using soninCoronaEquiv.injective (by simpa using this)

/-- Reindexing a bounded family along a clock map. -/
def soninReindex (σ : ℕ → ℕ) (f : SoninBoundedSeq) : SoninBoundedSeq :=
  ⟨fun n => (f : ℕ → evenSubspace) (σ n),
    memℓp_infty_of_forall_norm_le fun n =>
      lp.norm_apply_le_norm (E := fun _ : ℕ => evenSubspace) ENNReal.top_ne_zero f (σ n)⟩

@[simp] theorem coe_soninReindex (σ : ℕ → ℕ) (f : SoninBoundedSeq) (n : ℕ) :
    ((soninReindex σ f : SoninBoundedSeq) : ℕ → evenSubspace) n =
      (f : ℕ → evenSubspace) (σ n) := rfl

theorem norm_soninReindex_le (σ : ℕ → ℕ) (f : SoninBoundedSeq) :
    ‖soninReindex σ f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_le (norm_nonneg f) fun n =>
    lp.norm_apply_le_norm (E := fun _ : ℕ => evenSubspace) ENNReal.top_ne_zero f (σ n)

/-- **Reindexing along a surjective clock is isometric.** -/
theorem norm_soninReindex (σ : ℕ → ℕ) (hσ : Function.Surjective σ) (f : SoninBoundedSeq) :
    ‖soninReindex σ f‖ = ‖f‖ := by
  refine le_antisymm (norm_soninReindex_le σ f) ?_
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun i => ?_
  obtain ⟨n, rfl⟩ := hσ i
  exact lp.norm_apply_le_norm (E := fun _ : ℕ => evenSubspace) ENNReal.top_ne_zero
    (soninReindex σ f) n

/-- Reindexing is linear. -/
def soninReindexₗ (σ : ℕ → ℕ) : SoninBoundedSeq →ₗ[ℂ] SoninBoundedSeq where
  toFun := soninReindex σ
  map_add' f g := by
    refine Subtype.ext (funext fun n => ?_)
    show (f : ℕ → evenSubspace) (σ n) + (g : ℕ → evenSubspace) (σ n) =
      ((soninReindex σ f + soninReindex σ g : SoninBoundedSeq) : ℕ → evenSubspace) n
    rw [lp.coeFn_add]
    rfl
  map_smul' c f := by
    refine Subtype.ext (funext fun n => ?_)
    show c • (f : ℕ → evenSubspace) (σ n) =
      ((c • soninReindex σ f : SoninBoundedSeq) : ℕ → evenSubspace) n
    rw [lp.coeFn_smul]
    rfl

/-- An escaping clock reindex preserves nullity, so it descends to the corona. -/
def soninCoronaReindex (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    SoninCoronaSpace →ₗ[ℂ] SoninCoronaSpace :=
  Submodule.mapQ soninNullSeq soninNullSeq (soninReindexₗ σ) (by
    intro f hf
    show Tendsto (fun n => ‖((soninReindex σ f : SoninBoundedSeq) : ℕ → evenSubspace) n‖)
      atTop (𝓝 0)
    exact (hf : Tendsto (fun n => ‖(f : ℕ → evenSubspace) n‖) atTop (𝓝 0)).comp hσ)

@[simp] theorem soninCoronaReindex_soninCoronaClass (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop)
    (f : SoninBoundedSeq) :
    soninCoronaReindex σ hσ (soninCoronaClass f) = soninCoronaClass (soninReindex σ f) := rfl

end RHTower
