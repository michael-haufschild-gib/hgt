import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import Mathlib

/-!
# Cofinal inverse capacity and the vertical fibre of a closed graph

A partially defined linear map `T` into a finite-dimensional target `Y` is filtered by an
increasing tower of subspaces `S₀ ⊆ S₁ ⊆ ⋯` of its domain whose union is the whole domain and on
which `T` is eventually surjective.  Each stage carries the *filling norm*

`q_k(y) = inf {‖x‖ : x ∈ S_k, T x = y}`,

which decreases in `k`; its limit `q_∞` is again a seminorm.  The main theorem identifies the
vanishing locus of `q_∞` with the multivalued part of the closed graph of `T`:

`{y | q_∞ y = 0} = {y | (0, y) ∈ closure (graph T)}`.

Consequently `T` is closable exactly when `q_∞` is a norm.

The proof is a two-sided estimate.  A vector with vanishing limiting filling norm has lifts of
arbitrarily small norm, which converge to `0` and exhibit `y` as a vertical limit.  Conversely a
vertical limit is approximated by domain vectors of small norm, and the stage seminorm inequality
`q_k(y) ≤ q_k(T z) + q_k(y - T z) ≤ ‖z‖ + C ‖y - T z‖` forces `q_∞ y = 0`, the constant `C` coming
from a linear right inverse of the base stage, continuous because `Y` is finite dimensional.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology InnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

/-! ## The stage filling norm -/

section FillNorm

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Norms of the lifts of `y` through `T` that stay inside the port stage `S`. -/
def portLiftNorms (T : X →ₗ.[𝕜] Y) (S : Submodule 𝕜 T.domain) (y : Y) : Set ℝ :=
  {r : ℝ | ∃ x : T.domain, x ∈ S ∧ T x = y ∧ ‖(x : X)‖ = r}

/-- The **stage filling norm**: the least norm of a lift of `y` inside the port stage `S`. -/
noncomputable def portFillNorm (T : X →ₗ.[𝕜] Y) (S : Submodule 𝕜 T.domain) (y : Y) : ℝ :=
  sInf (portLiftNorms T S y)

/-- The stage `S` fills the whole output: every target vector has a lift inside `S`. -/
def PortFilling (T : X →ₗ.[𝕜] Y) (S : Submodule 𝕜 T.domain) : Prop :=
  ∀ y : Y, ∃ x : T.domain, x ∈ S ∧ T x = y

variable (T : X →ₗ.[𝕜] Y)

theorem portLiftNorms_bddBelow (S : Submodule 𝕜 T.domain) (y : Y) :
    BddBelow (portLiftNorms T S y) := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, -, -, rfl⟩
  exact norm_nonneg _

theorem portFillNorm_nonneg (S : Submodule 𝕜 T.domain) (y : Y) : 0 ≤ portFillNorm T S y := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨x, -, -, rfl⟩
  exact norm_nonneg _

theorem portFillNorm_le {S : Submodule 𝕜 T.domain} {y : Y} {x : T.domain}
    (hx : x ∈ S) (hTx : T x = y) : portFillNorm T S y ≤ ‖(x : X)‖ :=
  csInf_le (portLiftNorms_bddBelow T S y) ⟨x, hx, hTx, rfl⟩

theorem portLiftNorms_nonempty {S : Submodule 𝕜 T.domain} (h : PortFilling T S) (y : Y) :
    (portLiftNorms T S y).Nonempty := by
  obtain ⟨x, hx, hTx⟩ := h y
  exact ⟨‖(x : X)‖, x, hx, hTx, rfl⟩

theorem exists_lift_norm_lt {S : Submodule 𝕜 T.domain} (h : PortFilling T S) (y : Y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : T.domain, x ∈ S ∧ T x = y ∧ ‖(x : X)‖ < portFillNorm T S y + ε := by
  obtain ⟨r, hr, hlt⟩ := Real.lt_sInf_add_pos (portLiftNorms_nonempty T h y) hε
  obtain ⟨x, hx, hTx, rfl⟩ := hr
  exact ⟨x, hx, hTx, hlt⟩

/-- Enlarging the stage can only decrease the filling norm. -/
theorem portFillNorm_antitone {S S' : Submodule 𝕜 T.domain} (hSS : S ≤ S')
    (h : PortFilling T S) (y : Y) : portFillNorm T S' y ≤ portFillNorm T S y := by
  refine csInf_le_csInf (portLiftNorms_bddBelow T S' y) (portLiftNorms_nonempty T h y) ?_
  rintro r ⟨x, hx, hTx, hr⟩
  exact ⟨x, hSS hx, hTx, hr⟩

@[simp] theorem portFillNorm_zero (S : Submodule 𝕜 T.domain) : portFillNorm T S 0 = 0 := by
  refine le_antisymm ?_ (portFillNorm_nonneg T S 0)
  have := portFillNorm_le T (S := S) (y := 0) (x := (0 : T.domain)) S.zero_mem T.map_zero
  simpa using this

/-- The stage filling norm is subadditive. -/
theorem portFillNorm_add_le {S : Submodule 𝕜 T.domain} (h : PortFilling T S) (a b : Y) :
    portFillNorm T S (a + b) ≤ portFillNorm T S a + portFillNorm T S b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨xa, hxa, hTa, hna⟩ := exists_lift_norm_lt T h a (half_pos hε)
  obtain ⟨xb, hxb, hTb, hnb⟩ := exists_lift_norm_lt T h b (half_pos hε)
  have hsum : portFillNorm T S (a + b) ≤ ‖((xa + xb : T.domain) : X)‖ :=
    portFillNorm_le T (S.add_mem hxa hxb) (by rw [T.map_add, hTa, hTb])
  have htri : ‖((xa + xb : T.domain) : X)‖ ≤ ‖(xa : X)‖ + ‖(xb : X)‖ := by
    simpa using norm_add_le ((xa : X)) ((xb : X))
  linarith

/-- The stage filling norm is absolutely homogeneous. -/
theorem portFillNorm_smul {S : Submodule 𝕜 T.domain} (h : PortFilling T S) (c : 𝕜) (y : Y) :
    portFillNorm T S (c • y) = ‖c‖ * portFillNorm T S y := by
  have key : ∀ (d : 𝕜) (z : Y), d ≠ 0 →
      portFillNorm T S (d • z) ≤ ‖d‖ * portFillNorm T S z := by
    intro d z hd
    have hdpos : 0 < ‖d‖ := by simpa [norm_pos_iff] using hd
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨x, hx, hTx, hn⟩ := exists_lift_norm_lt T h z (by positivity : 0 < ε / ‖d‖)
    have hlift : portFillNorm T S (d • z) ≤ ‖((d • x : T.domain) : X)‖ :=
      portFillNorm_le T (S.smul_mem d hx) (by rw [T.map_smul, hTx])
    have hnorm : ‖((d • x : T.domain) : X)‖ = ‖d‖ * ‖(x : X)‖ := by
      simp [norm_smul]
    have : ‖d‖ * ‖(x : X)‖ < ‖d‖ * (portFillNorm T S z + ε / ‖d‖) :=
      mul_lt_mul_of_pos_left hn hdpos
    have hexp : ‖d‖ * (portFillNorm T S z + ε / ‖d‖) = ‖d‖ * portFillNorm T S z + ε := by
      field_simp
    linarith [hlift, hnorm.le, hnorm.ge]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine le_antisymm (key c y hc) ?_
    have hback := key c⁻¹ (c • y) (inv_ne_zero hc)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at hback
    have hcpos : 0 < ‖c‖ := by simpa [norm_pos_iff] using hc
    have hscaled := mul_le_mul_of_nonneg_left hback hcpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at hscaled

end FillNorm

/-! ## Cofinal port towers -/

section Tower

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A **cofinal port tower** for a partially defined map `T`: an increasing exhaustion of the
domain by subspaces on which `T` is eventually surjective. -/
structure PortTower (T : X →ₗ.[𝕜] Y) where
  /-- The stages of the tower. -/
  stage : ℕ → Submodule 𝕜 T.domain
  /-- The stages increase. -/
  mono : Monotone stage
  /-- The stages exhaust the domain. -/
  exhaust : ⨆ n, stage n = ⊤
  /-- The index beyond which every stage fills the output. -/
  base : ℕ
  /-- Every stage beyond the base fills the output. -/
  filling : ∀ n, base ≤ n → PortFilling T (stage n)

variable {T : X →ₗ.[𝕜] Y}

/-- The filling norm of the `k`-th stage past the base. -/
noncomputable def PortTower.fillNorm (P : PortTower T) (k : ℕ) (y : Y) : ℝ :=
  portFillNorm T (P.stage (P.base + k)) y

theorem PortTower.fillNorm_def (P : PortTower T) (k : ℕ) (y : Y) :
    P.fillNorm k y = portFillNorm T (P.stage (P.base + k)) y := rfl

theorem PortTower.fillNorm_nonneg (P : PortTower T) (k : ℕ) (y : Y) : 0 ≤ P.fillNorm k y :=
  portFillNorm_nonneg _ _ _

theorem PortTower.filling_add (P : PortTower T) (k : ℕ) :
    PortFilling T (P.stage (P.base + k)) := P.filling _ (Nat.le_add_right _ _)

theorem PortTower.fillNorm_antitone (P : PortTower T) (y : Y) :
    Antitone fun k => P.fillNorm k y := by
  intro k l hkl
  exact portFillNorm_antitone T (P.mono (Nat.add_le_add_left hkl _)) (P.filling_add k) y

theorem PortTower.fillNorm_bddBelow (P : PortTower T) (y : Y) :
    BddBelow (Set.range fun k => P.fillNorm k y) := by
  refine ⟨0, ?_⟩
  rintro r ⟨k, rfl⟩
  exact P.fillNorm_nonneg k y

/-- The **limiting filling seminorm** of a cofinal port tower. -/
noncomputable def PortTower.fillNormInf (P : PortTower T) (y : Y) : ℝ :=
  ⨅ k, P.fillNorm k y

theorem PortTower.fillNormInf_le (P : PortTower T) (k : ℕ) (y : Y) :
    P.fillNormInf y ≤ P.fillNorm k y :=
  ciInf_le (P.fillNorm_bddBelow y) k

theorem PortTower.fillNormInf_nonneg (P : PortTower T) (y : Y) : 0 ≤ P.fillNormInf y :=
  le_ciInf fun k => P.fillNorm_nonneg k y

/-- The stage filling norms converge to the limiting filling seminorm. -/
theorem PortTower.tendsto_fillNorm (P : PortTower T) (y : Y) :
    Tendsto (fun k => P.fillNorm k y) atTop (𝓝 (P.fillNormInf y)) :=
  tendsto_atTop_ciInf (P.fillNorm_antitone y) (P.fillNorm_bddBelow y)

@[simp] theorem PortTower.fillNormInf_zero (P : PortTower T) : P.fillNormInf 0 = 0 := by
  refine le_antisymm ?_ (P.fillNormInf_nonneg 0)
  have := P.fillNormInf_le 0 0
  rwa [P.fillNorm_def, portFillNorm_zero] at this

theorem PortTower.fillNormInf_add_le (P : PortTower T) (a b : Y) :
    P.fillNormInf (a + b) ≤ P.fillNormInf a + P.fillNormInf b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk⟩ : ∃ k, P.fillNorm k a < P.fillNormInf a + ε / 2 := by
    by_contra hcon
    push_neg at hcon
    have : P.fillNormInf a + ε / 2 ≤ P.fillNormInf a := le_ciInf fun k => hcon k
    linarith
  obtain ⟨l, hl⟩ : ∃ l, P.fillNorm l b < P.fillNormInf b + ε / 2 := by
    by_contra hcon
    push_neg at hcon
    have : P.fillNormInf b + ε / 2 ≤ P.fillNormInf b := le_ciInf fun l => hcon l
    linarith
  set m := max k l with hm
  have hma : P.fillNorm m a ≤ P.fillNorm k a := P.fillNorm_antitone a (le_max_left k l)
  have hmb : P.fillNorm m b ≤ P.fillNorm l b := P.fillNorm_antitone b (le_max_right k l)
  have hsub : P.fillNorm m (a + b) ≤ P.fillNorm m a + P.fillNorm m b :=
    portFillNorm_add_le T (P.filling_add m) a b
  have := P.fillNormInf_le m (a + b)
  linarith

theorem PortTower.fillNormInf_smul (P : PortTower T) (c : 𝕜) (y : Y) :
    P.fillNormInf (c • y) = ‖c‖ * P.fillNormInf y := by
  have hstage : ∀ k, P.fillNorm k (c • y) = ‖c‖ * P.fillNorm k y := fun k =>
    portFillNorm_smul T (P.filling_add k) c y
  calc P.fillNormInf (c • y) = ⨅ k, ‖c‖ * P.fillNorm k y := by
        simp only [PortTower.fillNormInf, hstage]
    _ = ‖c‖ * ⨅ k, P.fillNorm k y := (Real.mul_iInf_of_nonneg (norm_nonneg c) _).symm
    _ = ‖c‖ * P.fillNormInf y := rfl

/-- **The limiting filling seminorm is a seminorm.** -/
noncomputable def PortTower.fillSeminorm (P : PortTower T) : Seminorm 𝕜 Y where
  toFun := P.fillNormInf
  map_zero' := P.fillNormInf_zero
  add_le' := P.fillNormInf_add_le
  neg' := by
    intro y
    have := P.fillNormInf_smul (-1 : 𝕜) y
    simpa using this
  smul' := P.fillNormInf_smul

@[simp] theorem PortTower.fillSeminorm_apply (P : PortTower T) (y : Y) :
    P.fillSeminorm y = P.fillNormInf y := rfl

end Tower

/-! ## The vertical fibre identity -/

section VerticalFibre

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {T : X →ₗ.[𝕜] Y}

theorem mem_graph_coe {x : T.domain} : ((x : X), T x) ∈ (T.graph : Set (X × Y)) :=
  (LinearPMap.mem_graph_iff T).mpr ⟨x, rfl, rfl⟩

/-- Every stage filling norm is dominated by a fixed multiple of the target norm. -/
theorem PortTower.exists_fillNorm_bound [FiniteDimensional 𝕜 Y] (P : PortTower T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (y : Y), P.fillNorm k y ≤ C * ‖y‖ := by
  classical
  set S := P.stage P.base with hS
  set A : S →ₗ[𝕜] Y := T.toFun ∘ₗ S.subtype with hA
  have hAsurj : LinearMap.range A = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx, hTx⟩ := P.filling P.base le_rfl y
    exact ⟨⟨x, hx⟩, hTx⟩
  obtain ⟨g, hg⟩ := A.exists_rightInverse_of_surjective hAsurj
  set R : Y →ₗ[𝕜] X := T.domain.subtype ∘ₗ S.subtype ∘ₗ g with hR
  have hRcont : Continuous R := LinearMap.continuous_of_finiteDimensional R
  set Rc : Y →L[𝕜] X := ⟨R, hRcont⟩ with hRc
  refine ⟨‖Rc‖, norm_nonneg _, fun k y => ?_⟩
  have hbase : P.fillNorm 0 y ≤ ‖Rc y‖ := by
    have hmem : ((S.subtype (g y) : T.domain)) ∈ S := (g y).2
    have hval : T (S.subtype (g y)) = y := by
      have := congrArg (fun (f : Y →ₗ[𝕜] Y) => f y) hg
      simpa [hA, LinearMap.comp_apply] using this
    have := portFillNorm_le T (S := P.stage (P.base + 0)) (x := (S.subtype (g y) : T.domain))
      (by simpa [hS] using hmem) hval
    simpa [PortTower.fillNorm, hRc, hR] using this
  have hmono : P.fillNorm k y ≤ P.fillNorm 0 y := P.fillNorm_antitone y (Nat.zero_le k)
  exact hmono.trans (hbase.trans (Rc.le_opNorm y))

/-- **Cofinal inverse-capacity law.**  The multivalued part of the closed graph of a partially
defined map is exactly the null space of the limiting filling seminorm of any cofinal port
tower. -/
theorem PortTower.multivaluedHorizon_eq [FiniteDimensional 𝕜 Y] (P : PortTower T) :
    multivaluedHorizon T = {y : Y | P.fillNormInf y = 0} := by
  ext y
  simp only [multivaluedHorizon, Set.mem_setOf_eq]
  constructor
  · intro hy
    obtain ⟨C, hC0, hC⟩ := P.exists_fillNorm_bound
    refine le_antisymm ?_ (P.fillNormInf_nonneg y)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ : ℝ := ε / (2 * (C + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hy δ hδ
    obtain ⟨u, hu1, hu2⟩ := (LinearPMap.mem_graph_iff T).mp hb
    have hd : dist ((0 : X), y) b = max (dist (0 : X) b.1) (dist y b.2) := Prod.dist_eq
    have h1 : ‖(u : X)‖ < δ := by
      have : dist (0 : X) b.1 ≤ dist ((0 : X), y) b := by rw [hd]; exact le_max_left _ _
      have h := lt_of_le_of_lt this hdist
      rwa [← hu1, dist_zero_left] at h
    have h2 : ‖y - T u‖ < δ := by
      have : dist y b.2 ≤ dist ((0 : X), y) b := by rw [hd]; exact le_max_right _ _
      have h := lt_of_le_of_lt this hdist
      rwa [← hu2, dist_eq_norm] at h
    obtain ⟨m, hm⟩ :=
      (Submodule.mem_iSup_of_directed P.stage (P.mono.directed_le)).mp
        (by rw [P.exhaust]; trivial : u ∈ ⨆ n, P.stage n)
    set k : ℕ := max m P.base - P.base with hk
    have hkbase : P.base + k = max m P.base := by
      have : P.base ≤ max m P.base := le_max_right _ _
      omega
    have humem : u ∈ P.stage (P.base + k) := by
      rw [hkbase]
      exact P.mono (le_max_left m P.base) hm
    have hstage : P.fillNorm k y ≤ P.fillNorm k (T u) + P.fillNorm k (y - T u) := by
      have h := portFillNorm_add_le T (P.filling_add k) (T u) (y - T u)
      rw [show T u + (y - T u) = y by abel] at h
      simpa only [P.fillNorm_def] using h
    have hTu : P.fillNorm k (T u) ≤ ‖(u : X)‖ := portFillNorm_le T humem rfl
    have hrest : P.fillNorm k (y - T u) ≤ C * ‖y - T u‖ := hC k _
    have hCd : C * ‖y - T u‖ ≤ C * δ := by
      exact mul_le_mul_of_nonneg_left h2.le hC0
    have hfinal : P.fillNormInf y ≤ δ + C * δ := by
      have := P.fillNormInf_le k y
      linarith
    have hδbound : δ + C * δ ≤ 0 + ε := by
      have hδe : δ * (1 + C) ≤ ε := by
        rw [hδdef]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (C + 1))]
        nlinarith
      nlinarith
    linarith
  · intro hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k, P.fillNorm k y < ε / 2 := by
      by_contra hcon
      push_neg at hcon
      have : ε / 2 ≤ P.fillNormInf y := le_ciInf fun k => hcon k
      rw [hy] at this
      linarith
    obtain ⟨x, hx, hTx, hn⟩ :=
      exists_lift_norm_lt T (P.filling_add k) y (show (0:ℝ) < ε / 2 by linarith)
    refine ⟨((x : X), T x), mem_graph_coe, ?_⟩
    rw [Prod.dist_eq]
    have h1 : dist (0 : X) (x : X) < ε := by
      rw [dist_zero_left]
      rw [P.fillNorm_def] at hk
      linarith
    have h2 : dist y (T x) = 0 := by rw [hTx]; simp
    simp only [h2]
    exact max_lt h1 (by linarith)

/-- **Closability criterion.**  `T` is closable exactly when its limiting filling seminorm is a
norm. -/
theorem PortTower.isClosable_iff [FiniteDimensional 𝕜 Y] (P : PortTower T) :
    T.IsClosable ↔ ∀ y : Y, P.fillNormInf y = 0 → y = 0 := by
  have hclosure : ∀ z : Y, ((0 : X), z) ∈ T.graph.topologicalClosure ↔ P.fillNormInf z = 0 := by
    intro z
    have hcoe : ((0 : X), z) ∈ T.graph.topologicalClosure
        ↔ ((0 : X), z) ∈ closure ((T.graph : Submodule 𝕜 (X × Y)) : Set (X × Y)) := by
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      rfl
    rw [hcoe]
    have : z ∈ multivaluedHorizon T ↔ z ∈ {y : Y | P.fillNormInf y = 0} := by
      rw [P.multivaluedHorizon_eq]
    simpa [multivaluedHorizon] using this
  constructor
  · rintro ⟨f', hf'⟩ y hy
    have hmem : ((0 : X), y) ∈ T.graph.topologicalClosure := (hclosure y).mpr hy
    rw [hf'] at hmem
    obtain ⟨u, hu1, hu2⟩ := (LinearPMap.mem_graph_iff f').mp hmem
    have hu0 : u = 0 := Subtype.ext hu1
    have : (0 : Y) = y := by rw [← f'.map_zero, ← hu0]; exact hu2
    exact this.symm
  · intro hnorm
    have hgraph : ∀ p ∈ T.graph.topologicalClosure, p.1 = 0 → p.2 = 0 := by
      intro p hp hp1
      have hp' : ((0 : X), p.2) ∈ T.graph.topologicalClosure := by
        rwa [← hp1]
      exact hnorm _ ((hclosure p.2).mp hp')
    exact ⟨T.graph.topologicalClosure.toLinearPMap,
      (Submodule.toLinearPMap_graph_eq _ hgraph).symm⟩

end VerticalFibre

end HTGeometry.ConstraintMotiveRelativity
