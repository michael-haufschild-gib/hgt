import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CofinalInverseCapacity
import Mathlib

/-!
# The Hilbert chart of the cofinal inverse-capacity law

In a Hilbert source the stage filling norm of a cofinal port tower is computed by a Gram operator.
For a finite-dimensional port stage `S` inside the domain of `T` on which `T` is surjective, write
`T_S` for the restriction of `T` to `S` and `G_S = T_S T_S^*`.  Then `G_S` is invertible, `Q_S`
denotes its inverse, the minimum-norm lift of `y` is `T_S^* Q_S y`, and

`q_S(y)^2 = re ⟪Q_S y, y⟫`.

Along a tower the Gram quadratic forms increase and the inverse capacities decrease; the inverse
capacities converge to an operator `Q_∞` whose quadratic form is the square of the limiting filling
seminorm, so that

`ker Q_∞ = {y | q_∞ y = 0} = mul (closure (graph T))`.

For a scalar output the filling norm and the capacity are exactly reciprocal, so the closed relation
is either single valued or totally vertical.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology InnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

/-! ## Gram operators of a port stage -/

section Stage

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]

variable (T : X →ₗ.[𝕜] Y) (S : Submodule 𝕜 X) (h : S ≤ T.domain)

/-- The restriction of `T` to a port stage. -/
def portStageMap : S →ₗ[𝕜] Y := T.toFun ∘ₗ Submodule.inclusion h

omit [FiniteDimensional 𝕜 Y] in
@[simp] theorem portStageMap_apply (v : S) :
    portStageMap T S h v = T (Submodule.inclusion h v) := rfl

variable [FiniteDimensional 𝕜 S]

/-- The adjoint co-lift of a port stage, read inside the domain of `T`. -/
noncomputable def portCoLift : Y →ₗ[𝕜] T.domain :=
  Submodule.inclusion h ∘ₗ LinearMap.adjoint (portStageMap T S h)

/-- The **stage Gram operator** `T_S T_S^*` on the target. -/
noncomputable def portGram : Y →ₗ[𝕜] Y := T.toFun ∘ₗ portCoLift T S h

theorem portGram_apply (z : Y) : portGram T S h z = T (portCoLift T S h z) := rfl

theorem portCoLift_mem (z : Y) : ((portCoLift T S h z : T.domain) : X) ∈ S :=
  (LinearMap.adjoint (portStageMap T S h) z).2

/-- The defining adjunction of the co-lift. -/
theorem inner_portCoLift (z : Y) (v : T.domain) (hv : (v : X) ∈ S) :
    ⟪((portCoLift T S h z : T.domain) : X), (v : X)⟫_𝕜 = ⟪z, T v⟫_𝕜 := by
  have hadj := LinearMap.adjoint_inner_left (portStageMap T S h) (⟨(v : X), hv⟩ : S) z
  rw [Submodule.coe_inner] at hadj
  have hv' : Submodule.inclusion h (⟨(v : X), hv⟩ : S) = v := Subtype.ext rfl
  rw [portStageMap_apply, hv'] at hadj
  exact hadj

theorem inner_portCoLift_portCoLift (z w : Y) :
    ⟪((portCoLift T S h z : T.domain) : X), ((portCoLift T S h w : T.domain) : X)⟫_𝕜
      = ⟪z, portGram T S h w⟫_𝕜 := by
  rw [inner_portCoLift T S h z _ (portCoLift_mem T S h w), portGram_apply]

/-- The **stage capacity**: the Gram quadratic form. -/
noncomputable def portCapacity (z : Y) : ℝ := ‖((portCoLift T S h z : T.domain) : X)‖ ^ 2

theorem portCapacity_eq (z : Y) : portCapacity T S h z = RCLike.re ⟪z, portGram T S h z⟫_𝕜 := by
  have hz := inner_portCoLift_portCoLift T S h z z
  rw [inner_self_eq_norm_sq_to_K] at hz
  have h2 := congrArg (RCLike.re (K := 𝕜)) hz
  simpa [portCapacity] using h2

/-- **The Gram quadratic form increases with the stage.** -/
theorem portCapacity_mono {S' : Submodule 𝕜 X} (h' : S' ≤ T.domain) [FiniteDimensional 𝕜 S']
    (hSS : S ≤ S') (z : Y) : portCapacity T S h z ≤ portCapacity T S' h' z := by
  set a := ((portCoLift T S h z : T.domain) : X) with ha
  set b := ((portCoLift T S' h' z : T.domain) : X) with hb
  have hperp : ⟪a, b - a⟫_𝕜 = 0 := by
    have h1 : ⟪a, a⟫_𝕜 = ⟪z, T (portCoLift T S h z)⟫_𝕜 :=
      inner_portCoLift T S h z _ (portCoLift_mem T S h z)
    have h2 : ⟪b, a⟫_𝕜 = ⟪z, T (portCoLift T S h z)⟫_𝕜 :=
      inner_portCoLift T S' h' z _ (hSS (portCoLift_mem T S h z))
    have hba : ⟪b - a, a⟫_𝕜 = 0 := by rw [inner_sub_left, h2, h1, sub_self]
    rw [← inner_conj_symm, hba, map_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a (b - a) hperp
  rw [add_sub_cancel] at hpy
  simp only [portCapacity, ← ha, ← hb]
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (b - a)]


/-- **Characterization of the co-lift.**  An element of the stage that reproduces the adjunction
is the co-lift. -/
theorem portCoLift_eq (z : Y) (u : T.domain) (hu : (u : X) ∈ S)
    (hchar : ∀ v : T.domain, (v : X) ∈ S → ⟪(u : X), (v : X)⟫_𝕜 = ⟪z, T v⟫_𝕜) :
    portCoLift T S h z = u := by
  set d : T.domain := portCoLift T S h z - u with hd
  have hdS : ((d : T.domain) : X) ∈ S := by
    have : ((portCoLift T S h z - u : T.domain) : X)
        = ((portCoLift T S h z : T.domain) : X) - (u : X) := by simp
    rw [hd, this]
    exact S.sub_mem (portCoLift_mem T S h z) hu
  have hzero : ⟪((d : T.domain) : X), ((d : T.domain) : X)⟫_𝕜 = 0 := by
    have h1 := inner_portCoLift T S h z d hdS
    have h2 := hchar d hdS
    have hexp : ⟪((d : T.domain) : X), ((d : T.domain) : X)⟫_𝕜
        = ⟪((portCoLift T S h z : T.domain) : X), ((d : T.domain) : X)⟫_𝕜
          - ⟪(u : X), ((d : T.domain) : X)⟫_𝕜 := by
      rw [← inner_sub_left]
      congr 2
    rw [hexp, h1, h2, sub_self]
  have : ((d : T.domain) : X) = 0 := inner_self_eq_zero.mp hzero
  have hd0 : d = 0 := Subtype.ext this
  rw [hd] at hd0
  exact sub_eq_zero.mp hd0

/-- The Gram operator evaluated through an explicit co-lift. -/
theorem portGram_eq_of_coLift (z : Y) (u : T.domain) (hu : (u : X) ∈ S)
    (hchar : ∀ v : T.domain, (v : X) ∈ S → ⟪(u : X), (v : X)⟫_𝕜 = ⟪z, T v⟫_𝕜) :
    portGram T S h z = T u := by
  rw [portGram_apply, portCoLift_eq T S h z u hu hchar]

/-! ## The inverse capacity of a filling stage -/

theorem portGram_injective (hs : PortFilling T S) : Function.Injective (portGram T S h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hnorm : portCapacity T S h z = 0 := by
    rw [portCapacity_eq, hz]
    simp
  have hzero : ((portCoLift T S h z : T.domain) : X) = 0 := by
    have hn : ‖((portCoLift T S h z : T.domain) : X)‖ = 0 := by
      have := norm_nonneg ((portCoLift T S h z : T.domain) : X)
      simp only [portCapacity] at hnorm
      nlinarith
    rwa [norm_eq_zero] at hn
  have hall : ∀ y : Y, ⟪z, y⟫_𝕜 = 0 := by
    intro y
    obtain ⟨v, hv, hTv⟩ := hs y
    have hiv := inner_portCoLift T S h z v hv
    rw [hzero, hTv, inner_zero_left] at hiv
    exact hiv.symm
  exact inner_self_eq_zero.mp (hall z)

/-- The **inverse capacity** `Q_S = G_S⁻¹` of a filling stage. -/
noncomputable def portInvGram (hs : PortFilling T S) : Y →ₗ[𝕜] Y :=
  (LinearEquiv.ofBijective (portGram T S h)
    ⟨portGram_injective T S h hs,
      LinearMap.injective_iff_surjective.mp (portGram_injective T S h hs)⟩).symm

@[simp] theorem portGram_portInvGram (hs : PortFilling T S) (y : Y) :
    portGram T S h (portInvGram T S h hs y) = y :=
  (LinearEquiv.ofBijective (portGram T S h)
    ⟨portGram_injective T S h hs,
      LinearMap.injective_iff_surjective.mp (portGram_injective T S h hs)⟩).apply_symm_apply y

/-- The **minimum-norm lift** `T_S^* Q_S y`. -/
noncomputable def portMinLift (hs : PortFilling T S) (y : Y) : T.domain :=
  portCoLift T S h (portInvGram T S h hs y)

theorem portMinLift_mem (hs : PortFilling T S) (y : Y) :
    ((portMinLift T S h hs y : T.domain) : X) ∈ S := portCoLift_mem T S h _

@[simp] theorem map_portMinLift (hs : PortFilling T S) (y : Y) :
    T (portMinLift T S h hs y) = y := by
  rw [portMinLift, ← portGram_apply, portGram_portInvGram]

/-- The squared minimum filling energy is the inverse-capacity quadratic form. -/
theorem normSq_portMinLift (hs : PortFilling T S) (y : Y) :
    ‖((portMinLift T S h hs y : T.domain) : X)‖ ^ 2 = RCLike.re ⟪portInvGram T S h hs y, y⟫_𝕜 := by
  have hc := portCapacity_eq T S h (portInvGram T S h hs y)
  rw [portGram_portInvGram] at hc
  exact hc

/-- Any lift is at least as long as the minimum-norm lift. -/
theorem norm_portMinLift_le (hs : PortFilling T S) {y : Y} {x : T.domain}
    (hx : (x : X) ∈ S) (hTx : T x = y) :
    ‖((portMinLift T S h hs y : T.domain) : X)‖ ≤ ‖(x : X)‖ := by
  set m := ((portMinLift T S h hs y : T.domain) : X) with hm
  have hmem : ((x - portMinLift T S h hs y : T.domain) : X) ∈ S := by
    simpa using S.sub_mem hx (portMinLift_mem T S h hs y)
  have hperp : ⟪m, (x : X) - m⟫_𝕜 = 0 := by
    have hiv := inner_portCoLift T S h (portInvGram T S h hs y)
      (x - portMinLift T S h hs y) hmem
    rw [T.map_sub, hTx, map_portMinLift, sub_self, inner_zero_right] at hiv
    simpa [hm, portMinLift] using hiv
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero m ((x : X) - m) hperp
  rw [add_sub_cancel] at hpy
  nlinarith [norm_nonneg m, norm_nonneg (x : X), norm_nonneg ((x : X) - m)]

theorem portFillNorm_eq (hs : PortFilling T S) (y : Y) :
    portFillNorm T S y = ‖((portMinLift T S h hs y : T.domain) : X)‖ :=
  le_antisymm (portFillNorm_le T (portMinLift_mem T S h hs y) (map_portMinLift T S h hs y))
    (le_csInf (portLiftNorms_nonempty T hs y) (by
      rintro r ⟨x, hx, hTx, rfl⟩
      exact norm_portMinLift_le T S h hs hx hTx))

/-- **Exact inverse-capacity formula.**  The squared stage filling norm is the quadratic form of
the inverse Gram operator. -/
theorem portFillNorm_sq (hs : PortFilling T S) (y : Y) :
    portFillNorm T S y ^ 2 = RCLike.re ⟪portInvGram T S h hs y, y⟫_𝕜 := by
  rw [portFillNorm_eq T S h hs y, normSq_portMinLift]

theorem inner_portMinLift (hs : PortFilling T S) (y z : Y) :
    ⟪((portMinLift T S h hs y : T.domain) : X), ((portMinLift T S h hs z : T.domain) : X)⟫_𝕜
      = ⟪portInvGram T S h hs y, z⟫_𝕜 := by
  rw [portMinLift, portMinLift, inner_portCoLift_portCoLift, portGram_portInvGram]

end Stage

/-! ## Hilbert port towers -/

section Tower

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
variable {T : X →ₗ.[𝕜] Y}

/-- A cofinal port tower whose stages are finite dimensional. -/
structure HilbertPortTower (T : X →ₗ.[𝕜] Y) extends PortTower T where
  /-- Every stage is finite dimensional. -/
  finite : ∀ n, FiniteDimensional 𝕜 (stage n)

namespace HilbertPortTower

variable (P : HilbertPortTower T)

instance instFiniteStage (n : ℕ) : FiniteDimensional 𝕜 (P.stage n) := P.finite n

/-- The Gram operator of the `k`-th stage past the base. -/
noncomputable def gram (k : ℕ) : Y →ₗ[𝕜] Y :=
  portGram T (P.stage (P.base + k)) (P.toPortTower.stage_le _)

/-- The inverse capacity of the `k`-th stage past the base. -/
noncomputable def invGram (k : ℕ) : Y →ₗ[𝕜] Y :=
  portInvGram T (P.stage (P.base + k)) (P.toPortTower.stage_le _) (P.toPortTower.filling_add k)

/-- The minimum-norm lift at the `k`-th stage past the base. -/
noncomputable def minLift (k : ℕ) (y : Y) : X :=
  ((portMinLift T (P.stage (P.base + k)) (P.toPortTower.stage_le _)
    (P.toPortTower.filling_add k) y : T.domain) : X)

theorem norm_minLift (k : ℕ) (y : Y) : ‖P.minLift k y‖ = P.toPortTower.fillNorm k y :=
  (portFillNorm_eq T _ (P.toPortTower.stage_le _) (P.toPortTower.filling_add k) y).symm

theorem minLift_mem (k : ℕ) (y : Y) : P.minLift k y ∈ P.stage (P.base + k) :=
  portMinLift_mem T _ _ _ y

theorem inner_minLift (k : ℕ) (y z : Y) :
    ⟪P.minLift k y, P.minLift k z⟫_𝕜 = ⟪P.invGram k y, z⟫_𝕜 :=
  inner_portMinLift T _ (P.toPortTower.stage_le _) (P.toPortTower.filling_add k) y z

theorem re_inner_invGram (k : ℕ) (y : Y) :
    RCLike.re ⟪P.invGram k y, y⟫_𝕜 = P.toPortTower.fillNorm k y ^ 2 :=
  (portFillNorm_sq T (P.stage (P.base + k)) (P.toPortTower.stage_le _)
    (P.toPortTower.filling_add k) y).symm

/-- **The Gram family increases along the tower.** -/
theorem re_inner_gram_mono {k l : ℕ} (hkl : k ≤ l) (z : Y) :
    RCLike.re ⟪z, P.gram k z⟫_𝕜 ≤ RCLike.re ⟪z, P.gram l z⟫_𝕜 := by
  have hmono := portCapacity_mono T (P.stage (P.base + k)) (P.toPortTower.stage_le _)
    (S' := P.stage (P.base + l)) (P.toPortTower.stage_le _)
    (P.mono (Nat.add_le_add_left hkl _)) z
  rw [portCapacity_eq, portCapacity_eq] at hmono
  exact hmono

/-- **The inverse capacities decrease along the tower.** -/
theorem re_inner_invGram_antitone {k l : ℕ} (hkl : k ≤ l) (y : Y) :
    RCLike.re ⟪P.invGram l y, y⟫_𝕜 ≤ RCLike.re ⟪P.invGram k y, y⟫_𝕜 := by
  rw [P.re_inner_invGram, P.re_inner_invGram]
  have hmono := P.toPortTower.fillNorm_antitone y hkl
  nlinarith [P.toPortTower.fillNorm_nonneg k y, P.toPortTower.fillNorm_nonneg l y]

/-- Cofinal minimum-norm lifts of the same output are orthogonally nested. -/
theorem inner_minLift_sub {k l : ℕ} (hkl : k ≤ l) (y z : Y) :
    ⟪P.minLift l y, P.minLift k z - P.minLift l z⟫_𝕜 = 0 := by
  have hmem : P.minLift k z - P.minLift l z ∈ P.stage (P.base + l) :=
    Submodule.sub_mem _ (P.mono (Nat.add_le_add_left hkl _) (P.minLift_mem k z))
      (P.minLift_mem l z)
  set vk := portMinLift T (P.stage (P.base + k)) (P.toPortTower.stage_le _)
    (P.toPortTower.filling_add k) z with hvk
  set vl := portMinLift T (P.stage (P.base + l)) (P.toPortTower.stage_le _)
    (P.toPortTower.filling_add l) z with hvl
  have hmem' : (((vk - vl : T.domain)) : X) ∈ P.stage (P.base + l) := by
    simpa [minLift, hvk, hvl] using hmem
  have hiv := inner_portCoLift T (P.stage (P.base + l)) (P.toPortTower.stage_le _)
    (portInvGram T (P.stage (P.base + l)) (P.toPortTower.stage_le _)
      (P.toPortTower.filling_add l) y) (vk - vl) hmem'
  rw [T.map_sub, hvk, hvl, map_portMinLift, map_portMinLift, sub_self, inner_zero_right] at hiv
  simpa [minLift, portMinLift, hvk, hvl] using hiv

/-- The Pythagorean decomposition of nested minimum-norm lifts. -/
theorem normSq_minLift_sub {k l : ℕ} (hkl : k ≤ l) (y : Y) :
    ‖P.minLift k y - P.minLift l y‖ ^ 2 = ‖P.minLift k y‖ ^ 2 - ‖P.minLift l y‖ ^ 2 := by
  have hperp : ⟪P.minLift l y, P.minLift k y - P.minLift l y⟫_𝕜 = 0 :=
    P.inner_minLift_sub hkl y y
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P.minLift l y)
    (P.minLift k y - P.minLift l y) hperp
  rw [add_sub_cancel] at hpy
  nlinarith [hpy]

/-- The exact defect of the inverse-capacity sesquilinear form between two stages. -/
theorem inner_invGram_sub {k l : ℕ} (hkl : k ≤ l) (y z : Y) :
    ⟪P.invGram k y, z⟫_𝕜 - ⟪P.invGram l y, z⟫_𝕜
      = ⟪P.minLift k y - P.minLift l y, P.minLift k z⟫_𝕜 := by
  have hk := P.inner_minLift k y z
  have hl := P.inner_minLift l y z
  have hcross : ⟪P.minLift l y, P.minLift k z - P.minLift l z⟫_𝕜 = 0 :=
    P.inner_minLift_sub hkl y z
  rw [inner_sub_right] at hcross
  rw [← hk, ← hl, inner_sub_left]
  have hmid : ⟪P.minLift l y, P.minLift k z⟫_𝕜 = ⟪P.minLift l y, P.minLift l z⟫_𝕜 :=
    sub_eq_zero.mp hcross
  rw [hmid]

/-! ### The limiting inverse capacity -/

/-- A uniform bound for the minimum-norm lifts along the tower. -/
theorem exists_minLift_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (y : Y), ‖P.minLift k y‖ ≤ C * ‖y‖ := by
  obtain ⟨C, hC0, hC⟩ := P.toPortTower.exists_fillNorm_bound
  refine ⟨C + 1, by linarith, fun k y => ?_⟩
  have hk := hC k y
  rw [P.norm_minLift]
  nlinarith [norm_nonneg y]

/-- The inverse capacity is controlled by the minimum-norm lift. -/
theorem norm_invGram_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (k : ℕ) (y : Y), ‖P.minLift k y‖ ≤ C * ‖y‖)
    (k : ℕ) (y : Y) : ‖P.invGram k y‖ ≤ C * ‖P.minLift k y‖ := by
  set w := P.invGram k y with hw
  have hinner : ⟪w, w⟫_𝕜 = ⟪P.minLift k y, P.minLift k w⟫_𝕜 := (P.inner_minLift k y w).symm
  have hsq : ‖w‖ ^ 2 = RCLike.re ⟪w, w⟫_𝕜 := (inner_self_eq_norm_sq w).symm
  have hbound : RCLike.re ⟪P.minLift k y, P.minLift k w⟫_𝕜 ≤ ‖P.minLift k y‖ * (C * ‖w‖) := by
    refine le_trans (RCLike.re_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
    exact mul_le_mul_of_nonneg_left (hC k w) (norm_nonneg _)
  rw [hinner] at hsq
  rcases eq_or_lt_of_le (norm_nonneg w) with hzero | hpos
  · rw [← hzero]
    positivity
  · nlinarith [hbound, hsq]

/-- The exact Cauchy estimate for the inverse capacities. -/
theorem norm_invGram_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (k : ℕ) (y : Y), ‖P.minLift k y‖ ≤ C * ‖y‖)
    {k l : ℕ} (hkl : k ≤ l) (y : Y) :
    ‖P.invGram k y - P.invGram l y‖ ≤ C * ‖P.minLift k y - P.minLift l y‖ := by
  set w := P.invGram k y - P.invGram l y with hw
  have hdefect := P.inner_invGram_sub hkl y w
  have hleft : ⟪w, w⟫_𝕜 = ⟪P.invGram k y, w⟫_𝕜 - ⟪P.invGram l y, w⟫_𝕜 := by
    rw [hw, inner_sub_left]
  have hsq : ‖w‖ ^ 2 = RCLike.re ⟪w, w⟫_𝕜 := (inner_self_eq_norm_sq w).symm
  rw [hleft, hdefect] at hsq
  have hbound : RCLike.re ⟪P.minLift k y - P.minLift l y, P.minLift k w⟫_𝕜
      ≤ ‖P.minLift k y - P.minLift l y‖ * (C * ‖w‖) := by
    refine le_trans (RCLike.re_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
    exact mul_le_mul_of_nonneg_left (hC k w) (norm_nonneg _)
  rcases eq_or_lt_of_le (norm_nonneg w) with hzero | hpos
  · rw [← hzero]
    have h0 : (0:ℝ) ≤ ‖P.minLift k y - P.minLift l y‖ := norm_nonneg _
    positivity
  · nlinarith [hbound, hsq]

theorem cauchySeq_invGram (y : Y) : CauchySeq fun k => P.invGram k y := by
  obtain ⟨C, hCpos, hC⟩ := P.exists_minLift_bound
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsq : Tendsto (fun k => P.toPortTower.fillNorm k y ^ 2) atTop
      (𝓝 (P.toPortTower.fillNormInf y ^ 2)) := (P.toPortTower.tendsto_fillNorm y).pow 2
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hsq.cauchySeq ((ε / (C + 1)) ^ 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have key : ∀ a b : ℕ, N ≤ a → N ≤ b → a ≤ b →
      ‖P.invGram a y - P.invGram b y‖ < ε := by
    intro a b ha hb hab
    have hd := hN b hb a ha
    have hpyth := P.normSq_minLift_sub hab y
    rw [P.norm_minLift, P.norm_minLift] at hpyth
    have hlt : ‖P.minLift a y - P.minLift b y‖ ^ 2 < (ε / (C + 1)) ^ 2 := by
      rw [hpyth]
      have hgap : P.toPortTower.fillNorm a y ^ 2 - P.toPortTower.fillNorm b y ^ 2
          ≤ dist (P.toPortTower.fillNorm b y ^ 2) (P.toPortTower.fillNorm a y ^ 2) := by
        rw [Real.dist_eq, abs_sub_comm]
        exact le_abs_self _
      linarith
    have hnn : ‖P.minLift a y - P.minLift b y‖ < ε / (C + 1) := by
      nlinarith [norm_nonneg (P.minLift a y - P.minLift b y),
        (by positivity : (0:ℝ) < ε / (C + 1))]
    have := P.norm_invGram_sub_le hCpos.le hC hab y
    have hstep : C * ‖P.minLift a y - P.minLift b y‖ < C * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left hnn hCpos
    have hfin : C * (ε / (C + 1)) < ε := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < C + 1)]
      nlinarith
    linarith
  rw [dist_eq_norm]
  rcases le_total m n with hmn | hnm
  · exact key m n hm hn hmn
  · rw [← norm_neg]
    simpa using key n m hn hm hnm

theorem tendsto_invGram (y : Y) :
    Tendsto (fun k => P.invGram k y) atTop (𝓝 (limUnder atTop fun k => P.invGram k y)) := by
  haveI : CompleteSpace Y := FiniteDimensional.complete 𝕜 Y
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (P.cauchySeq_invGram y)
  rw [hx.limUnder_eq]
  exact hx

/-- The **limiting inverse capacity** `Q_∞`. -/
noncomputable def limitInvGram : Y →ₗ[𝕜] Y where
  toFun y := limUnder atTop fun k => P.invGram k y
  map_add' a b := by
    refine tendsto_nhds_unique (P.tendsto_invGram (a + b)) ?_
    have := (P.tendsto_invGram a).add (P.tendsto_invGram b)
    simpa only [map_add] using this
  map_smul' c y := by
    refine tendsto_nhds_unique (P.tendsto_invGram (c • y)) ?_
    have := (P.tendsto_invGram y).const_smul c
    simpa only [map_smul, RingHom.id_apply] using this

theorem tendsto_limitInvGram (y : Y) :
    Tendsto (fun k => P.invGram k y) atTop (𝓝 (P.limitInvGram y)) := P.tendsto_invGram y

/-- **The limiting inverse capacity carries the limiting filling seminorm.** -/
theorem re_inner_limitInvGram (y : Y) :
    RCLike.re ⟪P.limitInvGram y, y⟫_𝕜 = P.toPortTower.fillNormInf y ^ 2 := by
  have h1 : Tendsto (fun k => RCLike.re ⟪P.invGram k y, y⟫_𝕜) atTop
      (𝓝 (RCLike.re ⟪P.limitInvGram y, y⟫_𝕜)) := by
    have hinner : Tendsto (fun k => ⟪P.invGram k y, y⟫_𝕜) atTop
        (𝓝 ⟪P.limitInvGram y, y⟫_𝕜) :=
      (P.tendsto_limitInvGram y).inner tendsto_const_nhds
    exact (RCLike.continuous_re.tendsto _).comp hinner
  have h2 : Tendsto (fun k => RCLike.re ⟪P.invGram k y, y⟫_𝕜) atTop
      (𝓝 (P.toPortTower.fillNormInf y ^ 2)) := by
    simp only [P.re_inner_invGram]
    exact (P.toPortTower.tendsto_fillNorm y).pow 2
  exact tendsto_nhds_unique h1 h2

/-- **Hilbert form of the cofinal inverse-capacity law.**  The multivalued part of the closed
graph is exactly the kernel of the limiting inverse capacity. -/
theorem multivaluedHorizon_eq_ker :
    multivaluedHorizon T = (LinearMap.ker P.limitInvGram : Set Y) := by
  rw [P.toPortTower.multivaluedHorizon_eq]
  ext y
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro hy
    obtain ⟨C, hCpos, hC⟩ := P.exists_minLift_bound
    have hm : Tendsto (fun k => ‖P.minLift k y‖) atTop (𝓝 0) := by
      have := P.toPortTower.tendsto_fillNorm y
      rw [hy] at this
      simpa only [P.norm_minLift] using this
    have hb : ∀ k, ‖P.invGram k y‖ ≤ C * ‖P.minLift k y‖ :=
      fun k => P.norm_invGram_le hCpos.le hC k y
    have hzero : Tendsto (fun k => ‖P.invGram k y‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => norm_nonneg _) hb ?_
      simpa using hm.const_mul C
    have hlim := (P.tendsto_limitInvGram y).norm
    exact norm_eq_zero.mp (tendsto_nhds_unique hlim hzero)
  · intro hy
    have hre := P.re_inner_limitInvGram y
    rw [hy, inner_zero_left, map_zero] at hre
    have := P.toPortTower.fillNormInf_nonneg y
    nlinarith [hre]

end HilbertPortTower

end Tower

end HTGeometry.ConstraintMotiveRelativity
