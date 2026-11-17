import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.TemperedConfigurationsWithAFiniteOffLineLayerHaveCriticalStates

/-!
# The critical state is the resolvent of its off-line layer (Birman–Schwinger)

Write a layered energy as `𝓔(X) = A(X) + ⟪V X, X⟫`: `A` the nonnegative series, `V X = Σ_k (v_k/2)
(⟪p_k, X⟫ q_k + ⟪q_k, X⟫ p_k)` the finite-rank layer (`layerVec`).

* **Resolvent** (`exists_resolvent`, `resolvent`, `resolventMap`). For `c > 0` and every `y` there is a
  unique admissible `X = R_c y` with `A(X, G) + c⟪X, G⟫ = ⟪y, G⟫` for all admissible `G`: the minimizer of
  the coercive convex functional `A(X) + c‖X‖² − 2⟪y, X⟫` (weak compactness and lower semicontinuity of
  the series). Uniqueness makes `R_c` linear.
* **Birman–Schwinger form** (`eq_resolvent_layerVec_of_groundState`). A ground state `F` with ground
  energy `−a < 0` satisfies `A(F, G) + a⟪F, G⟫ = −⟪V F, G⟫`, hence `F = R_a(−V F)`: the resolvent of the
  positive part applied to a combination of the finitely many layer vectors. So `F` lies in the span
  of the `2|κ|` vectors `R_a p_k, R_a q_k` (`mem_span_resolvent_of_groundState`).

**Tempered configurations** (`exists_configCriticalState_resolvent`). For every conjugation-invariant
tempered configuration with a finite nonempty off-line layer, possibly infinitely many on-line
zeros, the critical state is `R_a(−V F)` and lies in the span of the resolvents of the finitely many
off-line exponentials `e^{(z+8)u} cos(Im z · u)`, `e^{(z+8)u} sin(Im z · u)`, `z = ±(ρ − ½)`.
-/

noncomputable section
open Set Filter Topology Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GroundState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι κ : Type*}

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

namespace LayeredEnergy

variable (L : LayeredEnergy E ι κ)

/-- The polar form of the positive series. -/
def seriesPair (X G : E) : ℝ :=
  ∑' j, L.w j * (⟪L.a j, X⟫ * ⟪L.a j, G⟫ + ⟪L.b j, X⟫ * ⟪L.b j, G⟫)

/-- The finite-rank layer as an operator: `⟪V X, G⟫` is the layer part of the polar form. -/
def layerVec [Fintype κ] (X : E) : E :=
  ∑ k, (L.v k / 2) • (⟪L.p k, X⟫ • L.q k + ⟪L.q k, X⟫ • L.p k)

theorem seriesPair_self (X : E) : L.seriesPair X X = L.series X := by
  unfold seriesPair series term
  congr 1; funext j; ring

theorem admissible_zero : L.Admissible 0 := by
  unfold Admissible term; simp

theorem pair_eq_seriesPair_add [Fintype κ] (F G : E) :
    L.pair F G = L.seriesPair F G + ⟪L.layerVec F, G⟫ := by
  unfold pair seriesPair layerVec
  rw [sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  ring

theorem layerVec_mem_span [Fintype κ] (X : E) :
    L.layerVec X ∈ Submodule.span ℝ (Set.range L.p ∪ Set.range L.q) := by
  unfold layerVec
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨k, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨k, rfl⟩))))

theorem seriesPair_add_smul_left {X Y G : E} (hX : L.Admissible X) (hY : L.Admissible Y)
    (hG : L.Admissible G) (t : ℝ) :
    L.seriesPair (X + t • Y) G = L.seriesPair X G + t * L.seriesPair Y G := by
  unfold seriesPair
  rw [← tsum_mul_left, ← Summable.tsum_add (L.summable_cross hX hG)
    ((L.summable_cross hY hG).mul_left t)]
  congr 1; funext j
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
  ring

theorem series_add_smul {X G : E} (hX : L.Admissible X) (hG : L.Admissible G) (t : ℝ) :
    L.series (X + t • G) = L.series X + 2 * t * L.seriesPair X G + t ^ 2 * L.series G := by
  have e : L.term (X + t • G) = fun j => L.term X j +
      2 * t * (L.w j * (⟪L.a j, X⟫ * ⟪L.a j, G⟫ + ⟪L.b j, X⟫ * ⟪L.b j, G⟫)) + t ^ 2 * L.term G j := by
    funext j
    unfold term
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  unfold series seriesPair
  rw [e, Summable.tsum_add (hX.add ((L.summable_cross hX hG).mul_left (2 * t))) (hG.mul_left _),
    Summable.tsum_add hX ((L.summable_cross hX hG).mul_left (2 * t)), tsum_mul_left, tsum_mul_left]

/-- The resolvent equation `A(X, G) + c⟪X, G⟫ = ⟪y, G⟫` on admissible vectors. -/
def SolvesResolvent (c : ℝ) (y X : E) : Prop :=
  L.Admissible X ∧ ∀ G : E, L.Admissible G → L.seriesPair X G + c * ⟪X, G⟫ = ⟪y, G⟫

/-- **Uniqueness**: the form `A + c‖·‖²` is coercive. -/
theorem SolvesResolvent.unique {c : ℝ} (hc : 0 < c) {y X X' : E} (hX : L.SolvesResolvent c y X)
    (hX' : L.SolvesResolvent c y X') : X = X' := by
  have hZ := L.admissible_add_smul hX.1 hX'.1 (-1)
  have h := L.seriesPair_add_smul_left hX.1 hX'.1 hZ (-1)
  have h1 := hX.2 _ hZ
  have h2 := hX'.2 _ hZ
  rw [seriesPair_self] at h
  have hn : ⟪X + (-1 : ℝ) • X', X + (-1 : ℝ) • X'⟫ = ⟪X, X + (-1 : ℝ) • X'⟫ - ⟪X', X + (-1 : ℝ) • X'⟫ := by
    rw [inner_add_left, real_inner_smul_left]; ring
  have hs := L.series_nonneg (X + (-1 : ℝ) • X')
  rw [real_inner_self_eq_norm_sq] at hn
  have hsq : c * ‖X + (-1 : ℝ) • X'‖ ^ 2 ≤ 0 := by nlinarith
  have h0 : ‖X + (-1 : ℝ) • X'‖ ^ 2 ≤ 0 := by
    by_contra hpos; push Not at hpos; nlinarith [mul_pos hc hpos]
  have hz : X + (-1 : ℝ) • X' = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm h0 (sq_nonneg _)))
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact hz

/-- **Existence**: the minimizer of `A(X) + c‖X‖² − 2⟪y, X⟫` over admissible vectors. -/
theorem exists_resolvent [CompleteSpace E] [TopologicalSpace.SeparableSpace E] {c : ℝ}
    (hc : 0 < c) (y : E) : ∃ X : E, L.SolvesResolvent c y X := by
  classical
  have hJlow : ∀ X : E, -(‖y‖ ^ 2 / c) ≤ L.series X + c * ‖X‖ ^ 2 - 2 * ⟪y, X⟫ := fun X => by
    have h1 := L.series_nonneg X
    have h2 : ⟪y, X⟫ ≤ ‖y‖ * ‖X‖ := real_inner_le_norm y X
    have h3 : -(‖y‖ ^ 2) ≤ c * (c * ‖X‖ ^ 2 - 2 * (‖y‖ * ‖X‖)) := by
      nlinarith [sq_nonneg (c * ‖X‖ - ‖y‖)]
    have h4 : -(‖y‖ ^ 2 / c) ≤ c * ‖X‖ ^ 2 - 2 * (‖y‖ * ‖X‖) := by
      rw [← neg_div, div_le_iff₀ hc]; linarith
    linarith
  set S : Set ℝ := {r | ∃ X : E, L.Admissible X ∧ L.series X + c * ‖X‖ ^ 2 - 2 * ⟪y, X⟫ = r}
  have hS : S.Nonempty := ⟨_, 0, L.admissible_zero, rfl⟩
  have hSb : BddBelow S := ⟨-(‖y‖ ^ 2 / c), by rintro _ ⟨X, -, rfl⟩; exact hJlow X⟩
  obtain ⟨u, hu_anti, hu_lim, hu_mem⟩ := exists_seq_tendsto_sInf hS hSb
  choose X hXadm hXval using hu_mem
  have hJle : ∀ n, L.series (X n) + c * ‖X n‖ ^ 2 - 2 * ⟪y, X n⟫ ≤ u 0 := fun n => by
    rw [hXval n]; exact hu_anti (Nat.zero_le n)
  -- a minimizing sequence is bounded
  have hXb : ∀ n, ‖X n‖ ≤ 1 + (2 * ‖y‖ + |u 0|) / c := fun n => by
    have h1 := L.series_nonneg (X n)
    have h2 : ⟪y, X n⟫ ≤ ‖y‖ * ‖X n‖ := real_inner_le_norm y (X n)
    have h3 := hJle n
    have h4 := le_abs_self (u 0)
    have hq : 0 ≤ (2 * ‖y‖ + |u 0|) / c := div_nonneg (by positivity) hc.le
    by_contra hcon
    push Not at hcon
    have ht1 : 1 < ‖X n‖ := by linarith
    have hct : 2 * ‖y‖ + |u 0| < c * (‖X n‖ - 1) := by
      have h5 : (2 * ‖y‖ + |u 0|) / c < ‖X n‖ - 1 := by linarith
      rw [div_lt_iff₀ hc] at h5
      linarith
    have h6 : 0 < c * ‖X n‖ - 2 * ‖y‖ := by nlinarith [abs_nonneg (u 0)]
    nlinarith [mul_pos (sub_pos.mpr ht1) h6, abs_nonneg (u 0)]
  -- weak limit, along which the series converges
  obtain ⟨X₀, φ, hφ, -, hweak⟩ := exists_weaklyConvergent_subseq X _ hXb
  have hsb : ∀ n, L.series (X (φ n)) ∈
      Icc (0 : ℝ) (u 0 + 2 * ‖y‖ * (1 + (2 * ‖y‖ + |u 0|) / c)) := fun n => by
    refine ⟨L.series_nonneg _, ?_⟩
    have h3 := hJle (φ n)
    have h2 : ⟪y, X (φ n)⟫ ≤ ‖y‖ * ‖X (φ n)‖ := real_inner_le_norm _ _
    have h7 := mul_le_mul_of_nonneg_left (hXb (φ n)) (norm_nonneg y)
    nlinarith [mul_nonneg hc.le (sq_nonneg ‖X (φ n)‖)]
  obtain ⟨sl, -, ψ, hψ, hs⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc _ _) hsb
  have hw : ∀ z : E, Tendsto (fun n => ⟪X (φ (ψ n)), z⟫) atTop (𝓝 ⟪X₀, z⟫) :=
    fun z => (hweak z).comp hψ.tendsto_atTop
  have hs' : Tendsto (fun n => L.series (X (φ (ψ n)))) atTop (𝓝 sl) := hs
  obtain ⟨hX₀adm, hX₀ser⟩ := L.admissible_and_series_le_of_tendsto hw (fun n => hXadm _) hs'
  -- the functional converges to its infimum along the subsequence
  have hJ : Tendsto (fun n => L.series (X (φ (ψ n))) + c * ‖X (φ (ψ n))‖ ^ 2 -
      2 * ⟪y, X (φ (ψ n))⟫) atTop (𝓝 (sInf S)) :=
    (hu_lim.comp ((hφ.comp hψ).tendsto_atTop)).congr fun n => (hXval _).symm
  have hy : Tendsto (fun n => ⟪y, X (φ (ψ n))⟫) atTop (𝓝 ⟪y, X₀⟫) := by
    have h := hw y
    rw [real_inner_comm] at h
    exact h.congr fun n => real_inner_comm _ _
  have hN : Tendsto (fun n => c * ‖X (φ (ψ n))‖ ^ 2) atTop
      (𝓝 (sInf S - sl + 2 * ⟪y, X₀⟫)) := by
    refine ((hJ.sub hs').add (hy.const_mul 2)).congr fun n => ?_
    ring
  -- lower semicontinuity of the norm
  have hlsc : c * ‖X₀‖ ^ 2 ≤ sInf S - sl + 2 * ⟪y, X₀⟫ := by
    have hin : Tendsto (fun n => c * ⟪X (φ (ψ n)), X₀⟫) atTop (𝓝 (c * ‖X₀‖ ^ 2)) := by
      rw [← real_inner_self_eq_norm_sq]; exact (hw X₀).const_mul c
    have hb : ∀ n, c * ⟪X (φ (ψ n)), X₀⟫ ≤ (c * ‖X (φ (ψ n))‖ ^ 2 + c * ‖X₀‖ ^ 2) / 2 := fun n => by
      have h := norm_sub_sq_real (X (φ (ψ n))) X₀
      nlinarith [mul_nonneg hc.le (sq_nonneg ‖X (φ (ψ n)) - X₀‖)]
    have hlim := le_of_tendsto_of_tendsto' hin ((hN.add_const (c * ‖X₀‖ ^ 2)).div_const 2) hb
    linarith
  have hJ₀ : L.series X₀ + c * ‖X₀‖ ^ 2 - 2 * ⟪y, X₀⟫ ≤ sInf S := by linarith
  have hmin : ∀ Z : E, L.Admissible Z →
      L.series X₀ + c * ‖X₀‖ ^ 2 - 2 * ⟪y, X₀⟫ ≤ L.series Z + c * ‖Z‖ ^ 2 - 2 * ⟪y, Z⟫ :=
    fun Z hZ => hJ₀.trans (csInf_le hSb ⟨Z, hZ, rfl⟩)
  -- the Euler–Lagrange equation of the minimizer
  refine ⟨X₀, hX₀adm, fun G hG => ?_⟩
  have h : ∀ t : ℝ, 0 ≤ (2 * (L.seriesPair X₀ G + c * ⟪X₀, G⟫ - ⟪y, G⟫)) * t +
      (L.series G + c * ‖G‖ ^ 2) * t ^ 2 := by
    intro t
    have h1 := hmin _ (L.admissible_add_smul hX₀adm hG t)
    rw [L.series_add_smul hX₀adm hG t] at h1
    have hn : ‖X₀ + t • G‖ ^ 2 = ‖X₀‖ ^ 2 + 2 * t * ⟪X₀, G⟫ + t ^ 2 * ‖G‖ ^ 2 := by
      rw [@norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have hi : ⟪y, X₀ + t • G⟫ = ⟪y, X₀⟫ + t * ⟪y, G⟫ := by
      rw [inner_add_right, inner_smul_right]
    rw [hn, hi] at h1
    nlinarith
  have := eq_zero_of_forall_linear_add_sq_nonneg h
  linarith

/-- The resolvent `R_c y`. -/
def resolvent [CompleteSpace E] [TopologicalSpace.SeparableSpace E] {c : ℝ} (hc : 0 < c) (y : E) :
    E :=
  (L.exists_resolvent hc y).choose

theorem resolvent_spec [CompleteSpace E] [TopologicalSpace.SeparableSpace E] {c : ℝ} (hc : 0 < c)
    (y : E) : L.SolvesResolvent c y (L.resolvent hc y) :=
  (L.exists_resolvent hc y).choose_spec

theorem eq_resolvent [CompleteSpace E] [TopologicalSpace.SeparableSpace E] {c : ℝ} (hc : 0 < c)
    {y X : E} (hX : L.SolvesResolvent c y X) : X = L.resolvent hc y :=
  SolvesResolvent.unique L hc hX (L.resolvent_spec hc y)

theorem solvesResolvent_add_smul {c : ℝ} {y y' X X' : E} (hX : L.SolvesResolvent c y X)
    (hX' : L.SolvesResolvent c y' X') (t : ℝ) : L.SolvesResolvent c (y + t • y') (X + t • X') := by
  refine ⟨L.admissible_add_smul hX.1 hX'.1 t, fun G hG => ?_⟩
  rw [L.seriesPair_add_smul_left hX.1 hX'.1 hG t, inner_add_left, real_inner_smul_left,
    inner_add_left, real_inner_smul_left, ← hX.2 G hG, ← hX'.2 G hG]
  ring

/-- **The resolvent is linear.** -/
def resolventMap [CompleteSpace E] [TopologicalSpace.SeparableSpace E] {c : ℝ} (hc : 0 < c) :
    E →ₗ[ℝ] E where
  toFun := L.resolvent hc
  map_add' y y' := by
    have h := L.solvesResolvent_add_smul (L.resolvent_spec hc y) (L.resolvent_spec hc y') 1
    simp only [one_smul] at h
    exact (L.eq_resolvent hc h).symm
  map_smul' t y := by
    have h := L.solvesResolvent_add_smul (L.resolvent_spec hc 0) (L.resolvent_spec hc y) t
    have h0 : L.resolvent hc 0 = 0 :=
      (L.eq_resolvent hc ⟨L.admissible_zero, fun G _ => by simp [seriesPair]⟩).symm
    rw [h0, zero_add, zero_add] at h
    exact (L.eq_resolvent hc h).symm

/-- **Birman–Schwinger form of a ground state.** A ground state with ground energy `−a < 0` is the
resolvent of the positive part applied to minus its layer vector. -/
theorem eq_resolvent_layerVec_of_groundState [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] [Fintype κ] {a : ℝ} (ha : 0 < a) {F : E}
    (hF : L.Admissible F) (hE : L.energy F = -a * ‖F‖ ^ 2)
    (hmin : ∀ G, L.Admissible G → -a * ‖G‖ ^ 2 ≤ L.energy G) :
    F = L.resolvent ha (-L.layerVec F) := by
  refine L.eq_resolvent ha ⟨hF, fun G hG => ?_⟩
  have h := L.pair_eq_of_groundState hF hE hmin hG
  rw [pair_eq_seriesPair_add] at h
  rw [inner_neg_left]
  linarith

/-- **A ground state lies in the span of the resolvents of the layer vectors.** -/
theorem mem_span_resolvent_of_groundState [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] [Fintype κ] {a : ℝ} (ha : 0 < a) {F : E}
    (hF : L.Admissible F) (hE : L.energy F = -a * ‖F‖ ^ 2)
    (hmin : ∀ G, L.Admissible G → -a * ‖G‖ ^ 2 ≤ L.energy G) :
    F ∈ Submodule.span ℝ (L.resolvent ha '' (Set.range L.p ∪ Set.range L.q)) := by
  rw [L.eq_resolvent_layerVec_of_groundState ha hF hE hmin]
  have hmem := Submodule.neg_mem _ (L.layerVec_mem_span F)
  have h := Submodule.mem_map_of_mem (f := L.resolventMap ha) hmem
  rw [Submodule.map_span] at h
  exact h

end LayeredEnergy

end GroundState

namespace ModelStates

open GroundState
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

variable {Z : ZeroConfig}

/-- **Birman–Schwinger form of the critical state of a tempered configuration.** With possibly
infinitely many on-line zeros, the critical state `F` is the resolvent of the positive on-line form
applied to `−V F`, a combination of the finitely many off-line exponentials, and lies in the span of the
resolvents of those exponentials. -/
theorem exists_configCriticalState_resolvent (hZ : TemperedConfig Z)
    (hfin : (offLineSet Z).Finite)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ (a : ℝ) (ha : 0 < a) (F : ConfSpace), (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
      (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      (∀ G : ConfSpace, (configEnergy hfin).Admissible G →
        0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
      F = (configEnergy hfin).resolvent ha (-(configEnergy hfin).layerVec F) ∧
      F ∈ Submodule.span ℝ ((configEnergy hfin).resolvent ha ''
        (Set.range (configEnergy hfin).p ∪ Set.range (configEnergy hfin).q)) := by
  obtain ⟨a, F, ha, hFa, hF1, hEq, hmin⟩ := exists_configCriticalState hZ hfin hconj hρ₀ hre
  have hE : (configEnergy hfin).energy F = -a * ‖F‖ ^ 2 := by linarith
  have hmin' : ∀ G, (configEnergy hfin).Admissible G → -a * ‖G‖ ^ 2 ≤ (configEnergy hfin).energy G :=
    fun G hG => by have := hmin G hG; linarith
  exact ⟨a, ha, F, hFa, hF1, hEq, hmin,
    (configEnergy hfin).eq_resolvent_layerVec_of_groundState ha hFa hE hmin',
    (configEnergy hfin).mem_span_resolvent_of_groundState ha hFa hE hmin'⟩

#print axioms exists_configCriticalState_resolvent

end ModelStates

end GaloisForLFunctions.ExclusionOfTheCriticalState
