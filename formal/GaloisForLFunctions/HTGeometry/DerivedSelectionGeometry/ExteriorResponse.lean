import Mathlib

/-!
# Exterior-source and breadth laws

Two constraints on scalarised exterior responses, independent of the Cartier depth direction.

**Finite-port fracture.**  On `E = k u ⊕ W` with `S : W → Z` linear, the alternating exterior
response is `β(au+w, bu+v) = a S(v) - b S(w)`.  Post-composing with `Λ : Z → N` gives
`ω_Λ = Λ β`, whose radical is the kernel of `ω_Λ` viewed as a map `E → (E →ₗ N)`:

* `ker_scalarResponse` — if `Λ S ≠ 0` then `Rad ω_Λ = 0 ⊕ ker(ΛS)`;
* `ker_scalarResponse_of_comp_eq_zero` — if `Λ S = 0` the radical is all of `E`;
* `ker_scalarResponse_ne_bot_of_finrank_lt` — fewer ports than `dim W` forces degeneracy;
* `comp_eq_zero_of_separable` — a nonzero `ω_Λ` is never a sum of a function of the first variable
  and a function of the second.

**Uniform breadth singularity.**  If a linear response `κ` takes the same nonzero value `c` on
every member of an orthonormal family, then

* `sq_apply_le` and `sq_apply_eq_of_ones` — its norm on the first `N` atoms is exactly `|c|√N`;
* `breadthVector_tendsto_zero`, `apply_breadthVector` — the averaged atoms tend to `0` while the
  response stays `c`, so
* `graph_mem_closure` — the pair `(0, c)` lies in the closure of the graph and
* `not_continuous` — `κ` is not continuous; the graph is not the graph of any extension.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

section FinitePort

variable {k W Z N : Type*} [Field k] [AddCommGroup W] [Module k W]
  [AddCommGroup Z] [Module k Z] [AddCommGroup N] [Module k N]

/-- The alternating exterior response `β(au+w, bu+v) = a S(v) - b S(w)` on `E = k ⊕ W`. -/
def extResponse (S : W →ₗ[k] Z) : (k × W) →ₗ[k] (k × W) →ₗ[k] Z :=
  LinearMap.mk₂ k (fun e f => e.1 • S f.2 - f.1 • S e.2)
    (fun e e' f => by simp [add_smul, map_add, smul_add]; abel)
    (fun c e f => by
      simp [Prod.smul_def, smul_eq_mul, mul_smul, map_smul, smul_sub, smul_comm c])
    (fun e f f' => by simp [add_smul, map_add, smul_add]; abel)
    (fun c e f => by
      simp [Prod.smul_def, smul_eq_mul, mul_smul, map_smul, smul_sub, smul_comm c])

@[simp] theorem extResponse_apply (S : W →ₗ[k] Z) (e f : k × W) :
    extResponse S e f = e.1 • S f.2 - f.1 • S e.2 := rfl

/-- The scalarised response `ω_Λ = Λ β`. -/
def scalarResponse (S : W →ₗ[k] Z) (Λ : Z →ₗ[k] N) : (k × W) →ₗ[k] (k × W) →ₗ[k] N :=
  LinearMap.compr₂ (extResponse S) Λ

@[simp] theorem scalarResponse_apply (S : W →ₗ[k] Z) (Λ : Z →ₗ[k] N) (e f : k × W) :
    scalarResponse S Λ e f = e.1 • Λ (S f.2) - f.1 • Λ (S e.2) := by
  simp [scalarResponse, LinearMap.compr₂_apply, map_sub, map_smul]

variable {S : W →ₗ[k] Z} {Λ : Z →ₗ[k] N}

/-- **Theorem 6.1, degenerate case.**  If the scalarised port map vanishes, the whole space is
radical. -/
theorem ker_scalarResponse_of_comp_eq_zero (h : Λ ∘ₗ S = 0) :
    LinearMap.ker (scalarResponse S Λ) = ⊤ := by
  rw [eq_top_iff]
  intro e _
  simp only [LinearMap.mem_ker]
  refine LinearMap.ext fun f => ?_
  have h1 : Λ (S f.2) = 0 := by
    have := LinearMap.congr_fun h f.2; simpa using this
  have h2 : Λ (S e.2) = 0 := by
    have := LinearMap.congr_fun h e.2; simpa using this
  simp only [scalarResponse_apply, LinearMap.zero_apply, h1, h2, smul_zero, sub_zero]

/-- **Theorem 6.1 (6.2).**  If the scalarised port map is nonzero, the radical of the scalarised
exterior response is `0 ⊕ ker(ΛS)`. -/
theorem ker_scalarResponse (h : Λ ∘ₗ S ≠ 0) :
    LinearMap.ker (scalarResponse S Λ) =
      Submodule.prod (⊥ : Submodule k k) (LinearMap.ker (Λ ∘ₗ S)) := by
  obtain ⟨v, hv⟩ : ∃ v, Λ (S v) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (by ext v; simpa using hc v)
  ext e
  simp only [LinearMap.mem_ker, Submodule.mem_prod, Submodule.mem_bot, LinearMap.coe_comp,
    Function.comp_apply]
  constructor
  · intro he
    have hall : ∀ f : k × W, scalarResponse S Λ e f = 0 := fun f => by
      rw [he]; rfl
    have h1 := hall (0, v)
    have h2 := hall (1, 0)
    simp only [scalarResponse_apply] at h1 h2
    rw [zero_smul, sub_zero] at h1
    constructor
    · rcases smul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hv
    · rw [map_zero, map_zero, smul_zero, zero_sub, one_smul, neg_eq_zero] at h2
      exact h2
  · rintro ⟨h1, h2⟩
    refine LinearMap.ext fun f => ?_
    simp only [scalarResponse_apply, LinearMap.zero_apply, h1, h2, zero_smul, smul_zero,
      sub_zero]

/-- **Theorem 6.1, port bound.**  Fewer scalar ports than the dimension of `W` forces a nonzero
radical. -/
theorem ker_scalarResponse_ne_bot_of_finrank_lt [FiniteDimensional k W] [FiniteDimensional k N]
    (hlt : Module.finrank k N < Module.finrank k W) :
    LinearMap.ker (scalarResponse S Λ) ≠ ⊥ := by
  have hker : LinearMap.ker (Λ ∘ₗ S) ≠ ⊥ := by
    intro hc
    have hinj : Function.Injective (Λ ∘ₗ S) := LinearMap.ker_eq_bot.1 hc
    have := (Λ ∘ₗ S).finrank_le_finrank_of_injective hinj
    omega
  by_cases h : Λ ∘ₗ S = 0
  · rw [ker_scalarResponse_of_comp_eq_zero h]
    intro hc
    have : (⊤ : Submodule k (k × W)) = ⊥ := hc
    have h1 : ((1 : k), (0 : W)) ∈ (⊤ : Submodule k (k × W)) := trivial
    rw [this, Submodule.mem_bot] at h1
    exact one_ne_zero (congrArg Prod.fst h1)
  · rw [ker_scalarResponse h]
    intro hc
    apply hker
    rw [eq_bot_iff]
    intro w hw
    have : ((0 : k), w) ∈ Submodule.prod (⊥ : Submodule k k) (LinearMap.ker (Λ ∘ₗ S)) :=
      ⟨rfl, hw⟩
    rw [hc, Submodule.mem_bot] at this
    simpa using congrArg Prod.snd this

/-- **Theorem 6.1, two-leg inseparability.**  If the scalarised response is a sum of a function of
its first argument and a function of its second, then the port map vanishes, hence the response is
identically zero. -/
theorem comp_eq_zero_of_separable
    (F G : (k × W) → N) (hFG : ∀ e f, scalarResponse S Λ e f = F e + G f) :
    Λ ∘ₗ S = 0 := by
  have hax : ∀ (a : k) (v : W), (a : k) • Λ (S v) = 0 := by
    intro a v
    have hkk : ∀ a b : k, F ((a, 0) : k × W) + G ((b, 0) : k × W) = 0 := by
      intro a b
      rw [← hFG]
      simp
    have hww : ∀ w v : W, F ((0, w) : k × W) + G ((0, v) : k × W) = 0 := by
      intro w v
      rw [← hFG]
      simp
    have hF0 : F ((a, 0) : k × W) = F ((0, 0) : k × W) := by
      have h1 := hkk a 0
      have h2 := hkk 0 0
      have := h1.trans h2.symm
      exact add_right_cancel this
    have hG0 : G ((0, v) : k × W) = G ((0, 0) : k × W) := by
      have h1 := hww 0 v
      have h2 := hww 0 0
      have := h1.trans h2.symm
      exact add_left_cancel this
    have hsum : F ((0, 0) : k × W) + G ((0, 0) : k × W) = 0 := hkk 0 0
    have hmain := hFG ((a, 0) : k × W) ((0, v) : k × W)
    simp only [scalarResponse_apply, map_zero, smul_zero, sub_zero] at hmain
    rw [hF0, hG0] at hmain
    rw [hmain, hsum]
  ext v
  have := hax 1 v
  simpa using this

end FinitePort

section Breadth

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The normalised breadth vector `v_N = N⁻¹ ∑_{n<N} e_n`. -/
noncomputable def breadthVector (e : ℕ → H) (N : ℕ) : H :=
  (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, e i

variable {e : ℕ → H} {κ : H →ₗ[ℝ] ℝ} {c : ℝ}

theorem norm_sum_range_orthonormal (he : Orthonormal ℝ e) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, e i‖ = Real.sqrt N := by
  have hsq : ‖∑ i ∈ Finset.range N, e i‖ ^ 2 = (N : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    have := he.inner_sum (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (Finset.range N)
    simpa using this
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem norm_sum_range_smul_orthonormal (he : Orthonormal ℝ e) (a : ℕ → ℝ) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, a i • e i‖ ^ 2 = ∑ i ∈ Finset.range N, a i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have := he.inner_sum a a (Finset.range N)
  simpa [sq] using this

theorem apply_sum_range (hκ : ∀ n, κ (e n) = c) (a : ℕ → ℝ) (N : ℕ) :
    κ (∑ i ∈ Finset.range N, a i • e i) = c * ∑ i ∈ Finset.range N, a i := by
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hκ i, smul_eq_mul, mul_comm]

/-- **Theorem 6.2, upper bound.**  On the span of the first `N` atoms the response is bounded by
`|c|√N` times the norm. -/
theorem abs_apply_le (he : Orthonormal ℝ e) (hκ : ∀ n, κ (e n) = c) (a : ℕ → ℝ) (N : ℕ) :
    |κ (∑ i ∈ Finset.range N, a i • e i)| ≤
      |c| * Real.sqrt N * ‖∑ i ∈ Finset.range N, a i • e i‖ := by
  set x := ∑ i ∈ Finset.range N, a i • e i with hx
  have hcs : (∑ i ∈ Finset.range N, a i) ^ 2 ≤ (N : ℝ) * ∑ i ∈ Finset.range N, a i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := a)
    simpa using this
  have hnorm : ‖x‖ ^ 2 = ∑ i ∈ Finset.range N, a i ^ 2 := norm_sum_range_smul_orthonormal he a N
  have hsq : (κ x) ^ 2 ≤ (|c| * Real.sqrt N * ‖x‖) ^ 2 := by
    rw [apply_sum_range hκ a N, mul_pow, mul_pow, mul_pow, sq_abs,
      Real.sq_sqrt (by positivity), hnorm]
    nlinarith [sq_nonneg c, hcs]
  have hnn : 0 ≤ |c| * Real.sqrt N * ‖x‖ := by positivity
  calc |κ x| = Real.sqrt ((κ x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((|c| * Real.sqrt N * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |c| * Real.sqrt N * ‖x‖ := Real.sqrt_sq hnn

/-- **Theorem 6.2, attainment.**  The bound `|c|√N` is achieved on the all-ones atom sum, so the
restricted norm is exactly `|c|√N`. -/
theorem abs_apply_sum_range (he : Orthonormal ℝ e) (hκ : ∀ n, κ (e n) = c) (N : ℕ) :
    |κ (∑ i ∈ Finset.range N, e i)| =
      |c| * Real.sqrt N * ‖∑ i ∈ Finset.range N, e i‖ := by
  have h1 : κ (∑ i ∈ Finset.range N, e i) = c * N := by
    have := apply_sum_range hκ (fun _ => (1 : ℝ)) N
    simpa using this
  rw [h1, norm_sum_range_orthonormal he N, abs_mul, mul_assoc,
    Real.mul_self_sqrt (Nat.cast_nonneg N), Nat.abs_cast]

@[simp] theorem apply_breadthVector (hκ : ∀ n, κ (e n) = c) {N : ℕ} (hN : N ≠ 0) :
    κ (breadthVector e N) = c := by
  rw [breadthVector, map_smul, smul_eq_mul]
  have h := apply_sum_range hκ (fun _ => (1 : ℝ)) N
  simp only [one_smul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [h]
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  field_simp

theorem norm_breadthVector (he : Orthonormal ℝ e) {N : ℕ} (hN : N ≠ 0) :
    ‖breadthVector e N‖ = (Real.sqrt N)⁻¹ := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hs : Real.sqrt N ≠ 0 := Real.sqrt_ne_zero'.2 hNpos
  have hss : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
  rw [breadthVector, norm_smul, norm_sum_range_orthonormal he N, norm_inv, Real.norm_natCast]
  field_simp
  linarith [hss]

theorem breadthVector_tendsto_zero (he : Orthonormal ℝ e) :
    Tendsto (breadthVector e) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun N : ℕ => ‖breadthVector e N‖) =ᶠ[atTop] fun N : ℕ => (Real.sqrt N)⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact norm_breadthVector he hN.ne'
  have h0 : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp h0
    simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_inv] at h
    exact h
  exact Tendsto.congr' heq.symm h1

theorem apply_breadthVector_succ_tendsto (hκ : ∀ n, κ (e n) = c) :
    Tendsto (fun N : ℕ => κ (breadthVector e (N + 1))) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr fun N => ?_
  exact (apply_breadthVector hκ (Nat.succ_ne_zero N)).symm

/-- **Theorem 6.2, nonclosability.**  The pair `(0, c)` lies in the closure of the graph of `κ`.
For `c ≠ 0` this exhibits the graph as non-closable. -/
theorem graph_mem_closure (he : Orthonormal ℝ e) (hκ : ∀ n, κ (e n) = c) :
    ((0 : H), c) ∈ closure (Set.range fun x : H => (x, κ x)) := by
  have h1 : Tendsto (fun N : ℕ => breadthVector e (N + 1)) atTop (𝓝 0) :=
    (breadthVector_tendsto_zero he).comp (tendsto_add_atTop_nat 1)
  have h2 := apply_breadthVector_succ_tendsto hκ
  have h3 : Tendsto (fun N : ℕ => (breadthVector e (N + 1), κ (breadthVector e (N + 1))))
      atTop (𝓝 ((0 : H), c)) := h1.prodMk_nhds h2
  refine mem_closure_of_tendsto h3 ?_
  filter_upwards with N
  exact Set.mem_range_self _

/-- **Theorem 6.2, unboundedness.**  A uniform nonzero response on an orthonormal family is not
continuous. -/
theorem not_continuous (he : Orthonormal ℝ e) (hκ : ∀ n, κ (e n) = c) (hc : c ≠ 0) :
    ¬ Continuous κ := by
  intro hcont
  have h1 : Tendsto (fun N : ℕ => κ (breadthVector e (N + 1))) atTop (𝓝 (κ 0)) :=
    (hcont.tendsto 0).comp ((breadthVector_tendsto_zero he).comp (tendsto_add_atTop_nat 1))
  have h2 := apply_breadthVector_succ_tendsto hκ
  have h3 := tendsto_nhds_unique h1 h2
  rw [map_zero] at h3
  exact hc h3.symm

end Breadth

end GaloisForLFunctions.HTGeometry.DerivedSelection
