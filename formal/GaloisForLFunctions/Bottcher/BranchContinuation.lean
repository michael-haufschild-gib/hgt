/-
# Path-continuation machinery for the algebraic branch (natural-boundary route)

Under the contradiction hypothesis (`φ_c` algebraic, relation `P`), `φ_c` is an algebraic function and
continues along any path off `P`'s finite branch locus — single-valued, because path-lifts carry no
monodromy. This file builds the gluing machinery for that continuation: consecutive local simple-root
branches (`AlgebraicBranch.exists_analyticAt_branch_poly`) that agree on an overlap glue into one analytic
branch (`AlgebraicBranch.branch_eqOn_of_eq_at` for agreement, here packaged into the union).

`branch_glue_union` is the chain-extension step: glue two agreeing branches into one on the union of their
domains. Iterated along a finite cover of a path (compactness / Lebesgue number), it produces the
single-valued continuation reaching a non-resonant repelling periodic point — feeding
`NaturalBoundaryContradiction.false_of_funEq_at_nonresonant` (with the functional equation propagated by
`TranscendenceReduction.eqOn_funEq_of_eventuallyEq`). This route uses only `P` and the algebraic-branch
lemmas (not the dynamical `f_c`-cover), so it is independent of the basin-construction lane.
-/
import GaloisForLFunctions.Bottcher.AlgebraicBranch
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integral

open Filter Topology Set Classical

namespace Bottcher

/-- The quadratic `z ↦ z²+c` as a polynomial, `p`-fold composed; evaluates to the function iterate
`(quadratic c)^[p]`. The polynomial form of `f^[p]`, needed to build `Q(z,w) := P(f^[p]z, w^{2^p})` as a
`Polynomial (Polynomial ℂ)` (its outer coefficients are `P.coeff i` composed with this). -/
noncomputable def quadIteratePoly (c : ℂ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.X
  | (p + 1) => (Polynomial.X ^ 2 + Polynomial.C c).comp (quadIteratePoly c p)

@[simp] theorem quadIteratePoly_zero (c : ℂ) : quadIteratePoly c 0 = Polynomial.X := rfl

theorem quadIteratePoly_eval (c : ℂ) (p : ℕ) (z : ℂ) :
    (quadIteratePoly c p).eval z = (quadratic c)^[p] z := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [quadIteratePoly, Polynomial.eval_comp, ih, Function.iterate_succ_apply']
    simp [quadratic]

/-- **A finite set closed under a map contains a periodic point.** If `f` maps the finite set `S` into
itself and `s₀ ∈ S`, some `s ∈ S` is periodic: `f^[m] s = s` for `m ≥ 1` (pigeonhole on the orbit). For
`f = (·^d)` on the roots of `P(z₀,·)` (closed under `w↦w^d` by the divisibility) this yields the periodic
root `w₀^{d^m} = w₀` the divisibility route needs at the periodic point `z₀`. -/
theorem exists_periodic_of_finite_mapsTo {α : Type*} {S : Set α} (hS : S.Finite) {f : α → α}
    (hmaps : Set.MapsTo f S S) {s₀ : α} (hs₀ : s₀ ∈ S) :
    ∃ s ∈ S, ∃ m : ℕ, 1 ≤ m ∧ f^[m] s = s := by
  have horb : ∀ n : ℕ, f^[n] s₀ ∈ S := fun n => (hmaps.iterate n) hs₀
  haveI : Finite S := hS
  have hni : ¬ Function.Injective (fun n : ℕ => (⟨f^[n] s₀, horb n⟩ : S)) :=
    fun hinj => not_injective_infinite_finite _ hinj
  rw [Function.not_injective_iff] at hni
  obtain ⟨i, j, hij, hne⟩ := hni
  have hval : f^[i] s₀ = f^[j] s₀ := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨f^[i] s₀, horb i, j - i, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h), ← hval]
  · refine ⟨f^[j] s₀, horb j, i - j, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h), hval]

/-- **The relation as a genuine `ℂ`-polynomial evaluation.** `Σᵢ (P.coeff i)(z)·wⁱ = (P.map(eval z)).eval w`,
bridging the `eval₂`-sum relation to mathlib's `Polynomial.eval`/`roots` machinery for the fibre polynomial
`P.map (evalRingHom z) ∈ ℂ[w]` (root bounds via `norm_root_le_of_monic`, finiteness of the fibre, etc.). -/
theorem relation_eq_eval_map (P : Polynomial (Polynomial ℂ)) (z w : ℂ) :
    (∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i)
      = (P.map (Polynomial.evalRingHom z)).eval w := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.coe_evalRingHom, Polynomial.coe_aeval_eq_eval]

/-- **The relation is multiplicative.** `relation(P·S) = relation(P)·relation(S)` at any `(z,w)` (the
relation-evaluation `P ↦ Σᵢ (P.coeff i)(z)·wⁱ` is the ring hom `P ↦ (P.map(eval z)).eval w`). With `Q = P·S`
this gives `relation(Q)(z,w) = relation(P)(z,w)·relation(S)(z,w)`; at `(z, g z)` with `relation(P)(z,gz)=0`
it yields `relation(Q)(z,gz)=0` — the `hdiv` input of `funEq_of_branch` once `P ∣ Q`. -/
theorem relation_mul (P S : Polynomial (Polynomial ℂ)) (z w : ℂ) :
    (∑ i ∈ (P * S).support, ((P * S).coeff i).aeval z * w ^ i)
      = (∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i)
        * (∑ i ∈ S.support, (S.coeff i).aeval z * w ^ i) := by
  rw [relation_eq_eval_map, relation_eq_eval_map, relation_eq_eval_map, Polynomial.map_mul,
    Polynomial.eval_mul]

/-- **The relation of a constant-in-`w` polynomial** `C e` is `e.eval z` (the relation-evaluation is the
ring hom `P ↦ (P.map(eval z)).eval w`, and a `w`-constant has only the degree-0 term). Used in the
divisibility gateway to peel the cleared denominator `e ∈ ℂ[z]` off `(C e)·Q`. -/
theorem relation_C (e : Polynomial ℂ) (z w : ℂ) :
    (∑ i ∈ (Polynomial.C e).support, ((Polynomial.C e).coeff i).aeval z * w ^ i) = e.eval z := by
  rw [relation_eq_eval_map, Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom]

/-- **The relation is additive**, `relation(A+B) = relation(A)+relation(B)` (the relation-evaluation is a
ring hom in the polynomial). Splits the cleared-denominator identity `(C e)·Q = P·S + R` into its `P·S`
and remainder parts when evaluating on the vanishing set. -/
theorem relation_add (A B : Polynomial (Polynomial ℂ)) (z w : ℂ) :
    (∑ i ∈ (A + B).support, ((A + B).coeff i).aeval z * w ^ i)
      = (∑ i ∈ A.support, (A.coeff i).aeval z * w ^ i)
        + (∑ i ∈ B.support, (B.coeff i).aeval z * w ^ i) := by
  rw [relation_eq_eval_map, relation_eq_eval_map, relation_eq_eval_map, Polynomial.map_add,
    Polynomial.eval_add]

/-- **The relation at a constant `w₀`** equals `(P.eval (C w₀)).eval z` — the `z`-polynomial obtained by
substituting the constant `w₀` for `w`. So `relation(P)(·, w₀) ≡ 0` near a point forces `P.eval (C w₀) = 0`
in `ℂ[z]`, i.e. `(X - C(C w₀)) ∣ P` (factor theorem) — the algebraic criterion for the local branch through
`(z₀, w₀)` to be the constant `w₀`. Used to derive branch non-constancy from non-divisibility. -/
theorem relation_at_const (P : Polynomial (Polynomial ℂ)) (z w₀ : ℂ) :
    (∑ i ∈ P.support, (P.coeff i).aeval z * w₀ ^ i) = (P.eval (Polynomial.C w₀)).eval z := by
  rw [relation_eq_eval_map]
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp [Polynomial.eval_C, Polynomial.coe_evalRingHom]

/-- **Derivative of the relation polynomial in `w`.** The `w`-derivative of `w ↦ Σᵢ (P.coeff i)(z)·wⁱ` at
`w₀` is `Σᵢ (P.coeff i)(z)·(i·w₀^{i-1})`. Supplies the `hpartial` of `exists_analyticAt_branch_poly` /
`branch_unique_poly` from a "simple root" hypothesis (that derivative sum `≠ 0`). -/
theorem hasDerivAt_relationPoly (P : Polynomial (Polynomial ℂ)) (z w₀ : ℂ) :
    HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i)
      (∑ i ∈ P.support, (P.coeff i).aeval z * ((i : ℂ) * w₀ ^ (i - 1))) w₀ := by
  have key : (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i)
      = ∑ i ∈ P.support, (fun w => (P.coeff i).aeval z * w ^ i) := by
    funext w; simp only [Finset.sum_apply]
  rw [key]
  exact HasDerivAt.sum (fun i _ => (hasDerivAt_pow i w₀).const_mul ((P.coeff i).aeval z))

/-- **Cauchy bound for roots of a monic polynomial.** Any root `z` of a monic `p` (degree ≥ 1) satisfies
`‖z‖ ≤ max 1 (Σ_{i<deg} ‖coeff i‖)`. (Not in mathlib.) Used to bound the value-lift `v(t)` uniformly on a
compact parameter interval, supplying the closed-direction convergence of the algebraic path-continuation. -/
theorem norm_root_le_of_monic {p : Polynomial ℂ} (hp : p.Monic) {z : ℂ} (hz : p.eval z = 0)
    (hdeg : 0 < p.natDegree) :
    ‖z‖ ≤ max 1 (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) := by
  by_contra hcon
  push_neg at hcon
  set n := p.natDegree with hn
  have h1 : (1 : ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have hS : (∑ i ∈ Finset.range n, ‖p.coeff i‖) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hcon
  have hexp : z ^ n + ∑ i ∈ Finset.range n, p.coeff i * z ^ i = 0 := by
    have h := Polynomial.eval_eq_sum_range z (p := p)
    rw [hz, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
    linear_combination -h
  have hzn : ‖z‖ ^ n = ‖∑ i ∈ Finset.range n, p.coeff i * z ^ i‖ := by
    rw [← norm_pow, show z ^ n = -(∑ i ∈ Finset.range n, p.coeff i * z ^ i) by linear_combination hexp,
      norm_neg]
  have hbound : ‖∑ i ∈ Finset.range n, p.coeff i * z ^ i‖
      ≤ (∑ i ∈ Finset.range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1) := by
    calc ‖∑ i ∈ Finset.range n, p.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range n, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range n, ‖p.coeff i‖ * ‖z‖ ^ i := by simp [norm_pow]
      _ ≤ ∑ i ∈ Finset.range n, ‖p.coeff i‖ * ‖z‖ ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply pow_le_pow_right₀ (le_of_lt h1)
          rw [Finset.mem_range] at hi; omega
      _ = (∑ i ∈ Finset.range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1) := by rw [Finset.sum_mul]
  have hzpos : (0 : ℝ) < ‖z‖ ^ (n - 1) := by positivity
  have hpow : ‖z‖ * ‖z‖ ^ (n - 1) = ‖z‖ ^ n := by rw [← pow_succ']; congr 1; omega
  have hlt : ‖z‖ ^ n < ‖z‖ ^ n := by
    calc ‖z‖ ^ n = ‖∑ i ∈ Finset.range n, p.coeff i * z ^ i‖ := hzn
      _ ≤ (∑ i ∈ Finset.range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1) := hbound
      _ < ‖z‖ * ‖z‖ ^ (n - 1) := mul_lt_mul_of_pos_right hS hzpos
      _ = ‖z‖ ^ n := hpow
  exact lt_irrefl _ hlt

/-- **Continuous functions agreeing locally on a preconnected set agree on it** (the continuous analogue
of the identity theorem; not in mathlib). The clopen-equalizer pillar for path-lift uniqueness: the
agreement set is closed (continuity) and open (local agreement), hence all of the preconnected `s`. -/
theorem eqOn_of_locally_eq {f g : ℝ → ℂ} {s : Set ℝ} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    {a : ℝ} (ha : a ∈ s) (hfa : f a = g a)
    (hloc : ∀ t ∈ s, f t = g t → ∃ u ∈ 𝓝 t, ∀ y ∈ u ∩ s, f y = g y) :
    Set.EqOn f g s := by
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hEclosed : IsClosed {x : s | f x.1 = g x.1} :=
    isClosed_eq (continuousOn_iff_continuous_restrict.mp hf)
      (continuousOn_iff_continuous_restrict.mp hg)
  have hEopen : IsOpen {x : s | f x.1 = g x.1} := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨t, ht⟩ hmem
    obtain ⟨u, hu, hsub⟩ := hloc t ht hmem
    obtain ⟨v, hvu, hvopen, htv⟩ := mem_nhds_iff.mp hu
    refine mem_nhds_iff.mpr ⟨Subtype.val ⁻¹' v, ?_, hvopen.preimage continuous_subtype_val, htv⟩
    rintro ⟨y, hy⟩ hyv
    exact hsub y ⟨hvu hyv, hy⟩
  have huniv : {x : s | f x.1 = g x.1} = univ :=
    IsClopen.eq_univ ⟨hEclosed, hEopen⟩ ⟨⟨a, ha⟩, hfa⟩
  intro t ht
  have : (⟨t, ht⟩ : s) ∈ {x : s | f x.1 = g x.1} := by rw [huniv]; trivial
  exact this

/-- **Local lift along the path.** At a simple root `w₀` of the relation at `γ t₀`, the algebraic branch
composed with the path gives a continuous local lift `u = g ∘ γ` on a parameter ball `ball t₀ δ`, with
`u t₀ = w₀` and `relation(γ s, u s) = 0` there. The open-extension atom of the value-lift along `γ`. -/
theorem exists_local_lift (P : Polynomial (Polynomial ℂ)) {γ : ℝ → ℂ} (hγ : Continuous γ)
    {t₀ : ℝ} {w₀ d : ℂ}
    (hroot : ∑ i ∈ P.support, (P.coeff i).aeval (γ t₀) * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval (γ t₀) * w ^ i) d w₀)
    (hd : d ≠ 0) :
    ∃ (u : ℝ → ℂ) (δ : ℝ), 0 < δ ∧ u t₀ = w₀ ∧
      ContinuousOn u (Metric.ball t₀ δ) ∧
      ∀ s ∈ Metric.ball t₀ δ, ∑ i ∈ P.support, (P.coeff i).aeval (γ s) * (u s) ^ i = 0 := by
  obtain ⟨g, hgan, hgz, hgrel⟩ := exists_analyticAt_branch_poly P hroot hpartial hd
  have hrel_t : ∀ᶠ s in 𝓝 t₀, ∑ i ∈ P.support, (P.coeff i).aeval (γ s) * (g (γ s)) ^ i = 0 :=
    (hγ.tendsto t₀).eventually hgrel
  have hcont_t : ∀ᶠ s in 𝓝 t₀, AnalyticAt ℂ g (γ s) :=
    (hγ.tendsto t₀).eventually hgan.eventually_analyticAt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hrel_t.and hcont_t)
  refine ⟨g ∘ γ, δ, hδ, hgz, ?_, ?_⟩
  · intro s hs
    exact (((hball (Metric.mem_ball.mp hs)).2.continuousAt).comp hγ.continuousAt).continuousWithinAt
  · intro s hs
    exact (hball (Metric.mem_ball.mp hs)).1

/-- **Pointwise local uniqueness of a simple root.** Near a simple root `(z₀,w₀)` of the relation
(`∂_Y = d ≠ 0`), with `g` the branch through it (continuous, `g z₀ = w₀`, satisfying the relation near
`z₀`), every root `(z,w)` near `(z₀,w₀)` equals the branch: `w = g z`. (Factoring `F(z,w)−F(z,g z) =
(w − g z)·Q` with `Q(z₀,w₀) = d ≠ 0`.) The pointwise companion of `branch_unique_poly` — the closed
direction / lift uniqueness of the algebraic path-continuation needs that a root near a simple root is the
branch value. -/
theorem eventually_unique_root (P : Polynomial (Polynomial ℂ)) {z₀ w₀ d : ℂ}
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {g : ℂ → ℂ} (hg : ContinuousAt g z₀) (hgz : g z₀ = w₀)
    (hgrel : ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (z₀, w₀),
      (∑ i ∈ P.support, (P.coeff i).aeval p.1 * p.2 ^ i = 0) → p.2 = g p.1 := by
  have hfactor : ∀ z a b : ℂ,
      (∑ i ∈ P.support, (P.coeff i).aeval z * a ^ i) - (∑ i ∈ P.support, (P.coeff i).aeval z * b ^ i)
        = (a - b) * ∑ i ∈ P.support, (P.coeff i).aeval z *
            (∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)) := by
    intro z a b
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hg2 : a ^ i - b ^ i = (∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)) * (a - b) :=
      (geom_sum₂_mul a b i).symm
    rw [← mul_sub, hg2]; ring
  set Q : ℂ × ℂ → ℂ := fun p => ∑ i ∈ P.support, (P.coeff i).aeval p.1 *
    (∑ j ∈ Finset.range i, p.2 ^ j * (g p.1) ^ (i - 1 - j)) with hQdef
  have hQ0 : Q (z₀, w₀) = d := by
    have hd' : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i)
        (∑ i ∈ P.support, (P.coeff i).aeval z₀ * ((i : ℂ) * w₀ ^ (i - 1))) w₀ := by
      have key : (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i)
          = ∑ i ∈ P.support, (fun w => (P.coeff i).aeval z₀ * w ^ i) := by
        funext w; simp only [Finset.sum_apply]
      rw [key]
      exact HasDerivAt.sum (fun i _ => (hasDerivAt_pow i w₀).const_mul ((P.coeff i).aeval z₀))
    show (∑ i ∈ P.support, (P.coeff i).aeval z₀ *
      (∑ j ∈ Finset.range i, w₀ ^ j * (g z₀) ^ (i - 1 - j))) = d
    rw [hgz, ← hd'.unique hpartial]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hinner : ∀ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j) = w₀ ^ (i - 1) := by
      intro j hj; rw [Finset.mem_range] at hj; rw [← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hQcont : ContinuousAt Q (z₀, w₀) := by
    apply tendsto_finsetSum
    intro i _
    apply ContinuousAt.mul
    · exact ((Polynomial.contDiff_aeval (𝕜 := ℂ) (P.coeff i) ⊤).continuous.continuousAt).comp
        continuousAt_fst
    · apply tendsto_finsetSum
      intro j _
      exact (continuousAt_snd.pow j).mul ((hg.comp continuousAt_fst).pow _)
  have hQne : ∀ᶠ p in 𝓝 (z₀, w₀), Q p ≠ 0 := hQcont.eventually_ne (by rw [hQ0]; exact hd)
  have hgrel2 : ∀ᶠ p : ℂ × ℂ in 𝓝 (z₀, w₀),
      ∑ i ∈ P.support, (P.coeff i).aeval p.1 * (g p.1) ^ i = 0 :=
    (continuous_fst.tendsto (z₀, w₀)).eventually hgrel
  filter_upwards [hQne, hgrel2] with p hQp hgp hrelp
  have hz : (p.2 - g p.1) * Q p = 0 := by
    have h := hfactor p.1 p.2 (g p.1)
    rw [hrelp, hgp] at h
    simpa [hQdef] using h.symm
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hQp

/-- **Gluing two agreeing branches into one on the union.** If `g₁, g₂` are analytic branches of the
relation `Σᵢ (P.coeff i)(z)·wⁱ = 0` on opens `W₁, W₂`, agreeing on the (preconnected) overlap at a
simple-root point `w₁` (`∂_Y P` at `(w₁, g₁ w₁)` is `d ≠ 0`, `g₂ w₁ = g₁ w₁`), then the piecewise function
`W₁.piecewise g₁ g₂` is analytic on `W₁ ∪ W₂`. The chain-extension step of path-continuation: on `W₁` it is
`g₁`, on `W₂` it is `g₂` (they coincide on the overlap by `branch_eqOn_of_eq_at`). -/
theorem branch_glue_union {P : Polynomial (Polynomial ℂ)} {W₁ W₂ : Set ℂ}
    (hW₁o : IsOpen W₁) (hW₂o : IsOpen W₂) (hovc : IsPreconnected (W₁ ∩ W₂))
    {g₁ g₂ : ℂ → ℂ}
    (hg₁ : AnalyticOnNhd ℂ g₁ W₁) (hg₂ : AnalyticOnNhd ℂ g₂ W₂)
    {w₁ d : ℂ} (hw₁ : w₁ ∈ W₁ ∩ W₂)
    (hrel₁ : ∀ᶠ z in 𝓝 w₁, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₁ z) ^ i = 0)
    (hrel₂ : ∀ᶠ z in 𝓝 w₁, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₂ z) ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval w₁ * w ^ i) d (g₁ w₁))
    (hd : d ≠ 0) (heq : g₂ w₁ = g₁ w₁) :
    AnalyticOnNhd ℂ (W₁.piecewise g₁ g₂) (W₁ ∪ W₂) := by
  have hEq : Set.EqOn g₁ g₂ (W₁ ∩ W₂) :=
    branch_eqOn_of_eq_at hovc (hg₁.mono inter_subset_left) (hg₂.mono inter_subset_right)
      hw₁ hrel₁ hrel₂ hpartial hd heq
  intro z hz
  rcases hz with hz1 | hz2
  · have hev : W₁.piecewise g₁ g₂ =ᶠ[𝓝 z] g₁ := by
      filter_upwards [hW₁o.mem_nhds hz1] with y hy using Set.piecewise_eq_of_mem _ _ _ hy
    exact (hg₁ z hz1).congr hev.symm
  · have hev : W₁.piecewise g₁ g₂ =ᶠ[𝓝 z] g₂ := by
      filter_upwards [hW₂o.mem_nhds hz2] with y hy
      by_cases hy1 : y ∈ W₁
      · rw [Set.piecewise_eq_of_mem _ _ _ hy1]; exact hEq ⟨hy1, hy⟩
      · simp only [Set.piecewise, if_neg hy1]
    exact (hg₂ z hz2).congr hev.symm

/-- **Functional equation for a local branch, via divisibility + pointwise uniqueness.** If `g` is the
local simple-root branch at `(z₀, w₀)`, `F` fixes `z₀` (continuous), `w₀^dd = w₀`, and the divisibility
consequence `P(F z, g(z)^dd) = 0` holds near `z₀` (from `P ∣ P(F·, ·^dd)`), then `g(F z) = g(z)^dd` near
`z₀`. The functional-equation step of the **divisibility route** to the connected/disconnected cases — NO
path-continuation/tube: both `g(Fz)` and `g(z)^dd` are roots of `P(Fz,·)` tending to the simple root `w₀`,
so they coincide by `eventually_unique_root`. Feeds `NaturalBoundaryContradiction.false_of_funEq_at_nonresonant`
(after propagating the local functional equation to a connected neighbourhood). -/
theorem funEq_of_branch (P : Polynomial (Polynomial ℂ)) {F g : ℂ → ℂ} {z₀ w₀ d : ℂ} {dd : ℕ}
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hgan : AnalyticAt ℂ g z₀) (hgz : g z₀ = w₀)
    (hgrel : ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0)
    (hF : ContinuousAt F z₀) (hFz : F z₀ = z₀) (hw₀ : w₀ ^ dd = w₀)
    (hdiv : ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval (F z) * ((g z) ^ dd) ^ i = 0) :
    ∀ᶠ z in 𝓝 z₀, g (F z) = (g z) ^ dd := by
  have huniq := eventually_unique_root P hpartial hd hgan.continuousAt hgz hgrel
  have htends : Tendsto (fun z => (F z, (g z) ^ dd)) (𝓝 z₀) (𝓝 (z₀, w₀)) := by
    refine Tendsto.prodMk_nhds ?_ ?_
    · have := hF.tendsto; rw [hFz] at this; exact this
    · have := (hgan.continuousAt.tendsto).pow dd; rw [hgz, hw₀] at this; exact this
  filter_upwards [htends.eventually huniq, hdiv] with z h hdz
  exact (h hdz).symm

/-- **φ_c is a root of `Q(z,w) := P(f^[p]z, w^{2^p})`** (function-level on `escapeOpen`). From the relation
on `escapeOpen` + the iterated functional equation `φ_c(f^[p]z) = φ_c(z)^{2^p}` (`bottcherCoord_iterate`):
`P(f^[p]z, φ_c(z)^{2^p}) = P(f^[p]z, φ_c(f^[p]z)) = 0`. The input to the divisibility `P ∣ Q` (whence, by
minimality of `P`, the divisibility consequence `hdiv` of `funEq_of_branch`). `escapeOpen` is
forward-invariant (`norm_iterate_ge`). -/
theorem relation_iterate_eq_zero (P : Polynomial (Polynomial ℂ)) {c : ℂ} (p : ℕ)
    (hrel : ∀ z ∈ escapeOpen c,
      ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∀ z ∈ escapeOpen c, ∑ i ∈ P.support, (P.coeff i).aeval ((quadratic c)^[p] z) *
        ((bottcherCoord c z) ^ (2 ^ p)) ^ i = 0 := by
  intro z hz
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  have hfz : (quadratic c)^[p] z ∈ escapeOpen c := by
    have hge := norm_iterate_ge hc hz2 p
    simp only [escapeOpen, Set.mem_setOf_eq] at hz ⊢
    linarith
  rw [← bottcherCoord_iterate hc hz2 p]
  exact hrel _ hfz

/-- **Minimal-degree vanishing relation, with minimality exposed.** From any nonzero `q` whose relation
vanishes on the infinite `U`, extract a nonzero `P` of minimal `w`-degree (`≥ 1`) whose relation vanishes
on `U`, AND expose the minimality `∀ R ≠ 0 vanishing, P.natDegree ≤ R.natDegree`. The minimality makes `P`
generate the relation ideal: Euclidean division gives `P ∣ Q` for every vanishing `Q` (e.g.
`Q(z,w) = P(f^[p]z, w^{2^p})` from `relation_iterate_eq_zero`), the divisibility behind `funEq_of_branch`'s
`hdiv`. -/
theorem exists_minimal_relation {U : Set ℂ} (hUinf : U.Infinite)
    (c : ℂ)
    (q : Polynomial (Polynomial ℂ)) (hq0 : q ≠ 0)
    (hqrel : ∀ z ∈ U, ∑ i ∈ q.support, (q.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧ 1 ≤ P.natDegree ∧
      (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) ∧
      (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree) := by
  classical
  set Pr : ℕ → Prop := fun n => ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧ Q.natDegree = n ∧
    (∀ z ∈ U, ∑ i ∈ Q.support, (Q.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) with hPr
  have hex : ∃ n, Pr n := ⟨q.natDegree, q, hq0, rfl, hqrel⟩
  obtain ⟨P, hP0, hPnd, hPrel⟩ := Nat.find_spec hex
  have hmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
      Nat.find hex ≤ R.natDegree :=
    fun R hR0 hRrel => Nat.find_min' hex ⟨R, hR0, rfl, hRrel⟩
  have hdeg1 : 1 ≤ P.natDegree := by
    by_contra h
    push_neg at h
    have hnd0 : P.natDegree = 0 := by omega
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hnd0
    have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hP0 ha.symm
    have hazero : ∀ z ∈ U, a.eval z = 0 := by
      intro z hz
      have hthis := hPrel z hz
      rw [relation_eq_eval_map, ← ha] at hthis
      simpa [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom] using hthis
    have hsub : U ⊆ {x | Polynomial.IsRoot a x} := fun z hz => hazero z hz
    exact ha0 (Polynomial.eq_zero_of_infinite_isRoot a (hUinf.mono hsub))
  exact ⟨P, hP0, hdeg1, hPrel, fun R hR0 hRrel => hPnd ▸ hmin R hR0 hRrel⟩

/-- `Q(z,w) := P(f^[p]z, w^{2^p})` as a polynomial: compose `P`'s outer coeffs with `quadIteratePoly c p`
(`coeff ↦ coeff∘f^[p]`), then substitute `w ↦ w^{2^p}`. Its relation is the composed relation
(`compRelPoly_relation`); `relation_iterate_eq_zero` says `φ_c` is its root; minimality of `P` gives `P ∣ Q`. -/
noncomputable def compRelPoly (c : ℂ) (p : ℕ) (P : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial ℂ) :=
  (P.map (Polynomial.eval₂RingHom Polynomial.C (quadIteratePoly c p))).comp (Polynomial.X ^ (2 ^ p))

/-- **`compRelPoly`'s relation is the composed relation** `relation(Q)(z,w) = P(f^[p]z, w^{2^p})`. -/
theorem compRelPoly_relation (c : ℂ) (p : ℕ) (P : Polynomial (Polynomial ℂ)) (z w : ℂ) :
    (∑ i ∈ (compRelPoly c p P).support, ((compRelPoly c p P).coeff i).aeval z * w ^ i)
      = ∑ i ∈ P.support, (P.coeff i).aeval ((quadratic c)^[p] z) * (w ^ (2 ^ p)) ^ i := by
  rw [relation_eq_eval_map, relation_eq_eval_map P ((quadratic c)^[p] z) (w ^ (2 ^ p))]
  rw [compRelPoly, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.map_map]
  congr 2
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_evalRingHom,
    Polynomial.coe_eval₂RingHom]
  change Polynomial.eval z (a.comp (quadIteratePoly c p)) = Polynomial.eval ((quadratic c)^[p] z) a
  rw [Polynomial.eval_comp, quadIteratePoly_eval]

/-- The `m`-fold iterate of `w ↦ w^N` is `w ↦ w^{N^m}`. -/
theorem iterate_pow (N : ℕ) (w : ℂ) (m : ℕ) : (fun x : ℂ => x ^ N)^[m] w = w ^ (N ^ m) := by
  induction m with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ih, ← pow_mul, ← pow_succ]

/-- **Squaring-fixed nonzero root at a periodic point.** At a periodic `z₀` (`f_c^[p] z₀ = z₀`), with the
divisibility `(C e)·compRelPoly = P·S` and `e(z₀) ≠ 0`, the nonzero roots of `P(z₀, ·)` are closed under
`w ↦ w^{2^p}` (from `compRelPoly_relation` at the fixed point). The set is finite (`P(z₀,·) ≠ 0`), so by
`exists_periodic_of_finite_mapsTo` it contains `w₀ ≠ 0` with `w₀^{2^{p·m}} = w₀` for some `m ≥ 1` — exactly
the `w₀^{2^{p'}} = w₀`, `w₀ ≠ 0` simple-root datum the divisibility-route capstone needs (with the matching
`f_c^[p·m] z₀ = z₀`). Reduces the dynamical input to: a periodic point with `P(z₀,·)` nonzero, nonzero-rooted,
`e(z₀) ≠ 0` — plus simplicity and non-resonance at exponent `p·m`. -/
theorem exists_pow_fixed_root (c : ℂ) (p : ℕ) (P S : Polynomial (Polynomial ℂ)) {e : Polynomial ℂ}
    {z₀ : ℂ} (hper : (quadratic c)^[p] z₀ = z₀)
    (hPS : (Polynomial.C e) * (compRelPoly c p P) = P * S) (hez : e.eval z₀ ≠ 0)
    (hPz0 : P.map (Polynomial.evalRingHom z₀) ≠ 0)
    {w : ℂ} (hw : (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) = 0) (hwne : w ≠ 0) :
    ∃ (w₀ : ℂ) (m : ℕ), 1 ≤ m ∧ w₀ ≠ 0 ∧
      (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧ w₀ ^ (2 ^ (p * m)) = w₀ := by
  classical
  have hclosed : ∀ v : ℂ, (∑ i ∈ P.support, (P.coeff i).aeval z₀ * v ^ i) = 0 →
      (∑ i ∈ P.support, (P.coeff i).aeval z₀ * (v ^ (2 ^ p)) ^ i) = 0 := by
    intro v hv
    have key := congrArg (fun T : Polynomial (Polynomial ℂ) =>
        ∑ i ∈ T.support, (T.coeff i).aeval z₀ * v ^ i) hPS
    simp only [] at key
    rw [relation_mul, relation_C, relation_mul, hv, zero_mul, compRelPoly_relation, hper] at key
    exact (mul_eq_zero.mp key).resolve_left hez
  set rootSet := {v : ℂ | (∑ i ∈ P.support, (P.coeff i).aeval z₀ * v ^ i) = 0 ∧ v ≠ 0} with hrs
  have hrelmap : ∀ v : ℂ, (∑ i ∈ P.support, (P.coeff i).aeval z₀ * v ^ i)
      = (P.map (Polynomial.evalRingHom z₀)).eval v := fun v => relation_eq_eval_map P z₀ v
  have hfin : rootSet.Finite := by
    apply Set.Finite.subset (Polynomial.finite_setOf_isRoot hPz0)
    intro v hv
    rw [hrs, Set.mem_setOf_eq] at hv
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, ← hrelmap]
    exact hv.1
  have hmaps : Set.MapsTo (fun v => v ^ (2 ^ p)) rootSet rootSet := by
    intro v hv
    rw [hrs, Set.mem_setOf_eq] at hv ⊢
    exact ⟨hclosed v hv.1, pow_ne_zero _ hv.2⟩
  have hw_mem : w ∈ rootSet := ⟨hw, hwne⟩
  obtain ⟨w₀, hw₀mem, m, hm1, hfix⟩ := exists_periodic_of_finite_mapsTo hfin hmaps hw_mem
  rw [hrs, Set.mem_setOf_eq] at hw₀mem
  refine ⟨w₀, m, hm1, hw₀mem.2, hw₀mem.1, ?_⟩
  rw [iterate_pow, ← pow_mul] at hfix
  exact hfix

/-- **Non-resonance from a modulus bound.** If `‖λ‖ > 2^p` then `λ^m ≠ 2^p` for all `m ≥ 1`
(`‖λ^m‖ = ‖λ‖^m ≥ ‖λ‖ > 2^p`). Converts the resonance side-condition of `const_of_no_resonance` into a
single inequality on the multiplier modulus — and it transfers through exponent adjustment: `‖λ‖ > 2^p`
gives `‖λ^m‖ = ‖λ‖^m > (2^p)^m = 2^{p·m}`, so a strongly-repelling cycle stays non-resonant at the
squaring-orbit exponent `p·m`. -/
theorem nonresonant_of_norm_gt {lam : ℂ} {p : ℕ} (h : (2 ^ p : ℝ) < ‖lam‖) :
    ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ) := by
  intro m hm hcon
  have hnormeq : ‖lam‖ ^ m = (2 ^ p : ℝ) := by
    have := congrArg norm hcon
    rw [norm_pow] at this
    rw [this, Complex.norm_natCast]; push_cast; ring
  have h2p : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have h1 : (1 : ℝ) ≤ ‖lam‖ := le_of_lt (lt_of_le_of_lt h2p h)
  have hge : (2 ^ p : ℝ) < ‖lam‖ ^ m := by
    calc (2 ^ p : ℝ) < ‖lam‖ := h
      _ = ‖lam‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖lam‖ ^ m := pow_le_pow_right₀ h1 hm
  linarith [hnormeq, hge]

/-- **Non-resonance from an attracting multiplier.** If `‖λ‖ < 1` (and `p ≥ 1`) then `λ^m ≠ 2^p` for all
`m ≥ 1` (`‖λ^m‖ = ‖λ‖^m ≤ ‖λ‖ < 1 < 2 ≤ 2^p`). Completes the modulus dichotomy with `nonresonant_of_norm_gt`:
both attracting and strongly-repelling cycles are non-resonant. -/
theorem nonresonant_of_norm_lt_one {lam : ℂ} {p : ℕ} (hp : 1 ≤ p) (h : ‖lam‖ < 1) :
    ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ) := by
  intro m hm hcon
  have hnormeq : ‖lam‖ ^ m = (2 ^ p : ℝ) := by
    have := congrArg norm hcon
    rw [norm_pow] at this
    rw [this, Complex.norm_natCast]; push_cast; ring
  have hle : ‖lam‖ ^ m ≤ ‖lam‖ := by
    calc ‖lam‖ ^ m ≤ ‖lam‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h) hm
      _ = ‖lam‖ := pow_one _
  have h2p : (2 : ℝ) ≤ 2 ^ p := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  linarith [hnormeq, hle, h]

/-- **Multiplier of an iterated period.** At a point fixed by `F^[p]` (`F^[p] z₀ = z₀`) with
`HasDerivAt (F^[p]) λ z₀`, the `m`-fold composite `F^[p·m]` has derivative `λ^m` at `z₀` (chain rule along
the cycle). Pairs with `exists_pow_fixed_root`: when the squaring-orbit exponent is `p·m`, the multiplier
becomes `λ^m`, and `nonresonant_of_norm_gt` applies to `‖λ^m‖ = ‖λ‖^m`. -/
theorem hasDerivAt_iterate_periodic {F : ℂ → ℂ} {z₀ lam : ℂ} {p : ℕ}
    (hper : F^[p] z₀ = z₀) (hlam : HasDerivAt (F^[p]) lam z₀) :
    ∀ m : ℕ, HasDerivAt (F^[p * m]) (lam ^ m) z₀ := by
  intro m
  induction m with
  | zero => simpa using hasDerivAt_id z₀
  | succ k ih =>
    have hcomp : F^[p * (k + 1)] = F^[p] ∘ F^[p * k] := by
      rw [← Function.iterate_add, Nat.mul_succ, Nat.add_comm]
    have hfix : F^[p * k] z₀ = z₀ := by
      rw [Function.iterate_mul]; exact Function.iterate_fixed hper k
    have hg : HasDerivAt (F^[p]) lam (F^[p * k] z₀) := by rw [hfix]; exact hlam
    rw [hcomp, pow_succ']
    exact hg.comp z₀ ih

/-- **Divisibility up to a `ℂ[z]`-denominator — the gateway of the divisibility route.** If `P` is a
minimal-`w`-degree nonzero relation vanishing on `U` (at `w = φ_c`) and `Q` is *any* relation vanishing on
`U`, then `(C e)·Q = P·S` for some nonzero `e ∈ ℂ[z]` and `S ∈ ℂ[z][w]` — i.e. `P ∣ Q` in `ℂ(z)[w]`.
Proof: Euclidean-divide `Q = P·S + R` in `(RatFunc ℂ)[w]` (a field's polynomial ring, `degree R < degree P`);
clear denominators with `IsLocalization.integerNormalization` into one identity `(C e)·Q = P·S₃ + R₃` over
`ℂ[z][w]` with `natDegree R₃ < natDegree P`; the `relation` ring-hom at `(z, φ_c z)` for `z ∈ U` annihilates
the `e`-, `P`- and `Q`-terms (via `relation_mul`/`relation_add`/`relation_C` and the two vanishing
hypotheses), so `R₃` vanishes on all of `U`; minimality of `P` forces `R₃ = 0`. With `Q = compRelPoly c p P`
this is exactly the `P ∣ P(f^[p]·, ·^{2^p})` behind `funEq_of_branch`'s `hdiv`. -/
theorem divides_relation_up_to_denom {U : Set ℂ} (c : ℂ)
    (P Q : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hQrel : ∀ z ∈ U, ∑ i ∈ Q.support, (Q.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 ∧
      (Polynomial.C e) * Q = P * S := by
  classical
  set fm : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) with hfm
  have hinj : Function.Injective fm := IsFractionRing.injective _ _
  set Pb := P.map fm with hPbdef
  set Qb := Q.map fm with hQbdef
  have hPbne : Pb ≠ 0 := by rw [hPbdef, ne_eq, Polynomial.map_eq_zero_iff hinj]; exact hP0
  set Sb := Qb / Pb with hSbdef
  set Rb := Qb % Pb with hRbdef
  have hdiveq : Pb * Sb + Rb = Qb := EuclideanDomain.div_add_mod Qb Pb
  have hRbdeg : Rb.degree < Pb.degree := Polynomial.degree_mod_lt Qb hPbne
  obtain ⟨bS, hbSmem, hbS⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℂ)) Sb
  obtain ⟨bR, hbRmem, hbR⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℂ)) Rb
  set Sn := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial ℂ)) Sb with hSndef
  set Rn := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial ℂ)) Rb with hRndef
  have hbS0 : bS ≠ 0 := nonZeroDivisors.ne_zero hbSmem
  have hbR0 : bR ≠ 0 := nonZeroDivisors.ne_zero hbRmem
  set e : Polynomial ℂ := bS * bR with hedef
  have he0 : e ≠ 0 := mul_ne_zero hbS0 hbR0
  set S₃ : Polynomial (Polynomial ℂ) := (Polynomial.C bR) * Sn with hS3def
  set R₃ : Polynomial (Polynomial ℂ) := (Polynomial.C bS) * Rn with hR3def
  have hsmulS : bS • Sb = Polynomial.C (fm bS) * Sb := by rw [Algebra.smul_def]; rfl
  have hsmulR : bR • Rb = Polynomial.C (fm bR) * Rb := by rw [Algebra.smul_def]; rfl
  have hmapS3 : Polynomial.map fm S₃ = Polynomial.C (fm bR) * (bS • Sb) := by
    rw [hS3def, Polynomial.map_mul, Polynomial.map_C, hbS]
  have hmapR3 : Polynomial.map fm R₃ = Polynomial.C (fm bS) * (bR • Rb) := by
    rw [hR3def, Polynomial.map_mul, Polynomial.map_C, hbR]
  have hCe : Polynomial.C (fm e) = Polynomial.C (fm bS) * Polynomial.C (fm bR) := by
    rw [hedef, map_mul, Polynomial.C_mul]
  have hL : Polynomial.map fm ((Polynomial.C e) * Q) = Polynomial.C (fm e) * Qb := by
    rw [Polynomial.map_mul, Polynomial.map_C, ← hQbdef]
  have hR : Polynomial.map fm (P * S₃ + R₃) = Polynomial.C (fm e) * Qb := by
    rw [Polynomial.map_add, Polynomial.map_mul, hmapS3, hmapR3, hsmulS, hsmulR, ← hPbdef, hCe,
      ← hdiveq]
    ring
  have hmaster : (Polynomial.C e) * Q = P * S₃ + R₃ :=
    Polynomial.map_injective fm hinj (hL.trans hR.symm)
  have hrelR3 : ∀ z ∈ U, (∑ i ∈ R₃.support, (R₃.coeff i).aeval z * (bottcherCoord c z) ^ i) = 0 := by
    intro z hz
    have key : (∑ i ∈ ((Polynomial.C e) * Q).support,
          (((Polynomial.C e) * Q).coeff i).aeval z * (bottcherCoord c z) ^ i)
        = (∑ i ∈ (P * S₃ + R₃).support, ((P * S₃ + R₃).coeff i).aeval z * (bottcherCoord c z) ^ i) := by
      rw [hmaster]
    rw [relation_mul, relation_C, relation_add, relation_mul, hQrel z hz, hPrel z hz,
      mul_zero, zero_mul, zero_add] at key
    exact key.symm
  have hR30 : R₃ = 0 := by
    by_contra hne
    have hRnne : Rn ≠ 0 := by rintro h; rw [hR3def, h, mul_zero] at hne; exact hne rfl
    have hRbne : Rb ≠ 0 := by
      rintro h
      apply hRnne
      have : Polynomial.map fm Rn = 0 := by rw [hbR, h, smul_zero]
      exact (Polynomial.map_eq_zero_iff hinj).mp this
    have hfmbR : fm bR ≠ 0 := by rw [hfm, ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hbR0
    have hnatRn : Rn.natDegree = Rb.natDegree := by
      have h1 : (Polynomial.map fm Rn).natDegree = Rn.natDegree :=
        Polynomial.natDegree_map_eq_of_injective hinj Rn
      rw [hbR, hsmulR, Polynomial.natDegree_C_mul hfmbR] at h1
      exact h1.symm
    have hRbnat : Rb.natDegree < Pb.natDegree := Polynomial.natDegree_lt_natDegree hRbne hRbdeg
    have hPbnat : Pb.natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective hinj P
    have hR3nat : R₃.natDegree = Rn.natDegree := by
      rw [hR3def, Polynomial.natDegree_C_mul hbS0]
    have hlt : R₃.natDegree < P.natDegree := by rw [hR3nat, hnatRn, ← hPbnat]; exact hRbnat
    have hle := hPmin R₃ hne hrelR3
    omega
  exact ⟨e, S₃, he0, by rw [hmaster, hR30, add_zero]⟩

/-- **The `hdiv` of `funEq_of_branch`, produced by the divisibility gateway.** Given `(C e)·Q = P·S`
(`Q = compRelPoly c p P`, `e ≠ 0`) and a local branch `g` of `P` at `z₀` (continuous, satisfying
`relation(P)(z, g z) = 0` near `z₀`), the composed relation `P(f^[p]z, (g z)^{2^p}) = relation(Q)(z, g z)`
vanishes near `z₀`. Evaluating the `relation` ring-hom at `(z, g z)` gives `e.eval z · relation(Q)(z,gz) =
relation(P)(z,gz)·relation(S)(z,gz) = 0` near `z₀`; `e ≠ 0` is nonzero off its finite root set (`𝓝[≠] z₀ ≤
cofinite`), so `relation(Q)(z,gz) = 0` on the punctured neighbourhood, and continuity of `z ↦
relation(Q)(z,gz)` extends it across `z₀`. This is exactly `funEq_of_branch`'s `hdiv` with `F = f^[p]`,
`dd = 2^p` — the bridge from the algebraic-divisibility gateway to the Böttcher functional equation. -/
theorem funEq_hdiv_of_divides (c : ℂ) (p : ℕ) (P : Polynomial (Polynomial ℂ))
    {e : Polynomial ℂ} {S : Polynomial (Polynomial ℂ)} (he0 : e ≠ 0)
    (hPS : (Polynomial.C e) * (compRelPoly c p P) = P * S)
    {g : ℂ → ℂ} {z₀ : ℂ} (hg : ContinuousAt g z₀)
    (hgrel : ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0) :
    ∀ᶠ z in 𝓝 z₀,
      ∑ i ∈ P.support, (P.coeff i).aeval ((quadratic c)^[p] z) * ((g z) ^ (2 ^ p)) ^ i = 0 := by
  set Q := compRelPoly c p P with hQdef
  set h : ℂ → ℂ := fun z => ∑ i ∈ Q.support, (Q.coeff i).aeval z * (g z) ^ i with hhdef
  have hcont : ContinuousAt h z₀ := by
    apply tendsto_finsetSum
    intro i _
    exact ((Polynomial.contDiff_aeval (𝕜 := ℂ) (Q.coeff i) ⊤).continuous.continuousAt).mul (hg.pow i)
  have hkey : ∀ᶠ z in 𝓝 z₀, e.eval z * h z = 0 := by
    filter_upwards [hgrel] with z hz
    have hev : (∑ i ∈ ((Polynomial.C e) * Q).support,
          (((Polynomial.C e) * Q).coeff i).aeval z * (g z) ^ i)
        = (∑ i ∈ (P * S).support, ((P * S).coeff i).aeval z * (g z) ^ i) := by rw [hPS]
    rw [relation_mul, relation_C, relation_mul, hz, zero_mul] at hev
    exact hev
  have hane : ∀ᶠ z in 𝓝[≠] z₀, e.eval z ≠ 0 := by
    have hfin : ({x | e.IsRoot x}).Finite := Polynomial.finite_setOf_isRoot he0
    have hmem : ({x | e.IsRoot x}ᶜ) ∈ 𝓝[≠] z₀ := nhdsNE_le_cofinite z₀ hfin.compl_mem_cofinite
    filter_upwards [hmem] with z hz
    exact hz
  have hpunct : ∀ᶠ z in 𝓝[≠] z₀, h z = 0 := by
    filter_upwards [hane, hkey.filter_mono nhdsWithin_le_nhds] with z hane' hkey'
    exact (mul_eq_zero.mp hkey').resolve_left hane'
  have hz0 : h z₀ = 0 := by
    have h2 : Tendsto h (𝓝[≠] z₀) (𝓝 (h z₀)) := hcont.continuousWithinAt.tendsto
    have h3 : Tendsto h (𝓝[≠] z₀) (𝓝 0) :=
      Filter.Tendsto.congr' (hpunct.mono (fun z hz => hz.symm)) tendsto_const_nhds
    exact tendsto_nhds_unique h2 h3
  have hfull : ∀ᶠ z in 𝓝 z₀, h z = 0 := by
    rw [eventually_nhdsWithin_iff] at hpunct
    filter_upwards [hpunct] with z hz
    by_cases hzz : z = z₀
    · rw [hzz]; exact hz0
    · exact hz (by simp [hzz])
  filter_upwards [hfull] with z hz
  rw [← compRelPoly_relation c p P z (g z)]
  exact hz

end Bottcher
