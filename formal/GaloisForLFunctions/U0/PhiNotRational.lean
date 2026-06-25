/-
# φ_c is not a rational function (the `n = 1` case of φ_c transcendence)

Assembles the Mahler obstruction (`MahlerPolynomial.no_coprime_mahler_rational`) with the escape-region
functional equation (`bottcherCoord_quadratic`) to prove: for `c ≠ 0`, the Böttcher coordinate `φ_c` is
**not** a rational function. If `φ_c = p/q` (coprime, not both constant) on the escape region, the
functional equation `φ_c(z²+c) = φ_c(z)²` cross-multiplies to the *polynomial* identity
`p(z²+c)·q(z)² = p(z)²·q(z²+c)` — equality on the infinite escape region forces equality of polynomials
(identity theorem) — which `no_coprime_mahler_rational` refutes.

This is the `deg_Y = 1` sub-case of the card's `deg_U = 0` step (φ_c not algebraic over `ℂ(z)`); the
higher-degree cases are the full Mahler/Nishioka height argument.
-/
import GaloisForLFunctions.U0.MahlerPolynomial

open Polynomial Bottcher

namespace PhiNotRational

/-- The escape region is infinite (it contains the real ray `(max 2 ‖c‖, ∞)`). -/
@[aesop safe]
theorem escapeOpen_infinite (c : ℂ) : (escapeOpen c).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((max 2 ‖c‖ + 1 + n : ℝ) : ℂ))
  · intro a b hab
    have h1 : (max 2 ‖c‖ + 1 + (a : ℝ)) = (max 2 ‖c‖ + 1 + (b : ℝ)) := Complex.ofReal_injective hab
    exact_mod_cast (by linarith : (a : ℝ) = (b : ℝ))
  · intro n
    show max 2 ‖c‖ < ‖((max 2 ‖c‖ + 1 + (n : ℝ) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := le_max_left 2 ‖c‖; positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **φ_c is not rational (PROVED).** For `c ≠ 0`, no coprime, not-both-constant `p, q ∈ ℂ[X]` (with
`p, q ≠ 0`) represent the Böttcher coordinate as `φ_c = p/q` on the escape region. The functional
equation cross-multiplies to `p(z²+c)·q(z)² = p(z)²·q(z²+c)`, valid wherever `q(z), q(z²+c) ≠ 0` — a
cofinite subset of the infinite escape region — hence a polynomial identity by `eq_of_infinite_eval_eq`,
refuted by `no_coprime_mahler_rational`. -/
@[aesop safe]
theorem bottcher_not_rational {c : ℂ} (hc : c ≠ 0) {p q : ℂ[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hncc : 0 < p.natDegree ∨ 0 < q.natDegree)
    (hrep : ∀ z ∈ escapeOpen c, q.eval z ≠ 0 → bottcherCoord c z = p.eval z / q.eval z) :
    False := by
  set σ : ℂ[X] := X ^ 2 + C c with hσ
  have hσ_ne : q.comp σ ≠ 0 := by
    intro h
    rw [comp_eq_zero_iff] at h
    rcases h with h1 | ⟨_, h2⟩
    · exact hq h1
    · have hd : σ.natDegree = 2 := by rw [hσ]; compute_degree!
      rw [h2, natDegree_C] at hd; exact absurd hd (by norm_num)
  -- The polynomial cross-equation, proved by the identity theorem.
  have hcross : p.comp σ * q ^ 2 = p ^ 2 * q.comp σ := by
    apply eq_of_infinite_eval_eq
    have hqfin : {z : ℂ | q.IsRoot z}.Finite := finite_setOf_isRoot hq
    have hqσfin : {z : ℂ | (q.comp σ).IsRoot z}.Finite := finite_setOf_isRoot hσ_ne
    have hgood : (escapeOpen c \ ({z | q.IsRoot z} ∪ {z | (q.comp σ).IsRoot z}))
        ⊆ {x : ℂ | eval x (p.comp σ * q ^ 2) = eval x (p ^ 2 * q.comp σ)} := by
      rintro z ⟨hzesc, hznot⟩
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hznot
      obtain ⟨hqz, hqσz⟩ := hznot
      have hqz' : q.eval z ≠ 0 := hqz
      have hσz : σ.eval z = quadratic c z := by rw [hσ, quadratic_apply]; simp
      have hσz_esc : quadratic c z ∈ escapeOpen c := PhiMahler.quadratic_mem_escapeOpen hzesc
      have hqAt : q.eval (quadratic c z) ≠ 0 := by
        have he : (q.comp σ).eval z = q.eval (quadratic c z) := by rw [eval_comp, hσz]
        rw [IsRoot.def, he] at hqσz; exact hqσz
      have hφz : bottcherCoord c z = p.eval z / q.eval z := hrep z hzesc hqz'
      have hφσz : bottcherCoord c (quadratic c z)
          = p.eval (quadratic c z) / q.eval (quadratic c z) := hrep _ hσz_esc hqAt
      obtain ⟨hcle, hz2⟩ := mem_escapeOpen_regime hzesc
      have hfe : bottcherCoord c (quadratic c z) = (bottcherCoord c z) ^ 2 :=
        bottcherCoord_quadratic hcle hz2
      rw [hφσz, hφz] at hfe
      have hcrossval : p.eval (quadratic c z) * (q.eval z) ^ 2
          = (p.eval z) ^ 2 * q.eval (quadratic c z) := by
        field_simp at hfe
        linear_combination hfe
      simp only [Set.mem_setOf_eq, eval_mul, eval_pow, eval_comp, hσz]
      linear_combination hcrossval
    exact Set.Infinite.mono hgood ((escapeOpen_infinite c).diff (hqfin.union hqσfin))
  exact MahlerPolynomial.no_coprime_mahler_rational hc hpq hp hq hcross hncc

end PhiNotRational
