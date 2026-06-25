/-
# The Mahler polynomial obstruction: no nonconstant `r` with `r(z²+c) = λ r(z)²` for `c ≠ 0`

The Mahler-method route to φ_c transcendence (`PhiMahler`) reduces the `n = 1` case — φ_c **not
rational** — to a pure polynomial fact. If `φ_c = p/q` were rational, coprimality and the functional
equation force `p(z²+c) = λ p(z)²` and `q(z²+c) = λ q(z)²`; at least one of `p, q` is nonconstant.

This file proves the obstruction outright: for `c ≠ 0`, **no nonconstant `r ∈ ℂ[X]` satisfies
`r(z²+c) = λ r(z)²`** (`no_nonconstant_mahler_poly`). The mechanism is multiplicity doubling. The
squaring map `σ : z ↦ z²+c` is unramified except at `0`, so for a root `z₀ ≠ 0`,
`mult_{σz₀}(r) = 2·mult_{z₀}(r)` — the multiplicity *doubles* along the forward orbit. A finite-degree
polynomial cannot sustain that, unless the maximal-multiplicity root is `0`; but then the ramified
relation at `0` makes `c` a root of equal (maximal) multiplicity, and `c ≠ 0` bounces back into the
doubling contradiction.

The key tool is a general composition-multiplicity identity
`rootMultiplicity z (p ∘ g) = mult_{g(z)}(p) · mult_z(g − g(z))`.
-/
import GaloisForLFunctions.U0.PhiMahler
import Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial

namespace MahlerPolynomial

/-- **Multiplicity of a power.** `mult_z(fᵏ) = k · mult_z(f)` for `f ≠ 0`. -/
theorem rootMultiplicity_pow {f : ℂ[X]} (hf : f ≠ 0) (k : ℕ) (z : ℂ) :
    rootMultiplicity z (f ^ k) = k * rootMultiplicity z f := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hf) hf), ih]
    ring

/-- **Composition-multiplicity identity.** For `p ≠ 0` and `w = g(z)`, factoring `p = (X − C w)^k · s`
with `s(w) ≠ 0` gives `p ∘ g = (g − C w)^k · (s ∘ g)`, and `s ∘ g` is nonzero at `z`. Hence
`mult_z(p ∘ g) = mult_{g(z)}(p) · mult_z(g − C(g(z)))`. The hypothesis `hgz` (that `g − C(g z) ≠ 0`,
automatic for nonconstant `g`) avoids the degenerate constant-`g` branch. -/
theorem rootMultiplicity_comp {p g : ℂ[X]} (hp : p ≠ 0) (z : ℂ)
    (hgz : g - C (g.eval z) ≠ 0) :
    rootMultiplicity z (p.comp g)
      = rootMultiplicity (g.eval z) p * rootMultiplicity z (g - C (g.eval z)) := by
  set w := g.eval z with hw
  obtain ⟨s, hps, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp w
  have hsw : s.eval w ≠ 0 := fun h => hnd ((dvd_iff_isRoot).mpr h)
  have hcomp : p.comp g = (g - C w) ^ (rootMultiplicity w p) * s.comp g := by
    conv_lhs => rw [hps]
    rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp]
  have hscompne : s.comp g ≠ 0 := by
    intro h
    have h2 := congrArg (eval z) h
    rw [eval_comp, eval_zero] at h2
    exact hsw h2
  have hsroot : ¬ (s.comp g).IsRoot z := by
    rw [IsRoot.def, eval_comp]; exact hsw
  rw [hcomp, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hgz) hscompne),
      rootMultiplicity_pow hgz, rootMultiplicity_eq_zero hsroot, add_zero]

/-- **The quadratic ramification factor.** `mult_z((X²+c) − C((z²+c))) = mult_z(X² − C(z²))` is `2` if
`z = 0` (the critical point, ramified) and `1` otherwise. -/
theorem rootMultiplicity_quadratic_factor (c z : ℂ) :
    rootMultiplicity z ((X ^ 2 + C c) - C (((X ^ 2 + C c).eval z))) = if z = 0 then 2 else 1 := by
  have heval : (X ^ 2 + C c).eval z = z ^ 2 + c := by simp
  have hfact : (X ^ 2 + C c) - C (z ^ 2 + c) = (X - C z) * (X + C z) := by
    simp only [map_add, map_pow]; ring
  rw [heval, hfact]
  have h2ne : (X + C z) ≠ 0 := by
    rw [show (X + C z) = X - C (-z) by rw [map_neg, sub_neg_eq_add]]; exact X_sub_C_ne_zero _
  rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero z) h2ne), rootMultiplicity_X_sub_C_self]
  have h2 : rootMultiplicity z (X + C z) = if z = 0 then 1 else 0 := by
    by_cases hz : z = 0
    · subst hz
      rw [map_zero, add_zero, if_pos rfl, show (X : ℂ[X]) = X - C 0 by rw [map_zero, sub_zero],
          rootMultiplicity_X_sub_C_self]
    · rw [if_neg hz]
      apply rootMultiplicity_eq_zero
      rw [IsRoot.def, eval_add, eval_X, eval_C]
      intro h
      exact hz (by linear_combination h / 2)
  rw [h2]
  by_cases hz : z = 0 <;> simp [hz]

/-- **The Mahler multiplicity identity.** From `r(z²+c) = λ r(z)²` (with `r ≠ 0`, forcing `λ ≠ 0`), at
every `z`: `2·mult_z(r) = mult_{z²+c}(r) · (2 if z=0 else 1)`. The left side is `mult_z` of the square;
the right is `mult_z` of the composition `r ∘ (X²+c)` via `rootMultiplicity_comp` and the ramification
factor. -/
theorem mahler_mult_identity {c lam : ℂ} {r : ℂ[X]} (hr0 : r ≠ 0) (hlam : lam ≠ 0)
    (hr : r.comp (X ^ 2 + C c) = C lam * r ^ 2) (z : ℂ) :
    2 * rootMultiplicity z r = rootMultiplicity (z ^ 2 + c) r * (if z = 0 then 2 else 1) := by
  have heval : (X ^ 2 + C c).eval z = z ^ 2 + c := by simp
  have hquad_ne : (X ^ 2 + C c) - C (((X ^ 2 + C c).eval z)) ≠ 0 := by
    rw [heval, show (X ^ 2 + C c) - C (z ^ 2 + c) = (X - C z) * (X + C z) by
      simp only [map_add, map_pow]; ring]
    exact mul_ne_zero (X_sub_C_ne_zero z)
      (by rw [show (X + C z) = X - C (-z) by rw [map_neg, sub_neg_eq_add]]; exact X_sub_C_ne_zero _)
  have e1 : rootMultiplicity z (r.comp (X ^ 2 + C c))
      = rootMultiplicity (z ^ 2 + c) r * (if z = 0 then 2 else 1) := by
    rw [rootMultiplicity_comp hr0 z hquad_ne, rootMultiplicity_quadratic_factor, heval]
  have e2 : rootMultiplicity z (r.comp (X ^ 2 + C c)) = 2 * rootMultiplicity z r := by
    rw [hr, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero 2 hr0)),
        rootMultiplicity_C, zero_add, rootMultiplicity_pow hr0]
  exact e2.symm.trans e1

/-- **No nonconstant Mahler polynomial (PROVED).** For `c ≠ 0`, there is no nonconstant `r ∈ ℂ[X]` with
`r(z²+c) = λ r(z)²`. Proof: let `z₀` be a root of maximal multiplicity `m ≥ 1`. If `z₀ ≠ 0`, the
identity gives `mult_{z₀²+c}(r) = 2m`, but `z₀²+c` is then a root, so `2m ≤ m` — impossible. If `z₀ = 0`,
the ramified identity makes `mult_c(r) = m`, and `c ≠ 0` is a maximal root; applying the unramified case
to `c` gives `2m ≤ m`. Either way, contradiction. This is the `n = 1` case of φ_c transcendence: φ_c is
not a rational function. -/
theorem no_nonconstant_mahler_poly {c lam : ℂ} (hc : c ≠ 0) {r : ℂ[X]}
    (hnc : 0 < r.natDegree) (hr : r.comp (X ^ 2 + C c) = C lam * r ^ 2) : False := by
  have hr0 : r ≠ 0 := fun h => by simp [h] at hnc
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul, comp_eq_zero_iff] at hr
    rcases hr with h1 | ⟨_, h2⟩
    · exact hr0 h1
    · have hdeg : (X ^ 2 + C c).natDegree = 2 := by compute_degree!
      rw [h2, natDegree_C] at hdeg; exact absurd hdeg (by norm_num)
  have key := mahler_mult_identity hr0 hlam hr
  set S := r.roots.toFinset with hS
  have hSne : S.Nonempty := by
    obtain ⟨w, hw⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hnc)
    exact ⟨w, by rw [hS, Multiset.mem_toFinset, mem_roots hr0]; exact hw⟩
  obtain ⟨z₀, hz₀S, hz₀max⟩ := S.exists_max_image (fun w => rootMultiplicity w r) hSne
  have hz₀root : r.IsRoot z₀ := by rw [hS, Multiset.mem_toFinset, mem_roots hr0] at hz₀S; exact hz₀S
  have hm1 : 1 ≤ rootMultiplicity z₀ r := (rootMultiplicity_pos hr0).mpr hz₀root
  have hmax : ∀ w : ℂ, r.IsRoot w → rootMultiplicity w r ≤ rootMultiplicity z₀ r :=
    fun w hw => hz₀max w (by rw [hS, Multiset.mem_toFinset, mem_roots hr0]; exact hw)
  have step : ∀ w : ℂ, w ≠ 0 → rootMultiplicity z₀ r ≤ rootMultiplicity w r → False := by
    intro w hw0 hwm
    have hk := key w
    rw [if_neg hw0, mul_one] at hk
    have hpos : 0 < rootMultiplicity (w ^ 2 + c) r := by omega
    have hroot : r.IsRoot (w ^ 2 + c) := (rootMultiplicity_pos hr0).mp hpos
    have hle := hmax (w ^ 2 + c) hroot
    omega
  by_cases hz0 : z₀ = 0
  · have hk := key z₀
    rw [if_pos hz0, hz0, show (0 : ℂ) ^ 2 + c = c by ring] at hk
    have hcle : rootMultiplicity z₀ r ≤ rootMultiplicity c r := by rw [hz0]; omega
    exact step c hc hcle
  · exact step z₀ hz0 (le_refl _)

/-- **Coprime cross-multiplied form ⟹ each side is `const · square`.** If coprime `p, q` satisfy the
cross-multiplied functional equation `p(σz)·q(z)² = p(z)²·q(σz)` (`σ = X²+c`), then `p(σz) = λ·p(z)²`
for a constant `λ`. Proof: from the equation `p² ∣ p(σz)·q²`, and `IsCoprime (p²) (q²)` gives
`p² ∣ p(σz)`; since `σ` has degree `2`, `deg(p∘σ) = 2·deg p = deg(p²)`, so the cofactor is a constant.
(The symmetric statement for `q` holds by the same argument with `p, q` swapped.) This is the algebraic
bridge from a rational `φ_c = p/q` to the Mahler obstruction `no_nonconstant_mahler_poly`. -/
theorem comp_eq_const_mul_sq {c : ℂ} {p q : ℂ[X]} (hp : p ≠ 0) (hpq : IsCoprime p q)
    (heq : p.comp (X ^ 2 + C c) * q ^ 2 = p ^ 2 * q.comp (X ^ 2 + C c)) :
    ∃ lam : ℂ, p.comp (X ^ 2 + C c) = C lam * p ^ 2 := by
  set g := X ^ 2 + C c with hg
  have hgdeg : g.natDegree = 2 := by rw [hg]; compute_degree!
  have hpcomp_ne : p.comp g ≠ 0 := by
    intro h
    rw [comp_eq_zero_iff] at h
    rcases h with h1 | ⟨_, h2⟩
    · exact hp h1
    · have hgd := hgdeg; rw [h2, natDegree_C] at hgd; exact absurd hgd (by norm_num)
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hdvd1 : p ^ 2 ∣ p.comp g := by
    have h : p ^ 2 ∣ p.comp g * q ^ 2 := by rw [heq]; exact dvd_mul_right _ _
    exact (hpq.pow).dvd_of_dvd_mul_right h
  obtain ⟨t, ht⟩ := hdvd1
  have ht0 : t ≠ 0 := by intro h; rw [h, mul_zero] at ht; exact hpcomp_ne ht
  have hdeg : (p.comp g).natDegree = (p ^ 2).natDegree := by
    rw [natDegree_comp, hgdeg, natDegree_pow]; ring
  have htdeg : t.natDegree = 0 := by
    rw [ht, natDegree_mul hp2 ht0] at hdeg; omega
  obtain ⟨lam, hlamt⟩ := natDegree_eq_zero.mp htdeg
  exact ⟨lam, by rw [ht, ← hlamt]; ring⟩

/-- **No coprime rational solution of the Mahler equation (PROVED).** For `c ≠ 0`, there are no coprime
`p, q ∈ ℂ[X]` (not both constant) with `p(σz)·q(z)² = p(z)²·q(σz)` — the cross-multiplied form of
`φ_c(σz) = φ_c(z)²` for `φ_c = p/q`. By `comp_eq_const_mul_sq`, `p(σz)=λp²` and `q(σz)=μq²`; whichever of
`p, q` is nonconstant then violates `no_nonconstant_mahler_poly`. This is the polynomial skeleton of
"φ_c is not rational" — the `n = 1` case of φ_c transcendence over `ℂ(z)`; the only remaining step is the
analytic bridge expressing the escape-region identity `φ_c = p/q` as this polynomial equation. -/
theorem no_coprime_mahler_rational {c : ℂ} (hc : c ≠ 0) {p q : ℂ[X]}
    (hpq : IsCoprime p q) (hp : p ≠ 0) (hq : q ≠ 0)
    (heq : p.comp (X ^ 2 + C c) * q ^ 2 = p ^ 2 * q.comp (X ^ 2 + C c))
    (hnc : 0 < p.natDegree ∨ 0 < q.natDegree) : False := by
  rcases hnc with h | h
  · obtain ⟨lam, hlam⟩ := comp_eq_const_mul_sq hp hpq heq
    exact no_nonconstant_mahler_poly hc h hlam
  · obtain ⟨mu, hmu⟩ := comp_eq_const_mul_sq hq hpq.symm
      (by rw [mul_comm (q.comp (X ^ 2 + C c)) (p ^ 2), mul_comm (q ^ 2) (p.comp (X ^ 2 + C c))];
          exact heq.symm)
    exact no_nonconstant_mahler_poly hc h hmu

end MahlerPolynomial
