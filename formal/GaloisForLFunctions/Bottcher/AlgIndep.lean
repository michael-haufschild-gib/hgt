/-
# Böttcher tower — Tier 1→4 bridge: monodromy ⟹ algebraic independence

Lifts the scalar obstruction (`eq_zero_of_high_monodromy`) to the conclusion the
q62 assembly actually needs: if a field automorphism `σ` (the monodromy / deck
transformation) fixes a transcendental `G`, fixes the multiplier `ζ` of order `m`,
and scales `F ↦ ζ·F`, then no nonzero polynomial relation `P(F,G)=0` of `Y`-degree
`< m` survives.  This is the algebraic content of
`unbounded-one-coordinate-monodromy-obstruction.md` in its bivariate form (the
negation of `AlgebraicIndependent` for the pair `(F,G)` at bounded degree).

Pure algebra; no analysis.  The complex-dynamics input (existence of `σ` with these
properties, of unbounded order `m`) is supplied later by the exact-monodromy tower.
-/
import GaloisForLFunctions.Bottcher.MonodromyObstruction
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

open Polynomial

namespace Bottcher

/-- Iterating the monodromy: `σ^[k] F = ζ^k · F` when `σ` fixes `ζ` and `σ F = ζ·F`. -/
theorem iterate_monodromy {M : Type*} [Field M] (σ : M →+* M)
    {ζ F : M} (hζ : σ ζ = ζ) (hF : σ F = ζ * F) :
    ∀ k : ℕ, σ^[k] F = ζ ^ k * F := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih, map_mul, map_pow, hζ, hF]
    ring

/-- A ring endomorphism that fixes every coefficient of `q` commutes with evaluation:
`σ (q.eval x) = q.eval (σ x)`. -/
theorem eval_comm_of_coeff_fixed {M : Type*} [Field M] (σ : M →+* M) (q : M[X]) (x : M)
    (hfix : ∀ i, σ (q.coeff i) = q.coeff i) : σ (q.eval x) = q.eval (σ x) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow, hfix]

/-- **Monodromy ⟹ algebraic independence (bivariate obstruction).**
Let `σ : M ≃ₐ[K] M` fix the transcendental `G` and the order-`m` multiplier `ζ`, and
send `F ↦ ζ·F` with `F ≠ 0`. Then any `P ∈ K[W][Y]` of `Y`-degree `< m` whose
substitution `P(F,G)` vanishes is the zero polynomial. -/
theorem eq_zero_of_monodromy
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (hG : Transcendental K G)
    (σ : M ≃ₐ[K] M) (hσG : σ G = G)
    (ζ : M) (m : ℕ) (hζord : orderOf ζ = m) (hσζ : σ ζ = ζ)
    (hF : F ≠ 0) (hσF : σ F = ζ * F)
    (P : Polynomial (Polynomial K)) (hdeg : P.natDegree < m)
    (hrel : (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0) :
    P = 0 := by
  classical
  set φ : Polynomial K →+* M := (aeval G : Polynomial K →ₐ[K] M).toRingHom with hφ
  set q : Polynomial M := P.map φ with hq
  -- (1) every coefficient of `q` is fixed by `σ`.
  have hfix : ∀ i, σ (q.coeff i) = q.coeff i := by
    intro i
    rw [hq, coeff_map]
    show σ ((aeval G) (P.coeff i)) = (aeval G) (P.coeff i)
    rw [← aeval_algHom_apply σ G (P.coeff i), hσG]
  have hfix' : ∀ i, σ.toRingHom (q.coeff i) = q.coeff i := hfix
  -- (2) evaluation at `F` commutes with all iterates of `σ`.
  have hcomm : ∀ k : ℕ, σ.toRingHom^[k] (q.eval F) = q.eval (σ.toRingHom^[k] F) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih,
          eval_comm_of_coeff_fixed σ.toRingHom q (σ.toRingHom^[n] F) hfix',
          ← Function.comp_apply (f := σ.toRingHom), ← Function.iterate_succ']
  -- (3) `q` vanishes at every rotate `ζ^k · F`, `k < m`.
  have hvanish : ∀ k : ℕ, k < m → q.eval (ζ ^ k * F) = 0 := by
    intro k _
    have hiter : σ.toRingHom^[k] F = ζ ^ k * F :=
      iterate_monodromy σ.toRingHom hσζ hσF k
    have hk := hcomm k
    rw [hiter, hrel, Function.iterate_fixed (map_zero σ.toRingHom) k] at hk
    exact hk.symm
  -- (4) hence `q = 0` by the finite-degree obstruction.
  have hdegq : q.natDegree < m := lt_of_le_of_lt natDegree_map_le hdeg
  have hq0 : q = 0 := eq_zero_of_high_monodromy hζord hF q hvanish hdegq
  -- (5) descend to `P = 0` using transcendence of `G`.
  refine Polynomial.ext (fun i => ?_)
  rw [coeff_zero]
  have h0 : q.coeff i = 0 := by rw [hq0]; simp
  rw [hq, coeff_map] at h0
  -- `h0 : φ (P.coeff i) = 0`, i.e. `aeval G (P.coeff i) = 0`
  by_contra hne
  exact hG ⟨P.coeff i, hne, h0⟩

/-- **Disconnected-case assembly (abstract).** If for every bound `d` there is a
monodromy automorphism fixing the transcendental `G`, fixing a multiplier `ζ` of
order `> d`, and scaling `F ↦ ζ·F`, then `F` and `G` satisfy *no* nonzero polynomial
relation — full algebraic independence. This is the §2 logic of
`q62-bottcher-independence-n2-all-parameters.md`: against any fixed-degree relation,
choose a deep enough Cantor cylinder (order `2ⁿ > deg`) and collapse it.
The hypothesis `mono` is exactly what `bottcher-exact-pruefer-monodromy` supplies. -/
theorem algIndep_of_unbounded_monodromy
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (hG : Transcendental K G) (hF : F ≠ 0)
    (mono : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F)
    (P : Polynomial (Polynomial K))
    (hrel : (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0) :
    P = 0 := by
  obtain ⟨σ, ζ, m, hlt, hord, hσG, hσζ, hσF⟩ := mono P.natDegree
  exact eq_zero_of_monodromy F G hG σ hσG ζ m hord hσζ hF hσF P hlt hrel

/-- **Unbounded monodromy ⟹ transcendence.** If `G ≠ 0` is scaled by automorphisms `σ` by
multipliers `ζ` of unbounded order (with `σ ζ = ζ`), then `G` is transcendental over `K`. An
algebraic `G` of degree `d` would have its `> d` distinct conjugates `ζ^k·G` (`k < orderOf ζ`,
order `> d`) all roots of its minimal polynomial — impossible. So the dyadic monodromy that gives
independence ALSO gives transcendence: the `Transcendental K G` hypothesis of
`algIndep_of_unbounded_monodromy` is itself a consequence of the monodromy tower, not a separate
input — reducing what the disconnected case must supply to the single `mono` datum. -/
theorem transcendental_of_monodromy {K M : Type*} [Field K] [Field M] [Algebra K M]
    (G : M) (hG0 : G ≠ 0)
    (mono : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M), d < orderOf ζ ∧ σ ζ = ζ ∧ σ G = ζ * G) :
    Transcendental K G := by
  classical
  intro hAlg
  obtain ⟨p, hp0, hpG⟩ := hAlg
  set q : M[X] := p.map (algebraMap K M) with hq
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K M).injective).mpr hp0
  obtain ⟨σ, ζ, hd, hσζ, hσG⟩ := mono p.natDegree
  have hpow : ∀ k, (σ ^ k) G = ζ ^ k * G := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hσζ, hσG]; ring
  have hconj : ∀ k, q.eval (ζ ^ k * G) = 0 := by
    intro k
    have he : q.eval ((σ ^ k) G) = aeval ((σ ^ k) G) p := by
      rw [hq, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [← hpow k, he, Polynomial.aeval_algHom_apply, hpG, map_zero]
  set m := orderOf ζ with hm
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k * G) (Set.Iio m) := rotate_injOn rfl hG0
  set S : Finset M := (Finset.range m).image (fun k => ζ ^ k * G) with hS
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro j hj k hk hjk
    exact hinj (Finset.mem_range.mp hj) (Finset.mem_range.mp hk) hjk
  have hvanish : ∀ x ∈ S, q.eval x = 0 := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact hconj k
  have hdeg : q.natDegree < S.card := by
    rw [hScard, hq, Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective]
    exact hd
  exact hq0 (eq_zero_of_card_roots_gt_natDegree q S hvanish hdeg)

end Bottcher
